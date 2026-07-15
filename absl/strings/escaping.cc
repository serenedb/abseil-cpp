// Copyright 2017 The Abseil Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "absl/strings/escaping.h"

#include <simdutf.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iterator>
#include <limits>
#include <optional>
#include <string>
#include <utility>

#include "absl/base/config.h"
#include "absl/base/internal/endian.h"
#include "absl/base/internal/raw_logging.h"
#include "absl/base/internal/unaligned_access.h"
#include "absl/base/macros.h"
#include "absl/base/nullability.h"
#include "absl/base/optimization.h"
#include "absl/strings/ascii.h"
#include "absl/strings/charset.h"
#include "absl/strings/internal/append_and_overwrite.h"
#include "absl/strings/internal/escaping.h"
#include "absl/strings/internal/utf8.h"
#include "absl/strings/numbers.h"
#include "absl/strings/resize_and_overwrite.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

namespace absl {
ABSL_NAMESPACE_BEGIN
namespace {

// These are used for the leave_nulls_escaped argument to CUnescapeInternal().
constexpr bool kUnescapeNulls = false;

inline bool is_octal_digit(char c) { return ('0' <= c) && (c <= '7'); }

inline unsigned int hex_digit_to_int(char c) {
  static_assert('0' == 0x30 && 'A' == 0x41 && 'a' == 0x61,
                "Character set must be ASCII.");
  assert(absl::ascii_isxdigit(static_cast<unsigned char>(c)));
  unsigned int x = static_cast<unsigned char>(c);
  if (x > '9') {
    x += 9;
  }
  return x & 0xf;
}

inline char int_to_hex_digit(int i) {
  assert(i >= 0 && i <= 15);
  return ((i < 10) ? (static_cast<char>(i) + '0')
                   : (static_cast<char>(i - 10) + 'A'));
}

inline bool IsSurrogate(char32_t c, absl::string_view src,
                        std::string* absl_nullable error) {
  if (c >= 0xD800 && c <= 0xDFFF) {
    if (error) {
      *error = absl::StrCat("invalid surrogate character (0xD800-DFFF): \\",
                            src);
    }
    return true;
  }
  return false;
}

// ----------------------------------------------------------------------
// CUnescapeInternal()
//    Implements both CUnescape() and CUnescapeForNullTerminatedString().
//
//    Unescapes C escape sequences and is the reverse of CEscape().
//
//    If `src` is valid, stores the unescaped string in `dst` and the length of
//    unescaped string in `dst_size`, and returns true. Otherwise returns false
//    and optionally stores the error description in `error`. Set `error` to
//    nullptr to disable error reporting.
//
//    `src` and `dst` may use the same underlying buffer (but keep in mind
//    that if this returns an error, it will leave both `src` and `dst` in
//    an unspecified state because they are using the same underlying buffer.)
//    `dst` must have at least as much space as `src`.
// ----------------------------------------------------------------------

bool CUnescapeInternal(absl::string_view src, bool leave_nulls_escaped,
                       char* absl_nonnull dst, size_t* absl_nonnull dst_size,
                       std::string* absl_nullable error) {
  absl::string_view::size_type p = 0;  // Current src position.
  size_t d = 0;                        // Current dst position.

  // When unescaping in-place, skip any prefix that does not have escaping.
  if (src.data() == dst) {
    while (p < src.size() && src[p] != '\\') p++, d++;
  }

  while (p < src.size()) {
    if (src[p] != '\\') {
      dst[d++] = src[p++];
    } else {
      if (++p >= src.size()) {  // skip past the '\\'
        if (error != nullptr) {
          *error = "String cannot end with \\";
        }
        return false;
      }
      switch (src[p]) {
          // clang-format off
        case 'a':  dst[d++] = '\a';  break;
        case 'b':  dst[d++] = '\b';  break;
        case 'f':  dst[d++] = '\f';  break;
        case 'n':  dst[d++] = '\n';  break;
        case 'r':  dst[d++] = '\r';  break;
        case 't':  dst[d++] = '\t';  break;
        case 'v':  dst[d++] = '\v';  break;
        case '\\': dst[d++] = '\\';  break;
        case '?':  dst[d++] = '\?';  break;
        case '\'': dst[d++] = '\'';  break;
        case '"':  dst[d++] = '\"';  break;
        // clang-format on
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7': {
          // octal digit: 1 to 3 digits
          auto octal_start = p;
          unsigned int ch = static_cast<unsigned int>(src[p] - '0');  // digit 1
          if (p + 1 < src.size() && is_octal_digit(src[p + 1]))
            ch = ch * 8 + static_cast<unsigned int>(src[++p] - '0');  // digit 2
          if (p + 1 < src.size() && is_octal_digit(src[p + 1]))
            ch = ch * 8 + static_cast<unsigned int>(src[++p] - '0');  // digit 3
          if (ch > 0xff) {
            if (error != nullptr) {
              *error =
                  "Value of \\" +
                  std::string(src.substr(octal_start, p + 1 - octal_start)) +
                  " exceeds 0xff";
            }
            return false;
          }
          if ((ch == 0) && leave_nulls_escaped) {
            // Copy the escape sequence for the null character
            dst[d++] = '\\';
            while (octal_start <= p) {
              dst[d++] = src[octal_start++];
            }
            break;
          }
          dst[d++] = static_cast<char>(ch);
          break;
        }
        case 'x':
        case 'X': {
          if (p + 1 >= src.size()) {
            if (error != nullptr) {
              *error = "String cannot end with \\x";
            }
            return false;
          } else if (!absl::ascii_isxdigit(
              static_cast<unsigned char>(src[p + 1]))) {
            if (error != nullptr) {
              *error = "\\x cannot be followed by a non-hex digit";
            }
            return false;
          }
          unsigned int ch = 0;
          auto hex_start = p;
          while (p + 1 < src.size() &&
                 absl::ascii_isxdigit(static_cast<unsigned char>(src[p + 1]))) {
            // Arbitrarily many hex digits
            ch = (ch << 4) + hex_digit_to_int(src[++p]);
            // If ch was 0xFF at the start of this loop, the most can it can be
            // here is (0xFF << 4) + 0xF, which is 4095, thus ch cannot overflow
            // 32-bits here. The check below is sufficient.
            if (ch > 0xFF) {
              if (error != nullptr) {
                *error = "Value of \\" +
                         std::string(src.substr(hex_start, p + 1 - hex_start)) +
                         " exceeds 0xff";
              }
              return false;
            }
          }
          if ((ch == 0) && leave_nulls_escaped) {
            // Copy the escape sequence for the null character
            dst[d++] = '\\';
            while (hex_start <= p) {
              dst[d++] = src[hex_start++];
            }
            break;
          }
          dst[d++] = static_cast<char>(ch);
          break;
        }
        case 'u': {
          // \uhhhh => convert 4 hex digits to UTF-8
          char32_t rune = 0;
          auto hex_start = p;
          if (p + 4 >= src.size()) {
            if (error != nullptr) {
              *error = "\\u must be followed by 4 hex digits";
            }
            return false;
          }
          for (int i = 0; i < 4; ++i) {
            // Look one char ahead.
            if (absl::ascii_isxdigit(static_cast<unsigned char>(src[p + 1]))) {
              rune = (rune << 4) + hex_digit_to_int(src[++p]);
            } else {
              if (error != nullptr) {
                *error = "\\u must be followed by 4 hex digits: \\" +
                         std::string(src.substr(hex_start, p + 1 - hex_start));
              }
              return false;
            }
          }
          if ((rune == 0) && leave_nulls_escaped) {
            // Copy the escape sequence for the null character
            dst[d++] = '\\';
            while (hex_start <= p) {
              dst[d++] = src[hex_start++];
            }
            break;
          }
          if (IsSurrogate(rune, src.substr(hex_start, 5), error)) {
            return false;
          }
          d += strings_internal::EncodeUTF8Char(dst + d, rune);
          break;
        }
        case 'U': {
          // \Uhhhhhhhh => convert 8 hex digits to UTF-8
          char32_t rune = 0;
          auto hex_start = p;
          if (p + 8 >= src.size()) {
            if (error != nullptr) {
              *error = "\\U must be followed by 8 hex digits";
            }
            return false;
          }
          for (int i = 0; i < 8; ++i) {
            // Look one char ahead.
            if (absl::ascii_isxdigit(static_cast<unsigned char>(src[p + 1]))) {
              // Don't change rune until we're sure this
              // is within the Unicode limit, but do advance p.
              uint32_t newrune = (rune << 4) + hex_digit_to_int(src[++p]);
              if (newrune > 0x10FFFF) {
                if (error != nullptr) {
                  *error =
                      "Value of \\" +
                      std::string(src.substr(hex_start, p + 1 - hex_start)) +
                      " exceeds Unicode limit (0x10FFFF)";
                }
                return false;
              } else {
                rune = newrune;
              }
            } else {
              if (error != nullptr) {
                *error = "\\U must be followed by 8 hex digits: \\" +
                         std::string(src.substr(hex_start, p + 1 - hex_start));
              }
              return false;
            }
          }
          if ((rune == 0) && leave_nulls_escaped) {
            // Copy the escape sequence for the null character
            dst[d++] = '\\';
            // U00000000
            while (hex_start <= p) {
              dst[d++] = src[hex_start++];
            }
            break;
          }
          if (IsSurrogate(rune, src.substr(hex_start, 9), error)) {
            return false;
          }
          d += strings_internal::EncodeUTF8Char(dst + d, rune);
          break;
        }
        default: {
          if (error != nullptr) {
            *error = std::string("Unknown escape sequence: \\") + src[p];
          }
          return false;
        }
      }
      p++;  // Read past letter we escaped.
    }
  }

  *dst_size = d;
  return true;
}

// ----------------------------------------------------------------------
// CEscape()
// CHexEscape()
// Utf8SafeCEscape()
// Utf8SafeCHexEscape()
//    Escapes 'src' using C-style escape sequences.  This is useful for
//    preparing query flags.  The 'Hex' version uses hexadecimal rather than
//    octal sequences.  The 'Utf8Safe' version does not touch UTF-8 bytes.
//
//    Escaped chars: \n, \r, \t, ", ', \, and !absl::ascii_isprint().
// ----------------------------------------------------------------------
std::string CEscapeInternal(absl::string_view src, bool use_hex,
                            bool utf8_safe) {
  std::string dest;
  bool last_hex_escape = false;  // true if last output char was \xNN.

  for (char c : src) {
    bool is_hex_escape = false;
    switch (c) {
      case '\n': dest.append("\\" "n"); break;
      case '\r': dest.append("\\" "r"); break;
      case '\t': dest.append("\\" "t"); break;
      case '\"': dest.append("\\" "\""); break;
      case '\'': dest.append("\\" "'"); break;
      case '\\': dest.append("\\" "\\"); break;
      default: {
        // Note that if we emit \xNN and the src character after that is a hex
        // digit then that digit must be escaped too to prevent it being
        // interpreted as part of the character code by C.
        const unsigned char uc = static_cast<unsigned char>(c);
        if ((!utf8_safe || uc < 0x80) &&
            (!absl::ascii_isprint(uc) ||
             (last_hex_escape && absl::ascii_isxdigit(uc)))) {
          if (use_hex) {
            dest.append("\\" "x");
            dest.push_back(numbers_internal::kHexChar[uc / 16]);
            dest.push_back(numbers_internal::kHexChar[uc % 16]);
            is_hex_escape = true;
          } else {
            dest.append("\\");
            dest.push_back(numbers_internal::kHexChar[uc / 64]);
            dest.push_back(numbers_internal::kHexChar[(uc % 64) / 8]);
            dest.push_back(numbers_internal::kHexChar[uc % 8]);
          }
        } else {
          dest.push_back(c);
          break;
        }
      }
    }
    last_hex_escape = is_hex_escape;
  }

  return dest;
}

/* clang-format off */
constexpr std::array<unsigned char, 256> kCEscapedLen = {
    4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 4, 4, 2, 4, 4,  // \t, \n, \r
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,  // ", '
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,  // '0'..'9'
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,  // 'A'..'O'
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1,  // 'P'..'Z', '\'
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,  // 'a'..'o'
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4,  // 'p'..'z', DEL
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
};
/* clang-format on */

constexpr uint32_t MakeCEscapedLittleEndianUint32(size_t c) {
  size_t char_len = kCEscapedLen[c];
  if (char_len == 1) {
    return static_cast<uint32_t>(c);
  }
  if (char_len == 2) {
    switch (c) {
      case '\n':
        return '\\' | (static_cast<uint32_t>('n') << 8);
      case '\r':
        return '\\' | (static_cast<uint32_t>('r') << 8);
      case '\t':
        return '\\' | (static_cast<uint32_t>('t') << 8);
      case '\"':
        return '\\' | (static_cast<uint32_t>('\"') << 8);
      case '\'':
        return '\\' | (static_cast<uint32_t>('\'') << 8);
      case '\\':
        return '\\' | (static_cast<uint32_t>('\\') << 8);
    }
  }
  return static_cast<uint32_t>('\\' | (('0' + (c / 64)) << 8) |
                               (('0' + ((c % 64) / 8)) << 16) |
                               (('0' + (c % 8)) << 24));
}

template <size_t... indexes>
inline constexpr std::array<uint32_t, sizeof...(indexes)>
MakeCEscapedLittleEndianUint32Array(std::index_sequence<indexes...>) {
  return {MakeCEscapedLittleEndianUint32(indexes)...};
}
constexpr std::array<uint32_t, 256> kCEscapedLittleEndianUint32Array =
    MakeCEscapedLittleEndianUint32Array(std::make_index_sequence<256>());

// Calculates the length of the C-style escaped version of 'src'.
// Assumes that non-printable characters are escaped using octal sequences, and
// that UTF-8 bytes are not handled specially.
inline size_t CEscapedLength(absl::string_view src) {
  size_t escaped_len = 0;
  // The maximum value of kCEscapedLen[x] is 4, so we can escape any string of
  // length size_t_max/4 without checking for overflow.
  size_t unchecked_limit =
      std::min<size_t>(src.size(), std::numeric_limits<size_t>::max() / 4);
  size_t i = 0;
  while (i < unchecked_limit) {
    // Common case: No need to check for overflow.
    escaped_len += kCEscapedLen[static_cast<unsigned char>(src[i++])];
  }
  while (i < src.size()) {
    // Beyond unchecked_limit we need to check for overflow before adding.
    size_t char_len = kCEscapedLen[static_cast<unsigned char>(src[i++])];
    ABSL_INTERNAL_CHECK(
        escaped_len <= std::numeric_limits<size_t>::max() - char_len,
        "escaped_len overflow");
    escaped_len += char_len;
  }
  return escaped_len;
}

void CEscapeAndAppendInternal(absl::string_view src,
                              std::string* absl_nonnull dest) {
  size_t escaped_len = CEscapedLength(src);
  if (escaped_len == src.size()) {
    dest->append(src.data(), src.size());
    return;
  }

  // We keep 3 slop bytes so that we can call `little_endian::Store32`
  // invariably regardless of the length of the escaped character.
  constexpr size_t kSlopBytes = 3;
  ABSL_INTERNAL_CHECK(
      escaped_len <= std::numeric_limits<size_t>::max() - kSlopBytes,
      "CEscape length overflow");
  size_t append_buf_len = escaped_len + kSlopBytes;
  strings_internal::StringAppendAndOverwrite(
      *dest, append_buf_len, [src, escaped_len](char* append_ptr, size_t) {
        for (char c : src) {
          unsigned char uc = static_cast<unsigned char>(c);
          size_t char_len = kCEscapedLen[uc];
          uint32_t little_endian_uint32 = kCEscapedLittleEndianUint32Array[uc];
          little_endian::Store32(append_ptr, little_endian_uint32);
          append_ptr += char_len;
        }
        return escaped_len;
      });
}

}  // namespace

// The two strings below provide maps from normal 6-bit characters to their
// base64-escaped equivalent.
// For the inverse case, see kUn(WebSafe)Base64 in the external
// escaping.cc.

// ----------------------------------------------------------------------
//   Take the input in groups of 4 characters and turn each
//   character into a code 0 to 63 thus:
//           A-Z map to 0 to 25
//           a-z map to 26 to 51
//           0-9 map to 52 to 61
//           +(- for WebSafe) maps to 62
//           /(_ for WebSafe) maps to 63
//   There will be four numbers, all less than 64 which can be represented
//   by a 6 digit binary number (aaaaaa, bbbbbb, cccccc, dddddd respectively).
//   Arrange the 6 digit binary numbers into three bytes as such:
//   aaaaaabb bbbbcccc ccdddddd
//   Equals signs (one or two) are used at the end of the encoded block to
//   indicate that the text was not an integer multiple of three bytes long.
// ----------------------------------------------------------------------
namespace {

std::string Base64EscapeToStringInternal(const char* src, size_t szsrc,
                                         simdutf::base64_options options) {
  std::string escaped;
  const size_t calc_escaped_size =
      simdutf::base64_length_from_binary(szsrc, options);
  StringResizeAndOverwrite(
      escaped, calc_escaped_size, [&](char* buf, size_t buf_size) {
        const size_t escaped_len =
            simdutf::binary_to_base64(src, szsrc, buf, options);
        assert(escaped_len == buf_size);
        return escaped_len;
      });
  return escaped;
}

bool Base64UnescapeInternal(const char* absl_nullable src, size_t slen,
                            std::string* absl_nonnull dest,
                            simdutf::base64_options options) {
  // Determine the size of the output string.  Base64 encodes every 3 bytes into
  // 4 characters.  Any leftover chars are added directly for good measure.
  const size_t dest_len = simdutf::maximal_binary_length_from_base64(src, slen);

  bool ok;
  StringResizeAndOverwrite(*dest, dest_len, [&](char* buf, size_t buf_size) {
    size_t len = buf_size;
    ok = simdutf::base64_to_binary_safe(
             src, slen, buf, len, options,
             simdutf::last_chunk_handling_options::loose)
             .error == simdutf::error_code::SUCCESS;
    if (!ok) {
      len = 0;
    }
    assert(len <= buf_size);  // Could be shorter if there was padding.
    return len;
  });
  return ok;
}

/* clang-format off */
constexpr std::array<uint8_t, 256> kHexValueLenient = {
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  1,  2,  3,  4,  5,  6, 7, 8, 9, 0, 0, 0, 0, 0, 0,  // '0'..'9'
    0, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0,  // 'A'..'F'
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0,  // 'a'..'f'
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
/* clang-format on */

// This is a templated function so that T can be either a char*
// or a string.  This works because we use the [] operator to access
// individual characters at a time.
template <typename T>
void HexStringToBytesInternal(const char* absl_nullable from, T to,
                              size_t num) {
  for (size_t i = 0; i < num; i++) {
    to[i] = static_cast<char>(kHexValueLenient[from[i * 2] & 0xFF] << 4) +
            static_cast<char>(kHexValueLenient[from[i * 2 + 1] & 0xFF]);
  }
}

}  // namespace

// ----------------------------------------------------------------------
// CUnescape()
//
// See CUnescapeInternal() for implementation details.
// ----------------------------------------------------------------------

bool CUnescape(absl::string_view source, std::string* absl_nonnull dest,
               std::string* absl_nullable error) {
  bool success;

  // `CUnescape()` allows for in-place unescaping, which means `source` may
  // alias `*dest`.  However, absl::StringResizeAndOverwrite() invalidates all
  // iterators, pointers, and references into the string, regardless whether
  // reallocation occurs. Therefore we need to avoid calling
  // absl::StringResizeAndOverwrite() when `source.data() ==
  // dest->data()`. Comparing the sizes is sufficient to cover this case.
  if (dest->size() >= source.size()) {
    size_t dest_size = 0;
    success = CUnescapeInternal(source, kUnescapeNulls, dest->data(),
                                &dest_size, error);
    ABSL_ASSERT(dest_size <= dest->size());
    dest->erase(dest_size);
  } else {
    StringResizeAndOverwrite(
        *dest, source.size(),
        [source, error, &success](char* buf, size_t buf_size) {
          size_t dest_size = 0;
          success =
              CUnescapeInternal(source, kUnescapeNulls, buf, &dest_size, error);
          ABSL_ASSERT(dest_size <= buf_size);
          return dest_size;
        });
  }
  return success;
}

std::string CEscape(absl::string_view src) {
  std::string dest;
  CEscapeAndAppendInternal(src, &dest);
  return dest;
}

std::string CHexEscape(absl::string_view src) {
  return CEscapeInternal(src, true, false);
}

std::string Utf8SafeCEscape(absl::string_view src) {
  return CEscapeInternal(src, false, true);
}

std::string Utf8SafeCHexEscape(absl::string_view src) {
  return CEscapeInternal(src, true, true);
}

bool Base64Unescape(absl::string_view src, std::string* absl_nonnull dest) {
  return Base64UnescapeInternal(src.data(), src.size(), dest,
                                simdutf::base64_default);
}

bool WebSafeBase64Unescape(absl::string_view src,
                           std::string* absl_nonnull dest) {
  return Base64UnescapeInternal(src.data(), src.size(), dest,
                                simdutf::base64_url);
}

std::string Base64Escape(absl::string_view src) {
  return Base64EscapeToStringInternal(src.data(), src.size(),
                                      simdutf::base64_default);
}

std::string WebSafeBase64Escape(absl::string_view src) {
  return Base64EscapeToStringInternal(src.data(), src.size(),
                                      simdutf::base64_url);
}

bool HexStringToBytes(absl::string_view hex, std::string* absl_nonnull bytes) {
  std::string output;

  size_t num_bytes = hex.size() / 2;
  if (hex.size() != num_bytes * 2) {
    return false;
  }

  StringResizeAndOverwrite(
      output, num_bytes, [hex](char* buf, size_t buf_size) {
        auto hex_p = hex.cbegin();
        for (size_t i = 0; i < buf_size; ++i) {
          int h1 = absl::kHexValueStrict[static_cast<size_t>(
              static_cast<uint8_t>(*hex_p++))];
          int h2 = absl::kHexValueStrict[static_cast<size_t>(
              static_cast<uint8_t>(*hex_p++))];
          if (h1 == -1 || h2 == -1) {
            return size_t{0};
          }
          buf[i] = static_cast<char>((h1 << 4) + h2);
        }
        return buf_size;
      });

  if (output.size() != num_bytes) {
    return false;
  }
  *bytes = std::move(output);
  return true;
}

std::string HexStringToBytes(absl::string_view from) {
  std::string result;
  const auto num = from.size() / 2;
  StringResizeAndOverwrite(result, num, [from](char* buf, size_t buf_size) {
    absl::HexStringToBytesInternal<char*>(from.data(), buf, buf_size);
    return buf_size;
  });
  return result;
}

std::string BytesToHexString(absl::string_view from) {
  std::string result;
  ABSL_INTERNAL_CHECK(from.size() <= std::numeric_limits<size_t>::max() / 2,
                      "BytesToHexString() overflow");
  StringResizeAndOverwrite(
      result, 2 * from.size(), [from](char* buf, size_t buf_size) {
        absl::BytesToHexStringInternal(
            reinterpret_cast<const unsigned char*>(from.data()), buf,
            from.size());
        return buf_size;
      });
  return result;
}

static std::string UrlEscapeInternal(absl::string_view input,
                                     const bool escape_space_to_plus) {
  // Unreserved characters from RFC 3986.
  // See https://www.rfc-editor.org/info/rfc3986/#section-2.3.
  static constexpr absl::CharSet kRfc3986Unreserved =
      absl::CharSet::AsciiAlphanumerics() | absl::CharSet("-._~");

  std::string output;
  absl::string_view::iterator in = input.begin();

  // Fast path for when we don't need to do any escaping.
  while (in < input.end() && kRfc3986Unreserved.contains(*in)) {
    ++in;
  }

  std::size_t initial_portion =
      static_cast<std::size_t>(std::distance(input.begin(), in));

  if (initial_portion == input.size()) {
    return std::string(input);
  }

  // We need a buffer with enough space to store at most the initial portion
  // plus 3 bytes for each remaining character since escapes use 3 characters.
  ABSL_INTERNAL_CHECK(
      (input.size() - initial_portion) <=
          (std::numeric_limits<size_t>::max() - initial_portion) / 3,
      "UrlEscape() overflow");
  StringResizeAndOverwrite(
      output, initial_portion + 3 * (input.size() - initial_portion),
      [&](char* buf, size_t) {
        char* out = buf;

        // Copy the initial portion that did not need escaping.
        out = std::copy(input.begin(), in, out);

        // Handle the rest of the string.
        while (in < input.end()) {
          char c = *in++;
          if (kRfc3986Unreserved.contains(c)) {
            *out++ = c;
          } else if (escape_space_to_plus && c == ' ') {
            *out++ = '+';
          } else {
            *out++ = '%';
            *out++ = static_cast<char>(
                int_to_hex_digit((static_cast<unsigned char>(c) >> 4) & 0xf));
            *out++ = static_cast<char>(
                int_to_hex_digit(static_cast<unsigned char>(c) & 0xf));
          }
        }
        return static_cast<size_t>(std::distance(buf, out));
      });

  return output;
}

static std::optional<std::string> UrlUnescapeInternal(
    absl::string_view input, const bool unescape_plus_to_space) {
  std::string output;

  // Fast path for when we don't need to do any unescaping.
  // This case includes empty input, which allows us to return 0 from the
  // lambda below to signal the error case.
  size_t in =
      unescape_plus_to_space ? input.find_first_of("%+") : input.find('%');
  if (in == input.npos) {
    return std::string(input);
  }

  StringResizeAndOverwrite(output, input.size(), [&](char* buf, size_t) {
    char* out = buf;

    // Copy the initial portion that did not need unescaping.
    out = std::copy_n(input.data(), in, out);

    // Handle the rest of the string.
    while (in < input.size()) {
      char c = input[in++];
      if (unescape_plus_to_space && c == '+') {
        *out++ = ' ';
      } else if (c == '%') {
        if (in + 1 >= input.size() ||
            !absl::ascii_isxdigit(static_cast<unsigned char>(input[in])) ||
            !absl::ascii_isxdigit(static_cast<unsigned char>(input[in + 1]))) {
          return size_t{0};  // Error.
        }
        int x = static_cast<int>(hex_digit_to_int(input[in++])) << 4;
        x += static_cast<int>(hex_digit_to_int(input[in++]));
        *out++ = static_cast<char>(x);
      } else {
        *out++ = c;
      }
    }
    return static_cast<size_t>(std::distance(buf, out));
  });

  if (output.empty()) {
    // Empty output is only valid if the input was empty, and that case is
    // handled above.
    return std::nullopt;
  }

  return output;
}

std::string UrlEscape(absl::string_view input) {
  constexpr bool kEscapeSpaceToPlus = false;
  return UrlEscapeInternal(input, kEscapeSpaceToPlus);
}

std::optional<std::string> UrlUnescape(absl::string_view input) {
  constexpr bool kUnescapePlusToSpace = false;
  return UrlUnescapeInternal(input, kUnescapePlusToSpace);
}

std::string UrlEscapePlus(absl::string_view input) {
  constexpr bool kEscapeSpaceToPlus = true;
  return UrlEscapeInternal(input, kEscapeSpaceToPlus);
}

std::optional<std::string> UrlUnescapePlus(absl::string_view input) {
  constexpr bool kUnescapePlusToSpace = true;
  return UrlUnescapeInternal(input, kUnescapePlusToSpace);
}

ABSL_NAMESPACE_END
}  // namespace absl
