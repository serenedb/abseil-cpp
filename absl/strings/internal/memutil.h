//
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
//

#ifndef ABSL_STRINGS_INTERNAL_MEMUTIL_H_
#define ABSL_STRINGS_INTERNAL_MEMUTIL_H_

#include <cstddef>
#include <cstdint>
#include <cstring>

#include "absl/base/port.h"  // disable some warnings on Windows
#include "absl/strings/ascii.h"  // for absl::ascii_tolower

namespace absl {
ABSL_NAMESPACE_BEGIN
namespace strings_internal {

// Branchless SWAR ASCII upper->lower fold ('A'..'Z' -> 'a'..'z'); every other
// byte (including bytes >= 0x80) is left unchanged. Folds all packed bytes of
// the word in parallel. Shared so case-insensitive hashing and comparison use a
// single definition.
inline uint8_t ToLowerAscii8(uint8_t c) {
  uint8_t rotated = c & uint8_t(0x7fUL);
  rotated += uint8_t(0x25UL);
  rotated &= uint8_t(0x7fUL);
  rotated += uint8_t(0x1aUL);
  rotated &= ~c;
  rotated >>= 2;
  rotated &= uint8_t(0x20UL);
  return c + rotated;
}

inline uint16_t ToLowerAscii16(uint16_t c) {
  uint16_t rotated = c & uint16_t(0x7f7fUL);
  rotated += uint16_t(0x2525UL);
  rotated &= uint16_t(0x7f7fUL);
  rotated += uint16_t(0x1a1aUL);
  rotated &= ~c;
  rotated >>= 2;
  rotated &= uint16_t(0x2020UL);
  return c + rotated;
}

inline uint32_t ToLowerAscii32(uint32_t c) {
  uint32_t rotated = c & uint32_t(0x7f7f7f7fUL);
  rotated += uint32_t(0x25252525UL);
  rotated &= uint32_t(0x7f7f7f7fUL);
  rotated += uint32_t(0x1a1a1a1aUL);
  rotated &= ~c;
  rotated >>= 2;
  rotated &= uint32_t(0x20202020UL);
  return c + rotated;
}

inline uint64_t ToLowerAscii64(uint64_t c) {
  uint64_t rotated = c & uint64_t(0x7f7f7f7f7f7f7f7fULL);
  rotated += uint64_t(0x2525252525252525ULL);
  rotated &= uint64_t(0x7f7f7f7f7f7f7f7fULL);
  rotated += uint64_t(0x1a1a1a1a1a1a1a1aULL);
  rotated &= ~c;
  rotated >>= 2;
  rotated &= uint64_t(0x2020202020202020ULL);
  return c + rotated;
}

// Performs a byte-by-byte comparison of `len` bytes of the strings `s1` and
// `s2`, ignoring the case of the characters. It returns an integer less than,
// equal to, or greater than zero if `s1` is found, respectively, to be less
// than, to match, or be greater than `s2`.
int memcasecmp(const char* s1, const char* s2, size_t len);

}  // namespace strings_internal
ABSL_NAMESPACE_END
}  // namespace absl

#endif  // ABSL_STRINGS_INTERNAL_MEMUTIL_H_
