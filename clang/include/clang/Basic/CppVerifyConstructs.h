//===--- CppVerifyConstructs.h - cpp-verify construct words -----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_BASIC_CPPVERIFYCONSTRUCTS_H
#define LLVM_CLANG_BASIC_CPPVERIFYCONSTRUCTS_H

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSwitch.h"
#include <cstdint>
#include <optional>

namespace clang {

/// A cpp-verify construct, written cppverify::word.
enum class CppVerifyConstruct : uint8_t {
#define CPPVERIFY_CONSTRUCT(Name, Spelling, Positions) Name,
#include "clang/Basic/CppVerifyConstructs.def"
};

/// Where a construct may be written.
namespace CppVerifyPosition {
enum : unsigned {
  FunctionClause = 1u << 0, ///< After a function declarator.
  LoopClause = 1u << 1,     ///< Between a loop head and its body.
  ClassMember = 1u << 2,    ///< In a class body.
  Specifier = 1u << 3,      ///< Among the declaration specifiers.
  Statement = 1u << 4,      ///< At the start of a statement.
  Expression = 1u << 5,     ///< As a primary expression.
};
} // namespace CppVerifyPosition

inline std::optional<CppVerifyConstruct>
lookupCppVerifyConstruct(llvm::StringRef Word) {
  return llvm::StringSwitch<std::optional<CppVerifyConstruct>>(Word)
#define CPPVERIFY_CONSTRUCT(Name, Spelling, Positions)                         \
  .Case(Spelling, CppVerifyConstruct::Name)
#include "clang/Basic/CppVerifyConstructs.def"
      .Default(std::nullopt);
}

inline llvm::StringRef getCppVerifySpelling(CppVerifyConstruct C) {
  switch (C) {
#define CPPVERIFY_CONSTRUCT(Name, Spelling, Positions)                         \
  case CppVerifyConstruct::Name:                                               \
    return Spelling;
#include "clang/Basic/CppVerifyConstructs.def"
  }
  return "";
}

inline unsigned getCppVerifyPositions(CppVerifyConstruct C) {
  using namespace CppVerifyPosition;
  switch (C) {
#define CPPVERIFY_CONSTRUCT(Name, Spelling, Positions)                         \
  case CppVerifyConstruct::Name:                                               \
    return Positions;
#include "clang/Basic/CppVerifyConstructs.def"
  }
  return 0;
}

} // namespace clang

#endif // LLVM_CLANG_BASIC_CPPVERIFYCONSTRUCTS_H
