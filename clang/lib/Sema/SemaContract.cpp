//===--- SemaContract.cpp - Semantic Analysis for Contracts ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements semantic analysis for CppVerify contract constructs.
// For the MVP, contract expressions are parsed as normal Clang expressions
// and get basic type checking through the standard Sema pipeline. This file
// provides a home for future contract-specific semantic checks.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/StmtContract.h"
#include "clang/Sema/Sema.h"

using namespace clang;

/// ActOnContractCondition - Semantic action called by the parser after
/// parsing a contract condition expression (pre/post/invariant/contract_assert).
///
/// Verifies that the expression is contextually convertible to bool.
///
/// ForallExpr and ExistsExpr already carry type BoolTy so the conversion is
/// a no-op; plain integer/pointer expressions receive the standard bool cast.
ExprResult Sema::ActOnContractCondition(ExprResult E) {
  if (E.isInvalid())
    return E;
  return PerformContextuallyConvertToBool(E.get());
}
