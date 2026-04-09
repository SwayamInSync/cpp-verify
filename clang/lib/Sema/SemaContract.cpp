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

// Contract-specific semantic analysis will be added here as the verifier
// matures. For now, contract expressions are type-checked by Clang's
// standard expression Sema (since they are parsed as normal expressions),
// and the new AST nodes (ForallExpr, etc.) are constructed directly
// by the parser with ASTContext allocation.
