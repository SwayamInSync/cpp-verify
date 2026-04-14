//===--- ExprContract.cpp - Contract expression AST node impl ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ExprContract.h"
#include "clang/AST/ASTContext.h"

using namespace clang;

// All methods are inline in the header for now. This file exists so the
// build system has a .cpp to compile and link, and for future non-inline
// implementations (e.g., profiling, serialization).
