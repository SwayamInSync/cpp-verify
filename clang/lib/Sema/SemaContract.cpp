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
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/StmtContract.h"
#include "clang/Sema/Sema.h"
#include "TreeTransform.h"

using namespace clang;

namespace {

class TypeInvariantFieldRewriter : public TreeTransform<TypeInvariantFieldRewriter> {
  typedef TreeTransform<TypeInvariantFieldRewriter> Base;
  CXXRecordDecl *Record;

public:
  TypeInvariantFieldRewriter(Sema &S, CXXRecordDecl *RD)
      : Base(S), Record(RD) {}

  ExprResult TransformDeclRefExpr(DeclRefExpr *E) {
    if (FieldDecl *FD = dyn_cast<FieldDecl>(E->getDecl())) {
      if (FD->getParent() == Record) {
        SourceLocation Loc = E->getBeginLoc();
        QualType ThisTy =
            getSema().Context.getTypeDeclType(cast<TypeDecl>(Record));
        ExprResult This =
            getSema().BuildCXXThisExpr(Loc, ThisTy, /*IsImplicit=*/true);
        if (This.isInvalid())
          return ExprError();
        DeclarationNameInfo NameInfo(FD->getDeclName(), Loc);
        return getSema().BuildMemberExpr(
            This.get(), /*IsArrow=*/false, Loc, NestedNameSpecifierLoc(),
            SourceLocation(), FD, DeclAccessPair::make(FD, FD->getAccess()),
            /*HadMultipleCandidates=*/false, NameInfo, FD->getType(),
            VK_LValue, OK_Ordinary, /*TemplateArgs=*/nullptr);
      }
    }
    return Base::TransformDeclRefExpr(E);
  }
};

} // namespace

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

ExprResult Sema::ActOnTypeInvariantExpr(ExprResult E, CXXRecordDecl *Record) {
  if (E.isInvalid() || !Record)
    return E;
  TypeInvariantFieldRewriter Rewriter(*this, Record);
  ExprResult Transformed = Rewriter.TransformExpr(E.get());
  if (Transformed.isInvalid())
    return Transformed;
  return ActOnContractCondition(Transformed.get());
}
