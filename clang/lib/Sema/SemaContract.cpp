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

#include "TreeTransform.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTLambda.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtContract.h"
#include "clang/Sema/Sema.h"

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

const FunctionContractInfo *contractOf(const ASTContext &Ctx,
                                       const FunctionDecl *FD) {
  for (const FunctionDecl *Redecl : FD->redecls())
    if (const FunctionContractInfo *FCI = Ctx.getFunctionContract(Redecl))
      return FCI;
  return nullptr;
}

/// Finds spec-function references in evaluated executable code.
class ExecutableSpecUseFinder
    : public RecursiveASTVisitor<ExecutableSpecUseFinder> {
  using Base = RecursiveASTVisitor<ExecutableSpecUseFinder>;
  Sema &S;
  unsigned GhostDepth = 0;

  template <typename Traverse> bool inGhost(Traverse &&T) {
    ++GhostDepth;
    bool Result = T();
    --GhostDepth;
    return Result;
  }

public:
  explicit ExecutableSpecUseFinder(Sema &S) : S(S) {}

  bool TraverseGhostBlockStmt(GhostBlockStmt *G) {
    return inGhost([&] { return Base::TraverseGhostBlockStmt(G); });
  }
  bool TraverseContractAssertStmt(ContractAssertStmt *C) {
    return inGhost([&] { return Base::TraverseContractAssertStmt(C); });
  }
  bool TraverseRevealWithFuelStmt(RevealWithFuelStmt *R) {
    return inGhost([&] { return Base::TraverseRevealWithFuelStmt(R); });
  }
  bool TraverseHideSpecStmt(HideSpecStmt *H) {
    return inGhost([&] { return Base::TraverseHideSpecStmt(H); });
  }
  bool TraverseRevealSpecStmt(RevealSpecStmt *R) {
    return inGhost([&] { return Base::TraverseRevealSpecStmt(R); });
  }

  // Unevaluated operands emit no code.
  bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr *) {
    return true;
  }
  bool TraverseCXXNoexceptExpr(CXXNoexceptExpr *) { return true; }
  bool TraverseRequiresExpr(RequiresExpr *) { return true; }
  bool TraverseDecltypeTypeLoc(DecltypeTypeLoc, bool = true) { return true; }
  bool TraverseTypeOfExprTypeLoc(TypeOfExprTypeLoc, bool = true) {
    return true;
  }
  bool TraverseCXXTypeidExpr(CXXTypeidExpr *E) {
    return !E->isPotentiallyEvaluated() || Base::TraverseCXXTypeidExpr(E);
  }

  // A default argument is evaluated where it is used.
  bool TraverseCXXDefaultArgExpr(CXXDefaultArgExpr *E) {
    return TraverseStmt(E->getExpr());
  }

  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (GhostDepth)
      return true;
    const auto *FD = dyn_cast<FunctionDecl>(E->getDecl());
    if (!FD)
      return true;
    const FunctionContractInfo *FCI = contractOf(S.Context, FD);
    if (FCI && FCI->IsSpec &&
        S.DiagnosedSpecFunctionUses.insert(E->getExprLoc()).second)
      S.Diag(E->getExprLoc(), diag::err_spec_function_in_executable_code) << FD;
    return true;
  }
};

} // namespace

void Sema::CheckSpecFunctionUses(const FunctionDecl *FD, Stmt *Code) {
  if (!Code)
    return;
  ExecutableSpecUseFinder Finder(*this);
  if (FD) {
    // The enclosing function's walk covers a lambda body in its context.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(FD);
        Method && isLambdaCallOperator(Method))
      return;
    if (const FunctionContractInfo *FCI = contractOf(Context, FD);
        FCI && (FCI->IsSpec || FCI->IsProof))
      return;
    if (const auto *Ctor = dyn_cast<CXXConstructorDecl>(FD))
      for (const CXXCtorInitializer *Init : Ctor->inits())
        if (Init->isWritten())
          Finder.TraverseStmt(Init->getInit());
  }
  Finder.TraverseStmt(Code);
}

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
