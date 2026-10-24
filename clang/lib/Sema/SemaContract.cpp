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
        // this->field, as a member function reads it, so that a class
        // template's instantiation rebuilds it with its own `this`.
        SourceLocation Loc = E->getBeginLoc();
        QualType ThisTy = getSema().getCurrentThisType();
        if (ThisTy.isNull())
          return Base::TransformDeclRefExpr(E);
        ExprResult This =
            getSema().BuildCXXThisExpr(Loc, ThisTy, /*IsImplicit=*/true);
        if (This.isInvalid())
          return ExprError();
        DeclarationNameInfo NameInfo(FD->getDeclName(), Loc);
        return getSema().BuildMemberExpr(
            This.get(), /*IsArrow=*/true, Loc, NestedNameSpecifierLoc(),
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

/// Declared by cppverify.h: a function or record of namespace cppverify, or a
/// member of one of its records.
bool isCollectionDecl(const Decl *D) {
  const DeclContext *DC = D->getDeclContext();
  if (const auto *RD = dyn_cast<CXXRecordDecl>(DC))
    DC = RD->getDeclContext();
  const auto *NS = dyn_cast<NamespaceDecl>(DC);
  return NS && NS->getIdentifier() && NS->getIdentifier()->isStr("cppverify") &&
         NS->getDeclContext()->getRedeclContext()->isTranslationUnit();
}

bool isCollectionType(QualType T) {
  const CXXRecordDecl *RD = T.getNonReferenceType()->getAsCXXRecordDecl();
  return RD && isCollectionDecl(RD);
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

  // A generic lambda's body as written is dependent; its specializations,
  // instantiated before or after this walk, are executable where it is.
  bool TraverseLambdaExpr(LambdaExpr *E) {
    CXXRecordDecl *Class = E->getLambdaClass();
    if (!GhostDepth && Class->isGenericLambda() &&
        S.ExecutableGenericLambdas.insert(Class).second)
      for (FunctionDecl *Spec :
           Class->getDependentLambdaCallOperator()->specializations())
        TraverseStmt(Spec->getBody());
    return Base::TraverseLambdaExpr(E);
  }

  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (GhostDepth)
      return true;
    if (const auto *VD = dyn_cast<VarDecl>(E->getDecl())) {
      if (S.Context.isGhostVariable(VD) &&
          S.DiagnosedSpecFunctionUses.insert(E->getExprLoc()).second)
        S.Diag(E->getExprLoc(), diag::err_ghost_variable_in_executable_code)
            << VD;
      return true;
    }
    const auto *FD = dyn_cast<FunctionDecl>(E->getDecl());
    if (!FD)
      return true;
    // The constructs' declarations are deleted.
    if (isCollectionDecl(FD) && !FD->isDeleted()) {
      diagnoseCollectionOperation(E->getExprLoc(), FD);
      return true;
    }
    const FunctionContractInfo *FCI = contractOf(S.Context, FD);
    if (FCI && FCI->IsSpec &&
        S.DiagnosedSpecFunctionUses.insert(E->getExprLoc()).second)
      S.Diag(E->getExprLoc(), diag::err_spec_function_in_executable_code) << FD;
    return true;
  }

  bool VisitMemberExpr(MemberExpr *E) {
    if (!GhostDepth && isCollectionDecl(E->getMemberDecl()))
      diagnoseCollectionOperation(E->getMemberLoc(), E->getMemberDecl());
    return true;
  }

  bool VisitVarDecl(VarDecl *VD) {
    if (!GhostDepth && isCollectionType(VD->getType()) &&
        !S.Context.isGhostVariable(VD) &&
        S.DiagnosedSpecFunctionUses.insert(VD->getLocation()).second)
      S.Diag(VD->getLocation(), diag::err_collection_in_executable_code)
          << 1 << VD->getType().getNonReferenceType().getUnqualifiedType();
    return true;
  }

  void diagnoseCollectionOperation(SourceLocation Loc, const NamedDecl *D) {
    if (S.DiagnosedSpecFunctionUses.insert(Loc).second)
      S.Diag(Loc, diag::err_collection_in_executable_code) << 0 << D;
  }

  // A quantifier or a choice has no value at run time: it is reported once,
  // and what it contains with it.
  bool TraverseForallExpr(ForallExpr *E) {
    return diagnoseConstruct(E, "forall") || Base::TraverseForallExpr(E);
  }
  bool TraverseExistsExpr(ExistsExpr *E) {
    return diagnoseConstruct(E, "exists") || Base::TraverseExistsExpr(E);
  }
  bool TraverseContractChooseExpr(ContractChooseExpr *E) {
    return diagnoseConstruct(E, "choose") ||
           Base::TraverseContractChooseExpr(E);
  }

  /// Whether \p E is in executable code, which is then reported.
  bool diagnoseConstruct(Expr *E, llvm::StringRef Name) {
    if (GhostDepth)
      return false;
    if (S.DiagnosedSpecFunctionUses.insert(E->getExprLoc()).second)
      S.Diag(E->getExprLoc(),
             diag::err_verification_construct_in_executable_code)
          << Name;
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
        Method && isLambdaCallOperator(Method)) {
      if (isGenericLambdaCallOperatorSpecialization(Method) &&
          ExecutableGenericLambdas.contains(Method->getParent()))
        Finder.TraverseStmt(Code);
      return;
    }
    if (const FunctionContractInfo *FCI = contractOf(Context, FD);
        FCI && (FCI->IsSpec || FCI->IsProof))
      return;
    // A collection has no runtime value to pass or return.
    for (const ParmVarDecl *Param : FD->parameters())
      if (isCollectionType(Param->getType()) &&
          DiagnosedSpecFunctionUses.insert(Param->getLocation()).second)
        Diag(Param->getLocation(), diag::err_collection_in_executable_code)
            << 1 << Param->getType().getNonReferenceType().getUnqualifiedType();
    if (isCollectionType(FD->getReturnType()) &&
        DiagnosedSpecFunctionUses.insert(FD->getLocation()).second)
      Diag(FD->getLocation(), diag::err_collection_in_executable_code)
          << 1 << FD->getReturnType().getUnqualifiedType();
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
  // A dependent condition is converted where it is instantiated.
  if (E.isInvalid() || E.get()->isTypeDependent())
    return E;
  return PerformContextuallyConvertToBool(E.get());
}

ExprResult Sema::ActOnContractRange(Expr *Base, Expr *Lower,
                                    SourceLocation ColonLoc, Expr *Length,
                                    SourceLocation RBLoc) {
  if (Base->isTypeDependent() || (Lower && Lower->isTypeDependent()) ||
      (Length && Length->isTypeDependent()))
    return new (Context)
        ArraySectionExpr(Base, Lower, Length, Context.DependentTy, VK_LValue,
                         OK_Ordinary, ColonLoc, RBLoc);
  ExprResult BaseResult = DefaultFunctionArrayLvalueConversion(Base);
  if (BaseResult.isInvalid())
    return ExprError();
  Base = BaseResult.get();
  const auto *PT = Base->getType()->getAs<PointerType>();
  if (!PT || PT->getPointeeType()->isFunctionType() ||
      RequireCompleteType(Base->getExprLoc(), PT->getPointeeType(),
                          diag::err_contract_range_base, Base->getType())) {
    if (!PT || PT->getPointeeType()->isFunctionType())
      Diag(Base->getExprLoc(), diag::err_contract_range_base)
          << Base->getType() << Base->getSourceRange();
    return ExprError();
  }
  if (!Length) {
    Diag(ColonLoc, diag::err_contract_range_no_length);
    return ExprError();
  }
  for (Expr **Bound : {&Lower, &Length}) {
    if (!*Bound)
      continue;
    ExprResult Converted = DefaultLvalueConversion(*Bound);
    if (Converted.isInvalid())
      return ExprError();
    *Bound = Converted.get();
    if (!(*Bound)->getType()->isIntegerType() ||
        (*Bound)->getType()->isBooleanType()) {
      Diag((*Bound)->getExprLoc(), diag::err_contract_range_bound_not_int)
          << (Bound == &Length) << (*Bound)->getSourceRange();
      return ExprError();
    }
  }
  return new (Context)
      ArraySectionExpr(Base, Lower, Length, Context.ArraySectionTy, VK_LValue,
                       OK_Ordinary, ColonLoc, RBLoc);
}

ExprResult Sema::ActOnContractMeasure(ExprResult E) {
  if (E.isInvalid() || E.get()->isTypeDependent() ||
      E.get()->getType()->isIntegerType())
    return E;
  Diag(E.get()->getExprLoc(), diag::err_contract_decreases_not_int);
  return ExprError();
}

ExprResult Sema::BuildContractBinderExpr(Stmt::StmtClass Kind,
                                         SourceLocation KeywordLoc,
                                         SourceLocation LParenLoc,
                                         SourceLocation RParenLoc,
                                         VarDecl *Binder, Expr *Lo, Expr *Hi,
                                         Expr *Body) {
  for (Expr *Bound : {Lo, Hi})
    if (Bound && !Bound->isTypeDependent() &&
        !Bound->getType()->isIntegerType()) {
      Diag(Bound->getExprLoc(), diag::err_contract_quantifier_bound_not_int);
      return ExprError();
    }
  ExprResult Condition = ActOnContractCondition(Body);
  if (Condition.isInvalid())
    return ExprError();
  switch (Kind) {
  case Stmt::ContractChooseExprClass:
    return new (Context) ContractChooseExpr(KeywordLoc, LParenLoc, RParenLoc,
                                            Binder, Lo, Hi, Condition.get(),
                                            Binder->getType());
  case Stmt::ForallExprClass:
    return new (Context) ForallExpr(KeywordLoc, LParenLoc, RParenLoc, Binder,
                                    Lo, Hi, Condition.get(), Context.BoolTy);
  default:
    assert(Kind == Stmt::ExistsExprClass && "not a quantifier or a choice");
    return new (Context) ExistsExpr(KeywordLoc, LParenLoc, RParenLoc, Binder,
                                    Lo, Hi, Condition.get(), Context.BoolTy);
  }
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
