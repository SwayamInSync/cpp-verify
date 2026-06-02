//===--- ASTConverter.cpp -------------------------------------------------===//
#include "ASTConverter.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/StmtContract.h"
#include "llvm/ADT/StringSet.h"
#include <functional>

using namespace clang;
using namespace verify;

bool ASTConverter::calleeIsSpec(const FunctionDecl *FD) const {
  if (!FD)
    return false;
  if (const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD)) {
    if (FCI->IsSpec)
      return true;
  }
  return FD->isConstexpr() && FD->hasBody();
}

VIntMode ASTConverter::specCallIntMode(const FunctionDecl *FD) const {
  if (!FD)
    return VIntMode::Machine;
  if (const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD)) {
    if (FCI->IsSpec)
      return VIntMode::Math;
  }
  if (FD->isConstexpr())
    return VIntMode::Machine;
  return VIntMode::Math;
}

bool ASTConverter::contractsReferenceSpec(const FunctionContractInfo &FCI) const {
  std::function<bool(const Expr *)> check = [&](const Expr *E) -> bool {
    if (!E)
      return false;
    E = E->IgnoreParenImpCasts();
    if (const auto *CE = dyn_cast<CallExpr>(E)) {
      if (const FunctionDecl *Callee = CE->getDirectCallee())
        return calleeIsSpec(Callee);
    }
    if (const auto *B = dyn_cast<BinaryOperator>(E)) {
      return check(B->getLHS()) || check(B->getRHS());
    }
    if (const auto *U = dyn_cast<UnaryOperator>(E))
      return check(U->getSubExpr());
    if (const auto *O = dyn_cast<OldExpr>(E))
      return check(O->getInner());
    if (const auto *C = dyn_cast<ConditionalOperator>(E)) {
      return check(C->getCond()) || check(C->getTrueExpr()) ||
             check(C->getFalseExpr());
    }
    return false;
  };
  for (const Expr *E : FCI.Preconditions)
    if (check(E))
      return true;
  for (const Expr *E : FCI.Postconditions)
    if (check(E))
      return true;
  for (const Expr *E : FCI.Recommends)
    if (check(E))
      return true;
  return false;
}

std::string ASTConverter::specNameFromExpr(const Expr *E) {
  if (!E)
    return {};
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts()))
    if (const auto *FD = dyn_cast<FunctionDecl>(DRE->getDecl()))
      return FD->getNameAsString();
  return {};
}

bool ASTConverter::calleeIsProof(const FunctionDecl *FD) const {
  if (!FD)
    return false;
  if (const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD))
    return FCI->IsProof;
  return false;
}

static bool isMutablePointerParam(const ParmVarDecl *P) {
  QualType T = P->getType();
  if (!T->isPointerType() && !T->isReferenceType())
    return false;
  if (T->isReferenceType())
    T = T.getNonReferenceType();
  return !T->getPointeeType().isConstQualified();
}

static bool aliasesListed(const FunctionContractInfo &FCI, const ParmVarDecl *A,
                          const ParmVarDecl *B) {
  for (const auto &Pair : FCI.Aliases) {
    const auto *L = dyn_cast<DeclRefExpr>(Pair.first->IgnoreParenImpCasts());
    const auto *R = dyn_cast<DeclRefExpr>(Pair.second->IgnoreParenImpCasts());
    if (!L || !R)
      continue;
    const auto *LD = dyn_cast<ParmVarDecl>(L->getDecl());
    const auto *RD = dyn_cast<ParmVarDecl>(R->getDecl());
    if (!LD || !RD)
      continue;
    if ((LD == A && RD == B) || (LD == B && RD == A))
      return true;
  }
  return false;
}

static bool exprReferencesSpecCall(const VExpr *E, const std::string &Name) {
  if (!E)
    return false;
  if (E->K == VExpr::SpecCall &&
      static_cast<const VSpecCallExpr *>(E)->Callee == Name)
    return true;
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return exprReferencesSpecCall(B->Lhs.get(), Name) ||
           exprReferencesSpecCall(B->Rhs.get(), Name);
  }
  if (E->K == VExpr::UnaryOp)
    return exprReferencesSpecCall(static_cast<const VUnaryOpExpr *>(E)->Operand.get(),
                                Name);
  if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return exprReferencesSpecCall(C->Cond.get(), Name) ||
           exprReferencesSpecCall(C->Then.get(), Name) ||
           exprReferencesSpecCall(C->Else.get(), Name);
  }
  return false;
}

static bool vexprHasSpecCall(const VExpr *E) {
  if (!E)
    return false;
  if (E->K == VExpr::SpecCall)
    return true;
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return vexprHasSpecCall(B->Lhs.get()) || vexprHasSpecCall(B->Rhs.get());
  }
  if (E->K == VExpr::UnaryOp)
    return vexprHasSpecCall(static_cast<const VUnaryOpExpr *>(E)->Operand.get());
  if (E->K == VExpr::Old)
    return vexprHasSpecCall(static_cast<const VOldExpr *>(E)->Inner.get());
  if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return vexprHasSpecCall(C->Cond.get()) || vexprHasSpecCall(C->Then.get()) ||
           vexprHasSpecCall(C->Else.get());
  }
  return false;
}

static bool fnReferencesSpec(const VFunction &Fn) {
  for (const auto &P : Fn.Preconditions)
    if (vexprHasSpecCall(P.get()))
      return true;
  for (const auto &P : Fn.Postconditions)
    if (vexprHasSpecCall(P.get()))
      return true;
  return false;
}

static bool bodyHasRecursiveSpec(const VFunction &Fn) {
  for (const auto &S : Fn.Body) {
    if (S->K == VStmt::Assign &&
        exprReferencesSpecCall(static_cast<const VAssignStmt &>(*S).Value.get(),
                               Fn.Name))
      return true;
    if (S->K == VStmt::Return &&
        exprReferencesSpecCall(static_cast<const VReturnStmt &>(*S).Value.get(),
                               Fn.Name))
      return true;
  }
  return false;
}

std::vector<std::unique_ptr<VFunction>>
ASTConverter::convertTranslationUnit() {
  std::vector<std::unique_ptr<VFunction>> Out;
  llvm::StringSet<> Names;
  for (const auto *D : Ctx.getTranslationUnitDecl()->decls()) {
    const auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD || !FD->isThisDeclarationADefinition() || FD->isTemplated())
      continue;
    if (FD->isInStdNamespace())
      continue;
    auto Fn = convertFunction(FD);
    if (Fn) {
      Names.insert(Fn->Name);
      Out.push_back(std::move(Fn));
    }
  }
  for (const auto *D : Ctx.getTranslationUnitDecl()->decls()) {
    const auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD || !FD->isThisDeclarationADefinition() || FD->isTemplated())
      continue;
    if (FD->isInStdNamespace() || Names.contains(FD->getName()))
      continue;
    if (!FD->isConstexpr() || !FD->hasBody())
      continue;
    if (Ctx.getFunctionContract(FD))
      continue;
    auto Fn = convertConstexprSpec(FD);
    if (Fn) {
      Names.insert(Fn->Name);
      Out.push_back(std::move(Fn));
    }
  }
  for (auto &Fn : Out) {
    if (!Fn->IsSpec && !Fn->IsProof)
      continue;
    bool Recursive = bodyHasRecursiveSpec(*Fn);
    for (const auto &S : Fn->Body)
      if (S->K == VStmt::Call &&
          static_cast<const VCallStmt &>(*S).Callee == Fn->Name)
        Recursive = true;
    Fn->NeedsDecreasesCheck = Fn->Decreases != nullptr && Recursive;
  }
  return Out;
}

std::unique_ptr<VFunction>
ASTConverter::convertFunction(const FunctionDecl *FD) {
  const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD);
  if (!FCI)
    return nullptr;

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  Fn->IsSpec = FCI->IsSpec;
  Fn->IsProof = FCI->IsProof;
  IntMode = FCI->IsSpec ? VIntMode::Math : VIntMode::Machine;
  if (!FCI->IsSpec && contractsReferenceSpec(*FCI))
    IntMode = VIntMode::Math;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode);
  CurrentFn = Fn.get();
  if (FCI->Decreases)
    Fn->Decreases = convertExpr(FCI->Decreases);

  SmallVector<const ParmVarDecl *, 8> MutablePtrParams;
  for (const ParmVarDecl *P : FD->parameters()) {
    Fn->Params.emplace_back(P->getNameAsString(),
                            VType::fromQualType(P->getType(), IntMode));
    if (isMutablePointerParam(P))
      MutablePtrParams.push_back(P);
  }

  auto recordContractExpr = [&](const char *Clause, const Expr *E,
                                std::unique_ptr<VExpr> &Out) {
    if (!E)
      return;
    Out = convertExpr(E);
    if (!Out)
      Errors.push_back(Fn->Name + ": unsupported expression in " + Clause);
  };

  InPost = false;
  for (const Expr *E : FCI->Preconditions) {
    std::unique_ptr<VExpr> PE;
    recordContractExpr("pre", E, PE);
    if (PE)
      Fn->Preconditions.push_back(std::move(PE));
  }
  InPost = true;
  for (const Expr *E : FCI->Postconditions) {
    std::unique_ptr<VExpr> PE;
    recordContractExpr("post", E, PE);
    if (PE)
      Fn->Postconditions.push_back(std::move(PE));
  }
  InPost = false;
  for (const Expr *E : FCI->Recommends) {
    std::unique_ptr<VExpr> RE;
    recordContractExpr("recommends", E, RE);
    if (RE)
      Fn->Recommends.push_back(std::move(RE));
  }
  for (const Expr *E : FCI->Modifies) {
    std::unique_ptr<VExpr> ME;
    recordContractExpr("modifies", E, ME);
    if (ME)
      Fn->Modifies.push_back(std::move(ME));
  }
  for (const auto &Pair : FCI->Aliases) {
    std::unique_ptr<VExpr> L;
    std::unique_ptr<VExpr> R;
    recordContractExpr("aliases", Pair.first, L);
    recordContractExpr("aliases", Pair.second, R);
    if (L && R)
      Fn->Aliases.emplace_back(std::move(L), std::move(R));
  }
  InPost = false;

  // Implicit non-aliasing between distinct mutable pointer parameters.
  for (unsigned I = 0; I < MutablePtrParams.size(); ++I) {
    for (unsigned J = I + 1; J < MutablePtrParams.size(); ++J) {
      if (aliasesListed(*FCI, MutablePtrParams[I], MutablePtrParams[J]))
        continue;
      auto A = std::make_unique<VVarExpr>(MutablePtrParams[I]->getNameAsString(),
                                          VType::makePtr(), SourceLocation());
      auto B = std::make_unique<VVarExpr>(MutablePtrParams[J]->getNameAsString(),
                                          VType::makePtr(), SourceLocation());
      auto Zero = std::make_unique<VLiteralExpr>(0, VType::makePtr(), SourceLocation());
      auto Ne = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, std::move(A), std::move(B), VType::makeBool(), SourceLocation());
      Fn->Preconditions.push_back(std::move(Ne));
      (void)Zero;
    }
  }

  if (const Stmt *Body = FD->getBody()) {
    Fn->Body = convertStmt(Body);
    if (!Fn->IsSpec && Fn->Body.empty() && Fn->Postconditions.empty())
      return nullptr;
  }
  if (Fn->IsSpec && Fn->Body.empty() && !Fn->Decreases)
    return nullptr;
  CurrentFn = nullptr;
  return Fn;
}

std::unique_ptr<VFunction>
ASTConverter::convertConstexprSpec(const FunctionDecl *FD) {
  if (!FD->isConstexpr() || !FD->hasBody())
    return nullptr;

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  Fn->IsSpec = true;
  Fn->IsConstexprSpec = true;
  IntMode = VIntMode::Machine;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode);
  CurrentFn = Fn.get();

  for (const ParmVarDecl *P : FD->parameters())
    Fn->Params.emplace_back(P->getNameAsString(),
                            VType::fromQualType(P->getType(), IntMode));

  if (const Stmt *Body = FD->getBody())
    Fn->Body = convertStmt(Body);
  if (Fn->Body.empty())
    return nullptr;
  CurrentFn = nullptr;
  return Fn;
}

VBinOp ASTConverter::convertBinOpcode(BinaryOperatorKind Op) {
  switch (Op) {
  case BO_LT: return VBinOp::Lt;
  case BO_LE: return VBinOp::Le;
  case BO_GT: return VBinOp::Gt;
  case BO_GE: return VBinOp::Ge;
  case BO_EQ: return VBinOp::Eq;
  case BO_NE: return VBinOp::Ne;
  case BO_Add: return VBinOp::Add;
  case BO_Sub: return VBinOp::Sub;
  case BO_Mul: return VBinOp::Mul;
  case BO_Div: return VBinOp::Div;
  case BO_Rem: return VBinOp::Rem;
  case BO_LAnd: return VBinOp::And;
  case BO_LOr: return VBinOp::Or;
  default: return VBinOp::Eq;
  }
}

std::unique_ptr<VExpr> ASTConverter::convertExpr(const Expr *E) {
  if (!E)
    return nullptr;
  E = E->IgnoreParenImpCasts();
  while (const auto *CE = dyn_cast<CastExpr>(E)) {
    if (CE->getCastKind() == CK_NoOp || CE->getCastKind() == CK_LValueToRValue ||
        CE->getCastKind() == CK_ConstructorConversion ||
        CE->getCastKind() == CK_UncheckedDerivedToBase)
      E = CE->getSubExpr()->IgnoreParenImpCasts();
    else
      break;
  }

  if (const auto *MTE = dyn_cast<MaterializeTemporaryExpr>(E))
    return convertExpr(MTE->getSubExpr());
  if (const auto *CE = dyn_cast<CXXConstructExpr>(E)) {
    if (CE->getNumArgs() == 1)
      return convertExpr(CE->getArg(0));
    if (CE->getNumArgs() == 0 && CE->getConstructor()->isDefaultConstructor())
      return nullptr;
  }
  if (const auto *IL = dyn_cast<IntegerLiteral>(E)) {
    VType Ty = VType::fromQualType(E->getType(), IntMode);
    return std::make_unique<VLiteralExpr>(IL->getValue().getSExtValue(), Ty,
                                          E->getExprLoc());
  }
  if (isa<CXXNullPtrLiteralExpr>(E)) {
    return std::make_unique<VLiteralExpr>(0, VType::makePtr(), E->getExprLoc());
  }
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VVarExpr>(VD->getNameAsString(), Ty,
                                        E->getExprLoc());
    }
    if (const auto *PD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VVarExpr>(PD->getNameAsString(), Ty,
                                        E->getExprLoc());
    }
  }
  if (const auto *U = dyn_cast<UnaryOperator>(E)) {
    if (U->getOpcode() == UO_Deref) {
      auto Ptr = convertExpr(U->getSubExpr());
      if (!Ptr)
        return nullptr;
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VLoadExpr>(std::move(Ptr), Ty, E->getExprLoc());
    }
    auto Op = convertExpr(U->getSubExpr());
    if (!Op)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode);
    if (U->getOpcode() == UO_Minus)
      return std::make_unique<VUnaryOpExpr>(VUnaryOp::Neg, std::move(Op), Ty,
                                            E->getExprLoc());
    if (U->getOpcode() == UO_LNot)
      return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(Op), Ty,
                                            E->getExprLoc());
  }
  if (const auto *B = dyn_cast<BinaryOperator>(E)) {
    auto L = convertExpr(B->getLHS());
    auto R = convertExpr(B->getRHS());
    if (!L || !R)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode);
    return std::make_unique<VBinOpExpr>(convertBinOpcode(B->getOpcode()),
                                        std::move(L), std::move(R), Ty,
                                        E->getExprLoc());
  }
  if (const auto *ICE = dyn_cast<ImplicitCastExpr>(E)) {
    auto Inner = convertExpr(ICE->getSubExpr());
    if (!Inner)
      return nullptr;
    VType To = VType::fromQualType(E->getType(), IntMode);
    return std::make_unique<VCastExpr>(std::move(Inner), Inner->Ty, To,
                                       E->getExprLoc());
  }
  if (const auto *CE = dyn_cast<CStyleCastExpr>(E)) {
    auto Inner = convertExpr(CE->getSubExpr());
    if (!Inner)
      return nullptr;
    VType To = VType::fromQualType(E->getType(), IntMode);
    return std::make_unique<VCastExpr>(std::move(Inner), Inner->Ty, To,
                                       E->getExprLoc());
  }
  if (const auto *O = dyn_cast<OldExpr>(E)) {
    bool Saved = InPost;
    InPost = true;
    auto Inner = convertExpr(O->getInner());
    InPost = Saved;
    if (!Inner)
      return nullptr;
    return std::make_unique<VOldExpr>(std::move(Inner), Inner->Ty,
                                      E->getExprLoc());
  }
  if (const auto *C = dyn_cast<ConditionalOperator>(E)) {
    auto Cond = convertExpr(C->getCond());
    auto T = convertExpr(C->getTrueExpr());
    auto F = convertExpr(C->getFalseExpr());
    if (!Cond || !T || !F)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode);
    return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(T),
                                              std::move(F), Ty, E->getExprLoc());
  }
  if (const auto *M = dyn_cast<MemberExpr>(E)) {
    if (M->isArrow()) {
      auto Base = convertExpr(M->getBase());
      if (!Base)
        return nullptr;
      auto Ptr = std::make_unique<VLoadExpr>(std::move(Base),
                                             VType::fromQualType(M->getBase()->getType(), IntMode),
                                             E->getExprLoc());
      if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
        VType Ty = VType::fromQualType(E->getType(), IntMode);
        return std::make_unique<VLoadExpr>(std::move(Ptr), Ty, E->getExprLoc());
      }
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(M->getBase()->IgnoreParenImpCasts())) {
      if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
          VType Ty = VType::fromQualType(E->getType(), IntMode);
          std::string Name = VD->getNameAsString() + "." + FD->getNameAsString();
          return std::make_unique<VVarExpr>(Name, Ty, E->getExprLoc());
        }
      }
      if (const auto *PD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
        if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
          VType Ty = VType::fromQualType(E->getType(), IntMode);
          std::string Name = PD->getNameAsString() + "." + FD->getNameAsString();
          return std::make_unique<VVarExpr>(Name, Ty, E->getExprLoc());
        }
      }
    }
    if (InPost && isa<ResultExpr>(M->getBase()->IgnoreParenImpCasts())) {
      if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
        VType Ty = VType::fromQualType(E->getType(), IntMode);
        return std::make_unique<VVarExpr>("result." + FD->getNameAsString(), Ty,
                                          E->getExprLoc());
      }
    }
    auto Base = convertExpr(M->getBase());
    if (!Base)
      return nullptr;
    if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VFieldAccessExpr>(std::move(Base), FD->getNameAsString(), Ty,
                                                E->getExprLoc());
    }
  }
  if (dyn_cast<ResultExpr>(E)) {
    if (!InPost)
      return nullptr;
    return std::make_unique<VResultExpr>(
        VType::fromQualType(E->getType(), IntMode), E->getExprLoc());
  }
  if (const auto *F = dyn_cast<ForallExpr>(E)) {
    std::string Binder = F->getBoundVar() ? F->getBoundVar()->getNameAsString()
                                          : "i";
    return std::make_unique<VForallExpr>(
        Binder, convertExpr(F->getLo()), convertExpr(F->getHi()),
        convertExpr(F->getBody()), E->getExprLoc());
  }
  if (const auto *Ex = dyn_cast<ExistsExpr>(E)) {
    std::string Binder = Ex->getBoundVar() ? Ex->getBoundVar()->getNameAsString()
                                           : "i";
    return std::make_unique<VExistsExpr>(
        Binder, convertExpr(Ex->getLo()), convertExpr(Ex->getHi()),
        convertExpr(Ex->getBody()), E->getExprLoc());
  }
  if (const auto *CE = dyn_cast<CallExpr>(E)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if (Callee->isConstexpr() && CE->isEvaluatable(Ctx)) {
        Expr::EvalResult EV;
        if (CE->EvaluateAsInt(EV, Ctx)) {
          VType Ty = VType::fromQualType(E->getType(), VIntMode::Machine);
          return std::make_unique<VLiteralExpr>(EV.Val.getInt().getSExtValue(), Ty,
                                                E->getExprLoc());
        }
      }
      if (calleeIsSpec(Callee)) {
        std::vector<std::unique_ptr<VExpr>> Args;
        for (const Expr *A : CE->arguments())
          if (auto AE = convertExpr(A))
            Args.push_back(std::move(AE));
        VType Ty = VType::fromQualType(E->getType(), specCallIntMode(Callee));
        return std::make_unique<VSpecCallExpr>(Callee->getNameAsString(),
                                               std::move(Args), Ty, E->getExprLoc());
      }
    }
  }
  return nullptr;
}

void ASTConverter::convertExecCallArg(
    const Expr *E, std::vector<std::unique_ptr<VStmt>> &Prelude,
    std::unique_ptr<VExpr> &Out) {
  if (!E) {
    Out = nullptr;
    return;
  }
  E = E->IgnoreParenImpCasts();
  if (const auto *CE = dyn_cast<CallExpr>(E)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if (Ctx.getFunctionContract(Callee) && !calleeIsSpec(Callee) &&
          !calleeIsProof(Callee)) {
        std::vector<std::unique_ptr<VExpr>> InnerArgs;
        convertExecCallArgs(CE, Prelude, InnerArgs);
        std::string Tmp = "__nested_" + std::to_string(++NestedCallId);
        Out = std::make_unique<VVarExpr>(
            Tmp, VType::fromQualType(E->getType(), IntMode), E->getExprLoc());
        Prelude.push_back(std::make_unique<VCallStmt>(
            Callee->getNameAsString(), std::move(InnerArgs), Tmp,
            E->getExprLoc(), false));
        return;
      }
    }
  }
  Out = convertExpr(E);
}

void ASTConverter::convertExecCallArgs(const CallExpr *CE,
                                       std::vector<std::unique_ptr<VStmt>> &Prelude,
                                       std::vector<std::unique_ptr<VExpr>> &Args) {
  if (!CE)
    return;
  for (const Expr *A : CE->arguments()) {
    std::unique_ptr<VExpr> Arg;
    convertExecCallArg(A, Prelude, Arg);
    if (Arg)
      Args.push_back(std::move(Arg));
  }
}

std::vector<std::unique_ptr<VStmt>>
ASTConverter::convertStmt(const Stmt *S) {
  std::vector<std::unique_ptr<VStmt>> Out;
  if (!S)
    return Out;

  if (const auto *CS = dyn_cast<CompoundStmt>(S)) {
    for (const Stmt *Child : CS->body()) {
      auto Part = convertStmt(Child);
      Out.insert(Out.end(), std::make_move_iterator(Part.begin()),
                 std::make_move_iterator(Part.end()));
    }
    return Out;
  }
  if (S->getStmtClass() == Stmt::ReturnStmtClass) {
    const auto *RS = cast<ReturnStmt>(S);
    if (const Expr *RetE = RS->getRetValue()) {
      const auto *CE = dyn_cast<CallExpr>(RetE->IgnoreParenImpCasts());
      if (CE) {
        if (const FunctionDecl *Callee = CE->getDirectCallee()) {
          if (Ctx.getFunctionContract(Callee) && !calleeIsSpec(Callee) &&
              !calleeIsProof(Callee)) {
            std::vector<std::unique_ptr<VExpr>> Args;
            convertExecCallArgs(CE, Out, Args);
            Out.push_back(std::make_unique<VCallStmt>(
                Callee->getNameAsString(), std::move(Args), "result",
                RS->getBeginLoc(), false));
            Out.push_back(std::make_unique<VReturnStmt>(
                std::make_unique<VVarExpr>(
                    "result", VType::fromQualType(RS->getRetValue()->getType(), IntMode),
                    RS->getBeginLoc()),
                RS->getBeginLoc()));
            return Out;
          }
        }
      }
    }
    std::unique_ptr<VExpr> Val;
    if (RS->getRetValue())
      Val = convertExpr(RS->getRetValue());
    Out.push_back(
        std::make_unique<VReturnStmt>(std::move(Val), RS->getBeginLoc()));
    return Out;
  }
  if (const auto *IS = dyn_cast<IfStmt>(S)) {
    auto Cond = convertExpr(IS->getCond());
    if (!Cond)
      return Out;
    auto Then = convertStmt(IS->getThen());
    std::vector<std::unique_ptr<VStmt>> Else;
    if (IS->getElse())
      Else = convertStmt(IS->getElse());
    Out.push_back(std::make_unique<VIfStmt>(std::move(Cond), std::move(Then),
                                            std::move(Else), IS->getBeginLoc()));
    return Out;
  }
  if (const auto *WS = dyn_cast<WhileStmt>(S)) {
    auto Cond = convertExpr(WS->getCond());
    if (!Cond)
      return Out;
    std::vector<std::unique_ptr<VExpr>> Invariants;
    std::unique_ptr<VExpr> Decreases;
    if (const LoopContractInfo *LCI = Ctx.getLoopContract(WS)) {
      for (const Expr *Inv : LCI->Invariants)
        if (auto E = convertExpr(Inv))
          Invariants.push_back(std::move(E));
      if (LCI->Decreases)
        Decreases = convertExpr(LCI->Decreases);
    }
    auto Body = convertStmt(WS->getBody());
    Out.push_back(std::make_unique<VWhileStmt>(std::move(Cond), std::move(Invariants),
                                               std::move(Decreases), std::move(Body),
                                               WS->getBeginLoc()));
    return Out;
  }
  if (const auto *FS = dyn_cast<ForStmt>(S)) {
    if (FS->getInit()) {
      auto Init = convertStmt(FS->getInit());
      Out.insert(Out.end(), std::make_move_iterator(Init.begin()),
                 std::make_move_iterator(Init.end()));
    }
    auto Cond = convertExpr(FS->getCond());
    if (!Cond)
      return Out;
    std::vector<std::unique_ptr<VExpr>> Invariants;
    std::unique_ptr<VExpr> Decreases;
    if (const LoopContractInfo *LCI = Ctx.getLoopContract(FS)) {
      for (const Expr *Inv : LCI->Invariants)
        if (auto E = convertExpr(Inv))
          Invariants.push_back(std::move(E));
      if (LCI->Decreases)
        Decreases = convertExpr(LCI->Decreases);
    }
    auto Body = convertStmt(FS->getBody());
    if (const Expr *Inc = FS->getInc()) {
      if (const auto *IncStmt = dyn_cast<Stmt>(Inc)) {
        auto IncPart = convertStmt(IncStmt);
        Body.insert(Body.end(), std::make_move_iterator(IncPart.begin()),
                    std::make_move_iterator(IncPart.end()));
      }
    }
    Out.push_back(std::make_unique<VWhileStmt>(std::move(Cond), std::move(Invariants),
                                               std::move(Decreases), std::move(Body),
                                               FS->getBeginLoc()));
    return Out;
  }
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if (calleeIsSpec(Callee))
        return Out;
      if (Ctx.getFunctionContract(Callee)) {
        std::vector<std::unique_ptr<VExpr>> Args;
        convertExecCallArgs(CE, Out, Args);
        bool IsProof = calleeIsProof(Callee);
        Out.push_back(std::make_unique<VCallStmt>(
            Callee->getNameAsString(), std::move(Args), "", CE->getExprLoc(),
            IsProof));
      }
    }
    return Out;
  }
  if (const auto *GB = dyn_cast<GhostBlockStmt>(S)) {
    bool SavedGhost = InGhost;
    InGhost = true;
    auto Body = convertStmt(GB->getBody());
    InGhost = SavedGhost;
    Out.push_back(std::make_unique<VGhostBlockStmt>(std::move(Body), GB->getBeginLoc()));
    return Out;
  }
  if (const auto *RW = dyn_cast<RevealWithFuelStmt>(S)) {
    std::string SpecName = specNameFromExpr(RW->getFunction());
    unsigned FuelVal = 1;
    if (const auto *IL = dyn_cast<IntegerLiteral>(RW->getFuel()))
      FuelVal = static_cast<unsigned>(IL->getValue().getZExtValue());
    if (CurrentFn && !SpecName.empty()) {
      CurrentFn->SpecFuel[SpecName] = std::max(CurrentFn->SpecFuel[SpecName], FuelVal);
      CurrentFn->RevealedSpecs.insert(SpecName);
    }
    Out.push_back(std::make_unique<VRevealWithFuelStmt>(SpecName, FuelVal, RW->getBeginLoc()));
    return Out;
  }
  if (const auto *H = dyn_cast<HideSpecStmt>(S)) {
    std::string SpecName = specNameFromExpr(H->getFunction());
    if (CurrentFn && !SpecName.empty())
      CurrentFn->HiddenSpecs.insert(SpecName);
    Out.push_back(std::make_unique<VHideSpecStmt>(SpecName, H->getBeginLoc()));
    return Out;
  }
  if (const auto *R = dyn_cast<RevealSpecStmt>(S)) {
    std::string SpecName = specNameFromExpr(R->getFunction());
    if (CurrentFn && !SpecName.empty()) {
      CurrentFn->RevealedSpecs.insert(SpecName);
      CurrentFn->SpecFuel[SpecName] = std::max(CurrentFn->SpecFuel[SpecName], 1u);
    }
    Out.push_back(std::make_unique<VRevealSpecStmt>(SpecName, R->getBeginLoc()));
    return Out;
  }
  if (const auto *CA = dyn_cast<ContractAssertStmt>(S)) {
    if (auto C = convertExpr(CA->getCond()))
      Out.push_back(std::make_unique<VContractAssertStmt>(std::move(C), CA->getBeginLoc()));
    return Out;
  }
  if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->isAssignmentOp()) {
      if (const auto *DRE = dyn_cast<DeclRefExpr>(BO->getLHS()->IgnoreParenImpCasts())) {
        if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
          auto Val = convertExpr(BO->getRHS());
          if (Val)
            Out.push_back(std::make_unique<VAssignStmt>(
                VD->getNameAsString(), std::move(Val), BO->getExprLoc()));
        }
      } else if (const auto *ME = dyn_cast<MemberExpr>(BO->getLHS()->IgnoreParenImpCasts())) {
        if (auto L = convertExpr(ME)) {
          std::string Target;
          if (L->K == VExpr::FieldAccess)
            Target = static_cast<const VFieldAccessExpr *>(L.get())->Field;
          if (const auto *FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
            std::string BaseName;
            if (const auto *DRE = dyn_cast<DeclRefExpr>(ME->getBase()->IgnoreParenImpCasts()))
              if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
                BaseName = VD->getNameAsString();
            if (!BaseName.empty()) {
              auto Val = convertExpr(BO->getRHS());
              if (Val)
                Out.push_back(std::make_unique<VAssignStmt>(
                    BaseName + "." + FD->getNameAsString(), std::move(Val), BO->getExprLoc()));
            }
          }
        }
      } else if (const auto *U = dyn_cast<UnaryOperator>(
                     BO->getLHS()->IgnoreParenImpCasts())) {
        if (U->getOpcode() == UO_Deref) {
          auto Ptr = convertExpr(U->getSubExpr());
          auto Val = convertExpr(BO->getRHS());
          if (Ptr && Val)
            Out.push_back(std::make_unique<VStoreStmt>(
                std::move(Ptr), std::move(Val), BO->getExprLoc()));
        }
      }
    }
    return Out;
  }
  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    for (const Decl *D : DS->decls()) {
      const auto *VD = dyn_cast<VarDecl>(D);
      if (!VD || !VD->hasInit())
        continue;
      if (const auto *CE = dyn_cast<CallExpr>(VD->getInit())) {
        if (const FunctionDecl *Callee = CE->getDirectCallee()) {
          if (calleeIsSpec(Callee)) {
            if (auto Val = convertExpr(CE)) {
              Out.push_back(std::make_unique<VAssignStmt>(VD->getNameAsString(),
                                                            std::move(Val),
                                                            VD->getBeginLoc()));
            }
            continue;
          }
          if (Ctx.getFunctionContract(Callee)) {
            std::vector<std::unique_ptr<VExpr>> Args;
            convertExecCallArgs(CE, Out, Args);
            Out.push_back(std::make_unique<VCallStmt>(
                Callee->getNameAsString(), std::move(Args), VD->getNameAsString(),
                VD->getBeginLoc(), calleeIsProof(Callee)));
            continue;
          }
        }
      }
      auto Val = convertExpr(VD->getInit());
      if (Val)
        Out.push_back(std::make_unique<VAssignStmt>(VD->getNameAsString(),
                                                    std::move(Val),
                                                    VD->getBeginLoc()));
    }
    return Out;
  }
  return Out;
}