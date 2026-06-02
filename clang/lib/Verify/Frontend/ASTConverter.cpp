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

using namespace clang;
using namespace verify;

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

std::vector<std::unique_ptr<VFunction>>
ASTConverter::convertTranslationUnit() {
  std::vector<std::unique_ptr<VFunction>> Out;
  for (const auto *D : Ctx.getTranslationUnitDecl()->decls()) {
    const auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD || !FD->isThisDeclarationADefinition() || FD->isTemplated())
      continue;
    if (FD->isInStdNamespace())
      continue;
    auto Fn = convertFunction(FD);
    if (Fn)
      Out.push_back(std::move(Fn));
  }
  return Out;
}

std::unique_ptr<VFunction>
ASTConverter::convertFunction(const FunctionDecl *FD) {
  const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD);
  if (!FCI)
    return nullptr;
  if (FCI->IsSpec || FCI->IsProof)
    return nullptr;

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  IntMode = FCI->IsSpec ? VIntMode::Math : VIntMode::Machine;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode);

  SmallVector<const ParmVarDecl *, 8> MutablePtrParams;
  for (const ParmVarDecl *P : FD->parameters()) {
    Fn->Params.emplace_back(P->getNameAsString(),
                            VType::fromQualType(P->getType(), IntMode));
    if (isMutablePointerParam(P))
      MutablePtrParams.push_back(P);
  }

  InPost = false;
  for (const Expr *E : FCI->Preconditions)
    Fn->Preconditions.push_back(convertExpr(E));
  for (const Expr *E : FCI->Postconditions)
    Fn->Postconditions.push_back(convertExpr(E));
  for (const Expr *E : FCI->Recommends)
    Fn->Recommends.push_back(convertExpr(E));
  for (const Expr *E : FCI->Modifies)
    Fn->Modifies.push_back(convertExpr(E));
  for (const auto &Pair : FCI->Aliases) {
    auto L = convertExpr(Pair.first);
    auto R = convertExpr(Pair.second);
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
    if (Fn->Body.empty() && Fn->Postconditions.empty())
      return nullptr;
  }
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
  return nullptr;
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
  if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->isAssignmentOp()) {
      if (const auto *DRE = dyn_cast<DeclRefExpr>(BO->getLHS()->IgnoreParenImpCasts())) {
        if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
          auto Val = convertExpr(BO->getRHS());
          if (Val)
            Out.push_back(std::make_unique<VAssignStmt>(
                VD->getNameAsString(), std::move(Val), BO->getExprLoc()));
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