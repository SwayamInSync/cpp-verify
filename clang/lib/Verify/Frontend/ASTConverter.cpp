//===--- ASTConverter.cpp -------------------------------------------------===//
#include "ASTConverter.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"

using namespace clang;
using namespace verify;

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

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  IntMode = FCI->IsSpec ? VIntMode::Math : VIntMode::Machine;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode);

  for (const ParmVarDecl *P : FD->parameters()) {
    Fn->Params.emplace_back(P->getNameAsString(),
                            VType::fromQualType(P->getType(), IntMode));
  }

  InPost = true;
  for (const Expr *E : FCI->Preconditions)
    Fn->Preconditions.push_back(convertExpr(E));
  for (const Expr *E : FCI->Postconditions)
    Fn->Postconditions.push_back(convertExpr(E));
  InPost = false;

  if (const Stmt *Body = FD->getBody()) {
    Fn->Body = convertStmt(Body);
    if (Fn->Body.empty())
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
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VVarExpr>(VD->getNameAsString(), Ty,
                                        E->getExprLoc());
    }
  }
  if (const auto *U = dyn_cast<UnaryOperator>(E)) {
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
    auto Inner = convertExpr(O->getInner());
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
  if (const auto *U = dyn_cast<UnaryOperator>(E)) {
    if (U->getOpcode() == UO_Deref) {
      auto Ptr = convertExpr(U->getSubExpr());
      if (!Ptr)
        return nullptr;
      VType Ty = VType::fromQualType(E->getType(), IntMode);
      return std::make_unique<VLoadExpr>(std::move(Ptr), Ty, E->getExprLoc());
    }
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