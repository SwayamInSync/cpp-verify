//===--- ASTConverter.h - Clang AST to VCR IR -------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H
#define LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H

#include "../IR/VStmt.h"
#include "clang/AST/ASTContext.h"

namespace clang {
namespace verify {

class ASTConverter {
  ASTContext &Ctx;
  VIntMode IntMode = VIntMode::Machine;
  bool InPost = false;
  bool InGhost = false;
  std::string ResultName = "result";
  VFunction *CurrentFn = nullptr;
  unsigned NestedCallId = 0;

public:
  explicit ASTConverter(ASTContext &Ctx) : Ctx(Ctx) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();

private:
  std::unique_ptr<VFunction> convertFunction(const FunctionDecl *FD);
  std::unique_ptr<VFunction> convertConstexprSpec(const FunctionDecl *FD);
  std::unique_ptr<VExpr> convertExpr(const Expr *E);
  std::vector<std::unique_ptr<VStmt>> convertStmt(const Stmt *S);
  void convertExecCallArgs(const CallExpr *CE,
                           std::vector<std::unique_ptr<VStmt>> &Prelude,
                           std::vector<std::unique_ptr<VExpr>> &Args);
  void convertExecCallArg(const Expr *E,
                          std::vector<std::unique_ptr<VStmt>> &Prelude,
                          std::unique_ptr<VExpr> &Out);
  VBinOp convertBinOpcode(BinaryOperatorKind Op);
  bool calleeIsSpec(const FunctionDecl *FD) const;
  bool calleeIsProof(const FunctionDecl *FD) const;
  VIntMode specCallIntMode(const FunctionDecl *FD) const;
  bool contractsReferenceSpec(const FunctionContractInfo &FCI) const;
  static std::string specNameFromExpr(const Expr *E);
};

} // namespace verify
} // namespace clang

#endif