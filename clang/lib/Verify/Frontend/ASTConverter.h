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
  std::string ResultName = "result";

public:
  explicit ASTConverter(ASTContext &Ctx) : Ctx(Ctx) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();

private:
  std::unique_ptr<VFunction> convertFunction(const FunctionDecl *FD);
  std::unique_ptr<VExpr> convertExpr(const Expr *E);
  std::vector<std::unique_ptr<VStmt>> convertStmt(const Stmt *S);
  VBinOp convertBinOpcode(BinaryOperatorKind Op);
};

} // namespace verify
} // namespace clang

#endif