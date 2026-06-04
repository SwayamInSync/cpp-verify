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
  std::vector<std::string> Errors;
  /// Maps unqualified field name -> "param." for type_invariant lowering.
  std::map<std::string, std::string> FieldSubstPrefix;

public:
  explicit ASTConverter(ASTContext &Ctx) : Ctx(Ctx) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();
  const std::vector<std::string> &getErrors() const { return Errors; }

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
  /// VType::fromQualType with this converter's ASTContext, so integer widths are
  /// taken from the target's data model (long = 64-bit on LP64, etc.).
  VType vtype(QualType QT, VIntMode M) const {
    return VType::fromQualType(QT, M, &Ctx);
  }
  void injectTypeInvariants(const FunctionDecl *FD, VFunction &Fn);
  std::unique_ptr<VExpr> convertTypeInvariantExpr(const Expr *E);
  /// If RetE is a struct variable whose type carries a type_invariant, append a
  /// contract_assert of that invariant (over the variable's fields) to Out, so a
  /// returned value is checked to satisfy its invariant.
  void emitReturnInvariantAssert(const Expr *RetE,
                                 std::vector<std::unique_ptr<VStmt>> &Out,
                                 SourceLocation Loc);
};

} // namespace verify
} // namespace clang

#endif