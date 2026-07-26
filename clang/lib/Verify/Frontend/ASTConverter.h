//===--- ASTConverter.h - Clang AST to VCR IR -------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H
#define LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H

#include "../IR/VStmt.h"
#include "clang/AST/ASTContext.h"
#include <optional>
#include <set>

namespace clang {
namespace verify {

class ASTConverter {
  ASTContext &Ctx;
  VIntMode IntMode = VIntMode::Machine;
  bool InPost = false;
  bool InOld = false;
  bool InGhost = false;
  bool InContractExpression = false;
  std::string ResultName = "result";
  VFunction *CurrentFn = nullptr;
  unsigned NestedCallId = 0;
  std::vector<std::string> Errors;
  /// Maps unqualified field name -> "param." for type_invariant lowering.
  std::map<std::string, std::string> FieldSubstPrefix;
  bool TrackInitialization = false;
  bool InitializationPathReachable = true;
  std::set<std::string> DeclaredValueNames;
  std::set<std::string> InitializedValues;
  std::set<std::string> ReportedUninitializedValues;
  std::map<const ValueDecl *, std::string> BoundValues;
  std::map<const ParmVarDecl *, std::string> ParameterNames;
  unsigned BoundValueId = 0;
  std::map<const FunctionDecl *, std::string> FunctionIdentities;

public:
  explicit ASTConverter(ASTContext &Ctx) : Ctx(Ctx) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();
  const std::vector<std::string> &getErrors() const { return Errors; }

private:
  std::unique_ptr<VFunction> convertFunction(const FunctionDecl *FD);
  std::unique_ptr<VFunction> convertConstexprSpec(const FunctionDecl *FD);
  std::unique_ptr<VExpr> convertExpr(const Expr *E);
  std::unique_ptr<VExpr> convertRecordField(std::unique_ptr<VExpr> Base,
                                            const FieldDecl *Field,
                                            SourceLocation Loc);
  std::unique_ptr<VExpr> convertArrowFieldAddress(const MemberExpr *M);
  std::vector<std::unique_ptr<VStmt>> convertStmt(const Stmt *S);
  void convertExecCallArgs(const CallExpr *CE,
                           std::vector<std::unique_ptr<VStmt>> &Prelude,
                           std::vector<std::unique_ptr<VExpr>> &Args);
  void convertExecCallArg(const Expr *E,
                          std::vector<std::unique_ptr<VStmt>> &Prelude,
                          std::unique_ptr<VExpr> &Out);
  std::unique_ptr<VExpr> convertCallResultValue(std::string Name,
                                                QualType SourceType,
                                                const VType &TargetType,
                                                SourceLocation Loc);
  bool appendRecordCallArgument(const Expr *E, const ParmVarDecl *Formal,
                                std::vector<std::unique_ptr<VExpr>> &Args);
  std::unique_ptr<VExpr>
  convertAssignmentValue(const BinaryOperator *Assignment);
  void appendAssignment(const Expr *LHS, std::unique_ptr<VExpr> Value,
                        SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  bool appendRecordCopy(const Expr *Source, const VarDecl *Target,
                        SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  bool appendRecordInitializer(const InitListExpr *Init, const VarDecl *Target,
                               SourceLocation Loc,
                               std::vector<std::unique_ptr<VStmt>> &Out);
  std::optional<VBinOp> convertBinOpcode(BinaryOperatorKind Op);
  const FunctionContractInfo *functionContract(const FunctionDecl *FD) const;
  bool calleeIsSpec(const FunctionDecl *FD) const;
  bool calleeIsProof(const FunctionDecl *FD) const;
  VIntMode specCallIntMode(const FunctionDecl *FD) const;
  std::string functionIdentity(const FunctionDecl *FD);
  std::string specIdentityFromExpr(const Expr *E);
  void injectTypeInvariants(const FunctionDecl *FD, VFunction &Fn);
  std::unique_ptr<VExpr> convertTypeInvariantExpr(const Expr *E);
  void emitReturnInvariantAssert(const Expr *RetE,
                                 std::vector<std::unique_ptr<VStmt>> &Out,
                                 SourceLocation Loc);
  std::vector<std::string> trackedValueNames(const ValueDecl *D) const;
  std::string valueName(const ValueDecl *D) const;
  void beginInitializationTracking(const FunctionDecl *FD);
  bool requireInitialized(const ValueDecl *D, const FieldDecl *Field = nullptr);
  void markInitialized(const ValueDecl *D, const FieldDecl *Field = nullptr);
};

} // namespace verify
} // namespace clang

#endif