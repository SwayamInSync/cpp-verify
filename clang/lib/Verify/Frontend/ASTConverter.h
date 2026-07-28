//===--- ASTConverter.h - Clang AST to VCR IR -------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H
#define LLVM_CLANG_VERIFY_FRONTEND_ASTCONVERTER_H

#include "../IR/VPlace.h"
#include "../IR/VStmt.h"
#include "clang/AST/ASTContext.h"
#include "llvm/ADT/STLFunctionalExtras.h"
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
  std::set<std::string> FreshOwnedCalleeIdentities;
  std::set<const VarDecl *> DynamicPointers;
  std::map<const VarDecl *, std::string> DynamicPointerProvenanceVariables;
  std::set<const VarDecl *> AddressableLocals;
  std::map<const VarDecl *, std::string> AutomaticLocalProvenanceVariables;
  std::vector<std::vector<const VarDecl *>> AutomaticScopeStack;
  std::vector<const VarDecl *> ActiveAutomaticLocals;
  std::map<const VarDecl *, std::string> LocalReferenceProvenanceVariables;
  std::set<const VarDecl *> GhostLocals;
  unsigned DynamicProvenanceId = 0;
  unsigned DynamicPointerAssignmentId = 0;
  unsigned AutomaticStorageId = 0;
  unsigned LocalReferenceId = 0;
  unsigned LoopDepth = 0;

public:
  explicit ASTConverter(
      ASTContext &Ctx,
      const std::set<std::string> &FreshOwnedCalleeIdentities = {})
      : Ctx(Ctx), FreshOwnedCalleeIdentities(FreshOwnedCalleeIdentities) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();
  const std::vector<std::string> &getErrors() const { return Errors; }

private:
  std::unique_ptr<VFunction> convertFunction(const FunctionDecl *FD);
  std::unique_ptr<VFunction> convertConstexprSpec(const FunctionDecl *FD);
  std::unique_ptr<VExpr> convertExpr(const Expr *E);
  std::unique_ptr<VExpr> convertPointerDifferenceOperand(const Expr *E,
                                                         uint64_t PointeeSize);
  std::unique_ptr<VExpr>
  convertLValueAddress(const Expr *E,
                       std::unique_ptr<VExpr> *AccessCondition = nullptr);
  std::unique_ptr<VExpr>
  convertAutomaticLocalAddress(const VarDecl *VD, SourceLocation Loc,
                               bool RequireInitialized = true);
  /// Typed VPlace builders. The `convert*Address` helpers above are thin
  /// wrappers that lower these places to plain VLoad/VStore address
  /// expressions.
  std::optional<VPlace> lvaluePlace(const Expr *E);
  std::optional<VPlace> automaticLocalPlace(const VarDecl *VD,
                                            SourceLocation Loc,
                                            bool RequireInitialized = true);
  std::optional<VPlace> derefPlace(const Expr *PointerExpr, SourceLocation Loc);
  std::optional<VPlace> arrowFieldPlace(const MemberExpr *M);
  std::optional<VPlace> subscriptPlace(const ArraySubscriptExpr *AS);
  /// Root-object discovery: peel no-op casts, array-to-pointer decays, dot
  /// member chains and fixed-array subscripts down to the enclosing local
  /// object. Returns the root only when it was promoted to one automatic
  /// byte-addressed object.
  const VarDecl *promotedRootLocal(const Expr *E) const;
  /// Build the exact byte-offset place of a subobject of a promoted local.
  std::optional<VPlace> promotedObjectPlace(const Expr *E,
                                            bool RequireInitialized = true);
  std::optional<uint64_t> recordFieldOffset(const FieldDecl *FD) const;
  /// Visit every scalar/pointer leaf of a promoted object type in offset order.
  bool forEachObjectLeaf(QualType Ty, uint64_t Offset,
                         llvm::function_ref<bool(QualType, uint64_t)> Fn) const;
  std::unique_ptr<VExpr> objectLeafAddress(const VExpr *Base, uint64_t Offset,
                                           SourceLocation Loc) const;
  bool appendObjectInitialization(const Expr *Init, QualType Ty,
                                  const VExpr *Base, uint64_t Offset,
                                  SourceLocation Loc,
                                  std::vector<std::unique_ptr<VStmt>> &Out);
  bool appendObjectZeroInitialization(QualType Ty, const VExpr *Base,
                                      uint64_t Offset, SourceLocation Loc,
                                      std::vector<std::unique_ptr<VStmt>> &Out);
  bool appendObjectCopy(const Expr *Source, QualType Ty, const VExpr *Base,
                        uint64_t Offset, SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  std::unique_ptr<VExpr> recordFixedArrayBoundsCheck(const Expr *Index,
                                                     const VExpr *IndexValue,
                                                     uint64_t Count,
                                                     SourceLocation Loc);
  std::unique_ptr<VExpr> convertAddressProvenance(const VExpr *Address);
  void appendReferenceBindingCheck(const Expr *Source, const VExpr *Address,
                                   SourceLocation Loc,
                                   std::vector<std::unique_ptr<VStmt>> &Out);
  std::unique_ptr<VExpr> convertRecordField(std::unique_ptr<VExpr> Base,
                                            const FieldDecl *Field,
                                            SourceLocation Loc);
  std::unique_ptr<VExpr> convertArrowFieldAddress(const MemberExpr *M);
  std::unique_ptr<VExpr> convertSubscriptAddress(const ArraySubscriptExpr *AS);
  std::vector<std::unique_ptr<VStmt>> convertStmt(const Stmt *S);
  std::vector<std::unique_ptr<VStmt>> convertStmtBody(const Stmt *S);
  std::vector<std::unique_ptr<VStmt>> convertScopedSubstatement(const Stmt *S);
  void enterAutomaticScope();
  void registerAutomaticLocal(const VarDecl *VD);
  void appendActiveLifetimeEnds(std::vector<std::unique_ptr<VStmt>> &Out,
                                SourceLocation Loc);
  void leaveAutomaticScope(std::vector<std::unique_ptr<VStmt>> &Out,
                           SourceLocation Loc);
  void appendReturn(std::unique_ptr<VExpr> Value,
                    std::vector<std::unique_ptr<VStmt>> &Out,
                    SourceLocation Loc);
  void convertExecCallArgs(const CallExpr *CE,
                           std::vector<std::unique_ptr<VStmt>> &Prelude,
                           std::vector<std::unique_ptr<VExpr>> &Args);
  void convertExecCallArg(const Expr *E, const ParmVarDecl *Formal,
                          std::vector<std::unique_ptr<VStmt>> &Prelude,
                          std::unique_ptr<VExpr> &Out);
  std::unique_ptr<VExpr> convertCallResultValue(std::string Name,
                                                QualType SourceType,
                                                const VType &TargetType,
                                                SourceLocation Loc,
                                                std::string Provenance = "");
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
  bool calleeReturnsFreshOwned(const FunctionDecl *FD);
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
  bool referencesDynamicPointer(const Expr *E) const;
  const VarDecl *directDynamicPointer(const Expr *E) const;
  bool dynamicPointerSourceTypesMatch(const VarDecl *Target,
                                      const Expr *Source) const;
  std::unique_ptr<VExpr> convertDynamicPointerProvenance(const Expr *E);
  bool appendDynamicPointerAssignment(const VarDecl *Target, const Expr *Source,
                                      SourceLocation Loc,
                                      std::vector<std::unique_ptr<VStmt>> &Out);
  bool ghostAssignmentAllowed(const Expr *E) const;
  /// Populate `Fn.Layouts` with canonical, deduplicated layouts for the record
  /// and constant-array types encountered in `FD`'s signature and body.
  void collectLayouts(const FunctionDecl *FD, VFunction &Fn);
  void registerLayoutType(QualType QT, VFunction &Fn);
  void buildRecordLayout(QualType QT, VFunction &Fn);
  void buildArrayLayout(QualType QT, const ConstantArrayType *CAT,
                        VFunction &Fn);
  bool flattenRecordInto(const RecordDecl *RD, const std::string &Prefix,
                         uint64_t BaseOffset,
                         const std::vector<VObjectRepeat> &Repeats,
                         std::vector<VObjectLeaf> &Leaves,
                         std::vector<QualType> &PendingPointees);
  bool flattenArrayInto(const ConstantArrayType *CAT, const std::string &Prefix,
                        uint64_t BaseOffset,
                        const std::vector<VObjectRepeat> &Repeats,
                        SourceLocation Loc, std::vector<VObjectLeaf> &Leaves,
                        std::vector<QualType> &PendingPointees);
  std::set<std::string> KnownLayoutIdentities;
};

} // namespace verify
} // namespace clang

#endif