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

/// A construct the converter cannot represent, and where it is written.
struct ConversionError {
  SourceRange Range;
  std::string Message;
  /// The function it is written in (its identity and name), whose verdict it
  /// decides; empty for an error of the translation unit.
  std::string Function;
  std::string FunctionName;
  SourceLocation FunctionLoc;
  /// In the function's signature or contract, rather than its body: then
  /// its callers cannot use the contract either.
  bool InContract = false;
};

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
  /// Where the statement being lowered puts what forming a pointer to a
  /// subobject needs (its checks and its bounds); null where the pointer is
  /// only a value, as in a condition or a contract.
  std::vector<std::unique_ptr<VStmt>> *SubobjectSink = nullptr;
  unsigned SubobjectPointerId = 0;
  /// Where the statement or condition being lowered in executable code puts
  /// the calls and writes its expressions make, each value into a temporary,
  /// in evaluation order; null where no executable call can be made.
  std::vector<std::unique_ptr<VStmt>> *CallSink = nullptr;
  /// The temporary of each call, increment, decrement, or assignment already
  /// put there, and its type, and each comma whose first operand is (with no
  /// temporary), so converting an expression twice evaluates it once.
  std::map<const Expr *, std::pair<std::string, VType>> HoistedValues;
  /// The next statement converted is a write an expression makes, which
  /// continues its evaluation and keeps HoistedValues.
  bool ContinuesEvaluation = false;
  std::vector<ConversionError> Errors;
  /// The innermost declaration, statement, or expression being converted,
  /// where an error is reported unless it names a place of its own.
  SourceRange CurrentRange;
  /// The function whose conversion an error belongs to, and whether the
  /// converter is in its signature and contract or in its body.
  std::string ErrorFunction;
  std::string ErrorFunctionName;
  SourceLocation ErrorFunctionLoc;
  bool ErrorInContract = false;
  void error(std::string Message) { error(CurrentRange, std::move(Message)); }
  void error(SourceRange Range, std::string Message) {
    Errors.push_back({Range, std::move(Message), ErrorFunction,
                      ErrorFunctionName, ErrorFunctionLoc, ErrorInContract});
  }
  /// An error about \p Fn found once every function is converted.
  void errorOf(const VFunction &Fn, SourceLocation Loc, std::string Message) {
    Errors.push_back({SourceRange(Loc), std::move(Message), Fn.Identity,
                      Fn.Name, Fn.DeclLoc, false});
  }
  std::vector<std::pair<SourceLocation, std::string>> Warnings;
  /// Maps unqualified field name -> "param." for type_invariant lowering.
  std::map<std::string, std::string> FieldSubstPrefix;
  bool TrackInitialization = false;
  bool InitializationPathReachable = true;
  std::set<std::string> DeclaredValueNames;
  /// The names of locals declared where their name was already taken.
  std::map<const VarDecl *, std::string> LocalNames;
  std::set<std::string> InitializedValues;
  std::set<std::string> ReportedUninitializedValues;
  std::map<const ValueDecl *, std::string> BoundValues;
  /// Binders of a forall being introduced by contract_assert(...) by.
  std::set<const ValueDecl *> ArbitraryValues;
  std::map<std::string, std::set<std::string>> UnverifiedCallers;
  std::map<std::string, std::pair<SourceLocation, std::string>>
      InstantiationPoints;
  std::map<const ParmVarDecl *, std::string> ParameterNames;
  /// The parameters of a lifted spec that refer to const scalars, which
  /// stand for the values they refer to.
  std::set<const VarDecl *> ValueReferences;
  /// For a parameter a pack expands to, its index in the pack, `...[1]`.
  std::map<const ParmVarDecl *, std::string> PackElements;
  /// Names each parameter of \p FD after the declaration \p ContractDecl
  /// whose contract names them.
  void nameParameters(const FunctionDecl *ContractDecl, const FunctionDecl *FD);
  unsigned BoundValueId = 0;
  std::map<const FunctionDecl *, std::string> FunctionIdentities;
  std::map<std::string, std::string> ContractTexts;
  std::map<const FunctionDecl *, bool> SpecHeapReads;
  /// Uncontracted constexpr functions the lowered code calls or names.
  std::set<const FunctionDecl *> UsedConstexprSpecs;
  std::set<std::string> FreshOwnedCalleeIdentities;
  std::set<const VarDecl *> DynamicPointers;
  std::map<const VarDecl *, std::string> DynamicPointerProvenanceVariables;
  std::set<const VarDecl *> AddressableLocals;
  std::map<const VarDecl *, std::string> AutomaticLocalProvenanceVariables;
  std::vector<std::vector<const VarDecl *>> AutomaticScopeStack;
  std::vector<const VarDecl *> ActiveAutomaticLocals;
  std::map<const VarDecl *, std::string> LocalReferenceProvenanceVariables;
  /// The first arguments of extent markers that name a pointer field of an
  /// address parameter, by the synthetic parameter of the field's entry value
  /// (VFunction::FieldParams).
  std::map<const Expr *, std::string> FieldExtentParameters;
  /// Converting a clause where an extent marker states nothing (a class
  /// invariant at exit): each marker is true.
  bool DropExtentMarkers = false;
  /// The object `this` stands for while a class invariant is instantiated
  /// for a parameter: the pointer or reference that addresses it.
  const VExpr *ThisSubstitute = nullptr;
  /// The function whose body is being converted.
  const FunctionDecl *ConvertingDecl = nullptr;
  std::set<const VarDecl *> GhostLocals;
  unsigned DynamicProvenanceId = 0;
  unsigned DynamicPointerAssignmentId = 0;
  unsigned AutomaticStorageId = 0;
  unsigned LocalReferenceId = 0;
  unsigned LoopDepth = 0;
  /// The loops and switches a break or continue may leave, innermost last.
  /// A `do` loop's first iteration is lowered outside it.
  struct EnclosingLoop {
    const Expr *Increment = nullptr;
    bool IsDo = false;
    bool IsGhost = false;
    bool IsSwitch = false;
    /// The automatic objects live where a switch begins, and the depth of
    /// its body's scope.
    size_t ActiveLocals = 0;
    size_t Scope = 0;
    /// Whether a break or continue leaves it, and the values initialized on
    /// every path that does.
    bool Breaks = false;
    bool Continues = false;
    std::optional<std::set<std::string>> BreakInitialized;
    std::optional<std::set<std::string>> ContinueInitialized;
    /// The increment of a loop the converter builds, which a continue runs.
    const VStmt *IncrementStmt = nullptr;
  };
  std::vector<EnclosingLoop> EnclosingLoops;
  /// The counter that cppverify::index, the declaration RangeIndex, names
  /// while a range-based for loop's contract is converted.
  std::string RangeIndexName;
  const VarDecl *RangeIndex = nullptr;
  /// Fixed addresses of the mutable global variables, assigned on first use.
  std::map<const VarDecl *, uint64_t> GlobalAddresses;
  uint64_t NextGlobalAddress = GlobalRegionBase;

public:
  explicit ASTConverter(
      ASTContext &Ctx,
      const std::set<std::string> &FreshOwnedCalleeIdentities = {})
      : Ctx(Ctx), FreshOwnedCalleeIdentities(FreshOwnedCalleeIdentities) {}

  std::vector<std::unique_ptr<VFunction>> convertTranslationUnit();
  const std::vector<ConversionError> &getErrors() const { return Errors; }
  /// For each contracted function, the functions not verified whose bodies
  /// call it: its precondition is assumed there, not checked.
  const std::map<std::string, std::set<std::string>> &
  getUnverifiedCallers() const {
    return UnverifiedCallers;
  }
  const std::vector<std::pair<SourceLocation, std::string>> &
  getWarnings() const {
    return Warnings;
  }
  /// For each template specialization converted, by its name: where it is
  /// instantiated and what it is ("function template specialization"),
  /// which its diagnostics note as a compiler's do. A name two
  /// specializations share has no location.
  const std::map<std::string, std::pair<SourceLocation, std::string>> &
  getInstantiationPoints() const {
    return InstantiationPoints;
  }
  /// For each contracted function, by its identity: its contract as written,
  /// which another file's declaration of it must state the same.
  const std::map<std::string, std::string> &getContractTexts() const {
    return ContractTexts;
  }

private:
  /// Contract arithmetic is mathematical, as in ACSL and Verus spec code: an
  /// integer operand is read exactly and no operation wraps.
  bool contractMath() const {
    return InContractExpression && IntMode == VIntMode::Machine;
  }
  std::unique_ptr<VFunction> convertFunction(const FunctionDecl *FD);
  /// Numbers the nondeterministic choices of contract_assert(...) by.
  unsigned NextAssertBy = 0;
  /// The functions choose(...) expressions are lifted to.
  std::vector<std::unique_ptr<VFunction>> ChoiceFunctions;
  /// The lifted choice of each condition, by its structural key.
  std::map<std::string, std::string> ChoiceByCondition;
  /// Specs of <cppverify.h> the translation unit calls, such as valid.
  std::vector<std::unique_ptr<VFunction>> BuiltinFunctions;
  std::unique_ptr<VExpr> convertChoose(const ContractChooseExpr *C);
  std::unique_ptr<VExpr>
  choiceApplication(const ContractChooseExpr *C, const std::string &Identity,
                    std::vector<std::unique_ptr<VExpr>> Args,
                    const VType &ValueType, bool ReadsHeap, SourceLocation Loc);
  /// A cppverify collection operation or copy, with Handled set; null and
  /// Handled clear for anything else.
  std::unique_ptr<VExpr> convertCollection(const Expr *E, bool &Handled);
  bool checkLoopTermination(const Stmt *Loop, bool HasMeasure);
  /// The condition of \p Loop: the constant false when it never repeats.
  /// Its calls go to Calls, which is null where none can be made.
  std::unique_ptr<VExpr>
  convertLoopCondition(const Stmt *Loop, const Expr *Cond,
                       std::vector<std::unique_ptr<VStmt>> *Calls = nullptr);
  /// A loop whose condition makes calls tests it inside its body, so they
  /// run at every test.
  void testAtEveryIteration(std::vector<std::unique_ptr<VStmt>> Calls,
                            std::unique_ptr<VExpr> &Cond,
                            std::vector<std::unique_ptr<VStmt>> &Body);
  bool isTriggerMarked(const Expr *E) const;
  void markTrigger(std::unique_ptr<VExpr> &Result, const Expr *E);
  /// A modifies footprint: an lvalue, the cells p[lo : n], or the bytes of a
  /// record or array inside an object.
  std::optional<VFootprint> convertFootprint(const Expr *E);
  /// A loop's declared footprints, each naming memory.
  std::vector<VFootprint> convertLoopFootprints(const LoopContractInfo &LCI);
  /// A global's constant value, when it is const with a constant initializer.
  std::optional<llvm::APSInt> globalConstant(const VarDecl *VD) const;
  /// The address of a supported mutable global, or null after an error.
  std::unique_ptr<VExpr> globalAddress(const VarDecl *VD, SourceLocation Loc);
  std::unique_ptr<VFunction> convertConstexprSpec(const FunctionDecl *FD);
  /// std::max(a, b), or std::min(a, b), of two integers, as the standard
  /// defines it.
  std::unique_ptr<VExpr> convertMinOrMax(const CallExpr *CE, bool IsMax);
  /// A call of a bit-counting or byte-swapping builtin, by its definition;
  /// nullopt for any other call.
  std::optional<std::unique_ptr<VExpr>> convertBitBuiltin(const CallExpr *CE);
  /// The models of <cppverify.h> (cppverify::model) that converted calls
  /// use, in the order of their first use.
  std::vector<const FunctionDecl *> UsedLibraryModels;
  /// The model named \p Name whose first parameter points to \p Element.
  const FunctionDecl *libraryModel(llvm::StringRef Name,
                                   QualType Element) const;
  /// A call of memcpy, memmove, memset, or memcmp: a call of its model for
  /// the objects its pointers address, into \p Out, with its result in
  /// \p Result unless that is empty; the model, or null after an error.
  /// Nothing for any other call.
  std::optional<const FunctionDecl *>
  convertLibraryCall(const CallExpr *CE,
                     std::vector<std::unique_ptr<VStmt>> &Out,
                     const std::string &Result);
  /// abs, labs, llabs, and std::abs of an integer: its definition, in the
  /// parameter's type (mathematical in a spec); nothing for any other call.
  std::optional<std::unique_ptr<VExpr>> convertAbs(const CallExpr *CE);
  void noteSpecUse(const FunctionDecl *FD);
  std::unique_ptr<VExpr> convertExpr(const Expr *E);
  std::unique_ptr<VExpr> convertExprImpl(const Expr *E);
  std::unique_ptr<VExpr> convertPointerDifferenceOperand(const Expr *E,
                                                         uint64_t PointeeSize);
  std::unique_ptr<VExpr>
  convertLValueAddress(const Expr *E,
                       std::unique_ptr<VExpr> *AccessCondition = nullptr);
  std::unique_ptr<VExpr>
  convertAutomaticLocalAddress(const VarDecl *VD, SourceLocation Loc);
  /// Typed VPlace builders. The `convert*Address` helpers above are thin
  /// wrappers that lower these places to plain VLoad/VStore address
  /// expressions.
  std::optional<VPlace> lvaluePlace(const Expr *E);
  std::optional<VPlace> automaticLocalPlace(const VarDecl *VD,
                                            SourceLocation Loc);
  std::optional<VPlace> derefPlace(const Expr *PointerExpr, SourceLocation Loc);
  std::optional<VPlace> arrowFieldPlace(const MemberExpr *M);
  std::optional<VPlace> subscriptPlace(const ArraySubscriptExpr *AS);
  /// The object \p PointerExpr addresses, as the root of a selection.
  std::optional<VPlace> pointeePlace(const Expr *PointerExpr,
                                     SourceLocation Loc);
  /// p[k]: the element of the objects p addresses, bounded by their extent.
  std::optional<VPlace> pointerElementPlace(const ArraySubscriptExpr *AS);
  /// Root-object discovery: peel no-op casts, array-to-pointer decays, dot
  /// member chains and fixed-array subscripts down to the enclosing local
  /// object. Returns the root only when it was promoted to one automatic
  /// byte-addressed object.
  const VarDecl *promotedRootLocal(const Expr *E) const;
  /// The reference parameter or local whose record \p E selects a field or
  /// element of (or is), if any.
  const VarDecl *recordReferenceRoot(const Expr *E) const;
  /// Whether \p E is a place in an object reached through a pointer or a
  /// reference, rather than a value of the function's own.
  bool inPointeeObject(const Expr *E) const;
  /// Whether a pointer may be formed into the place \p E (its address, or a
  /// decayed member array): a place in an object that outlives the function,
  /// reached through a pointer or a reference to a record.
  bool subobjectPointerRoot(const Expr *E) const;
  /// The pointer whose pointee a chain of field and fixed-array element
  /// selections starts at (p in *p, p->m, p[k], (*p).a.b[i]); null when the
  /// chain does not start at a pointee.
  const Expr *pointeeRootPointer(const Expr *E) const;
  /// Why the decay of \p Array to a pointer is unsupported, in the terms of
  /// what the array is.
  std::string arrayDecayError(const Expr *Array) const;
  /// A pointer to \p Object, a subobject of the object a pointer addresses:
  /// the array \p E decays (AddressOf false) or the lvalue \p E takes the
  /// address of. Bounded by the array it decays from or whose element it
  /// addresses, else by the field or record it addresses.
  std::unique_ptr<VExpr> subobjectPointer(const Expr *E, const Expr *Object,
                                          bool AddressOf);
  /// The exact byte-offset place of a subobject, reached by field and
  /// fixed-array element selections from a promoted local or from the
  /// object a pointer addresses; each fixed-array index is bounded by its
  /// array in the place's access condition.
  std::optional<VPlace> objectPlace(const Expr *E);
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
  /// The member initializers of a constructor, in the order they run, on
  /// the object at Base + Offset.
  bool appendMemberInitializers(const CXXConstructorDecl *Ctor,
                                const VExpr *Base, uint64_t Offset,
                                SourceLocation Loc,
                                std::vector<std::unique_ptr<VStmt>> &Out);
  /// Runs a constructor on the object at Base + Offset: a call of one the
  /// class provides, else its members' initializers.
  bool appendConstruction(const CXXConstructExpr *Construct, QualType Ty,
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
  /// A constant table: a constant array with a constant initializer, or a
  /// string literal, given to the solver as a spec of its linear index.
  struct ConstantTable {
    std::string Name;
    std::string Identity;
    std::vector<uint64_t> Dims;
    VType ElementTy;
    std::vector<llvm::APSInt> Values;
  };
  std::optional<ConstantTable> constantTable(const Expr *Array) const;
  std::optional<ConstantTable> constantTable(const VarDecl *VD,
                                             const StringLiteral *Literal,
                                             QualType Element) const;
  /// Declares the spec of \p Table once.
  void defineTable(const ConstantTable &Table, SourceLocation Loc);
  /// An element of \p Table: the spec at the linear index, where every index
  /// must lie in its array.
  std::unique_ptr<VExpr> tableRead(const ConstantTable &Table,
                                   std::vector<std::unique_ptr<VExpr>> Indices,
                                   SourceLocation Loc);
  /// A whole read of a constant table, t[i][j]; std::nullopt when \p AS
  /// reads no such table.
  std::optional<std::unique_ptr<VExpr>>
  convertTableRead(const ArraySubscriptExpr *AS);
  /// A constant array with a constant initializer, of integers,
  /// enumerations, or bools: a table, which declares no object to run.
  bool isConstantTable(const VarDecl *VD) const;
  std::vector<std::unique_ptr<VStmt>>
  convertRangeFor(const CXXForRangeStmt *RF);
  /// Gives the local \p VD its VCR name: its own, or name#N when the name is
  /// already taken.
  void declareLocalName(const VarDecl *VD);
  std::vector<std::unique_ptr<VStmt>> convertStmt(const Stmt *S);
  std::vector<std::unique_ptr<VStmt>> convertStmtBody(const Stmt *S);
  std::vector<std::unique_ptr<VStmt>> convertScopedSubstatement(const Stmt *S);
  std::vector<std::unique_ptr<VStmt>> convertSwitch(const SwitchStmt *SS);
  /// if (Cond) Then else Else, with what each path initializes.
  void appendBranches(std::unique_ptr<VExpr> Cond, const Stmt *Then,
                      const Stmt *Else, SourceLocation Loc,
                      std::vector<std::unique_ptr<VStmt>> &Out);
  /// A discarded-value expression statement without side effects.
  void appendDiscarded(const Expr *E, std::vector<std::unique_ptr<VStmt>> &Out);
  /// [[assume(e)]] and __builtin_assume(e): e is proved, then assumed.
  void appendAssumption(const Expr *Assumption, SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  /// The declaration of a loop's condition variable, made at every test.
  void declareConditionVariable(const DeclStmt *Decl,
                                std::vector<std::unique_ptr<VStmt>> &Out);
  /// Rejects a loop contract that names the condition variable, which does
  /// not exist at the loop's head.
  bool checkConditionVariableUnnamed(
      const VarDecl *Var, const std::vector<std::unique_ptr<VExpr>> &Invariants,
      const std::vector<std::unique_ptr<VExpr>> &Decreases);
  void enterAutomaticScope();
  void registerAutomaticLocal(const VarDecl *VD);
  void appendActiveLifetimeEnds(std::vector<std::unique_ptr<VStmt>> &Out,
                                SourceLocation Loc, size_t From = 0,
                                bool IsFunctionExit = true);
  void leaveAutomaticScope(std::vector<std::unique_ptr<VStmt>> &Out,
                           SourceLocation Loc);
  void appendReturn(std::unique_ptr<VExpr> Value,
                    std::vector<std::unique_ptr<VStmt>> &Out,
                    SourceLocation Loc);
  void convertExecCallArgs(const CallExpr *CE,
                           std::vector<std::unique_ptr<VStmt>> &Prelude,
                           std::vector<std::unique_ptr<VExpr>> &Args);
  /// An executable call in an expression: a call statement into a temporary
  /// in the call sink, and a read of the temporary.
  std::unique_ptr<VExpr> hoistExecCall(const CallExpr *CE,
                                       const FunctionDecl *Callee);
  /// An increment, a decrement, or an assignment whose value an expression
  /// uses: its statements in the call sink, and a read of the value it has,
  /// the old one for a postfix operator, in a temporary.
  std::unique_ptr<VExpr> hoistSideEffect(const Expr *E);
  /// The variables that the increments, decrements, and assignments in \p S
  /// write (a field of a record held by value as its record's), and whether
  /// one writes memory.
  void collectWrites(const Stmt *S, std::set<const VarDecl *> &Written,
                     bool &Memory) const;
  /// Whether an increment, a decrement, or an assignment in \p Writer writes
  /// a variable \p Reader names, or memory when \p ReaderReadsMemory.
  bool writesWhatReads(const Expr *Writer, const Expr *Reader,
                       bool ReaderReadsMemory) const;
  /// A call of a contracted executable function, which may be hoisted.
  bool isExecCall(const Stmt *S) const;
  bool containsExecCall(const Stmt *S) const;
  /// A call that may write memory: its callee states a frame or takes a
  /// pointer or reference.
  bool containsModifyingCall(const Stmt *S) const;
  /// An evaluation a call's writes may change: a load, a reference, an
  /// addressable local, or another executable call.
  bool isHeapSensitive(const Stmt *S) const;
  /// Two unsequenced operands of which one may write what the other reads,
  /// so that their order, which C++ leaves open, matters.
  bool orderDependent(const Expr *A, const Expr *B) const;
  /// Whether locating the object \p E designates reads memory: the pointers
  /// and indices on the way are read, the object itself is not.
  bool locatingIsHeapSensitive(const Expr *E) const;
  /// `&&`, `||`, and `?:` in a statement. An operand evaluated only on a
  /// path of its own whose calls or checks need statements gets them on that
  /// path: the operator becomes statements, and the value a read of their
  /// result.
  std::unique_ptr<VExpr> convertOnPaths(const Expr *E);
  void convertExecCallArg(const Expr *E, const ParmVarDecl *Formal,
                          std::vector<std::unique_ptr<VStmt>> &Prelude,
                          std::unique_ptr<VExpr> &Out);
  /// A mathematical value stored in a machine-typed C++ object (a ghost or
  /// proof variable, a parameter, a return value) is converted there, and
  /// must fit; until then it stays mathematical.
  std::unique_ptr<VExpr> materialize(std::unique_ptr<VExpr> V,
                                     const VType &Target);
  std::unique_ptr<VExpr> materialize(std::unique_ptr<VExpr> V,
                                     QualType Target) {
    return materialize(std::move(V),
                       VType::fromQualType(Target.getNonReferenceType(),
                                           IntMode, Ctx));
  }
  std::unique_ptr<VExpr> convertCallResultValue(std::string Name,
                                                QualType SourceType,
                                                const VType &TargetType,
                                                SourceLocation Loc,
                                                std::string Provenance = "");
  bool appendRecordCallArgument(const Expr *E, const ParmVarDecl *Formal,
                                std::vector<std::unique_ptr<VExpr>> &Args);
  /// The fields of a record value that is kept in memory, a local object or
  /// one a pointer or reference addresses, each read where it is: nothing
  /// when E is no such record, false after an error.
  std::optional<bool> recordFieldsInMemory(
      const Expr *E, SourceLocation Loc,
      std::vector<std::pair<const FieldDecl *, std::unique_ptr<VExpr>>>
          &Fields);
  /// The value of \p Target stepped by \p Offset elements.
  std::unique_ptr<VExpr> convertPointerStep(const Expr *Target, VBinOp Op,
                                            std::unique_ptr<VExpr> Offset,
                                            SourceLocation Loc);
  std::unique_ptr<VExpr>
  convertAssignmentValue(const BinaryOperator *Assignment);
  void appendAssignment(const Expr *LHS, std::unique_ptr<VExpr> Value,
                        SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  /// A store to a field or fixed-array element inside the object a pointer
  /// addresses, with the element bounds of the place.
  void appendPointeeStore(const Expr *LHS, std::unique_ptr<VExpr> Value,
                          SourceLocation Loc,
                          std::vector<std::unique_ptr<VStmt>> &Out);
  bool appendRecordCopy(const Expr *Source, const VarDecl *Target,
                        SourceLocation Loc,
                        std::vector<std::unique_ptr<VStmt>> &Out);
  /// Reports a use of the reference a member function returns to its own
  /// object, which is no value.
  bool rejectOwnObjectUse(const Expr *E);
  bool appendRecordInitializer(const InitListExpr *Init, const VarDecl *Target,
                               SourceLocation Loc,
                               std::vector<std::unique_ptr<VStmt>> &Out);
  std::optional<VBinOp> convertBinOpcode(BinaryOperatorKind Op);
  const FunctionContractInfo *functionContract(const FunctionDecl *FD) const;
  bool calleeIsSpec(const FunctionDecl *FD) const;
  bool specReadsHeap(const FunctionDecl *FD);
  bool calleeIsProof(const FunctionDecl *FD) const;
  bool calleeReturnsFreshOwned(const FunctionDecl *FD);
  VIntMode specCallIntMode(const FunctionDecl *FD) const;
  std::string functionIdentity(const FunctionDecl *FD);
  /// The clauses of a contract as written, each kind tagged.
  std::string contractText(const FunctionContractInfo &FCI) const;
  std::string specIdentityFromExpr(const Expr *E);
  void injectTypeInvariants(const FunctionDecl *FD, VFunction &Fn);
  std::unique_ptr<VExpr> convertTypeInvariantExpr(const Expr *E);
  void appendObjectInvariants(std::vector<std::unique_ptr<VExpr>> &Invariants);
  void emitReturnInvariantAssert(const Expr *RetE,
                                 std::vector<std::unique_ptr<VStmt>> &Out,
                                 SourceLocation Loc);
  std::vector<std::string> trackedValueNames(const ValueDecl *D) const;
  std::string valueName(const ValueDecl *D) const;
  void recordSourceVariable(const ValueDecl *D);
  /// Reports \p FD when an expression in it, or in a contract it carries,
  /// nests deeper than every later pass, which recurses, can take.
  bool exceedsNestingLimit(const FunctionDecl *FD,
                           const FunctionContractInfo *FCI);
  void beginInitializationTracking(const FunctionDecl *FD);
  bool requireInitialized(const ValueDecl *D, const FieldDecl *Field = nullptr);
  void markInitialized(const ValueDecl *D, const FieldDecl *Field = nullptr);
  /// Whether \p E's value is an address computed from a dynamic-storage
  /// pointer. A value read through one is not: dynamic objects are scalars.
  bool isDynamicAddress(const Expr *E) const;
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
  /// An address the default separation covers: a pointer or reference
  /// parameter, or the entry value of a pointer field with an extent.
  struct AddressEntry {
    std::string Name;
    QualType Addressed;
    bool Mutable;
  };
  /// Gives each pointer field of an address parameter that an extent marker
  /// of FCI's preconditions names a synthetic parameter for its entry value
  /// (VFunction::FieldParams), and returns them for the default
  /// separation.
  std::vector<AddressEntry>
  collectFieldExtents(const FunctionContractInfo &FCI,
                      llvm::ArrayRef<const Expr *> Invariants, VFunction &Fn);
  std::vector<const Expr *> entryClassInvariants(const CXXMethodDecl *Method,
                                                 bool Constructor) const;
  std::vector<const Expr *> exitClassInvariants(const CXXMethodDecl *Method,
                                                bool Constructor) const;
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