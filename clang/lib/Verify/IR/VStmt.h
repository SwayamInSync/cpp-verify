//===--- VStmt.h - Layer 1 statements for CppVerify -------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VSTMT_H
#define LLVM_CLANG_VERIFY_IR_VSTMT_H

#include "VExpr.h"
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace clang {
namespace verify {

/// What a proof obligation establishes. Mirrors ObligationKind.
enum class ProofObligationKind {
  Assertion,
  Postcondition,
  Unwinding,
  Precondition,
  InvariantEntry,
  InvariantPreserved,
  Termination,
  TypeInvariant,
  Recommends,
  Overflow,
  DivisionByZero,
  Shift,
  Bounds,
  Dereference,
  Initialization,
  PointerDifference,
  PointerValidity,
  Aliasing,
  Frame,
  Deallocation,
  MissingReturn,
  Unsupported
};

class VStmt {
public:
  enum Kind {
    Assign,
    Store,
    Allocate,
    EndLifetime,
    Free,
    If,
    While,
    Call,
    Assert,
    Assume,
    Return,
    Seq,
    Havoc,
    GhostBlock,
    RevealWithFuel,
    HideSpec,
    RevealSpec,
    ContractAssert,
    Break,
    Continue
  };

  Kind K;
  SourceLocation Loc;
  virtual ~VStmt() = default;

protected:
  VStmt(Kind K, SourceLocation Loc) : K(K), Loc(Loc) {}
};

struct VAssignStmt : VStmt {
  std::string Target;
  std::unique_ptr<VExpr> Value;
  bool IsReferenceBinding;
  VAssignStmt(std::string T, std::unique_ptr<VExpr> V, SourceLocation Loc,
              bool IsReferenceBinding = false)
      : VStmt(Assign, Loc), Target(std::move(T)), Value(std::move(V)),
        IsReferenceBinding(IsReferenceBinding) {}
};

struct VStoreStmt : VStmt {
  std::unique_ptr<VExpr> Ptr;
  std::unique_ptr<VExpr> Value;
  std::unique_ptr<VExpr> AccessCondition;
  VStoreStmt(std::unique_ptr<VExpr> P, std::unique_ptr<VExpr> V,
             SourceLocation Loc,
             std::unique_ptr<VExpr> AccessCondition = nullptr)
      : VStmt(Store, Loc), Ptr(std::move(P)), Value(std::move(V)),
        AccessCondition(std::move(AccessCondition)) {}
};

struct VAllocateStmt : VStmt {
  std::string Target;
  std::string ProvenanceTarget;
  VType AllocatedType;
  std::unique_ptr<VExpr> Initializer;
  uint64_t SizeBytes;
  uint64_t AlignBytes;
  bool IsAutomatic;
  VAllocateStmt(std::string Target, std::string ProvenanceTarget,
                VType AllocatedType, std::unique_ptr<VExpr> Initializer,
                uint64_t SizeBytes, uint64_t AlignBytes, SourceLocation Loc,
                bool IsAutomatic = false)
      : VStmt(Allocate, Loc), Target(std::move(Target)),
        ProvenanceTarget(std::move(ProvenanceTarget)),
        AllocatedType(AllocatedType), Initializer(std::move(Initializer)),
        SizeBytes(SizeBytes), AlignBytes(AlignBytes), IsAutomatic(IsAutomatic) {
  }
};

struct VEndLifetimeStmt : VStmt {
  std::string Target;
  std::string ProvenanceTarget;
  bool IsFunctionExit;
  VEndLifetimeStmt(std::string Target, std::string ProvenanceTarget,
                   SourceLocation Loc, bool IsFunctionExit = false)
      : VStmt(EndLifetime, Loc), Target(std::move(Target)),
        ProvenanceTarget(std::move(ProvenanceTarget)),
        IsFunctionExit(IsFunctionExit) {}
};

struct VFreeStmt : VStmt {
  std::unique_ptr<VExpr> Ptr;
  VFreeStmt(std::unique_ptr<VExpr> Ptr, SourceLocation Loc)
      : VStmt(Free, Loc), Ptr(std::move(Ptr)) {}
};

struct VIfStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  std::vector<std::unique_ptr<VStmt>> Then;
  std::vector<std::unique_ptr<VStmt>> Else;
  bool IsLoopUnroll;
  unsigned LoopUnrollIteration;
  VIfStmt(std::unique_ptr<VExpr> C, std::vector<std::unique_ptr<VStmt>> T,
          std::vector<std::unique_ptr<VStmt>> E, SourceLocation Loc,
          bool IsLoopUnroll = false, unsigned LoopUnrollIteration = 0)
      : VStmt(If, Loc), Cond(std::move(C)), Then(std::move(T)),
        Else(std::move(E)), IsLoopUnroll(IsLoopUnroll),
        LoopUnrollIteration(LoopUnrollIteration) {}
};

struct VAssertStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  ProofObligationKind ProofKind;
  VAssertStmt(std::unique_ptr<VExpr> C, SourceLocation Loc,
              ProofObligationKind ProofKind)
      : VStmt(Assert, Loc), Cond(std::move(C)), ProofKind(ProofKind) {}
};

struct VAssumeStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  VAssumeStmt(std::unique_ptr<VExpr> C, SourceLocation Loc)
      : VStmt(Assume, Loc), Cond(std::move(C)) {}
};

struct VReturnStmt : VStmt {
  std::unique_ptr<VExpr> Value;
  VReturnStmt(std::unique_ptr<VExpr> V, SourceLocation Loc)
      : VStmt(Return, Loc), Value(std::move(V)) {}
};

/// Leaves the innermost enclosing loop.
struct VBreakStmt : VStmt {
  explicit VBreakStmt(SourceLocation Loc) : VStmt(Break, Loc) {}
};

/// Ends the iteration; a `for` increment is lowered before it.
struct VContinueStmt : VStmt {
  explicit VContinueStmt(SourceLocation Loc) : VStmt(Continue, Loc) {}
};

struct VSeqStmt : VStmt {
  std::vector<std::unique_ptr<VStmt>> Stmts;
  VSeqStmt(std::vector<std::unique_ptr<VStmt>> S, SourceLocation Loc)
      : VStmt(Seq, Loc), Stmts(std::move(S)) {}
};

struct VHavocStmt : VStmt {
  std::string Target;
  VHavocStmt(std::string T, SourceLocation Loc)
      : VStmt(Havoc, Loc), Target(std::move(T)) {}
};

/// A modifies footprint. Target names the lvalue (a Load for memory); with
/// Count, the footprint is the Count cells of ElementSize bytes from Target's
/// address.
struct VFootprint {
  std::unique_ptr<VExpr> Target;
  std::unique_ptr<VExpr> Count;
  uint64_t ElementSize = 0;
};

VFootprint cloneFootprint(const VFootprint &F);

struct VWhileStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  std::vector<std::unique_ptr<VExpr>> Invariants;
  /// Lexicographic termination measure (ordered tuple); empty means none.
  std::vector<std::unique_ptr<VExpr>> Decreases;
  /// The memory the loop may write, read in each iteration's state; empty
  /// means none was declared.
  std::vector<VFootprint> Modifies;
  std::vector<std::unique_ptr<VStmt>> Body;
  VWhileStmt(std::unique_ptr<VExpr> C, std::vector<std::unique_ptr<VExpr>> Inv,
             std::vector<std::unique_ptr<VExpr>> Dec,
             std::vector<std::unique_ptr<VStmt>> B, SourceLocation Loc)
      : VStmt(While, Loc), Cond(std::move(C)), Invariants(std::move(Inv)),
        Decreases(std::move(Dec)), Body(std::move(B)) {}
};

struct VCallStmt : VStmt {
  /// User-facing source name.
  std::string Callee;
  /// Signature-stable internal identity.
  std::string CalleeIdentity;
  std::vector<std::unique_ptr<VExpr>> Args;
  std::string ResultTarget;
  /// SSA companion receiving the lifetime identity of a pointer result.
  std::string ResultProvenanceTarget;
  bool IsProofCall = false;
  VCallStmt(std::string Callee, std::string CalleeIdentity,
            std::vector<std::unique_ptr<VExpr>> Args, std::string ResultTarget,
            SourceLocation Loc, bool IsProofCall = false,
            std::string ResultProvenanceTarget = "")
      : VStmt(Call, Loc), Callee(std::move(Callee)),
        CalleeIdentity(std::move(CalleeIdentity)), Args(std::move(Args)),
        ResultTarget(std::move(ResultTarget)),
        ResultProvenanceTarget(std::move(ResultProvenanceTarget)),
        IsProofCall(IsProofCall) {}
};

struct VGhostBlockStmt : VStmt {
  std::vector<std::unique_ptr<VStmt>> Body;
  VGhostBlockStmt(std::vector<std::unique_ptr<VStmt>> B, SourceLocation Loc)
      : VStmt(GhostBlock, Loc), Body(std::move(B)) {}
};

struct VRevealWithFuelStmt : VStmt {
  std::string SpecFunction;
  unsigned Fuel = 1;
  VRevealWithFuelStmt(std::string Fn, unsigned Fuel, SourceLocation Loc)
      : VStmt(RevealWithFuel, Loc), SpecFunction(std::move(Fn)), Fuel(Fuel) {}
};

struct VHideSpecStmt : VStmt {
  std::string SpecFunction;
  VHideSpecStmt(std::string Fn, SourceLocation Loc)
      : VStmt(HideSpec, Loc), SpecFunction(std::move(Fn)) {}
};

struct VRevealSpecStmt : VStmt {
  std::string SpecFunction;
  VRevealSpecStmt(std::string Fn, SourceLocation Loc)
      : VStmt(RevealSpec, Loc), SpecFunction(std::move(Fn)) {}
};

struct VContractAssertStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  VContractAssertStmt(std::unique_ptr<VExpr> C, SourceLocation Loc)
      : VStmt(ContractAssert, Loc), Cond(std::move(C)) {}
};

std::unique_ptr<VStmt> cloneVStmt(const VStmt *S);

struct VValidExtent {
  std::string Base;
  VType PointerType;
  std::unique_ptr<VExpr> Length;

  VValidExtent(std::string Base, VType PointerType,
               std::unique_ptr<VExpr> Length)
      : Base(std::move(Base)), PointerType(PointerType),
        Length(std::move(Length)) {}
};

/// A parameter pair under the implicit non-aliasing default (not `aliases`).
struct VDisjointAddresses {
  std::string First;
  std::string Second;
  uint64_t FirstSizeBytes = 0;
  uint64_t SecondSizeBytes = 0;
};

/// Inferred effect for a pointer result that transfers one fresh allocation to
/// the caller. This is derived from a verified body, never from contract text.
struct VFreshOwnedReturn {
  VType AllocatedType;
  uint64_t SizeBytes = 0;
  uint64_t AlignBytes = 0;
  bool MayReturnNull = false;
};

/// Source identity retained independently of later SSA names.
struct VSourceVariable {
  std::string DisplayName;
  VType Type;
  SourceLocation Loc;
  SourceLocation EndLoc;
};

/// reads(Base, Count) on a spec: the cells Base[0..Count), ElementSize bytes
/// apart, which bound everything the spec reads.
struct VReadRange {
  std::unique_ptr<VExpr> Base;
  std::unique_ptr<VExpr> Count;
  uint64_t ElementSize = 1;
};

struct VFunction {
  /// User-facing source name.
  std::string Name;
  /// Signature-stable internal identity.
  std::string Identity;
  VType ReturnType;
  VIntMode IntMode = VIntMode::Machine;
  bool IsSpec = false;
  bool IsProof = false;
  bool IsConstexprSpec = false;
  /// Reads memory, directly or through another spec.
  bool ReadsHeap = false;
  bool RequiresCallDefinedness = false;
  bool IsExternalContract = false;
  /// [[cppverify::trusted]]: its contract is assumed and its body, if any,
  /// is not verified.
  bool IsTrusted = false;
  /// The declaration, for diagnostics about the function itself.
  SourceLocation DeclLoc;
  bool NeedsDecreasesCheck = false;
  /// decreases(*) on the function or one of its loops: it may diverge.
  SourceLocation DivergenceLoc;
  /// decreases(*) on the function itself: it may also recurse without a
  /// measure.
  bool DivergenceDeclared = false;
  /// An executable loop with no decreases clause.
  SourceLocation UnmeasuredLoop;
  /// Memory is checked against the parameters' objects: an access through a
  /// pointer without provenance lies in one at entry.
  bool ObjectModel = false;
  /// The other spec functions of a mutually recursive cycle.
  std::set<std::string> RecursionGroup;
  /// The other specs and proof functions this one reaches and is reached
  /// from through calls and applications in bodies, contracts, and proof
  /// blocks, when all of them share a measure of one length (Dafny's
  /// cluster): a call to one lowers the measure, and a postcondition of one
  /// is assumed only where the measure is lower, so their contracts and
  /// postconditions are proved together by well-founded induction.
  std::set<std::string> Cluster;
  /// Every spec function its contracts and body reach, transitively.
  std::set<std::string> SpecDependencies;
  std::vector<VReadRange> Reads;
  /// when(c): the domain on which the body defines a spec.
  std::unique_ptr<VExpr> Domain;
  /// A spec without a definition: the value of another outside its domain.
  bool Uninterpreted = false;
  /// A choose(...) lifted to a function of what its body mentions: its post
  /// is the defining axiom (a witness when one exists), assumed, not proved.
  bool IsChoice = false;
  /// Supplied by <cppverify.h> rather than written in the program.
  bool IsBuiltin = false;
  /// inductive: the least predicate its body defines, a function that is
  /// true where some finite derivation shows it.
  SourceLocation InductiveLoc;
  /// The body of an inductive predicate as one condition over its
  /// parameters, applying the predicate itself: equal to it at every
  /// application.
  std::unique_ptr<VExpr> Unfolding;
  /// The step-indexed definition of the inductive predicate named here.
  std::string InductiveStepOf;
  /// A generated proof of a rule of the inductive predicate with this
  /// identity; its unfolding may be used once all of them are proved.
  std::string InductiveRuleOf;
  /// Specs whose postconditions and unfoldings are not assumed at their
  /// applications here: the rules this function proves come before them.
  std::set<std::string> FactsWithheld;
  /// A generated proof about specs, not C++ code: its expressions are total
  /// as in specs, so they carry no definedness obligations.
  bool TotalExpressions = false;
  /// Ghost code the user gave for a check of a spec's clause,
  /// post(...) by { ... }: it runs after the check's assumptions and before
  /// its obligations.
  struct ClauseProof {
    enum Kind { Post, Decreases, Reads } K;
    std::vector<std::unique_ptr<VStmt>> Body;
    SourceLocation Loc;
  };
  std::vector<ClauseProof> ClauseProofs;
  /// Each behavior's name and assumption, to check that it can apply.
  std::vector<std::pair<std::string, std::unique_ptr<VExpr>>> Behaviors;
  bool UsesDynamicStorage = false;
  std::optional<VFreshOwnedReturn> FreshOwnedReturn;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  std::vector<std::pair<std::string, VType>> Params;
  std::map<std::string, VSourceVariable> SourceVariables;
  std::set<std::string> ReferenceParams;
  /// Pointer and reference parameters to const objects: the function
  /// writes nothing through them.
  std::set<std::string> ConstAddressParams;
  std::vector<std::pair<std::string, VType>> ReturnFields;
  /// Number of leading preconditions originating from explicit pre clauses.
  unsigned ExplicitPreconditionCount = 0;
  std::vector<std::unique_ptr<VExpr>> Preconditions;
  std::vector<std::unique_ptr<VExpr>> Postconditions;
  /// Kinds of generated clauses by index; see preconditionKind().
  std::vector<ProofObligationKind> PreconditionKinds;
  std::vector<ProofObligationKind> PostconditionKinds;
  std::vector<std::unique_ptr<VExpr>> Recommends;
  std::vector<VFootprint> Modifies;
  std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
      Aliases;
  /// Positive top-level valid(base, length) interface extents discovered by
  /// UB instrumentation before the marker's spec body is prepared away.
  std::vector<VValidExtent> ValidExtents;
  std::vector<VDisjointAddresses> DisjointAddresses;
  /// Lexicographic termination measure (ordered tuple); empty means none.
  std::vector<std::unique_ptr<VExpr>> Decreases;
  std::vector<std::unique_ptr<VStmt>> Body;
  /// Canonical layout table for by-value record and constant-array types
  /// encountered in this function's signature and body. One entry per canonical
  /// type identity; non-recursive (pointer fields stop at Ptr leaves).
  std::vector<VObjectLayout> Layouts;
};

/// Global variables live at fixed addresses from here to the end of the
/// address space; every other object lies below.
inline constexpr uint64_t GlobalRegionBase = 0xFFFFFFFF00000000ULL;

VFunction cloneVFunction(const VFunction &Fn);

void addPrecondition(VFunction &Fn, std::unique_ptr<VExpr> Condition,
                     ProofObligationKind Kind);
void addPostcondition(VFunction &Fn, std::unique_ptr<VExpr> Condition,
                      ProofObligationKind Kind);
ProofObligationKind preconditionKind(const VFunction &Fn, size_t Index);
ProofObligationKind postconditionKind(const VFunction &Fn, size_t Index);

} // namespace verify
} // namespace clang

#endif