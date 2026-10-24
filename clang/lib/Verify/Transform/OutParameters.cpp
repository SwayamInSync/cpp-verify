//===--- OutParameters.cpp ------------------------------------------------===//
//
// A parameter's storage needs to be initialized at entry only where the
// function may read it before writing it, as C# requires of an `out`
// parameter by definite assignment. The analysis is a conservative,
// flow-sensitive walk of the converted body per pointer or reference
// parameter: the leaves written on every path so far, at constant offsets
// from the parameter, cover the reads after them; a read anywhere else, a
// read of the entry state in a contract, a callee that may read the storage,
// or any use of the pointer other than an access, a null test, or a validity
// check makes it an input. Postconditions, loop invariants, and checks
// describe what the body has written, and the verifier checks their reads
// against it, so they are not reads here; but of storage the function never
// writes they read the caller's values, which makes it an input. The
// classification decides the contract only; the body is verified against
// it, its reads of an out-parameter checked against the initialization it
// tracks.
//
// The leaves of its object a function writes on every path to a return are
// initialized when it returns, which a generated postcondition states and
// the function's exit checks prove; a call writes them in its caller's walk.
//
//===----------------------------------------------------------------------===//
#include "OutParameters.h"
#include "UBChecks.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <cerrno>
#include <cstdlib>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>

using namespace clang;
using namespace verify;

namespace {

/// Per function identity, per parameter.
template <typename T>
using PerParameter = std::map<std::string, std::map<std::string, T>>;
using FunctionsByIdentity = std::map<std::string, const VFunction *>;

const VExpr *stripCasts(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  return E;
}

bool isVar(const VExpr *E, const std::string &Name) {
  E = stripCasts(E);
  return E && E->K == VExpr::Var &&
         static_cast<const VVarExpr *>(E)->Name == Name;
}

bool mentions(const VExpr *E, const std::string &Name) {
  if (!E)
    return false;
  if (E->K == VExpr::Var)
    return static_cast<const VVarExpr *>(E)->Name == Name;
  bool Found = false;
  forEachVExprChild(
      E, [&](const VExpr *Child) { Found = Found || mentions(Child, Name); });
  return Found;
}

std::optional<int64_t> constantValue(const VExpr *E) {
  E = stripCasts(E);
  if (!E)
    return std::nullopt;
  if (E->K == VExpr::Literal) {
    const std::string &Text = static_cast<const VLiteralExpr *>(E)->Value;
    char *End = nullptr;
    errno = 0;
    const long long Value = std::strtoll(Text.c_str(), &End, 10);
    if (errno || Text.empty() || *End)
      return std::nullopt;
    return Value;
  }
  if (E->K != VExpr::BinOp)
    return std::nullopt;
  const auto *B = static_cast<const VBinOpExpr *>(E);
  auto L = constantValue(B->Lhs.get());
  auto R = constantValue(B->Rhs.get());
  if (!L || !R || *L < 0 || *R < 0 || *L > (1 << 30) || *R > (1 << 30))
    return std::nullopt;
  switch (B->Op) {
  case VBinOp::Add:
    return *L + *R;
  case VBinOp::Mul:
    return *L * *R;
  default:
    return std::nullopt;
  }
}

/// The byte offset of an address from Param when it is the parameter plus
/// constants.
std::optional<uint64_t> offsetFrom(const VExpr *E, const std::string &Param) {
  E = stripCasts(E);
  if (isVar(E, Param))
    return 0;
  if (!E || E->K != VExpr::BinOp)
    return std::nullopt;
  const auto *B = static_cast<const VBinOpExpr *>(E);
  if (B->Op != VBinOp::Add || B->Lhs->Ty.Kind != VTypeKind::Ptr)
    return std::nullopt;
  auto Base = offsetFrom(B->Lhs.get(), Param);
  auto Step = constantValue(B->Rhs.get());
  if (!Base || !Step || *Step < 0)
    return std::nullopt;
  return *Base + static_cast<uint64_t>(*Step);
}

/// The leaves of the object a parameter of Fn addresses, as offsets: those
/// of its record layout, or one scalar at offset 0.
std::optional<std::set<uint64_t>> pointeeLeaves(const VFunction &Fn,
                                                const std::string &Param) {
  auto Record = Fn.RecordParams.find(Param);
  if (Record == Fn.RecordParams.end())
    return std::set<uint64_t>{0};
  auto Layout = std::find_if(
      Fn.Layouts.begin(), Fn.Layouts.end(),
      [&](const VObjectLayout &L) { return L.TypeIdentity == Record->second; });
  if (Layout == Fn.Layouts.end())
    return std::nullopt;
  std::set<uint64_t> Leaves;
  for (const VObjectLeaf &Leaf : Layout->Leaves) {
    std::vector<uint64_t> Offsets = {Leaf.OffsetBytes};
    for (const VObjectRepeat &Repeat : Leaf.Repeats) {
      std::vector<uint64_t> Next;
      for (uint64_t Base : Offsets)
        for (uint64_t K = 0; K < Repeat.Count; ++K) {
          if (Next.size() + Leaves.size() > 4096)
            return std::nullopt;
          Next.push_back(Base + K * Repeat.StrideBytes);
        }
      Offsets = std::move(Next);
    }
    Leaves.insert(Offsets.begin(), Offsets.end());
  }
  return Leaves;
}

/// The leaves written on every path to a point, by offset; an ended path
/// (after a return, break, or continue) reaches no later point.
struct Written {
  std::set<uint64_t> Leaves;
  bool Ended = false;

  static Written join(const Written &A, const Written &B) {
    if (A.Ended)
      return B;
    if (B.Ended)
      return A;
    Written Out;
    std::set_intersection(A.Leaves.begin(), A.Leaves.end(), B.Leaves.begin(),
                          B.Leaves.end(),
                          std::inserter(Out.Leaves, Out.Leaves.begin()));
    return Out;
  }
};

class Analysis {
  const VFunction &Fn;
  const std::string &Param;
  const FunctionsByIdentity &Functions;
  /// The out-parameters assumed so far.
  const PerParameter<bool> &Out;
  /// The leaves each function writes on every path, found so far.
  const PerParameter<std::set<uint64_t>> &Writes;
  /// Whether the walk ends at the first read: the leaves written are not
  /// needed then.
  bool StopAtRead;
  bool Reads = false;
  /// A store through the parameter, or a call passing it to a callee's
  /// out-parameter.
  bool WritesSomewhere = false;
  /// A postcondition, invariant, or check reads its storage.
  bool LaterStateReads = false;
  /// The leaves written at every return.
  std::optional<Written> Exit;

  void read(uint64_t Offset, const Written &W) {
    if (!W.Leaves.count(Offset))
      Reads = true;
  }

  bool stopped(const Written &W) const {
    return W.Ended || (Reads && StopAtRead);
  }

  void exit(const Written &W) {
    if (W.Ended)
      return;
    Exit = Exit ? Written::join(*Exit, W) : W;
  }

  /// Any access through the parameter, where E is evaluated.
  bool readsStorage(const VExpr *E) const {
    if (!E)
      return false;
    if (E->K == VExpr::Load &&
        mentions(static_cast<const VLoadExpr *>(E)->Ptr.get(), Param))
      return true;
    if (E->K == VExpr::SpecCall) {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      auto Callee = Functions.find(C->CalleeIdentity);
      const bool ReadsHeap = C->ReadsHeap || Callee == Functions.end() ||
                             Callee->second->ReadsHeap;
      if (ReadsHeap && llvm::any_of(C->Args, [&](const auto &Arg) {
            return mentions(Arg.get(), Param);
          }))
        return true;
    }
    bool Found = false;
    forEachVExprChild(
        E, [&](const VExpr *Child) { Found = Found || readsStorage(Child); });
    return Found;
  }

  /// The reads of a clause about a later state: those under `old` read the
  /// entry state.
  void laterStateReads(const VExpr *E) {
    LaterStateReads = LaterStateReads || readsStorage(E);
    oldReads(E);
  }

  void oldReads(const VExpr *E) {
    if (!E)
      return;
    if (E->K == VExpr::Old) {
      Reads =
          Reads || readsStorage(static_cast<const VOldExpr *>(E)->Inner.get());
      return;
    }
    forEachVExprChild(E, [&](const VExpr *Child) { oldReads(Child); });
  }

  /// An address computed from the parameter: its index expressions are
  /// evaluated, and anything but a step from the parameter is a use of it.
  void address(const VExpr *E, const Written &W) {
    E = stripCasts(E);
    if (isVar(E, Param))
      return;
    if (E && E->K == VExpr::BinOp) {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      if ((B->Op == VBinOp::Add || B->Op == VBinOp::Sub) &&
          B->Lhs->Ty.Kind == VTypeKind::Ptr && mentions(B->Lhs.get(), Param)) {
        address(B->Lhs.get(), W);
        expr(B->Rhs.get(), W);
        return;
      }
    }
    Reads = true;
  }

  void expr(const VExpr *E, const Written &W) {
    if (!E)
      return;
    switch (E->K) {
    case VExpr::Var:
      // The pointer itself escapes: copied, compared, returned, converted.
      if (static_cast<const VVarExpr *>(E)->Name == Param)
        Reads = true;
      return;
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      expr(L->AccessCondition.get(), W);
      if (!mentions(L->Ptr.get(), Param)) {
        expr(L->Ptr.get(), W);
        return;
      }
      if (auto Offset = offsetFrom(L->Ptr.get(), Param))
        read(*Offset, W);
      else
        Reads = true;
      return;
    }
    case VExpr::Cast:
      // A null test reads nothing.
      if (E->Ty.Kind == VTypeKind::Bool &&
          isVar(static_cast<const VCastExpr *>(E)->Inner.get(), Param))
        return;
      break;
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      if ((B->Op == VBinOp::Eq || B->Op == VBinOp::Ne) &&
          ((isVar(B->Lhs.get(), Param) && constantValue(B->Rhs.get()) == 0) ||
           (isVar(B->Rhs.get(), Param) && constantValue(B->Lhs.get()) == 0)))
        return;
      break;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      if (U->Op == VUnaryOp::ValidPtr && mentions(U->Operand.get(), Param)) {
        address(U->Operand.get(), W);
        return;
      }
      if (U->Op == VUnaryOp::InitializedPtr &&
          mentions(U->Operand.get(), Param)) {
        Reads = true;
        return;
      }
      break;
    }
    case VExpr::SpecCall:
      if (readsStorage(E)) {
        Reads = true;
        return;
      }
      // A spec that does not read memory computes from the address alone.
      for (const auto &Arg : static_cast<const VSpecCallExpr *>(E)->Args)
        if (mentions(Arg.get(), Param))
          address(Arg.get(), W);
        else
          expr(Arg.get(), W);
      return;
    case VExpr::Old:
      Reads =
          Reads || readsStorage(static_cast<const VOldExpr *>(E)->Inner.get());
      return;
    default:
      break;
    }
    forEachVExprChild(E, [&](const VExpr *Child) { expr(Child, W); });
  }

  void call(const VCallStmt &C, Written &W) {
    auto CalleeIt = Functions.find(C.CalleeIdentity);
    const VFunction *Callee =
        CalleeIt == Functions.end() ? nullptr : CalleeIt->second;
    std::set<uint64_t> Initialized;
    for (unsigned I = 0; I < C.Args.size(); ++I) {
      const VExpr *Arg = C.Args[I].get();
      if (!mentions(Arg, Param)) {
        expr(Arg, W);
        continue;
      }
      if (Arg->Ty.Kind != VTypeKind::Ptr || !Callee ||
          I >= Callee->Params.size()) {
        Reads = true;
        continue;
      }
      const std::string &Formal = Callee->Params[I].first;
      address(Arg, W);
      auto Offset = offsetFrom(Arg, Param);
      if (auto CalleeWrites = Writes.find(Callee->Identity);
          Offset && CalleeWrites != Writes.end())
        if (auto Leaves = CalleeWrites->second.find(Formal);
            Leaves != CalleeWrites->second.end())
          for (uint64_t Leaf : Leaves->second)
            Initialized.insert(*Offset + Leaf);
      auto CalleeOut = Out.find(Callee->Identity);
      if (CalleeOut != Out.end() && CalleeOut->second.count(Formal)) {
        WritesSomewhere = true;
        continue;
      }
      // A callee that may read the storage it receives reads all of it, and
      // one with an extent reads more than this analysis follows.
      auto Leaves = pointeeLeaves(*Callee, Formal);
      if (!Offset || !Leaves ||
          llvm::any_of(Callee->ValidExtents, [&](const VValidExtent &E) {
            return E.Base == Formal;
          })) {
        Reads = true;
        continue;
      }
      for (uint64_t Leaf : *Leaves)
        read(*Offset + Leaf, W);
    }
    W.Leaves.insert(Initialized.begin(), Initialized.end());
  }

  void stmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, Written &W) {
    for (const auto &S : Stmts) {
      if (stopped(W))
        return;
      stmt(*S, W);
    }
  }

  void stmt(const VStmt &S, Written &W) {
    if (isBindingInitialization(S, Param))
      return;
    switch (S.K) {
    case VStmt::Assign:
      expr(static_cast<const VAssignStmt &>(S).Value.get(), W);
      return;
    case VStmt::Store: {
      const auto &St = static_cast<const VStoreStmt &>(S);
      expr(St.Value.get(), W);
      expr(St.AccessCondition.get(), W);
      if (!mentions(St.Ptr.get(), Param)) {
        expr(St.Ptr.get(), W);
        return;
      }
      address(St.Ptr.get(), W);
      WritesSomewhere = true;
      if (auto Offset = offsetFrom(St.Ptr.get(), Param))
        W.Leaves.insert(*Offset);
      return;
    }
    case VStmt::Allocate:
      expr(static_cast<const VAllocateStmt &>(S).Initializer.get(), W);
      return;
    case VStmt::Free:
      expr(static_cast<const VFreeStmt &>(S).Ptr.get(), W);
      return;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      expr(I.Cond.get(), W);
      Written Then = W, Else = W;
      stmts(I.Then, Then);
      stmts(I.Else, Else);
      W = Written::join(Then, Else);
      return;
    }
    case VStmt::While: {
      const auto &L = static_cast<const VWhileStmt &>(S);
      // Every iteration starts with at least the leaves written before the
      // loop, and the loop may run no iteration.
      expr(L.Cond.get(), W);
      for (const auto &Invariant : L.Invariants)
        laterStateReads(Invariant.get());
      for (const auto &Measure : L.Decreases)
        expr(Measure.get(), W);
      for (const VFootprint &F : L.Modifies)
        expr(F.Count.get(), W);
      Written Body = W;
      stmts(L.Body, Body);
      return;
    }
    case VStmt::Call:
      call(static_cast<const VCallStmt &>(S), W);
      return;
    case VStmt::Assert:
      expr(static_cast<const VAssertStmt &>(S).Cond.get(), W);
      return;
    case VStmt::Assume:
      expr(static_cast<const VAssumeStmt &>(S).Cond.get(), W);
      return;
    case VStmt::Return:
      expr(static_cast<const VReturnStmt &>(S).Value.get(), W);
      exit(W);
      W.Ended = true;
      return;
    case VStmt::Break:
    case VStmt::Continue:
      W.Ended = true;
      return;
    case VStmt::Seq:
      stmts(static_cast<const VSeqStmt &>(S).Stmts, W);
      return;
    case VStmt::GhostBlock: {
      Written Ghost = W;
      stmts(static_cast<const VGhostBlockStmt &>(S).Body, Ghost);
      return;
    }
    case VStmt::ContractAssert:
      laterStateReads(static_cast<const VContractAssertStmt &>(S).Cond.get());
      return;
    case VStmt::Havoc:
      if (static_cast<const VHavocStmt &>(S).Target == Param)
        Reads = true;
      return;
    case VStmt::EndLifetime:
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
      return;
    }
  }

public:
  Analysis(const VFunction &Fn, const std::string &Param,
           const FunctionsByIdentity &Functions, const PerParameter<bool> &Out,
           const PerParameter<std::set<uint64_t>> &Writes, bool StopAtRead)
      : Fn(Fn), Param(Param), Functions(Functions), Out(Out), Writes(Writes),
        StopAtRead(StopAtRead) {}

  /// The converter's check that a reference bound to part of an object
  /// reads as initialized: initialization of the object asserted, of the
  /// part assumed. Binding reads nothing, and an out-parameter's parts are
  /// tracked themselves, so neither applies to one.
  static bool isBindingInitialization(const VStmt &S,
                                      const std::string &Param) {
    auto IsInitialized = [&](const VExpr *C) {
      return C && C->K == VExpr::UnaryOp &&
             static_cast<const VUnaryOpExpr *>(C)->Op ==
                 VUnaryOp::InitializedPtr &&
             mentions(C, Param);
    };
    if (S.K == VStmt::Assert) {
      const auto &A = static_cast<const VAssertStmt &>(S);
      return A.ProofKind == ProofObligationKind::Initialization &&
             IsInitialized(A.Cond.get());
    }
    if (S.K == VStmt::Assume) {
      const VExpr *C = static_cast<const VAssumeStmt &>(S).Cond.get();
      return C && C->K == VExpr::BinOp &&
             static_cast<const VBinOpExpr *>(C)->Op == VBinOp::And &&
             IsInitialized(static_cast<const VBinOpExpr *>(C)->Rhs.get());
    }
    return false;
  }

  void run() {
    for (const auto &Pre : Fn.Preconditions)
      Reads = Reads || readsStorage(Pre.get());
    for (const auto &E : Fn.Recommends)
      Reads = Reads || readsStorage(E.get());
    for (const auto &E : Fn.Decreases)
      Reads = Reads || readsStorage(E.get());
    for (const auto &[Name, Assumes] : Fn.Behaviors)
      Reads = Reads || readsStorage(Assumes.get());
    for (const auto &[Name, Field] : Fn.FieldParams)
      Reads = Reads || readsStorage(Field.get());
    for (const VFootprint &F : Fn.Modifies)
      Reads = Reads || readsStorage(F.Count.get());
    for (const VValidExtent &Extent : Fn.ValidExtents)
      Reads = Reads || readsStorage(Extent.Length.get());
    for (const auto &Post : Fn.Postconditions)
      laterStateReads(Post.get());
    Written W;
    stmts(Fn.Body, W);
    exit(W);
    if (LaterStateReads && !WritesSomewhere)
      Reads = true;
  }

  /// Whether the function may read the parameter's storage before writing
  /// it.
  bool readsBeforeWriting() const { return Reads; }

  /// The leaves of the parameter's object written at every return.
  std::set<uint64_t> writtenAtExit() const {
    std::set<uint64_t> Out;
    auto Leaves = pointeeLeaves(Fn, Param);
    if (!Exit || !Leaves)
      return Out;
    for (uint64_t Leaf : Exit->Leaves)
      if (Leaves->count(Leaf))
        Out.insert(Leaf);
    return Out;
  }
};

std::set<std::string> candidates(const VFunction &Fn) {
  std::set<std::string> Out;
  if (Fn.IsSpec || Fn.IsProof || Fn.IsExternalContract || Fn.IsTrusted ||
      Fn.IsBuiltin || Fn.UnsupportedConstruct || Fn.TotalExpressions)
    return Out;
  const std::set<std::string> Assigned = assignedNames(Fn.Body);
  for (const auto &[Name, Ty] : Fn.Params) {
    if (Ty.Kind != VTypeKind::Ptr || Ty.PointeeSizeBytes == 0 ||
        Assigned.count(Name) || (Fn.IsConstructor && Name == "this") ||
        llvm::any_of(Fn.FieldParams, [&, &Name = Name](const auto &F) {
          return F.first == Name;
        }))
      continue;
    Out.insert(Name);
  }
  return Out;
}

/// E without the initialization of storage that IsOut names: a conjunct
/// dropped, or true in its place elsewhere.
std::unique_ptr<VExpr>
withoutInitialization(std::unique_ptr<VExpr> E,
                      const std::function<bool(const VExpr *)> &IsOut) {
  if (!E)
    return E;
  if (E->K == VExpr::UnaryOp) {
    auto *U = static_cast<VUnaryOpExpr *>(E.get());
    if (U->Op == VUnaryOp::InitializedPtr && IsOut(U->Operand.get()))
      return std::make_unique<VLiteralExpr>(1, VType::makeBool(), E->Loc);
    return E;
  }
  if (E->K != VExpr::BinOp)
    return E;
  auto *B = static_cast<VBinOpExpr *>(E.get());
  if (B->Op != VBinOp::And && B->Op != VBinOp::Or)
    return E;
  B->Lhs = withoutInitialization(std::move(B->Lhs), IsOut);
  B->Rhs = withoutInitialization(std::move(B->Rhs), IsOut);
  auto IsTrue = [](const VExpr *X) {
    return X->K == VExpr::Literal &&
           static_cast<const VLiteralExpr *>(X)->Value == "1";
  };
  if (B->Op == VBinOp::And && IsTrue(B->Rhs.get()))
    return std::move(B->Lhs);
  if (B->Op == VBinOp::And && IsTrue(B->Lhs.get()))
    return std::move(B->Rhs);
  return E;
}

void dropBindingInitialization(std::vector<std::unique_ptr<VStmt>> &Stmts,
                               const std::set<std::string> &OutParams) {
  auto IsOut = [&](const VExpr *X) {
    return llvm::any_of(
        OutParams, [&](const std::string &Name) { return mentions(X, Name); });
  };
  std::vector<std::unique_ptr<VStmt>> Kept;
  for (auto &S : Stmts) {
    const bool Binding = llvm::any_of(OutParams, [&](const std::string &Name) {
      return Analysis::isBindingInitialization(*S, Name);
    });
    if (Binding && S->K == VStmt::Assert)
      continue;
    if (Binding) {
      auto &A = static_cast<VAssumeStmt &>(*S);
      A.Cond = withoutInitialization(std::move(A.Cond), IsOut);
    }
    switch (S->K) {
    case VStmt::If: {
      auto &I = static_cast<VIfStmt &>(*S);
      dropBindingInitialization(I.Then, OutParams);
      dropBindingInitialization(I.Else, OutParams);
      break;
    }
    case VStmt::While:
      dropBindingInitialization(static_cast<VWhileStmt &>(*S).Body, OutParams);
      break;
    case VStmt::Seq:
      dropBindingInitialization(static_cast<VSeqStmt &>(*S).Stmts, OutParams);
      break;
    case VStmt::GhostBlock:
      dropBindingInitialization(static_cast<VGhostBlockStmt &>(*S).Body,
                                OutParams);
      break;
    default:
      break;
    }
    Kept.push_back(std::move(S));
  }
  Stmts = std::move(Kept);
}

} // namespace

void verify::inferOutParameters(
    std::vector<std::unique_ptr<VFunction>> &Functions) {
  FunctionsByIdentity ByIdentity;
  PerParameter<bool> Out;
  for (const auto &Fn : Functions) {
    ByIdentity[Fn->Identity] = Fn.get();
    for (const std::string &Param : candidates(*Fn))
      Out[Fn->Identity][Param] = true;
  }
  // The leaves written on every path, a least fixpoint: a call writes what
  // the callee was found to write, recursive calls included, so nothing is
  // assumed of a call that only induction would show.
  PerParameter<std::set<uint64_t>> Writes;
  for (bool Changed = true; Changed;) {
    Changed = false;
    for (const auto &Fn : Functions)
      for (const auto &[Param, Unused] : Out[Fn->Identity]) {
        Analysis A(*Fn, Param, ByIdentity, Out, Writes, /*StopAtRead=*/false);
        A.run();
        std::set<uint64_t> &Known = Writes[Fn->Identity][Param];
        std::set<uint64_t> Found = A.writtenAtExit();
        if (Found != Known) {
          Known = std::move(Found);
          Changed = true;
        }
      }
  }
  // The out-parameters, a greatest fixpoint: a call that passes the storage
  // on to a callee's out-parameter reads nothing, recursive calls included.
  for (bool Changed = true; Changed;) {
    Changed = false;
    for (const auto &Fn : Functions) {
      auto &Params = Out[Fn->Identity];
      for (auto It = Params.begin(); It != Params.end();) {
        Analysis A(*Fn, It->first, ByIdentity, Out, Writes,
                   /*StopAtRead=*/true);
        A.run();
        if (A.readsBeforeWriting()) {
          It = Params.erase(It);
          Changed = true;
        } else {
          ++It;
        }
      }
    }
  }
  for (auto &Fn : Functions) {
    for (const auto &[Param, Unused] : Out[Fn->Identity])
      Fn->OutParameters.insert(Param);
    if (Fn->OutParameters.empty())
      continue;
    auto IsOutParameter = [&](const VExpr *X) {
      X = stripCasts(X);
      return X && X->K == VExpr::Var &&
             Fn->OutParameters.count(static_cast<const VVarExpr *>(X)->Name);
    };
    for (size_t I = 0; I != Fn->Preconditions.size(); ++I)
      if (preconditionKind(*Fn, I) == ProofObligationKind::PointerValidity)
        Fn->Preconditions[I] = withoutInitialization(
            std::move(Fn->Preconditions[I]), IsOutParameter);
    dropBindingInitialization(Fn->Body, Fn->OutParameters);
    // What the body writes on every path is initialized at every return.
    for (const std::string &Param : Fn->OutParameters) {
      auto Source = Fn->SourceVariables.find(Param);
      const SourceLocation Loc = Source != Fn->SourceVariables.end()
                                     ? Source->second.Loc
                                     : Fn->DeclLoc;
      for (uint64_t Leaf : Writes[Fn->Identity][Param]) {
        std::unique_ptr<VExpr> Address =
            std::make_unique<VVarExpr>(Param, VType::makePtr(), Loc);
        if (Leaf != 0)
          Address = std::make_unique<VBinOpExpr>(
              VBinOp::Add, std::move(Address),
              std::make_unique<VLiteralExpr>(std::to_string(Leaf),
                                             VType::makePtr(), Loc),
              VType::makePtr(), Loc);
        addPostcondition(*Fn,
                         std::make_unique<VUnaryOpExpr>(
                             VUnaryOp::InitializedPtr, std::move(Address),
                             VType::makeBool(), Loc),
                         ProofObligationKind::Initialization);
      }
    }
  }
}
