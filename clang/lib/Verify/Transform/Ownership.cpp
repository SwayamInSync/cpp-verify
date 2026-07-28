//===--- Ownership.cpp ----------------------------------------------------===//
#include "Ownership.h"
#include <iterator>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace clang;
using namespace verify;

namespace {

struct PointerValue {
  bool Unknown = false;
  bool MayBeNull = false;
  bool NullExcludesRoots = true;
  std::set<unsigned> Roots;
};

struct RootState {
  VFreshOwnedReturn Summary;
  bool Live = true;
  bool Initialized = false;
  bool MayExist = false;
};

struct PathState {
  std::map<std::string, PointerValue> Values;
  std::map<unsigned, RootState> Roots;
};

static bool sameOwnedType(const VFreshOwnedReturn &L,
                          const VFreshOwnedReturn &R) {
  return sameRepresentation(L.AllocatedType, R.AllocatedType) &&
         L.SizeBytes == R.SizeBytes && L.AlignBytes == R.AlignBytes;
}

static PointerValue mergePointerValues(PointerValue L, PointerValue R) {
  PointerValue Out;
  Out.Unknown = L.Unknown || R.Unknown;
  Out.MayBeNull = L.MayBeNull || R.MayBeNull;
  Out.Roots = L.Roots;
  Out.Roots.insert(R.Roots.begin(), R.Roots.end());
  Out.NullExcludesRoots =
      (!L.MayBeNull || (L.NullExcludesRoots && L.Roots == Out.Roots)) &&
      (!R.MayBeNull || (R.NullExcludesRoots && R.Roots == Out.Roots));
  return Out;
}

class OwnedReturnAnalyzer {
  const VFunction &Fn;
  const std::map<std::string, VFreshOwnedReturn> &Summaries;
  unsigned NextRoot = 0;
  bool Invalid = false;
  bool SawOwnedReturn = false;
  bool MayReturnNull = false;
  std::optional<VFreshOwnedReturn> ResultSummary;

  PointerValue evalPointer(const VExpr *E, const PathState &Path) const {
    if (!E || E->Ty.Kind != VTypeKind::Ptr)
      return PointerValue{true};
    switch (E->K) {
    case VExpr::Literal: {
      const auto &L = static_cast<const VLiteralExpr &>(*E);
      if (L.Value == "0")
        return PointerValue{false, true, true, {}};
      return PointerValue{true};
    }
    case VExpr::Var: {
      const auto &V = static_cast<const VVarExpr &>(*E);
      auto It = Path.Values.find(V.Name);
      return It == Path.Values.end() ? PointerValue{true} : It->second;
    }
    case VExpr::Cast:
      return evalPointer(static_cast<const VCastExpr &>(*E).Inner.get(), Path);
    case VExpr::Conditional: {
      const auto &C = static_cast<const VConditionalExpr &>(*E);
      return mergePointerValues(evalPointer(C.Then.get(), Path),
                                evalPointer(C.Else.get(), Path));
    }
    case VExpr::BinOp: {
      const auto &B = static_cast<const VBinOpExpr &>(*E);
      PointerValue Out{true};
      if (B.Lhs->Ty.Kind == VTypeKind::Ptr)
        Out =
            mergePointerValues(std::move(Out), evalPointer(B.Lhs.get(), Path));
      if (B.Rhs->Ty.Kind == VTypeKind::Ptr)
        Out =
            mergePointerValues(std::move(Out), evalPointer(B.Rhs.get(), Path));
      Out.Unknown = true;
      return Out;
    }
    case VExpr::Old:
      return evalPointer(static_cast<const VOldExpr &>(*E).Inner.get(), Path);
    case VExpr::UnaryOp:
    case VExpr::Load:
    case VExpr::Result:
    case VExpr::Forall:
    case VExpr::Exists:
    case VExpr::HeapStore:
    case VExpr::FieldAccess:
    case VExpr::SpecCall:
    case VExpr::OverflowCheck:
      return PointerValue{true};
    }
    return PointerValue{true};
  }

  unsigned addRoot(PathState &Path, const VFreshOwnedReturn &Summary,
                   bool Initialized, bool MayExist) {
    const unsigned Root = ++NextRoot;
    Path.Roots.emplace(Root, RootState{Summary, true, Initialized, MayExist});
    return Root;
  }

  void recordReturn(const PointerValue &Value, const PathState &Path) {
    if (Value.Unknown || Value.Roots.size() > 1) {
      Invalid = true;
      return;
    }

    if (Value.MayBeNull) {
      if (!Value.NullExcludesRoots || Value.Roots.size() != Path.Roots.size()) {
        Invalid = true;
        return;
      }
      MayReturnNull = true;
    }

    if (Value.Roots.empty()) {
      if (!Value.MayBeNull || !Path.Roots.empty())
        Invalid = true;
      return;
    }

    const unsigned Root = *Value.Roots.begin();
    auto It = Path.Roots.find(Root);
    if (It == Path.Roots.end() || Path.Roots.size() != 1 || !It->second.Live ||
        !It->second.Initialized) {
      Invalid = true;
      return;
    }
    if (Value.MayBeNull && !It->second.MayExist) {
      Invalid = true;
      return;
    }
    if (ResultSummary && !sameOwnedType(*ResultSummary, It->second.Summary)) {
      Invalid = true;
      return;
    }
    ResultSummary = It->second.Summary;
    SawOwnedReturn = true;
  }

  std::vector<PathState>
  processStatements(const std::vector<std::unique_ptr<VStmt>> &Statements,
                    std::vector<PathState> Paths) {
    for (const auto &S : Statements) {
      std::vector<PathState> Next;
      for (PathState &Path : Paths) {
        auto Produced = processStatement(*S, std::move(Path));
        Next.insert(Next.end(), std::make_move_iterator(Produced.begin()),
                    std::make_move_iterator(Produced.end()));
      }
      Paths = std::move(Next);
      if (Invalid || Paths.size() > 128) {
        Invalid = true;
        return {};
      }
    }
    return Paths;
  }

  std::vector<PathState> processStatement(const VStmt &S, PathState Path) {
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      if (A.Value && A.Value->Ty.Kind == VTypeKind::Ptr) {
        PointerValue Value = evalPointer(A.Value.get(), Path);
        if (Value.Unknown && !Value.Roots.empty()) {
          Invalid = true;
          return {};
        }
        Path.Values[A.Target] = std::move(Value);
      }
      return single(std::move(Path));
    }
    case VStmt::Store: {
      const auto &Store = static_cast<const VStoreStmt &>(S);
      PointerValue Address = evalPointer(Store.Ptr.get(), Path);
      if (Store.Value && Store.Value->Ty.Kind == VTypeKind::Ptr) {
        PointerValue Stored = evalPointer(Store.Value.get(), Path);
        if (!Stored.Roots.empty()) {
          Invalid = true;
          return {};
        }
      }
      if (!Address.Roots.empty()) {
        if (Address.Unknown || Address.MayBeNull || Address.Roots.size() != 1) {
          Invalid = true;
          return {};
        }
        Path.Roots[*Address.Roots.begin()].Initialized = true;
      }
      return single(std::move(Path));
    }
    case VStmt::Allocate: {
      const auto &A = static_cast<const VAllocateStmt &>(S);
      if (A.IsAutomatic) {
        Path.Values[A.Target] = PointerValue{true};
        return single(std::move(Path));
      }
      VFreshOwnedReturn Summary{A.AllocatedType, A.SizeBytes, A.AlignBytes,
                                false};
      const unsigned Root =
          addRoot(Path, Summary, A.Initializer != nullptr, false);
      Path.Values[A.Target] = PointerValue{false, false, true, {Root}};
      return single(std::move(Path));
    }
    case VStmt::EndLifetime:
      return single(std::move(Path));
    case VStmt::Free: {
      PointerValue Value =
          evalPointer(static_cast<const VFreeStmt &>(S).Ptr.get(), Path);
      if (Value.Unknown || Value.Roots.size() > 1) {
        Invalid = true;
        return {};
      }
      if (!Value.Roots.empty())
        Path.Roots[*Value.Roots.begin()].Live = false;
      return single(std::move(Path));
    }
    case VStmt::If: {
      const auto &If = static_cast<const VIfStmt &>(S);
      std::vector<PathState> Then = processStatements(If.Then, single(Path));
      std::vector<PathState> Else =
          processStatements(If.Else, single(std::move(Path)));
      Then.insert(Then.end(), std::make_move_iterator(Else.begin()),
                  std::make_move_iterator(Else.end()));
      return Then;
    }
    case VStmt::Call: {
      const auto &Call = static_cast<const VCallStmt &>(S);
      for (const auto &Arg : Call.Args)
        if (Arg && Arg->Ty.Kind == VTypeKind::Ptr &&
            !evalPointer(Arg.get(), Path).Roots.empty()) {
          Invalid = true;
          return {};
        }
      auto Summary = Summaries.find(Call.CalleeIdentity);
      if (Summary == Summaries.end() || Call.ResultTarget.empty()) {
        Invalid = true;
        return {};
      }
      const unsigned Root =
          addRoot(Path, Summary->second, true, Summary->second.MayReturnNull);
      Path.Values[Call.ResultTarget] =
          PointerValue{false, Summary->second.MayReturnNull, true, {Root}};
      return single(std::move(Path));
    }
    case VStmt::Return: {
      const auto &Return = static_cast<const VReturnStmt &>(S);
      recordReturn(evalPointer(Return.Value.get(), Path), Path);
      return {};
    }
    case VStmt::Seq:
      return processStatements(static_cast<const VSeqStmt &>(S).Stmts,
                               single(std::move(Path)));
    case VStmt::GhostBlock:
      return processStatements(static_cast<const VGhostBlockStmt &>(S).Body,
                               single(std::move(Path)));
    case VStmt::While:
    case VStmt::Havoc:
      Invalid = true;
      return {};
    case VStmt::Assert:
    case VStmt::Assume:
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
    case VStmt::ContractAssert:
      return single(std::move(Path));
    }
    Invalid = true;
    return {};
  }

  static std::vector<PathState> single(PathState Path) {
    std::vector<PathState> Out;
    Out.push_back(std::move(Path));
    return Out;
  }

public:
  OwnedReturnAnalyzer(const VFunction &Fn,
                      const std::map<std::string, VFreshOwnedReturn> &Summaries)
      : Fn(Fn), Summaries(Summaries) {}

  std::optional<VFreshOwnedReturn> run() {
    if (Fn.IsSpec || Fn.IsProof || Fn.IsExternalContract ||
        Fn.ReturnType.Kind != VTypeKind::Ptr || Fn.Body.empty() ||
        !Fn.Modifies.empty())
      return std::nullopt;
    for (const auto &Param : Fn.Params)
      if (Param.second.Kind == VTypeKind::Ptr)
        return std::nullopt;

    std::vector<PathState> Fallthrough =
        processStatements(Fn.Body, single(PathState{}));
    if (Invalid || !Fallthrough.empty() || !SawOwnedReturn || !ResultSummary)
      return std::nullopt;
    if (Fn.ReturnType.PointeeSizeBytes == 0 ||
        Fn.ReturnType.PointeeSizeBytes != ResultSummary->SizeBytes)
      return std::nullopt;
    ResultSummary->MayReturnNull = MayReturnNull;
    return ResultSummary;
  }
};

} // namespace

void verify::inferFreshOwnedReturns(
    std::vector<std::unique_ptr<VFunction>> &Functions) {
  std::map<std::string, VFreshOwnedReturn> Summaries;
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (auto &Fn : Functions) {
      if (Fn->FreshOwnedReturn)
        continue;
      if (auto Summary = OwnedReturnAnalyzer(*Fn, Summaries).run()) {
        Fn->FreshOwnedReturn = *Summary;
        Summaries.emplace(Fn->Identity, *Summary);
        Changed = true;
      }
    }
  }
}
