//===--- Origins.cpp - Objects pointer variables may address --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Origins.h"
#include "UBChecks.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include <functional>
#include <map>
#include <set>

using namespace clang;
using namespace verify;

namespace {

/// The origins a value may have; nullopt when unknown.
using OriginSet = std::optional<std::set<std::string>>;
/// Each variable's origins; a variable absent from it has unknown ones.
using State = std::map<std::string, OriginSet>;

constexpr size_t MaxOrigins = 8;

OriginSet join(const OriginSet &A, const OriginSet &B) {
  if (!A || !B)
    return std::nullopt;
  std::set<std::string> Both = *A;
  Both.insert(B->begin(), B->end());
  if (Both.size() > MaxOrigins)
    return std::nullopt;
  return Both;
}

/// Unreachable states are nullopt.
std::optional<State> join(const std::optional<State> &A,
                          const std::optional<State> &B) {
  if (!A)
    return B;
  if (!B)
    return A;
  State Out;
  for (const auto &[Name, Origins] : *A)
    if (auto It = B->find(Name); It != B->end())
      Out[Name] = join(Origins, It->second);
  return Out;
}

const std::string CompanionSuffix = ".__origin";

/// A global's origin: "@address/size".
std::string globalOrigin(const VExpr &Literal) {
  return "@" + static_cast<const VLiteralExpr &>(Literal).Value + "/" +
         std::to_string(Literal.Ty.PointeeSizeBytes);
}

std::unique_ptr<VExpr> boolLiteral(bool Value, SourceLocation Loc) {
  return std::make_unique<VLiteralExpr>(Value, VType::makeBool(), Loc);
}

VType identityType() { return VType::makeInt(VIntMode::Math, 64, true); }

class OriginAnalysis {
public:
  explicit OriginAnalysis(VFunction &Fn) : Fn(Fn) {}

  void run() {
    State Entry;
    Objects = abstractObjects(Fn);
    for (const AbstractObject &Object : Objects)
      Entry[Object.Name] = std::set<std::string>{Object.Name};
    for (const auto &[Name, Ty] : Fn.Params)
      if (Ty.Kind == VTypeKind::Ptr && !Entry.count(Name))
        Entry[Name] = std::nullopt;
    EntryState = Entry;

    for (auto &Pre : Fn.Preconditions)
      annotate(Pre.get(), Entry, false);
    for (auto &Post : Fn.Postconditions)
      annotate(Post.get(), Entry, true);
    for (VFootprint &F : Fn.Modifies) {
      annotate(F.Target.get(), Entry, false);
      annotate(F.Count.get(), Entry, false);
    }
    Annotating = true;
    transfer(Fn.Body, Entry, nullptr);
    Annotating = false;

    std::vector<std::unique_ptr<VStmt>> Prologue;
    for (const auto &[Name, Ty] : Fn.Params)
      if (Multi.count(Name) && EntryState[Name] &&
          EntryState[Name]->size() == 1)
        Prologue.push_back(std::make_unique<VAssignStmt>(
            Name + CompanionSuffix,
            originIdentity(*EntryState[Name]->begin(), Fn.DeclLoc),
            Fn.DeclLoc));
    addCompanions(Fn.Body);
    Fn.Body.insert(Fn.Body.begin(), std::make_move_iterator(Prologue.begin()),
                   std::make_move_iterator(Prologue.end()));
  }

private:
  struct LoopExits {
    std::optional<State> Breaks;
    std::optional<State> Continues;
  };

  VFunction &Fn;
  std::vector<AbstractObject> Objects;
  State EntryState;
  bool Annotating = false;
  /// Variables some occurrence of which may hold several origins.
  std::set<std::string> Multi;
  /// Each loop's state at its head.
  std::map<const VWhileStmt *, State> Heads;

  static OriginSet lookup(const State &S, const std::string &Name) {
    auto It = S.find(Name);
    return It == S.end() ? std::nullopt : It->second;
  }

  OriginSet originsOf(const VExpr *E, const State &S) const {
    if (!E)
      return std::nullopt;
    switch (E->K) {
    case VExpr::Var: {
      const auto *V = static_cast<const VVarExpr *>(E);
      if (V->Ty.Kind != VTypeKind::Ptr || !V->ProvenanceVariable.empty())
        return std::nullopt;
      return lookup(S, V->Name);
    }
    case VExpr::Literal: {
      if (E->Ty.Kind != VTypeKind::Ptr)
        return std::nullopt;
      const std::string &Value = static_cast<const VLiteralExpr *>(E)->Value;
      if (Value == "0")
        return std::set<std::string>{};
      return std::set<std::string>{globalOrigin(*E)};
    }
    case VExpr::Cast: {
      const auto *C = static_cast<const VCastExpr *>(E);
      if (C->Ty.Kind != VTypeKind::Ptr || C->Inner->Ty.Kind != VTypeKind::Ptr)
        return std::nullopt;
      return originsOf(C->Inner.get(), S);
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      if (B->Op != VBinOp::Add && B->Op != VBinOp::Sub)
        return std::nullopt;
      const bool Left = B->Lhs->Ty.Kind == VTypeKind::Ptr;
      const bool Right = B->Rhs->Ty.Kind == VTypeKind::Ptr;
      if (Left && !Right)
        return originsOf(B->Lhs.get(), S);
      if (Right && !Left && B->Op == VBinOp::Add)
        return originsOf(B->Rhs.get(), S);
      return std::nullopt;
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      return join(originsOf(C->Then.get(), S), originsOf(C->Else.get(), S));
    }
    case VExpr::Old:
      return originsOf(static_cast<const VOldExpr *>(E)->Inner.get(),
                       EntryState);
    default:
      return std::nullopt;
    }
  }

  void annotate(VExpr *E, const State &S, bool AtEntry) {
    if (!E)
      return;
    if (E->K == VExpr::Var) {
      auto *V = static_cast<VVarExpr *>(E);
      if (V->Ty.Kind != VTypeKind::Ptr || !V->ProvenanceVariable.empty())
        return;
      OriginSet Origins = lookup(AtEntry ? EntryState : S, V->Name);
      V->OriginCompanion.clear();
      if (Origins) {
        V->Origins = std::vector<std::string>(Origins->begin(), Origins->end());
        if (Origins->size() > 1) {
          Multi.insert(V->Name);
          V->OriginCompanion = V->Name + CompanionSuffix;
        }
      } else {
        V->Origins.reset();
      }
      return;
    }
    const bool Entry = AtEntry || E->K == VExpr::Old;
    forEachVExprChildSlot(E, [&](std::unique_ptr<VExpr> &Child) {
      annotate(Child.get(), S, Entry);
    });
  }

  void annotateIn(VExpr *E, const std::optional<State> &S) {
    if (Annotating && S)
      annotate(E, *S, false);
  }

  std::optional<State> transfer(std::vector<std::unique_ptr<VStmt>> &Stmts,
                                std::optional<State> S, LoopExits *Loop) {
    for (auto &Stmt : Stmts)
      S = transfer(*Stmt, std::move(S), Loop);
    return S;
  }

  std::optional<State> transfer(VStmt &Stmt, std::optional<State> S,
                                LoopExits *Loop) {
    switch (Stmt.K) {
    case VStmt::Assign: {
      auto &A = static_cast<VAssignStmt &>(Stmt);
      annotateIn(A.Value.get(), S);
      if (S)
        (*S)[A.Target] = A.Value && A.Value->Ty.Kind == VTypeKind::Ptr
                             ? originsOf(A.Value.get(), *S)
                             : std::nullopt;
      return S;
    }
    case VStmt::Store: {
      auto &St = static_cast<VStoreStmt &>(Stmt);
      annotateIn(St.Ptr.get(), S);
      annotateIn(St.Value.get(), S);
      annotateIn(St.AccessCondition.get(), S);
      return S;
    }
    case VStmt::Allocate: {
      auto &A = static_cast<VAllocateStmt &>(Stmt);
      annotateIn(A.Initializer.get(), S);
      if (S)
        (*S)[A.Target] = std::nullopt;
      return S;
    }
    case VStmt::Free:
      annotateIn(static_cast<VFreeStmt &>(Stmt).Ptr.get(), S);
      return S;
    case VStmt::Call: {
      auto &C = static_cast<VCallStmt &>(Stmt);
      for (auto &Arg : C.Args)
        annotateIn(Arg.get(), S);
      if (S && !C.ResultTarget.empty())
        (*S)[C.ResultTarget] = std::nullopt;
      return S;
    }
    case VStmt::Havoc:
      if (S)
        (*S)[static_cast<VHavocStmt &>(Stmt).Target] = std::nullopt;
      return S;
    case VStmt::Assert:
      annotateIn(static_cast<VAssertStmt &>(Stmt).Cond.get(), S);
      return S;
    case VStmt::Assume:
      annotateIn(static_cast<VAssumeStmt &>(Stmt).Cond.get(), S);
      return S;
    case VStmt::ContractAssert:
      annotateIn(static_cast<VContractAssertStmt &>(Stmt).Cond.get(), S);
      return S;
    case VStmt::Return:
      annotateIn(static_cast<VReturnStmt &>(Stmt).Value.get(), S);
      return std::nullopt;
    case VStmt::Break:
      if (Loop)
        Loop->Breaks = join(Loop->Breaks, S);
      return std::nullopt;
    case VStmt::Continue:
      if (Loop)
        Loop->Continues = join(Loop->Continues, S);
      return std::nullopt;
    case VStmt::Seq:
      return transfer(static_cast<VSeqStmt &>(Stmt).Stmts, std::move(S), Loop);
    case VStmt::GhostBlock:
      return transfer(static_cast<VGhostBlockStmt &>(Stmt).Body, std::move(S),
                      Loop);
    case VStmt::If: {
      auto &I = static_cast<VIfStmt &>(Stmt);
      annotateIn(I.Cond.get(), S);
      auto Then = transfer(I.Then, S, Loop);
      auto Else = transfer(I.Else, S, Loop);
      return join(Then, Else);
    }
    case VStmt::While:
      return transferLoop(static_cast<VWhileStmt &>(Stmt), std::move(S));
    default:
      return S;
    }
  }

  std::optional<State> transferLoop(VWhileStmt &W, std::optional<State> S) {
    if (!S)
      return std::nullopt;
    // The head state is the least fixpoint above the entry state; sets are
    // bounded, so it is reached.
    const bool Outer = Annotating;
    Annotating = false;
    State Head = *S;
    LoopExits Exits;
    while (true) {
      Exits = LoopExits{};
      auto End = transfer(W.Body, Head, &Exits);
      auto Next = join(join(std::optional<State>(*S), End), Exits.Continues);
      if (*Next == Head)
        break;
      Head = std::move(*Next);
    }
    Annotating = Outer;
    if (Annotating) {
      Heads[&W] = Head;
      annotate(W.Cond.get(), Head, false);
      for (auto &Invariant : W.Invariants)
        annotate(Invariant.get(), Head, false);
      for (auto &Measure : W.Decreases)
        annotate(Measure.get(), Head, false);
      for (VFootprint &F : W.Modifies) {
        annotate(F.Target.get(), Head, false);
        annotate(F.Count.get(), Head, false);
      }
      Exits = LoopExits{};
      transfer(W.Body, Head, &Exits);
    }
    return join(std::optional<State>(Head), Exits.Breaks);
  }

  /// Assign each multi-origin variable's companion beside it, and keep a
  /// companion a loop changes among its possible origins.
  void addCompanions(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    for (size_t I = 0; I < Stmts.size(); ++I) {
      VStmt &S = *Stmts[I];
      switch (S.K) {
      case VStmt::Assign: {
        auto &A = static_cast<VAssignStmt &>(S);
        if (!Multi.count(A.Target))
          break;
        auto Term = A.Value ? pointerOriginTerm(A.Value.get()) : nullptr;
        // A step keeps the companion: leaving it unassigned keeps it out of
        // the loop's changed state.
        if (!Term || (Term->K == VExpr::Var &&
                      static_cast<const VVarExpr &>(*Term).Name ==
                          A.Target + CompanionSuffix))
          break;
        Stmts.insert(Stmts.begin() + I + 1,
                     std::make_unique<VAssignStmt>(A.Target + CompanionSuffix,
                                                   std::move(Term), A.Loc));
        ++I;
        break;
      }
      case VStmt::Seq:
        addCompanions(static_cast<VSeqStmt &>(S).Stmts);
        break;
      case VStmt::GhostBlock:
        addCompanions(static_cast<VGhostBlockStmt &>(S).Body);
        break;
      case VStmt::If:
        addCompanions(static_cast<VIfStmt &>(S).Then);
        addCompanions(static_cast<VIfStmt &>(S).Else);
        break;
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(S);
        addCompanions(W.Body);
        const State &Head = Heads[&W];
        std::set<std::string> Changed;
        assignedCompanions(W.Body, Changed);
        for (const auto &[Name, Stride] : steppedPointers(W.Body))
          if (auto Aligned = alignedInOrigins(Name, Stride, Head, W.Loc))
            W.Invariants.push_back(std::move(Aligned));
        for (const std::string &Name : Changed) {
          OriginSet Origins = lookup(Head, Name);
          if (!Origins || Origins->empty())
            continue;
          std::unique_ptr<VExpr> Among = boolLiteral(false, W.Loc);
          for (const std::string &Origin : *Origins)
            Among = std::make_unique<VBinOpExpr>(
                VBinOp::Or, std::move(Among),
                std::make_unique<VBinOpExpr>(
                    VBinOp::Eq,
                    std::make_unique<VVarExpr>(Name + CompanionSuffix,
                                               identityType(), W.Loc),
                    originIdentity(Origin, W.Loc), VType::makeBool(), W.Loc),
                VType::makeBool(), W.Loc);
          W.Invariants.push_back(std::move(Among));
        }
        break;
      }
      default:
        break;
      }
    }
  }

  /// The pointer variables Stmts assign, with their element sizes.
  static std::map<std::string, uint64_t>
  steppedPointers(const std::vector<std::unique_ptr<VStmt>> &Stmts) {
    std::map<std::string, uint64_t> Out;
    std::function<void(const std::vector<std::unique_ptr<VStmt>> &)> Visit =
        [&](const std::vector<std::unique_ptr<VStmt>> &Body) {
          for (const auto &S : Body) {
            switch (S->K) {
            case VStmt::Assign: {
              const auto &A = static_cast<const VAssignStmt &>(*S);
              if (A.Value && A.Value->Ty.Kind == VTypeKind::Ptr &&
                  A.Value->Ty.PointeeSizeBytes != 0)
                Out[A.Target] = A.Value->Ty.PointeeSizeBytes;
              break;
            }
            case VStmt::Seq:
              Visit(static_cast<const VSeqStmt &>(*S).Stmts);
              break;
            case VStmt::GhostBlock:
              Visit(static_cast<const VGhostBlockStmt &>(*S).Body);
              break;
            case VStmt::If:
              Visit(static_cast<const VIfStmt &>(*S).Then);
              Visit(static_cast<const VIfStmt &>(*S).Else);
              break;
            case VStmt::While:
              Visit(static_cast<const VWhileStmt &>(*S).Body);
              break;
            default:
              break;
            }
          }
        };
    Visit(Stmts);
    return Out;
  }

  /// Name, a pointer of Stride-byte elements a loop moves, lies at an element
  /// of the object its origin names (or is null): pointer arithmetic moves by
  /// whole elements. A generated invariant, so it is proved, not assumed.
  std::unique_ptr<VExpr> alignedInOrigins(const std::string &Name,
                                          uint64_t Stride, const State &Head,
                                          SourceLocation Loc) const {
    OriginSet Origins = lookup(Head, Name);
    if (!Origins || Origins->empty())
      return nullptr;
    const VType Integer = identityType();
    const VType Pointer = VType::makePtr(Stride);
    // Addresses are positive, so q lies at a whole element from o exactly
    // when both leave the same remainder.
    auto remainder = [&](std::unique_ptr<VExpr> P) {
      return std::make_unique<VBinOpExpr>(
          VBinOp::Rem, std::move(P),
          std::make_unique<VLiteralExpr>(std::to_string(Stride), Pointer, Loc),
          Pointer, Loc);
    };
    std::unique_ptr<VExpr> All = boolLiteral(true, Loc);
    for (const std::string &Origin : *Origins) {
      std::unique_ptr<VExpr> Start;
      if (isGlobalOrigin(Origin)) {
        Start = std::make_unique<VLiteralExpr>(globalOriginExtent(Origin).first,
                                               Pointer, Loc);
      } else {
        auto Object = llvm::find_if(
            Objects, [&](const AbstractObject &O) { return O.Name == Origin; });
        if (Object == Objects.end() ||
            Object->PointerType.PointeeSizeBytes != Stride)
          return nullptr;
        Start = std::make_unique<VOldExpr>(
            std::make_unique<VVarExpr>(Origin, Object->PointerType, Loc),
            Object->PointerType, Loc);
      }
      std::unique_ptr<VExpr> Aligned = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, remainder(std::make_unique<VVarExpr>(Name, Pointer, Loc)),
          remainder(std::move(Start)), VType::makeBool(), Loc);
      if (Origins->size() > 1)
        Aligned = std::make_unique<VBinOpExpr>(
            VBinOp::Or,
            std::make_unique<VBinOpExpr>(
                VBinOp::Ne,
                std::make_unique<VVarExpr>(Name + CompanionSuffix, Integer,
                                           Loc),
                originIdentity(Origin, Loc), VType::makeBool(), Loc),
            std::move(Aligned), VType::makeBool(), Loc);
      All = std::make_unique<VBinOpExpr>(VBinOp::And, std::move(All),
                                         std::move(Aligned), VType::makeBool(),
                                         Loc);
    }
    auto Null = std::make_unique<VBinOpExpr>(
        VBinOp::Eq, std::make_unique<VVarExpr>(Name, Pointer, Loc),
        std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
        VType::makeBool(), Loc);
    return std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(Null),
                                        std::move(All), VType::makeBool(), Loc);
  }

  void assignedCompanions(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                          std::set<std::string> &Out) const {
    for (const auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign: {
        const auto &A = static_cast<const VAssignStmt &>(*S);
        llvm::StringRef Target(A.Target);
        if (Target.consume_back(CompanionSuffix))
          Out.insert(Target.str());
        break;
      }
      case VStmt::Seq:
        assignedCompanions(static_cast<const VSeqStmt &>(*S).Stmts, Out);
        break;
      case VStmt::GhostBlock:
        assignedCompanions(static_cast<const VGhostBlockStmt &>(*S).Body, Out);
        break;
      case VStmt::If:
        assignedCompanions(static_cast<const VIfStmt &>(*S).Then, Out);
        assignedCompanions(static_cast<const VIfStmt &>(*S).Else, Out);
        break;
      case VStmt::While:
        assignedCompanions(static_cast<const VWhileStmt &>(*S).Body, Out);
        break;
      default:
        break;
      }
    }
  }
};

} // namespace

bool verify::isGlobalOrigin(const std::string &Origin) {
  return !Origin.empty() && Origin[0] == '@';
}

std::pair<std::string, uint64_t>
verify::globalOriginExtent(const std::string &Origin) {
  auto [Address, Size] = llvm::StringRef(Origin).drop_front().split('/');
  uint64_t Bytes = 0;
  if (Size.getAsInteger(10, Bytes))
    Bytes = 0;
  return {Address.str(), Bytes};
}

std::unique_ptr<VExpr> verify::originIdentity(const std::string &Origin,
                                              SourceLocation Loc) {
  // Injective: a global is its address; a parameter is the negated number
  // whose base-256 digits are its name's bytes.
  if (isGlobalOrigin(Origin))
    return std::make_unique<VLiteralExpr>(
        llvm::StringRef(Origin).drop_front().split('/').first.str(),
        identityType(), Loc);
  llvm::APInt Value(8 * Origin.size() + 8, 0);
  for (char C : llvm::reverse(Origin)) {
    Value <<= 8;
    Value |= static_cast<unsigned char>(C);
  }
  llvm::SmallString<64> Digits;
  Value.toString(Digits, 10, /*Signed=*/false);
  return std::make_unique<VLiteralExpr>("-" + std::string(Digits),
                                        identityType(), Loc);
}

std::optional<std::vector<std::string>> verify::pointerOrigins(const VExpr *E) {
  if (!E)
    return std::nullopt;
  switch (E->K) {
  case VExpr::Var:
    return static_cast<const VVarExpr *>(E)->Origins;
  case VExpr::Literal: {
    if (E->Ty.Kind != VTypeKind::Ptr)
      return std::nullopt;
    const std::string &Value = static_cast<const VLiteralExpr *>(E)->Value;
    if (Value == "0")
      return std::vector<std::string>{};
    return std::vector<std::string>{globalOrigin(*E)};
  }
  case VExpr::Cast:
    return pointerOrigins(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if (B->Op != VBinOp::Add && B->Op != VBinOp::Sub)
      return std::nullopt;
    const bool Left = B->Lhs->Ty.Kind == VTypeKind::Ptr;
    const bool Right = B->Rhs->Ty.Kind == VTypeKind::Ptr;
    if (Left && !Right)
      return pointerOrigins(B->Lhs.get());
    if (Right && !Left && B->Op == VBinOp::Add)
      return pointerOrigins(B->Rhs.get());
    return std::nullopt;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    auto Then = pointerOrigins(C->Then.get());
    auto Else = pointerOrigins(C->Else.get());
    if (!Then || !Else)
      return std::nullopt;
    std::set<std::string> Both(Then->begin(), Then->end());
    Both.insert(Else->begin(), Else->end());
    return std::vector<std::string>(Both.begin(), Both.end());
  }
  default:
    return std::nullopt;
  }
}

std::unique_ptr<VExpr> verify::pointerOriginTerm(const VExpr *E) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (!V->Origins)
      return nullptr;
    if (V->Origins->empty())
      return std::make_unique<VLiteralExpr>(0, identityType(), V->Loc);
    if (V->Origins->size() == 1)
      return originIdentity(V->Origins->front(), V->Loc);
    if (V->OriginCompanion.empty())
      return nullptr;
    return std::make_unique<VVarExpr>(V->OriginCompanion, identityType(),
                                      V->Loc);
  }
  case VExpr::Literal: {
    const std::string &Value = static_cast<const VLiteralExpr *>(E)->Value;
    if (E->Ty.Kind != VTypeKind::Ptr)
      return nullptr;
    if (Value == "0")
      return std::make_unique<VLiteralExpr>(0, identityType(), E->Loc);
    return originIdentity(globalOrigin(*E), E->Loc);
  }
  case VExpr::Cast:
    return pointerOriginTerm(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if (B->Op != VBinOp::Add && B->Op != VBinOp::Sub)
      return nullptr;
    const bool Left = B->Lhs->Ty.Kind == VTypeKind::Ptr;
    const bool Right = B->Rhs->Ty.Kind == VTypeKind::Ptr;
    if (Left && !Right)
      return pointerOriginTerm(B->Lhs.get());
    if (Right && !Left && B->Op == VBinOp::Add)
      return pointerOriginTerm(B->Rhs.get());
    return nullptr;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    auto Then = pointerOriginTerm(C->Then.get());
    auto Else = pointerOriginTerm(C->Else.get());
    if (!Then || !Else)
      return nullptr;
    return std::make_unique<VConditionalExpr>(cloneVExpr(C->Cond.get()),
                                              std::move(Then), std::move(Else),
                                              identityType(), C->Loc);
  }
  default:
    return nullptr;
  }
}

void verify::annotatePointerOrigins(VFunction &Fn) {
  if (Fn.IsSpec)
    return;
  OriginAnalysis(Fn).run();
}
