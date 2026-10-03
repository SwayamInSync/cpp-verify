//===--- Inductive.cpp - Inductive predicates -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// An inductive predicate P is the least fixpoint of its body F: true where a
// finite derivation shows it. Predicates that apply each other form a group,
// defined together. Each member is defined as exists(h, P.step(h, x)), where
// the step-indexed P.step(h, x) is h > 0 && F with every application Q(a) of
// a member read as Q.step(h - 1, a). Proofs see P through its unfolding
// P(x) == F(x), which the driver lets them use only once three generated
// proof functions per member are proved:
//
//  - monotonicity: P.step(h, x) && h <= j implies P.step(j, x), by induction
//    on h;
//  - case analysis: P(x) implies F(x), at the height P.height(x) chosen for
//    x;
//  - introduction: F(x) implies P(x), at a height built here: one more than
//    the heights of the applications F uses, taken at the witnesses chosen
//    for its existentials and maximized over its bounded universals by
//    generated recursive specs.
//
// The proofs never ask a solver to invent a height or a witness: every term
// they need is named, and each universal is generalized from a fresh value.
//
//===----------------------------------------------------------------------===//

#include "Inductive.h"
#include "SpecInline.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>
#include <map>
#include <set>

using namespace clang;
using namespace clang::verify;

namespace {

using Expr = std::unique_ptr<VExpr>;
using Stmts = std::vector<std::unique_ptr<VStmt>>;
using Env = std::map<std::string, Expr>;

const VType HeightType = VType::makeInt(VIntMode::Math, 64);

bool appliesAny(const VExpr *E, const std::set<std::string> &Group) {
  if (!E)
    return false;
  if (E->K == VExpr::SpecCall &&
      Group.count(static_cast<const VSpecCallExpr *>(E)->CalleeIdentity))
    return true;
  bool Found = false;
  forEachVExprChild(E, [&](const VExpr *Child) {
    Found = Found || appliesAny(Child, Group);
  });
  return Found;
}

/// The statements still to run, innermost block last.
using StmtCursor =
    std::vector<std::pair<const std::vector<std::unique_ptr<VStmt>> *, size_t>>;

/// The value a body returns, as one expression, when it consists of returns
/// under if and else; null otherwise.
Expr returnedValue(StmtCursor Cursor) {
  while (!Cursor.empty() && Cursor.back().second == Cursor.back().first->size())
    Cursor.pop_back();
  if (Cursor.empty())
    return nullptr;
  const VStmt *S = (*Cursor.back().first)[Cursor.back().second++].get();
  switch (S->K) {
  case VStmt::Return:
    return cloneVExpr(static_cast<const VReturnStmt *>(S)->Value.get());
  case VStmt::Seq:
    Cursor.push_back({&static_cast<const VSeqStmt *>(S)->Stmts, 0});
    return returnedValue(std::move(Cursor));
  case VStmt::If: {
    const auto *If = static_cast<const VIfStmt *>(S);
    StmtCursor Else = Cursor;
    Cursor.push_back({&If->Then, 0});
    Else.push_back({&If->Else, 0});
    auto Then = returnedValue(std::move(Cursor));
    auto Otherwise = returnedValue(std::move(Else));
    if (!If->Cond || !Then || !Otherwise)
      return nullptr;
    const VType Ty = Then->Ty;
    return std::make_unique<VConditionalExpr>(
        cloneVExpr(If->Cond.get()), std::move(Then), std::move(Otherwise), Ty,
        If->Loc);
  }
  default:
    return nullptr;
  }
}

/// Where a member of \p Group occurs in \p E other than positively, or empty:
/// only as a conjunct, a disjunct, a branch, or the body of exists or of a
/// bounded forall, so that the body is monotone and continuous in it.
std::string nonPositiveOccurrence(const VExpr *E,
                                  const std::set<std::string> &Group) {
  if (!appliesAny(E, Group))
    return "";
  switch (E->K) {
  case VExpr::SpecCall: {
    const auto *Call = static_cast<const VSpecCallExpr *>(E);
    if (!Group.count(Call->CalleeIdentity))
      return "in an argument of " + Call->Callee;
    return llvm::any_of(
               Call->Args,
               [&](const Expr &Arg) { return appliesAny(Arg.get(), Group); })
               ? "in its own argument"
               : "";
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if (B->Op != VBinOp::And && B->Op != VBinOp::Or)
      return "in a comparison or arithmetic";
    std::string Why = nonPositiveOccurrence(B->Lhs.get(), Group);
    return Why.empty() ? nonPositiveOccurrence(B->Rhs.get(), Group) : Why;
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    if (!C->IsTrigger &&
        !(C->Ty.Kind == VTypeKind::Bool && C->FromTy.Kind == VTypeKind::Bool))
      return "in a conversion";
    return nonPositiveOccurrence(C->Inner.get(), Group);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    if (appliesAny(C->Cond.get(), Group))
      return "in a condition";
    std::string Why = nonPositiveOccurrence(C->Then.get(), Group);
    return Why.empty() ? nonPositiveOccurrence(C->Else.get(), Group) : Why;
  }
  case VExpr::Exists:
  case VExpr::Forall: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    if (appliesAny(Q->Lo.get(), Group) || appliesAny(Q->Hi.get(), Group))
      return "in the bounds of a quantifier";
    if (E->K == VExpr::Forall && !Q->Lo)
      return "under a forall without bounds";
    return nonPositiveOccurrence(Q->Body.get(), Group);
  }
  case VExpr::UnaryOp:
    return "under negation";
  default:
    return "in this position";
  }
}

const VExpr *withoutCasts(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  return E;
}

bool mentionsResult(const VExpr *E) {
  if (!E)
    return false;
  if (E->K == VExpr::Result)
    return true;
  bool Found = false;
  forEachVExprChild(
      E, [&](const VExpr *Child) { Found = Found || mentionsResult(Child); });
  return Found;
}

void disjuncts(const VExpr *E, std::vector<const VExpr *> &Out) {
  E = withoutCasts(E);
  if (E && E->K == VExpr::BinOp &&
      static_cast<const VBinOpExpr *>(E)->Op == VBinOp::Or) {
    disjuncts(static_cast<const VBinOpExpr *>(E)->Lhs.get(), Out);
    disjuncts(static_cast<const VBinOpExpr *>(E)->Rhs.get(), Out);
    return;
  }
  Out.push_back(E);
}

/// Whether a postcondition has the form !result || Q, Q free of result.
bool describesDerivations(const VExpr *Post) {
  std::vector<const VExpr *> Parts;
  disjuncts(Post, Parts);
  bool Negated = false;
  for (const VExpr *Part : Parts) {
    if (!Negated && Part && Part->K == VExpr::UnaryOp &&
        static_cast<const VUnaryOpExpr *>(Part)->Op == VUnaryOp::Not &&
        withoutCasts(static_cast<const VUnaryOpExpr *>(Part)->Operand.get())
                ->K == VExpr::Result)
      Negated = true;
    else if (!Part || mentionsResult(Part))
      return false;
  }
  return Negated;
}

void replaceVariable(Expr &E, const std::string &Name, const VExpr &With) {
  if (!E)
    return;
  if (E->K == VExpr::Var && static_cast<VVarExpr &>(*E).Name == Name) {
    E = cloneVExpr(&With);
    return;
  }
  forEachVExprChildSlot(
      E.get(), [&](Expr &Child) { replaceVariable(Child, Name, With); });
}

/// The variables \p E reads that no quantifier within it binds, in order of
/// first occurrence.
void freeVariables(const VExpr *E, std::set<std::string> &Bound,
                   std::vector<std::pair<std::string, VType>> &Out) {
  if (!E)
    return;
  if (E->K == VExpr::Var) {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (!Bound.count(V->Name) && llvm::none_of(Out, [&](const auto &Seen) {
          return Seen.first == V->Name;
        }))
      Out.push_back({V->Name, V->Ty});
    return;
  }
  const bool Binds = E->K == VExpr::Forall || E->K == VExpr::Exists;
  const std::string Binder =
      Binds ? static_cast<const VQuantifiedExpr *>(E)->Binder : "";
  if (Binds) {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    freeVariables(Q->Lo.get(), Bound, Out);
    freeVariables(Q->Hi.get(), Bound, Out);
    const bool Inserted = Bound.insert(Binder).second;
    freeVariables(Q->Body.get(), Bound, Out);
    if (Inserted)
      Bound.erase(Binder);
    return;
  }
  forEachVExprChild(
      E, [&](const VExpr *Child) { freeVariables(Child, Bound, Out); });
}

std::vector<std::pair<std::string, VType>> freeVariables(const VExpr *E) {
  std::set<std::string> Bound;
  std::vector<std::pair<std::string, VType>> Out;
  freeVariables(E, Bound, Out);
  return Out;
}

bool readsHeap(const VExpr *E) {
  if (!E)
    return false;
  if (E->K == VExpr::Load || (E->K == VExpr::SpecCall &&
                              static_cast<const VSpecCallExpr *>(E)->ReadsHeap))
    return true;
  bool Found = false;
  forEachVExprChild(
      E, [&](const VExpr *Child) { Found = Found || readsHeap(Child); });
  return Found;
}

/// The members of one group and what is generated for each.
struct Member {
  VFunction *Predicate = nullptr;
  Expr Unfolding;
  VFunction *Step = nullptr;
  VFunction *Height = nullptr;
  VFunction *Monotone = nullptr;
};

class GroupExpander {
  std::vector<Member> Members;
  std::set<std::string> Group;
  std::set<std::string> Withheld;
  std::map<std::string, Member *> ByIdentity;
  std::vector<std::unique_ptr<VFunction>> &Generated;
  SourceLocation Loc;
  unsigned Fresh = 0;
  std::map<const VExpr *, VFunction *> Witnesses;
  std::map<const VExpr *, VFunction *> Bounds;
  std::map<std::string, std::vector<bool>> Fixed;

  // Expressions.
  Expr var(const std::string &Name, VType Ty) const {
    return std::make_unique<VVarExpr>(Name, Ty, Loc);
  }
  Expr literal(int64_t Value, VType Ty) const {
    return std::make_unique<VLiteralExpr>(Value, Ty, Loc);
  }
  Expr boolean(VBinOp Op, Expr L, Expr R) const {
    return std::make_unique<VBinOpExpr>(Op, std::move(L), std::move(R),
                                        VType::makeBool(), Loc);
  }
  Expr arithmetic(VBinOp Op, Expr L, Expr R) const {
    return std::make_unique<VBinOpExpr>(Op, std::move(L), std::move(R),
                                        HeightType, Loc);
  }
  Expr negation(Expr E) const {
    return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                          VType::makeBool(), Loc);
  }
  Expr implies(Expr A, Expr B) const {
    return boolean(VBinOp::Or, negation(std::move(A)), std::move(B));
  }
  static bool isZero(const VExpr *E) {
    return E->K == VExpr::Literal &&
           static_cast<const VLiteralExpr *>(E)->Value == "0";
  }
  Expr maximum(Expr A, Expr B) const {
    if (isZero(A.get()))
      return B;
    if (isZero(B.get()))
      return A;
    auto Larger = boolean(VBinOp::Ge, cloneVExpr(A.get()), cloneVExpr(B.get()));
    return std::make_unique<VConditionalExpr>(std::move(Larger), std::move(A),
                                              std::move(B), HeightType, Loc);
  }
  Expr apply(const VFunction &Fn, std::vector<Expr> Args) const {
    return std::make_unique<VSpecCallExpr>(Fn.Name, Fn.Identity,
                                           std::move(Args), Fn.ReturnType, Loc,
                                           Fn.ReadsHeap);
  }
  std::vector<Expr>
  variables(const std::vector<std::pair<std::string, VType>> &Names) const {
    std::vector<Expr> Out;
    for (const auto &[Name, Ty] : Names)
      Out.push_back(var(Name, Ty));
    return Out;
  }
  std::vector<Expr> cloned(const std::vector<Expr> &Args, const Env &E) const {
    std::vector<Expr> Out;
    for (const Expr &Arg : Args)
      Out.push_back(substParamsInExpr(Arg.get(), E));
    return Out;
  }
  Expr stepAt(const Member &M, Expr Height, std::vector<Expr> Args) const {
    std::vector<Expr> All;
    All.push_back(std::move(Height));
    for (Expr &Arg : Args)
      All.push_back(std::move(Arg));
    return apply(*M.Step, std::move(All));
  }
  std::string fresh(const std::string &Role) {
    return "derivation." + Role + std::to_string(Fresh++);
  }

  /// Phi under \p E with every application Q(a) of a member mapped by \p Map.
  Expr mapped(
      const VExpr *Phi, const Env &E,
      const std::function<Expr(const Member &, std::vector<Expr>)> &Map) const {
    Expr Out = substParamsInExpr(Phi, E);
    std::function<void(Expr &)> visit = [&](Expr &Slot) {
      forEachVExprChildSlot(Slot.get(), visit);
      if (Slot->K != VExpr::SpecCall)
        return;
      auto &Call = static_cast<VSpecCallExpr &>(*Slot);
      auto It = ByIdentity.find(Call.CalleeIdentity);
      if (It == ByIdentity.end())
        return;
      Slot = Map(*It->second, std::move(Call.Args));
    };
    visit(Out);
    return Out;
  }

  /// forall(Binders, Fact): Proof shows Fact for fresh values of the binders
  /// in their ranges, which by generalization then holds for all.
  /// Proof receives the fresh values and returns Fact over them.
  Expr
  generalize(Stmts &Out,
             const std::vector<std::tuple<std::string, VType, const VExpr *,
                                          const VExpr *>> &Binders,
             const std::function<Expr(Stmts &, const Env &)> &Proof) {
    const std::string Choice = fresh("choice");
    Out.push_back(std::make_unique<VAssignStmt>(
        Choice, literal(0, VType::makeBool()), Loc));
    Out.push_back(std::make_unique<VHavocStmt>(Choice, Loc));
    Stmts Block;
    Env Values;
    std::vector<std::string> Names;
    for (const auto &[Binder, Ty, Lo, Hi] : Binders) {
      const std::string Name = fresh("value");
      Names.push_back(Name);
      Block.push_back(std::make_unique<VAssignStmt>(Name, literal(0, Ty), Loc));
      Block.push_back(std::make_unique<VHavocStmt>(Name, Loc));
      if (Lo && Hi)
        Block.push_back(std::make_unique<VAssumeStmt>(
            boolean(VBinOp::And,
                    boolean(VBinOp::Le, substParamsInExpr(Lo, Values),
                            var(Name, Ty)),
                    boolean(VBinOp::Lt, var(Name, Ty),
                            substParamsInExpr(Hi, Values))),
            Loc));
      Values[Binder] = var(Name, Ty);
    }
    Expr Fact = Proof(Block, Values);
    Block.push_back(
        std::make_unique<VContractAssertStmt>(cloneVExpr(Fact.get()), Loc));
    Block.push_back(
        std::make_unique<VAssumeStmt>(literal(0, VType::makeBool()), Loc));
    Out.push_back(std::make_unique<VIfStmt>(var(Choice, VType::makeBool()),
                                            std::move(Block), Stmts(), Loc));
    for (size_t I = Binders.size(); I-- > 0;) {
      const auto &[Binder, Ty, Lo, Hi] = Binders[I];
      replaceVariable(Fact, Names[I], *var(Binder, Ty));
      Fact = std::make_unique<VForallExpr>(
          Binder, Lo ? cloneVExpr(Lo) : nullptr, Hi ? cloneVExpr(Hi) : nullptr,
          std::move(Fact), Loc, Ty);
    }
    Out.push_back(std::make_unique<VAssumeStmt>(cloneVExpr(Fact.get()), Loc));
    return Fact;
  }

  /// Hilbert's choice of Binder in [Lo, Hi) satisfying Body: an uninterpreted
  /// spec of Body's free values whose postcondition is the choice axiom.
  VFunction *choice(const std::string &Name, const std::string &Identity,
                    const std::string &Binder, VType BinderType,
                    const VExpr *Lo, const VExpr *Hi, const VExpr *Body,
                    std::vector<std::pair<std::string, VType>> &Params) {
    auto Probe = std::make_unique<VExistsExpr>(
        Binder, Lo ? cloneVExpr(Lo) : nullptr, Hi ? cloneVExpr(Hi) : nullptr,
        cloneVExpr(Body), Loc, BinderType);
    Params = freeVariables(Probe.get());
    auto Fn = std::make_unique<VFunction>();
    Fn->Name = Name;
    Fn->Identity = Identity;
    Fn->ReturnType = BinderType;
    Fn->IntMode = VIntMode::Math;
    Fn->IsSpec = true;
    Fn->Uninterpreted = true;
    Fn->IsChoice = true;
    Fn->DeclLoc = Members.front().Predicate->DeclLoc;
    Fn->Params = Params;
    Fn->ReadsHeap = readsHeap(Probe.get());
    VResultExpr Chosen(BinderType, Loc);
    Expr Holds = cloneVExpr(Body);
    replaceVariable(Holds, Binder, Chosen);
    if (Lo && Hi)
      Holds = boolean(
          VBinOp::And,
          boolean(VBinOp::And,
                  boolean(VBinOp::Le, cloneVExpr(Lo), cloneVExpr(&Chosen)),
                  boolean(VBinOp::Lt, cloneVExpr(&Chosen), cloneVExpr(Hi))),
          std::move(Holds));
    Fn->Postconditions.push_back(
        boolean(VBinOp::Or, negation(std::move(Probe)), std::move(Holds)));
    VFunction *Raw = Fn.get();
    Generated.push_back(std::move(Fn));
    return Raw;
  }

  /// The choice of the witness of an existential that introduction uses.
  Expr witnessAt(const VQuantifiedExpr &Exists) {
    VFunction *&Fn = Witnesses[&Exists];
    if (!Fn) {
      std::vector<std::pair<std::string, VType>> Params;
      const Member &Owner = Members.front();
      Fn = choice(Owner.Predicate->Name + ".witness",
                  Owner.Predicate->Identity + "::witness" +
                      std::to_string(Witnesses.size()),
                  Exists.Binder, Exists.BinderType, Exists.Lo.get(),
                  Exists.Hi.get(), Exists.Body.get(), Params);
    }
    return apply(*Fn, variables(Fn->Params));
  }

  /// A height at which every application Phi uses holds, under \p E: the
  /// height Q.height(a) chosen for each application Q(a), the largest of its
  /// parts, at the witness chosen for an existential, and the largest over a
  /// bounded universal's range.
  Expr heightOf(const VExpr *Phi, const Env &E) {
    if (!appliesAny(Phi, Group))
      return literal(0, HeightType);
    switch (Phi->K) {
    case VExpr::SpecCall: {
      const auto *Call = static_cast<const VSpecCallExpr *>(Phi);
      return apply(*ByIdentity.at(Call->CalleeIdentity)->Height,
                   cloned(Call->Args, E));
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(Phi);
      return maximum(heightOf(B->Lhs.get(), E), heightOf(B->Rhs.get(), E));
    }
    case VExpr::Cast:
      return heightOf(static_cast<const VCastExpr *>(Phi)->Inner.get(), E);
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(Phi);
      return maximum(heightOf(C->Then.get(), E), heightOf(C->Else.get(), E));
    }
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      Env Inner = copy(E);
      Inner[Q->Binder] = substParamsInExpr(witnessAt(*Q).get(), E);
      return heightOf(Q->Body.get(), Inner);
    }
    case VExpr::Forall: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      VFunction *Bound = boundOver(*Q);
      std::vector<Expr> Args;
      Args.push_back(substParamsInExpr(Q->Lo.get(), E));
      Args.push_back(substParamsInExpr(Q->Hi.get(), E));
      for (size_t I = 2; I < Bound->Params.size(); ++I)
        Args.push_back(substParamsInExpr(
            var(Bound->Params[I].first, Bound->Params[I].second).get(), E));
      return apply(*Bound, std::move(Args));
    }
    default:
      return literal(0, HeightType);
    }
  }

  static Env copy(const Env &E) {
    Env Out;
    for (const auto &[Name, Value] : E)
      Out[Name] = cloneVExpr(Value.get());
    return Out;
  }

  /// The largest height over a bounded universal's range:
  /// bound(lo, hi, v) = lo >= hi ? 0 : max(height[w := lo], bound(lo + 1, hi,
  /// v)), with the postcondition that it bounds the height at every w.
  VFunction *boundOver(const VQuantifiedExpr &Forall) {
    VFunction *&Fn = Bounds[&Forall];
    if (Fn)
      return Fn;
    const Member &Owner = Members.front();
    auto Bound = std::make_unique<VFunction>();
    Fn = Bound.get();
    Bound->Name = Owner.Predicate->Name + ".bound";
    Bound->Identity =
        Owner.Predicate->Identity + "::bound" + std::to_string(Bounds.size());
    Bound->ReturnType = HeightType;
    Bound->IntMode = VIntMode::Math;
    Bound->IsSpec = true;
    Bound->DeclLoc = Owner.Predicate->DeclLoc;
    Expr Height = heightOf(Forall.Body.get(), Env());
    const std::string Lo = "derivation.lo";
    const std::string Hi = "derivation.hi";
    Bound->Params.push_back({Lo, HeightType});
    Bound->Params.push_back({Hi, HeightType});
    for (const auto &Free : freeVariables(&Forall))
      Bound->Params.push_back(Free);
    Bound->ReadsHeap = readsHeap(Height.get());
    Expr AtLo = cloneVExpr(Height.get());
    replaceVariable(AtLo, Forall.Binder, *var(Lo, HeightType));
    std::vector<Expr> Next;
    Next.push_back(
        arithmetic(VBinOp::Add, var(Lo, HeightType), literal(1, HeightType)));
    Next.push_back(var(Hi, HeightType));
    for (size_t I = 2; I < Bound->Params.size(); ++I)
      Next.push_back(var(Bound->Params[I].first, Bound->Params[I].second));
    Bound->Body.push_back(std::make_unique<VReturnStmt>(
        std::make_unique<VConditionalExpr>(
            boolean(VBinOp::Ge, var(Lo, HeightType), var(Hi, HeightType)),
            literal(0, HeightType),
            maximum(std::move(AtLo), apply(*Bound, std::move(Next))),
            HeightType, Loc),
        Loc));
    Bound->Decreases.push_back(
        arithmetic(VBinOp::Sub, var(Hi, HeightType), var(Lo, HeightType)));
    Bound->Postconditions.push_back(std::make_unique<VForallExpr>(
        Forall.Binder, var(Lo, HeightType), var(Hi, HeightType),
        boolean(VBinOp::Le, std::move(Height),
                std::make_unique<VResultExpr>(HeightType, Loc)),
        Loc, Forall.BinderType));
    Generated.push_back(std::move(Bound));
    return Fn;
  }

  /// Steps showing Phi[From] implies Phi[To] under \p E where that needs a
  /// fresh value: each bounded universal is generalized from one, and an
  /// existential above one is fixed at its chosen witness.
  void
  transport(const VExpr *Phi, const Env &E,
            const std::function<Expr(const Member &, std::vector<Expr>)> &From,
            const std::function<Expr(const Member &, std::vector<Expr>)> &To,
            Stmts &Out) {
    if (!appliesAny(Phi, Group) || !containsForall(Phi))
      return;
    switch (Phi->K) {
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(Phi);
      transport(B->Lhs.get(), E, From, To, Out);
      transport(B->Rhs.get(), E, From, To, Out);
      return;
    }
    case VExpr::Cast:
      transport(static_cast<const VCastExpr *>(Phi)->Inner.get(), E, From, To,
                Out);
      return;
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(Phi);
      transport(C->Then.get(), E, From, To, Out);
      transport(C->Else.get(), E, From, To, Out);
      return;
    }
    case VExpr::Exists: {
      // The witness chosen for the existential of Phi[From].
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      Expr Source = mapped(Q, E, From);
      const auto &SourceExists = static_cast<const VQuantifiedExpr &>(*Source);
      std::vector<std::pair<std::string, VType>> Params;
      VFunction *Fn = choice(Members.front().Predicate->Name + ".witness",
                             Members.front().Predicate->Identity +
                                 "::transport" + std::to_string(Fresh++),
                             SourceExists.Binder, SourceExists.BinderType,
                             SourceExists.Lo.get(), SourceExists.Hi.get(),
                             SourceExists.Body.get(), Params);
      Env Inner = copy(E);
      Inner[Q->Binder] = apply(*Fn, variables(Params));
      transport(Q->Body.get(), Inner, From, To, Out);
      return;
    }
    case VExpr::Forall: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      Expr Lo = substParamsInExpr(Q->Lo.get(), E);
      Expr Hi = substParamsInExpr(Q->Hi.get(), E);
      generalize(
          Out, {{Q->Binder, Q->BinderType, Lo.get(), Hi.get()}},
          [&](Stmts &Block, const Env &Values) {
            Env Inner = copy(E);
            for (const auto &[Name, Value] : Values)
              Inner[Name] = cloneVExpr(Value.get());
            Expr Source = mapped(Q->Body.get(), Inner, From);
            Stmts Steps;
            transport(Q->Body.get(), Inner, From, To, Steps);
            Block.push_back(std::make_unique<VIfStmt>(
                cloneVExpr(Source.get()), std::move(Steps), Stmts(), Loc));
            return implies(std::move(Source), mapped(Q->Body.get(), Inner, To));
          });
      return;
    }
    default:
      return;
    }
  }

  static bool containsForall(const VExpr *E) {
    if (!E)
      return false;
    if (E->K == VExpr::Forall)
      return true;
    bool Found = false;
    forEachVExprChild(
        E, [&](const VExpr *Child) { Found = Found || containsForall(Child); });
    return Found;
  }

  /// Introduction steps for Phi under \p E: every application Q(a) Phi uses
  /// is raised to height \p Bound by monotonicity. Returns what they show,
  /// an implication per application.
  Expr introduce(const VExpr *Phi, const Env &E, const VExpr &Bound,
                 Stmts &Out) {
    if (!appliesAny(Phi, Group))
      return literal(1, VType::makeBool());
    switch (Phi->K) {
    case VExpr::SpecCall: {
      const auto *Call = static_cast<const VSpecCallExpr *>(Phi);
      const Member &Q = *ByIdentity.at(Call->CalleeIdentity);
      auto args = [&] { return cloned(Call->Args, E); };
      auto height = [&] { return apply(*Q.Height, args()); };
      Expr Guard = boolean(VBinOp::And, stepAt(Q, height(), args()),
                           boolean(VBinOp::Le, height(), cloneVExpr(&Bound)));
      std::vector<Expr> CallArgs;
      CallArgs.push_back(height());
      CallArgs.push_back(cloneVExpr(&Bound));
      for (Expr &Arg : args())
        CallArgs.push_back(std::move(Arg));
      Stmts Raise;
      Raise.push_back(std::make_unique<VCallStmt>(
          Q.Monotone->Name, Q.Monotone->Identity, std::move(CallArgs), "", Loc,
          /*IsProofCall=*/true));
      Out.push_back(std::make_unique<VIfStmt>(cloneVExpr(Guard.get()),
                                              std::move(Raise), Stmts(), Loc));
      return implies(std::move(Guard), stepAt(Q, cloneVExpr(&Bound), args()));
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(Phi);
      Expr L = introduce(B->Lhs.get(), E, Bound, Out);
      return boolean(VBinOp::And, std::move(L),
                     introduce(B->Rhs.get(), E, Bound, Out));
    }
    case VExpr::Cast:
      return introduce(static_cast<const VCastExpr *>(Phi)->Inner.get(), E,
                       Bound, Out);
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(Phi);
      Expr T = introduce(C->Then.get(), E, Bound, Out);
      return boolean(VBinOp::And, std::move(T),
                     introduce(C->Else.get(), E, Bound, Out));
    }
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      Env Inner = copy(E);
      Inner[Q->Binder] = substParamsInExpr(witnessAt(*Q).get(), E);
      return introduce(Q->Body.get(), Inner, Bound, Out);
    }
    case VExpr::Forall: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(Phi);
      Expr Lo = substParamsInExpr(Q->Lo.get(), E);
      Expr Hi = substParamsInExpr(Q->Hi.get(), E);
      return generalize(Out, {{Q->Binder, Q->BinderType, Lo.get(), Hi.get()}},
                        [&](Stmts &Block, const Env &Values) {
                          Env Inner = copy(E);
                          for (const auto &[Name, Value] : Values)
                            Inner[Name] = cloneVExpr(Value.get());
                          return introduce(Q->Body.get(), Inner, Bound, Block);
                        });
    }
    default:
      return literal(1, VType::makeBool());
    }
  }

  /// The parameters of each member that every application in the group
  /// passes unchanged, as the parameter of the same name and type of the
  /// member it occurs in. Facts about other applications are never needed,
  /// so the proofs quantify over the other parameters only.
  void findFixedParameters() {
    for (const Member &Q : Members)
      Fixed[Q.Predicate->Identity].assign(Q.Predicate->Params.size(), true);
    for (const Member &M : Members) {
      std::set<std::string> Bound;
      std::function<void(const VExpr *)> visit = [&](const VExpr *E) {
        if (!E)
          return;
        if (E->K == VExpr::Forall || E->K == VExpr::Exists) {
          const auto *Q = static_cast<const VQuantifiedExpr *>(E);
          visit(Q->Lo.get());
          visit(Q->Hi.get());
          const bool Inserted = Bound.insert(Q->Binder).second;
          visit(Q->Body.get());
          if (Inserted)
            Bound.erase(Q->Binder);
          return;
        }
        if (E->K == VExpr::SpecCall) {
          const auto *Call = static_cast<const VSpecCallExpr *>(E);
          if (auto It = ByIdentity.find(Call->CalleeIdentity);
              It != ByIdentity.end()) {
            const auto &Params = It->second->Predicate->Params;
            std::vector<bool> &Positions = Fixed[Call->CalleeIdentity];
            for (size_t K = 0; K != Params.size(); ++K) {
              const auto &[Name, Ty] = Params[K];
              const VExpr *Arg = Call->Args[K].get();
              Positions[K] =
                  Positions[K] && Arg->K == VExpr::Var &&
                  static_cast<const VVarExpr *>(Arg)->Name == Name &&
                  !Bound.count(Name) &&
                  llvm::any_of(M.Predicate->Params, [&](const auto &Own) {
                    return Own.first == Name && Own.second.Kind == Ty.Kind &&
                           Own.second.BitWidth == Ty.BitWidth &&
                           Own.second.IsSigned == Ty.IsSigned;
                  });
            }
          }
        }
        forEachVExprChild(E, visit);
      };
      visit(M.Unfolding.get());
    }
  }

  /// One binder for each parameter of Q that is not fixed, named apart from
  /// any parameter.
  std::vector<std::tuple<std::string, VType, const VExpr *, const VExpr *>>
  everyArgument(const Member &Q) const {
    std::vector<std::tuple<std::string, VType, const VExpr *, const VExpr *>>
        Binders;
    const std::vector<bool> &Positions = Fixed.at(Q.Predicate->Identity);
    for (size_t K = 0; K != Q.Predicate->Params.size(); ++K)
      if (!Positions[K])
        Binders.emplace_back("derivation.all." + Q.Predicate->Params[K].first,
                             Q.Predicate->Params[K].second, nullptr, nullptr);
    return Binders;
  }
  std::vector<Expr> argumentsIn(const Member &Q, const Env &Values) const {
    std::vector<Expr> Out;
    const std::vector<bool> &Positions = Fixed.at(Q.Predicate->Identity);
    for (size_t K = 0; K != Q.Predicate->Params.size(); ++K) {
      const auto &[Name, Ty] = Q.Predicate->Params[K];
      Out.push_back(
          Positions[K] ? var(Name, Ty)
                       : cloneVExpr(Values.at("derivation.all." + Name).get()));
    }
    return Out;
  }
  bool applies(const Member &M, const Member &Q) const {
    return appliesAny(M.Unfolding.get(), {Q.Predicate->Identity});
  }

  std::unique_ptr<VFunction> ruleProof(const Member &P, const std::string &Rule,
                                       const std::string &Suffix) {
    auto Fn = std::make_unique<VFunction>();
    Fn->Name = P.Predicate->Name + " (" + Rule + ")";
    Fn->Identity = P.Predicate->Identity + "::" + Suffix;
    Fn->ReturnType = VType::makeVoid();
    Fn->IntMode = VIntMode::Math;
    Fn->IsProof = true;
    Fn->DeclLoc = P.Predicate->DeclLoc;
    Fn->InductiveRuleOf = P.Predicate->Identity;
    Fn->TotalExpressions = true;
    Fn->RevealedSpecs = Group;
    Fn->FactsWithheld = Withheld;
    return Fn;
  }

  void buildStep(Member &M) {
    VFunction &P = *M.Predicate;
    const std::string Height = "derivation.height";
    auto Step = std::make_unique<VFunction>();
    Step->Name = P.Name + ".step";
    Step->Identity = P.Identity + "::step";
    Step->ReturnType = P.ReturnType;
    Step->IntMode = VIntMode::Math;
    Step->IsSpec = true;
    Step->DeclLoc = P.DeclLoc;
    Step->InductiveStepOf = P.Name;
    Step->SpecFuel = P.SpecFuel;
    Step->HiddenSpecs = P.HiddenSpecs;
    Step->RevealedSpecs = P.RevealedSpecs;
    Step->SourceVariables = P.SourceVariables;
    Step->ReadsHeap = P.ReadsHeap;
    for (const VReadRange &Range : P.Reads)
      Step->Reads.push_back({cloneVExpr(Range.Base.get()),
                             cloneVExpr(Range.Count.get()), Range.ElementSize});
    Step->Params.push_back({Height, HeightType});
    Step->Params.insert(Step->Params.end(), P.Params.begin(), P.Params.end());
    Step->Decreases.push_back(var(Height, HeightType));
    // The proofs of P's clauses are about derivations: they run in the
    // checks of its step.
    Step->ClauseProofs = std::move(P.ClauseProofs);
    P.ClauseProofs.clear();
    M.Step = Step.get();
    Generated.push_back(std::move(Step));
  }

  void finishStep(Member &M) {
    VFunction &P = *M.Predicate;
    const std::string Height = M.Step->Params.front().first;
    Expr Lowered = mapped(
        M.Unfolding.get(), Env(), [&](const Member &Q, std::vector<Expr> Args) {
          return stepAt(Q,
                        arithmetic(VBinOp::Sub, var(Height, HeightType),
                                   literal(1, HeightType)),
                        std::move(Args));
        });
    M.Step->Body.push_back(std::make_unique<VReturnStmt>(
        boolean(VBinOp::And,
                boolean(VBinOp::Gt, var(Height, HeightType),
                        literal(0, HeightType)),
                std::move(Lowered)),
        Loc));
    for (size_t I = 0; I != P.Postconditions.size(); ++I)
      addPostcondition(*M.Step, cloneVExpr(P.Postconditions[I].get()),
                       postconditionKind(P, I));
    // P(x) is exists(h, P.step(h, x)).
    P.Body.clear();
    P.Body.push_back(std::make_unique<VReturnStmt>(
        std::make_unique<VExistsExpr>(
            Height, nullptr, nullptr,
            stepAt(M, var(Height, HeightType), variables(P.Params)), Loc,
            HeightType),
        Loc));
    // P.height(x): a height at which P.step holds, when one does.
    const std::string Chosen = "derivation.chosen";
    std::vector<std::pair<std::string, VType>> Params;
    Expr Body = stepAt(M, var(Chosen, HeightType), variables(P.Params));
    M.Height = choice(P.Name + ".height", P.Identity + "::height", Chosen,
                      HeightType, nullptr, nullptr, Body.get(), Params);
    // Keep the predicate's parameter order whatever the body mentions.
    M.Height->Params = P.Params;
  }

  void buildMonotone(Member &M) {
    VFunction &P = *M.Predicate;
    auto Fn = ruleProof(M, "monotonicity", "monotone");
    const std::string H = "derivation.height";
    const std::string J = "derivation.bound";
    Fn->Params.push_back({H, HeightType});
    Fn->Params.push_back({J, HeightType});
    Fn->Params.insert(Fn->Params.end(), P.Params.begin(), P.Params.end());
    Fn->Decreases.push_back(var(H, HeightType));
    M.Monotone = Fn.get();
    Generated.push_back(std::move(Fn));
  }

  void finishMonotone(Member &M) {
    VFunction &P = *M.Predicate;
    VFunction &Fn = *M.Monotone;
    const std::string H = Fn.Params[0].first;
    const std::string J = Fn.Params[1].first;
    auto h = [&] { return var(H, HeightType); };
    auto j = [&] { return var(J, HeightType); };
    auto less = [&](Expr E) {
      return arithmetic(VBinOp::Sub, std::move(E), literal(1, HeightType));
    };
    addPrecondition(Fn,
                    boolean(VBinOp::And, stepAt(M, h(), variables(P.Params)),
                            boolean(VBinOp::Le, h(), j())),
                    ProofObligationKind::Precondition);
    Fn.ExplicitPreconditionCount = 1;
    addPostcondition(Fn, stepAt(M, j(), variables(P.Params)),
                     ProofObligationKind::Postcondition);
    Stmts Induction;
    // The hypothesis: every member's derivations of height h - 1 also have
    // height j - 1.
    for (const Member &Q : Members) {
      if (!applies(M, Q))
        continue;
      generalize(Induction, everyArgument(Q),
                 [&](Stmts &Block, const Env &Values) {
                   auto args = [&] { return argumentsIn(Q, Values); };
                   std::vector<Expr> CallArgs;
                   CallArgs.push_back(less(h()));
                   CallArgs.push_back(less(j()));
                   for (Expr &Arg : args())
                     CallArgs.push_back(std::move(Arg));
                   Stmts Recurse;
                   Recurse.push_back(std::make_unique<VCallStmt>(
                       Q.Monotone->Name, Q.Monotone->Identity,
                       std::move(CallArgs), "", Loc, /*IsProofCall=*/true));
                   Block.push_back(std::make_unique<VIfStmt>(
                       boolean(VBinOp::And, stepAt(Q, less(h()), args()),
                               boolean(VBinOp::Le, less(h()), less(j()))),
                       std::move(Recurse), Stmts(), Loc));
                   return implies(stepAt(Q, less(h()), args()),
                                  stepAt(Q, less(j()), args()));
                 });
    }
    transport(
        M.Unfolding.get(), Env(),
        [&](const Member &Q, std::vector<Expr> Args) {
          return stepAt(Q, less(h()), std::move(Args));
        },
        [&](const Member &Q, std::vector<Expr> Args) {
          return stepAt(Q, less(j()), std::move(Args));
        },
        Induction);
    Fn.Body.push_back(std::make_unique<VIfStmt>(
        boolean(VBinOp::Gt, h(), literal(0, HeightType)), std::move(Induction),
        Stmts(), Loc));
  }

  void buildInversion(Member &M) {
    VFunction &P = *M.Predicate;
    auto Fn = ruleProof(M, "case analysis", "inversion");
    Fn->Params = P.Params;
    addPrecondition(*Fn, apply(P, variables(P.Params)),
                    ProofObligationKind::Precondition);
    Fn->ExplicitPreconditionCount = 1;
    addPostcondition(*Fn, cloneVExpr(M.Unfolding.get()),
                     ProofObligationKind::Postcondition);
    const std::string H = "derivation.height";
    auto h = [&] { return var(H, HeightType); };
    auto below = [&] {
      return arithmetic(VBinOp::Sub, h(), literal(1, HeightType));
    };
    Fn->Body.push_back(std::make_unique<VAssignStmt>(
        H, apply(*M.Height, variables(P.Params)), Loc));
    Fn->Body.push_back(std::make_unique<VContractAssertStmt>(
        stepAt(M, h(), variables(P.Params)), Loc));
    // A derivation of height h - 1 is a derivation.
    for (const Member &Q : Members)
      if (applies(M, Q))
        generalize(Fn->Body, everyArgument(Q), [&](Stmts &, const Env &Values) {
          return implies(stepAt(Q, below(), argumentsIn(Q, Values)),
                         apply(*Q.Predicate, argumentsIn(Q, Values)));
        });
    transport(
        M.Unfolding.get(), Env(),
        [&](const Member &Q, std::vector<Expr> Args) {
          return stepAt(Q, below(), std::move(Args));
        },
        [&](const Member &Q, std::vector<Expr> Args) {
          return apply(*Q.Predicate, std::move(Args));
        },
        Fn->Body);
    Generated.push_back(std::move(Fn));
  }

  void buildIntroduction(Member &M) {
    VFunction &P = *M.Predicate;
    auto Fn = ruleProof(M, "introduction", "introduction");
    Fn->Params = P.Params;
    addPrecondition(*Fn, cloneVExpr(M.Unfolding.get()),
                    ProofObligationKind::Precondition);
    Fn->ExplicitPreconditionCount = 1;
    addPostcondition(*Fn, apply(P, variables(P.Params)),
                     ProofObligationKind::Postcondition);
    const std::string B = "derivation.bound";
    // A chosen height is arbitrary where its predicate is false, so the bound
    // is clamped at zero explicitly.
    Expr Height = heightOf(M.Unfolding.get(), Env());
    Expr Positive =
        boolean(VBinOp::Ge, cloneVExpr(Height.get()), literal(0, HeightType));
    Fn->Body.push_back(std::make_unique<VAssignStmt>(
        B,
        std::make_unique<VConditionalExpr>(
            std::move(Positive), std::move(Height), literal(0, HeightType),
            HeightType, Loc),
        Loc));
    Expr Bound = var(B, HeightType);
    introduce(M.Unfolding.get(), Env(), *Bound, Fn->Body);
    Fn->Body.push_back(std::make_unique<VContractAssertStmt>(
        stepAt(
            M,
            arithmetic(VBinOp::Add, var(B, HeightType), literal(1, HeightType)),
            variables(P.Params)),
        Loc));
    Generated.push_back(std::move(Fn));
  }

public:
  GroupExpander(std::vector<Member> Members,
                std::vector<std::unique_ptr<VFunction>> &Generated)
      : Members(std::move(Members)), Generated(Generated) {
    Loc = this->Members.front().Predicate->InductiveLoc;
    for (Member &M : this->Members) {
      Group.insert(M.Predicate->Identity);
      ByIdentity[M.Predicate->Identity] = &M;
    }
  }

  void expand() {
    findFixedParameters();
    for (Member &M : Members)
      buildStep(M);
    for (Member &M : Members) {
      Withheld.insert(M.Predicate->Identity);
      Withheld.insert(M.Step->Identity);
    }
    for (Member &M : Members)
      finishStep(M);
    for (Member &M : Members)
      buildMonotone(M);
    for (Member &M : Members)
      finishMonotone(M);
    for (Member &M : Members) {
      buildInversion(M);
      buildIntroduction(M);
    }
    for (Member &M : Members) {
      M.Monotone->FactsWithheld = Withheld;
      M.Predicate->Unfolding = std::move(M.Unfolding);
    }
  }
};

} // namespace

void verify::expandInductivePredicates(
    std::vector<std::unique_ptr<VFunction>> &Functions,
    std::vector<std::string> &Errors) {
  std::map<std::string, VFunction *> Inductive;
  for (auto &Fn : Functions)
    if (Fn->InductiveLoc.isValid())
      Inductive[Fn->Identity] = Fn.get();
  if (Inductive.empty())
    return;

  std::set<std::string> Rejected;
  std::map<std::string, Expr> Unfoldings;
  for (auto &[Identity, Fn] : Inductive) {
    auto reject = [&](const std::string &Why) {
      Errors.push_back(Fn->Name + ": " + Why);
      Rejected.insert(Identity);
    };
    if (!Fn->IsSpec || Fn->ReturnType.Kind != VTypeKind::Bool) {
      reject("only a spec function returning bool can be inductive");
      continue;
    }
    if (!Fn->Decreases.empty()) {
      reject("an inductive predicate holds by its derivations, so it takes "
             "no decreases");
      continue;
    }
    if (Fn->Domain) {
      reject("an inductive predicate is defined everywhere, so it takes no "
             "when");
      continue;
    }
    Expr Unfolding = returnedValue({{&Fn->Body, 0}});
    if (!Unfolding) {
      reject("the body of an inductive predicate returns a condition, under "
             "if and else at most");
      continue;
    }
    if (llvm::any_of(Fn->Postconditions, [&](const Expr &Post) {
          return !describesDerivations(Post.get());
        })) {
      reject("a postcondition of an inductive predicate states what holds "
             "where it is true, as !result || Q");
      continue;
    }
    Unfoldings[Identity] = std::move(Unfolding);
  }

  // Members applied by one another form a group, defined together.
  std::map<std::string, std::set<std::string>> Applies;
  std::set<std::string> All;
  for (const auto &[Identity, Unfolding] : Unfoldings)
    All.insert(Identity);
  for (const auto &[Identity, Unfolding] : Unfoldings)
    for (const std::string &Other : All)
      if (appliesAny(Unfolding.get(), {Other}))
        Applies[Identity].insert(Other);
  auto reaches = [&](const std::string &From, const std::string &To) {
    std::set<std::string> Seen{From};
    std::vector<std::string> Work{From};
    while (!Work.empty()) {
      std::string Current = Work.back();
      Work.pop_back();
      for (const std::string &Next : Applies[Current]) {
        if (Next == To)
          return true;
        if (Seen.insert(Next).second)
          Work.push_back(Next);
      }
    }
    return false;
  };
  std::set<std::string> Placed;
  std::vector<std::unique_ptr<VFunction>> Generated;
  for (const auto &[Identity, Unfolding] : Unfoldings) {
    if (Placed.count(Identity))
      continue;
    std::set<std::string> Group{Identity};
    for (const std::string &Other : All)
      if (Other != Identity && reaches(Identity, Other) &&
          reaches(Other, Identity))
        Group.insert(Other);
    Placed.insert(Group.begin(), Group.end());
    bool Malformed = false;
    for (const std::string &Member : Group) {
      VFunction &Fn = *Inductive.at(Member);
      if (std::string Where =
              nonPositiveOccurrence(Unfoldings.at(Member).get(), Group);
          !Where.empty()) {
        Errors.push_back(
            Fn.Name + ": " +
            (Group.size() == 1 ? Fn.Name
                               : std::string("a predicate it is "
                                             "defined with")) +
            " occurs in its body " + Where +
            "; an inductive predicate occurs in its body only positively "
            "(not negated, compared, converted, or in a condition), and "
            "under forall only with bounds");
        Rejected.insert(Member);
        Malformed = true;
      }
    }
    if (Malformed)
      continue;
    std::vector<Member> Members;
    for (const std::string &Member : Group) {
      ::Member M;
      M.Predicate = Inductive.at(Member);
      M.Unfolding = std::move(Unfoldings.at(Member));
      Members.push_back(std::move(M));
    }
    GroupExpander(std::move(Members), Generated).expand();
  }
  for (auto &Fn : Generated)
    Functions.push_back(std::move(Fn));
  // A proof sees an inductive predicate through its unfolding, unless it
  // reveals the definition; reveal_with_fuel asks for deeper unfolding.
  for (const auto &Predicate : Functions)
    if (Predicate->Unfolding)
      for (auto &Fn : Functions) {
        if (Fn->SpecFuel.count(Predicate->Identity))
          Fn->RevealedSpecs.erase(Predicate->Identity);
        if (!Fn->RevealedSpecs.count(Predicate->Identity))
          Fn->HiddenSpecs.insert(Predicate->Identity);
      }
}
