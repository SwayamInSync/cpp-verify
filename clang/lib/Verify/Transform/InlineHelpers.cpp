//===--- InlineHelpers.cpp - Calls of functions without contracts ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "InlineHelpers.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
#include <set>

using namespace clang;
using namespace verify;

namespace {

using StmtList = std::vector<std::unique_ptr<VStmt>>;

/// Calls \p Visit on each expression slot of \p S itself, not of the
/// statements it holds.
void forEachExprSlot(VStmt &S,
                     llvm::function_ref<void(std::unique_ptr<VExpr> &)> Visit) {
  auto checks = [&](std::vector<VMemoryCheck> &Checks) {
    for (VMemoryCheck &Check : Checks)
      Visit(Check.Cond);
  };
  switch (S.K) {
  case VStmt::Assign:
    Visit(static_cast<VAssignStmt &>(S).Value);
    break;
  case VStmt::Store: {
    auto &St = static_cast<VStoreStmt &>(S);
    Visit(St.Ptr);
    Visit(St.Value);
    Visit(St.AccessCondition);
    break;
  }
  case VStmt::Allocate:
    Visit(static_cast<VAllocateStmt &>(S).Initializer);
    break;
  case VStmt::Free:
    Visit(static_cast<VFreeStmt &>(S).Ptr);
    break;
  case VStmt::If:
    Visit(static_cast<VIfStmt &>(S).Cond);
    break;
  case VStmt::While: {
    auto &W = static_cast<VWhileStmt &>(S);
    Visit(W.Cond);
    for (auto &Inv : W.Invariants)
      Visit(Inv);
    for (auto &Dec : W.Decreases)
      Visit(Dec);
    for (VFootprint &F : W.Modifies) {
      Visit(F.Target);
      Visit(F.Count);
    }
    for (auto &Checks : W.InvariantChecks)
      checks(Checks);
    break;
  }
  case VStmt::Call:
    for (auto &Arg : static_cast<VCallStmt &>(S).Args)
      Visit(Arg);
    break;
  case VStmt::Assert:
    Visit(static_cast<VAssertStmt &>(S).Cond);
    break;
  case VStmt::Assume:
    Visit(static_cast<VAssumeStmt &>(S).Cond);
    break;
  case VStmt::Return:
    Visit(static_cast<VReturnStmt &>(S).Value);
    break;
  case VStmt::ContractAssert: {
    auto &A = static_cast<VContractAssertStmt &>(S);
    Visit(A.Cond);
    checks(A.MemoryChecks);
    break;
  }
  case VStmt::EndLifetime:
  case VStmt::Seq:
  case VStmt::Havoc:
  case VStmt::GhostBlock:
  case VStmt::RevealWithFuel:
  case VStmt::HideSpec:
  case VStmt::RevealSpec:
  case VStmt::Break:
  case VStmt::Continue:
    break;
  }
}

/// Calls \p Visit on each list of statements \p S holds.
void forEachBody(VStmt &S, llvm::function_ref<void(StmtList &)> Visit) {
  switch (S.K) {
  case VStmt::If:
    Visit(static_cast<VIfStmt &>(S).Then);
    Visit(static_cast<VIfStmt &>(S).Else);
    break;
  case VStmt::While:
    Visit(static_cast<VWhileStmt &>(S).Body);
    break;
  case VStmt::Seq:
    Visit(static_cast<VSeqStmt &>(S).Stmts);
    break;
  case VStmt::GhostBlock:
    Visit(static_cast<VGhostBlockStmt &>(S).Body);
    break;
  default:
    break;
  }
}

/// Whether \p E reads the entry state or the function's result, which in an
/// inlined body would be the caller's.
bool readsEntryOrResult(const VExpr *E) {
  if (!E)
    return false;
  if (E->K == VExpr::Old || E->K == VExpr::Result)
    return true;
  bool Found = false;
  forEachVExprChild(E, [&](const VExpr *Child) {
    Found = Found || readsEntryOrResult(Child);
  });
  return Found;
}

bool readsEntryOrResult(StmtList &Body) {
  bool Found = false;
  for (auto &S : Body) {
    forEachExprSlot(*S, [&](std::unique_ptr<VExpr> &E) {
      Found = Found || readsEntryOrResult(E.get());
    });
    forEachBody(*S, [&](StmtList &Inner) {
      Found = Found || readsEntryOrResult(Inner);
    });
  }
  return Found;
}

size_t countStatements(StmtList &Body) {
  size_t Count = 0;
  for (auto &S : Body) {
    ++Count;
    forEachBody(*S, [&](StmtList &Inner) { Count += countStatements(Inner); });
  }
  return Count;
}

/// Prefixes every variable an inlined body names, so that it is apart from
/// the caller's and from another call's.
class Renamer {
public:
  explicit Renamer(std::string Prefix) : Prefix(std::move(Prefix)) {}

  std::string name(const std::string &Name) const {
    return Name.empty() ? Name : Prefix + Name;
  }

  void expr(VExpr *E) const {
    if (!E)
      return;
    if (E->K == VExpr::Var) {
      auto *V = static_cast<VVarExpr *>(E);
      V->Name = name(V->Name);
      V->ProvenanceVariable = name(V->ProvenanceVariable);
      V->OriginCompanion = name(V->OriginCompanion);
    } else if (E->K == VExpr::Forall || E->K == VExpr::Exists) {
      auto *Q = static_cast<VQuantifiedExpr *>(E);
      Q->Binder = name(Q->Binder);
    }
    forEachVExprChildSlot(E,
                          [&](std::unique_ptr<VExpr> &Child) { expr(Child.get()); });
  }

  void stmts(StmtList &Body) const {
    for (auto &S : Body)
      stmt(*S);
  }

private:
  void stmt(VStmt &S) const {
    switch (S.K) {
    case VStmt::Assign: {
      auto &A = static_cast<VAssignStmt &>(S);
      A.Target = name(A.Target);
      break;
    }
    case VStmt::Allocate: {
      auto &A = static_cast<VAllocateStmt &>(S);
      A.Target = name(A.Target);
      A.ProvenanceTarget = name(A.ProvenanceTarget);
      break;
    }
    case VStmt::EndLifetime: {
      auto &E = static_cast<VEndLifetimeStmt &>(S);
      E.Target = name(E.Target);
      E.ProvenanceTarget = name(E.ProvenanceTarget);
      break;
    }
    case VStmt::Call: {
      auto &C = static_cast<VCallStmt &>(S);
      C.ResultTarget = name(C.ResultTarget);
      C.ResultProvenanceTarget = name(C.ResultProvenanceTarget);
      break;
    }
    case VStmt::Havoc: {
      auto &H = static_cast<VHavocStmt &>(S);
      H.Target = name(H.Target);
      break;
    }
    default:
      break;
    }
    forEachExprSlot(S, [&](std::unique_ptr<VExpr> &E) { expr(E.get()); });
    forEachBody(S, [&](StmtList &Inner) { stmts(Inner); });
  }

  std::string Prefix;
};

std::unique_ptr<VExpr> boolean(bool Value, SourceLocation Loc) {
  return std::make_unique<VLiteralExpr>(Value ? 1 : 0, VType::makeBool(),
                                        Loc);
}

std::unique_ptr<VExpr> flag(const std::string &Name, SourceLocation Loc) {
  return std::make_unique<VVarExpr>(Name, VType::makeBool(), Loc);
}

/// Lowers the returns of an inlined body: `return e` assigns e to the call's
/// result and sets Done. Outside loops the statements after one that may
/// return run only if Done is clear; inside a loop a return also breaks, a
/// loop that may return is followed by `if (Done) break;`, and every loop
/// that may set Done keeps it clear by a generated invariant (a path that
/// sets it leaves the loop at once).
class ReturnLowering {
public:
  ReturnLowering(std::string Done, std::string Result)
      : Done(std::move(Done)), Result(std::move(Result)) {}

  /// Lowers the returns in \p Body, which \p InLoop loops of the inlined
  /// body enclose; whether a statement of it may set Done.
  bool lower(StmtList &Body, bool InLoop) {
    StmtList Out;
    bool Any = false;
    for (size_t I = 0; I != Body.size(); ++I) {
      std::unique_ptr<VStmt> &S = Body[I];
      const SourceLocation Loc = S->Loc;
      bool MaySet = false;
      switch (S->K) {
      case VStmt::Return: {
        auto &R = static_cast<VReturnStmt &>(*S);
        if (R.Value)
          Out.push_back(
              std::make_unique<VAssignStmt>(Result, std::move(R.Value), Loc));
        Out.push_back(std::make_unique<VAssignStmt>(Done, boolean(true, Loc),
                                                    Loc));
        if (InLoop)
          Out.push_back(std::make_unique<VBreakStmt>(Loc));
        // What follows a return in its list never runs.
        Body = std::move(Out);
        return true;
      }
      case VStmt::If: {
        auto &If = static_cast<VIfStmt &>(*S);
        const bool Then = lower(If.Then, InLoop);
        const bool Else = lower(If.Else, InLoop);
        MaySet = Then || Else;
        break;
      }
      case VStmt::Seq:
        MaySet = lower(static_cast<VSeqStmt &>(*S).Stmts, InLoop);
        break;
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        MaySet = lower(W.Body, /*InLoop=*/true);
        if (MaySet) {
          W.Invariants.push_back(std::make_unique<VUnaryOpExpr>(
              VUnaryOp::Not, flag(Done, Loc), VType::makeBool(), Loc));
          Out.push_back(std::move(S));
          if (InLoop) {
            StmtList Leave;
            Leave.push_back(std::make_unique<VBreakStmt>(Loc));
            Out.push_back(std::make_unique<VIfStmt>(
                flag(Done, Loc), std::move(Leave), StmtList(), Loc));
            Any = true;
            continue;
          }
          return guardRest(Body, I, Out, InLoop);
        }
        break;
      }
      default:
        break;
      }
      Out.push_back(std::move(S));
      // Inside a loop a return has left already.
      if (MaySet && !InLoop)
        return guardRest(Body, I, Out, InLoop);
      Any |= MaySet;
    }
    Body = std::move(Out);
    return Any;
  }

private:
  /// Body[I] may set Done: the statements after it run only if it did not.
  bool guardRest(StmtList &Body, size_t I, StmtList &Out, bool InLoop) {
    StmtList Rest;
    for (size_t J = I + 1; J != Body.size(); ++J)
      Rest.push_back(std::move(Body[J]));
    if (!Rest.empty()) {
      const SourceLocation Loc = Rest.front()->Loc;
      lower(Rest, InLoop);
      Out.push_back(std::make_unique<VIfStmt>(
          std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, flag(Done, Loc),
                                         VType::makeBool(), Loc),
          std::move(Rest), StmtList(), Loc));
    }
    Body = std::move(Out);
    return true;
  }

  std::string Done;
  std::string Result;
};

/// A name for variables that is a valid part of one: the letters, digits,
/// and underscores of \p Name.
std::string identifierPart(llvm::StringRef Name) {
  std::string Out;
  for (char C : Name)
    if (llvm::isAlnum(C) || C == '_')
      Out += C;
  return Out;
}

class Inliner {
public:
  Inliner(const std::map<std::string, const VFunction *> &Helpers,
          const std::map<std::string, std::string> &Unconverted,
          VFunction &Caller)
      : Helpers(Helpers), Unconverted(Unconverted), Caller(Caller) {}

  void run() {
    inlineIn(Caller.Body);
    // Past the budget the caller is not verified: its body is the call that
    // exceeded it, which fails closed.
    if (OverBudget) {
      StmtList Body = unsupported(*OverBudget, OverBudgetWhy);
      Caller.Body = std::move(Body);
    }
  }

private:
  void inlineIn(StmtList &Body) {
    StmtList Out;
    for (auto &S : Body) {
      forEachBody(*S, [&](StmtList &Inner) { inlineIn(Inner); });
      if (S->K == VStmt::Call && static_cast<VCallStmt &>(*S).InlinesHelper) {
        for (auto &Inlined : expand(static_cast<VCallStmt &>(*S)))
          Out.push_back(std::move(Inlined));
        continue;
      }
      Out.push_back(std::move(S));
    }
    Body = std::move(Out);
  }

  /// The call fails closed: an unsupported obligation that says why, and
  /// the end of the path, since nothing is known of what the call does.
  StmtList unsupported(const VCallStmt &C, std::string Why) {
    StmtList Out;
    Out.push_back(std::make_unique<VAssertStmt>(
        boolean(false, C.Loc), C.Loc, ProofObligationKind::Unsupported,
        std::move(Why)));
    Out.push_back(std::make_unique<VAssumeStmt>(boolean(false, C.Loc), C.Loc));
    return Out;
  }

  StmtList expand(VCallStmt &C) {
    auto Found = Helpers.find(C.CalleeIdentity);
    if (Found == Helpers.end()) {
      auto Why = Unconverted.find(C.CalleeIdentity);
      return unsupported(
          C, C.Callee + " has no contract, and its body cannot be inlined" +
                 (Why == Unconverted.end() ? std::string()
                                           : " (" + Why->second + ")") +
                 "; give it a contract");
    }
    const VFunction &H = *Found->second;
    if (llvm::is_contained(Stack, H.Identity)) {
      if (Stack.back() == H.Identity)
        return unsupported(C, H.Name +
                                  " has no contract and calls itself, so its "
                                  "body cannot be inlined; give it a "
                                  "contract");
      std::vector<std::string> Cycle;
      for (auto It = llvm::find(Stack, H.Identity); It != Stack.end(); ++It)
        Cycle.push_back(Helpers.at(*It)->Name);
      Cycle.push_back(H.Name);
      return unsupported(C, "the functions without contracts " +
                                llvm::join(Cycle, " -> ") +
                                " call each other, so their bodies cannot be "
                                "inlined; give one of them a contract");
    }
    // A record parameter is flattened into its fields, and a pointer to one
    // addresses the caller's object; a record result is not.
    if (!H.ReturnFields.empty())
      return unsupported(C, H.Name +
                                " has no contract and returns a record by "
                                "value, which inlining does not support; give "
                                "it a contract");
    if (H.UsesDynamicStorage || !C.ResultProvenanceTarget.empty())
      return unsupported(C, H.Name +
                                " has no contract and allocates, frees, or "
                                "returns dynamic storage, which inlining "
                                "does not support; give it a contract");
    StmtList Body;
    for (const auto &S : H.Body)
      Body.push_back(cloneVStmt(S.get()));
    if (readsEntryOrResult(Body))
      return unsupported(C, H.Name +
                                " has no contract and its loop invariants use "
                                "cppverify::old, whose entry would be the "
                                "caller's if it were inlined; give it a "
                                "contract");
    const size_t Size = countStatements(Body);
    if (Stack.empty())
      Outermost = {C.Loc, H.Name};
    if (OverBudget || Inlined + Size > MaxInlinedStatements) {
      // A contract on the helper the caller calls stops all of it.
      if (!OverBudget) {
        OverBudget = std::make_unique<VCallStmt>(
            Outermost.second, "", std::vector<std::unique_ptr<VExpr>>(), "",
            Outermost.first);
        OverBudgetWhy = "the bodies of the functions without contracts that " +
                        Caller.Name + " runs would be more than " +
                        std::to_string(MaxInlinedStatements) +
                        " statements inlined; give " + Outermost.second +
                        " a contract";
      }
      return {};
    }
    Inlined += Size;

    const std::string Prefix = "__inline" + std::to_string(++Calls) + "_" +
                               identifierPart(H.Name) + "$";
    Renamer Rename(Prefix);
    Rename.stmts(Body);
    StmtList Out;
    for (size_t I = 0; I != H.Params.size() && I != C.Args.size(); ++I) {
      const std::string &Param = H.Params[I].first;
      Out.push_back(std::make_unique<VAssignStmt>(
          Rename.name(Param), std::move(C.Args[I]), C.Loc,
          /*IsReferenceBinding=*/H.ScalarReferenceParams.count(Param) != 0));
    }
    // The body's result is its own until it returns, and has a value of its
    // type before the body, so that a return inside a loop reaches the
    // loop's exit (a variable first assigned in a loop is the loop's own);
    // every return assigns it, and a body that may end without one fails its
    // missing-return check. A result nobody reads is still evaluated.
    const std::string Result = Prefix + "__result";
    const std::string Done = Prefix + "__returned";
    Out.push_back(
        std::make_unique<VAssignStmt>(Done, boolean(false, C.Loc), C.Loc));
    const bool Returns = H.ReturnType.Kind != VTypeKind::Void;
    if (Returns)
      Out.push_back(std::make_unique<VAssignStmt>(
          Result, std::make_unique<VLiteralExpr>(0, H.ReturnType, C.Loc),
          C.Loc));
    ReturnLowering(Done, Result).lower(Body, /*InLoop=*/false);
    for (auto &S : Body)
      Out.push_back(std::move(S));
    if (Returns && !C.ResultTarget.empty())
      Out.push_back(std::make_unique<VAssignStmt>(
          C.ResultTarget,
          std::make_unique<VVarExpr>(Result, H.ReturnType, C.Loc), C.Loc));

    Stack.push_back(H.Identity);
    inlineIn(Out);
    Stack.pop_back();

    // What the body states about itself holds of the caller. Its result is
    // the call's, shown as the caller's variable that receives it.
    for (const auto &[Name, Variable] : H.SourceVariables) {
      if (Name == "__result" || llvm::StringRef(Name).starts_with("result."))
        continue;
      VSourceVariable Copy = Variable;
      Copy.DisplayName = H.Name + "::" + Variable.DisplayName;
      Caller.SourceVariables[Rename.name(Name)] = std::move(Copy);
    }
    for (const std::string &Pointer : H.BoundedPointers)
      Caller.BoundedPointers.insert(Rename.name(Pointer));
    if (!llvm::is_contained(Caller.InlinedExtents, H.Extent))
      Caller.InlinedExtents.push_back(H.Extent);
    // Its static locals are the caller's state wherever its body runs.
    for (const auto &Object : H.PrivateObjects)
      addPrivateObject(Caller, *Object);
    Caller.SpecDependencies.insert(H.SpecDependencies.begin(),
                                   H.SpecDependencies.end());
    // Its reveal_with_fuel unfolds its specs where it runs; more unfolding
    // only adds equations of their definitions. Its hide stays its own, which
    // would withhold a definition from the caller's other claims.
    for (const auto &[Spec, Fuel] : H.SpecFuel)
      Caller.SpecFuel[Spec] = std::max(Caller.SpecFuel[Spec], Fuel);
    Caller.RevealedSpecs.insert(H.RevealedSpecs.begin(),
                                H.RevealedSpecs.end());
    if (!Caller.DivergenceLoc.isValid())
      Caller.DivergenceLoc = H.DivergenceLoc;
    if (!Caller.UnmeasuredLoop.isValid())
      Caller.UnmeasuredLoop = H.UnmeasuredLoop;
    return Out;
  }

  const std::map<std::string, const VFunction *> &Helpers;
  const std::map<std::string, std::string> &Unconverted;
  VFunction &Caller;
  /// The helpers whose bodies are being inlined, outermost first.
  std::vector<std::string> Stack;
  size_t Inlined = 0;
  unsigned Calls = 0;
  /// The call in the caller's own body being inlined, and its callee.
  std::pair<SourceLocation, std::string> Outermost;
  /// Where the inlining exceeds MaxInlinedStatements, and why.
  std::unique_ptr<VCallStmt> OverBudget;
  std::string OverBudgetWhy;
};

void collectInlinedCallees(StmtList &Body, std::set<std::string> &Out) {
  for (auto &S : Body) {
    if (S->K == VStmt::Call && static_cast<VCallStmt &>(*S).InlinesHelper)
      Out.insert(static_cast<VCallStmt &>(*S).CalleeIdentity);
    forEachBody(*S, [&](StmtList &Inner) { collectInlinedCallees(Inner, Out); });
  }
}

} // namespace

void verify::inlineHelperCalls(
    std::vector<std::unique_ptr<VFunction>> &Functions,
    const std::map<std::string, std::string> &Unconverted) {
  std::set<std::string> Callees;
  for (auto &Fn : Functions)
    collectInlinedCallees(Fn->Body, Callees);
  if (Callees.empty())
    return;
  // The bodies as converted: a helper verified on its own is inlined as it
  // is written, not as its own calls were inlined.
  std::vector<std::unique_ptr<VFunction>> Converted;
  std::map<std::string, const VFunction *> Helpers;
  for (auto &Fn : Functions)
    if (Callees.count(Fn->Identity)) {
      Converted.push_back(std::make_unique<VFunction>(cloneVFunction(*Fn)));
      Helpers[Fn->Identity] = Converted.back().get();
    }
  // A function without a contract is verified where verified code calls
  // it, with that code, and on its own only when none does.
  auto InlinedOnly = [&](const std::unique_ptr<VFunction> &Fn) {
    return Fn->IsInlineHelper ||
           (Fn->WithoutContract && Callees.count(Fn->Identity));
  };
  for (auto &Fn : Functions)
    if (!InlinedOnly(Fn))
      Inliner(Helpers, Unconverted, *Fn).run();
  llvm::erase_if(Functions, InlinedOnly);
}
