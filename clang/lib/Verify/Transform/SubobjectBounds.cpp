//===--- SubobjectBounds.cpp - Bounds of subobject pointers ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "SubobjectBounds.h"
#include "Origins.h"
#include "llvm/ADT/StringRef.h"
#include <map>

using namespace clang;
using namespace verify;

const char verify::FormedSubobjectPrefix[] = "__subobject_";

std::string verify::lowerBoundName(const std::string &Pointer) {
  return Pointer + ".__lo";
}

std::string verify::upperBoundName(const std::string &Pointer) {
  return Pointer + ".__hi";
}

bool verify::isBoundCompanion(const std::string &Name) {
  llvm::StringRef Ref(Name);
  return Ref.ends_with(".__lo") || Ref.ends_with(".__hi");
}

bool verify::isFormedSubobjectPointer(const std::string &Name) {
  return llvm::StringRef(Name).starts_with(FormedSubobjectPrefix);
}

namespace {

/// The pointer operand a step or cast keeps the bounds of.
const VExpr *steppedOperand(const VExpr *E) {
  if (E->K == VExpr::Cast) {
    const auto *C = static_cast<const VCastExpr *>(E);
    return C->Inner->Ty.Kind == VTypeKind::Ptr ? C->Inner.get() : nullptr;
  }
  if (E->K == VExpr::BinOp)
    return steppedPointer(*static_cast<const VBinOpExpr *>(E));
  return nullptr;
}

std::unique_ptr<VExpr> anyByte(bool Upper, SourceLocation Loc) {
  // Every object lies below 2^64.
  return std::make_unique<VLiteralExpr>(
      std::string(Upper ? "18446744073709551616" : "0"), VType::makePtr(), Loc);
}

/// Whether Value is Pointer stepped: a step keeps its bounds.
bool isStepOf(const VExpr *Value, const std::string &Pointer) {
  while (Value) {
    if (Value->K == VExpr::Var)
      return static_cast<const VVarExpr *>(Value)->Name == Pointer;
    Value = steppedOperand(Value);
  }
  return false;
}

class Propagation {
public:
  explicit Propagation(VFunction &Fn) : Fn(Fn) {}

  std::vector<std::pair<SourceLocation, std::string>> run() {
    // Bounded variables: the formed pointers and, to a fixpoint, every
    // pointer variable assigned a value rooted at one.
    for (bool Changed = true; Changed;) {
      Changed = false;
      collect(Fn.Body, Changed);
    }
    if (Fn.BoundedPointers.empty())
      return {};
    rewrite(Fn.Body);
    std::vector<std::unique_ptr<VStmt>> Entry;
    for (const std::string &Name : Fn.BoundedPointers)
      if (!isFormedSubobjectPointer(Name))
        appendAnyByte(Name, Fn.DeclLoc, Entry);
    Fn.Body.insert(Fn.Body.begin(), std::make_move_iterator(Entry.begin()),
                   std::make_move_iterator(Entry.end()));
    return std::move(Lost);
  }

private:
  VFunction &Fn;
  std::vector<std::pair<SourceLocation, std::string>> Lost;

  void collect(const std::vector<std::unique_ptr<VStmt>> &Stmts,
               bool &Changed) {
    for (const auto &S : Stmts)
      collect(*S, Changed);
  }

  void collect(const VStmt &S, bool &Changed) {
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      if (A.Value && A.Value->Ty.Kind == VTypeKind::Ptr &&
          hasBoundedRoot(A.Value.get(), Fn.BoundedPointers))
        Changed |= Fn.BoundedPointers.insert(A.Target).second;
      return;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      collect(I.Then, Changed);
      collect(I.Else, Changed);
      return;
    }
    case VStmt::While:
      collect(static_cast<const VWhileStmt &>(S).Body, Changed);
      return;
    case VStmt::Seq:
      collect(static_cast<const VSeqStmt &>(S).Stmts, Changed);
      return;
    case VStmt::GhostBlock:
      collect(static_cast<const VGhostBlockStmt &>(S).Body, Changed);
      return;
    default:
      return;
    }
  }

  void appendAnyByte(const std::string &Name, SourceLocation Loc,
                     std::vector<std::unique_ptr<VStmt>> &Out) {
    Out.push_back(std::make_unique<VAssignStmt>(lowerBoundName(Name),
                                                anyByte(false, Loc), Loc));
    Out.push_back(std::make_unique<VAssignStmt>(upperBoundName(Name),
                                                anyByte(true, Loc), Loc));
  }

  bool bounded(const std::string &Name) const {
    return Fn.BoundedPointers.count(Name);
  }

  /// The bounded pointers Stmts assign, with their element sizes.
  void assignedPointers(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                        std::map<std::string, uint64_t> &Out) const {
    for (const auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign: {
        const auto &A = static_cast<const VAssignStmt &>(*S);
        if (bounded(A.Target) && A.Value &&
            A.Value->Ty.Kind == VTypeKind::Ptr &&
            A.Value->Ty.PointeeSizeBytes != 0)
          Out[A.Target] = A.Value->Ty.PointeeSizeBytes;
        break;
      }
      case VStmt::If:
        assignedPointers(static_cast<const VIfStmt &>(*S).Then, Out);
        assignedPointers(static_cast<const VIfStmt &>(*S).Else, Out);
        break;
      case VStmt::While:
        assignedPointers(static_cast<const VWhileStmt &>(*S).Body, Out);
        break;
      case VStmt::Seq:
        assignedPointers(static_cast<const VSeqStmt &>(*S).Stmts, Out);
        break;
      case VStmt::GhostBlock:
        assignedPointers(static_cast<const VGhostBlockStmt &>(*S).Body, Out);
        break;
      default:
        break;
      }
    }
  }

  /// A bounded pointer a loop moves stays a whole number of elements from
  /// its lower bound (or has none): it starts at an element of its array or
  /// at its field, and steps move by whole elements. A generated invariant,
  /// so it is proved, not assumed.
  void addAlignment(VWhileStmt &W) const {
    std::map<std::string, uint64_t> Moved;
    assignedPointers(W.Body, Moved);
    const SourceLocation Loc = W.Loc;
    for (const auto &[Name, Stride] : Moved) {
      const VType Pointer = VType::makePtr(Stride);
      auto remainder = [&](std::unique_ptr<VExpr> P) {
        return std::make_unique<VBinOpExpr>(
            VBinOp::Rem, std::move(P),
            std::make_unique<VLiteralExpr>(std::to_string(Stride), Pointer,
                                           Loc),
            Pointer, Loc);
      };
      auto isZero = [&](std::string Variable) {
        return std::make_unique<VBinOpExpr>(
            VBinOp::Eq, std::make_unique<VVarExpr>(Variable, Pointer, Loc),
            std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
            VType::makeBool(), Loc);
      };
      auto Aligned = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, remainder(std::make_unique<VVarExpr>(Name, Pointer, Loc)),
          remainder(
              std::make_unique<VVarExpr>(lowerBoundName(Name), Pointer, Loc)),
          VType::makeBool(), Loc);
      W.Invariants.push_back(std::make_unique<VBinOpExpr>(
          VBinOp::Or,
          std::make_unique<VBinOpExpr>(VBinOp::Or, isZero(Name),
                                       isZero(lowerBoundName(Name)),
                                       VType::makeBool(), Loc),
          std::move(Aligned), VType::makeBool(), Loc));
    }
  }

  void rewrite(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    std::vector<std::unique_ptr<VStmt>> Out;
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign: {
        auto &A = static_cast<VAssignStmt &>(*S);
        // The companions take the value's bounds before the assignment,
        // in the state its value is computed in.
        if (bounded(A.Target) && !isFormedSubobjectPointer(A.Target) &&
            !isStepOf(A.Value.get(), A.Target)) {
          for (bool Upper : {false, true}) {
            auto Bound = pointerBound(A.Value.get(), Upper, Fn.BoundedPointers);
            Out.push_back(std::make_unique<VAssignStmt>(
                Upper ? upperBoundName(A.Target) : lowerBoundName(A.Target),
                Bound ? std::move(Bound) : anyByte(Upper, A.Loc), A.Loc));
          }
        }
        break;
      }
      case VStmt::Store: {
        const auto &St = static_cast<const VStoreStmt &>(*S);
        if (St.Value && St.Value->Ty.Kind == VTypeKind::Ptr &&
            hasBoundedRoot(St.Value.get(), Fn.BoundedPointers))
          Lost.emplace_back(St.Loc, "a pointer into a member array or field "
                                    "cannot be stored in memory yet");
        break;
      }
      case VStmt::Allocate: {
        const auto &A = static_cast<const VAllocateStmt &>(*S);
        if (A.Initializer && A.Initializer->Ty.Kind == VTypeKind::Ptr &&
            hasBoundedRoot(A.Initializer.get(), Fn.BoundedPointers))
          Lost.emplace_back(A.Loc, "a pointer into a member array or field "
                                   "cannot be stored in memory yet");
        break;
      }
      case VStmt::Return: {
        const auto &R = static_cast<const VReturnStmt &>(*S);
        if (R.Value && R.Value->Ty.Kind == VTypeKind::Ptr &&
            hasBoundedRoot(R.Value.get(), Fn.BoundedPointers))
          Lost.emplace_back(R.Loc, "returning a pointer into a member array "
                                   "or field is unsupported");
        break;
      }
      case VStmt::If: {
        auto &I = static_cast<VIfStmt &>(*S);
        rewrite(I.Then);
        rewrite(I.Else);
        break;
      }
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        rewrite(W.Body);
        addAlignment(W);
        break;
      }
      case VStmt::Seq:
        rewrite(static_cast<VSeqStmt &>(*S).Stmts);
        break;
      case VStmt::GhostBlock:
        rewrite(static_cast<VGhostBlockStmt &>(*S).Body);
        break;
      default:
        break;
      }
      // A result or a forgotten value may address anything.
      std::string Reset;
      if (S->K == VStmt::Call)
        Reset = static_cast<const VCallStmt &>(*S).ResultTarget;
      else if (S->K == VStmt::Havoc)
        Reset = static_cast<const VHavocStmt &>(*S).Target;
      else if (S->K == VStmt::Allocate)
        Reset = static_cast<const VAllocateStmt &>(*S).Target;
      const SourceLocation Loc = S->Loc;
      Out.push_back(std::move(S));
      if (!Reset.empty() && bounded(Reset))
        appendAnyByte(Reset, Loc, Out);
    }
    Stmts = std::move(Out);
  }
};

} // namespace

bool verify::hasBoundedRoot(const VExpr *Value,
                            const std::set<std::string> &Bounded) {
  if (!Value)
    return false;
  if (Value->K == VExpr::Var)
    return Bounded.count(static_cast<const VVarExpr *>(Value)->Name);
  if (Value->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(Value);
    return hasBoundedRoot(C->Then.get(), Bounded) ||
           hasBoundedRoot(C->Else.get(), Bounded);
  }
  return hasBoundedRoot(steppedOperand(Value), Bounded);
}

std::unique_ptr<VExpr>
verify::pointerBound(const VExpr *Value, bool Upper,
                     const std::set<std::string> &Bounded) {
  if (!hasBoundedRoot(Value, Bounded))
    return nullptr;
  if (Value->K == VExpr::Var) {
    const std::string &Name = static_cast<const VVarExpr *>(Value)->Name;
    return std::make_unique<VVarExpr>(Upper ? upperBoundName(Name)
                                            : lowerBoundName(Name),
                                      VType::makePtr(), Value->Loc);
  }
  if (Value->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(Value);
    auto Then = pointerBound(C->Then.get(), Upper, Bounded);
    auto Else = pointerBound(C->Else.get(), Upper, Bounded);
    return std::make_unique<VConditionalExpr>(
        cloneVExpr(C->Cond.get()),
        Then ? std::move(Then) : anyByte(Upper, C->Loc),
        Else ? std::move(Else) : anyByte(Upper, C->Loc), VType::makePtr(),
        C->Loc);
  }
  return pointerBound(steppedOperand(Value), Upper, Bounded);
}

std::vector<std::pair<SourceLocation, std::string>>
verify::propagateSubobjectBounds(VFunction &Fn) {
  return Propagation(Fn).run();
}
