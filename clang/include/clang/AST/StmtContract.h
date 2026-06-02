//===--- StmtContract.h - Contract statement AST nodes ----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines AST nodes for CppVerify contract statements:
//   ContractAssertStmt, GhostBlockStmt, RevealWithFuelStmt,
//   HideSpecStmt, RevealSpecStmt
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_STMTCONTRACT_H
#define LLVM_CLANG_AST_STMTCONTRACT_H

#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace clang {

// Forward declaration for serialization friend access.
class ASTStmtReader;

/// ContractAssertStmt - Represents contract_assert(expr);
/// Generates a verification condition, not a runtime check.
class ContractAssertStmt : public Stmt {
  friend class ASTStmtReader;
  SourceLocation ContractAssertLoc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  Stmt *Cond;

public:
  ContractAssertStmt(SourceLocation ContractAssertLoc,
                     SourceLocation LParenLoc, SourceLocation RParenLoc,
                     Expr *Cond)
      : Stmt(ContractAssertStmtClass),
        ContractAssertLoc(ContractAssertLoc), LParenLoc(LParenLoc),
        RParenLoc(RParenLoc), Cond(Cond) {}

  explicit ContractAssertStmt(EmptyShell Empty)
      : Stmt(ContractAssertStmtClass), Cond(nullptr) {}

  Expr *getCond() const { return cast<Expr>(Cond); }

  SourceLocation getContractAssertLoc() const { return ContractAssertLoc; }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getRParenLoc() const { return RParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return ContractAssertLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ContractAssertStmtClass;
  }

  child_range children() { return child_range(&Cond, &Cond + 1); }
  const_child_range children() const {
    return const_child_range(&Cond, &Cond + 1);
  }
};

/// GhostBlockStmt - Represents ghost { ... }
/// Code inside a ghost block exists only for verification purposes.
/// CodeGen skips it entirely.
class GhostBlockStmt : public Stmt {
  friend class ASTStmtReader;
  SourceLocation GhostLoc;
  Stmt *Body;

public:
  GhostBlockStmt(SourceLocation GhostLoc, Stmt *Body)
      : Stmt(GhostBlockStmtClass), GhostLoc(GhostLoc), Body(Body) {}

  explicit GhostBlockStmt(EmptyShell Empty)
      : Stmt(GhostBlockStmtClass), Body(nullptr) {}

  Stmt *getBody() const { return Body; }

  SourceLocation getGhostLoc() const { return GhostLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return GhostLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY {
    return Body->getEndLoc();
  }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == GhostBlockStmtClass;
  }

  child_range children() { return child_range(&Body, &Body + 1); }
  const_child_range children() const {
    return const_child_range(&Body, &Body + 1);
  }
};

/// RevealWithFuelStmt - ghost { reveal_with_fuel(fn, depth); }
/// Locally raises Z3 unfolding depth for a recursive spec function.
class RevealWithFuelStmt : public Stmt {
  friend class ASTStmtReader;
  friend class ASTStmtWriter;
  SourceLocation Loc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  enum { FN, FUEL, NUM_SUBEXPRS };
  Stmt *SubExprs[NUM_SUBEXPRS];

public:
  RevealWithFuelStmt(SourceLocation Loc, SourceLocation LParenLoc,
                     SourceLocation RParenLoc, Expr *Function, Expr *Fuel)
      : Stmt(RevealWithFuelStmtClass), Loc(Loc), LParenLoc(LParenLoc),
        RParenLoc(RParenLoc) {
    SubExprs[FN] = Function;
    SubExprs[FUEL] = Fuel;
  }

  explicit RevealWithFuelStmt(EmptyShell Empty)
      : Stmt(RevealWithFuelStmtClass) {
    SubExprs[FN] = nullptr;
    SubExprs[FUEL] = nullptr;
  }

  Expr *getFunction() const { return cast<Expr>(SubExprs[FN]); }
  Expr *getFuel() const { return cast<Expr>(SubExprs[FUEL]); }

  SourceLocation getLParenLoc() const { return LParenLoc; }

  SourceLocation getBeginLoc() const LLVM_READONLY { return Loc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == RevealWithFuelStmtClass;
  }

  child_range children() {
    return child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
  const_child_range children() const {
    return const_child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
};

/// HideSpecStmt - ghost { hide(fn); } — keep spec body opaque in this VC.
class HideSpecStmt : public Stmt {
  friend class ASTStmtReader;
  SourceLocation Loc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  Stmt *Function;

public:
  HideSpecStmt(SourceLocation Loc, SourceLocation LParenLoc,
               SourceLocation RParenLoc, Expr *Function)
      : Stmt(HideSpecStmtClass), Loc(Loc), LParenLoc(LParenLoc),
        RParenLoc(RParenLoc), Function(Function) {}

  explicit HideSpecStmt(EmptyShell Empty)
      : Stmt(HideSpecStmtClass), Function(nullptr) {}

  Expr *getFunction() const { return cast<Expr>(Function); }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return Loc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == HideSpecStmtClass;
  }

  child_range children() { return child_range(&Function, &Function + 1); }
  const_child_range children() const {
    return const_child_range(&Function, &Function + 1);
  }
};

/// RevealSpecStmt - ghost { reveal(fn); } — inline spec body with default fuel.
class RevealSpecStmt : public Stmt {
  friend class ASTStmtReader;
  SourceLocation Loc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  Stmt *Function;

public:
  RevealSpecStmt(SourceLocation Loc, SourceLocation LParenLoc,
                 SourceLocation RParenLoc, Expr *Function)
      : Stmt(RevealSpecStmtClass), Loc(Loc), LParenLoc(LParenLoc),
        RParenLoc(RParenLoc), Function(Function) {}

  explicit RevealSpecStmt(EmptyShell Empty)
      : Stmt(RevealSpecStmtClass), Function(nullptr) {}

  Expr *getFunction() const { return cast<Expr>(Function); }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return Loc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == RevealSpecStmtClass;
  }

  child_range children() { return child_range(&Function, &Function + 1); }
  const_child_range children() const {
    return const_child_range(&Function, &Function + 1);
  }
};

} // namespace clang

#endif // LLVM_CLANG_AST_STMTCONTRACT_H
