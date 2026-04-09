//===--- StmtContract.h - Contract statement AST nodes ----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines AST nodes for CppVerify contract statements:
//   ContractAssertStmt, GhostBlockStmt
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_STMTCONTRACT_H
#define LLVM_CLANG_AST_STMTCONTRACT_H

#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace clang {

/// ContractAssertStmt - Represents contract_assert(expr);
/// Generates a verification condition, not a runtime check.
class ContractAssertStmt : public Stmt {
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

} // namespace clang

#endif // LLVM_CLANG_AST_STMTCONTRACT_H
