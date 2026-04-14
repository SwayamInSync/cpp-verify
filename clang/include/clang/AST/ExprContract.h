//===--- ExprContract.h - Contract expression AST nodes ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines AST nodes for CppVerify contract expressions:
//   ForallExpr, ExistsExpr, OldExpr, ResultExpr
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_EXPRCONTRACT_H
#define LLVM_CLANG_AST_EXPRCONTRACT_H

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Type.h"

namespace clang {

// Forward declaration for serialization friend access.
class ASTStmtReader;

/// ForallExpr - Represents a bounded universal quantifier:
///   forall(binder, lo, hi, body)
/// means: for all binder in [lo, hi), body holds.
class ForallExpr : public Expr {
  friend class ASTStmtReader;
  SourceLocation ForallLoc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  VarDecl *BoundVar;
  enum { LO, HI, BODY, NUM_SUBEXPRS };
  Stmt *SubExprs[NUM_SUBEXPRS];

public:
  ForallExpr(SourceLocation ForallLoc, SourceLocation LParenLoc,
             SourceLocation RParenLoc, VarDecl *BoundVar, Expr *Lo, Expr *Hi,
             Expr *Body, QualType BoolTy)
      : Expr(ForallExprClass, BoolTy, VK_PRValue, OK_Ordinary),
        ForallLoc(ForallLoc), LParenLoc(LParenLoc), RParenLoc(RParenLoc),
        BoundVar(BoundVar) {
    SubExprs[LO] = Lo;
    SubExprs[HI] = Hi;
    SubExprs[BODY] = Body;
    setDependence(ExprDependence::None);
  }

  explicit ForallExpr(EmptyShell Empty) : Expr(ForallExprClass, Empty) {}

  VarDecl *getBoundVar() const { return BoundVar; }
  Expr *getLo() const { return cast<Expr>(SubExprs[LO]); }
  Expr *getHi() const { return cast<Expr>(SubExprs[HI]); }
  Expr *getBody() const { return cast<Expr>(SubExprs[BODY]); }

  SourceLocation getForallLoc() const { return ForallLoc; }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getRParenLoc() const { return RParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return ForallLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ForallExprClass;
  }

  child_range children() {
    return child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
  const_child_range children() const {
    return const_child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
};

/// ExistsExpr - Represents a bounded existential quantifier:
///   exists(binder, lo, hi, body)
/// means: there exists binder in [lo, hi) such that body holds.
class ExistsExpr : public Expr {
  friend class ASTStmtReader;
  SourceLocation ExistsLoc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  VarDecl *BoundVar;
  enum { LO, HI, BODY, NUM_SUBEXPRS };
  Stmt *SubExprs[NUM_SUBEXPRS];

public:
  ExistsExpr(SourceLocation ExistsLoc, SourceLocation LParenLoc,
             SourceLocation RParenLoc, VarDecl *BoundVar, Expr *Lo, Expr *Hi,
             Expr *Body, QualType BoolTy)
      : Expr(ExistsExprClass, BoolTy, VK_PRValue, OK_Ordinary),
        ExistsLoc(ExistsLoc), LParenLoc(LParenLoc), RParenLoc(RParenLoc),
        BoundVar(BoundVar) {
    SubExprs[LO] = Lo;
    SubExprs[HI] = Hi;
    SubExprs[BODY] = Body;
    setDependence(ExprDependence::None);
  }

  explicit ExistsExpr(EmptyShell Empty) : Expr(ExistsExprClass, Empty) {}

  VarDecl *getBoundVar() const { return BoundVar; }
  Expr *getLo() const { return cast<Expr>(SubExprs[LO]); }
  Expr *getHi() const { return cast<Expr>(SubExprs[HI]); }
  Expr *getBody() const { return cast<Expr>(SubExprs[BODY]); }

  SourceLocation getExistsLoc() const { return ExistsLoc; }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getRParenLoc() const { return RParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return ExistsLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ExistsExprClass;
  }

  child_range children() {
    return child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
  const_child_range children() const {
    return const_child_range(&SubExprs[0], &SubExprs[NUM_SUBEXPRS]);
  }
};

/// OldExpr - Represents old(expr), referring to the value of expr at
/// function entry. Only valid in postconditions and proof function bodies.
class OldExpr : public Expr {
  friend class ASTStmtReader;
  SourceLocation OldLoc;
  SourceLocation LParenLoc;
  SourceLocation RParenLoc;
  Stmt *Inner;

public:
  OldExpr(SourceLocation OldLoc, SourceLocation LParenLoc,
          SourceLocation RParenLoc, Expr *Inner)
      : Expr(OldExprClass, Inner->getType(), VK_PRValue, OK_Ordinary),
        OldLoc(OldLoc), LParenLoc(LParenLoc), RParenLoc(RParenLoc),
        Inner(Inner) {
    setDependence(ExprDependence::None);
  }

  explicit OldExpr(EmptyShell Empty) : Expr(OldExprClass, Empty) {}

  Expr *getInner() const { return cast<Expr>(Inner); }

  SourceLocation getOldLoc() const { return OldLoc; }
  SourceLocation getLParenLoc() const { return LParenLoc; }
  SourceLocation getRParenLoc() const { return RParenLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return OldLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return RParenLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == OldExprClass;
  }

  child_range children() { return child_range(&Inner, &Inner + 1); }
  const_child_range children() const {
    return const_child_range(&Inner, &Inner + 1);
  }
};

/// ResultExpr - Represents 'result' in postconditions, referring to the
/// return value of the enclosing function.
class ResultExpr : public Expr {
  friend class ASTStmtReader;
  SourceLocation ResultLoc;

public:
  ResultExpr(SourceLocation ResultLoc, QualType ReturnType)
      : Expr(ResultExprClass, ReturnType, VK_PRValue, OK_Ordinary),
        ResultLoc(ResultLoc) {
    setDependence(ExprDependence::None);
  }

  explicit ResultExpr(EmptyShell Empty) : Expr(ResultExprClass, Empty) {}

  SourceLocation getResultLoc() const { return ResultLoc; }
  SourceLocation getBeginLoc() const LLVM_READONLY { return ResultLoc; }
  SourceLocation getEndLoc() const LLVM_READONLY { return ResultLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ResultExprClass;
  }

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }
  const_child_range children() const {
    return const_child_range(const_child_iterator(), const_child_iterator());
  }
};

} // namespace clang

#endif // LLVM_CLANG_AST_EXPRCONTRACT_H
