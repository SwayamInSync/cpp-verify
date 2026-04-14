// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Test contracts with simple structs (MVP supported feature).
// Structs by value, no inheritance, no virtual.

struct Point {
  int x;
  int y;
};

// ---------------------------------------------------------------------------
// 1. Function returning struct with postcondition on member
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} make_origin 'Point ()'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   MemberExpr {{.*}} 'int' {{.*}} .x
// CHECK:     ResultExpr {{.*}} 'Point'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   MemberExpr {{.*}} 'int' {{.*}} .y
// CHECK:     ResultExpr {{.*}} 'Point'
Point make_origin()
  post(result.x == 0)
  post(result.y == 0)
{
  Point p;
  p.x = 0;
  p.y = 0;
  return p;
}

// ---------------------------------------------------------------------------
// 2. Function taking struct with precondition on members
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} point_sum 'int (Point)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   MemberExpr {{.*}} 'int' {{.*}} .x
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   MemberExpr {{.*}} 'int' {{.*}} .y
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int point_sum(Point p)
  pre(p.x >= 0)
  pre(p.y >= 0)
  post(result >= 0)
{
  return p.x + p.y;
}

// ---------------------------------------------------------------------------
// 3. Function with old() on struct member
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} translate 'Point (Point, int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   MemberExpr {{.*}} 'int' {{.*}} .x
// CHECK:     ResultExpr {{.*}} 'Point'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
// CHECK:       MemberExpr {{.*}} 'int' {{.*}} .x
// CHECK:     OldExpr {{.*}} 'int'
// CHECK:       DeclRefExpr {{.*}} 'int' {{.*}} 'dx'
Point translate(Point p, int dx, int dy)
  post(result.x == old(p.x) + old(dx))
  post(result.y == old(p.y) + old(dy))
{
  Point r;
  r.x = p.x + dx;
  r.y = p.y + dy;
  return r;
}

// ---------------------------------------------------------------------------
// 4. Struct with ghost block and contract_assert on members
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} mirror_point_sum 'int (Point)'
// CHECK: GhostBlockStmt
// CHECK:   ContractAssertStmt
int mirror_point_sum(Point p)
  pre(p.x >= 0)
  post(result >= 0)
{
  ghost {
    contract_assert(p.x >= 0);
  }
  return p.x + p.y;
}
