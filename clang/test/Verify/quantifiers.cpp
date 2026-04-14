// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Exhaustive test for quantifier expressions: forall, exists.
// Tests binder scoping, nesting, various bound expressions, and body forms.

// ---------------------------------------------------------------------------
// 1. Basic forall with literal bounds
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_literal 'bool ()'
// CHECK: ForallExpr {{.*}} 'bool'
// CHECK:   IntegerLiteral {{.*}} 'int' 0
// CHECK:   IntegerLiteral {{.*}} 'int' 10
// CHECK:   BinaryOperator {{.*}} 'bool' '>='
bool forall_literal()
  post(result == forall(i, 0, 10, i >= 0))
{
  return true;
}

// ---------------------------------------------------------------------------
// 2. Basic exists with literal bounds
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} exists_literal 'bool ()'
// CHECK: ExistsExpr {{.*}} 'bool'
// CHECK:   IntegerLiteral {{.*}} 'int' 0
// CHECK:   IntegerLiteral {{.*}} 'int' 10
// CHECK:   BinaryOperator {{.*}} 'bool' '=='
bool exists_literal()
  post(result == exists(j, 0, 10, j == 5))
{
  return true;
}

// ---------------------------------------------------------------------------
// 3. Forall with variable bounds
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_var_bounds 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   IntegerLiteral {{.*}} 'int' 0
// CHECK:   DeclRefExpr {{.*}} 'int' {{.*}} 'n'
int forall_var_bounds(int n)
  pre(forall(i, 0, n, i >= 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 4. Exists with variable bounds
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} exists_var_bounds 'int (int)'
// CHECK: pre: ExistsExpr {{.*}} 'bool'
int exists_var_bounds(int n)
  pre(exists(k, 0, n, k == 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 5. Forall with expression bounds
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_expr_bounds 'int (int, int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:   BinaryOperator {{.*}} 'int' '*'
int forall_expr_bounds(int a, int b)
  pre(forall(i, a + 1, b * 2, i > 0))
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 6. Forall with complex body expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_complex_body 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   BinaryOperator {{.*}} 'bool' '&&'
int forall_complex_body(int n)
  pre(forall(i, 0, n, i >= 0 && i < 1000))
{
  return n;
}

// ---------------------------------------------------------------------------
// 7. Nested forall (forall inside forall body)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} nested_forall 'int (int, int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   ForallExpr {{.*}} 'bool'
int nested_forall(int m, int n)
  pre(forall(i, 0, m, forall(j, 0, n, i + j >= 0)))
{
  return m + n;
}

// ---------------------------------------------------------------------------
// 8. Exists inside forall
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} exists_in_forall 'int (int, int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   ExistsExpr {{.*}} 'bool'
int exists_in_forall(int m, int n)
  pre(forall(i, 0, m, exists(j, 0, n, j >= i)))
{
  return m;
}

// ---------------------------------------------------------------------------
// 9. Forall inside exists
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_in_exists 'int (int, int)'
// CHECK: pre: ExistsExpr {{.*}} 'bool'
// CHECK:   ForallExpr {{.*}} 'bool'
int forall_in_exists(int m, int n)
  pre(exists(i, 0, m, forall(j, 0, n, j + i > 0)))
{
  return m;
}

// ---------------------------------------------------------------------------
// 10. Forall in postcondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_in_post 'int (int)'
// CHECK: post: ForallExpr {{.*}} 'bool'
int forall_in_post(int n)
  pre(n >= 0)
  post(forall(k, 0, n, k < n))
{
  return n;
}

// ---------------------------------------------------------------------------
// 11. Exists in postcondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} exists_in_post 'int (int)'
// CHECK: post: ExistsExpr {{.*}} 'bool'
int exists_in_post(int n)
  pre(n > 0)
  post(exists(k, 0, n, k == 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 12. Forall with different binder names
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} binder_names 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK: pre: ForallExpr {{.*}} 'bool'
int binder_names(int n)
  pre(forall(x, 0, n, x >= 0))
  pre(forall(y, 0, n, y >= 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 13. Forall with binder used in arithmetic body
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} binder_arithmetic 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   BinaryOperator {{.*}} 'bool' '<'
// CHECK:     BinaryOperator {{.*}} 'int' '*'
int binder_arithmetic(int n)
  pre(forall(i, 0, n, i * i < 1000000))
{
  return n;
}

// ---------------------------------------------------------------------------
// 14. Triple-nested quantifiers
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} triple_nested 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   ForallExpr {{.*}} 'bool'
// CHECK:     ForallExpr {{.*}} 'bool'
int triple_nested(int n)
  pre(forall(i, 0, n, forall(j, 0, n, forall(k, 0, n, i + j + k >= 0))))
{
  return n;
}
