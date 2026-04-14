// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Exhaustive test for old() and result expressions:
// AST structure, type preservation, and various contexts.

// ---------------------------------------------------------------------------
// 1. result in simple post (int)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_int 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int result_int(int x)
  pre(x >= 0)
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 2. result type matches unsigned return type
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_uint 'unsigned int (unsigned int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'unsigned int'
unsigned int result_uint(unsigned int x)
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 3. result type matches bool return type
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_bool 'bool (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'bool'
bool result_bool(int x)
  post(result == true)
{
  return x > 0;
}

// ---------------------------------------------------------------------------
// 4. result in equality with expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_eq_expr 'int (int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
int result_eq_expr(int a, int b)
  post(result == a + b)
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 5. result used multiple times in one postcondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_multi_use 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '&&'
// CHECK:   BinaryOperator {{.*}} 'bool' '>='
// CHECK:     ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'bool' '<='
// CHECK:     ResultExpr {{.*}} 'int'
int result_multi_use(int x)
  pre(x >= 0)
  pre(x <= 100)
  post(result >= 0 && result <= 100)
{
  return x;
}

// ---------------------------------------------------------------------------
// 6. result in multiple post clauses
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_multi_post 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK: post: BinaryOperator {{.*}} 'bool' '<='
// CHECK:   ResultExpr {{.*}} 'int'
int result_multi_post(int x)
  pre(x >= 0)
  pre(x <= 50)
  post(result >= 0)
  post(result <= 50)
{
  return x;
}

// ---------------------------------------------------------------------------
// 7. old() of simple variable
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_simple 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
// CHECK:       DeclRefExpr {{.*}} 'int' {{.*}} 'x'
int old_simple(int x)
  pre(x >= 0)
  post(result == old(x) + 1)
{
  return x + 1;
}

// ---------------------------------------------------------------------------
// 8. old() of expression (not just variable)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_expr 'int (int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   OldExpr {{.*}} 'int'
// CHECK:     BinaryOperator {{.*}} 'int' '+'
int old_expr(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  post(result == old(a + b))
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 9. Multiple old() in one postcondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_multi 'int (int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
// CHECK:     OldExpr {{.*}} 'int'
int old_multi(int a, int b)
  post(result == old(a) + old(b))
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 10. old() with nested expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_nested 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   OldExpr {{.*}} 'int'
// CHECK:     BinaryOperator {{.*}} 'int' '*'
int old_nested(int x)
  pre(x >= 0)
  post(result == old(x * x))
{
  return x * x;
}

// ---------------------------------------------------------------------------
// 11. Combined result and old() in equality chain
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_old_chain 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   BinaryOperator {{.*}} 'int' '-'
// CHECK:     ResultExpr {{.*}} 'int'
// CHECK:     OldExpr {{.*}} 'int'
int result_old_chain(int x)
  pre(x > 0)
  post(result - old(x) == 1)
{
  return x + 1;
}

// ---------------------------------------------------------------------------
// 12. old() preserves type of inner expression (unsigned)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_unsigned 'unsigned int (unsigned int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'unsigned int'
// CHECK:   OldExpr {{.*}} 'unsigned int'
unsigned int old_unsigned(unsigned int x)
  post(result == old(x) + 1)
{
  return x + 1;
}
