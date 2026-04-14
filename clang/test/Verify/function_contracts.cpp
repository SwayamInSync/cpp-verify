// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Exhaustive test for function pre/post contracts: single, multiple,
// with various expression forms, result, old(), and nested quantifiers.

// ---------------------------------------------------------------------------
// 1. Single pre, single post
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} single_pre_post 'int (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int single_pre_post(int x)
  pre(x >= 0)
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 2. Multiple pre clauses (conjuncted)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} multi_pre 'int (int, int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: pre: BinaryOperator {{.*}} 'bool' '<='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int multi_pre(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  pre(a <= 100)
  post(result >= 0)
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 3. Multiple post clauses (conjuncted)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} multi_post 'int (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>'
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK: post: BinaryOperator {{.*}} 'bool' '<'
// CHECK:   ResultExpr {{.*}} 'int'
int multi_post(int x)
  pre(x > 0)
  post(result > 0)
  post(result < 1000)
{
  return x;
}

// ---------------------------------------------------------------------------
// 4. Interleaved pre and post clauses
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} interleaved 'int (int, int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK: post: BinaryOperator {{.*}} 'bool' '<='
// CHECK:   ResultExpr {{.*}} 'int'
int interleaved(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  post(result >= 0)
  post(result <= 200)
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 5. old() in postconditions
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} uses_old 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
int uses_old(int x)
  pre(x >= 0)
  post(result == old(x) + 1)
{
  return x + 1;
}

// ---------------------------------------------------------------------------
// 6. Multiple old() references in one postcondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} double_old 'int (int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
// CHECK:     OldExpr {{.*}} 'int'
int double_old(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  post(result == old(a) + old(b))
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 7. Boolean expressions in pre/post (logical ops)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} boolean_ops 'int (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '&&'
// CHECK: post: BinaryOperator {{.*}} 'bool' '||'
int boolean_ops(int x)
  pre(x >= 0 && x <= 100)
  post(result == 0 || result == 1)
{
  return x > 50 ? 1 : 0;
}

// ---------------------------------------------------------------------------
// 8. Forall in precondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} uses_forall_pre 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
int uses_forall_pre(int n)
  pre(forall(i, 0, n, i >= 0))
  post(result >= 0)
{
  return n;
}

// ---------------------------------------------------------------------------
// 9. Exists in precondition
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} uses_exists_pre 'int (int)'
// CHECK: pre: ExistsExpr {{.*}} 'bool'
int uses_exists_pre(int n)
  pre(exists(j, 0, n, j == 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 10. Forall in postcondition (with result)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_post 'int (int)'
// CHECK: post: ForallExpr {{.*}} 'bool'
int forall_post(int n)
  pre(n >= 0)
  post(forall(k, 0, n, k < n))
{
  return n;
}

// ---------------------------------------------------------------------------
// 11. void function with only pre
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} void_with_pre 'void (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>'
void void_with_pre(int x)
  pre(x > 0)
{
}

// ---------------------------------------------------------------------------
// 12. Function with no contracts (baseline—no pre/post labels)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} no_contracts 'int (int)'
// CHECK-NOT: pre:
// CHECK-NOT: post:
// CHECK: CompoundStmt
int no_contracts(int x) {
  return x;
}

// ---------------------------------------------------------------------------
// 13. Pre with comparison to literal boundary values
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} boundary_vals 'int (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '!='
int boundary_vals(int x)
  pre(x != -2147483648)
  post(result >= 0)
{
  if (x < 0) return -x;
  return x;
}

// ---------------------------------------------------------------------------
// 14. Pre with complex nested expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} complex_pre 'int (int, int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '&&'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '||'
int complex_pre(int a, int b)
  pre(a > 0 && b > 0)
  pre(a < 100 || b < 100)
  post(result > 0)
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 15. old() with complex expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} old_complex 'int (int, int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   OldExpr {{.*}} 'int'
// CHECK:     BinaryOperator {{.*}} 'int' '+'
int old_complex(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  post(result == old(a + b))
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 16. Post with conditional expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} post_conditional 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int post_conditional(int x)
  post(result >= 0)
{
  return x > 0 ? x : -x;
}
