// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Exhaustive test for loop contracts: invariant(), decreases() on while/for.

// ---------------------------------------------------------------------------
// 1. While loop with single invariant, single decreases
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_basic 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int while_basic(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
    decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 2. While loop with multiple invariants
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_multi_inv 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '<='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int while_multi_inv(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
    invariant(i >= 0)
    invariant(i <= n)
    decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 3. While loop with only invariant (no decreases)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_inv_only 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
int while_inv_only(int n)
  pre(n >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
  {
    s += i;
    i++;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 4. While loop with only decreases (no invariant)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_dec_only 'int (int)'
// CHECK: WhileStmt
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int while_dec_only(int n)
  pre(n >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 5. While loop with complex invariant expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_complex_inv 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '&&'
int while_complex_inv(int n)
  pre(n >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0 && i <= n)
    decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 6. For loop with invariant and decreases
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} for_basic 'int (int)'
// CHECK: ForStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int for_basic(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(s >= 0)
    decreases(n - i)
  {
    s = s + i;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 7. For loop with multiple invariants
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} for_multi_inv 'int (int)'
// CHECK: ForStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '<='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int for_multi_inv(int n)
  pre(n >= 0)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(s >= 0)
    invariant(i <= n)
    decreases(n - i)
  {
    s = s + i;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 8. Nested while loops with contracts on both
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} nested_while 'int (int, int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
// CHECK:   WhileStmt
// CHECK:   invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   decreases: BinaryOperator {{.*}} 'int' '-'
int nested_while(int m, int n)
  pre(m >= 0)
  pre(n >= 0)
  post(result >= 0)
{
  int total = 0;
  int i = 0;
  while (i < m)
    invariant(total >= 0)
    decreases(m - i)
  {
    int j = 0;
    while (j < n)
      invariant(j >= 0)
      decreases(n - j)
    {
      total = total + 1;
      j = j + 1;
    }
    i = i + 1;
  }
  return total;
}

// ---------------------------------------------------------------------------
// 9. For loop with invariant only (no decreases)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} for_inv_only 'int (int)'
// CHECK: ForStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
int for_inv_only(int n)
  pre(n >= 0)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(s >= 0)
  {
    s = s + i;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 10. While loop - invariant is a simple boolean variable-like expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} while_bool_inv 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '!='
int while_bool_inv(int n)
  pre(n >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i != n)
    decreases(n - i)
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 11. Loop with function pre/post AND loop contracts together
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} full_annotated 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: BinaryOperator {{.*}} 'int' '+'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
int full_annotated(int n)
  pre(n >= 0)
  post(result >= 1)
{
  int r = 1, k = 1;
  while (k <= n)
    invariant(r >= 1)
    invariant(k >= 1)
    decreases(n - k + 1)
  {
    r = r * k;
    k = k + 1;
  }
  return r;
}

// ---------------------------------------------------------------------------
// 12. For loop with decreases only (no invariant)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} for_dec_only 'int (int)'
// CHECK: ForStmt
// CHECK: decreases: DeclRefExpr {{.*}} 'int'
int for_dec_only(int n)
  pre(n >= 0)
{
  int s = 0;
  for (int i = n; i > 0; i = i - 1)
    decreases(i)
  {
    s = s + i;
  }
  return s;
}
