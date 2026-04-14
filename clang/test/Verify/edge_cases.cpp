// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Edge cases and stress tests for the CppVerify contract system.

// ---------------------------------------------------------------------------
// 1. Function with many pre clauses (stress)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} many_pres 'int (int)'
// CHECK: pre: BinaryOperator
// CHECK: pre: BinaryOperator
// CHECK: pre: BinaryOperator
// CHECK: pre: BinaryOperator
// CHECK: pre: BinaryOperator
int many_pres(int x)
  pre(x > -1000)
  pre(x < 1000)
  pre(x != 0)
  pre(x != 1)
  pre(x != -1)
{
  return x * x;
}

// ---------------------------------------------------------------------------
// 2. Function with many post clauses (stress)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} many_posts 'int (int)'
// CHECK: post: BinaryOperator
// CHECK: post: BinaryOperator
// CHECK: post: BinaryOperator
// CHECK: post: BinaryOperator
int many_posts(int x)
  pre(x > 0)
  post(result > 0)
  post(result >= x)
  post(result < 2000000)
  post(result != -1)
{
  return x * x;
}

// ---------------------------------------------------------------------------
// 3. While loop with many invariants
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} many_invariants 'int (int)'
// CHECK: WhileStmt
// CHECK: invariant:
// CHECK: invariant:
// CHECK: invariant:
// CHECK: invariant:
// CHECK: invariant:
// CHECK: decreases:
int many_invariants(int n)
  pre(n >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(i >= 0)
    invariant(i <= n)
    invariant(s >= 0)
    invariant(s <= n * n)
    invariant(i + (n - i) == n)
    decreases(n - i)
  {
    s = s + i;
    i = i + 1;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 4. Deeply nested ghost within if within while
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} deep_nesting 'int (int)'
// CHECK: WhileStmt
// CHECK:   IfStmt
// CHECK:     GhostBlockStmt
// CHECK:       ContractAssertStmt
int deep_nesting(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
    decreases(n - i)
  {
    if (i > 0) {
      ghost {
        contract_assert(i > 0);
      }
    }
    s = s + i;
    i = i + 1;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 5. Contract with ternary expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} ternary_contract 'int (int)'
// CHECK: pre: ConditionalOperator
int ternary_contract(int x)
  pre(x > 0 ? true : false)
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 6. Contract with parenthesized expressions
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} parens_contract 'int (int)'
// CHECK: pre: ParenExpr
int parens_contract(int x)
  pre((x >= 0))
  post((result >= 0))
{
  return x;
}

// ---------------------------------------------------------------------------
// 7. Contract with unary NOT
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} not_contract 'int (int)'
// CHECK: pre: UnaryOperator {{.*}} 'bool' prefix '!'
int not_contract(int x)
  pre(!( x < 0))
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 8. Forall with zero-width range
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_zero_range 'int ()'
// CHECK: post: ForallExpr {{.*}} 'bool'
int forall_zero_range()
  post(forall(i, 0, 0, i >= 0))
{
  return 0;
}

// ---------------------------------------------------------------------------
// 9. Exists with single element range
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} exists_single 'int ()'
// CHECK: post: ExistsExpr {{.*}} 'bool'
int exists_single()
  post(exists(i, 0, 1, i == 0))
{
  return 0;
}

// ---------------------------------------------------------------------------
// 10. Quantifier with negative lower bound
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} forall_neg_bound 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   UnaryOperator {{.*}} 'int' prefix '-'
int forall_neg_bound(int n)
  pre(forall(i, -10, n, i + 10 >= 0))
{
  return n;
}

// ---------------------------------------------------------------------------
// 11. Empty function body with contracts
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} empty_body 'void (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>'
void empty_body(int x)
  pre(x > 0)
{
}

// ---------------------------------------------------------------------------
// 12. Multiple return paths with contracts
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} multi_return 'int (int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'int'
int multi_return(int x)
  pre(x >= -100)
  post(result >= 0)
{
  if (x > 10) return x;
  if (x > 0) return x * 2;
  if (x == 0) return 1;
  return -x;
}

// ---------------------------------------------------------------------------
// 13. Spec function with no decreases and no recursion
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} identity_spec 'int (int)' inline contract_spec
spec int identity_spec(int x) {
  return x;
}

// ---------------------------------------------------------------------------
// 14. Quantifier binder shadowing outer variable name
// (body should reference the binder, not the outer)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} binder_shadow 'int (int, int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
int binder_shadow(int n, int i)
  pre(forall(i, 0, n, i >= 0))
{
  return n + i;
}
