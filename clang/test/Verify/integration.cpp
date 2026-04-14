// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o %t %s
//
// Integration test: exercises all contract features together in a realistic
// scenario. Verifies correct AST generation and zero-cost ghost codegen.

// ===========================================================================
// Spec functions
// ===========================================================================

// CHECK: FunctionDecl {{.*}} sum_spec 'int (int)' inline contract_spec
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
spec int sum_spec(int n)
  decreases(n)
{
  if (n <= 0) return 0;
  return n + sum_spec(n - 1);
}

// CHECK: FunctionDecl {{.*}} is_sorted_spec 'bool (int)' inline contract_spec
spec bool is_sorted_spec(int n) {
  return forall(i, 0, n, i >= 0);
}

// ===========================================================================
// Proof functions
// ===========================================================================

// CHECK: FunctionDecl {{.*}} lemma_sum_nonneg 'void (int)' inline contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
proof void lemma_sum_nonneg(int n)
  pre(n >= 0)
  post(sum_spec(n) >= 0)
  decreases(n)
{
  if (n == 0) {
  } else {
    lemma_sum_nonneg(n - 1);
  }
}

// ===========================================================================
// Main function with all contract features
// ===========================================================================

// CHECK: FunctionDecl {{.*}} compute_sum 'int (int)'
// CHECK-NOT: contract_spec
// CHECK-NOT: contract_proof
int compute_sum(int n)
  pre(n >= 0)
  pre(n <= 1000)
  post(result >= 0)
  post(result == sum_spec(n))
{
  // Ghost block at start
  // CHECK: GhostBlockStmt
  // CHECK:   ContractAssertStmt
  ghost {
    lemma_sum_nonneg(n);
    contract_assert(sum_spec(n) >= 0);
  }

  int s = 0, i = 0;

  // While loop with contracts
  // CHECK: WhileStmt
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '<='
  // CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
  while (i < n)
    invariant(s >= 0)
    invariant(i >= 0)
    invariant(i <= n)
    decreases(n - i)
  {
    // Ghost block inside loop
    ghost {
      contract_assert(i < n);
    }
    s = s + i + 1;
    i = i + 1;
  }

  return s;
}

// ===========================================================================
// For loop variant
// ===========================================================================

// CHECK: FunctionDecl {{.*}} compute_sum_for 'int (int)'
int compute_sum_for(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0;
  // CHECK: ForStmt
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
  // CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
  for (int i = 0; i < n; i = i + 1)
    invariant(s >= 0)
    decreases(n - i)
  {
    s = s + i + 1;
  }
  return s;
}

// ===========================================================================
// old() and result in postconditions
// ===========================================================================

// CHECK: FunctionDecl {{.*}} increment 'int (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
// CHECK:   BinaryOperator {{.*}} 'int' '+'
// CHECK:     OldExpr {{.*}} 'int'
int increment(int x)
  pre(x >= 0)
  post(result == old(x) + 1)
{
  return x + 1;
}

// ===========================================================================
// Quantifiers in contracts
// ===========================================================================

// CHECK: FunctionDecl {{.*}} quant_test 'int (int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK: post: ExistsExpr {{.*}} 'bool'
int quant_test(int n)
  pre(forall(i, 0, n, i >= 0))
  post(exists(j, 0, n, j == 0))
{
  return n;
}

// ===========================================================================
// Nested quantifiers
// ===========================================================================

// CHECK: FunctionDecl {{.*}} nested_quant 'int (int, int)'
// CHECK: pre: ForallExpr {{.*}} 'bool'
// CHECK:   ExistsExpr {{.*}} 'bool'
int nested_quant(int m, int n)
  pre(forall(i, 0, m, exists(j, 0, n, j >= i)))
{
  return m + n;
}

// ===========================================================================
// Multiple ghost blocks throughout function
// ===========================================================================

// CHECK: FunctionDecl {{.*}} multi_ghost_fn 'int (int)'
// CHECK: GhostBlockStmt
// CHECK: GhostBlockStmt
// CHECK: GhostBlockStmt
int multi_ghost_fn(int x)
  pre(x >= 0)
  post(result == x * 2)
{
  ghost {
    contract_assert(x >= 0);
  }
  int a = x;
  ghost {
    contract_assert(a == x);
  }
  int b = a + x;
  ghost {
    contract_assert(b == x * 2);
  }
  return b;
}
