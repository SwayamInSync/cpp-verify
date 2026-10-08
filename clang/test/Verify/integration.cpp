// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -ast-dump %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o %t %s
//
// Integration test: exercises all contract features together in a realistic
// scenario. Verifies correct AST generation and zero-cost ghost codegen.

// ===========================================================================
// Spec functions
// ===========================================================================

// CHECK: FunctionDecl {{.*}} sum_spec 'int (int)' inline external-linkage contract_spec
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
cppverify::spec int sum_spec(int n)
  cppverify::decreases(n)
{
  if (n <= 0) return 0;
  return n + sum_spec(n - 1);
}

// CHECK: FunctionDecl {{.*}} is_sorted_spec 'bool (int)' inline external-linkage contract_spec
cppverify::spec bool is_sorted_spec(int n) {
  return cppverify::forall(i, 0, n, i >= 0);
}

// ===========================================================================
// Proof functions
// ===========================================================================

// CHECK: FunctionDecl {{.*}} lemma_sum_nonneg 'void (int)' inline external-linkage contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
cppverify::proof void lemma_sum_nonneg(int n)
  cppverify::pre(n >= 0)
  cppverify::post(sum_spec(n) >= 0)
  cppverify::decreases(n)
{
  cppverify::reveal_with_fuel(sum_spec, 2);
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
  cppverify::pre(n >= 0)
  cppverify::pre(n <= 1000)
  cppverify::post(cppverify::result >= 0)
  cppverify::post(cppverify::result == sum_spec(n))
{
  // Ghost block at start
  // CHECK: GhostBlockStmt
  // CHECK:   ContractAssertStmt
  cppverify::ghost {
    cppverify::reveal_with_fuel(sum_spec, 2);
    lemma_sum_nonneg(n);
    cppverify::check(sum_spec(n) >= 0);
  }

  int s = 0, i = 0;

  // While loop with contracts
  // CHECK: WhileStmt
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '=='
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '>='
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '<='
  // CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
  while (i < n)
    cppverify::invariant(s >= 0)
    cppverify::invariant(s == sum_spec(i))
    cppverify::invariant(i >= 0)
    cppverify::invariant(i <= n)
    cppverify::invariant(s <= 1001 * i)
    cppverify::decreases(n - i)
  {
    // Ghost block inside loop
    cppverify::ghost {
      cppverify::check(i < n);
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
  cppverify::pre(n >= 0 && n <= 1000)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  // CHECK: ForStmt
  // CHECK: invariant: BinaryOperator {{.*}} 'bool' '&&'
  // CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(s >= 0 && s <= i * i && i >= 0 && i <= n)
    cppverify::decreases(n - i)
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
  cppverify::pre(x >= 0 && x < 2147483647)
  cppverify::post(cppverify::result == cppverify::old(x) + 1)
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
  cppverify::pre(n > 0)
  cppverify::pre(cppverify::forall(i, 0, n, i >= 0))
  cppverify::post(cppverify::exists(j, 0, n, j == 0))
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
  cppverify::pre(m >= 0 && m <= 1000000)
  cppverify::pre(n >= 0 && n <= 1000000)
  cppverify::pre(cppverify::forall(i, 0, m, cppverify::exists(j, 0, n, j >= i)))
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
  cppverify::pre(x >= 0 && x <= 1073741823)
  cppverify::post(cppverify::result == x * 2)
{
  cppverify::ghost {
    cppverify::check(x >= 0);
  }
  int a = x;
  cppverify::ghost {
    cppverify::check(a == x);
  }
  int b = a + x;
  cppverify::ghost {
    cppverify::check(b == x * 2);
  }
  return b;
}
