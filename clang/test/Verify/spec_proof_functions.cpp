// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Exhaustive test for spec and proof functions: declaration, recognition,
// contract attributes, and interactions with other contract features.

// ---------------------------------------------------------------------------
// 1. Basic spec function (no contracts)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} simple_spec 'int (int)' inline contract_spec
// CHECK: CompoundStmt
spec int simple_spec(int x) {
  return x;
}

// ---------------------------------------------------------------------------
// 2. Spec function with decreases
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} factorial 'int (int)' inline contract_spec
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
spec int factorial(int n)
  decreases(n)
{
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}

// ---------------------------------------------------------------------------
// 3. Spec function returning bool
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} is_positive 'bool (int)' inline contract_spec
spec bool is_positive(int x) {
  return x > 0;
}

// ---------------------------------------------------------------------------
// 4. Spec function with multiple parameters
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} max_spec 'int (int, int)' inline contract_spec
spec int max_spec(int a, int b) {
  if (a >= b) return a;
  return b;
}

// ---------------------------------------------------------------------------
// 5. Spec function calling other spec function
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} double_factorial 'int (int)' inline contract_spec
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
spec int double_factorial(int n)
  decreases(n)
{
  return factorial(n) * 2;
}

// ---------------------------------------------------------------------------
// 6. Spec function with boolean body using forall
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} all_nonneg 'bool (int)' inline contract_spec
// CHECK: ForallExpr {{.*}} 'bool'
spec bool all_nonneg(int n) {
  return forall(i, 0, n, i >= 0);
}

// ---------------------------------------------------------------------------
// 7. Spec function with exists in body
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} has_positive 'bool (int)' inline contract_spec
// CHECK: ExistsExpr {{.*}} 'bool'
spec bool has_positive(int n) {
  return exists(i, 0, n, i > 0);
}

// ---------------------------------------------------------------------------
// 8. Basic proof function
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} trivial_proof 'void (int)' inline contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
proof void trivial_proof(int n)
  pre(n >= 0)
  post(n >= 0)
{
}

// ---------------------------------------------------------------------------
// 9. Proof function with decreases
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} lemma_positive 'void (int)' inline contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
proof void lemma_positive(int n)
  pre(n >= 1)
  post(factorial(n) >= 1)
  decreases(n)
{
  if (n == 1) {
  } else {
    lemma_positive(n - 1);
  }
}

// ---------------------------------------------------------------------------
// 10. Proof function with pre/post using spec function
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} lemma_max 'void (int, int)' inline contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
proof void lemma_max(int a, int b)
  pre(a >= 0)
  post(max_spec(a, b) >= a)
{
}

// ---------------------------------------------------------------------------
// 11. Regular function using spec function in contracts
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} compute_factorial 'int (int)'
// CHECK-NOT: contract_spec
// CHECK-NOT: contract_proof
// CHECK: pre: BinaryOperator {{.*}} 'bool' '>='
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'int'
int compute_factorial(int n)
  pre(n >= 0)
  pre(n <= 12)
  post(result == factorial(n))
{
  int acc = 1;
  int i = 1;
  while (i <= n)
    invariant(acc >= 1)
    invariant(i >= 1)
    decreases(n - i + 1)
  {
    acc = acc * i;
    i = i + 1;
  }
  return acc;
}

// ---------------------------------------------------------------------------
// 12. Regular function calling proof function in ghost block
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} safe_compute 'int (int)'
// CHECK: GhostBlockStmt
int safe_compute(int n)
  pre(n >= 1)
  post(result >= 1)
{
  ghost {
    lemma_positive(n);
  }
  int acc = 1;
  int i = 1;
  while (i <= n)
    invariant(acc >= 1)
    decreases(n - i + 1)
  {
    acc = acc * i;
    i = i + 1;
  }
  return acc;
}

// ---------------------------------------------------------------------------
// 13. Spec function with recursive call and complex decreases
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} fib 'int (int)' inline contract_spec
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
spec int fib(int n)
  decreases(n)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib(n - 1) + fib(n - 2);
}

// ---------------------------------------------------------------------------
// 14. Proof function calling another proof function
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} lemma2 'void (int)' inline contract_proof
// CHECK: decreases: DeclRefExpr {{.*}} 'int' {{.*}} 'n'
proof void lemma2(int n)
  pre(n >= 2)
  post(fib(n) >= 1)
  decreases(n)
{
  if (n == 2) {
  } else {
    lemma2(n - 1);
  }
}

// ---------------------------------------------------------------------------
// 15. Spec function with no parameters
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} zero_spec 'int ()' inline contract_spec
spec int zero_spec() {
  return 0;
}
