// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Week-2 milestone test: verify that contract AST nodes appear in -ast-dump
// output when -fverify-contracts is active.
//
// CHECK: FunctionDecl {{.*}} safe_add
// CHECK: GhostBlockStmt
// CHECK: ContractAssertStmt
// CHECK: ForallExpr

int safe_add(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
  post(result >= 0)
{
  ghost {
    contract_assert(a + b >= 0);
  }
  return a + b;
}

int clamped_index(int i, int n)
  pre(n > 0)
  pre(forall(j, 0, n, j >= 0))
  post(result >= 0)
{
  if (i < 0) return 0;
  if (i >= n) return n - 1;
  return i;
}
