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
  cppverify::pre(a >= 0)
  cppverify::pre(b >= 0)
  cppverify::post(cppverify::result >= 0)
{
  cppverify::ghost {
    cppverify::check(a + b >= 0);
  }
  return a + b;
}

int clamped_index(int i, int n)
  cppverify::pre(n > 0)
  cppverify::pre(cppverify::forall(j, 0, n, j >= 0))
  cppverify::post(cppverify::result >= 0)
{
  if (i < 0) return 0;
  if (i >= n) return n - 1;
  return i;
}
