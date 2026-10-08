// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Week-2 milestone test: verify that loop contract AST nodes (invariant,
// decreases) are accepted by the parser and visible in -ast-dump.
//
// CHECK: FunctionDecl {{.*}} sum
// CHECK: WhileStmt

int sum(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    cppverify::invariant(s >= 0)
    cppverify::invariant(i >= 0)
    cppverify::decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

int factorial(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result >= 1)
{
  int r = 1, k = 1;
  while (k <= n)
    cppverify::invariant(r >= 1)
    cppverify::invariant(k >= 1)
    cppverify::decreases(n - k + 1)
  {
    r *= k;
    k++;
  }
  return r;
}
