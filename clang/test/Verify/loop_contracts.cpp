// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Week-2 milestone test: verify that loop contract AST nodes (invariant,
// decreases) are accepted by the parser and visible in -ast-dump.
//
// CHECK: FunctionDecl {{.*}} sum
// CHECK: WhileStmt

int sum(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
    invariant(i >= 0)
    decreases(n - i)
  {
    s += i;
    i++;
  }
  return s;
}

int factorial(int n)
  pre(n >= 0)
  post(result >= 1)
{
  int r = 1, k = 1;
  while (k <= n)
    invariant(r >= 1)
    invariant(k >= 1)
    decreases(n - k + 1)
  {
    r *= k;
    k++;
  }
  return r;
}
