// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s

// CHECK: FunctionDecl {{.*}} count_to
// CHECK: DoStmt
// CHECK: invariant: BinaryOperator {{.*}} 'bool' '&&'
// CHECK: decreases: BinaryOperator {{.*}} 'int' '-'
int count_to(int n)
  pre(n >= 0 && n <= 20)
  post(result == n + 1)
{
  int value = 0;
  do {
    value = value + 1;
  } while (value <= n)
    invariant(value >= 1 && value <= n + 1)
    decreases(n + 1 - value);
  return value;
}
