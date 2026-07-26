// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s
// RUN: grep -q 'Z3 check: failed' %t.lean

int invalid_lean_export(int x)
  post(result == x + 1)
{
  return x;
}

// CHECK: error: verification failed: invalid_lean_export (lean export written)
