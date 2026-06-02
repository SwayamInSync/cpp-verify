// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: grep -q 'theorem cppverify_goal' %t.lean
// RUN: grep -q 'sorry' %t.lean

int abs(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

// VERIFY: lean export: abs