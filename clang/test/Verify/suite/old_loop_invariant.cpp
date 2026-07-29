// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s

int preserve_entry_value(int value)
  pre(value >= 0 && value <= 20)
  post(result == old(value))
{
  int original = value;
  while (value > 0)
    invariant(old(value) == original)
    invariant(old(forall(i, 0, 1, i == 0)))
    invariant(value >= 0)
    decreases(value)
  {
    value = value - 1;
  }
  return original;
}

// CHECK: Verified: preserve_entry_value
