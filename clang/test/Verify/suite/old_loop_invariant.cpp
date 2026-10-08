// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s

int preserve_entry_value(int value)
  cppverify::pre(value >= 0 && value <= 20)
  cppverify::post(cppverify::result == cppverify::old(value))
{
  int original = value;
  while (value > 0)
    cppverify::invariant(cppverify::old(value) == original)
    cppverify::invariant(cppverify::old(cppverify::forall(i, 0, 1, i == 0)))
    cppverify::invariant(value >= 0)
    cppverify::decreases(value)
  {
    value = value - 1;
  }
  return original;
}

// CHECK: Verified: preserve_entry_value
