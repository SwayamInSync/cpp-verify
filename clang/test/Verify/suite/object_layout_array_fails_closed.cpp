// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// Negative: an array *value* must fail closed. The frontend rejects the
// unsupported array type rather than silently degrading the Array marker to a
// scalar, so no such value can reach the passive/Obligation IR. The aggregate
// backend sorts mirror this: Array (like Struct) has no logic sort.

int array_value_fail()
  post(result == 0)
{
  int a[4];
  a[0] = 0;
  return a[0];
}

// VERIFY: error: array_value_fail: unsupported C++ type in verification: int[4]
// VERIFY-NOT: Verified: array_value_fail
// VERIFY-NOT: Lowered: array_value_fail
