// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// Negative: an array *value* must never degrade into a scalar. Fixed local
// arrays are modelled as byte-addressed automatic objects (see
// local_array_lowering.cpp); every remaining array form is rejected by the
// frontend, so no Array marker can reach the passive/Obligation IR. The
// aggregate backend sorts mirror this: Array (like Struct) has no logic sort.

struct WithArray {
  int values[2];
};

int unsupported_element_array()
  post(result == 0)
{
  float a[4];
  a[0] = 0;
  return 0;
}

int array_value_parameter(WithArray box)
  post(result == 0)
{
  return box.values[0];
}

// VERIFY-DAG: error: unsupported_element_array: unsupported C++ type in verification: float[4]
// VERIFY-DAG: error: array_value_parameter: unsupported C++ type in verification: WithArray
// VERIFY-NOT: Verified: unsupported_element_array
// VERIFY-NOT: Verified: array_value_parameter
// VERIFY-NOT: Lowered: unsupported_element_array
