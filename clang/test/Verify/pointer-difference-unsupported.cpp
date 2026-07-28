// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec long spec_pointer_difference(int *pointer) {
  return pointer - pointer;
}

constexpr long constexpr_pointer_difference(int *pointer) {
  return (pointer + 1) - pointer;
}

// VERIFY-DAG: error: spec_pointer_difference: pointer difference in spec or lifted constexpr functions is unsupported
// VERIFY-DAG: error: constexpr_pointer_difference: pointer difference in spec or lifted constexpr functions is unsupported
