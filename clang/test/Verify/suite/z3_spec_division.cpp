// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int quotient(int value, int divisor) {
  return value / divisor;
}

spec int remainder(int value, int divisor) {
  return value % divisor;
}

int valid_spec_division()
  post(quotient(-5, 2) == -2)
  post(quotient(5, -2) == -2)
  post(quotient(-5, -2) == 2)
  post(remainder(-5, 2) == -1)
  post(remainder(5, -2) == 1)
  post(remainder(-5, -2) == -1)
{
  return 0;
}

int valid_spec_zero_extension()
  post(quotient(5, 0) == 0)
  post(remainder(5, 0) == 5)
{
  return 0;
}

int invalid_euclidean_quotient()
  post(quotient(-5, 2) == -3)
{
  return 0;
}

// VERIFY-DAG: Verified: spec axiom: quotient
// VERIFY-DAG: Verified: spec axiom: remainder
// VERIFY-DAG: Verified: valid_spec_division
// VERIFY-DAG: Verified: valid_spec_zero_extension
// VERIFY-DAG: error: verification failed: invalid_euclidean_quotient
