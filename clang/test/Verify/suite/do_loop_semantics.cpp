// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR

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

int invalid_do_establishment()
  post(result == 2)
{
  int value = 0;
  do {
    value = 2;
  } while (false)
    invariant(value == 1);
  return value;
}

int invalid_do_preservation()
  post(result >= 0)
{
  int value = 0;
  do {
    value = value + 1;
  } while (value <= 1)
    invariant(value == 1)
    decreases(2 - value);
  return value;
}

// VERIFY-DAG: Verified: count_to
// VERIFY-DAG: error: verification failed: invalid_do_establishment
// VERIFY-DAG: error: verification failed: invalid_do_preservation

// VCR-LABEL: fn count_to
// VCR: assign value
// VCR: while
// VCR: assign value
