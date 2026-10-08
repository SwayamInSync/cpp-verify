// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR

int count_to(int n)
  cppverify::pre(n >= 0 && n <= 20)
  cppverify::post(cppverify::result == n + 1)
{
  int value = 0;
  do {
    value = value + 1;
  } while (value <= n)
    cppverify::invariant(value >= 1 && value <= n + 1)
    cppverify::decreases(n + 1 - value);
  return value;
}

int invalid_do_establishment()
  cppverify::post(cppverify::result == 2)
{
  int value = 0;
  do {
    value = 2;
  } while (false)
    cppverify::invariant(value == 1);
  return value;
}

int invalid_do_preservation()
  cppverify::post(cppverify::result >= 0)
{
  int value = 0;
  do {
    value = value + 1;
  } while (value <= 1)
    cppverify::invariant(value == 1)
    cppverify::decreases(2 - value);
  return value;
}

// VERIFY-DAG: Verified: count_to
// VERIFY-DAG: error: verification failed: invalid_do_establishment
// VERIFY-DAG: error: verification failed: invalid_do_preservation

// VCR-LABEL: fn count_to
// VCR: assign value
// VCR: while
// VCR: assign value
