// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --lower-only --dump-ir=2 %s -- 2>&1 | FileCheck %s --check-prefix=PASSIVE

int valid_early_return(int x)
  cppverify::post((x > 0 && cppverify::result == 1) || (x <= 0 && cppverify::result == 0))
{
  if (x > 0)
    return 1;
  cppverify::check(x <= 0);
  return 0;
}

int invalid_early_return(int x)
  cppverify::post(cppverify::result == 0)
{
  if (x > 0)
    return 1;
  return 0;
}

int valid_assignment_after_early_return(bool stop, int value)
  cppverify::post(cppverify::result == (stop ? value : 1))
{
  if (stop)
    return value;
  value = 1;
  return value;
}

int valid_loop_after_early_return(bool stop, int value)
  cppverify::post(cppverify::result == value)
{
  int expected = value;
  if (stop)
    return value;
  while (false)
    cppverify::invariant(value == expected)
    cppverify::decreases(0)
  {
    value = 1;
  }
  return value;
}

// VERIFY-DAG: Verified: valid_early_return
// VERIFY-DAG: Verified: valid_assignment_after_early_return
// VERIFY-DAG: Verified: valid_loop_after_early_return
// VERIFY-DAG: error: verification failed: invalid_early_return

// BMC-DAG: Verified: valid_early_return
// BMC-DAG: Verified: valid_assignment_after_early_return
// BMC-DAG: Verified: valid_loop_after_early_return
// BMC-DAG: error: verification failed: invalid_early_return

// PASSIVE-LABEL: passive valid_assignment_after_early_return
// PASSIVE: value_1
// PASSIVE-NEXT: 1
// PASSIVE: value_1
// PASSIVE-NEXT: value_0
// PASSIVE-LABEL: passive valid_loop_after_early_return
// PASSIVE: value_1
// PASSIVE-NEXT: value_0
// PASSIVE: value_2
// PASSIVE-NEXT: 1
// PASSIVE: value_2
// PASSIVE-NEXT: value_1
