// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// A by-value parameter in a postcondition denotes the caller's argument, its
// value at entry: reassigning the local copy cannot establish a claim about it.
void force_zero(int value)
  post(value == 0)
{
  value = 0;
}

proof void proof_force_zero(int value)
  post(value == 0)
{
  value = 0;
}

int doubled(int value)
  pre(value >= 0 && value < 1000)
  post(result == 2 * value)
{
  value = value * 2;
  return value;
}

int valid_after_rebinding(int value)
  pre(value >= 0 && value < 1000)
  post(result == 2 * value)
{
  return doubled(value);
}

int invalid_after_rebinding(int value)
  pre(value >= 0 && value < 1000)
  post(result == value)
{
  return doubled(value);
}

int relies_on_force_zero(int value)
  pre(value != 0)
  post(result == 1)
{
  force_zero(value);
  return 0;
}

// VERIFY-DAG: error: verification failed: force_zero {{.*}}(counterexample: value [ssa=value_0] [type=i32] = {{-?[1-9][0-9]*}}
// VERIFY-DAG: error: verification failed: proof_force_zero
// VERIFY-DAG: Verified: doubled
// VERIFY-DAG: Verified: valid_after_rebinding
// VERIFY-DAG: error: verification failed: invalid_after_rebinding
// VERIFY-DAG: Unresolved: relies_on_force_zero {{.*}}[vacuous] [reason=callee.contract] (relies on the contract of force_zero, which is not established)
