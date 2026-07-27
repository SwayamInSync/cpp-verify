// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

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

int valid_after_rebinding(int value)
  pre(value != 0)
  post(result == value)
{
  force_zero(value);
  return value;
}

int invalid_after_rebinding(int value)
  pre(value != 0)
  post(result == 1)
{
  force_zero(value);
  return 0;
}

int invalid_after_proof_rebinding(int value)
  pre(value != 0)
  post(result == 1)
{
  ghost {
    proof_force_zero(value);
  }
  return 0;
}

// VERIFY-DAG: Verified: force_zero
// VERIFY-DAG: Verified: proof_force_zero
// VERIFY-DAG: Verified: valid_after_rebinding
// VERIFY-DAG: error: verification failed: invalid_after_rebinding
// VERIFY-DAG: error: verification failed: invalid_after_proof_rebinding
