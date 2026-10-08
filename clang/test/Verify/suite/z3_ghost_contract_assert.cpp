// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int guarded(int x)
  cppverify::pre(x != (-2147483647 - 1))
  cppverify::post(cppverify::result >= 0)
{
  cppverify::ghost { cppverify::check(x != (-2147483647 - 1)); }
  return x < 0 ? -x : x;
}

int ghost_local_update(int x)
  cppverify::pre(x < 2147483647)
  cppverify::post(cppverify::result == x)
{
  cppverify::ghost {
    int proof_value = x;
    proof_value = proof_value + 1;
    cppverify::check(proof_value == x + 1);
  }
  return x;
}

// VERIFY-DAG: Verified: guarded
// VERIFY-DAG: Verified: ghost_local_update