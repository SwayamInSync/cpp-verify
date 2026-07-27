// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int guarded(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  ghost { contract_assert(x != (-2147483647 - 1)); }
  return x < 0 ? -x : x;
}

int ghost_local_update(int x)
  pre(x < 2147483647)
  post(result == x)
{
  ghost {
    int proof_value = x;
    proof_value = proof_value + 1;
    contract_assert(proof_value == x + 1);
  }
  return x;
}

// VERIFY-DAG: Verified: guarded
// VERIFY-DAG: Verified: ghost_local_update