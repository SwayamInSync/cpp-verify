// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int guarded(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  ghost { contract_assert(x != (-2147483647 - 1)); }
  return x < 0 ? -x : x;
}

// VERIFY: verified: guarded