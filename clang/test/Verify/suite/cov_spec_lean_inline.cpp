// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int triple(int x) { return 3 * x; }

spec int pick(int x)
{
  if (x < 0)
    return 0;
  return x;
}

int client(int x)
  pre(x >= 0 && x <= 10)
  post(result == triple(x))
  recommends(pick(x) >= 0)
{
  ghost { reveal(triple); hide(pick); }
  int mid = triple(x);
  if (x < 5)
    return mid;
  return mid;
}

// VERIFY: Exported: lean obligation: client