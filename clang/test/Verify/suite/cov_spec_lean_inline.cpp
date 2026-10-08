// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int triple(int x) { return 3 * x; }

cppverify::spec int pick(int x)
{
  if (x < 0)
    return 0;
  return x;
}

int client(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::post(cppverify::result == triple(x))
  cppverify::recommends(pick(x) >= 0)
{
  cppverify::ghost {
    cppverify::reveal(triple);
    cppverify::hide(pick);
    int tripled = triple(x);
    cppverify::check(tripled == 3 * x);
  }
  int mid = 3 * x;
  if (x < 5)
    return mid;
  return mid;
}

// VERIFY: Exported: lean obligation: client