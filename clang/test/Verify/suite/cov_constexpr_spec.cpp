// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int twice(int x) { return 2 * x; }

int use_constexpr(int x)
  pre(x >= 0 && x < 50)
  post(result == twice(x))
{
  return twice(x);
}

// VERIFY: verified: use_constexpr