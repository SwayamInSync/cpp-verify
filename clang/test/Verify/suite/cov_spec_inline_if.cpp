// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int bump(int x) { return x + 1; }

int use_bump(int x)
  pre(x >= 0 && x < 10)
  post(result == x + 1)
{
  ghost { reveal(bump); }
  return bump(x);
}

// VERIFY: Verified: use_bump