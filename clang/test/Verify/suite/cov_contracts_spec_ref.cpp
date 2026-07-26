// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int s(int x) { return x + 1; }

int client(int x)
  pre(x >= -100 && x < 100)
  pre(x < 0 || s(x) > 0)
  post(result == s(x))
{
  return s(x);
}

// VERIFY: Verified: client