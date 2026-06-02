// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int hidden(int x) { return x + 1; }

int client(int x)
  pre(hidden(x) >= 0 && x >= 0 && x < 10)
  post(result >= 0)
{
  ghost { hide(hidden); }
  return x;
}

// VERIFY: Verified: client