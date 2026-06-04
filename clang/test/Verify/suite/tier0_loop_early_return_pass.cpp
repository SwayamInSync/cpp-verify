// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: a loop placed after an early return verifies. The loop's invariant
// obligations are guarded by the not-yet-returned path condition, and the
// post-condition reads the right result on both the early-return path and the
// loop path.
int sum_or_zero(int n)
  pre(n >= 0 && n <= 50)
  post(result >= 0)
{
  if (n == 0)
    return 0;
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: Verified: sum_or_zero
