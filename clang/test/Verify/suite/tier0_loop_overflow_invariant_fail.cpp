// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0 (machine-integer honesty): `s >= 0` is NOT an inductive invariant for
// an unbounded accumulator -- from an arbitrary s == INT_MAX, `s + 1` overflows
// to a negative value, so preservation fails. The sound encoding catches this;
// the old flat-VC encoding masked it.
int overflow_invariant_fail(int n)
  pre(n >= 0 && n <= 1000)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    invariant(i >= 0 && i <= n && s >= 0)
    decreases(n - i)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}
// VERIFY: verification failed
