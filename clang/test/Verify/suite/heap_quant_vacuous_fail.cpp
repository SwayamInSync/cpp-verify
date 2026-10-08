// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// SOUNDNESS REGRESSION: a symbolic-range forall over the heap must NOT be
// vacuously true. The loop stores 7 everywhere, so post forall p[i] == 0 is
// false and must be rejected (previously a forall over a symbolic range was
// encoded as `true`).
void v(int* p, int n)
  cppverify::pre(p != nullptr && n >= 1 && n <= 10)
  cppverify::modifies(*p)
  cppverify::post(cppverify::forall(i, 0, n, p[i] == 0))
{
  int j = 0;
  while (j < n) cppverify::invariant(0 <= j && j <= n) cppverify::decreases(n - j) { p[j] = 7; j = j + 1; }
}
// VERIFY: verification failed
