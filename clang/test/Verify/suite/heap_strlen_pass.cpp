// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: strlen-style search returns an in-bounds index of the terminator.
spec bool valid(int *p, int n) { return true; }

int slen(int* s, int n)
  pre(valid(s, n) && n >= 1 && n <= 1000 && s[n - 1] == 0)
  post(result >= 0 && result < n && s[result] == 0)
{
  int i = 0;
  while (s[i] != 0)
    invariant(0 <= i && i < n)
    decreases(n - i)
  { i = i + 1; }
  return i;
}
// VERIFY: Verified: slen
