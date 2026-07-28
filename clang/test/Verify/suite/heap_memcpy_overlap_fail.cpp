// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap soundness: without a non-overlap precondition the copy is NOT correct
// (storing to d may clobber an s cell still to be read -- exactly the memcpy vs
// memmove distinction), so it must never verify. Z3 may find a concrete
// counterexample or conservatively time out on the quantified array obligation.
void mcpy(int* d, int* s, int n)
  pre(d != nullptr && s != nullptr && n >= 0 && n <= 1000)
  modifies(*d)
  post(forall(i, 0, n, d[i] == s[i]))
{
  int j = 0;
  while (j < n)
    invariant(0 <= j && j <= n && forall(i, 0, j, d[i] == s[i]))
    decreases(n - j)
  { d[j] = s[j]; j = j + 1; }
}
// VERIFY: {{(error: verification failed|Unresolved): mcpy}}
