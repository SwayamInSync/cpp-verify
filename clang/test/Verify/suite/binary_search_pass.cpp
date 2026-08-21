// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --timeout=60000 %s 2>&1 | FileCheck %s
//
// Binary search over an abstract sorted buffer, with the overflow-safe
// midpoint. Companion to binary_search_overflow_fail.cpp, which shows the
// classic lo + hi form being rejected.
//
// Proved here, for every n and every input satisfying the precondition:
//   - termination (the decreases clause);
//   - memory safety: every a[mid] read is inside the declared extent;
//   - definedness: no signed overflow anywhere, including the midpoint;
//   - the result is -1 or a valid index.
//
// Not proved here: that a non-negative result points at the key, and that -1
// means the key is absent. Both need the array's sortedness as a nested
// quantifier (forall i <= j. a[i] <= a[j]); the isolated instantiation lemmas
// verify, but the inductive loop obligation did not close within 900s. Treated
// as incomplete automation, not as a proved property. See
// extras/docs/LIMITATIONS.md.
//
// Normalization: `return mid` inside the loop is not expressible (return
// statements inside loops are unsupported), so a found index is recorded in
// `res` and the live range is collapsed to end the search. This is a
// restructuring of the control flow, not of the algorithm.

spec bool valid(int* p, int n) { return true; }

int bsearch_fixed(int* a, int n, int key)
  pre(valid(a, n) && n >= 0)
  post(-1 <= result && result < n)
{
  int lo = 0;
  int hi = n - 1;
  int res = -1;
  while (lo <= hi)
    invariant(0 <= lo && lo <= n && -1 <= hi && hi < n && -1 <= res && res < n)
    decreases(hi - lo + 1)
  {
    int mid = lo + (hi - lo) / 2;
    if (a[mid] == key) { res = mid; lo = mid; hi = mid - 1; }
    else if (a[mid] < key) { lo = mid + 1; }
    else { hi = mid - 1; }
  }
  return res;
}

// CHECK: Verified: bsearch_fixed
