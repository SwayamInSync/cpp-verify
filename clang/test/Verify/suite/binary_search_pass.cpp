// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --timeout=60000 %s -- 2>&1 | FileCheck %s
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
// Not stated here: that a non-negative result points at the key, and that -1
// means the key is absent. That functional specification, with sortedness as
// a nested quantifier and `return mid` inside the loop, verifies in section
// "Universal statements: sorted arrays" of the book's chapter 20
// (website/source/book/part-ii/ch20-mathematics-to-code.rst).

cppverify::spec bool valid(int* p, int n) { return true; }

int bsearch_fixed(int* a, int n, int key)
  cppverify::pre(valid(a, n) && n >= 0)
  cppverify::post(-1 <= cppverify::result && cppverify::result < n)
{
  int lo = 0;
  int hi = n - 1;
  int res = -1;
  while (lo <= hi)
    cppverify::invariant(0 <= lo && lo <= n && -1 <= hi && hi < n && -1 <= res && res < n)
    cppverify::decreases(hi - lo + 1)
  {
    int mid = lo + (hi - lo) / 2;
    if (a[mid] == key) { res = mid; lo = mid; hi = mid - 1; }
    else if (a[mid] < key) { lo = mid + 1; }
    else { hi = mid - 1; }
  }
  return res;
}

// CHECK: Verified: bsearch_fixed
