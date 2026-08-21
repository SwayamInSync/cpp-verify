// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub --timeout=30000 %s 2>&1 | FileCheck %s
//
// The classic broken binary-search midpoint. Bentley's *Programming Pearls*
// carried it for two decades and java.util.Arrays.binarySearch carried it for
// nine years (Bloch, "Nearly All Binary Searches and Mergesorts Are Broken",
// 2006). Once lo + hi exceeds INT_MAX the addition signed-overflows, which is
// undefined behavior -- long before the division narrows the value back into
// range.
//
// Nothing in the contract asks for an overflow check. CppVerify's always-on
// expression-definedness obligations reject the midpoint on their own and
// report a concrete lo/hi pair that breaks it.

spec bool valid(int* p, int n) { return true; }

int bsearch_broken(int* a, int n, int key)
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
    int mid = (lo + hi) / 2;
    if (a[mid] == key) { res = mid; lo = mid; hi = mid - 1; }
    else if (a[mid] < key) { lo = mid + 1; }
    else { hi = mid - 1; }
  }
  return res;
}

// CHECK: verification failed: bsearch_broken
// CHECK-SAME: counterexample
