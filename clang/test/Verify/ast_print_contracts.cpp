// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-print -ast-dump-filter max_index %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-print -ast-dump-filter sq %s | FileCheck %s --check-prefix=SPEC
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-print -ast-dump-filter max_index %s | grep -v '^Printing' > %t.cpp
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only %t.cpp
//
// Printed declarations carry their contracts, written qualified, as clangd's
// hover shows them; the printed code parses back.

namespace cv = cppverify;

// CHECK:      int max_index(const int *a, int n)
// CHECK-NEXT:     cppverify::pre(n > 0 && cppverify::valid(a, n))
// CHECK-NEXT:     cppverify::post(0 <= cppverify::result && cppverify::result < n)
// CHECK-NEXT:     cppverify::post(cppverify::forall(k, 0, n, a[k] <= a[cppverify::result])) {
// CHECK:          for (int i = 1; i < n; ++i)
// CHECK-NEXT:       cppverify::invariant(1 <= i && i <= n && 0 <= best && best < i)
// CHECK-NEXT:       cppverify::decreases(n - i) {
// CHECK:          cppverify::check(best < n);
// CHECK:          cppverify::ghost {
// CHECK-NEXT:         cppverify::check(cppverify::exists(k, 0, n, a[k] == a[best]));
int max_index(const int *a, int n)
  cv::pre(n > 0 && cppverify::valid(a, n))
  cv::post(0 <= cv::result && cv::result < n)
  cv::post(cv::forall(k, 0, n, a[k] <= a[cv::result]))
{
  int best = 0;
  for (int i = 1; i < n; ++i)
    cv::invariant(1 <= i && i <= n && 0 <= best && best < i)
    cv::decreases(n - i)
  {
    if (a[i] > a[best])
      best = i;
  }
  cv::check(best < n);
  cv::ghost {
    cv::check(cv::exists(k, 0, n, a[k] == a[best]));
  }
  return best;
}

// SPEC:      cppverify::spec int sq(int x)
// SPEC-NEXT:     cppverify::recommends(x >= 0)
// SPEC-NEXT:     cppverify::post(cppverify::result >= 0) {
cv::spec int sq(int x) cv::recommends(x >= 0) cv::post(cv::result >= 0) {
  return x * x;
}
