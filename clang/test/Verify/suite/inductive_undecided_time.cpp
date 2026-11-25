// RUN: not %python %S/Inputs/within_seconds.py 20 %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
//
// Whether an inductive predicate holds where its derivations never end is
// not decidable by search. The check of a counterexample that needs it
// tries doubling derivation heights under a limit of work of its own, so the
// answer "undecided" comes quickly and the same for every model, and is
// remembered: this claim took 42 s, most of it in checks that tried every
// height in turn until they ran out of steps on the same application.

namespace cv = cppverify;

cv::spec bool even(int n) cv::inductive { return n == 0 || even(n - 2); }

cv::proof void even_nonnegative(int n)
  cv::pre(even(n))
  cv::post(n >= 0)
  cv::post(n % 2 == 0)
{
}

// A derivation the search does reach still decides.
cv::proof void ten_is_even() cv::post(even(10)) {}
cv::proof void seven_is_even() cv::post(even(7)) {}

// CHECK-DAG: Unresolved: even_nonnegative {{.*}}[reason=spec.fuel] {{.*}}whether even({{-?[0-9]+}}) holds: no derivation was found among the heights tried
// CHECK-DAG: Verified: ten_is_even
// CHECK-DAG: seven_is_even
// CHECK: Summary:
