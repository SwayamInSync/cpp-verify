// RUN: c-index-test core -print-source-symbols -include-locals -- %s -std=c++17 -fverify-contracts -fno-verify | FileCheck %s
//
// The index records the uses in contracts, which find-references and rename
// in editors rely on, and the constructs as references to their declarations
// in <cppverify.h>.

namespace cv = cppverify;

cv::spec int sq(int x) { return x * x; }
// CHECK-DAG: [[@LINE-1]]:5 | enumerator/C | spec | {{.*}} | Ref,RelCont
// CHECK-DAG: [[@LINE-2]]:1 | namespace-alias/C++ | cv | {{.*}} | Ref,RelCont

int f(int n)
  cv::pre(n > 0)
// CHECK-DAG: [[@LINE-1]]:11 | param(local)/C | n | {{.*}} | Ref,Read,RelCont
// CHECK-DAG: [[@LINE-2]]:7 | function/C | pre | {{.*}} | Ref,RelCont
  cv::post(cv::result == sq(n))
// CHECK-DAG: [[@LINE-1]]:26 | function/C | sq | {{.*}} | Ref,Call,RelCall,RelCont
// CHECK-DAG: [[@LINE-2]]:29 | param(local)/C | n | {{.*}} | Ref,Read,RelCont
// CHECK-DAG: [[@LINE-3]]:16 | enumerator/C | result | {{.*}} | Ref,RelCont
{
  for (int i = 0; i < n; ++i)
    cv::invariant(i <= n)
// CHECK-DAG: [[@LINE-1]]:19 | variable(local)/C | i | {{.*}} | Ref,Read,RelCont
// CHECK-DAG: [[@LINE-2]]:24 | param(local)/C | n | {{.*}} | Ref,Read,RelCont
// CHECK-DAG: [[@LINE-3]]:9 | function/C | invariant | {{.*}} | Ref,RelCont
  {
  }
  cv::check(n > 0);
// CHECK-DAG: [[@LINE-1]]:13 | param(local)/C | n | {{.*}} | Ref,Read,RelCont
// CHECK-DAG: [[@LINE-2]]:7 | function/C | check | {{.*}} | Ref,RelCont
  return sq(n);
}
