// RUN: not %cpp-verify --certify-timeout=200 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=DEFAULT
//
// Checking one counterexample against the true definitions may take
// --certify-timeout milliseconds (by default half the query timeout), so
// that one model whose check is slow leaves the rest of the query's time to
// the others. The reason says which limit was reached.

#include <cppverify.h>

// odd(4) is false, and its derivations never end: deciding it takes a
// search of derivation heights.
spec bool odd(int n) inductive { return n == 1 || odd(n - 2); }

proof void four_is_odd() post(odd(4)) {}
// CHECK: four_is_odd {{.*}}[reason=spec.fuel] {{.*}}the time one counterexample check may take (200 ms, --certify-timeout) was spent
// DEFAULT: four_is_odd {{.*}}whether odd(4) holds: no derivation was found among the heights tried
