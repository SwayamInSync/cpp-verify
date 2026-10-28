// RUN: not %clang -std=c++17 -fverify-contracts -c -o %t.o %s 2>&1 | FileCheck %s --implicit-check-not=remark:
// RUN: not %clang -std=c++17 -fverify-contracts -Rcppverify -c -o %t.o %s 2>&1 | FileCheck %s --check-prefixes=CHECK,REMARK
// RUN: not %clang -std=c++17 -fverify-contracts -Wno-cppverify -c -o %t.o %s 2>&1 | FileCheck %s --check-prefix=QUIET
// RUN: not %clang -std=c++17 -fverify-contracts -Werror=cppverify -c -o %t.o %s 2>&1 | FileCheck %s --check-prefix=WERROR
// RUN: not %clang -std=c++17 -fverify-contracts -fdiagnostics-format=sarif -Wno-sarif-format-unstable -c -o %t.o %s 2>&1 | FileCheck %s --check-prefix=SARIF
// RUN: %clang -std=c++17 -fverify-contracts -fno-verify -c -o %t.o %s 2>&1 | count 0
//
// A compilation with -fverify-contracts reports each result as a diagnostic
// of the compiler: a failure is an error at the failing check, its
// expression underlined, with its counterexample and path as notes; an
// unresolved result is an error; a warning belongs to -Wcppverify; a proof
// is a remark of -Rcppverify at its function, shown only when asked for.

namespace cv = cppverify;

int inc(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}
// REMARK: compile_diagnostics.cpp:[[@LINE-6]]:5: remark: Verified: inc [backend=z3] [-Rcppverify]

int clamp(int x)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    return x + 1;
  return x;
}
//      CHECK: compile_diagnostics.cpp:[[@LINE-6]]:23: error: verification failed: clamp [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT:    [[@LINE-7]] |   cv::post(cv::result >= 0)
// CHECK-NEXT:       |            ~~~~~~~~~~~^~~~
// CHECK-NEXT: compile_diagnostics.cpp:[[@LINE-9]]:23: note: counterexample: x = {{-[0-9]+}}, result = {{-?[0-9]+}}
// CHECK-NEXT: compile_diagnostics.cpp:[[@LINE-8]]:3: note: takes the true branch
//      CHECK: compile_diagnostics.cpp:[[@LINE-8]]:5: note: returns {{-?[0-9]+}}

int never(int x)
  cv::pre(x > 0 && x < 0)
  cv::post(cv::result == 1)
{
  return 0;
}
// REMARK: compile_diagnostics.cpp:[[@LINE-6]]:5: remark: Verified: never [backend=z3] [vacuous] [-Rcppverify]
//  CHECK: compile_diagnostics.cpp:[[@LINE-7]]:5: warning: never: the precondition is unsatisfiable, so every claim about it holds vacuously [-Wcppverify]
// WERROR: compile_diagnostics.cpp:[[@LINE-8]]:5: error: never: the precondition is unsatisfiable, so every claim about it holds vacuously [-Werror,-Wcppverify]

int unmeasured(int n)
  cv::pre(n >= 0)
  cv::post(cv::result == n)
{
  int i = 0;
  while (i < n)
    cv::invariant(i <= n)
  {
    i = i + 1;
  }
  return i;
}
// CHECK: compile_diagnostics.cpp:[[@LINE-7]]:3: error: Unresolved: unmeasured [backend=z3] [reason=decreases.missing]
// CHECK: 1 warning and 2 errors generated.

// QUIET-NOT: warning:
// QUIET: error: verification failed: clamp
// QUIET-NOT: warning:
// QUIET: error: Unresolved: unmeasured
// QUIET-NOT: warning:
// QUIET: 2 errors generated.

// WERROR: 3 errors generated.

// SARIF: "level": "error",
// SARIF: "ruleId": "err_cppverify_result"
// SARIF: "level": "note",
// SARIF: "text": "counterexample: x = {{-[0-9]+}}, result = {{-?[0-9]+}}"
// SARIF: "ruleId": "note_cppverify_result"
// SARIF: "level": "warning",
// SARIF: "text": "never: the precondition is unsatisfiable, so every claim about it holds vacuously"
// SARIF: "ruleId": "warn_cppverify_result"
// SARIF: "text": "Unresolved: unmeasured [backend=z3] [reason=decreases.missing]
// SARIF: "ruleId": "err_cppverify_result"
