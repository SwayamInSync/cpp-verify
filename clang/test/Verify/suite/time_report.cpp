// RUN: not %cpp-verify --jobs=1 --timeout=1000 --time-report %s -- 2>&1 | FileCheck %s --check-prefix=TEXT
// RUN: not %cpp-verify --jobs=1 --timeout=1000 --time-report --diagnostics-format=json %s -- 2>/dev/null \
// RUN:   | %python %S/Inputs/time_report_phases.py | FileCheck %s --check-prefix=PHASES
// RUN: not %cpp-verify --backend=bmc --time-report --diagnostics-format=json %S/Inputs/time_report_wrong.cpp -- 2>/dev/null \
// RUN:   | %python %S/Inputs/time_report_phases.py | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --jobs=1 --time-report --function=proved %s -- 2>&1 | FileCheck %s --check-prefix=FILTER --implicit-check-not=after_loop --implicit-check-not=fibo
// RUN: not %cpp-verify --jobs=1 --timeout=1000 --progress %s -- 2>&1 >/dev/null | FileCheck %s --check-prefix=PROGRESS
// RUN: not %cpp-verify --jobs=1 --timeout=1000 %s -- 2>&1 >/dev/null | count 0
// RUN: not %cpp-verify --obligation-in=%t.none --time-report 2>&1 | FileCheck %s --check-prefix=REPLAY
//
// --time-report says where a run and each function spent their time: the
// lowering, the solving (with the inductions and the counterexample checks
// within it), and the confirmations after a failure, the busiest function
// first. --progress counts the functions done on standard error, which is
// the default only on a terminal.

namespace cv = cppverify;

// Solved, with no induction and nothing to confirm.
int proved(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

// Its failure passes through the loop, which unrolling confirms.
int after_loop(int n)
  cv::pre(n >= 0 && n <= 3)
  cv::post(cv::result == n)
{
  int c = 0;
  while (c < n)
    cv::decreases(n - c)
  {
    c = c + 1;
  }
  return c;
}

cv::spec int fibo(int n)
  cv::decreases(n)
  cv::post(cv::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// Proved by induction.
cv::proof void grows(int n)
  cv::pre(n >= 3)
  cv::post(fibo(n) >= n - 1)
{
}

cv::spec int pow2(int n)
  cv::decreases(n)
  cv::post(cv::result >= n + 1)
{
  return n <= 0 ? 1 : 2 * pow2(n - 1);
}

// Inductions are tried, and the counterexample is confirmed by a proof
// after every function is verified.
cv::proof void small_power(int n)
  cv::pre(n >= 1000000000)
  cv::post(pow2(n) < 1000)
{
}

// TEXT:      Time report (seconds): conversion {{[0-9]+\.[0-9][0-9][0-9]}}, verification {{[0-9]+\.[0-9][0-9][0-9]}}, settling {{[0-9]+\.[0-9][0-9][0-9]}}
// TEXT-NEXT: {{^}}     total  lowering   solving  induction  certification  confirmation  function{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  proved{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  after_loop{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  fibo{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  grows{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  pow2{{$}}
// TEXT-DAG:  {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  small_power{{$}}
// TEXT:      Summary: 4 verified, 2 failed

// Which phases took time, and that the times add up.
// PHASES:     run conversion settling verification
// PHASES-DAG: proved solving=1 induction=0 certification=1 confirmation=0 adds up
// PHASES-DAG: after_loop solving=1 induction=0 certification=1 confirmation=1 adds up
// PHASES-DAG: grows solving=1 induction=1 certification=1 confirmation=0 adds up
// PHASES-DAG: small_power solving=1 induction=1 certification=1 confirmation=1 adds up
// PHASES-DAG: fibo solving=1 induction=0 certification=0 confirmation=0 adds up
// PHASES:     {{^}}busiest first{{$}}

// Under BMC too; a failure without a loop has nothing to confirm.
// BMC-DAG: wrong solving=1 induction=0 certification=1 confirmation=0 adds up
// BMC-DAG: count solving=1 induction=0 certification=0 confirmation=0 adds up

// Only the functions reported are listed.
// FILTER:      Verified: proved
// FILTER-NEXT: Time report (seconds):
// FILTER-NEXT: total
// FILTER-NEXT: {{^ +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9] +[0-9]+\.[0-9][0-9][0-9]}}  proved{{$}}
// FILTER-NEXT: Summary: 1 verified

// PROGRESS: [1/6] proved{{.*}}[2/6] after_loop{{.*}}[6/6] small_power

// REPLAY: error: --time-report requires source verification
