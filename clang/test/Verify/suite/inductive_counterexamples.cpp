// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --confirm-bound=0 %s -- 2>&1 | FileCheck %s --check-prefix=NONE
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --backend=bmc --confirm-bound=3 %s -- 2>&1 | FileCheck %s --check-prefix=OPTION
//
// A counterexample that passes through a loop starts the loop's next steps
// from any state its invariants allow, which no execution need reach. Its
// failure says so, and unrolling each loop looks for an execution that
// fails: one within the bound, none within it, or a proof that none fails at
// all. A loop without a measure is named beside a failure too.

namespace cv = cppverify;

int count_up(int n)
  cv::pre(n >= 0 && n <= 5)
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

int sum_wrong(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(cv::result == n)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && s == 2 * i)
    cv::decreases(n - i)
  {
    s = s + 2;
  }
  return s;
}

int far_wrong(int n)
  cv::pre(n >= 0 && n <= 1000)
  cv::post(cv::result < 100)
{
  int c = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    c = c + 1;
  }
  return c;
}

int no_loop(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x)
{
  return x + 1;
}

int unmeasured(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(cv::result == n + 1)
{
  int c = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
  {
    c = c + 1;
  }
  return c;
}

// Unrolling checks the copies of the failed check, here the division in
// each iteration, and finds the execution that divides by zero.
int divides(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(cv::result >= -5)
{
  int c = 0;
  int q = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    q = 10 / (3 - c);
    c = c + 1;
  }
  return q - 5;
}

// Unrolling keeps no invariant, so it cannot confirm a failed one.
int grows(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(true)
{
  int c = 0;
  while (c < n)
    cv::invariant(c <= 2)
    cv::decreases(n - c)
  {
    c = c + 1;
  }
  return c;
}

// The copies of the failed check are those at its place: the check after
// the loop fails sooner, with n == 2, but it is another check.
int two_checks(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(true)
{
  int c = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    cv::check(c != 4);
    c = c + 1;
  }
  cv::check(c != 2);
  return c;
}

// And those of its kind: the failed check is the overflow of INT_MIN / -1,
// and the division by zero at the same place fails one iteration sooner, in
// every execution that would reach it. A copy is solved in the executions
// that pass the failing checks before it, so none fails the overflow.
int two_kinds(int a, int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(true)
{
  int c = 0;
  int q = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    q = a / (1 - c);
    c = c + 1;
  }
  return q;
}

// The first division fails at c == k, and the second one iteration sooner
// when m == k - 1: the execution that fails the first within 2 iterations
// divides by zero in the second first. The one shown passes it.
int past_failure(int k, int m, int n)
  cv::pre(n >= 0 && n <= 5)
  cv::pre((k == 1 && m == 0) || (k == 3 && m == 100))
  cv::post(true)
{
  int c = 0;
  int q = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    q = 100 / (k - c);
    q = q + 100 / (m - c);
    c = c + 1;
  }
  return q;
}

// A failure on a path that skips the loop has no loop to note.
int skipped(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(cv::result >= 0)
{
  int c = 0;
  if (n > 3) {
    while (c < n)
      cv::invariant(0 <= c && c <= n)
      cv::decreases(n - c)
    {
      c = c + 1;
    }
  }
  return c - 1;
}

// A proof gets no notes.
int count_up_proved(int n)
  cv::pre(n >= 0 && n <= 5)
  cv::post(cv::result == n)
{
  int c = 0;
  while (c < n)
    cv::invariant(0 <= c && c <= n)
    cv::decreases(n - c)
  {
    c = c + 1;
  }
  return c;
}

// CHECK:      inductive_counterexamples.cpp:16:23: error: verification failed: count_up [postcondition]
// CHECK: inductive_counterexamples.cpp:19:3: note: enters the loop
// CHECK: inductive_counterexamples.cpp:19:3: note: leaves the loop
// CHECK: note: the counterexample's state at the loop at 19:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 5 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof
// CHECK-NEXT: inductive_counterexamples.cpp:29:23: error: verification failed: sum_wrong [postcondition]
// CHECK: note: the counterexample's state at the loop at 32:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check within 1 iteration of each loop (counterexample: {{.*}}n = 1{{.*}})
// CHECK-NEXT: inductive_counterexamples.cpp:43:23: error: verification failed: far_wrong [postcondition]
// CHECK: note: the counterexample's state at the loop at 46:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check within 10 iterations of each loop
// CHECK-NEXT: inductive_counterexamples.cpp:57:23: error: verification failed: no_loop [postcondition]
// CHECK: inductive_counterexamples.cpp:64:23: error: verification failed: unmeasured [postcondition]
// CHECK: note: the loop at 67:3 has no cppverify::decreases: a proof would be Unresolved (decreases.missing) until it has one
// CHECK-NEXT: note: the counterexample's state at the loop at 67:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check with no iteration of any loop (counterexample: {{.*}}n = 0{{.*}})
// CHECK-NEXT: inductive_counterexamples.cpp:87:7: error: verification failed: divides [division-by-zero]
// CHECK: note: the counterexample's state at the loop at 83:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check within 4 iterations of each loop (counterexample: {{.*}}c = 0 -> 1 -> 2 -> 3{{.*}})
// CHECK-NEXT: inductive_counterexamples.cpp:100:21: error: verification failed: grows [invariant-preserved]
// CHECK: note: the counterexample's state at the loop at 99:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: inductive_counterexamples.cpp:119:5: error: verification failed: two_checks [assertion]
// CHECK: note: the counterexample's state at the loop at 115:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check within 5 iterations of each loop (counterexample: {{.*}}n = 5{{.*}})
// CHECK-NEXT: inductive_counterexamples.cpp:140:7: error: verification failed: two_kinds [overflow]
// CHECK: note: the counterexample's state at the loop at 136:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check without failing an earlier one first (the division-by-zero check at 140:7 fails): those that pass the checks before it end every loop within 2 iterations, and unrolling proves it there
// CHECK-NEXT: inductive_counterexamples.cpp:160:7: error: verification failed: past_failure [division-by-zero]
// CHECK: note: the counterexample's state at the loop at 156:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check within 4 iterations of each loop (counterexample: {{.*}}k = 3, m = 100{{.*}})
// CHECK-NEXT: inductive_counterexamples.cpp:170:23: error: verification failed: skipped [postcondition]
// CHECK: Verified: count_up_proved [backend=z3]
// CHECK-NEXT: Summary: 1 verified, 11 failed

// Without unrolling, a failure still says where its state comes from.
// NONE:      error: verification failed: count_up
// NONE: note: the counterexample's state at the loop at 19:3 is any state its invariants allow, not necessarily one an execution reaches
// NONE-NEXT: error: verification failed: sum_wrong

// JSON: "function":"count_up",{{.*}}"notes":["the counterexample's state at the loop at 19:3 is any state its invariants allow, not necessarily one an execution reaches","no execution fails this check: every loop ends within 5 iterations{{.*}}"]
// JSON: "function":"no_loop"
// JSON-NOT: "notes"
// JSON: "function":"unmeasured"

// OPTION: error: --confirm-bound requires source verification with --backend=z3, cvc5, portfolio, or race
