// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --check-prefix=ONE
// RUN: not %cpp-verify --jobs=1 --max-failures=2 %s -- 2>&1 | FileCheck %s --check-prefix=TWO
// RUN: not %cpp-verify --jobs=4 --max-failures=2 %s -- 2>&1 | FileCheck %s --check-prefix=TWO
// RUN: not %cpp-verify --jobs=1 --max-failures=0 %s -- 2>&1 | FileCheck %s --check-prefix=ALL
// RUN: not %cpp-verify --jobs=4 --max-failures=0 %s -- 2>&1 | FileCheck %s --check-prefix=ALL
// RUN: not %cpp-verify --jobs=1 --max-failures=0 --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --backend=cvc5 --max-failures=2 %s -- 2>&1 | FileCheck %s --check-prefix=OPTION
//
// A function reports the first check that fails, in the order an execution
// meets them; --max-failures=N reports the first N, and 0 every one, each
// with its own counterexample. A check after the first failure is solved in
// the executions that pass the failing checks before it, so its
// counterexample reaches it, and a check that fails only where an earlier
// one does is not reported. The summary still counts functions.

namespace cv = cppverify;

int three_bugs(int x, int y)
  cv::pre(x < 1000 && y < 1000)
  cv::post(cv::result > 0)
  cv::post(cv::result < 100)
{
  int q = 10 / y;
  int r = x + q;
  return r;
}

int one_bug(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x)
{
  return x + 1;
}

// The assertion fails only where the division divides by zero.
int dependent(int x)
  cv::pre(x < 100)
  cv::post(true)
{
  int q = 100 / x;
  cv::check(x != 0);
  return q;
}

// Each failure has its notes: the first holds in every execution, which its
// loop's missing invariant hides, and the second fails at once.
int counted(int n)
  cv::pre(n >= 0 && n <= 3)
  cv::post(cv::result == n)
  cv::post(cv::result == n + 1)
{
  int c = 0;
  while (c < n)
    cv::decreases(n - c)
  {
    c = c + 1;
  }
  return c;
}

// ONE:      max_failures.cpp:23:3: error: verification failed: three_bugs [division-by-zero] [backend=z3] [reason=counterexample]
// ONE: note: counterexample: {{.*}}y = 0{{( ->|,|$)}}
// ONE: max_failures.cpp:30:23: error: verification failed: one_bug [postcondition]
// ONE: max_failures.cpp:40:3: error: verification failed: dependent [division-by-zero]
// ONE: max_failures.cpp:49:23: error: verification failed: counted [postcondition]
// ONE: note: the counterexample's state at the loop at 53:3 is any state its invariants allow, not necessarily one an execution reaches
// ONE-NEXT: note: no execution fails this check: every loop ends within 3 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof
// ONE-NEXT: Summary: 4 failed

// The overflow's counterexample divides by y, which is not zero.
// TWO:      max_failures.cpp:23:3: error: verification failed: three_bugs [division-by-zero]
// TWO: max_failures.cpp:24:3: error: verification failed: three_bugs [overflow] [backend=z3] [reason=counterexample]
// TWO: note: counterexample: {{.*}}y = {{-?[1-9][0-9]*}}{{( ->|,|$)}}
// TWO: max_failures.cpp:30:23: error: verification failed: one_bug [postcondition]
// TWO: max_failures.cpp:40:3: error: verification failed: dependent [division-by-zero]
// TWO: max_failures.cpp:49:23: error: verification failed: counted [postcondition]
// TWO: note: the counterexample's state at the loop at 53:3 is any state its invariants allow, not necessarily one an execution reaches
// TWO-NEXT: note: no execution fails this check: every loop ends within 3 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof
// TWO-NEXT: max_failures.cpp:50:23: error: verification failed: counted [postcondition]
// TWO: note: the counterexample's state at the loop at 53:3 is any state its invariants allow, not necessarily one an execution reaches
// TWO-NEXT: note: an execution fails this check with no iteration of any loop (counterexample: {{.*}}n = 0{{.*}})
// TWO-NEXT: Summary: 4 failed

// ALL:      max_failures.cpp:23:3: error: verification failed: three_bugs [division-by-zero]
// ALL: max_failures.cpp:24:3: error: verification failed: three_bugs [overflow]
// ALL: note: counterexample: {{.*}}y = {{-?[1-9][0-9]*}}{{( ->|,|$)}}
// ALL: max_failures.cpp:20:23: error: verification failed: three_bugs [postcondition]
// ALL: note: counterexample: {{.*}}y = {{-?[1-9][0-9]*}}{{( ->|,|$)}}
// ALL: max_failures.cpp:21:23: error: verification failed: three_bugs [postcondition]
// ALL: note: counterexample: {{.*}}y = {{-?[1-9][0-9]*}}{{( ->|,|$)}}
// ALL: max_failures.cpp:30:23: error: verification failed: one_bug [postcondition]
// ALL: max_failures.cpp:40:3: error: verification failed: dependent [division-by-zero]
// ALL: max_failures.cpp:49:23: error: verification failed: counted [postcondition]
// ALL: note: the counterexample's state at the loop at 53:3 is any state its invariants allow, not necessarily one an execution reaches
// ALL-NEXT: note: no execution fails this check: every loop ends within 3 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof
// ALL-NEXT: max_failures.cpp:50:23: error: verification failed: counted [postcondition]
// ALL: note: the counterexample's state at the loop at 53:3 is any state its invariants allow, not necessarily one an execution reaches
// ALL-NEXT: note: an execution fails this check with no iteration of any loop (counterexample: {{.*}}n = 0{{.*}})
// ALL-NEXT: Summary: 4 failed

// JSON-COUNT-4: "function":"three_bugs"
// JSON-NOT: "function":"three_bugs"
// JSON: "function":"one_bug"
// JSON-NEXT: "function":"dependent"
// JSON-COUNT-2: "function":"counted"{{.*}}"notes":[
// JSON-NOT: "function"

// OPTION: error: --max-failures requires source verification with --backend=z3
