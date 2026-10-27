// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=4 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
//
// break and continue in a do loop, condition declarations in while and for
// loops, a for loop without a condition, and comma expressions as
// statements. Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

// The first iteration of a do loop runs before its invariant holds; a break
// there leaves the loop, and a continue goes to the condition.
int stop_at_three(int n)
  cv::pre(1 <= n && n <= 100)
  cv::post(cv::result == (n < 3 ? n : 3))
{
  int i = 0;
  do {
    i = i + 1;
    if (i == 3)
      break;
  } while (i < n)
    cv::invariant(1 <= i && i <= n && i < 3)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: Verified: stop_at_three [backend=z3]

int stop_at_three_wrong(int n)
  cv::pre(1 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  do {
    i = i + 1;
    if (i == 3)
      break;
  } while (i < n)
    cv::invariant(1 <= i && i <= n && i < 3)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: error: verification failed: stop_at_three_wrong [{{.*}}n [ssa=n_0] [type=i32] = {{[4-9]|[1-9][0-9]+}}{{[,;]}}{{.*}}[reason=counterexample]

// A break in the first iteration skips the loop.
int first_break(int x)
  cv::post(cv::result == (x > 0 ? 1 : 2))
{
  int r = 0;
  do {
    r = 1;
    if (x > 0)
      break;
    r = 2;
  } while (false);
  return r;
}
// CHECK-DAG: Verified: first_break [backend=z3]

int first_break_wrong(int x)
  cv::post(cv::result == 2)
{
  int r = 0;
  do {
    r = 1;
    if (x > 0)
      break;
    r = 2;
  } while (false);
  return r;
}
// CHECK-DAG: error: verification failed: first_break_wrong [{{.*}}x [ssa=x_0] [type=i32] = {{[1-9][0-9]*}}{{[,;]}}{{.*}}[reason=counterexample]

int count_odd(int n)
  cv::pre(1 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  int odd = 0;
  do {
    i = i + 1;
    if (i % 2 == 0)
      continue;
    odd = odd + 1;
  } while (i < n)
    cv::invariant(1 <= i && i <= n && odd == (i + 1) / 2)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: Verified: count_odd [backend=z3]

int count_odd_wrong(int n)
  cv::pre(1 <= n && n <= 100)
  cv::post(cv::result == (n + 1) / 2)
{
  int i = 0;
  int odd = 0;
  do {
    i = i + 1;
    if (i % 2 == 0)
      continue;
    odd = odd + 1;
  } while (i < n)
    cv::invariant(1 <= i && i <= n && odd == (i + 1) / 2)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: error: verification failed: count_odd_wrong [{{.*}}[reason=counterexample]

// A continue in the first iteration goes on to the condition.
int continue_first(int n)
  cv::pre(2 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  do {
    i = i + 1;
    if (i == 1)
      continue;
  } while (i < n)
    cv::invariant(1 <= i && i <= n)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: Verified: continue_first [backend=z3]

int continue_first_wrong(int n)
  cv::pre(2 <= n && n <= 100)
  cv::post(cv::result == 1)
{
  int i = 0;
  do {
    i = i + 1;
    if (i == 1)
      continue;
  } while (i < n)
    cv::invariant(1 <= i && i <= n)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: error: verification failed: continue_first_wrong [{{.*}}[reason=counterexample]

// A continue in the first iteration of a loop that may also break.
int both_exits(int n)
  cv::pre(2 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  do {
    i = i + 1;
    if (i == 1)
      continue;
    if (i > 1000)
      break;
  } while (i < n)
    cv::invariant(1 <= i && i <= n)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: Verified: both_exits [backend=z3]

// A continue in a switch continues the loop around it.
int skip_even(int n)
  cv::pre(1 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  do {
    i = i + 1;
    switch (i % 2) {
    case 0:
      continue;
    default:
      break;
    }
  } while (i < n)
    cv::invariant(1 <= i && i <= n)
    cv::decreases(n - i);
  return i;
}
// CHECK-DAG: Verified: skip_even [backend=z3]

// A value is initialized after the first iteration only where the condition
// is reached, by its end or by a continue, initializing it; after the loop,
// only where each way out initializes it.
int initialized_first(int x)
  cv::post(cv::result == 1)
{
  int r;
  do {
    r = 1;
    if (x > 0)
      break;
  } while (false);
  return r;
}
// CHECK-DAG: Verified: initialized_first [backend=z3]

int uninitialized_by_break(int x)
  cv::post(true)
{
  int r;
  do {
    if (x > 0)
      break;
    r = 1;
  } while (false);
  return r;
}
// CHECK-DAG: loop_forms.cpp:[[@LINE-2]]:10: error: uninitialized_by_break: read of uninitialized local value: r

int uninitialized_by_continue(int x)
  cv::post(true)
{
  int r;
  do {
    if (x > 0)
      continue;
    r = 1;
  } while (r < 0)
    cv::invariant(true)
    cv::decreases(0);
  return 0;
}
// CHECK-DAG: loop_forms.cpp:[[@LINE-5]]:12: error: uninitialized_by_continue: read of uninitialized local value: r

// A condition variable is declared, and its value tested, at every test.
int count_down(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == 0)
{
  int i = n;
  while (int k = i)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(i)
  {
    i = k - 1;
  }
  return i;
}
// CHECK-DAG: Verified: count_down [backend=z3]

int count_down_wrong(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == 0)
{
  int i = n;
  while (int k = i - 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(i)
  {
    i = k;
  }
  return i;
}
// CHECK-DAG: error: verification failed: count_down_wrong [{{.*}}[reason=counterexample]

int count_down_for(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == 0)
{
  int i = n;
  for (; int k = i; i = k - 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(i)
  {
  }
  return i;
}
// CHECK-DAG: Verified: count_down_for [backend=z3]

int named_condition(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(true)
{
  int i = n;
  while (int k = i)
    cv::invariant(0 <= i && i <= n && k >= 0)
    cv::decreases(i)
  {
    i = k - 1;
  }
  return i;
}
// CHECK-DAG: loop_forms.cpp:[[@LINE-8]]:3: error: named_condition: a loop's contract cannot name its condition variable 'k', which is declared at each test

// A for loop without a condition repeats until it is left.
int until_equal(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
{
  int i = 0;
  for (;;)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    if (i == n)
      return i;
    i = i + 1;
  }
}
// CHECK-DAG: Verified: until_equal [backend=z3]

int until_equal_wrong(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n + 1)
{
  int i = 0;
  for (;;)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    if (i == n)
      return i;
    i = i + 1;
  }
}
// CHECK-DAG: error: verification failed: until_equal_wrong [{{.*}}[reason=counterexample]

int spin(int n)
  cv::post(cv::result == 0)
{
  for (;;) {
    if (n == 0)
      break;
  }
  return n;
}
// CHECK-DAG: Unresolved: spin [backend=z3] [reason=decreases.missing]

// A comma expression as a statement runs its operands in order.
int pairs(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == 2 * n)
{
  int i = 0, j = 0;
  for (; i < n; i++, j += 2)
    cv::invariant(0 <= i && i <= n && j == 2 * i)
    cv::decreases(n - i)
  {
  }
  return j;
}
// CHECK-DAG: Verified: pairs [backend=z3]

int pairs_wrong(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == 2 * n)
{
  int i = 0, j = 0;
  for (; i < n; i++, j += 1)
    cv::invariant(0 <= i && i <= n && j == i)
    cv::decreases(n - i)
  {
  }
  return j;
}
// CHECK-DAG: error: verification failed: pairs_wrong [{{.*}}::postcondition@{{.*}}[reason=counterexample]

int ordered(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 2 * x + 1)
{
  int a = 0, b = 0;
  a = x, b = a * 2 + 1;
  return b;
}
// CHECK-DAG: Verified: ordered [backend=z3]

int ordered_wrong(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 1)
{
  int a = 0, b = 0;
  a = x, b = a * 2 + 1;
  return b;
}
// CHECK-DAG: error: verification failed: ordered_wrong [{{.*}}[reason=counterexample]

// BMC: Verified: first_break [backend=bmc, bound=0]
// BMC: error: verification failed: first_break_wrong
// BMC: error: verification failed: count_odd_wrong
// BMC: BoundedSafe: until_equal [backend=bmc, bound=4]
// BMC: error: verification failed: until_equal_wrong

// VCR-LABEL: fn first_break
// VCR:         assign __do_break_[[ID:[0-9]+]]
// VCR-NEXT:      false
// VCR-NEXT:    assign __do_continue_[[ID]]
// VCR-NEXT:      false
// VCR-NEXT:    assign r
// VCR-NEXT:      1
// VCR-NEXT:    if
// VCR-NEXT:      >
// VCR-NEXT:        x
// VCR-NEXT:        0
// VCR-NEXT:      assign __do_break_[[ID]]
// VCR-NEXT:        true
// VCR-NEXT:    if
// VCR-NEXT:      !
// VCR-NEXT:        ||
// VCR-NEXT:          __do_break_[[ID]]
// VCR-NEXT:          __do_continue_[[ID]]
// VCR-NEXT:      assign r
// VCR-NEXT:        2
// VCR-NEXT:    if
// VCR-NEXT:      !
// VCR-NEXT:        __do_break_[[ID]]
// VCR-NEXT:      while
// VCR-NEXT:        false

// VCR-LABEL: fn count_down
// VCR:         while
// VCR-NEXT:      true
// VCR:           assign k
// VCR-NEXT:        i
// VCR-NEXT:      if
// VCR-NEXT:        !
// VCR-NEXT:          cast
// VCR-NEXT:            k
// VCR-NEXT:        break
