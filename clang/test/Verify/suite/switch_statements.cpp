// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
//
// A switch runs the statements from the label its value matches, or from
// its default label when no case matches, to its end or to a break; a
// statement that leaves no label behind falls through to the next one.
// Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

int fall(int x)
  cv::post(x == 0 ? cv::result == 3 : true)
  cv::post(x == 1 ? cv::result == 2 : true)
  cv::post(x == 2 ? cv::result == 1 : true)
  cv::post(x < 0 || x > 2 ? cv::result == 0 : true)
{
  int r = 0;
  switch (x) {
  case 0:
    r = r + 1;
    [[fallthrough]];
  case 1:
    r = r + 1;
    [[fallthrough]];
  case 2:
    r = r + 1;
  }
  return r;
}
// CHECK-DAG: Verified: fall [backend=z3]

int fall_wrong(int x)
  cv::post(x == 0 ? cv::result == 1 : true)
{
  int r = 0;
  switch (x) {
  case 0:
    r = r + 1;
  case 1:
    r = r + 1;
    break;
  case 2:
    r = 7;
  }
  return r;
}
// CHECK-DAG: error: verification failed: fall_wrong [{{.*}}::postcondition@[[@LINE-14]]:{{.*}}x [ssa=x_0] [type=i32] = 0{{[,;]}}{{.*}}[reason=counterexample]

// The default label may stand anywhere; it is reached only when no case
// matches, and falls through like any other.
int middle_default(int x)
  cv::post(x == 5 ? cv::result == 50 : true)
  cv::post(x == 6 ? cv::result == 60 : true)
  cv::post(x != 5 && x != 6 ? cv::result == 61 : true)
{
  int r = 0;
  switch (x) {
  case 5:
    r = 50;
    break;
  default:
    r = 1;
  case 6:
    r = r + 60;
    break;
  }
  return r;
}
// CHECK-DAG: Verified: middle_default [backend=z3]

int middle_default_wrong(int x)
  cv::post(x == 6 ? cv::result == 61 : true)
{
  int r = 0;
  switch (x) {
  case 5:
    r = 50;
    break;
  default:
    r = 1;
  case 6:
    r = r + 60;
    break;
  }
  return r;
}
// CHECK-DAG: error: verification failed: middle_default_wrong [{{.*}}x [ssa=x_0] [type=i32] = 6{{[,;]}}{{.*}}[reason=counterexample]

// Without a default label, a value no case matches runs nothing.
int no_match(int x)
  cv::post(x != 1 && x != 2 ? cv::result == 0 : cv::result == x)
{
  int r = 0;
  switch (x) {
  case 1:
    r = 1;
    break;
  case 2:
    r = 2;
    break;
  }
  return r;
}
// CHECK-DAG: Verified: no_match [backend=z3]

int no_match_wrong(int x)
  cv::post(cv::result != 0)
{
  int r = 0;
  switch (x) {
  case 1:
    r = 1;
    break;
  case 2:
    r = 2;
    break;
  }
  return r;
}
// CHECK-DAG: error: verification failed: no_match_wrong [{{.*}}[reason=counterexample]

// An enumeration holds the values of its range, here 0 to 3, so a switch
// over its three enumerators leaves 3 to what follows.
enum Color { Red, Green, Blue };

int color_value(Color c)
  cv::post(cv::result >= 1 && cv::result <= 4)
{
  switch (c) {
  case Red:
    return 1;
  case Green:
    return 2;
  case Blue:
    return 3;
  }
  return 4;
}
// CHECK-DAG: Verified: color_value [backend=z3]

int color_value_wrong(Color c)
  cv::post(cv::result >= 1 && cv::result <= 3)
{
  switch (c) {
  case Red:
    return 1;
  case Green:
    return 2;
  case Blue:
    return 3;
  }
  return 0;
}
// CHECK-DAG: error: verification failed: color_value_wrong [{{.*}}c [ssa=c_0] [type=u32] = 3{{[,;]}}{{.*}}[reason=counterexample]

// Case values keep the width of the condition.
int big_case(long long x)
  cv::post(cv::result == (x == 5000000000LL ? 1 : 0))
{
  switch (x) {
  case 5000000000LL:
    return 1;
  default:
    return 0;
  }
}
// CHECK-DAG: Verified: big_case [backend=z3]

int big_case_wrong(long long x)
  cv::post(cv::result == 0)
{
  switch (x) {
  case 5000000000LL:
    return 1;
  default:
    return 0;
  }
}
// CHECK-DAG: error: verification failed: big_case_wrong [{{.*}}x [ssa=x_0] [type=i64] = 5000000000{{[,;]}}{{.*}}[reason=counterexample]

// A GNU case range matches every value from its first to its last.
int digit_class(int x)
  cv::post(1 <= x && x <= 9 ? cv::result == 1 : cv::result == 0)
{
  switch (x) {
  case 1 ... 9:
    return 1;
  default:
    return 0;
  }
}
// CHECK-DAG: Verified: digit_class [backend=z3]

int digit_class_wrong(int x)
  cv::post(1 <= x && x < 9 ? cv::result == 1 : cv::result == 0)
{
  switch (x) {
  case 1 ... 9:
    return 1;
  default:
    return 0;
  }
}
// CHECK-DAG: error: verification failed: digit_class_wrong [{{.*}}x [ssa=x_0] [type=i32] = 9{{[,;]}}{{.*}}[reason=counterexample]

// A break in a nested statement leaves the switch; the statements after it
// run only where it did not.
int nested_break(int x, int y)
  cv::post(x == 1 && y > 0 ? cv::result == 10 : true)
  cv::post(x == 1 && y <= 0 ? cv::result == 11 : true)
{
  int r = 0;
  switch (x) {
  case 1:
    r = 10;
    if (y > 0)
      break;
    r = 11;
    break;
  case 2:
    r = 20;
  }
  return r;
}
// CHECK-DAG: Verified: nested_break [backend=z3]

int nested_break_wrong(int x, int y)
  cv::post(x == 1 ? cv::result == 11 : true)
{
  int r = 0;
  switch (x) {
  case 1:
    r = 10;
    if (y > 0)
      break;
    r = 11;
    break;
  case 2:
    r = 20;
  }
  return r;
}
// CHECK-DAG: error: verification failed: nested_break_wrong [{{.*}}x [ssa=x_0] [type=i32] = 1{{[,;]}}{{.*}}[reason=counterexample]

// A break in a loop inside a switch leaves the loop; a continue in a switch
// inside a loop continues the loop.
int inner_loop(int x, int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(x == 1 ? cv::result == n + 100 : true)
{
  int r = 0;
  switch (x) {
  case 1: {
    int i = 0;
    while (true)
      cv::invariant(0 <= i && i <= n)
      cv::decreases(n - i)
    {
      if (i == n)
        break;
      i = i + 1;
    }
    r = i + 100;
    break;
  }
  default:
    r = 0;
  }
  return r;
}
// CHECK-DAG: Verified: inner_loop [backend=z3]

int count_up(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  int count = 0;
  for (; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && count == i)
    cv::decreases(n - i)
  {
    switch (i % 3) {
    case 0:
      count = count + 1;
      continue;
    default:
      count = count + 1;
      break;
    }
  }
  return count;
}
// CHECK-DAG: Verified: count_up [backend=z3]

int count_up_wrong(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  int count = 0;
  for (; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && count <= i)
    cv::decreases(n - i)
  {
    switch (i % 3) {
    case 0:
      continue;
    default:
      count = count + 1;
      break;
    }
  }
  return count;
}
// CHECK-DAG: error: verification failed: count_up_wrong [{{.*}}[reason=counterexample]

// An init statement and a condition variable are declared before the
// value is tested; a condition's call runs before it, once.
int inc(int x)
  cv::pre(x < 1000)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}
// CHECK-DAG: Verified: inc [backend=z3]

int declared(int x)
  cv::pre(-100 < x && x < 100)
  cv::post(cv::result == (x == 2 ? 1 : x + 1))
{
  switch (int y = inc(x); y) {
  case 3:
    return 1;
  default:
    return y;
  }
}
// CHECK-DAG: Verified: declared [backend=z3]

int condition_variable(int x)
  cv::pre(-100 < x && x < 100)
  cv::post(cv::result == 2 * x + 1)
{
  switch (int y = 2 * x) {
  default:
    return inc(y);
  }
}
// CHECK-DAG: Verified: condition_variable [backend=z3]

int condition_variable_wrong(int x)
  cv::pre(-100 < x && x < 100)
  cv::post(cv::result == 2 * x)
{
  switch (int y = 2 * x) {
  default:
    return inc(y);
  }
}
// CHECK-DAG: error: verification failed: condition_variable_wrong [{{.*}}[reason=counterexample]

int nested(int a, int b)
  cv::post(a == 1 ? cv::result == (b == 2 ? 12 : 10) : true)
{
  int r = 0;
  switch (a) {
  case 1:
    switch (b) {
    case 2:
      r = 2;
      break;
    }
    r = r + 10;
    break;
  case 2:
    r = 99;
    break;
  }
  return r;
}
// CHECK-DAG: Verified: nested [backend=z3]

int nested_wrong(int a, int b)
  cv::post(a == 1 ? cv::result == 2 : true)
{
  int r = 0;
  switch (a) {
  case 1:
    switch (b) {
    case 2:
      r = 2;
      break;
    }
    r = r + 10;
    break;
  case 2:
    r = 99;
    break;
  }
  return r;
}
// CHECK-DAG: error: verification failed: nested_wrong [{{.*}}a [ssa=a_0] [type=i32] = 1{{[,;]}}{{.*}}[reason=counterexample]

// Statements before the first label never run; a declaration there is in
// scope after it.
int before_labels(int x)
  cv::post(cv::result == (x == 1 ? 3 : 0))
{
  int r = 0;
  switch (x) {
    int t;
    r = 5;
  case 1:
    t = 3;
    r = t;
  }
  return r;
}
// CHECK-DAG: Verified: before_labels [backend=z3]

// A value is initialized after the switch only where every way out of it
// initializes it.
int initialized(int x)
  cv::post(cv::result > 0)
{
  int r;
  switch (x) {
  case 0:
    r = 1;
    break;
  default:
    r = 2;
  }
  return r;
}
// CHECK-DAG: Verified: initialized [backend=z3]

int uninitialized(int x)
  cv::post(true)
{
  int r;
  switch (x) {
  case 0:
    r = 1;
    break;
  case 1:
    r = 2;
    break;
  }
  return r;
}
// CHECK-DAG: switch_statements.cpp:[[@LINE-2]]:10: error: uninitialized: read of uninitialized local value: r

int uninitialized_by_break(int x)
  cv::post(true)
{
  int r;
  switch (x) {
  case 0:
    if (x == 0)
      break;
    r = 1;
    break;
  default:
    r = 2;
  }
  return r;
}
// CHECK-DAG: switch_statements.cpp:[[@LINE-2]]:10: error: uninitialized_by_break: read of uninitialized local value: r

// A label entered by its own match has only what was initialized before the
// switch, whatever the statements before the label initialize.
int read_after_jump(int x)
  cv::post(true)
{
  int r;
  switch (x) {
  case 0:
    r = 1;
    [[fallthrough]];
  case 1:
    return r;
  }
  return 0;
}
// CHECK-DAG: switch_statements.cpp:[[@LINE-4]]:12: error: read_after_jump: read of uninitialized local value: r

// Each case keeps the checks of its operations, on its own path.
int overflow_in_case(int x)
  cv::post(true)
{
  switch (x) {
  case 1:
    return x + 2147483647;
  default:
    return 0;
  }
}
// CHECK-DAG: error: verification failed: overflow_in_case [{{.*}}::overflow@[[@LINE-5]]:{{.*}}x [ssa=x_0] [type=i32] = 1{{[,;]}}{{.*}}[reason=counterexample]

// A spec, a lifted constexpr helper, a proof function, and ghost code may
// switch too.
cv::spec int select(int x)
{
  switch (x) {
  case 0:
    return 5;
  default:
    return 6;
  }
}
// CHECK-DAG: Verified: spec axiom: select

cv::spec int select_break(int x)
{
  int r = 0;
  switch (x) {
  case 0:
    r = 5;
    break;
  default:
    r = 6;
  }
  return r;
}
// CHECK-DAG: Verified: spec axiom: select_break

int uses_select(int x)
  cv::post(cv::result == select(x) && cv::result == select_break(x))
{
  return x == 0 ? 5 : 6;
}
// CHECK-DAG: Verified: uses_select [backend=z3]

int uses_select_wrong(int x)
  cv::post(cv::result == select(x))
{
  return 6;
}
// CHECK-DAG: error: verification failed: uses_select_wrong [{{.*}}x [ssa=x_0] [type=i32] = 0{{[,;]}}{{.*}}[reason=counterexample]

constexpr int digit_value(char c) {
  switch (c) {
  case 48:
    return 0;
  case 49:
    return 1;
  default:
    return -1;
  }
}

int uses_digit_value(char c)
  cv::pre(c == 49)
  cv::post(cv::result == 1)
{
  return digit_value(c);
}
// CHECK-DAG: Verified: uses_digit_value [backend=z3]

int uses_digit_value_wrong(char c)
  cv::pre(c == 48 || c == 49)
  cv::post(cv::result == 1)
{
  return digit_value(c);
}
// CHECK-DAG: error: verification failed: uses_digit_value_wrong [{{.*}}c [ssa=c_0] [type=i8] = 48{{[,;]}}{{.*}}[reason=counterexample]

cv::proof int positive_choice(int x)
  cv::post(cv::result > 0)
{
  int r = 0;
  switch (x) {
  case 1:
    r = 1;
    break;
  default:
    r = 2;
  }
  return r;
}
// CHECK-DAG: Verified: positive_choice [backend=z3]

int ghosted(int x)
  cv::post(cv::result == x)
{
  cv::ghost {
    int g = 0;
    switch (x) {
    case 3:
      g = 1;
      break;
    default:
      g = 2;
    }
    cv::check(g > 0);
  }
  return x;
}
// CHECK-DAG: Verified: ghosted [backend=z3]

int ghosted_wrong(int x)
  cv::post(cv::result == x)
{
  cv::ghost {
    int g = 0;
    switch (x) {
    case 3:
      g = 1;
      break;
    default:
      g = 2;
    }
    cv::check(g == 2);
  }
  return x;
}
// CHECK-DAG: error: verification failed: ghosted_wrong [{{.*}}x [ssa=x_0] [type=i32] = 3{{[,;]}}{{.*}}[reason=counterexample]

// A local lent to a callee ends where a break leaves its block.
void set(int *p, int v)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == v)
{
  *p = v;
}
// CHECK-DAG: Verified: set [backend=z3]

int lent(int x)
  cv::post(cv::result == (x == 1 ? 7 : 1))
{
  int r = 0;
  switch (x) {
  case 1: {
    int t = 0;
    set(&t, 7);
    r = t;
    break;
  }
  default:
    r = 1;
  }
  return r;
}
// CHECK-DAG: Verified: lent [backend=z3]

// Unsupported, each alone: a label inside another statement of its switch
// (as in Duff's device), and a local whose address is used declared
// directly in a switch, which a later label enters without declaring.
// [[assume(e)]] is proved where it stands (assertions.cpp).
int duff(int n)
  cv::post(true)
{
  int r = 0;
  switch (n % 2) {
  case 0:
    while (r < 1)
      cv::decreases(1 - r)
    {
      r = r + 1;
  case 1:
      r = r + 1;
    }
  }
  return r;
}
// CHECK-DAG: switch_statements.cpp:[[@LINE-6]]:3: error: duff: a case label inside another statement of its switch is unsupported

int assumed(int x)
  cv::post(true)
{
  [[assume(x > 0)]];
  return x;
}
// CHECK-DAG: error: verification failed: assumed [{{.*}}::assertion@[[@LINE-3]]:{{.*}}[reason=counterexample]

int lent_directly(int x)
  cv::post(true)
{
  int r = 0;
  switch (x) {
  case 1:
    int t;
    set(&t, 7);
    r = t;
    break;
  }
  return r;
}
// CHECK-DAG: switch_statements.cpp:[[@LINE-7]]:5: error: lent_directly: a local whose address is used, declared directly in a switch, is unsupported; declare it in a block after its label

// BMC: Verified: fall [backend=bmc, bound=0]
// BMC: error: verification failed: fall_wrong
// BMC: Verified: middle_default [backend=bmc, bound=0]
// BMC: BoundedSafe: count_up [backend=bmc, bound=3]
// BMC: error: verification failed: count_up_wrong
// BMC: Verified: lent [backend=bmc, bound=0]

// VCR-LABEL: fn middle_default
// VCR:         assign __switch_[[ID:[0-9]+]]
// VCR-NEXT:      x
// VCR-NEXT:    assign __switch_entered_[[ID]]
// VCR-NEXT:      false
// VCR-NEXT:    assign __switch_break_[[ID]]
// VCR-NEXT:      false
// VCR-NEXT:    assign __switch_entered_[[ID]]
// VCR-NEXT:      ||
// VCR-NEXT:        __switch_entered_[[ID]]
// VCR-NEXT:        ==
// VCR-NEXT:          __switch_[[ID]]
// VCR-NEXT:          5
// VCR-NEXT:    if
// VCR-NEXT:      &&
// VCR-NEXT:        __switch_entered_[[ID]]
// VCR-NEXT:        !
// VCR-NEXT:          __switch_break_[[ID]]
// VCR-NEXT:      assign r
// VCR-NEXT:        50
// VCR-NEXT:      assign __switch_break_[[ID]]
// VCR-NEXT:        true
// VCR-NEXT:    assign __switch_entered_[[ID]]
// VCR-NEXT:      ||
// VCR-NEXT:        __switch_entered_[[ID]]
// VCR-NEXT:        !
// VCR-NEXT:          ||
// VCR-NEXT:            ==
// VCR-NEXT:              __switch_[[ID]]
// VCR-NEXT:              6
// VCR-NEXT:            ==
// VCR-NEXT:              __switch_[[ID]]
// VCR-NEXT:              5
// VCR-NEXT:    if
// VCR-NEXT:      &&
// VCR-NEXT:        __switch_entered_[[ID]]
// VCR-NEXT:        !
// VCR-NEXT:          __switch_break_[[ID]]
// VCR-NEXT:      assign r
// VCR-NEXT:        1
// VCR-NEXT:    if
// VCR-NEXT:      !
// VCR-NEXT:        __switch_break_[[ID]]
// VCR-NEXT:      assign r
// VCR-NEXT:        +
// VCR-NEXT:          r
// VCR-NEXT:          60
// VCR-NEXT:      assign __switch_break_[[ID]]
// VCR-NEXT:        true
// VCR-NEXT:    return
// VCR-NEXT:      r

// VCR-LABEL: fn lent
// VCR:           call set
// VCR:           end_lifetime t
// VCR-NEXT:      assign __switch_break_{{[0-9]+}}
// VCR-NEXT:        true
