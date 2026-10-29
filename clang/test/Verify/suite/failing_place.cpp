// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --strict-whitespace
// RUN: not %cpp-verify --jobs=1 --function=odd_half --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --jobs=1 --function=odd_half --diagnostics-format=sarif %s -- 2>/dev/null | FileCheck %s --check-prefix=SARIF
// RUN: not %cpp-verify --jobs=1 --function=odd_half --diagnostics-format=github %s -- 2>/dev/null | FileCheck %s --check-prefix=GITHUB
// RUN: not %cpp-verify --jobs=1 --obligation-out=%t.cpv %s -- > /dev/null 2>&1
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 | FileCheck %s --check-prefix=REPLAY
// RUN: %python %S/Inputs/mutate_obligation_archive.py schema-v5 %t.cpv %t.v5.cpv
// RUN: not %cpp-verify --obligation-in=%t.v5.cpv 2>&1 | FileCheck %s --check-prefix=REPLAY-V5
//
// A failure is reported at the part of its check that fails. In a
// conjunction, that is the first conjunct the counterexample makes false; a
// disjunction fails as a whole. A check that an operation is defined is at
// the operation, under the short-circuit and branch conditions around it,
// not at the statement. A callee's precondition fails at the call, with a
// note at the callee's clause, its conjunct that does not hold. A replayed
// archive shows the same; one of schema v5, which has no places of checks,
// only a clause's conjunct.

namespace cv = cppverify;

int clamp(int x)
  cv::pre(-100 <= x && x <= 100)
  cv::post(0 <= cv::result && cv::result <= 50 && cv::result != 7)
{
  if (x < 0)
    return 0;
  return x;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-6]]:42: error: verification failed: clamp [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   cv::post(0 <= cv::result && cv::result <= 50 && cv::result != 7){{$}}
// CHECK-NEXT: {{^}}      |                               ~~~~~~~~~~~^~~~~{{$}}
// REPLAY: {{.*}}failing_place.cpp:[[@LINE-9]]:42: error: verification failed: clamp [postcondition]
// REPLAY-V5: {{.*}}failing_place.cpp:[[@LINE-10]]:42: error: verification failed: clamp [postcondition]

// A disjunction fails as a whole.
int either(int x)
  cv::pre(0 <= x && x <= 10)
  cv::post(cv::result < 0 || cv::result > 10)
{
  return x;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-4]]:27: error: verification failed: either [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-5]] |   cv::post(cv::result < 0 || cv::result > 10){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~{{$}}

// A loop invariant that the loop does not keep.
int count(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int i = 0;
  int c = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && c == i && c >= 0)
    cv::decreases(n - i)
  {
    i = i + 1;
    c = c + 2;
  }
  return c;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-8]]:41: error: verification failed: count [invariant-preserved] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-9]] |     cv::invariant(0 <= i && i <= n && c == i && c >= 0){{$}}
// CHECK-NEXT: {{^}}      |                                       ~~^~~~{{$}}

// An assertion in a branch, at its own condition.
void checked(int x)
  cv::pre(-10 <= x && x <= 10)
{
  if (x > 0)
    cv::check(x > 1 && x < 100);
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:17: error: verification failed: checked [assertion] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |     cv::check(x > 1 && x < 100);{{$}}
// CHECK-NEXT: {{^}}      |               ~~^~~{{$}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-5]]:17: note: counterexample: x = 1

// An operation that overflows, not the declaration it is in.
int square(int x)
  cv::post(cv::result > 0)
{
  int y = x * x + 1;
  return y;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-3]]:13: error: verification failed: square [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-4]] |   int y = x * x + 1;{{$}}
// CHECK-NEXT: {{^}}      |           ~~^~~{{$}}
// REPLAY: {{.*}}failing_place.cpp:[[@LINE-6]]:13: error: verification failed: square [overflow]
// REPLAY-V5: {{.*}}failing_place.cpp:[[@LINE-7]]:3: error: verification failed: square [overflow]

// Of the operations of one expression, the one that overflows.
int sum(int x, int y)
  cv::pre(0 <= x && x < 100)
{
  return x + 1 + y * y;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:20: error: verification failed: sum [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return x + 1 + y * y;{{$}}
// CHECK-NEXT: {{^}}      |                  ~~^~~{{$}}

// One under the condition before it.
bool guarded(int a, int b)
  cv::post(true)
{
  return a > 0 && a * b > 0;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:21: error: verification failed: guarded [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return a > 0 && a * b > 0;{{$}}
// CHECK-NEXT: {{^}}      |                   ~~^~~{{$}}

// One in a branch.
int divide(int x, int d)
  cv::post(true)
{
  if (d > 5)
    return x / d;
  return x / (d - 3);
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:17: error: verification failed: divide [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return x / (d - 3);{{$}}
// CHECK-NEXT: {{^}}      |              ~~~^~~~{{$}}

// An access out of bounds.
int read(const int *a, int n, int i)
  cv::pre(cv::valid(a, n) && 0 < n && n < 100)
{
  return a[i];
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:10: error: verification failed: read [bounds] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return a[i];{{$}}
// CHECK-NEXT: {{^}}      |          ^{{$}}

// A callee's precondition: at the call, and at the callee's conjunct.
int half(int x)
  cv::pre(0 <= x && x % 2 == 0)
  cv::post(cv::result * 2 == x)
{
  return x / 2;
}

int odd_half(int y)
  cv::pre(0 <= y && y <= 100)
{
  return half(2 * y + 1);
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:10: error: verification failed: odd_half [precondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return half(2 * y + 1);{{$}}
// CHECK-NEXT: {{^}}      |          ^~~~~~~~~~~~~~~{{$}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-5]]:10: note: counterexample: y = 0
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-15]]:27: note: this precondition does not hold at the call
// CHECK-NEXT: {{^ *}}[[@LINE-16]] |   cv::pre(0 <= x && x % 2 == 0){{$}}
// CHECK-NEXT: {{^}}      |                     ~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-9]]:10: note: calls half(1)
// REPLAY: {{.*}}failing_place.cpp:[[@LINE-10]]:10: error: verification failed: odd_half [precondition]
// REPLAY: {{.*}}failing_place.cpp:[[@LINE-20]]:27: note: this precondition does not hold at the call
// REPLAY-V5: {{.*}}failing_place.cpp:[[@LINE-12]]:3: error: verification failed: odd_half [precondition]
// REPLAY-V5-NOT: this precondition

// JSON:      "related":[{"message":"this precondition does not hold at the call","source":{"column":21,"end_column":31,"end_line":[[#@LINE-24]],"file":"{{.*}}failing_place.cpp","line":[[#@LINE-24]]}}]
// SARIF:     "relatedLocations": [
// SARIF:       "message": {
// SARIF-NEXT:    "text": "this precondition does not hold at the call"
// SARIF:         "endColumn": 31,
// SARIF-NEXT:    "endLine": [[#@LINE-29]],
// SARIF-NEXT:    "startColumn": 21,
// SARIF-NEXT:    "startLine": [[#@LINE-31]]
// GITHUB:    ::error file={{.*}}failing_place.cpp,line=[[#@LINE-23]],col=10,{{.*}}title=cpp-verify%3A precondition::verification failed: odd_half {{.*}}%0Athis precondition does not hold at the call ({{.*}}failing_place.cpp:[[#@LINE-32]]:27)

// Of several clauses, the one the call does not establish, whole.
int two(int x)
  cv::pre(x > 0)
  cv::pre(x < 10)
  cv::post(cv::result == x)
{
  return x;
}

int both(int y)
  cv::pre(0 < y && y < 5)
{
  return two(y) + two(y + 20);
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:19: error: verification failed: both [precondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return two(y) + two(y + 20);{{$}}
// CHECK-NEXT: {{^}}      |                   ^~~~~~~~~~~{{$}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-5]]:19: note: counterexample: y = {{[1-4]}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-15]]:13: note: this precondition does not hold at the call
// CHECK-NEXT: {{^ *}}[[@LINE-16]] |   cv::pre(x < 10){{$}}
// CHECK-NEXT: {{^}}      |           ~~^~~~{{$}}

// A member function's: at the member's name.
struct Box {
  int v;
  int take()
    cv::pre(v > 3)
    cv::post(cv::result == v)
  {
    return v;
  }
};

int member(int k)
  cv::pre(0 <= k && k < 10)
{
  Box b;
  b.v = k;
  return b.take();
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:12: error: verification failed: member [precondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return b.take();{{$}}
// CHECK-NEXT: {{^}}      |          ~~^~~~~~{{$}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-5]]:12: note: counterexample: k = {{[0-3]}}
// CHECK-NEXT: {{.*}}failing_place.cpp:[[@LINE-18]]:15: note: this precondition does not hold at the call

// A call that is an argument of another: the inner call.
int nested(int y)
  cv::pre(0 <= y && y < 50)
{
  return two(two(y));
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-2]]:14: error: verification failed: nested [precondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return two(two(y));{{$}}
// CHECK-NEXT: {{^}}      |              ^~~~~~{{$}}

// A lifted helper's check stays at the statement that calls it.
constexpr int doubled(int v) { return 2 * v; }

int uses_helper(int x)
  cv::post(true)
{
  int y = doubled(x) + 0;
  return y;
}
//      CHECK: {{.*}}failing_place.cpp:[[@LINE-3]]:3: error: verification failed: uses_helper [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-4]] |   int y = doubled(x) + 0;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// REPLAY: {{.*}}failing_place.cpp:[[@LINE-6]]:3: error: verification failed: uses_helper [overflow]
