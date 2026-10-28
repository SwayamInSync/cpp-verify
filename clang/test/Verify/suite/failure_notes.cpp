// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --strict-whitespace
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --jobs=1 --obligation-out=%t.cpv %s -- > /dev/null 2>&1
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 | FileCheck %s --check-prefix=REPLAY
//
// A failure is a Clang error at the failing check, its expression
// underlined with the caret at its operator when it lies on one line (a
// caret alone otherwise); its counterexample, each variable once with the
// values it takes along the path, and not those of branches the path does
// not take; and each step of the path at its line, in the words of Clang's
// static analyzer. A path of more than ten steps shows its first and last
// five. A step inside a macro is shown where the macro is used, and an
// operation whose own check fails is no step of the path.

namespace cv = cppverify;

int steps(int x)
  cv::pre(0 <= x && x <= 10)
  cv::post(cv::result < 3)
{
  int y = 0;
  if (x > 4)
    y = y + 1;
  else
    y = y + 2;
  if (x > 8)
    y = y + 3;
  return y;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-11]]:23: error: verification failed: steps [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-12]] |   cv::post(cv::result < 3){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-14]]:23: note: counterexample: x = {{9|10}}, y = 0 -> 1 -> 4, result = 4
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   if (x > 4){{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-11]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-12]] |   if (x > 8){{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: returns 4
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   return y;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}

int add(int a)
  cv::pre(a < 100)
  cv::post(cv::result == a + 1)
{
  return a + 1;
}

int calls(int x)
  cv::pre(0 <= x && x < 50)
  cv::post(cv::result < 10)
{
  return add(x);
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-4]]:23: error: verification failed: calls [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-5]] |   cv::post(cv::result < 10){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-7]]:23: note: counterexample: x = [[X:[0-9]+]], result = {{[0-9]+}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-6]]:3: note: calls add([[X]])
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   return add(x);{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:3: note: returns {{[0-9]+}}


void store(int *p, int v)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == 7)
{
  *p = v;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-4]]:15: error: verification failed: store [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-5]] |   cv::post(*p == 7){{$}}
// CHECK-NEXT: {{^}}      |            ~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-7]]:15: note: counterexample: p = [[P:[0-9]+]], v = [[V:-?[0-9]+]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-6]]:6: note: stores [[V]] at address [[P]]
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   *p = v;{{$}}
// CHECK-NEXT: {{^}}      |      ^{{$}}

int heap(int v)
  cv::post(cv::result == 1)
{
  int *p = new int(v);
  int r = *p;
  delete p;
  return r;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-7]]:23: error: verification failed: heap [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-8]] |   cv::post(cv::result == 1){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:23: note: counterexample: v = [[V:-?[0-9]+]], p = [[P:[0-9]+]], r = [[V]], result = [[V]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:3: note: allocates an object at address [[P]]
// CHECK-NEXT: {{^ *}}[[@LINE-10]] |   int *p = new int(v);{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:3: note: deletes the object at address [[P]]
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |   delete p;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: returns [[V]]
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   return r;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}

int local(int v)
  cv::pre(0 <= v && v < 100)
  cv::post(cv::result == 1)
{
  int a = v;
  int &r = a;
  r = r + 1;
  return a;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-7]]:23: error: verification failed: local [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-8]] |   cv::post(cv::result == 1){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:23: note: counterexample: v = [[V:[0-9]+]], &r = [[A:[0-9]+]], result = [[R:[0-9]+]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:3: note: creates a local object at address [[A]]
// CHECK-NEXT: {{^ *}}[[@LINE-10]] |   int a = v;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:5: note: stores [[R]] at address [[A]]
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |   r = r + 1;{{$}}
// CHECK-NEXT: {{^}}      |     ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: returns [[R]]
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   return a;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}

int scoped(int v)
  cv::pre(2 <= v && v < 100)
  cv::post(cv::result == 1)
{
  int s = 0;
  {
    int a = v;
    int &r = a;
    s = r;
  }
  return s;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-10]]:23: error: verification failed: scoped [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |   cv::post(cv::result == 1){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-13]]:23: note: counterexample: v = [[V:[0-9]+]], s = 0 -> [[V]], &r = [[A:[0-9]+]], result = [[V]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:5: note: creates a local object at address [[A]]
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |     int a = v;{{$}}
// CHECK-NEXT: {{^}}      |     ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:3: note: ends the lifetime of a local object
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |   }{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: returns [[V]]
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   return s;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}

int loop(int n)
  cv::pre(0 <= n && n <= 5)
  cv::post(cv::result == 0)
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-11]]:23: error: verification failed: loop [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-12]] |   cv::post(cv::result == 0){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-14]]:23: note: counterexample: n = [[N:[1-5]]], i = 0 -> [[N]], result = [[N]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-12]]:3: note: enters the loop
// CHECK-NEXT: {{^ *}}[[@LINE-13]] |   while (i < n){{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-15]]:3: note: leaves the loop
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-10]]:3: note: returns [[N]]
// CHECK-NEXT: {{^ *}}[[@LINE-11]] |   return i;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: note: the counterexample's state at the loop at [[@LINE-19]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: an execution fails this check within 1 iteration of each loop (counterexample: n = 1, i = 0 -> 1, result = 1)

int long_path(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result < 12)
{
  int c = 0;
  if (x > 0) c = c + 1;
  if (x > 1) c = c + 1;
  if (x > 2) c = c + 1;
  if (x > 3) c = c + 1;
  if (x > 4) c = c + 1;
  if (x > 5) c = c + 1;
  if (x > 6) c = c + 1;
  if (x > 7) c = c + 1;
  if (x > 8) c = c + 1;
  if (x > 9) c = c + 1;
  if (x > 10) c = c + 1;
  if (x > 11) c = c + 1;
  return c;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-17]]:23: error: verification failed: long_path [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-18]] |   cv::post(cv::result < 12){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-20]]:23: note: counterexample: x = {{[0-9]+}}, c = 0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 6 -> 7 -> 8 -> 9 -> 10 -> 11 -> 12, result = 12
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-18]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-19]] |   if (x > 0) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-20]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-21]] |   if (x > 1) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-22]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-23]] |   if (x > 2) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-24]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-25]] |   if (x > 3) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-26]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-27]] |   if (x > 4) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: note: (skipping 3 steps of the path; JSON lists every one)
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-26]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-27]] |   if (x > 8) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-28]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-29]] |   if (x > 9) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-30]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-31]] |   if (x > 10) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-32]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-33]] |   if (x > 11) c = c + 1;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-34]]:3: note: returns 12
// CHECK-NEXT: {{^ *}}[[@LINE-35]] |   return c;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}

int two_lines(int x)
  cv::pre(0 <= x && x <= 10)
  cv::post(cv::result ==
           x + 1)
{
  return x;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-5]]:23: error: verification failed: two_lines [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-6]] |   cv::post(cv::result =={{$}}
// CHECK-NEXT: {{^}}      |                       ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-8]]:23: note: counterexample: x = [[X:[0-9]+]], result = [[X]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-6]]:3: note: returns [[X]]
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   return x;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}


// JSON keeps every version, and marks those of branches the path does not
// take.
// A step the counterexample does not decide is marked.
int undecided(bool choose)
  cv::post(cv::result == 0)
{
  if (choose) {
  } else {
  }
  return 1;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-7]]:23: error: verification failed: undecided [postcondition] [backend=z3] [reason=counterexample]
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-6]]:3: note: perhaps takes the true branch (the counterexample does not decide whether this step is taken)
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   if (choose) {{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:3: note: perhaps takes the false branch (the counterexample does not decide whether this step is taken)

// A check inside a loop fails in an arbitrary iteration of it.
int iterate(int n)
  cv::pre(0 <= n && n <= 5)
  cv::post(cv::result == n)
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    cv::check(i < 4);
    i = i + 1;
  }
  return i;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-5]]:5: error: verification failed: iterate [assertion] [backend=z3] [reason=counterexample]
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-6]]:5: note: counterexample: n = [[N:[45]]], i = 0 -> 4
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-11]]:3: note: enters the loop
// CHECK-NEXT: {{^ *}}[[@LINE-12]] |   while (i < n){{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-14]]:3: note: starts an arbitrary iteration of the loop, where its condition is true

// An archive keeps where each version is defined, so its replay lists the
// same values.
// REPLAY: error: verification failed: steps [postcondition]
// REPLAY-NEXT: {{.*}}failure_notes.cpp:[[@LINE-274]]:23: note: counterexample: x = {{9|10}}, y = 0 -> 1 -> 4, result = 4

// JSON: "function":"steps"{{.*}}{"name":"y","on_path":false,"sort":"i32",{{.*}}"ssa_name":"y_3","value":"0"}

#define BUMP_IF_LARGE(v) if ((v) > 5) (v) = (v) + 1

int in_macro(int x)
  cv::pre(0 <= x && x <= 10)
  cv::post(cv::result <= 6)
{
  int y = x;
  BUMP_IF_LARGE(y);
  return y;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-6]]:23: error: verification failed: in_macro [postcondition] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-7]] |   cv::post(cv::result <= 6){{$}}
// CHECK-NEXT: {{^}}      |            ~~~~~~~~~~~^~~~{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:23: note: counterexample: x = [[X:[6-9]|10]], y = [[X]] -> [[Y:[0-9]+]], result = [[Y]]
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-7]]:3: note: takes the true branch
// CHECK-NEXT: {{^ *}}[[@LINE-8]] |   BUMP_IF_LARGE(y);{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-9]]:3: note: returns [[Y]]

int negated(int x)
  cv::post(cv::result >= 0 || cv::result < 0)
{
  return -x;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-2]]:3: error: verification failed: negated [overflow] [backend=z3] [reason=counterexample]
// CHECK-NEXT: {{^ *}}[[@LINE-3]] |   return -x;{{$}}
// CHECK-NEXT: {{^}}      |   ^{{$}}
// CHECK-NEXT: {{.*}}failure_notes.cpp:[[@LINE-5]]:3: note: counterexample: x = -2147483648
// CHECK-NOT: note:
// CHECK: error: verification failed: bump

void bump(int *p)
  cv::pre(p != nullptr)
  cv::modifies(*p)
{
  *p = *p + 1;
}
//      CHECK: {{.*}}failure_notes.cpp:[[@LINE-2]]:6: note: counterexample: p = {{[0-9]+}}
// CHECK-NOT: note:
// CHECK: Summary:

// BMC unrolls the loop, so its path runs the iterations one by one.
// BMC: error: verification failed: loop [postcondition] [backend=bmc, bound=1] [reason=counterexample]
// BMC: note: counterexample: n = 1, i = 0 -> 1, result = 1
// BMC-NEXT: note: runs iteration 1 of the loop
