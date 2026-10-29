// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
//
// A local declared where its name is already taken, by a parameter or by an
// earlier local, in an enclosing or an earlier scope, is another variable
// (x#2, x#3, ... inside the verifier). Every correct function has a wrong
// twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

int two_loops(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == 2 * n)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && s == i)
    cv::decreases(n - i)
  {
    s = s + 1;
  }
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && s == n + i)
    cv::decreases(n - i)
  {
    s = s + 1;
  }
  return s;
}
// CHECK-DAG: Verified: two_loops [backend=z3]

int two_loops_wrong(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == n)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && s == i)
    cv::decreases(n - i)
  {
    s = s + 1;
  }
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && s == n + i)
    cv::decreases(n - i)
  {
    s = s + 1;
  }
  return s;
}
// CHECK-DAG: error: verification failed: two_loops_wrong [{{.*}}[reason=counterexample]

// An inner local hides an outer one only in its block.
int hidden(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == x)
{
  int y = x;
  {
    int y = 5;
    y = y + 1;
  }
  return y;
}
// CHECK-DAG: Verified: hidden [backend=z3]

int hidden_wrong(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == 6)
{
  int y = x;
  {
    int y = 5;
    y = y + 1;
  }
  return y;
}
// CHECK-DAG: error: verification failed: hidden_wrong [postcondition]{{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: x = {{[0-9]+}}, y (line [[@LINE-8]]) = {{[0-9]+}}, y (line [[@LINE-6]]) = 5 -> 6, result = {{[0-9]+}}

// A block may hide a parameter; the contract reads the parameter.
int parameter_hidden(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == x + 3)
{
  int r = x;
  {
    int x = 3;
    r = r + x;
  }
  return r;
}
// CHECK-DAG: Verified: parameter_hidden [backend=z3]

int parameter_hidden_wrong(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == 2 * x)
{
  int r = x;
  {
    int x = 3;
    r = r + x;
  }
  return r;
}
// CHECK-DAG: error: verification failed: parameter_hidden_wrong [postcondition]{{.*}}[reason=counterexample]

// Each declaration starts uninitialized, whatever an earlier one with its
// name held.
int initialized_each(int x)
  cv::post(true)
{
  int s = 0;
  {
    int t = 1;
    s = s + t;
  }
  {
    int t;
    s = s + t;
  }
  return s;
}
// CHECK-DAG: local_names.cpp:[[@LINE-4]]:13: error: initialized_each: read of uninitialized local value: t#2

// Locals lent to a callee are objects of their own.
void set(int *p, int v)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == v)
{
  *p = v;
}
// CHECK-DAG: Verified: set [backend=z3]

int lent_twice(int x)
  cv::post(cv::result == 10)
{
  int t = 1;
  set(&t, 3);
  {
    int t = 2;
    set(&t, 7);
    x = t;
  }
  return x + t;
}
// CHECK-DAG: Verified: lent_twice [backend=z3]

int lent_twice_wrong(int x)
  cv::post(cv::result == 14)
{
  int t = 1;
  set(&t, 3);
  {
    int t = 2;
    set(&t, 7);
    x = t;
  }
  return x + t;
}
// CHECK-DAG: error: verification failed: lent_twice_wrong [{{.*}}[reason=counterexample]

// VCR-LABEL: fn hidden
// VCR:         assign y
// VCR-NEXT:      x
// VCR-NEXT:    assign y#2
// VCR-NEXT:      5
// VCR-NEXT:    assign y#2
// VCR-NEXT:      +
// VCR-NEXT:        y#2
// VCR-NEXT:        1
// VCR-NEXT:    return
// VCR-NEXT:      y
