// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
//
// A slice argument lies in valid storage when its elements lie in one of the
// caller's objects, however the pointer was computed: a copy, a choice, a
// pointer stepped in a loop, or a callee's result. Before, only a parameter
// plus an offset written at the call was contained, and every other argument
// failed with a counterexample although the program was correct.

int first(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 1)
  cppverify::post(cppverify::result == p[0])
{
  return p[0];
}
// CHECK-DAG: Verified: first [backend=z3]

int count(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 0)
  cppverify::post(cppverify::result == n)
{
  return n;
}
// CHECK-DAG: Verified: count [backend=z3]

void zero2(int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 2)
  cppverify::modifies(p[0 : 2])
  cppverify::post(p[0] == 0 && p[1] == 0)
{
  p[0] = 0;
  p[1] = 0;
}
// CHECK-DAG: Verified: zero2 [backend=z3]

const int *next(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 2)
  cppverify::post(cppverify::result == a + 1)
{
  return a + 1;
}
// CHECK-DAG: Verified: next [backend=z3]

const int *somewhere(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 2)
  cppverify::post(cppverify::result != nullptr)
{
  return a + 1;
}
// CHECK-DAG: Verified: somewhere [backend=z3]

int copied(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::post(cppverify::result == a[1])
{
  const int *q = a + 1;
  return first(q, 3);
}
// CHECK-DAG: Verified: copied [backend=z3]

void copied_write(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(a[0 : 4])
  cppverify::post(a[1] == 0 && a[2] == 0 && a[3] == cppverify::old(a[3]))
{
  int *q = a + 1;
  zero2(q, 3);
}
// CHECK-DAG: Verified: copied_write [backend=z3]

void chosen(int *a, int *b, bool c)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(a[0 : 4], b[0 : 4])
{
  int *q = c ? a + 1 : b;
  zero2(q, 3);
}
// CHECK-DAG: Verified: chosen [backend=z3]

int from_result(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::post(cppverify::result == a[1])
{
  const int *q = next(a, 4);
  return first(q, 3);
}
// CHECK-DAG: Verified: from_result [backend=z3]

int one_past_empty(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::post(cppverify::result == 0)
{
  const int *q = a + 4;
  return count(q, 0);
}
// CHECK-DAG: Verified: one_past_empty [backend=z3]

int walked(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 2 && n <= 100)
  cppverify::post(cppverify::result == a[n - 1])
{
  const int *q = a;
  int i = 0;
  while (i < n - 1)
    cppverify::invariant(0 <= i && i <= n - 1 && q == a + i)
    cppverify::decreases(n - 1 - i)
  {
    q = q + 1;
    i = i + 1;
  }
  return first(q, 1);
}
// CHECK-DAG: Verified: walked [backend=z3]

// Three elements from a + 2 run past a + 4.
int copied_past(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
{
  const int *q = a + 2;
  return first(q, 3);
}
// CHECK-DAG: error: verification failed: copied_past [{{.*}}::bounds@[[@LINE-2]]:3] (counterexample: a [ssa=a_0] [type=pointer] = {{[0-9]+}}, q [ssa=q_1] [type=pointer] = {{[0-9]+}};

void copied_write_past(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(a[0 : 4])
{
  int *q = a + 2;
  zero2(q, 3);
}
// CHECK-DAG: error: verification failed: copied_write_past [{{.*}}::bounds@[[@LINE-2]]:3]

// When c is true, a + 2 has two elements left; b has four.
void chosen_past(int *a, int *b, bool c)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(a[0 : 4], b[0 : 4])
{
  int *q = c ? a + 2 : b;
  zero2(q, 3);
}
// CHECK-DAG: error: verification failed: chosen_past [{{.*}}::bounds@[[@LINE-2]]:3] (counterexample: {{.*}}c [ssa=c_0] [type=bool] = true,

// The callee's contract does not say where its result points.
int from_unknown(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
{
  const int *q = somewhere(a, 4);
  return first(q, 3);
}
// CHECK-DAG: error: verification failed: from_unknown [{{.*}}::bounds@[[@LINE-2]]:3]

// The elements must start inside the object too: this result is one element
// before a, and the slice would end inside it.
[[cppverify::trusted]] const int *before(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1)
  cppverify::post(cppverify::result + 1 == a);
// CHECK-DAG: Trusted: before

int from_before(const int *a)
  cppverify::pre(cppverify::valid(a, 4))
{
  const int *q = before(a, 4);
  return first(q, 2);
}
// CHECK-DAG: error: verification failed: from_before [{{.*}}::bounds@[[@LINE-2]]:3] (counterexample: a [ssa=a_0] [type=pointer] = {{[0-9]+}}, q [ssa=q_1] [type=pointer] = {{[0-9]+}};

// A shorter walk leaves fewer elements than the call needs.
int walked_past(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 2 && n <= 100)
{
  const int *q = a;
  int i = 0;
  while (i < n - 1)
    cppverify::invariant(0 <= i && i <= n - 1 && q == a + i)
    cppverify::decreases(n - 1 - i)
  {
    q = q + 1;
    i = i + 1;
  }
  return first(q, 2);
}
// CHECK-DAG: error: verification failed: walked_past [{{.*}}::bounds@[[@LINE-2]]:3]
