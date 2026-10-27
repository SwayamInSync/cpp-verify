// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
//
// ++p, --p, p++, p--, p += n, and p -= n as statements: each is the
// assignment p = p + 1 (or p - 1, p + n, p - n), with the checks of that
// step: the result stays in the object p addresses, one past its end
// included. Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

int sum(const int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 100)
  cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] <= 10))
  cv::post(0 <= cv::result && cv::result <= 10 * n)
{
  int s = 0;
  int i = 0;
  for (const int *q = a; q != a + n; ++q)
    cv::invariant(0 <= i && i <= n && q == a + i && 0 <= s && s <= 10 * i)
    cv::decreases(n - i)
  {
    s = s + *q;
    i = i + 1;
  }
  return s;
}
// CHECK-DAG: Verified: sum [backend=z3]

int sum_past_end(const int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 100)
  cv::post(true)
{
  int s = 0;
  int i = 0;
  for (const int *q = a; q != a + n + 1; q++)
    cv::invariant(0 <= i && i <= n + 1 && q == a + i)
    cv::decreases(n + 1 - i)
  {
    s = *q;
    i = i + 1;
  }
  return s;
}
// CHECK-DAG: error: verification failed: sum_past_end [{{.*}}[reason=counterexample]

// A step that leaves the object fails where it is made, without an access.
int there_and_back(const int *a, int n)
  cv::pre(cv::valid(a, n) && 2 <= n && n <= 100)
  cv::post(cv::result == a[0])
{
  const int *q = a;
  q += 2;
  q -= 2;
  q++;
  q--;
  return *q;
}
// CHECK-DAG: Verified: there_and_back [backend=z3]

int too_far(const int *a, int n)
  cv::pre(cv::valid(a, n) && 1 <= n && n <= 100)
  cv::post(true)
{
  const int *q = a;
  q += 2;
  q -= 2;
  return *q;
}
// CHECK-DAG: error: verification failed: too_far [{{.*}}@[[@LINE-4]]:{{.*}}n [ssa=n_0] [type=i32] = 1{{[,;]}}{{.*}}[reason=counterexample]

int before_start(const int *a, int n)
  cv::pre(cv::valid(a, n) && 1 <= n && n <= 100)
  cv::post(true)
{
  const int *q = a;
  --q;
  ++q;
  return *q;
}
// CHECK-DAG: error: verification failed: before_start [{{.*}}@[[@LINE-4]]:{{.*}}[reason=counterexample]

// Stepping a null pointer is undefined.
int *step_null(int *p)
  cv::post(true)
{
  p += 1;
  return p;
}
// CHECK-DAG: error: verification failed: step_null [{{.*}}::bounds@[[@LINE-3]]:{{.*}}p [ssa=p_0] [type=pointer] = 0{{.*}}[reason=counterexample]

// A parameter may be stepped too; contracts read its entry value.
void zero(int *p, int n)
  cv::pre(cv::valid(p, n) && 0 <= n && n <= 100)
  cv::modifies(p[0 : n])
  cv::post(cv::forall(k, 0, n, p[k] == 0))
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && p == cv::old(p) + i)
    cv::invariant(cv::forall(k, 0, i, cv::old(p)[k] == 0))
    cv::modifies(cv::old(p)[0 : i])
    cv::decreases(n - i)
  {
    *p = 0;
    p++;
    i++;
  }
}
// CHECK-DAG: Verified: zero [backend=z3]

void zero_wrong(int *p, int n)
  cv::pre(cv::valid(p, n) && 0 <= n && n <= 100)
  cv::modifies(p[0 : n])
  cv::post(cv::forall(k, 0, n, p[k] == 0))
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && p == cv::old(p) + i)
    cv::invariant(cv::forall(k, 0, i, cv::old(p)[k] == 0))
    cv::modifies(cv::old(p)[0 : i])
    cv::decreases(n - i)
  {
    p++;
    *p = 0;
    i++;
  }
}
// CHECK-DAG: error: verification failed: zero_wrong [{{.*}}[reason=counterexample]

// Steps are whole elements of the pointee.
struct Pair {
  int key;
  int value;
};

int count_keys(const Pair *ps, int n, int key)
  cv::pre(cv::valid(ps, n) && 0 <= n && n <= 100)
  cv::post(0 <= cv::result && cv::result <= n)
{
  int c = 0;
  int i = 0;
  const Pair *q = ps;
  while (i < n)
    cv::invariant(0 <= i && i <= n && q == ps + i && 0 <= c && c <= i)
    cv::decreases(n - i)
  {
    if (q->key == key)
      c = c + 1;
    q += 1;
    i = i + 1;
  }
  return c;
}
// CHECK-DAG: Verified: count_keys [backend=z3]

// A pointer into a record's array member is bounded by the array.
struct Ring {
  int buf[8];
  int head;
};

int ring_total(const Ring *r)
  cv::pre(r != nullptr)
  cv::pre(cv::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 10))
  cv::post(0 <= cv::result && cv::result <= 80)
{
  int s = 0;
  int i = 0;
  for (const int *q = r->buf; q != r->buf + 8; ++q)
    cv::invariant(0 <= i && i <= 8 && q == r->buf + i && 0 <= s && s <= 10 * i)
    cv::decreases(8 - i)
  {
    s = s + *q;
    i = i + 1;
  }
  return s;
}
// CHECK-DAG: Verified: ring_total [backend=z3]

int ring_past(const Ring *r)
  cv::pre(r != nullptr)
  cv::post(true)
{
  const int *q = r->buf + 7;
  ++q;
  ++q;
  return 0;
}
// CHECK-DAG: error: verification failed: ring_past [{{.*}}@[[@LINE-3]]:{{.*}}[reason=counterexample]

// Unsupported: stepping a pointer to dynamic storage, and the value of a
// step in an expression.
int step_new()
  cv::post(true)
{
  int *p = new int(1);
  p++;
  return 0;
}
// CHECK-DAG: pointer_steps.cpp:[[@LINE-3]]:3: error: step_new: arithmetic on dynamic-storage pointers is unsupported

// BMC: Verified: there_and_back [backend=bmc, bound=0]
// BMC: error: verification failed: too_far
// BMC: error: verification failed: before_start
// BMC: error: verification failed: ring_past

// The step is checked, then assigned.
// VCR-LABEL: fn there_and_back
// VCR:         assign q
// VCR-NEXT:      a
// VCR-NEXT:    assert bounds
// VCR:         assign q
// VCR-NEXT:      +
// VCR-NEXT:        q
// VCR-NEXT:        *
// VCR-NEXT:          cast
// VCR-NEXT:            2
// VCR-NEXT:          4
