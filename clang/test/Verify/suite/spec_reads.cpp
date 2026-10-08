// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --check-ub --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --check-ub --lower-only --obligation-out=%t.cpv %s
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY
//
// reads(p, n) declares the cells p[0..n) a heap-reading spec depends on. It
// is checked against the body, and a write outside those cells leaves every
// application unchanged without unfolding the definition.

cppverify::spec bool valid(const int *p, int n) { return true; }
cppverify::spec bool valid(int *p, int n) { return true; }

cppverify::spec int sum(const int *p, int n)
  cppverify::reads(p, n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return sum(p, n - 1) + p[n - 1];
}
// CHECK-DAG: Verified: spec reads: sum
// CHECK-DAG: Verified: spec decreases: sum

void write_after(int *p, int n)
  cppverify::pre(n >= 0 && n <= 100 && valid(p, n + 1))
  cppverify::modifies(p[n])
  cppverify::post(sum(p, n) == cppverify::old(sum(p, n)))
{
  p[n] = 7;
}
// CHECK-DAG: Verified: write_after
// The frames are ordinary assumptions of the archived query.
// REPLAY-DAG: Verified: write_after

// Each store is framed separately, through both branches.
void write_around(int *p, int n, bool front)
  cppverify::pre(n >= 0 && n <= 100 && valid(p, n + 2))
  cppverify::modifies(p[n], p[n + 1])
  cppverify::post(sum(p, n) == cppverify::old(sum(p, n)))
{
  if (front)
    p[n] = 1;
  else
    p[n + 1] = 2;
  p[n + 1] = 3;
}
// CHECK-DAG: Verified: write_around

// Under a quantifier, the frame holds at every bound value.
void write_after_prefixes(int *p, int n)
  cppverify::pre(n >= 0 && n <= 100 && valid(p, n + 1))
  cppverify::modifies(p[n])
  cppverify::post(cppverify::forall(j, 0, n + 1, sum(p, j) == cppverify::old(sum(p, j))))
{
  p[n] = 7;
}
// CHECK-DAG: Verified: write_after_prefixes

void write_inside(int *p, int n)
  cppverify::pre(n >= 1 && n <= 100 && valid(p, n))
  cppverify::pre(p[0] != 7)
  cppverify::modifies(p[0])
  cppverify::post(sum(p, n) == cppverify::old(sum(p, n)))
{
  p[0] = 7;
}
// CHECK-DAG: verification failed: write_inside

// A reads clause that misses a cell the body loads is rejected, and a proof
// that relied on its frame proves nothing.
cppverify::spec int sum_short(const int *p, int n)
  cppverify::reads(p, n - 1)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return sum_short(p, n - 1) + p[n - 1];
}
// CHECK-DAG: error: spec reads failed: sum_short {{.*}}[reason=counterexample]
// REPLAY-DAG: verification failed: sum_short.reads [{{.*}}::reads::frame@

void write_last(int *p, int n)
  cppverify::pre(n >= 1 && n <= 100 && valid(p, n))
  cppverify::modifies(p[n - 1])
  cppverify::post(sum_short(p, n) == cppverify::old(sum_short(p, n)))
{
  p[n - 1] = 7;
}
// CHECK-DAG: Unresolved: write_last {{.*}}[reason=spec.reads] (relies on the reads clause of sum_short, which is not established)
// JSON-DAG: "function":"write_last"{{.*}}"reason":"spec.reads"{{.*}}"status":"unresolved"

// A spec reads what its heap-reading callees read.
cppverify::spec int sum_prefix(const int *p, int n, int k)
  cppverify::reads(p, n)
{
  if (k <= 0 || k > n)
    return 0;
  return sum(p, k);
}
// CHECK-DAG: Verified: spec reads: sum_prefix

cppverify::spec int sum_beyond(const int *p, int n)
  cppverify::reads(p, n)
{
  return sum(p, n + 1);
}
// CHECK-DAG: error: spec reads failed: sum_beyond {{.*}}[reason=counterexample]

cppverify::spec int first_unframed(const int *p)
{
  return p[0];
}

cppverify::spec int calls_unframed(const int *p)
  cppverify::reads(p, 1)
{
  return first_unframed(p);
}
// CHECK-DAG: error: spec reads failed: calls_unframed (calls first_unframed, which reads the heap without a reads clause)

// A load under a quantifier is in range for every binder value.
cppverify::spec bool all_positive(const int *p, int n)
  cppverify::reads(p, n)
{
  return cppverify::forall(i, 0, n, p[i] > 0);
}
// CHECK-DAG: Verified: spec reads: all_positive

cppverify::spec bool all_positive_past(const int *p, int n)
  cppverify::reads(p, n)
{
  return cppverify::forall(i, 0, n + 1, p[i] > 0);
}
// CHECK-DAG: error: spec reads failed: all_positive_past {{.*}}[reason=counterexample]

// A spec that need not terminate has no definition to frame.
cppverify::spec int sum_diverges(const int *p, int n)
  cppverify::reads(p, n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return sum_diverges(p, n) + p[n - 1];
}
// CHECK-DAG: error: spec decreases failed: sum_diverges {{.*}}[reason=counterexample]

void write_after_diverging(int *p, int n)
  cppverify::pre(n >= 0 && n <= 100 && valid(p, n + 1))
  cppverify::modifies(p[n])
  cppverify::post(sum_diverges(p, n) == cppverify::old(sum_diverges(p, n)))
{
  p[n] = 7;
}
// CHECK-DAG: Unresolved: write_after_diverging {{.*}}[reason=spec.termination]
