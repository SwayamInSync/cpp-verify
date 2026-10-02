// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A counterexample is checked even when its model gives a bounded quantifier a
// huge range. Where that is not possible the result says so instead of
// reporting an unchecked failure.

// Whatever length the solver first picks, a counterexample with a range small
// enough to check exists and is the one reported.
int first_positive(const int *p, int n)
  pre(n >= 1 && p != nullptr)
  pre(forall(i, 0, n, p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// Two million elements, but the body reads the binder only through p[i]: the
// model sets a few cells and the rest share one value, so it is checked.
int first_positive_long(const int *p, int n)
  pre(n >= 2000000 && p != nullptr)
  pre(forall(i, 0, n, p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// The instance at i == 0 decides the postcondition without expanding it.
void writes_first(int *p, int n)
  pre(n >= 2000000 && p != nullptr)
  pre(p[0] == 0)
  modifies(*p)
  post(forall(i, 0, n, i < 0 || p[i] == old(p[i])))
{
  p[0] = 1;
}

// The body also compares the index itself. The comparison is affine, so its
// truth changes only at its root and the range splits into a few intervals.
int first_positive_indexed(const int *p, int n)
  pre(n >= 2000000 && p != nullptr)
  pre(forall(i, 0, n, i < 0 || p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// Contract arithmetic is exact, so a nonlinear comparison is a polynomial
// whose sign changes are found exactly.
int first_positive_squared(const int *p, int n)
  pre(n >= 2000000 && n <= 3000000 && p != nullptr)
  pre(forall(i, 0, n, i * i < 0 || p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// So is one through a conversion to a machine type the value fits.
int first_positive_squared_wide(const int *p, int n)
  pre(n >= 2000000 && n <= 3000000 && p != nullptr)
  pre(forall(i, 0, n, (long long)i * i < 0 || p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// A bitwise use of the index would need two million instances checked one by
// one, and no shorter counterexample exists.
int first_positive_bitwise(const int *p, int n)
  pre(n >= 2000000 && n <= 3000000 && p != nullptr)
  pre(forall(i, 0, n, (i ^ 1431655765) < 0 || p[i] >= 0))
  post(result > 0)
{
  return p[0];
}

// CHECK-DAG: verification failed: first_positive_squared_wide [{{.*}}::postcondition@
// CHECK-DAG: verification failed: first_positive [{{.*}}::postcondition@
// CHECK-DAG: verification failed: first_positive_long [{{.*}}::postcondition@{{.*}}n [ssa=n_0] [type=i32] = 2000000
// CHECK-DAG: verification failed: writes_first [{{.*}}::postcondition@
// CHECK-DAG: verification failed: first_positive_indexed [{{.*}}::postcondition@
// CHECK-DAG: verification failed: first_positive_squared [{{.*}}::postcondition@
// CHECK-DAG: Unresolved: first_positive_bitwise [backend=z3] [reason=counterexample.unchecked]
// CHECK-DAG: a quantifier range of {{[0-9]+}} values is too wide to expand

// JSON-DAG: "function":"first_positive_bitwise"{{.*}}"reason":"counterexample.unchecked"
