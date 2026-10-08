// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --int-encoding=bitvector %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// At the default fuel a recursive spec applied at a symbolic argument keeps
// an opaque application, which a solver model may interpret arbitrarily. A
// satisfying model is reported as a counterexample only when it satisfies the
// query under the true definitions; otherwise the definitions are added at the
// disputed points and the query is solved again.

cppverify::spec int triangle(int n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return n + triangle(n - 1);
}

// Previously a failure with a model in which triangle(n - 1) was arbitrary.
int closed_form(int n)
  cppverify::pre(0 <= n && n <= 6)
  cppverify::post(cppverify::result == triangle(n))
{
  return n * (n + 1) / 2;
}

// A real counterexample survives the check against the definition.
int closed_form_wrong(int n)
  cppverify::pre(0 <= n && n <= 6)
  cppverify::post(cppverify::result == triangle(n))
{
  return n * (n - 1) / 2;
}

// No bound on n: refinement cannot settle every argument, and a model that
// only the missing unfolding makes fail is not reported as a counterexample.
// The property is inductive, so strong induction on n proves it.
void unbounded(int n)
  cppverify::pre(n >= 0)
  cppverify::post(triangle(n) >= 0)
{
}

// True, but the property at smaller n says nothing about n.
void not_inductive(int n)
  cppverify::pre(n >= 0)
  cppverify::post(triangle(n) != 7)
{
}

// CHECK-DAG: Verified: closed_form [
// CHECK-DAG: error: verification failed: closed_form_wrong [{{.*}}::postcondition@{{.*}}counterexample: {{.*}}n [ssa=n_0] [type=i32] = {{[1-6]}}
// CHECK-DAG: Verified: unbounded [backend=z3]
// CHECK-DAG: Unresolved: not_inductive [backend=z3] [reason=spec.fuel]

// JSON-DAG: "function":"not_inductive"{{.*}}"reason":"spec.fuel"
