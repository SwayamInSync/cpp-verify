// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
//
// forall(k, body) and exists(k, body) range over all mathematical integers.
// A counterexample is certified when the body depends on the binder through
// memory reads and comparisons: it is constant beyond them, so finitely many
// values decide it.

cppverify::spec int sq(int x) { return x * x; }

cppverify::proof void sq_nonnegative_all()
  cppverify::post(cppverify::forall(k, sq(k) >= 0))
{
}
// CHECK-DAG: Verified: sq_nonnegative_all

void uses_lemma(int a)
{
  cppverify::ghost { sq_nonnegative_all(); }
  cppverify::check(sq(a + 7) >= 0);
}
// CHECK-DAG: Verified: uses_lemma

void false_over_integers()
{
  cppverify::check(cppverify::forall(k, 2 * k + 1 > 0));
}
// CHECK-DAG: error: verification failed: false_over_integers [{{.*}}::assertion@{{.*}}[reason=counterexample]

void true_over_range()
{
  cppverify::check(cppverify::forall(k, 0, 10, 2 * k + 1 > 0));
}
// CHECK-DAG: Verified: true_over_range

void square_above(int n)
  cppverify::pre(n >= 0 && n < 1000)
{
  cppverify::check(cppverify::exists(k, k * k >= n));
}
// CHECK-DAG: Verified: square_above

cppverify::spec bool valid(int *p, int n) { return true; }

void cell_claim(int *p)
  cppverify::pre(valid(p, 4) && p[0] == 3 && p[1] == 4)
{
  cppverify::check(cppverify::forall(k, k < 0 || k > 1 || p[k] == 3));
}
// CHECK-DAG: error: verification failed: cell_claim [{{.*}}::assertion@{{.*}}[reason=counterexample]

void cell_claim_holds(int *p)
  cppverify::pre(valid(p, 4) && p[0] == 3)
{
  cppverify::check(cppverify::forall(k, k != 0 || p[k] == 3));
}
// CHECK-DAG: Verified: cell_claim_holds

// The unbounded quantifier has its body as its only child.
// VC-LABEL: vc false_over_integers
// VC: forall __quant_{{[0-9]+}}_{{.*}} : bool
// VC-NEXT: true : bool
// VC-NEXT: forall __quant_{{[0-9]+}}_{{.*}} : bool
// VC-NEXT: > : bool
