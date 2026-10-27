// RUN: not %cpp-verify --timeout=20000 %s -- 2>&1 | FileCheck %s
//
// A choice is any value its axiom allows. A proof receives the axiom of
// every choose its facts apply, inside the unfoldings, postconditions, and
// induction hypotheses it assumes too, and a counterexample stands only
// where every choice it reads meets its axiom.

// In the unfolding of an inductive predicate.
cppverify::spec bool zero_chosen(int n)
  cppverify::inductive
{
  return cppverify::choose(k, 0, 1, k == 0) == 0;
}

cppverify::proof void zero_chosen_at_5()
  cppverify::post(zero_chosen(5))
{
}
// CHECK-DAG: Verified: zero_chosen_at_5

cppverify::spec bool odd_chosen(int n)
  cppverify::inductive
{
  return n >= 0 && cppverify::choose(k, 0, 2, k == n % 2) == 1;
}

cppverify::proof void odd_chosen_at_3()
  cppverify::post(odd_chosen(3))
{
}
// CHECK-DAG: Verified: odd_chosen_at_3

cppverify::proof void not_odd_chosen_at_4()
  cppverify::post(!odd_chosen(4))
{
}
// CHECK-DAG: Verified: not_odd_chosen_at_4

cppverify::proof void odd_chosen_at_4()
  cppverify::post(odd_chosen(4))
{
}
// CHECK-DAG: error: verification failed: odd_chosen_at_4 [{{.*}}::postcondition@{{.*}}[reason=counterexample]

// In the postcondition of a hidden spec.
cppverify::spec int parity(int n)
  cppverify::post(n < 0 || cppverify::result == cppverify::choose(k, 0, 2, k == n % 2))
{
  return n % 2;
}

cppverify::proof void parity_of_7(int x)
  cppverify::pre(x == 7)
  cppverify::post(parity(x) == 1)
{
  cppverify::hide(parity);
}
// CHECK-DAG: Verified: parity_of_7

cppverify::proof void parity_of_7_wrong(int x)
  cppverify::pre(x == 7)
  cppverify::post(parity(x) == 0)
{
  cppverify::hide(parity);
}
// CHECK-DAG: error: verification failed: parity_of_7_wrong [{{.*}}::postcondition@{{.*}}[reason=counterexample]

// A choose that reads memory is read where its application is.
cppverify::spec int low_bit(const int *a)
  cppverify::post(a[0] < 0 || a[0] > 1 || cppverify::result == cppverify::choose(k, 0, 2, k == a[0]))
{
  return a[0];
}

void set_one(int *a)
  cppverify::pre(cppverify::valid(a, 1))
  cppverify::modifies(a[0])
  cppverify::post(low_bit(a) == 1)
{
  cppverify::hide(low_bit);
  a[0] = 1;
}
// CHECK-DAG: Verified: set_one

void set_one_wrong(int *a)
  cppverify::pre(cppverify::valid(a, 1) && a[0] == 0)
  cppverify::modifies(a[0])
  cppverify::post(low_bit(a) == cppverify::old(a[0]))
{
  cppverify::hide(low_bit);
  a[0] = 1;
}
// CHECK-DAG: error: verification failed: set_one_wrong [{{.*}}::postcondition@{{.*}}[reason=counterexample]

cppverify::spec int low_bit_rec(const int *a, int n)
  cppverify::decreases(n)
  cppverify::post(a[0] < 0 || a[0] > 1 || cppverify::result == cppverify::choose(k, 0, 2, k == a[0]))
{
  return n <= 0 ? a[0] : low_bit_rec(a, n - 1);
}
// CHECK-DAG: Verified: spec decreases and post: low_bit_rec

cppverify::spec int low_bit_doubled(const int *a, int n)
  cppverify::post(a[0] < 0 || a[0] > 1 || cppverify::result == 2 * low_bit_rec(a, 3 * n + 1))
{
  return 2 * a[0];
}
// CHECK-DAG: Verified: spec post: low_bit_doubled

// An axiom that applies its own choice under a quantifier holds for that
// application outside the quantifier.
cppverify::spec int some_max(const int *a, int n)
{
  return cppverify::choose(i, 0, n, cppverify::forall(k, 0, n, a[k] <= a[i]));
}

int max_at(const int *a, int n, int m)
  cppverify::pre(cppverify::valid(a, n) && 1 <= n && n <= 1000 && 0 <= m && m < n)
  cppverify::pre(cppverify::forall(k, 0, n, a[k] <= a[m]))
  cppverify::post(cppverify::result == a[some_max(a, n)])
{
  return a[m];
}
// CHECK-DAG: Verified: max_at

int max_index_wrong(const int *a, int n, int m)
  cppverify::pre(cppverify::valid(a, n) && 1 <= n && n <= 1000 && 0 <= m && m < n)
  cppverify::pre(cppverify::forall(k, 0, n, a[k] <= a[m]))
  cppverify::post(cppverify::result == some_max(a, n))
{
  return m;
}
// CHECK-DAG: error: verification failed: max_index_wrong [{{.*}}::postcondition@{{.*}}[reason=counterexample]

// In the induction hypothesis of a recursive spec.
cppverify::spec int bit(int n)
  cppverify::decreases(n)
  cppverify::post(n < 0 || cppverify::result == cppverify::choose(k, 0, 2, k == n % 2))
{
  return n <= 1 ? n : bit(n - 2);
}
// CHECK-DAG: Verified: spec decreases and post: bit

// In the postcondition of a spec a post check applies, at an argument no
// induction reaches.
cppverify::spec int doubled(int n)
  cppverify::post(n < 0 || cppverify::result == 2 * bit(3 * n + 1))
{
  return 2 * ((3 * n + 1) % 2);
}
// CHECK-DAG: Verified: spec post: doubled

// In the induction hypothesis a proof block states.
cppverify::spec int bit_block(int n)
  cppverify::decreases(n)
  cppverify::post(n < 0 || cppverify::result == cppverify::choose(k, 0, 2, k == n % 2)) by {
    if (n > 1) cppverify::check(bit_block(n - 2) == bit_block(n - 2));
  }
{
  return n <= 1 ? n : cppverify::choose(j, 0, 2, j == bit_block(n - 2));
}
// CHECK-DAG: Verified: spec decreases and post: bit_block

// The hypothesis also holds at an application inside the body of a choose,
// so no proof block is needed.
cppverify::spec int bit_unblocked(int n)
  cppverify::decreases(n)
  cppverify::post(n < 0 || cppverify::result == cppverify::choose(k, 0, 2, k == n % 2))
{
  return n <= 1 ? n : cppverify::choose(j, 0, 2, j == bit_unblocked(n - 2));
}
// CHECK-DAG: Verified: spec decreases and post: bit_unblocked

// In the definition instances refinement gives, where only the check of the
// model's choices sees them.
cppverify::spec int parity_sum(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : parity_sum(n - 1) + cppverify::choose(k, 0, 2, k == n % 2);
}

cppverify::proof void parity_sum_5(int x)
  cppverify::pre(x == 5)
  cppverify::post(parity_sum(x) == 3)
{
}
// CHECK-DAG: Verified: parity_sum_5

cppverify::proof void parity_sum_5_wrong(int x)
  cppverify::pre(x == 5)
  cppverify::post(parity_sum(x) == 2)
{
}
// CHECK-DAG: error: verification failed: parity_sum_5_wrong [{{.*}}::postcondition@{{.*}}[reason=counterexample]
