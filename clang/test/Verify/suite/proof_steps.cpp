// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=BMC
//
// contract_assert(c) by { proof } proves c from a ghost proof whose facts go
// no further: only c holds afterwards. calc { e0; op { proof } e1; ... }
// proves each step that way and concludes e0 R en, where R is == when every
// step is ==, < or > when some step is strict, else <= or >=.

cppverify::spec int sq(int x) { return x * x; }

cppverify::proof void sq_monotone(int a, int b)
  cppverify::pre(0 <= a && a <= b)
  cppverify::post(sq(a) <= sq(b))
{
}

cppverify::proof void sq_nonnegative(int a)
  cppverify::post(sq(a) >= 0)
{
}

int bigger(int a, int b)
  cppverify::pre(0 <= a && a <= b && b <= 1000)
  cppverify::post(cppverify::result == 1)
{
  cppverify::check(sq(a) <= sq(b)) by {
    sq_monotone(a, b);
  }
  return 1;
}
// CHECK-DAG: Verified: bigger

// With sq hidden, only the lemma states sq(a) >= 0, and its fact stays in
// the proof that used it.
void proved_with_lemma(int a)
{
  cppverify::ghost { cppverify::hide(sq); }
  cppverify::check(sq(a) >= 0) by {
    sq_nonnegative(a);
  }
}
// CHECK-DAG: Verified: proved_with_lemma

void lemma_fact_is_local(int a)
{
  cppverify::ghost { cppverify::hide(sq); }
  cppverify::check(true) by {
    sq_nonnegative(a);
  }
  cppverify::check(sq(a) >= 0);
}
// CHECK-DAG: Unresolved: lemma_fact_is_local {{.*}}[reason=spec.hidden]

void wrong_claim(int a, int b)
  cppverify::pre(0 <= a && a <= b && b <= 1000)
{
  cppverify::check(sq(b) <= sq(a)) by {
    sq_monotone(a, b);
  }
}
// CHECK-DAG: error: verification failed: wrong_claim [{{.*}}::assertion@[[@LINE-4]]:3]

// A lemma's precondition is checked where the proof calls it.
void lemma_outside_its_domain(int a, int b)
  cppverify::pre(0 <= b && b < a && a <= 1000)
{
  cppverify::check(true) by {
    sq_monotone(a, b);
  }
}
// CHECK-DAG: error: verification failed: lemma_outside_its_domain [{{.*}}::precondition@[[@LINE-3]]:5]

void ghost_local_in_proof(int a)
  cppverify::pre(0 <= a && a <= 1000)
{
  cppverify::check(sq(a) >= 0) by {
    int t = sq(a);
    cppverify::check(t == a * a);
  }
}
// CHECK-DAG: Verified: ghost_local_in_proof

// Each iteration proves its own instance.
void in_loop(int n)
  cppverify::pre(0 <= n && n <= 100)
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    cppverify::check(sq(i) <= sq(i + 1)) by {
      sq_monotone(i, i + 1);
    }
  }
}
// CHECK-DAG: Verified: in_loop

void chain(int a, int b, int c)
  cppverify::pre(0 <= a && a <= b && b < c && c <= 1000)
{
  cppverify::calc {
    sq(a);
    <= { sq_monotone(a, b); }
    sq(b);
    <= { sq_monotone(b, c); }
    sq(c);
    == c * c;
  }
  cppverify::check(sq(a) <= c * c);
}
// CHECK-DAG: Verified: chain

void strict_chain(int a, int b)
  cppverify::pre(0 <= a && a < b && b <= 1000)
{
  cppverify::calc {
    a;
    < b;
    <= b + 1;
  }
  cppverify::check(a < b + 1);
}
// CHECK-DAG: Verified: strict_chain

void descending_chain(int a, int b)
  cppverify::pre(0 <= b && b <= a && a <= 1000)
{
  cppverify::calc {
    sq(a);
    >= { sq_monotone(b, a); }
    sq(b);
    >= { sq_nonnegative(b); }
    0;
  }
}
// CHECK-DAG: Verified: descending_chain

void wrong_step(int a, int b)
  cppverify::pre(0 <= a && a <= b && b <= 1000)
{
  cppverify::calc {
    sq(b);
    <= { sq_monotone(a, b); }
    sq(a);
  }
}
// CHECK-DAG: error: verification failed: wrong_step [{{.*}}::assertion@[[@LINE-4]]:5]

// The chain's steps are local; its conclusion is not.
void step_is_local(int a)
{
  cppverify::ghost { cppverify::hide(sq); }
  cppverify::calc {
    sq(a);
    >= { sq_nonnegative(a); }
    0;
  }
  cppverify::check(sq(a) >= 0);
  cppverify::check(sq(a) + 1 > 0);
}
// CHECK-DAG: Verified: step_is_local

// BMC-DAG: Verified: bigger
// BMC-DAG: error: verification failed: wrong_claim
// BMC-DAG: Verified: chain
// BMC-DAG: error: verification failed: wrong_step
