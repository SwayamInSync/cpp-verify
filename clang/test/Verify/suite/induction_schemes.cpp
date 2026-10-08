// RUN: not %cpp-verify --timeout=10000 %s 2>&1 | FileCheck %s \
// RUN:   --implicit-check-not='Verified: loopy_zero'
// RUN: not %cpp-verify --timeout=10000 --backend=bmc --unroll=1 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --timeout=10000 --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// When no finite unfolding settles a claim about a recursive spec, the
// verifier tries well-founded inductions over it: the claim at every value
// smaller in a measure (the decrease relation of termination checks, which
// is well-founded by itself), all else fixed. The measure is a recursive
// spec's own, at the application the claim makes, and the hypothesis is
// given at the values its recursion reaches: through other members of its
// recursion group and under quantifiers too. The claim is the function's
// own, without the theorems added to it, so the hypothesis has no premise
// the solver cannot meet.

#include <cppverify.h>
using namespace cppverify;

cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// The hypothesis at n - 1 and n - 2, as fibo recurses.
cppverify::proof void grows(int n)
  cppverify::pre(n >= 3)
  cppverify::post(fibo(n) >= n - 1)
{
}
// CHECK-DAG: Verified: grows [backend=z3] [by induction following fibo]
// BMC-DAG: Verified: grows [backend=bmc, bound=0] [by induction following fibo]
// JSON-DAG: "function":"grows"{{.*}}"induction":"following fibo"

// Over a sequence: the hypothesis at the shorter sequence the recursion
// reaches.
cppverify::spec int total(seq s)
  cppverify::decreases(s.len())
{
  return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}

cppverify::proof void total_nonneg(seq s)
  cppverify::pre(cppverify::forall(k, 0, s.len(), s[k] >= 0))
  cppverify::post(total(s) >= 0)
{
}
// CHECK-DAG: Verified: total_nonneg [backend=z3] [by induction following total]

// Through another member of a recursion group: even reaches even(n - 2)
// through odd.
cppverify::spec bool odd(int n);
cppverify::spec bool even(int n) cppverify::decreases(n) { return n <= 0 ? true : odd(n - 1); }
cppverify::spec bool odd(int n) cppverify::decreases(n) { return n <= 0 ? false : even(n - 1); }

cppverify::proof void even_mod(int n)
  cppverify::pre(n >= 0)
  cppverify::post(even(n) == (n % 2 == 0))
{
}
// CHECK-DAG: Verified: even_mod

// Under a quantifier: the hypothesis for every k the forall ranges over.
cppverify::spec bool good(int n) cppverify::decreases(n) { return n <= 0 || cppverify::forall(k, 0, n, good(k)); }

cppverify::proof void all_good(int n)
  cppverify::post(good(n))
{
}
// CHECK-DAG: Verified: all_good

// False claims still fail, with counterexamples checked against the
// definitions: fibo(1) == fibo(2), odd(1) holds.
cppverify::proof void strictly_grows(int n)
  cppverify::pre(n >= 1)
  cppverify::post(fibo(n) < fibo(n + 1))
{
}
// CHECK-DAG: error: verification failed: strictly_grows {{.*}}[reason=counterexample]

cppverify::proof void even_wrong(int n)
  cppverify::pre(n >= 0)
  cppverify::post(even(n) == (n % 2 == 1))
{
}
// CHECK-DAG: error: verification failed: even_wrong {{.*}}[reason=counterexample]

cppverify::proof void total_positive(seq s)
  cppverify::pre(cppverify::forall(k, 0, s.len(), s[k] >= 0))
  cppverify::post(total(s) > 0)
{
}
// CHECK-DAG: error: verification failed: total_positive {{.*}}[reason=counterexample]

// A spec whose termination fails gives no well-founded recursion: its
// recursive call is at the same value, which the hypothesis's decrease
// excludes, and nothing that rests on its definition is established.
cppverify::spec int loopy(int n) cppverify::decreases(n) { return n <= 0 ? 0 : loopy(n); }

cppverify::proof void loopy_zero(int n)
  cppverify::post(loopy(n) == 0)
{
}
// CHECK-DAG: error: spec decreases failed: loopy
// CHECK-DAG: Unresolved: loopy_zero

// The recursion changes the accumulator, so a hypothesis at a fixed
// accumulator does not apply: the claim needs a stronger statement, which
// no induction finds. The message says what was tried, and a body to start
// from.
cppverify::spec int accumulate(int n, int acc)
  cppverify::decreases(n)
{
  return n <= 0 ? acc : accumulate(n - 1, acc + n);
}

cppverify::spec int sum(int n) cppverify::decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }

cppverify::proof void accumulated(int n)
  cppverify::pre(n >= 0 && n <= 25000)
  cppverify::post(accumulate(n, 0) == sum(n))
{
}
// CHECK-DAG: Unresolved: accumulated [backend=z3] [reason=spec.fuel] {{.*}}induction following accumulate and induction following sum and induction on n did not prove it; a proof by induction following sum could start from the body 'if (n > 0 && n - 1 >= 0 && n - 1 <= 25000) { accumulated(n - 1); }', with cppverify::decreases(n)
