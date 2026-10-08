// RUN: not %cpp-verify %s 2>&1 | FileCheck %s \
// RUN:   --implicit-check-not=monotonicity \
// RUN:   --implicit-check-not="case analysis" \
// RUN:   --implicit-check-not=introduction
// RUN: not %cpp-verify --solver-rlimit=1 %S/Inputs/inductive_unproved.cpp 2>&1 \
// RUN:   | FileCheck %s --check-prefix=UNPROVED
//
// Proofs use an inductive predicate through its unfolding P(x) == F(x) only
// once generated proofs of its rules hold: monotonicity of its step-indexed
// definition, case analysis, and introduction. Each shape of body below has
// its rules proved.

#include <cppverify.h>
using cppverify::valid;

// A bounded universal premise: the introduction height is the largest over
// the range, computed by a generated recursive spec.
cppverify::spec bool good(int n) cppverify::inductive {
  return n == 0 || (n > 0 && cppverify::forall(k, 0, n, good(k)));
}
// CHECK-DAG: Verified: inductive predicate: good
// CHECK-DAG: Verified: spec decreases and post: good.bound

cppverify::proof void two_is_good() cppverify::post(good(2)) {
  cppverify::check(good(0));
  cppverify::check(good(1));
}
// CHECK-DAG: Verified: two_is_good

// Two premises under an existential.
cppverify::spec bool ones(int n) cppverify::inductive {
  return n == 1 || cppverify::exists(a, 1, n, ones(a) && ones(n - a));
}
// CHECK-DAG: Verified: inductive predicate: ones

cppverify::proof void three_ones() cppverify::post(ones(3)) {
  cppverify::check(ones(1));
  cppverify::check(ones(2));
}
// CHECK-DAG: Verified: three_ones

// An existential above a universal.
cppverify::spec bool ladder(int n) cppverify::inductive {
  return n == 0 ||
         cppverify::exists(m, 0, n, m + 1 == n && cppverify::forall(k, 0, m + 1, ladder(k)));
}
// CHECK-DAG: Verified: inductive predicate: ladder
// CHECK-DAG: Verified: spec decreases and post: ladder.bound

// A body of if and else.
cppverify::spec bool even2(int n) cppverify::inductive {
  if (n == 0)
    return true;
  return n >= 2 && even2(n - 2);
}
// CHECK-DAG: Verified: inductive predicate: even2

// Predicates defined through each other form one group.
cppverify::spec bool ev(int n);
cppverify::spec bool od(int n) cppverify::inductive { return n == 1 || ev(n - 1); }
cppverify::spec bool ev(int n) cppverify::inductive { return n == 0 || od(n - 1); }
// CHECK-DAG: Verified: inductive predicate: od
// CHECK-DAG: Verified: inductive predicate: ev

cppverify::proof void three_is_odd() cppverify::post(od(3)) {
  cppverify::check(ev(0));
  cppverify::check(od(1));
  cppverify::check(ev(2));
}
// CHECK-DAG: Verified: three_is_odd

// Reading memory: j is reached from i by following next. The rules quantify
// over i only, since every application passes next, n, and j unchanged.
cppverify::spec bool linked(const int *next, int n, int i, int j)
  cppverify::inductive
  cppverify::reads(next, n)
{
  return i == j || (0 <= i && i < n && linked(next, n, next[i], j));
}
// CHECK-DAG: Verified: inductive predicate: linked
// CHECK-DAG: Verified: spec reads: linked

void follow(const int *next, int n)
  cppverify::pre(valid(next, n) && n == 3 && next[0] == 2 && next[2] == 1)
{
  cppverify::check(linked(next, n, 1, 1));
  cppverify::check(linked(next, n, 2, 1));
  cppverify::check(linked(next, n, 0, 1));
}
// CHECK-DAG: Verified: follow

// A pointer that changes along the derivation: a list segment.
struct node {
  int value;
  node *next;
};

cppverify::spec bool segment(const node *p, const node *q) cppverify::inductive {
  return p == q || (p != nullptr && segment(p->next, q));
}
// CHECK-DAG: Verified: inductive predicate: segment

void two_nodes(node *a, node *b)
  cppverify::pre(a != nullptr && b != nullptr && a->next == b && b->next == nullptr)
{
  cppverify::check(segment(nullptr, nullptr));
  cppverify::check(segment(b, nullptr));
  cppverify::check(segment(a, nullptr));
}
// CHECK-DAG: Verified: two_nodes

void not_empty(node *a)
  cppverify::pre(a != nullptr)
{
  cppverify::check(!segment(a, a));
}
// CHECK-DAG: error: verification failed: not_empty {{.*}}[reason=counterexample]

// A rule proof that fails is reported, and the predicate with it.
// UNPROVED-DAG: Unresolved: inductive predicate: reach [reason=spec.inductive] (its rules are not established: {{.*}})
// UNPROVED-DAG: Unresolved: reach (monotonicity)
