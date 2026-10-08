// RUN: not %cpp-verify --timeout=20000 %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VC
// RUN: not %cpp-verify --obligation-out=%t.obligations %s > /dev/null 2>&1
// RUN: not %cpp-verify --timeout=20000 --obligation-in=%t.obligations 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY
//
// cppverify::set, multiset, and map range over all mathematical integers and
// may be infinite. A multiset counts each value at least zero times; a key
// outside a map's domain maps to 0. Collections are equal when they have the
// same members, counts, or domain and values.

#include <cppverify.h>
using cppverify::map;
using cppverify::multiset;
using cppverify::set;

cppverify::proof void sets(set a, int x, int y)
  cppverify::pre(x != y)
{
  cppverify::check(a.insert(x).contains(x));
  cppverify::check(!a.remove(x).contains(x));
  cppverify::check(a.insert(x).remove(y).contains(x));
  cppverify::check(a.unite(cppverify::set_empty().insert(y)).contains(y));
  cppverify::check(a.intersect(cppverify::set_empty()) == cppverify::set_empty());
  cppverify::check(a.difference(a).subset_of(cppverify::set_empty()));
  cppverify::check(a.subset_of(a.insert(x)));
}
// CHECK-DAG: Verified: sets

cppverify::proof void set_wrong(set a, int x)
{
  cppverify::check(a.contains(x));
}
// CHECK-DAG: error: verification failed: set_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: a [ssa=a_0] [type=set] = {{{.*}}}{{.*}}) [backend=z3] [reason=counterexample]

cppverify::proof void multisets(multiset m, int x)
{
  cppverify::check(m.insert(x).count(x) == m.count(x) + 1);
  cppverify::check(m.insert(x).remove(x) == m);
  cppverify::check(m.count(x) >= 0);
  cppverify::check(cppverify::multiset_empty().remove(x).count(x) == 0);
}
// CHECK-DAG: Verified: multisets

// Removing first loses an occurrence that is not there.
cppverify::proof void multiset_wrong(multiset m, int x)
{
  cppverify::check(m.remove(x).insert(x) == m);
}
// CHECK-DAG: error: verification failed: multiset_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

cppverify::proof void maps(map m, int k, int v, int j)
  cppverify::pre(k != j)
{
  cppverify::check(m.insert(k, v)[k] == v);
  cppverify::check(m.insert(k, v).contains(k));
  cppverify::check(!m.remove(k).contains(k));
  cppverify::check(m.remove(k)[k] == 0);
  cppverify::check(m.insert(k, v)[j] == m[j]);
  cppverify::check(cppverify::map_empty().insert(k, v).remove(k) ==
                  cppverify::map_empty());
}
// CHECK-DAG: Verified: maps

cppverify::proof void map_wrong(map m, int k)
{
  cppverify::check(m.insert(k, 1).remove(k) == m);
}
// CHECK-DAG: error: verification failed: map_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: {{.*}}m [ssa=m_0] [type=map] = {{{.*}} -> {{.*}}}) [backend=z3] [reason=counterexample]

// A set may hold every integer; the certifier checks the infinite one.
cppverify::proof void some_outside(set a)
{
  cppverify::check(cppverify::exists(k, !a.contains(k)));
}
// CHECK-DAG: error: verification failed: some_outside [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: a [ssa=a_0] [type=set] = {..}) [backend=z3] [reason=counterexample]

cppverify::proof void map_values(map m)
  cppverify::pre(m.contains(5))
{
  cppverify::check(cppverify::forall(k, m[k] == 0));
}
// CHECK-DAG: error: verification failed: map_values [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: m [ssa=m_0] [type=map] = {{{.*}}5{{.*}}}) [backend=z3] [reason=counterexample]

cppverify::spec bool valid(const int *p, int n) { return true; }

// Ghost collections record what a loop has read.
int count_equal(const int *a, int n, int x)
  cppverify::pre(valid(a, n) && n >= 0 && n <= 1000)
  cppverify::post(0 <= cppverify::result && cppverify::result <= n)
{
  cppverify::ghost multiset seen = cppverify::multiset_empty();
  cppverify::ghost set values = cppverify::set_empty();
  cppverify::ghost map at = cppverify::map_empty();
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n && 0 <= c && c <= i)
    cppverify::invariant(seen.count(x) == c)
    cppverify::invariant(cppverify::forall(k, 0, i, values.contains(a[k])))
    cppverify::invariant(cppverify::forall(k, 0, i, at.contains(k) && at[k] == a[k]))
    cppverify::decreases(n - i)
  {
    if (a[i] == x)
      c = c + 1;
    cppverify::ghost {
      seen = seen.insert(a[i]);
      values = values.insert(a[i]);
      at = at.insert(i, a[i]);
    }
  }
  cppverify::check(cppverify::forall(k, 0, n, values.contains(a[k])));
  cppverify::check(n == 0 || at[n - 1] == a[n - 1]);
  return c;
}
// CHECK-DAG: Verified: count_equal

// REPLAY-DAG: Verified: sets
// REPLAY-DAG: Verified: count_equal
// REPLAY-DAG: error: verification failed: map_wrong

// VC-LABEL: vc sets
// VC: features {{.*}}collections
// VC: set.contains : bool
// VC-LABEL: vc count_equal
// VC: multiset.count : int
// VC: map.get : int
