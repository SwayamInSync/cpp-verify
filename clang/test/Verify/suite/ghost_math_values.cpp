// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// In ghost and proof code a mathematical value (a spec result, a sequence
// length or element, a count) stays mathematical until it is stored in a
// machine variable, passed to a machine parameter, or cast: arithmetic on it
// is exact, and only the conversion must show that the value fits.

#include <cppverify.h>
using cppverify::seq;

cppverify::proof void length_arithmetic(seq s)
  cppverify::pre(s.len() > 0)
  cppverify::post(true)
{
  seq t = s.subrange(0, s.len() - 1);
  cppverify::check(t.len() == s.len() - 1);
  if (t.len() + 1 > s.len())
    cppverify::check(false);
}
// CHECK-DAG: Verified: length_arithmetic

// An element is a mathematical integer, which need not fit in an int.
cppverify::proof void stores_element(seq s)
  cppverify::pre(s.len() > 0)
  cppverify::post(true)
{
  int x = s[0];
}
// CHECK-DAG: error: verification failed: stores_element [{{.*}}::overflow@[[@LINE-2]]:3]

cppverify::proof void stores_bounded_element(seq s)
  cppverify::pre(s.len() > 0 && 0 <= s[0] && s[0] < 100)
  cppverify::post(true)
{
  int x = s[0];
  cppverify::check(x < 100);
}
// CHECK-DAG: Verified: stores_bounded_element

cppverify::proof void takes_int(int n)
  cppverify::post(true)
{
}

cppverify::proof void passes_length(seq s)
  cppverify::pre(s.len() > 0)
  cppverify::post(true)
{
  takes_int(s.len() + 2147483647);
}
// CHECK-DAG: error: verification failed: passes_length [{{.*}}::overflow@[[@LINE-2]]:3]

cppverify::proof void passes_bounded_length(seq s)
  cppverify::pre(s.len() < 1000)
  cppverify::post(true)
{
  takes_int(s.len());
}
// CHECK-DAG: Verified: passes_bounded_length

cppverify::proof void assigns_sum(seq s, seq t)
  cppverify::pre(s.len() < 1000 && t.len() < 1000)
  cppverify::post(true)
{
  int n = 0;
  n = s.len() + t.len();
  cppverify::check(n == (s + t).len());
}
// CHECK-DAG: Verified: assigns_sum

void ghost_length_too_large(int n)
  cppverify::pre(n >= 0)
  cppverify::post(true)
{
  cppverify::ghost {
    seq s = cppverify::seq_of(n);
    int k = s.len() + 2147483647;
  }
}
// CHECK-DAG: error: verification failed: ghost_length_too_large [{{.*}}::overflow@
