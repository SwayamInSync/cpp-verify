// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// A spec function is defined for every argument and its body is its meaning.
// A precondition assumed by its termination check while its definition is
// used everywhere would make the definition inconsistent, so pre, modifies,
// and aliases are rejected. A post is a checked property of the body, and a
// spec changes no state for it to refer to with old.

spec int needs_pre(int n)
  pre(n >= 0)
  decreases(n)
{
  return n < 0 ? needs_pre(n) + 1 : 0;
}

spec int post_with_old(int n)
  post(result == old(n))
{
  return n;
}

int executable_when(int n)
  when(n > 0)
{
  return n;
}

// CHECK-DAG: error: executable_when: when restricts the domain of a spec function only
// CHECK-DAG: error: needs_pre: a spec function is defined for every argument and its body is its meaning, so pre, modifies, and aliases do not apply; use recommends for a soft precondition
// CHECK-DAG: error: post_with_old: a spec changes no state, so its post cannot use old
