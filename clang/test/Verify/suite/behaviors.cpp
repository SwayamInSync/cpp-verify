// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// ACSL behaviors: behavior(name, assumes) introduces a case; the pre and
// post clauses after it hold where its assumption does (assumes -> pre,
// old(assumes) -> post). complete_behaviors requires that some behavior
// applies to every input the preconditions admit, and disjoint_behaviors
// that no two do; either may name the behaviors it relates.

int abs_value(int x)
  behavior(nonnegative, x >= 0)
    post(result == x)
  behavior(negative, x < 0)
    pre(x > -2147483647 - 1)
    post(result == -x)
  complete_behaviors
  disjoint_behaviors
{
  return x < 0 ? -x : x;
}
// CHECK-DAG: Verified: abs_value

int uses_abs(int y)
  pre(y >= -100)
  post(result >= 0 && (y < 0 || result == y))
{
  return abs_value(y);
}
// CHECK-DAG: Verified: uses_abs

int calls_with_minimum(int y)
  post(true)
{
  return abs_value(y);
}
// CHECK-DAG: error: verification failed: calls_with_minimum [{{.*}}::precondition@[[@LINE-2]]:3]

int sign(int x)
  behavior(positive, x > 0)
    post(result == 1)
  behavior(negative, x < 0)
    post(result == -1)
  complete_behaviors
{
  return x > 0 ? 1 : (x < 0 ? -1 : 0);
}
// CHECK-DAG: error: verification failed: sign [{{.*}}::assertion@[[@LINE-4]]:3]

int clamp(int x)
  behavior(low, x <= 0)
    post(result <= 0)
  behavior(high, x >= 0)
    post(result >= 0)
  disjoint_behaviors(low, high)
{
  return x;
}
// CHECK-DAG: error: verification failed: clamp [{{.*}}::assertion@[[@LINE-4]]:3]

int small_zero(int x)
  behavior(small, x < 10)
    post(result == 0)
{
  return x < 5 ? 0 : 1;
}
// CHECK-DAG: error: verification failed: small_zero [{{.*}}::postcondition@[[@LINE-4]]:10]

// A behavior's assumption reads memory at entry.
void bump(int *p)
  pre(p != nullptr)
  modifies(*p)
  behavior(below, *p < 100)
    post(*p == old(*p) + 1)
  behavior(at_limit, *p >= 100)
    post(*p == old(*p))
  complete_behaviors
  disjoint_behaviors
{
  if (*p < 100)
    *p = *p + 1;
}
// CHECK-DAG: Verified: bump

// Global clauses hold in every behavior.
int halve(int x)
  pre(x >= 0)
  post(result <= x)
  behavior(even, x % 2 == 0)
    post(result * 2 == x)
  behavior(odd, x % 2 == 1)
    post(result * 2 + 1 == x)
  complete_behaviors
  disjoint_behaviors
{
  return x / 2;
}
// CHECK-DAG: Verified: halve
