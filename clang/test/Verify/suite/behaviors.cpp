// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
//
// ACSL behaviors: behavior(name, assumes) introduces a case; the pre and
// post clauses after it hold where its assumption does (assumes -> pre,
// old(assumes) -> post). complete_behaviors requires that some behavior
// applies to every input the preconditions admit, and disjoint_behaviors
// that no two do; either may name the behaviors it relates.

int abs_value(int x)
  cppverify::behavior(nonnegative, x >= 0)
    cppverify::post(cppverify::result == x)
  cppverify::behavior(negative, x < 0)
    cppverify::pre(x > -2147483647 - 1)
    cppverify::post(cppverify::result == -x)
  cppverify::complete_behaviors
  cppverify::disjoint_behaviors
{
  return x < 0 ? -x : x;
}
// CHECK-DAG: Verified: abs_value

int uses_abs(int y)
  cppverify::pre(y >= -100)
  cppverify::post(cppverify::result >= 0 && (y < 0 || cppverify::result == y))
{
  return abs_value(y);
}
// CHECK-DAG: Verified: uses_abs

int calls_with_minimum(int y)
  cppverify::post(true)
{
  return abs_value(y);
}
// CHECK-DAG: error: verification failed: calls_with_minimum [{{.*}}::precondition@[[@LINE-2]]:3]

int sign(int x)
  cppverify::behavior(positive, x > 0)
    cppverify::post(cppverify::result == 1)
  cppverify::behavior(negative, x < 0)
    cppverify::post(cppverify::result == -1)
  cppverify::complete_behaviors
{
  return x > 0 ? 1 : (x < 0 ? -1 : 0);
}
// CHECK-DAG: error: verification failed: sign [{{.*}}::assertion@[[@LINE-4]]:3]

int clamp(int x)
  cppverify::behavior(low, x <= 0)
    cppverify::post(cppverify::result <= 0)
  cppverify::behavior(high, x >= 0)
    cppverify::post(cppverify::result >= 0)
  cppverify::disjoint_behaviors(low, high)
{
  return x;
}
// CHECK-DAG: error: verification failed: clamp [{{.*}}::assertion@[[@LINE-4]]:3]

int small_zero(int x)
  cppverify::behavior(small, x < 10)
    cppverify::post(cppverify::result == 0)
{
  return x < 5 ? 0 : 1;
}
// CHECK-DAG: error: verification failed: small_zero [{{.*}}::postcondition@[[@LINE-4]]:21]

// A behavior's assumption reads memory at entry.
void bump(int *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::behavior(below, *p < 100)
    cppverify::post(*p == cppverify::old(*p) + 1)
  cppverify::behavior(at_limit, *p >= 100)
    cppverify::post(*p == cppverify::old(*p))
  cppverify::complete_behaviors
  cppverify::disjoint_behaviors
{
  if (*p < 100)
    *p = *p + 1;
}
// CHECK-DAG: Verified: bump

// Global clauses hold in every behavior.
int halve(int x)
  cppverify::pre(x >= 0)
  cppverify::post(cppverify::result <= x)
  cppverify::behavior(even, x % 2 == 0)
    cppverify::post(cppverify::result * 2 == x)
  cppverify::behavior(odd, x % 2 == 1)
    cppverify::post(cppverify::result * 2 + 1 == x)
  cppverify::complete_behaviors
  cppverify::disjoint_behaviors
{
  return x / 2;
}
// CHECK-DAG: Verified: halve
