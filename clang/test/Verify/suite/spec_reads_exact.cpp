// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s

// A spec's integers are mathematical, the values it reads from memory
// included: a value read is its exact value, so arithmetic on it does not
// wrap.

cppverify::spec int pair_sum(const int *p)
  cppverify::reads(p, 2)
  cppverify::post(p[0] < 0 || p[1] < 0 || cppverify::result >= 0)
{
  return p[0] + p[1];
}

cppverify::spec int doubled(const int *p)
  cppverify::reads(p, 1)
  cppverify::post(*p < 0 || cppverify::result >= 0)
{
  int t = *p;
  return t + t;
}

cppverify::spec int negated(const int *p)
  cppverify::reads(p, 1)
  cppverify::post(*p > 0 || cppverify::result >= 0)
{
  return -*p;
}

cppverify::spec int first(const int *p)
  cppverify::reads(p, 1)
{
  return *p;
}

// The sum of two cells of 2^30 is 2^31.
cppverify::proof void large_sum(const int *p)
  cppverify::pre(cppverify::valid(p, 2) && p[0] == 1073741824 && p[1] == 1073741824)
  cppverify::post(pair_sum(p) == 2147483648)
  cppverify::post(pair_sum(p) > first(p))
{
}

// False: the sum is positive.
cppverify::proof void negative_sum(const int *p)
  cppverify::pre(cppverify::valid(p, 2) && p[0] == 1073741824 && p[1] == 1073741824)
  cppverify::post(pair_sum(p) < 0)
{
}

cppverify::proof void smallest_negated(const int *p)
  cppverify::pre(cppverify::valid(p, 1) && *p == -2147483647 - 1)
  cppverify::post(negated(p) == 2147483648)
{
}

// Executable code reads machine values: unsigned arithmetic on them wraps.
unsigned next(const unsigned *p)
  cppverify::pre(cppverify::valid(p, 1) && *p == 4294967295u)
  cppverify::post(cppverify::result == 0)
{
  return *p + 1;
}

// CHECK:      Verified: spec reads: pair_sum
// CHECK-NEXT: Verified: spec post: pair_sum
// CHECK-NEXT: Verified: spec reads: doubled
// CHECK-NEXT: Verified: spec post: doubled
// CHECK-NEXT: Verified: spec reads: negated
// CHECK-NEXT: Verified: spec post: negated
// CHECK-NEXT: Verified: spec reads: first
// CHECK-NEXT: Verified: large_sum
// CHECK-NEXT: error: verification failed: negative_sum {{.*}}[reason=counterexample]
// CHECK-NEXT: Verified: smallest_negated
// CHECK-NEXT: Verified: next [backend=z3]{{$}}
