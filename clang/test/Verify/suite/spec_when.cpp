// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s
//
// when(c) restricts a spec's definition to the domain c: its termination is
// checked there only, and outside it the spec's value is unspecified, so
// nothing about it can be proved and no counterexample may depend on it.

cppverify::spec int log2(int n)
  cppverify::when(n >= 1)
  cppverify::decreases(n)
{
  return n == 1 ? 0 : 1 + log2(n / 2);
}
// CHECK-DAG: Verified: spec decreases: log2

void log2_values()
{
  cppverify::ghost { cppverify::check(log2(1) == 0 && log2(8) == 3 && log2(1000) == 9); }
}
// CHECK-DAG: Verified: log2_values

void log2_zero()
{
  cppverify::ghost { cppverify::check(log2(0) == 0); }
}
// CHECK-DAG: Unresolved: log2_zero {{.*}}[reason=counterexample.unchecked]

void log2_zero_is_a_value()
{
  cppverify::ghost { cppverify::check(log2(0) == log2(0 * 2)); }
}
// CHECK-DAG: Verified: log2_zero_is_a_value

// Without when, the same definition does not terminate at 0.
cppverify::spec int log2_total(int n)
  cppverify::decreases(n)
{
  return n == 1 ? 0 : 1 + log2_total(n / 2);
}
// CHECK-DAG: error: spec decreases failed: log2_total {{.*}}[reason=counterexample]

// A post holds on the domain.
cppverify::spec int log2_below(int n)
  cppverify::when(n >= 1)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0 && cppverify::result < n)
{
  return n == 1 ? 0 : 1 + log2_below(n / 2);
}
// CHECK-DAG: Verified: spec decreases and post: log2_below

void log2_below_use(int n)
  cppverify::pre(n >= 1)
{
  cppverify::ghost {
    cppverify::hide(log2_below);
    cppverify::check(log2_below(n) < n);
  }
}
// CHECK-DAG: Verified: log2_below_use

// A measure only has to be nonnegative where a call lowers it, so a step from
// 1 to -1 counts, and -1 is outside the domain.
cppverify::spec int skips(int n)
  cppverify::when(n >= 0)
  cppverify::decreases(n)
{
  return n == 0 ? 0 : skips(n - 2);
}
// CHECK-DAG: Verified: spec decreases: skips

// Within its domain a recursive call must still lower the measure, which an
// even argument does not.
cppverify::spec int stalls(int n)
  cppverify::when(n >= 0)
  cppverify::decreases(n)
{
  return n <= 1 ? 0 : stalls(n - (n % 2));
}
// CHECK-DAG: error: spec decreases failed: stalls {{.*}}[reason=counterexample] (n [type=math-i32] = {{[0-9]*[02468]}})
