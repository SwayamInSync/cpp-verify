// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --implicit-check-not=error
// RUN: not %cpp-verify %s -- -DUSE_UNSUPPORTED 2>&1 | FileCheck %s --check-prefix=USED
//
// An uncontracted constexpr function becomes a spec where verification uses
// it: in a contract, a verified body, a type invariant, or another such spec.
// One that nothing verified uses is never converted, so a construct the
// verifier does not support there (as in a standard header) cannot fail the
// run, while using it still does.

namespace lib {
struct Pair {
  int a;
  int b;
};
constexpr Pair make_pair(int a, int b) { return Pair{a, b}; }
} // namespace lib

constexpr int twice(int x) { return 2 * x; }
constexpr int four_times(int x) { return twice(twice(x)); }

int quadruple(int x)
  cppverify::pre(x >= 0 && x <= 1000)
  cppverify::post(cppverify::result == four_times(x))
{
  return 4 * x;
}
// CHECK-DAG: Verified: quadruple

constexpr bool is_even(int v) { return v % 2 == 0; }

struct Even {
  int v;
  cppverify::type_invariant(is_even(v) && v >= 0 && v <= 1000);
};

int next_even(Even e)
  cppverify::post(cppverify::result % 2 == 0)
{
  return e.v + 2;
}
// CHECK-DAG: Verified: next_even

#ifdef USE_UNSUPPORTED
int first(int a, int b)
  cppverify::post(cppverify::result == lib::make_pair(a, b).a)
{
  return a;
}
// USED: error: make_pair: aggregate-returning constexpr specs are unsupported
#endif
