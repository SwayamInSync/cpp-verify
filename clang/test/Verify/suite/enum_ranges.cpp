// RUN: not %cpp-verify --timeout=20000 %s -- 2>&1 | FileCheck %s --implicit-check-not="Verified: spec post: small_by"
//
// A machine value of an enumeration without a fixed underlying type lies in
// the enumeration's value range ([dcl.enum]/8): only a conversion can
// produce one outside it, and executable and proof code check every
// conversion. A spec converts without a check, so its values need not.

enum Color { Red, Green, Blue };
enum Sign { Negative = -1, Zero, Positive };
enum class Wide : int { A, B };

bool parameter(Color c)
  cppverify::post(cppverify::result)
{
  return 0 <= c && c < 4;
}
// CHECK-DAG: Verified: parameter

bool signed_parameter(Sign s)
  cppverify::post(cppverify::result)
{
  return -2 <= s && s < 2;
}
// CHECK-DAG: Verified: signed_parameter

bool load(const Color *p)
  cppverify::pre(cppverify::valid(p, 1))
  cppverify::post(cppverify::result)
{
  return *p < 4;
}
// CHECK-DAG: Verified: load

[[cppverify::trusted]] Color pick(int i)
  cppverify::pre(0 <= i);

bool call_result(int i)
  cppverify::pre(0 <= i)
  cppverify::post(cppverify::result)
{
  Color c = pick(i);
  return c < 4;
}
// CHECK-DAG: Verified: call_result

bool loop_head(Color c, int n)
  cppverify::pre(0 <= n && n <= 10)
  cppverify::post(cppverify::result)
{
  Color x = c;
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    if (x == Red)
      x = Blue;
  }
  return x < 4;
}
// CHECK-DAG: Verified: loop_head

cppverify::proof void lemma(Color c)
  cppverify::post(c < 4)
{
}
// CHECK-DAG: Verified: lemma

// An enumeration with a fixed underlying type has every value of that type.
bool fixed_type(Wide w)
  cppverify::post(cppverify::result)
{
  return static_cast<int>(w) < 2;
}
// CHECK-DAG: error: verification failed: fixed_type [postcondition]{{.*}}[reason=counterexample]

Color convert(int i)
  cppverify::pre(0 <= i && i <= 4)
{
  return static_cast<Color>(i);
}
// CHECK-DAG: error: verification failed: convert [overflow]{{.*}}[reason=counterexample]

cppverify::spec bool small(Color c)
  cppverify::post(cppverify::result)
{
  return c < 4;
}
// CHECK-DAG: error: spec post failed: small [backend=z3] [reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}c = 4{{( ->|,|$)}}

// The same check run as a proof function by its block.
cppverify::spec bool small_by(Color c)
  cppverify::post(cppverify::result) by { cppverify::check(true); }
{
  return c < 4;
}
