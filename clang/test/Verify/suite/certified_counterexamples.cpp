// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,Z3
// RUN: not %cpp-verify --int-encoding=bitvector %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefixes=CHECK,Z3
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefixes=CHECK,BMC
// RUN: not %cpp-verify --diagnostics-format=json %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A counterexample is reported only when it holds with every logical function
// at its true definition. A hidden function is withheld from proofs, so a
// query that its definition would settle is unresolved (spec.hidden), while a
// counterexample that holds whatever its value is still a failure.

cppverify::spec int twice(int x) { return 2 * x; }

cppverify::spec int triangle(int n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return n + triangle(n - 1);
}

constexpr unsigned scale(unsigned x) { return x * 3u; }

constexpr int low_bits(int x) { return x & 255; }

// True, but the solver may not use twice's definition: not a counterexample.
int hidden_true(int x)
  cppverify::pre(0 <= x && x <= 10)
  cppverify::post(cppverify::result == twice(x))
{
  cppverify::ghost { cppverify::hide(twice); }
  return 2 * x;
}

// False whatever value twice has at x: a checked counterexample.
int hidden_false(int x)
  cppverify::pre(0 <= x && x <= 10)
  cppverify::post(cppverify::result == twice(x) + 1)
{
  cppverify::ghost { cppverify::hide(twice); }
  return 2 * x;
}

int hidden_recursive(int n)
  cppverify::pre(0 <= n && n <= 3)
  cppverify::post(cppverify::result == triangle(n))
{
  cppverify::ghost { cppverify::hide(triangle); }
  return n * (n + 1) / 2;
}

// Beyond the default fuel; settled by definition instances.
int bounded_closed_form(int n)
  cppverify::pre(0 <= n && n <= 40)
  cppverify::post(cppverify::result == triangle(n))
{
  return n * (n + 1) / 2;
}

int bounded_closed_form_wrong(int n)
  cppverify::pre(0 <= n && n <= 40)
  cppverify::post(cppverify::result == triangle(n))
{
  return n == 33 ? 0 : n * (n + 1) / 2;
}

// Machine semantics: scale wraps, and the counterexample must agree.
unsigned scaled_true(unsigned x)
  cppverify::post(cppverify::result == scale(x))
{
  cppverify::ghost { cppverify::hide(scale); }
  return x + x + x;
}

unsigned scaled_wrong(unsigned x)
  cppverify::pre(x >= 2000000000u)
  cppverify::post(cppverify::result == scale(x))
{
  cppverify::ghost { cppverify::hide(scale); }
  return x * 3u + (x == 3000000000u ? 1u : 0u);
}

int masked_wrong(int x)
  cppverify::pre(0 <= x && x <= 1000)
  cppverify::post(cppverify::result == low_bits(x))
{
  cppverify::ghost { cppverify::hide(low_bits); }
  return x % 256 + (x == 700 ? 1 : 0);
}

// CHECK-DAG: Unresolved: hidden_true [backend={{z3|bmc, bound=0}}] [reason=spec.hidden]
// CHECK-DAG: verification failed: hidden_false
// CHECK-DAG: Unresolved: hidden_recursive [backend={{z3|bmc, bound=0}}] [reason=spec.hidden]
// Z3-DAG: Verified: bounded_closed_form [backend=z3]
// BMC-DAG: Verified: bounded_closed_form [backend=bmc
// CHECK-DAG: verification failed: bounded_closed_form_wrong {{.*}}n [ssa=n_0] [type=i32] = 33;
// CHECK-DAG: Unresolved: scaled_true [backend={{z3|bmc, bound=0}}] [reason=spec.hidden]
// CHECK-DAG: verification failed: scaled_wrong {{.*}}x [ssa=x_0] [type=u32] = 3000000000;
// CHECK-DAG: verification failed: masked_wrong {{.*}}x [ssa=x_0] [type=i32] = 700;

// JSON-DAG: "function":"hidden_true"{{.*}}"reason":"spec.hidden"
// JSON-DAG: "function":"hidden_false"{{.*}}"reason":"counterexample"
