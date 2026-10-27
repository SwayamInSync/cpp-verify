// RUN: %python %S/Inputs/interrupt_after.py 15 30 %cpp-verify --jobs=1 --timeout=600000 %s -- | FileCheck %s
// RUN: %python %S/Inputs/interrupt_after.py 5 30 %cpp-verify --jobs=1 --timeout=600000 --diagnostics-format=json %s -- | FileCheck %s --check-prefix=JSON
// RUN: %python %S/Inputs/interrupt_after.py 15 30 %cpp-verify --jobs=4 --timeout=600000 %s -- | FileCheck %s
// RUN: %python %S/Inputs/interrupt_after.py 5 30 %cpp-verify --jobs=1 --timeout=600000 %s %S/Inputs/interrupt_second.cpp -- | FileCheck %s --check-prefix=FILES
// RUN: %cpp-verify --lower-only --obligation-out=%t.cpv %s -- > /dev/null
// RUN: %python %S/Inputs/interrupt_after.py 5 30 %cpp-verify --obligation-in=%t.cpv --jobs=1 --timeout=600000 | FileCheck %s --check-prefix=REPLAY

// Ctrl-C stops the solvers, and cpp-verify exits with 128 + SIGINT. A
// function whose verification it cut short is reported Interrupted, and a
// proof that rests on its contract is not established.

int fast(int x)
  cppverify::pre(0 <= x && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

cppverify::proof void cubes(int x, int y, int z);

cppverify::proof void twice_a_cube(int x)
  cppverify::pre(x > 0)
  cppverify::post(x * x * x + x * x * x != 512)
{
  cubes(x, x, 8);
}

// Its counterexample is confirmed by a proof once every function is
// verified, which the interrupt comes before.
cppverify::spec int pow2(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= n + 1)
{
  return n <= 0 ? 1 : 2 * pow2(n - 1);
}

cppverify::proof void small_power(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(pow2(n) < 1000)
{
}

// No solver settles these within the timeout.
cppverify::proof void cubes(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x + y * y * y != z * z * z)
{
}

cppverify::proof void fourth_powers(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x * x + y * y * y * y != z * z * z * z)
{
}

// A spec axiom needs no solver.
cppverify::spec int cube(int x) { return x * x * x; }

// The run with four jobs reports the same.
// CHECK:      Verified: fast
// CHECK-NEXT: Unresolved: twice_a_cube {{.*}}[reason=callee.contract]
// CHECK-NEXT: Verified: spec decreases and post: pow2
// CHECK-NEXT: Interrupted: small_power
// CHECK-NEXT: Interrupted: cubes
// CHECK-NEXT: Interrupted: fourth_powers
// CHECK-NEXT: Summary: {{.*}}
// CHECK-NEXT: exit: 130

// JSON: "function":"cubes","message":"cubes","reason":"interrupted","schema":"cppverify.diagnostic/1","severity":"error","source":{{.*}}"status":"unresolved"
// JSON: exit: 130

// Replay stops the same way.
// REPLAY: Proved obligations: fast
// REPLAY: Interrupted: fourth_powers
// REPLAY-NEXT: exit: 130

// The files left are not read.
// FILES: Interrupted: fourth_powers
// FILES-NOT: second
// FILES: exit: 130
