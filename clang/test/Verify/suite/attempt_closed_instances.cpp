// RUN: rm -rf %t && mkdir %t
// RUN: not cpp-verify --dump-smt2=%t %s -- -std=c++17 2>&1 | FileCheck %s
// RUN: %python -c "import glob, sys; [print(sum(l.startswith('(assert') for l in open(f))) for f in glob.glob(sys.argv[1] + '/small_power-*/*.smt2') if 'to confirm a counterexample by proof' in open(f).read()]" %t | FileCheck %s --check-prefix=SIZE
//
// A query that confirms a counterexample is an attempt with a slice of the
// time, and Z3 cannot be stopped while it takes in ground facts. So the
// equations that compute sum(600), 601 of them, are not added to it; the
// confirmation needs only the postcondition of pow2.

cppverify::spec int pow2(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= n + 1)
{
  return n <= 0 ? 1 : 2 * pow2(n - 1);
}

cppverify::spec int sum(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : n + sum(n - 1);
}

cppverify::proof void small_power(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(pow2(n) < 1000 && sum(600) == 180300)
{
}

// CHECK: verification failed: small_power [postcondition] (confirmed by a proof at this input
// SIZE: {{^[0-9]+$}}
// SIZE-NOT: {{^[0-9][0-9][0-9]}}
