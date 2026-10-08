// RUN: %cpp-verify --dump-ir=all %s 2>&1 | FileCheck %s --check-prefix=DUMP
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int len_spec(int n) {
  int value = n;
  return value;
}

cppverify::spec int opaque_spec(int n) { return n; }

int run(int *p, int n)
  cppverify::pre(n >= 0 && n <= 2 && p != 0)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result == len_spec(n))
  cppverify::post(opaque_spec(n) == opaque_spec(n))
{
  cppverify::ghost {
    cppverify::reveal(len_spec);
    cppverify::hide(opaque_spec);
  }
  cppverify::check(n >= 0);
  int r = 0;
  if (n > 0)
    r = *p;
  else
    r = 0;
  *p = r;
  return n;
}

// DUMP: fn run
// DUMP: spec_call
// DUMP: ghost
// DUMP: hide_spec
// DUMP: contract_assert
// DUMP: passive run
// DUMP: vc run
// VERIFY: Verified: run