// RUN: %cpp-verify --dump-ir=all %s 2>&1 | FileCheck %s --check-prefix=DUMP
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int len_spec(int n) {
  int value = n;
  return value;
}

spec int opaque_spec(int n) { return n; }

int run(int *p, int n)
  pre(n >= 0 && n <= 2 && p != 0)
  modifies(*p)
  post(result == len_spec(n))
  post(opaque_spec(n) == opaque_spec(n))
{
  ghost {
    reveal(len_spec);
    hide(opaque_spec);
  }
  contract_assert(n >= 0);
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