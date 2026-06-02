// RUN: %cpp-verify --dump-ir=all %s 2>&1 | FileCheck %s --check-prefix=DUMP
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int len_spec(int n) { return n; }

int run(int *p, int n)
  pre(n >= 0 && n <= 2)
  modifies(*p)
  post(result == len_spec(n))
{
  ghost { reveal(len_spec); }
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
// DUMP: ghost
// DUMP: contract_assert
// DUMP: spec_call
// DUMP: passive run
// DUMP: vc run
// VERIFY: Verified: run