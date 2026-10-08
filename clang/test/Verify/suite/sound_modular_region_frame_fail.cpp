// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec bool valid(int *p, int n) { return true; }

void clobber_offset(int *p)
  cppverify::pre(valid(p, 2))
  cppverify::modifies(*p)
  cppverify::post(*p == 0)
{
  *p = 0;
  p[1] = 999;
}

void invalid_region_frame(int *p)
  cppverify::pre(valid(p, 2) && p[1] == 5)
  cppverify::modifies(*p)
  cppverify::post(p[1] == 5)
{
  clobber_offset(p);
}

// VERIFY-DAG: Verified: clobber_offset
// VERIFY-DAG: error: verification failed: invalid_region_frame [{{.*}}::postcondition@
