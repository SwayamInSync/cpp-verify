// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void clobber_offset(int *p)
  pre(p != nullptr)
  modifies(*p)
  post(*p == 0)
{
  *p = 0;
  p[1] = 999;
}

void invalid_region_frame(int *p)
  pre(p != nullptr && p[1] == 5)
  modifies(*p)
  post(p[1] == 5)
{
  clobber_offset(p);
}

// VERIFY-DAG: Verified: clobber_offset
// VERIFY-DAG: error: verification failed: invalid_region_frame
