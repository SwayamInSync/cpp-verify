// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

void write_ptr(int *p, int v)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == v)
{
  *p = v;
}

// VERIFY: Verified: write_ptr