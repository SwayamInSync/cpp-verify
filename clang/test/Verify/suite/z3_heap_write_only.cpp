// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void write_ptr(int *p, int v)
  pre(p != nullptr)
  modifies(*p)
  post(*p == v)
{
  *p = v;
}

// VERIFY: verified: write_ptr