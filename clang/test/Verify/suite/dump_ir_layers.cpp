// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=L1
// RUN: %cpp-verify --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=L2
// RUN: %cpp-verify --dump-ir=3,4 %s 2>&1 | FileCheck %s --check-prefix=L34

int inc(int x)
  pre(x >= 0 && x < 100)
  post(result == x + 1)
{
  return x + 1;
}

// L1: fn inc
// L1-NOT: passive inc
// L2: passive inc
// L2-NOT: {{^}}fn inc
// L34: vc inc
// L34: Verified: