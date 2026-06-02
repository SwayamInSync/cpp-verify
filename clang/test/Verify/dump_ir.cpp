// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=L1
// RUN: %cpp-verify --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=L2
// RUN: %cpp-verify --dump-ir=layer-3,layer-4 %s 2>&1 | FileCheck %s --check-prefix=L34
// RUN: %cpp-verify --dump-ir %s 2>&1 | FileCheck %s --check-prefix=ALL

int abs(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

// L1: fn abs
// L1-NOT: passive
// L1-NOT: vc abs
// L1-NOT: ======

// L2: passive abs
// L2-NOT: {{^}}fn abs
// L2-NOT: vc abs
// L2-NOT: ======

// L34: vc abs
// L34: (and true
// L34: ======
// L34-NOT: fn abs
// L34-NOT: passive abs

// ALL: fn abs
// ALL: ======
// ALL: passive abs
// ALL: ======
// ALL: vc abs
// ALL: ======
// ALL: (and true
// ALL: Verified: