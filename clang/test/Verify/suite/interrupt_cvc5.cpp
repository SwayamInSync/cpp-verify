// REQUIRES: cvc5
// RUN: %python %S/Inputs/interrupt_after.py 5 30 %cpp-verify --backend=cvc5 --jobs=1 --timeout=600000 %s -- | FileCheck %s
// RUN: %python %S/Inputs/interrupt_after.py 5 30 %cpp-verify --backend=race --jobs=1 --timeout=600000 %s -- | FileCheck %s

// Ctrl-C stops the cvc5 processes too: none is left running.

int fast(int x)
  cppverify::pre(0 <= x && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

cppverify::proof void cubes(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x + y * y * y != z * z * z)
{
}

// CHECK:      Verified: fast
// CHECK-NEXT: Interrupted: cubes
// CHECK-NEXT: Summary: {{.*}}
// CHECK-NEXT: exit: 130
