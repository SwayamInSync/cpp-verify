// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s
//
// A contract_assert is proved where it stands and assumed from there on, which
// is what makes it a proof step for the obligations after it.

int step(int x)
  pre(x > 0)
  post(result > 0)
{
  contract_assert(x >= 1);
  return x;
}

// CHECK-LABEL: passive step
// CHECK:      assert assertion
// CHECK-NEXT:   ||
// CHECK-NEXT:     !
// CHECK-NEXT:       true
// CHECK-NEXT:     >=
// CHECK-NEXT:       x_0
// CHECK-NEXT:       1
// CHECK-NEXT: assume
// CHECK-NEXT:   ||
// CHECK-NEXT:     !
// CHECK-NEXT:       true
// CHECK-NEXT:     >=
// CHECK-NEXT:       x_0
// CHECK-NEXT:       1
