// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=1,2,3,4 %s 2>&1 | FileCheck %s

long pointer_difference_ir(int value)
  post(result == 1)
{
  int *pointer = new int(value);
  long distance = (pointer + 1) - pointer;
  delete pointer;
  return distance;
}

// CHECK-LABEL: fn pointer_difference_ir
// CHECK: assign distance
// CHECK-NEXT: cast
// CHECK-NEXT: /
// CHECK-NEXT: -
// CHECK-NEXT: +
// CHECK-NEXT: pointer
// CHECK: ======
// CHECK-LABEL: passive pointer_difference_ir
// CHECK: valid_ptr
// CHECK-NEXT: pointer_
// CHECK: __cppverify_pointer_provenance_
// CHECK: ======
// CHECK-LABEL: vc pointer_difference_ir
// CHECK: features mathematical-integers, bit-vectors, pointers, heap-arrays
// CHECK: heap_select
// CHECK: __cppverify_pointer_provenance_
// CHECK: obligations
// CHECK: ======
// CHECK: (let
// CHECK: __heap_alloc_
// CHECK: div
// CHECK: bvsub
// CHECK: Lowered: pointer_difference_ir
