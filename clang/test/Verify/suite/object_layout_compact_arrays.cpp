// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s

unsigned long compact_nested_array()
  post(result == sizeof(int[300][300][300]))
{
  return sizeof(int[300][300][300]);
}

// CHECK: layout int[300][300][300] array size 108000000 align 4 count 300 stride 360000
// CHECK-NEXT: leaf [*][*][*] offset 0 size 4 align 4 repeat 300 stride 360000 repeat 300 stride 1200 repeat 300 stride 4 i32
// CHECK: Verified: compact_nested_array
