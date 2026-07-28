// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s

struct Outer {
  struct {
    int value;
  } first;
  struct {
    long long lo;
    long long hi;
  } second;
};

unsigned long anonymous_layouts()
  post(result == sizeof(Outer))
{
  return sizeof(Outer);
}

// CHECK: layout Outer record size 24 align 8
// CHECK: layout {{.*(anonymous|unnamed) struct.*}} record size 4 align 4
// CHECK-NEXT: leaf .value offset 0 size 4 align 4 i32
// CHECK: layout {{.*(anonymous|unnamed) struct.*}} record size 16 align 8
// CHECK-NEXT: leaf .lo offset 0 size 8 align 8 i64
// CHECK-NEXT: leaf .hi offset 8 size 8 align 8 i64
// CHECK: Verified: anonymous_layouts
