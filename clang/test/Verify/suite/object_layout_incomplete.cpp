// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s

struct Incomplete;

struct Holder {
  int count;
  Incomplete (*rows)[4];
};

unsigned long incomplete_array_pointee()
  post(result == sizeof(Holder) + sizeof(Incomplete (*)[4]))
{
  return sizeof(Holder) + sizeof(Incomplete (*)[4]);
}

// CHECK: layout Holder record size 16 align 8
// CHECK-NEXT: leaf .count offset 0 size 4 align 4 i32
// CHECK-NEXT: leaf .rows offset 8 size 8 align 8 ptr(0)
// CHECK-NOT: layout Incomplete[4]
// CHECK: Verified: incomplete_array_pointee
