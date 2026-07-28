// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-obj -o %t.o %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-obj -o %t2.o %s
// RUN: %clang -std=c++17 -fverify-contracts -c -o %t3.o %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o - %s | FileCheck %s

// The ordinary compilation path verifies promoted local objects during
// CodeGen and still emits plain machine code for them: contracts, reference
// bindings and ghost constructs add no runtime work.

struct Pair {
  int first;
  int second;
};

void set_scalar(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int local_record_object()
  post(result == 7)
{
  Pair value{1, 2};
  int &alias = value.second;
  alias = 7;
  return value.second;
}

int local_array_object(int index)
  pre(index >= 0 && index < 4)
  post(result == 9)
{
  int a[4] = {1, 2, 3, 4};
  set_scalar(a[index], 9);
  return a[index];
}

// CHECK: define {{.*}}@_Z19local_record_objectv
// CHECK: define {{.*}}@_Z18local_array_objecti
// CHECK-NOT: cppverify
