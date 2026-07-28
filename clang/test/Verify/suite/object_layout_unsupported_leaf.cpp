// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s

struct WithFloat {
  int integer;
  float floating;
};

struct Polymorphic {
  int value;
  virtual void method();
};

unsigned long unsupported_leaf_layout()
  post(result == sizeof(WithFloat) + sizeof(Polymorphic))
{
  return sizeof(WithFloat) + sizeof(Polymorphic);
}

// CHECK-NOT: layout WithFloat
// CHECK-NOT: layout Polymorphic
// CHECK: Verified: unsupported_leaf_layout
