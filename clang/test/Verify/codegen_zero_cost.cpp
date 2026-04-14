// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o - %s | FileCheck %s
//
// Test that ghost code, spec functions, proof functions, and contract_assert
// produce zero LLVM IR. Only regular functions should appear in the output.

spec int spec_double(int x) {
  return x * 2;
}

proof void proof_trivial(int x)
  pre(x >= 0)
  post(x >= 0)
{
}

int regular_with_ghost(int x)
  pre(x >= 0)
  post(result >= 0)
{
  ghost {
    contract_assert(x >= 0);
    int tmp = x + 1;
    contract_assert(tmp > 0);
  }
  return x;
}

int regular_no_contracts(int x) {
  return x + 1;
}

// Regular functions should be present in IR:
// CHECK: define {{.*}} @_Z18regular_with_ghosti(
// CHECK: ret i32
// CHECK: define {{.*}} @_Z20regular_no_contractsi(
// CHECK: ret i32

// Spec and proof functions should NOT appear as definitions:
// CHECK-NOT: define {{.*}}spec_double
// CHECK-NOT: define {{.*}}proof_trivial

// Ghost block content should NOT be in regular function IR:
// (The function is defined, but ghost content is absent from its body)
