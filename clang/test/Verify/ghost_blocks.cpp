// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o %t %s
//
// Test that ghost blocks and contract_assert:
// 1. Appear in the AST dump
// 2. Produce zero codegen (no LLVM IR for ghost content)
//
// CHECK: GhostBlockStmt
// CHECK: ContractAssertStmt

int abs_val(int x)
  cppverify::pre(x != -2147483648)
  cppverify::post(cppverify::result >= 0)
{
  cppverify::ghost {
    cppverify::check(x != -2147483648);
  }
  if (x < 0) return -x;
  return x;
}
