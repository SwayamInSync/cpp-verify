// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s

int reject_old_do_local()
  cppverify::post(cppverify::result == 1)
{
  int local;
  do {
    local = 1;
  } while (false)
    cppverify::invariant(cppverify::old(local) == 1);
  return local;
}

// CHECK: error: reject_old_do_local: cppverify::old(...) cannot refer to local variable
// CHECK-SAME: without a function-entry state: local
