// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

int reject_old_do_local()
  post(result == 1)
{
  int local;
  do {
    local = 1;
  } while (false)
    invariant(old(local) == 1);
  return local;
}

// CHECK: error: reject_old_do_local: old(...) cannot refer to local variable
// CHECK-SAME: without a function-entry state: local
