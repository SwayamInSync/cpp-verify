// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

struct LocalRecord {
  int field;
};

int reject_old_do_local_field()
  post(result == 2)
{
  LocalRecord local;
  do {
    local.field = 2;
  } while (false)
    invariant(old(local.field) == 2);
  return local.field;
}

// CHECK: error: reject_old_do_local_field: old(...) cannot refer to local
// CHECK-SAME: variable without a function-entry state: local
