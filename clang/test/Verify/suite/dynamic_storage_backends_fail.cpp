// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void rebind_pointer(int *target)
  post(target == nullptr)
{
  target = nullptr;
}

int dynamic_backend_rebinding()
  post(result == 2)
{
  int *owner = new int(1);
  rebind_pointer(owner);
  delete owner;
  return 1;
}

// VERIFY: error: verification failed: dynamic_backend_rebinding
