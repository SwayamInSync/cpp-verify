// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=LEAN

int backend_reassignment(bool choose)
  post(result == 1 || result == 2)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = first;
  if (choose)
    alias = second;
  int observed = *alias;
  delete first;
  delete second;
  return observed;
}

int backend_reassignment_use_after_delete(bool choose)
  post(true)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = choose ? first : second;
  delete first;
  return *alias;
}

// BMC-DAG: Verified: backend_reassignment
// BMC-DAG: error: verification failed: backend_reassignment_use_after_delete
// LEAN-DAG: Exported: lean obligation: backend_reassignment
// LEAN-DAG: Exported: lean obligation: backend_reassignment_use_after_delete
