// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=LOWER
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=LEAN
// RUN: not %cpp-verify --backend=unknown %s 2>&1 | FileCheck %s --check-prefix=INVALID
// RUN: rm -rf %t.no-fallback
// RUN: not %cpp-verify --lean-fallback=%t.no-fallback %s 2>&1 | FileCheck %s --check-prefix=NO-FALLBACK
// RUN: not grep -q '^import CppVerify.Proofs.Goal_' %t.no-fallback/CppVerify/Check.lean

int valid_result(int value)
  post(result == value)
{
  return value;
}

int invalid_result()
  post(result == 0)
{
  return 1;
}

// Z3-DAG: Verified: valid_result [backend=z3]
// Z3-DAG: backend_result_contract.cpp:{{[0-9]+}}:{{[0-9]+}}: error: verification failed: invalid_result [{{.*}}::obligation:{{[0-9]+}}]

// BMC-DAG: Verified: valid_result [backend=bmc, bound=1]
// BMC-DAG: backend_result_contract.cpp:{{[0-9]+}}:{{[0-9]+}}: error: verification failed: invalid_result [{{.*}}::obligation:{{[0-9]+}}]

// LOWER-DAG: Lowered: valid_result
// LOWER-DAG: Lowered: invalid_result
// LOWER-NOT: Verified:

// LEAN-DAG: Exported: lean obligation: valid_result
// LEAN-DAG: Exported: lean obligation: invalid_result
// LEAN-NOT: Verified:

// INVALID: error: unknown verification backend 'unknown'; expected z3, lean, or bmc
// INVALID-NOT: Verified:

// NO-FALLBACK: error: verification failed: invalid_result
// NO-FALLBACK-NOT: lean fallback
