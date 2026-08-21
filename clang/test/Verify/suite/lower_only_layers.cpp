// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=LOWER
// RUN: %cpp-verify --lower-only --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=LOWER
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --lower-only --backend=lean %s 2>&1 | FileCheck %s --check-prefix=LEAN
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3

spec int mathematical_successor(int x)
{
  return x + 1;
}

int machine_identity(int x)
  pre(x >= 0 && x < 100)
  post(result == mathematical_successor(x))
{
  return x;
}

// LOWER-DAG: Lowered: spec axiom: mathematical_successor
// LOWER-DAG: Lowered: machine_identity
// LOWER-NOT: Verified:
// LOWER-NOT: error:

// VERIFY: Verified: spec axiom: mathematical_successor
// VERIFY: error: verification failed: machine_identity

// LEAN: error: --lower-only supports Z3, cvc5, portfolio, and BMC

// VCR-LABEL: fn machine_identity
// VCR: param x
// VCR: pre
// VCR: &&
// VCR: post
// VCR: ==
// VCR: result
// VCR: +
// VCR: cast
// VCR: body
// VCR: return
// VCR-NEXT: x
// VCR-NOT: passive machine_identity

// PASSIVE-LABEL: passive machine_identity
// PASSIVE: result __result_1
// PASSIVE: entry
// PASSIVE: x_0
// PASSIVE: stmt
// PASSIVE: assume
// PASSIVE: __result_1
// PASSIVE: exit
// PASSIVE: cast
// PASSIVE-NOT: vc machine_identity

// VC-LABEL: vc machine_identity
// VC: identity fn_
// VC: features mathematical-integers, bit-vectors, pointers, heap-arrays
// VC: counterexample
// VC: !
// VC: x_0 : bitvector32
// VC: __result_1 : bitvector32
// VC: bv_to_int : int
// VC: obligations
// VC: obligation fn_
// VC-NOT: passive machine_identity

// Z3-DAG: (bvsge x_0 #x00000000)
// Z3-DAG: (bvslt x_0 #x00000064)
// Z3-DAG: (bv2int x_0)
// Z3-DAG: (- 2147483648)
// Z3-DAG: 2147483647
// Z3-DAG: (bvadd x_0 ((_ int2bv 32) 1))
// Z3-NOT: error:
