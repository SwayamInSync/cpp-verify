// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

int nested_scope_fallthrough()
  post(result == 7)
{
  int result_value = 0;
  {
    int values[2] = {3, 7};
    result_value = values[1];
  }
  return result_value;
}

int early_return_lifetime(bool choose)
  post(result == (choose ? 2 : 3))
{
  int outer[1] = {3};
  if (choose) {
    int inner[1] = {2};
    return inner[0];
  }
  return outer[0];
}

int reverse_lifetime_order()
  post(result == 5)
{
  int first[1] = {4};
  int second[1] = {5};
  return second[0];
}

// VERIFY-DAG: Verified: nested_scope_fallthrough
// VERIFY-DAG: Verified: early_return_lifetime
// VERIFY-DAG: Verified: reverse_lifetime_order

// The nested array ends at its closing brace, before the function return.
// VCR-LABEL: fn nested_scope_fallthrough
// VCR: stack_allocate values size 8 align 4 provenance
// VCR: assign result_value
// VCR-NEXT: load
// VCR: end_lifetime values provenance
// VCR-NEXT: return
// VCR-NEXT: result_value

// Every early return snapshots its value before ending the inner and outer
// objects. The fallthrough path ends only the outer object.
// VCR-LABEL: fn early_return_lifetime
// VCR: stack_allocate outer size 4 align 4 provenance
// VCR: if
// VCR: stack_allocate inner size 4 align 4 provenance
// VCR: assign __return_value_
// VCR-NEXT: load
// VCR: end_lifetime inner provenance
// VCR-NEXT: end_lifetime outer provenance
// VCR-NEXT: return
// VCR: assign __return_value_
// VCR-NEXT: load
// VCR: end_lifetime outer provenance
// VCR-NEXT: return

// Automatic objects end in reverse construction order.
// VCR-LABEL: fn reverse_lifetime_order
// VCR: stack_allocate first size 4 align 4 provenance
// VCR: stack_allocate second size 4 align 4 provenance
// VCR: assign __return_value_
// VCR: end_lifetime second provenance
// VCR-NEXT: end_lifetime first provenance
// VCR-NEXT: return

// A lexical inner-scope teardown is a semantic liveness-heap transition in
// passive SSA. Function-exit transitions are erased after non-escape checking.
// PASSIVE-LABEL: passive nested_scope_fallthrough
// PASSIVE: heap_store
// PASSIVE: false

// VC-LABEL: vc nested_scope_fallthrough
// VC: heap_store : bool
// VC: false : bool

// Z3: store
// Z3-NOT: unsupported

// BMC-DAG: Verified: nested_scope_fallthrough
// BMC-DAG: Verified: early_return_lifetime
// BMC-DAG: Verified: reverse_lifetime_order
