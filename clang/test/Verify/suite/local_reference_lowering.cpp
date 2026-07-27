// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

void set_value(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int local_reference_lowering(int value)
  post(result == value)
{
  int local = 0;
  int &alias = local;
  set_value(alias, value);
  return local;
}

// VCR-LABEL: fn local_reference_lowering
// VCR: stack_allocate local size 4 align 4 provenance __cppverify_stack_provenance_1
// VCR-NEXT: 0
// VCR: assert
// VCR: valid_ptr
// VCR-NEXT: local
// VCR: initialized_ptr
// VCR-NEXT: local
// VCR: assign alias
// VCR-NEXT: local
// VCR: assign __cppverify_reference_provenance_1
// VCR-NEXT: __cppverify_stack_provenance_1
// VCR: call set_value
// VCR-NEXT: alias
// VCR-NEXT: value
// VCR: return
// VCR-NEXT: load
// VCR-NEXT: local

// PASSIVE-LABEL: passive local_reference_lowering
// PASSIVE: __cppverify_stack_provenance_1_1
// PASSIVE: heap_store
// PASSIVE: local_1
// PASSIVE: valid_ptr
// PASSIVE: initialized_ptr
// PASSIVE: alias_1
// PASSIVE: __cppverify_reference_provenance_1_1
// PASSIVE: __cppverify_stack_provenance_1_1
// PASSIVE: heap_store
// PASSIVE: load
// PASSIVE: local_1
// PASSIVE: result

// VC-LABEL: vc local_reference_lowering
// VC: valid_ptr
// VC: initialized_ptr
// VC: heap_store

// Z3-DAG: (store __heap_alloc_used_0
// Z3-DAG: (store __heap_alloc_0
// Z3-DAG: (store __heap_live_0
// Z3-DAG: (store __heap_init_0
// Z3-DAG: (select __heap_
// Z3-NOT: error:

// BMC-DAG: Verified: set_value
// BMC-DAG: Verified: local_reference_lowering
