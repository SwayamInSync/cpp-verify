// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=LOWER
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3

int provenance_branch(bool choose)
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

int *provenance_identity(int *value)
  pre(value != nullptr)
  post(result == value)
  post(*result == old(*value))
{
  return value;
}

int provenance_call(int value)
  post(result == value)
{
  int *owner = new int(value);
  int *returned = provenance_identity(owner);
  int observed = *returned;
  delete owner;
  return observed;
}

// LOWER: Lowered: provenance_branch
// LOWER: Lowered: provenance_call
// LOWER-NOT: Verified:
// VERIFY: Verified: provenance_branch
// VERIFY: Verified: provenance_call

// VCR-LABEL: fn provenance_branch
// VCR: assign __cppverify_pointer_provenance_1
// VCR-NEXT: 0
// VCR: allocate first size 4 align 4 provenance __cppverify_pointer_provenance_1
// VCR: allocate second size 4 align 4 provenance __cppverify_pointer_provenance_2
// VCR: assign __cppverify_pointer_value_1
// VCR-NEXT: first
// VCR-NEXT: assign __cppverify_pointer_provenance_value_1
// VCR-NEXT: __cppverify_pointer_provenance_1
// VCR: if
// VCR: assign __cppverify_pointer_value_2
// VCR-NEXT: second
// VCR-NEXT: assign __cppverify_pointer_provenance_value_2
// VCR-NEXT: __cppverify_pointer_provenance_2
// VCR: load
// VCR-NEXT: alias
// VCR: free
// VCR-NEXT: first
// VCR: free
// VCR-NEXT: second
// VCR-LABEL: fn provenance_call
// VCR: call provenance_identity -> returned provenance __cppverify_pointer_provenance_

// PASSIVE-LABEL: passive provenance_branch
// PASSIVE: __cppverify_pointer_provenance_1_1
// PASSIVE-NEXT: 0
// PASSIVE: __cppverify_pointer_provenance_1_2
// PASSIVE-NEXT: 0
// PASSIVE: __cppverify_pointer_provenance_3_4
// PASSIVE-NEXT: ite
// PASSIVE-NEXT: choose_0
// PASSIVE-NEXT: __cppverify_pointer_provenance_3_3
// PASSIVE-NEXT: __cppverify_pointer_provenance_3_2
// PASSIVE: valid_ptr
// PASSIVE-NEXT: alias_3
// PASSIVE-LABEL: passive provenance_call
// PASSIVE: returned_
// PASSIVE: valid_ptr
// PASSIVE: returned_

// VC-LABEL: vc provenance_branch
// VC: features mathematical-integers, bit-vectors, pointers, heap-arrays
// VC: !
// VC: heap_select
// VC: alias_3 : pointer
// VC: obligations
// VC-LABEL: vc provenance_call
// VC: __cppverify_pointer_provenance_

// Z3-DAG: (select __heap_alloc_used_0
// Z3-DAG: (store __heap_alloc_used_0
// Z3-DAG: (distinct __cppverify_pointer_provenance_3_4 0)
// Z3-DAG: (= (select __heap_alloc_{{[0-9]+}} alias_3)
// Z3-DAG: __cppverify_pointer_provenance_3_4)
// Z3-DAG: (select __heap_live_{{[0-9]+}}
// Z3-DAG: (ite choose_0
// Z3-NOT: error:
