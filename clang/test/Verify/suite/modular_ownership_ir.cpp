// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=LEAN

int *ownership_factory(int value)
  post(result != nullptr)
  post(*result == value)
{
  int *owner = new int(value);
  return owner;
}

int *ownership_forward(int value)
  post(result != nullptr)
  post(*result == value)
{
  return ownership_factory(value);
}

int ownership_consume(int value)
  post(result == value)
{
  int *owner = ownership_forward(value);
  int observed = *owner;
  delete owner;
  return observed;
}

// VCR-LABEL: fn ownership_factory
// VCR: fresh_owned_return size 4 align 4
// VCR: allocate owner size 4 align 4 provenance
// VCR: return
// VCR-NEXT: owner
// VCR-LABEL: fn ownership_forward
// VCR: fresh_owned_return size 4 align 4
// VCR: call ownership_factory -> __return_call_1 provenance __return_call_provenance_1
// VCR: return
// VCR-NEXT: __return_call_1
// VCR-LABEL: fn ownership_consume
// VCR: call ownership_forward -> owner provenance
// VCR: free
// VCR-NEXT: owner

// PASSIVE-LABEL: passive ownership_forward
// PASSIVE: __return_call_provenance_1_1
// PASSIVE: heap_store __heap_alloc_used_0 -> __heap_alloc_used_1
// PASSIVE: heap_store __heap_alloc_0 -> __heap_alloc_1
// PASSIVE: heap_store __heap_alloc_base_0 -> __heap_alloc_base_1
// PASSIVE: heap_store __heap_alloc_size_0 -> __heap_alloc_size_1
// PASSIVE: heap_store __heap_alloc_align_0 -> __heap_alloc_align_1
// PASSIVE: heap_store __heap_live_0 -> __heap_live_1
// PASSIVE: heap_store __heap_0 -> __heap_1
// PASSIVE: __owned_call_value_
// PASSIVE: heap_store __heap_init_0 -> __heap_init_1
// PASSIVE-LABEL: passive ownership_consume
// PASSIVE: heap_store __heap_alloc_used_0 -> __heap_alloc_used_1
// PASSIVE: __owned_call_value_
// PASSIVE: valid_ptr
// PASSIVE: initialized_ptr
// PASSIVE: __heap_live_

// VC-LABEL: vc ownership_forward
// VC: features mathematical-integers, bit-vectors, pointers, heap-arrays
// VC: __heap_alloc_used_
// VC: __heap_alloc_
// VC: __heap_live_
// VC: __heap_init_
// VC: __owned_call_value_
// VC-LABEL: vc ownership_consume
// VC: __owned_call_value_
// VC: obligations

// Z3: (select __heap_alloc_used_0
// Z3: (store __heap_alloc_used_0
// Z3: (store __heap_alloc_0
// Z3: (store __heap_alloc_base_0
// Z3: (store __heap_alloc_size_0
// Z3: (store __heap_alloc_align_0
// Z3: (store __heap_live_0
// Z3: (store __heap_init_0
// Z3: __owned_call_value_
// Z3: Lowered: ownership_factory
// Z3: Lowered: ownership_forward
// Z3: Lowered: ownership_consume

// LEAN-DAG: Exported: lean obligation: ownership_factory
// LEAN-DAG: Exported: lean obligation: ownership_forward
// LEAN-DAG: Exported: lean obligation: ownership_consume
