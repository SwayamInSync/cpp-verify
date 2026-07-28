// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

struct Pair {
  int first;
  int second;
};

spec bool valid(int *p, int count) { return true; }

void set_scalar(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

void local_arrow_alias(Pair *p, int value)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies(p->second)
  post(p->first == 1 && p->second == value)
{
  int &alias = p->second;
  alias = value;
}

void local_deref_field_alias(Pair *p, int value)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies((*p).first)
  post((*p).first == value && (*p).second == 2)
{
  int &alias = (*p).first;
  alias = value;
}

void local_field_alias_in_region(Pair *p, int value)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies(*p)
  post(p->first == 1 && p->second == value)
{
  int &alias = p->second;
  alias = value;
}

void local_element_alias(int *p, int count, int index, int value)
  pre(p != nullptr && valid(p, count) && 0 <= index && index < count &&
      p[index] == 3)
  modifies(p[index])
  post(p[index] == value)
{
  int &alias = p[index];
  alias = value;
}

void call_arrow_field(Pair *p, int value)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies(p->second)
  post(p->first == 1 && p->second == value)
{
  set_scalar(p->second, value);
}

void call_deref_field(Pair *p, int value)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies((*p).first)
  post((*p).first == value && (*p).second == 2)
{
  set_scalar((*p).first, value);
}

void call_element(int *p, int count, int index, int value)
  pre(p != nullptr && valid(p, count) && 0 <= index && index < count &&
      p[index] == 3)
  modifies(p[index])
  post(p[index] == value)
{
  set_scalar(p[index], value);
}

int unchecked_element_alias(int *p, int index)
  pre(p != nullptr)
{
  int &alias = p[index];
  return alias;
}

int out_of_range_element_alias(int *p, int count)
  pre(p != nullptr && valid(p, count) && count >= 0)
{
  int &alias = p[count];
  return alias;
}

void invalid_frame(Pair *p)
  pre(p != nullptr && p->first == 1 && p->second == 2)
  modifies(p->first)
{
  set_scalar(p->second, 7);
}

// VERIFY-DAG: Verified: set_scalar
// VERIFY-DAG: Verified: local_arrow_alias
// VERIFY-DAG: Verified: local_deref_field_alias
// VERIFY-DAG: Verified: local_field_alias_in_region
// VERIFY-DAG: Verified: local_element_alias
// VERIFY-DAG: Verified: call_arrow_field
// VERIFY-DAG: Verified: call_deref_field
// VERIFY-DAG: Verified: call_element
// VERIFY-DAG: error: verification failed: unchecked_element_alias
// VERIFY-DAG: error: verification failed: out_of_range_element_alias
// VERIFY-DAG: error: verification failed: invalid_frame

// VCR-LABEL: fn local_arrow_alias
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: 4
// VCR-NEXT: store
// VCR-NEXT: alias
// VCR-NEXT: value
// VCR-LABEL: fn local_deref_field_alias
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: 0
// VCR-NEXT: store
// VCR-NEXT: alias
// VCR-NEXT: value
// VCR-LABEL: fn local_element_alias
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: index
// VCR-NEXT: 4
// VCR-NEXT: store
// VCR-NEXT: alias
// VCR-NEXT: value
// VCR-LABEL: fn call_arrow_field
// VCR: call set_scalar
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: 4
// VCR-NEXT: value
// VCR-LABEL: fn call_deref_field
// VCR: call set_scalar
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: 0
// VCR-NEXT: value
// VCR-LABEL: fn call_element
// VCR: call set_scalar
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: index
// VCR-NEXT: 4
// VCR-NEXT: value

// PASSIVE-LABEL: passive local_arrow_alias
// PASSIVE: alias_1
// PASSIVE-NEXT: +
// PASSIVE-NEXT: p_0
// PASSIVE-NEXT: 4
// PASSIVE: heap_store
// PASSIVE-LABEL: passive local_deref_field_alias
// PASSIVE-LABEL: passive local_element_alias
// PASSIVE: alias_1
// PASSIVE-NEXT: +
// PASSIVE-NEXT: p_0
// PASSIVE-NEXT: *
// PASSIVE-NEXT: cast
// PASSIVE-NEXT: index_0
// PASSIVE-NEXT: 4
// PASSIVE: heap_store

// VC-LABEL: vc local_arrow_alias
// VC: alias_1 : pointer
// VC-NEXT: + : pointer
// VC-NEXT: p_0 : pointer
// VC-NEXT: 4 : pointer
// VC: heap_store : bool
// VC-NEXT: __heap_0 : heap
// VC-NEXT: alias_1 : pointer
// VC-NEXT: value_0 : bitvector32
// VC-NEXT: __heap_1 : heap
// VC-LABEL: vc local_element_alias
// VC: alias_1 : pointer
// VC-NEXT: + : pointer
// VC-NEXT: p_0 : pointer
// VC-NEXT: * : int
// VC-NEXT: bv_to_int : int
// VC-NEXT: index_0 : bitvector32
// VC-NEXT: 4 : int
// VC: heap_store : bool
// VC-NEXT: __heap_0 : heap
// VC-NEXT: alias_1 : pointer
// VC-NEXT: value_0 : bitvector32
// VC-NEXT: __heap_1 : heap

// Z3-DAG: (= alias_1 (+ p_0 4))
// Z3-DAG: (select __heap_0 (+ p_0 4))
// Z3-DAG: (= __heap_1 (store __heap_0 alias_1 (bv2int value_0)))
// Z3-DAG: (a!1 (* (ite (bvslt index_0 #x00000000)
// Z3-DAG: (= alias_1 (+ p_0 a!1))
// Z3-DAG: (select __heap_1 (+ p_0 a!1))
// Z3-NOT: unsupported

// BMC-DAG: Verified: set_scalar
// BMC-DAG: Verified: local_arrow_alias
// BMC-DAG: Verified: local_deref_field_alias
// BMC-DAG: Verified: local_field_alias_in_region
// BMC-DAG: Verified: local_element_alias
// BMC-DAG: Verified: call_arrow_field
// BMC-DAG: Verified: call_deref_field
// BMC-DAG: Verified: call_element
// BMC-DAG: error: verification failed: unchecked_element_alias
// BMC-DAG: error: verification failed: out_of_range_element_alias
// BMC-DAG: error: verification failed: invalid_frame
