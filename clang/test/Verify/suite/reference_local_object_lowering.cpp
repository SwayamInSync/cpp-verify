// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

// Whole-object promotion: a local record whose field is bound by reference (or
// passed to a reference formal) becomes one automatic byte-addressed object.
// It keeps no flattened SSA companion, so every read and write is a heap
// access at the field's exact target byte offset.

struct Pair {
  int first;
  int second;
};

struct Inner {
  int lo;
  int hi;
};

struct Outer {
  Inner inner;
  int tag;
};

struct WithPtr {
  int value;
  int *link;
};

int read_first(Pair *p)
  pre(p != nullptr && p->first == 1)
  post(result == 1)
{
  return p->first;
}

void set_scalar(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int field_reference_binding()
  post(result == 7)
{
  Pair value{1, 2};
  int &alias = value.second;
  alias = 7;
  return value.second;
}

int modular_field_argument()
  post(result == 9)
{
  Pair value{1, 2};
  set_scalar(value.first, 9);
  return value.first;
}

int sibling_field_unchanged()
  post(result == 1)
{
  Pair value{1, 2};
  int &alias = value.second;
  alias = 7;
  return value.first;
}

int nested_field_binding()
  post(result == 5)
{
  Outer o{{1, 2}, 3};
  int &alias = o.inner.hi;
  alias = 5;
  return o.inner.hi;
}

int nested_siblings_unchanged()
  post(result == 4)
{
  Outer o{{1, 2}, 3};
  set_scalar(o.inner.hi, 5);
  return o.inner.lo + o.tag;
}

int value_initialized_record()
  post(result == 0)
{
  Pair value{};
  int &alias = value.first;
  return alias + value.second;
}

// The copy must read the promoted source's current storage, leaf by leaf.
int leafwise_copy()
  post(result == 7)
{
  Pair source{2, 3};
  int &alias = source.first;
  alias = 4;
  Pair copy = source;
  return copy.first + copy.second;
}

// A stale flattened companion would answer 2 here; the single representation
// must observe the store performed through the callee's reference formal.
int stale_dual_representation()
  post(result == 2)
{
  Pair value{1, 2};
  set_scalar(value.second, 7);
  return value.second;
}

// A pointer field is an ordinary leaf: the stored value round-trips exactly
// through the heap, and nothing else about it is assumed.
int pointer_leaf_roundtrip(int *q)
  pre(q != nullptr)
  post(result == 4)
{
  WithPtr w{4, q};
  int &alias = w.value;
  return alias;
}

// An unwritten pointer leaf stays uninitialized: its validity is never
// assumed, so dereferencing it cannot be proven.
int unwritten_pointer_leaf()
  post(result == 0)
{
  WithPtr w;
  int &alias = w.value;
  alias = 1;
  return *w.link;
}

// A heap-loaded pointer leaf is an unconstrained pointer value: the pointee
// it designates is not known.
int pointer_leaf_pointee_unknown(int *q)
  pre(q != nullptr)
  post(result == 0)
{
  WithPtr w{4, q};
  int &alias = w.value;
  return *w.link;
}

int false_sibling_changed()
  post(result == 7)
{
  Pair value{1, 2};
  int &alias = value.second;
  alias = 7;
  return value.first;
}

int uninitialized_field_binding()
  post(result == 0)
{
  Pair value;
  int &alias = value.first;
  return alias;
}

int uninitialized_sibling_read()
  post(result == 3)
{
  Pair value;
  int &alias = value.first;
  alias = 3;
  return value.first + value.second;
}

// VERIFY-DAG: Verified: set_scalar
// VERIFY-DAG: Verified: field_reference_binding
// VERIFY-DAG: Verified: modular_field_argument
// VERIFY-DAG: Verified: sibling_field_unchanged
// VERIFY-DAG: Verified: nested_field_binding
// VERIFY-DAG: Verified: nested_siblings_unchanged
// VERIFY-DAG: Verified: value_initialized_record
// VERIFY-DAG: Verified: leafwise_copy
// VERIFY-DAG: Verified: pointer_leaf_roundtrip
// VERIFY-DAG: error: verification failed: unwritten_pointer_leaf
// VERIFY-DAG: error: verification failed: pointer_leaf_pointee_unknown
// VERIFY-DAG: error: verification failed: stale_dual_representation
// VERIFY-DAG: error: verification failed: false_sibling_changed
// VERIFY-DAG: error: verification failed: uninitialized_field_binding
// VERIFY-DAG: error: verification failed: uninitialized_sibling_read

// One allocation for the whole record, then one ordinary scalar store per
// initialized leaf at its exact offset. No aggregate initializer value and no
// flattened `value.first` assignment survive.
// VCR-LABEL: fn field_reference_binding
// VCR: stack_allocate value size 8 align 4 provenance
// VCR-NEXT: store
// VCR-NEXT: value
// VCR-NEXT: 1
// VCR-NEXT: store
// VCR-NEXT: +
// VCR-NEXT: value
// VCR-NEXT: 4
// VCR-NEXT: 2
// VCR-NOT: assign value.
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: value
// VCR-NEXT: 4
// VCR: store
// VCR-NEXT: alias
// VCR-NEXT: 7
// VCR: return
// VCR-NEXT: load
// VCR-NEXT: +
// VCR-NEXT: value
// VCR-NEXT: 4

// VCR-LABEL: fn modular_field_argument
// VCR: call set_scalar
// VCR-NEXT: +
// VCR-NEXT: value
// VCR-NEXT: 0
// VCR-NEXT: 9

// Nested records keep exact offsets: Outer::inner::hi is at byte 4.
// VCR-LABEL: fn nested_field_binding
// VCR: stack_allocate o size 12 align 4 provenance
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: o
// VCR-NEXT: 4

// PASSIVE-LABEL: passive field_reference_binding
// PASSIVE: alias_1
// PASSIVE-NEXT: +
// PASSIVE-NEXT: value_1
// PASSIVE-NEXT: 4
// PASSIVE: heap_store

// VC-LABEL: vc field_reference_binding
// VC: alias_1 : pointer
// VC-NEXT: + : pointer
// VC-NEXT: value_1 : pointer
// VC-NEXT: 4 : pointer
// VC: heap_store : bool
// VC-NOT: value.first

// Z3-DAG: (= alias_1 (+ value_1 4))
// Z3-DAG: (select __heap_init_
// Z3-NOT: unsupported

// BMC-DAG: Verified: field_reference_binding
// BMC-DAG: Verified: modular_field_argument
// BMC-DAG: Verified: sibling_field_unchanged
// BMC-DAG: Verified: nested_field_binding
// BMC-DAG: Verified: nested_siblings_unchanged
// BMC-DAG: Verified: value_initialized_record
// BMC-DAG: Verified: leafwise_copy
// BMC-DAG: Verified: pointer_leaf_roundtrip
// BMC-DAG: error: verification failed: unwritten_pointer_leaf
// BMC-DAG: error: verification failed: pointer_leaf_pointee_unknown
// BMC-DAG: error: verification failed: stale_dual_representation
// BMC-DAG: error: verification failed: false_sibling_changed
// BMC-DAG: error: verification failed: uninitialized_field_binding
// BMC-DAG: error: verification failed: uninitialized_sibling_read
