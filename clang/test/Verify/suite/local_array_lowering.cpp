// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

// A fixed local array is always one automatic byte-addressed object: it has no
// flattened SSA form at all. Element places are exact `base + index * stride`
// addresses, and the allocation extent gives every access an exact bound.

struct Pair {
  int first;
  int second;
};

struct ArrayAndTag {
  int values[3];
  int tag;
};

struct PairArrayAndTail {
  Pair values[1];
  Pair tail;
};

struct PointerBox {
  int tag;
  int *pointer;
};

int *external_pointer()
  post(result != nullptr);

void set_scalar(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int element_reference_binding(int index)
  pre(index >= 0 && index < 4)
  post(result == 7)
{
  int a[4] = {1, 2, 3, 4};
  int &alias = a[index];
  alias = 7;
  return a[index];
}

int modular_element_argument(int index)
  pre(index >= 0 && index < 4)
  post(result == 9)
{
  int a[4] = {1, 2, 3, 4};
  set_scalar(a[index], 9);
  return a[index];
}

int other_element_unchanged()
  post(result == 3)
{
  int a[4] = {1, 2, 3, 4};
  a[1] = 9;
  return a[2];
}

int partially_initialized_array()
  post(result == 3)
{
  int a[4] = {1, 2};
  return a[0] + a[1] + a[2] + a[3];
}

int zero_initialized_array()
  post(result == 0)
{
  int a[4] = {};
  return a[0] + a[3];
}

int array_of_records(int index)
  pre(index >= 0 && index < 2)
  post(result == 8)
{
  Pair a[2] = {{1, 2}, {3, 4}};
  int &alias = a[index].second;
  alias = 8;
  return a[index].second;
}

int nested_array(int index)
  pre(index >= 0 && index < 2)
  post(result == 9)
{
  int m[2][3] = {{1, 2, 3}, {4, 5, 6}};
  int &alias = m[index][2];
  alias = 9;
  return m[index][2];
}

int skipped_conditional_access(bool take, int index)
  pre(!take && index == 4)
  post(result == 0)
{
  int a[4] = {1, 2, 3, 4};
  return take ? a[index] : 0;
}

bool skipped_and_access(bool take, int index)
  pre(!take && index == 4)
  post(!result)
{
  int a[4] = {1, 2, 3, 4};
  return take && a[index] == 1;
}

bool skipped_or_access(bool skip, int index)
  pre(skip && index == 4)
  post(result)
{
  int a[4] = {1, 2, 3, 4};
  return skip || a[index] == 1;
}

int false_other_element_changed()
  post(result == 9)
{
  int a[4] = {1, 2, 3, 4};
  a[1] = 9;
  return a[2];
}

int false_bad_result()
  post(result == 8)
{
  int a[4] = {1, 2, 3, 4};
  a[1] = 9;
  return a[1];
}

int out_of_bounds_symbolic_index(int index)
  pre(index >= 0)
  post(result == 1)
{
  int a[4] = {1, 1, 1, 1};
  return a[index];
}

int uninitialized_element_read()
  post(result == 0)
{
  int a[4];
  a[0] = 0;
  return a[2];
}

int uninitialized_element_binding()
  post(result == 0)
{
  int a[4];
  int &alias = a[1];
  return alias;
}

// These accesses would alias sibling storage if their declared subarray bounds
// were replaced by the containing allocation's byte extent.
int conditional_array_field_alias(bool take, int index)
  pre(take && index == 3)
  post(result == 9)
{
  ArrayAndTag value{{1, 2, 3}, 9};
  return take ? value.values[index] : 0;
}

bool short_circuit_and_array_field_alias(bool take, int index)
  pre(take && index == 3)
  post(result)
{
  ArrayAndTag value{{1, 2, 3}, 9};
  return take && value.values[index] == 9;
}

bool short_circuit_or_array_field_alias(bool skip, int index)
  pre(!skip && index == 3)
  post(result)
{
  ArrayAndTag value{{1, 2, 3}, 9};
  return skip || value.values[index] == 9;
}

int conditional_inner_array_alias(bool take, int row, int column)
  pre(take && row == 0 && column == 3)
  post(result == 4)
{
  int matrix[2][3] = {{1, 2, 3}, {4, 5, 6}};
  return take ? matrix[row][column] : 0;
}

int aggregate_copy_sibling_alias(int index)
  pre(index == 1)
  post(result == 9)
{
  PairArrayAndTail value{{{1, 2}}, {8, 9}};
  Pair copy = value.values[index];
  return copy.second;
}

int aggregate_assignment_sibling_alias(int index)
  pre(index == 1)
  post(result == 9)
{
  PairArrayAndTail value{{{1, 2}}, {8, 9}};
  Pair replacement{4, 5};
  value.values[index] = replacement;
  return value.tail.second;
}

int loop_condition_array_alias(int index)
  pre(index == 3)
  post(result == 9)
{
  ArrayAndTag value{{1, 2, 3}, 9};
  int observed = 0;
  while (observed == 0 && value.values[index] == 9)
    invariant(observed == 0 || observed == 9)
    invariant(value.tag == 9)
    decreases(observed == 0 ? 1 : 0)
  {
    observed = 9;
  }
  return observed;
}

bool stored_one_past_allows_adjacent_allocation()
  post(result)
{
  int *pointer = external_pointer();
  PointerBox saved{0, pointer + 1};
  int &promote = saved.tag;
  promote = 1;
  pointer = nullptr;
  int *fresh = new int(0);
  bool distinct = saved.pointer != fresh;
  delete fresh;
  return distinct;
}

// VERIFY-DAG: Verified: set_scalar
// VERIFY-DAG: Verified: element_reference_binding
// VERIFY-DAG: Verified: modular_element_argument
// VERIFY-DAG: Verified: other_element_unchanged
// VERIFY-DAG: Verified: partially_initialized_array
// VERIFY-DAG: Verified: zero_initialized_array
// VERIFY-DAG: Verified: array_of_records
// VERIFY-DAG: Verified: nested_array
// VERIFY-DAG: Verified: skipped_conditional_access
// VERIFY-DAG: Verified: skipped_and_access
// VERIFY-DAG: Verified: skipped_or_access
// VERIFY-DAG: error: verification failed: false_other_element_changed
// VERIFY-DAG: error: verification failed: false_bad_result
// VERIFY-DAG: error: verification failed: out_of_bounds_symbolic_index
// VERIFY-DAG: error: verification failed: uninitialized_element_read
// VERIFY-DAG: error: verification failed: uninitialized_element_binding
// VERIFY-DAG: error: verification failed: conditional_array_field_alias
// VERIFY-DAG: error: verification failed: short_circuit_and_array_field_alias
// VERIFY-DAG: error: verification failed: short_circuit_or_array_field_alias
// VERIFY-DAG: error: verification failed: conditional_inner_array_alias
// VERIFY-DAG: error: verification failed: aggregate_copy_sibling_alias
// VERIFY-DAG: error: verification failed: aggregate_assignment_sibling_alias
// VERIFY-DAG: error: verification failed: loop_condition_array_alias
// VERIFY-DAG: error: verification failed: stored_one_past_allows_adjacent_allocation

// One allocation for the whole array, one scalar store per initialized
// element, and an unconditional constant bound assertion on the symbolic
// index. No flattened array value exists.
// VCR-LABEL: fn element_reference_binding
// VCR: stack_allocate a size 16 align 4 provenance
// VCR-NEXT: store
// VCR-NEXT: a
// VCR-NEXT: 1
// VCR-NEXT: store
// VCR-NEXT: +
// VCR-NEXT: a
// VCR-NEXT: 4
// VCR-NEXT: 2
// VCR: assert
// VCR-NEXT: &&
// VCR-NEXT: >=
// VCR-NEXT: index
// VCR-NEXT: 0
// VCR-NEXT: <
// VCR-NEXT: index
// VCR-NEXT: 4
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: a
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: index
// VCR-NEXT: 4
// VCR-NOT: assign a

// Missing trailing initializers are value-initialized leaves, not holes.
// VCR-LABEL: fn partially_initialized_array
// VCR: stack_allocate a size 16 align 4 provenance
// VCR-COUNT-4: store

// Nested arrays keep the outer stride exactly.
// VCR-LABEL: fn nested_array
// VCR: stack_allocate m size 24 align 4 provenance
// VCR: assign alias
// VCR-NEXT: +
// VCR-NEXT: +
// VCR-NEXT: m
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: index
// VCR-NEXT: 12
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: 2
// VCR-NEXT: 4

// PASSIVE-LABEL: passive element_reference_binding
// PASSIVE: alias_1
// PASSIVE-NEXT: +
// PASSIVE-NEXT: a_1
// PASSIVE-NEXT: *
// PASSIVE-NEXT: cast
// PASSIVE-NEXT: index_0
// PASSIVE-NEXT: 4
// PASSIVE: heap_store

// VC-LABEL: vc element_reference_binding
// VC: alias_1 : pointer
// VC-NEXT: + : pointer
// VC-NEXT: a_1 : pointer
// VC-NEXT: * : int
// VC-NEXT: bv_to_int : int
// VC-NEXT: index_0 : bitvector32
// VC-NEXT: 4 : int
// VC: heap_store : bool

// Z3-DAG: (= alias_1 (+ a_1 a!
// Z3-NOT: unsupported

// BMC-DAG: Verified: element_reference_binding
// BMC-DAG: Verified: modular_element_argument
// BMC-DAG: Verified: other_element_unchanged
// BMC-DAG: Verified: partially_initialized_array
// BMC-DAG: Verified: zero_initialized_array
// BMC-DAG: Verified: array_of_records
// BMC-DAG: Verified: nested_array
// BMC-DAG: Verified: skipped_conditional_access
// BMC-DAG: Verified: skipped_and_access
// BMC-DAG: Verified: skipped_or_access
// BMC-DAG: error: verification failed: false_other_element_changed
// BMC-DAG: error: verification failed: false_bad_result
// BMC-DAG: error: verification failed: out_of_bounds_symbolic_index
// BMC-DAG: error: verification failed: uninitialized_element_read
// BMC-DAG: error: verification failed: uninitialized_element_binding
// BMC-DAG: error: verification failed: conditional_array_field_alias
// BMC-DAG: error: verification failed: short_circuit_and_array_field_alias
// BMC-DAG: error: verification failed: short_circuit_or_array_field_alias
// BMC-DAG: error: verification failed: conditional_inner_array_alias
// BMC-DAG: error: verification failed: aggregate_copy_sibling_alias
// BMC-DAG: error: verification failed: aggregate_assignment_sibling_alias
// BMC-DAG: error: verification failed: loop_condition_array_alias
// BMC-DAG: error: verification failed: stored_one_past_allows_adjacent_allocation
