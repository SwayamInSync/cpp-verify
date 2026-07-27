// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void write_allocated(int *target, int value)
  pre(target != nullptr)
  modifies(*target)
  post(*target == value)
{
  *target = value;
}

int read_allocated(const int *source)
  pre(source != nullptr)
  post(result == old(*source))
{
  return *source;
}

bool observe_aliases(int *left, int *right)
  aliases(left, right)
  post(result == (left == right))
{
  return left == right;
}

int pass_scalar_value(int value)
  post(result == value)
{
  return value;
}

int initialized_roundtrip(int value)
  post(result == value)
{
  int *p = new int(value);
  int observed = *p;
  delete p;
  return observed;
}

int stored_roundtrip(int value)
  post(result == value)
{
  int *p = new int;
  *p = value;
  int observed = *p;
  delete p;
  return observed;
}

bool distinct_allocations()
  post(result)
{
  int *p = new int(1);
  int *q = new int(2);
  bool distinct = p != q;
  delete q;
  delete p;
  return distinct;
}

int value_initialized()
  post(result == 0)
{
  int *p = new int();
  int observed = *p;
  delete p;
  return observed;
}

int reuse_after_delete(int value)
  post(result == value)
{
  int *old_object = new int(1);
  delete old_object;
  int *new_object = new int(value);
  int observed = *new_object;
  delete new_object;
  return observed;
}

int branch_initialized(bool choose)
  post(result == 1 || result == 2)
{
  int *p = new int;
  if (choose)
    *p = 1;
  else
    *p = 2;
  int observed = *p;
  delete p;
  return observed;
}

int allocation_after_incrementless_loop(int value)
  post(result == value)
{
  for (int i = 0; false;) {
  }
  int *p = new int(value);
  int observed = *p;
  delete p;
  return observed;
}

bool bool_roundtrip(bool value)
  post(result == value)
{
  bool *p = new bool(value);
  bool observed = *p;
  delete p;
  return observed;
}

enum class ByteState : unsigned char {
  Off,
  On,
};

ByteState enum_roundtrip(ByteState value)
  post(result == value)
{
  const ByteState *p = new ByteState(value);
  ByteState observed = *p;
  delete p;
  return observed;
}

int alias_store_roundtrip(int value)
  post(result == value)
{
  int *owner = new int;
  int *alias = owner;
  *alias = value;
  int observed = *owner;
  delete alias;
  return observed;
}

int const_alias_roundtrip(int value)
  post(result == value)
{
  int *owner = new int(value);
  const int *alias = owner;
  int observed = *alias;
  delete alias;
  return observed;
}

int modular_alias_write(int value)
  post(result == value)
{
  int *owner = new int(0);
  int *alias = owner;
  write_allocated(alias, value);
  int observed = *owner;
  delete owner;
  return observed;
}

int modular_read(int value)
  post(result == value)
{
  int *owner = new int(value);
  int observed = read_allocated(owner);
  delete owner;
  return observed;
}

bool modular_alias_observation()
  post(result)
{
  int *owner = new int(1);
  int *alias = owner;
  bool same = observe_aliases(owner, alias);
  delete owner;
  return same;
}

int modular_loaded_value(int value)
  post(result == value)
{
  int *owner = new int(value);
  int observed = pass_scalar_value(*owner);
  delete owner;
  return observed;
}

int direct_pointer_reassignment(int value)
  post(result == value)
{
  int *first = new int(1);
  int *second = new int(value);
  int *alias = first;
  alias = second;
  int observed = *alias;
  delete first;
  delete alias;
  return observed;
}

int owner_reassignment_preserves_alias(int value)
  post(result == value)
{
  int *owner = new int(value);
  int *alias = owner;
  int *replacement = new int(2);
  owner = replacement;
  int observed = *alias;
  delete alias;
  delete owner;
  return observed;
}

int conditional_pointer_copy(bool choose)
  post(result == 1 || result == 2)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = choose ? first : second;
  int observed = *alias;
  delete first;
  delete second;
  return observed;
}

int branch_pointer_reassignment(bool choose)
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

bool null_pointer_reassignment()
  post(result)
{
  int *owner = new int(1);
  int *alias = owner;
  alias = nullptr;
  delete alias;
  delete owner;
  return alias == nullptr;
}

int conditional_null_pointer(bool choose, int value)
  post(result == 0 || result == value)
{
  int *owner = new int(value);
  int *alias = choose ? owner : nullptr;
  int observed = 0;
  if (alias != nullptr)
    observed = *alias;
  delete owner;
  return observed;
}

int stale_pointer_reassigned_to_fresh_object(int value)
  post(result == value)
{
  int *owner = new int(1);
  int *alias = owner;
  delete owner;
  int *replacement = new int(value);
  alias = replacement;
  int observed = *alias;
  delete alias;
  return observed;
}

int modular_write_after_reassignment(int value)
  post(result == value)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = first;
  alias = second;
  write_allocated(alias, value);
  int observed = *second;
  delete first;
  delete second;
  return observed;
}

int self_referential_conditional_reassignment(int value)
  post(result == value)
{
  int *owner = new int(value);
  int *alias = nullptr;
  alias = alias == nullptr ? owner : nullptr;
  int observed = *alias;
  delete alias;
  return observed;
}

int branch_assignment_from_null(bool choose, int value)
  post(result == 0 || result == value)
{
  int *owner = new int(value);
  int *alias = nullptr;
  if (choose)
    alias = owner;
  int observed = 0;
  if (alias != nullptr)
    observed = *alias;
  delete owner;
  return observed;
}

int delete_null_preserves_liveness(int value)
  post(result == value)
{
  int *owner = new int(value);
  int *alias = owner;
  alias = nullptr;
  delete alias;
  int observed = *owner;
  delete owner;
  return observed;
}

int branch_order_independent_provenance(bool choose, int value)
  post(result == value)
{
  int *owner = new int(value);
  int *alias = nullptr;
  if (choose)
    delete alias;
  else
    alias = owner;
  int observed = *owner;
  delete owner;
  return observed;
}

// VERIFY-DAG: Verified: write_allocated
// VERIFY-DAG: Verified: read_allocated
// VERIFY-DAG: Verified: observe_aliases
// VERIFY-DAG: Verified: pass_scalar_value
// VERIFY-DAG: Verified: initialized_roundtrip
// VERIFY-DAG: Verified: stored_roundtrip
// VERIFY-DAG: Verified: distinct_allocations
// VERIFY-DAG: Verified: value_initialized
// VERIFY-DAG: Verified: reuse_after_delete
// VERIFY-DAG: Verified: branch_initialized
// VERIFY-DAG: Verified: allocation_after_incrementless_loop
// VERIFY-DAG: Verified: bool_roundtrip
// VERIFY-DAG: Verified: enum_roundtrip
// VERIFY-DAG: Verified: alias_store_roundtrip
// VERIFY-DAG: Verified: const_alias_roundtrip
// VERIFY-DAG: Verified: modular_alias_write
// VERIFY-DAG: Verified: modular_read
// VERIFY-DAG: Verified: modular_alias_observation
// VERIFY-DAG: Verified: modular_loaded_value
// VERIFY-DAG: Verified: direct_pointer_reassignment
// VERIFY-DAG: Verified: owner_reassignment_preserves_alias
// VERIFY-DAG: Verified: conditional_pointer_copy
// VERIFY-DAG: Verified: branch_pointer_reassignment
// VERIFY-DAG: Verified: null_pointer_reassignment
// VERIFY-DAG: Verified: conditional_null_pointer
// VERIFY-DAG: Verified: stale_pointer_reassigned_to_fresh_object
// VERIFY-DAG: Verified: modular_write_after_reassignment
// VERIFY-DAG: Verified: self_referential_conditional_reassignment
// VERIFY-DAG: Verified: branch_assignment_from_null
// VERIFY-DAG: Verified: delete_null_preserves_liveness
// VERIFY-DAG: Verified: branch_order_independent_provenance
