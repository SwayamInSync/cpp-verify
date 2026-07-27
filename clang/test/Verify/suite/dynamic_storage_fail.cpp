// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int read_allocated(const int *source)
  pre(source != nullptr)
  post(result == old(*source))
{
  return *source;
}

int *pointer_identity(int *value)
  pre(value != nullptr)
  post(result == value)
  post(*result == old(*value))
{
  return value;
}

bool require_distinct(int *left, int *right)
  post(result)
{
  return left != right;
}

int read_next(const int *source)
  post(result == old(source[1]))
{
  return source[1];
}

int external_read(const int *source)
  pre(source != nullptr)
  post(result == old(*source));

void rebind_pointer(int *target)
  post(target == nullptr)
{
  target = nullptr;
}

int offset_precondition(const int *source)
  pre((source + 1) == (source + 1))
  post(result == old(*source))
{
  return *source;
}

int scalar_identity(int value)
  post(result == value)
{
  return value;
}

int forward_loaded_scalar(const int *source)
  post(result == old(*source))
{
  return scalar_identity(*source);
}

int forward_saved_scalar(const int *source)
  post(result == old(*source))
{
  int saved = *source;
  return scalar_identity(saved);
}

int forward_controlled_scalar(const int *source)
  post(true)
{
  int selected = 0;
  if (*source != 0)
    selected = 1;
  return scalar_identity(selected);
}

spec int spec_identity(int value)
{
  return value;
}

int forward_loaded_spec(const int *source)
  post(result == old(*source))
{
  return spec_identity(*source);
}

proof void pointer_lemma(const int *source)
  pre(source != nullptr)
  post(true)
{
}

int *copied_pointer(int *source)
  pre(source != nullptr)
  post(result == source)
{
  int *copy = source;
  return copy;
}

int unsafe_forwarded_read(const int *source)
  pre(source != nullptr)
  post(result == old(source[1]))
{
  return read_next(source);
}

void discard_pointer_result(int *source)
  pre(source != nullptr)
  post(true)
{
  pointer_identity(source);
}

int use_after_delete()
  post(true)
{
  int *p = new int(1);
  delete p;
  return *p;
}

int double_delete()
  post(true)
{
  int *p = new int(1);
  delete p;
  delete p;
  return 0;
}

int uninitialized_read()
  post(true)
{
  int *p = new int;
  return *p;
}

bool simultaneous_allocations_are_equal()
  post(result)
{
  int *p = new int(1);
  int *q = new int(2);
  bool equal = p == q;
  delete q;
  delete p;
  return equal;
}

int path_sensitive_double_delete(bool twice)
  post(true)
{
  int *p = new int(1);
  if (twice)
    delete p;
  if (twice)
    delete p;
  return 0;
}

int path_sensitive_uninitialized_read(bool initialize)
  post(true)
{
  int *p = new int;
  if (initialize)
    *p = 1;
  return *p;
}

int stale_pointer_after_reuse()
  post(true)
{
  int *old_pointer = new int(1);
  delete old_pointer;
  int *replacement = new int(2);
  int observed = 0;
  if (old_pointer == replacement)
    observed = *old_pointer;
  delete replacement;
  return observed;
}

int alias_use_after_delete()
  post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  delete alias;
  return *owner;
}

int alias_double_delete()
  post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  delete alias;
  delete owner;
  return 0;
}

bool aliases_are_distinct()
  post(result)
{
  int *owner = new int(1);
  int *alias = owner;
  bool distinct = owner != alias;
  delete owner;
  return distinct;
}

int modular_uninitialized_read()
  post(true)
{
  int *owner = new int;
  int observed = read_allocated(owner);
  delete owner;
  return observed;
}

int modular_use_after_delete()
  post(true)
{
  int *owner = new int(1);
  delete owner;
  return read_allocated(owner);
}

int modular_nonalias_violation()
  post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  bool distinct = require_distinct(owner, alias);
  delete owner;
  return distinct;
}

int modular_scalar_extent_violation()
  post(true)
{
  int *owner = new int(1);
  int observed = read_next(owner);
  delete owner;
  return observed;
}

int modular_external_contract()
  post(true)
{
  int *owner = new int(1);
  int observed = external_read(owner);
  delete owner;
  return observed;
}

int modular_rebinding_false_proof()
  post(result == 2)
{
  int *owner = new int(1);
  rebind_pointer(owner);
  delete owner;
  return 1;
}

int modular_offset_precondition()
  post(true)
{
  int *owner = new int(1);
  int observed = offset_precondition(owner);
  delete owner;
  return observed;
}

int modular_forwarded_scalar()
  post(true)
{
  int *owner = new int(1);
  int observed = forward_loaded_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_temporary()
  post(true)
{
  int *owner = new int(1);
  int observed = forward_saved_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_control()
  post(true)
{
  int *owner = new int(1);
  int observed = forward_controlled_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_spec()
  post(true)
{
  int *owner = new int(1);
  int observed = forward_loaded_spec(owner);
  delete owner;
  return observed;
}

int modular_proof_call()
  post(true)
{
  int *owner = new int(1);
  pointer_lemma(owner);
  delete owner;
  return 0;
}

int branch_reassignment_use_after_delete(bool choose)
  post(true)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = first;
  if (choose)
    alias = second;
  delete first;
  return *alias;
}

int reassigned_alias_double_delete()
  post(true)
{
  int *first = new int(1);
  int *second = new int(2);
  int *alias = first;
  alias = second;
  delete alias;
  delete second;
  return 0;
}

int stale_alias_after_owner_reassignment()
  post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  int *replacement = new int(2);
  owner = replacement;
  delete alias;
  return *alias;
}

int copied_stale_pointer()
  post(true)
{
  int *owner = new int(1);
  delete owner;
  int *alias = owner;
  return *alias;
}

int null_reassignment_dereference()
  post(true)
{
  int *owner = new int(1);
  owner = nullptr;
  return *owner;
}

int returned_pointer_use_after_delete()
  post(true)
{
  int *owner = new int(1);
  int *returned = pointer_identity(owner);
  delete owner;
  return *returned;
}

int modular_copied_pointer_return()
  post(true)
{
  int *owner = new int(1);
  int *returned = copied_pointer(owner);
  int observed = *returned;
  delete owner;
  return observed;
}

int modular_unsafe_forwarding()
  post(true)
{
  int *owner = new int(1);
  int observed = unsafe_forwarded_read(owner);
  delete owner;
  return observed;
}

int modular_discarded_pointer_forwarding()
  post(true)
{
  int *owner = new int(1);
  discard_pointer_result(owner);
  delete owner;
  return 0;
}

// VERIFY-DAG: error: verification failed: use_after_delete
// VERIFY-DAG: error: verification failed: double_delete
// VERIFY-DAG: error: verification failed: uninitialized_read
// VERIFY-DAG: error: verification failed: simultaneous_allocations_are_equal
// VERIFY-DAG: error: verification failed: path_sensitive_double_delete
// VERIFY-DAG: error: verification failed: path_sensitive_uninitialized_read
// VERIFY-DAG: error: verification failed: stale_pointer_after_reuse
// VERIFY-DAG: error: verification failed: alias_use_after_delete
// VERIFY-DAG: error: verification failed: alias_double_delete
// VERIFY-DAG: error: verification failed: aliases_are_distinct
// VERIFY-DAG: error: verification failed: modular_uninitialized_read
// VERIFY-DAG: error: verification failed: modular_use_after_delete
// VERIFY-DAG: error: verification failed: modular_nonalias_violation
// VERIFY-DAG: error: verification failed: modular_scalar_extent_violation
// VERIFY-DAG: error: verification failed: modular_external_contract
// VERIFY-DAG: error: verification failed: modular_rebinding_false_proof
// VERIFY-DAG: error: verification failed: modular_offset_precondition
// VERIFY-DAG: error: verification failed: branch_reassignment_use_after_delete
// VERIFY-DAG: error: verification failed: reassigned_alias_double_delete
// VERIFY-DAG: error: verification failed: stale_alias_after_owner_reassignment
// VERIFY-DAG: error: verification failed: copied_stale_pointer
// VERIFY-DAG: error: verification failed: null_reassignment_dereference
// VERIFY-DAG: error: verification failed: modular_proof_call
// VERIFY-DAG: error: verification failed: returned_pointer_use_after_delete
// VERIFY-DAG: error: verification failed: modular_copied_pointer_return
// VERIFY-DAG: error: verification failed: modular_unsafe_forwarding
// VERIFY-DAG: error: verification failed: modular_discarded_pointer_forwarding
