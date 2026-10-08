// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int read_allocated(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == cppverify::old(*source))
{
  return *source;
}

int *pointer_identity(int *value)
  cppverify::pre(value != nullptr)
  cppverify::post(cppverify::result == value)
  cppverify::post(*cppverify::result == cppverify::old(*value))
{
  return value;
}

bool require_distinct(int *left, int *right)
  cppverify::post(cppverify::result)
{
  return left != right;
}

int read_next(const int *source)
  cppverify::post(cppverify::result == cppverify::old(source[1]))
{
  return source[1];
}

int external_read(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == cppverify::old(*source));

void rebind_pointer(int *target)
  cppverify::post(target == nullptr)
{
  target = nullptr;
}

int offset_precondition(const int *source)
  cppverify::pre((source + 1) == (source + 1))
  cppverify::post(cppverify::result == cppverify::old(*source))
{
  return *source;
}

int scalar_identity(int value)
  cppverify::post(cppverify::result == value)
{
  return value;
}

int forward_loaded_scalar(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == cppverify::old(*source))
{
  return scalar_identity(*source);
}

int forward_saved_scalar(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == cppverify::old(*source))
{
  int saved = *source;
  return scalar_identity(saved);
}

int forward_controlled_scalar(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(true)
{
  int selected = 0;
  if (*source != 0)
    selected = 1;
  return scalar_identity(selected);
}

cppverify::spec int spec_identity(int value)
{
  return value;
}

int forward_loaded_spec(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == spec_identity(cppverify::old(*source)))
{
  return *source;
}

cppverify::proof void pointer_lemma(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(true)
{
}

int *copied_pointer(int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == source)
{
  int *copy = source;
  return copy;
}

int unsafe_forwarded_read(const int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(cppverify::result == cppverify::old(source[1]))
{
  return read_next(source);
}

void discard_pointer_result(int *source)
  cppverify::pre(source != nullptr)
  cppverify::post(true)
{
  pointer_identity(source);
}

int use_after_delete()
  cppverify::post(true)
{
  int *p = new int(1);
  delete p;
  return *p;
}

int double_delete()
  cppverify::post(true)
{
  int *p = new int(1);
  delete p;
  delete p;
  return 0;
}

int uninitialized_read()
  cppverify::post(true)
{
  int *p = new int;
  return *p;
}

bool simultaneous_allocations_are_equal()
  cppverify::post(cppverify::result)
{
  int *p = new int(1);
  int *q = new int(2);
  bool equal = p == q;
  delete q;
  delete p;
  return equal;
}

int path_sensitive_double_delete(bool twice)
  cppverify::post(true)
{
  int *p = new int(1);
  if (twice)
    delete p;
  if (twice)
    delete p;
  return 0;
}

int path_sensitive_uninitialized_read(bool initialize)
  cppverify::post(true)
{
  int *p = new int;
  if (initialize)
    *p = 1;
  return *p;
}

int stale_pointer_after_reuse()
  cppverify::post(true)
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
  cppverify::post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  delete alias;
  return *owner;
}

int alias_double_delete()
  cppverify::post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  delete alias;
  delete owner;
  return 0;
}

bool aliases_are_distinct()
  cppverify::post(cppverify::result)
{
  int *owner = new int(1);
  int *alias = owner;
  bool distinct = owner != alias;
  delete owner;
  return distinct;
}

int modular_uninitialized_read()
  cppverify::post(true)
{
  int *owner = new int;
  int observed = read_allocated(owner);
  delete owner;
  return observed;
}

int modular_use_after_delete()
  cppverify::post(true)
{
  int *owner = new int(1);
  delete owner;
  return read_allocated(owner);
}

int modular_nonalias_violation()
  cppverify::post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  bool distinct = require_distinct(owner, alias);
  delete owner;
  return distinct;
}

int modular_scalar_extent_violation()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = read_next(owner);
  delete owner;
  return observed;
}

int modular_external_contract()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = external_read(owner);
  delete owner;
  return observed;
}

int modular_rebinding_false_proof()
  cppverify::post(cppverify::result == 2)
{
  int *owner = new int(1);
  rebind_pointer(owner);
  delete owner;
  return 1;
}

int modular_offset_precondition()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = offset_precondition(owner);
  delete owner;
  return observed;
}

int modular_forwarded_scalar()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = forward_loaded_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_temporary()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = forward_saved_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_control()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = forward_controlled_scalar(owner);
  delete owner;
  return observed;
}

int modular_forwarded_spec()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = forward_loaded_spec(owner);
  delete owner;
  return observed;
}

int modular_proof_call()
  cppverify::post(true)
{
  int *owner = new int(1);
  pointer_lemma(owner);
  delete owner;
  return 0;
}

int branch_reassignment_use_after_delete(bool choose)
  cppverify::post(true)
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
  cppverify::post(true)
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
  cppverify::post(true)
{
  int *owner = new int(1);
  int *alias = owner;
  int *replacement = new int(2);
  owner = replacement;
  delete alias;
  return *alias;
}

int copied_stale_pointer()
  cppverify::post(true)
{
  int *owner = new int(1);
  delete owner;
  int *alias = owner;
  return *alias;
}

int null_reassignment_dereference()
  cppverify::post(true)
{
  int *owner = new int(1);
  owner = nullptr;
  return *owner;
}

int returned_pointer_use_after_delete()
  cppverify::post(true)
{
  int *owner = new int(1);
  int *returned = pointer_identity(owner);
  delete owner;
  return *returned;
}

int modular_copied_pointer_return()
  cppverify::post(true)
{
  int *owner = new int(1);
  int *returned = copied_pointer(owner);
  int observed = *returned;
  delete owner;
  return observed;
}

int modular_unsafe_forwarding()
  cppverify::post(true)
{
  int *owner = new int(1);
  int observed = unsafe_forwarded_read(owner);
  delete owner;
  return observed;
}

int modular_discarded_pointer_forwarding()
  cppverify::post(true)
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
// VERIFY-DAG: Unresolved: modular_scalar_extent_violation {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: modular_external_contract {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: modular_rebinding_false_proof {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: modular_offset_precondition {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: error: verification failed: branch_reassignment_use_after_delete
// VERIFY-DAG: error: verification failed: reassigned_alias_double_delete
// VERIFY-DAG: error: verification failed: stale_alias_after_owner_reassignment
// VERIFY-DAG: error: verification failed: copied_stale_pointer
// VERIFY-DAG: error: verification failed: null_reassignment_dereference
// VERIFY-DAG: Unresolved: modular_proof_call {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: error: verification failed: returned_pointer_use_after_delete
// VERIFY-DAG: Unresolved: modular_copied_pointer_return {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: modular_unsafe_forwarding {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: modular_discarded_pointer_forwarding {{.*}}[reason=construct.unsupported]
// VERIFY-DAG: Unresolved: unsafe_forwarded_read {{.*}}[reason=callee.contract] (relies on the contract of read_next, which is not established)
// VERIFY-DAG: Verified: modular_forwarded_scalar
// VERIFY-DAG: Verified: modular_forwarded_temporary
// VERIFY-DAG: Verified: modular_forwarded_control
// VERIFY-DAG: Verified: modular_forwarded_spec
