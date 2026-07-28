// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

int *make_value(int value)
  post(result != nullptr)
  post(*result == value)
{
  int *owner = new int(value);
  return owner;
}

int observe_pointer(const int *value)
  pre(value != nullptr)
  post(result == old(*value))
{
  return *value;
}

int *uninitialized_factory()
  post(result != nullptr)
{
  int *owner = new int;
  return owner;
}

int consume_uninitialized_factory()
  post(true)
{
  int *owner = uninitialized_factory();
  delete owner;
  return 0;
}

int *freed_factory()
  post(result != nullptr)
{
  int *owner = new int(1);
  delete owner;
  return owner;
}

int consume_freed_factory()
  post(true)
{
  int *owner = freed_factory();
  delete owner;
  return 0;
}

int *freed_forward_factory()
  post(result != nullptr)
{
  int *owner = make_value(1);
  delete owner;
  return owner;
}

int consume_freed_forward_factory()
  post(true)
{
  int *owner = freed_forward_factory();
  delete owner;
  return 0;
}

int *multiple_allocation_factory()
  post(result != nullptr)
{
  int *first = new int(1);
  int *second = new int(2);
  return first;
}

int consume_multiple_allocation_factory()
  post(true)
{
  int *owner = multiple_allocation_factory();
  delete owner;
  return 0;
}

int *secondary_escape_factory()
  post(result != nullptr)
  post(*result == 1)
{
  int *owner = new int(1);
  int observed = observe_pointer(owner);
  return observed == 1 ? owner : owner;
}

int consume_secondary_escape_factory()
  post(true)
{
  int *owner = secondary_escape_factory();
  delete owner;
  return 0;
}

int *nullable_leak_factory(bool discard)
  post(result == nullptr || *result == 1)
{
  int *owner = new int(1);
  if (discard)
    return nullptr;
  return owner;
}

int consume_nullable_leak_factory(bool discard)
  post(true)
{
  int *owner = nullable_leak_factory(discard);
  delete owner;
  return 0;
}

int *recursive_factory(int count)
  pre(count >= 0)
  post(result != nullptr)
  post(*result == count)
  decreases(count)
{
  if (count == 0) {
    int *owner = new int(0);
    return owner;
  }
  return recursive_factory(count - 1);
}

int consume_recursive_factory()
  post(true)
{
  int *owner = recursive_factory(1);
  delete owner;
  return 0;
}

int *external_factory(int value)
  post(result != nullptr)
  post(*result == value);

int consume_external_factory()
  post(true)
{
  int *owner = external_factory(1);
  delete owner;
  return 0;
}

int double_delete_owned()
  post(true)
{
  int *owner = make_value(1);
  delete owner;
  delete owner;
  return 0;
}

int stale_alias_owned()
  post(true)
{
  int *owner = make_value(1);
  int *alias = owner;
  delete owner;
  return *alias;
}

bool equal_factory_results()
  post(result)
{
  int *left = make_value(1);
  int *right = make_value(2);
  bool equal = left == right;
  delete right;
  delete left;
  return equal;
}

void discard_owned_result()
  post(true)
{
  make_value(1);
}

// VERIFY-DAG: error: verification failed: consume_uninitialized_factory
// VERIFY-DAG: error: verification failed: consume_freed_factory
// VERIFY-DAG: error: verification failed: consume_freed_forward_factory
// VERIFY-DAG: error: verification failed: consume_multiple_allocation_factory
// VERIFY-DAG: error: verification failed: consume_secondary_escape_factory
// VERIFY-DAG: error: verification failed: consume_nullable_leak_factory
// VERIFY-DAG: error: verification failed: consume_recursive_factory
// VERIFY-DAG: error: verification failed: consume_external_factory
// VERIFY-DAG: error: verification failed: double_delete_owned
// VERIFY-DAG: error: verification failed: stale_alias_owned
// VERIFY-DAG: error: verification failed: equal_factory_results
// VERIFY-DAG: error: verification failed: discard_owned_result

// BMC-DAG: error: verification failed: consume_uninitialized_factory
// BMC-DAG: error: verification failed: consume_freed_factory
// BMC-DAG: error: verification failed: consume_freed_forward_factory
// BMC-DAG: error: verification failed: consume_multiple_allocation_factory
// BMC-DAG: error: verification failed: consume_secondary_escape_factory
// BMC-DAG: error: verification failed: consume_nullable_leak_factory
// BMC-DAG: error: verification failed: consume_recursive_factory
// BMC-DAG: error: verification failed: consume_external_factory
// BMC-DAG: error: verification failed: double_delete_owned
// BMC-DAG: error: verification failed: stale_alias_owned
// BMC-DAG: error: verification failed: equal_factory_results
// BMC-DAG: error: verification failed: discard_owned_result
