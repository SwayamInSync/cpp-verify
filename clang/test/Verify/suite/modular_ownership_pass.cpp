// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %clang -std=c++17 -fverify-contracts -c -o %t.o %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

int *make_value(int value)
  post(result != nullptr)
  post(*result == value)
{
  int *owner = new int(value);
  return owner;
}

int *make_stored_value(int value)
  post(result != nullptr)
  post(*result == value)
{
  int *owner = new int;
  *owner = value;
  return owner;
}

int *make_nullable(bool create, int value)
  post((result != nullptr) == create)
  post(result == nullptr || *result == value)
{
  if (!create)
    return nullptr;
  int *owner = new int(value);
  return owner;
}

int *forward_value(int value)
  post(result != nullptr)
  post(*result == value)
{
  return make_value(value);
}

int *forward_again(int value)
  post(result != nullptr)
  post(*result == value)
{
  return forward_value(value);
}

int *alias_forward(int value)
  post(result != nullptr)
  post(*result == value)
{
  int *owner = make_value(value);
  int *alias = owner;
  return alias;
}

int *forward_nullable(bool create, int value)
  post((result != nullptr) == create)
  post(result == nullptr || *result == value)
{
  return make_nullable(create, value);
}

int *branch_forward(bool first, int value)
  post(result != nullptr)
  post(*result == value)
{
  if (first)
    return make_value(value);
  return make_stored_value(value);
}

int read_owned(const int *value)
  pre(value != nullptr)
  post(result == old(*value))
{
  return *value;
}

int consume_value(int value)
  post(result == value)
{
  int *owner = forward_again(value);
  int observed = read_owned(owner);
  delete owner;
  return observed;
}

int consume_nullable(bool create, int value)
  post(result == (create ? value : 0))
{
  int *owner = forward_nullable(create, value);
  if (!owner)
    return 0;
  int observed = *owner;
  delete owner;
  return observed;
}

int mutate_owned(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  int *owner = make_value(value);
  *owner = value + 1;
  int observed = *owner;
  delete owner;
  return observed;
}

bool distinct_factory_results()
  post(result)
{
  int *left = make_value(1);
  int *right = make_value(2);
  bool distinct = left != right;
  delete right;
  delete left;
  return distinct;
}

bool distinct_local_and_factory()
  post(result)
{
  int *local = new int(1);
  int *returned = make_value(2);
  bool distinct = local != returned;
  delete returned;
  delete local;
  return distinct;
}

bool *make_bool(bool value)
  post(result != nullptr)
  post(*result == value)
{
  bool *owner = new bool(value);
  return owner;
}

bool consume_bool(bool value)
  post(result == value)
{
  bool *owner = make_bool(value);
  bool observed = *owner;
  delete owner;
  return observed;
}

// VERIFY-DAG: Verified: make_value
// VERIFY-DAG: Verified: make_stored_value
// VERIFY-DAG: Verified: make_nullable
// VERIFY-DAG: Verified: forward_value
// VERIFY-DAG: Verified: forward_again
// VERIFY-DAG: Verified: alias_forward
// VERIFY-DAG: Verified: forward_nullable
// VERIFY-DAG: Verified: branch_forward
// VERIFY-DAG: Verified: consume_value
// VERIFY-DAG: Verified: consume_nullable
// VERIFY-DAG: Verified: mutate_owned
// VERIFY-DAG: Verified: distinct_factory_results
// VERIFY-DAG: Verified: distinct_local_and_factory
// VERIFY-DAG: Verified: make_bool
// VERIFY-DAG: Verified: consume_bool

// BMC-DAG: Verified: make_value
// BMC-DAG: Verified: make_stored_value
// BMC-DAG: Verified: make_nullable
// BMC-DAG: Verified: forward_value
// BMC-DAG: Verified: forward_again
// BMC-DAG: Verified: alias_forward
// BMC-DAG: Verified: forward_nullable
// BMC-DAG: Verified: branch_forward
// BMC-DAG: Verified: consume_value
// BMC-DAG: Verified: consume_nullable
// BMC-DAG: Verified: mutate_owned
// BMC-DAG: Verified: distinct_factory_results
// BMC-DAG: Verified: distinct_local_and_factory
// BMC-DAG: Verified: make_bool
// BMC-DAG: Verified: consume_bool
