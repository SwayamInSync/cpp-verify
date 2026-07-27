// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

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
