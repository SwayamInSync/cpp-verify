// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

int reject_old_entry_overflow(int value)
  pre(value == 2147483647)
  post(result == 0)
{
  do {
    value = 0;
  } while (false)
    invariant(old(value + 1) == old(value + 1));
  return value;
}

int reject_quantified_old_entry_overflow(int value)
  pre(value == 2147483647)
  post(result == 0)
{
  do {
    value = 0;
  } while (false)
    invariant(old(forall(i, 0, 2, value + i == value + i)));
  return value;
}

int reject_old_entry_null_dereference(int *pointer, int *replacement)
  pre(pointer == nullptr && replacement != nullptr)
  post(result == 0)
{
  do {
    pointer = replacement;
  } while (false)
    invariant(old(*pointer) == old(*pointer));
  return 0;
}

// CHECK-DAG: error: verification failed: reject_old_entry_overflow
// CHECK-DAG: error: verification failed: reject_quantified_old_entry_overflow
// CHECK-DAG: error: verification failed: reject_old_entry_null_dereference

