// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

long unrelated_pointer_difference(int *left, int *right)
  pre(left != nullptr && right != nullptr)
  post(true)
{
  return left - right;
}

long equal_address_without_provenance(int *left, int *right)
  aliases(left, right)
  pre(left != nullptr && right != nullptr && left == right)
  post(true)
{
  return left - right;
}

long null_pointer_difference()
  post(true)
{
  int *pointer = nullptr;
  return pointer - pointer;
}

long incorrect_unit_difference(int *pointer)
  pre(pointer != nullptr)
  post(result == 2)
{
  return (pointer + 1) - pointer;
}

long dynamic_distinct_difference()
  post(true)
{
  int *left = new int(1);
  int *right = new int(2);
  long distance = left - right;
  delete right;
  delete left;
  return distance;
}

long dangling_pointer_difference()
  post(true)
{
  int *pointer = new int(1);
  delete pointer;
  return pointer - pointer;
}

long copied_offset_difference(int *pointer)
  pre(pointer != nullptr)
  post(true)
{
  int *next = pointer + 1;
  return next - pointer;
}

long offset_beyond_complete_object(int *pointer)
  pre(pointer != nullptr)
  post(true)
{
  return (pointer + 2) - pointer;
}

long negative_offset_without_extent(int *pointer)
  pre(pointer != nullptr)
  post(true)
{
  return (pointer - 1) - pointer;
}

// VERIFY-DAG: error: verification failed: unrelated_pointer_difference
// VERIFY-DAG: error: verification failed: equal_address_without_provenance
// VERIFY-DAG: error: verification failed: null_pointer_difference
// VERIFY-DAG: error: verification failed: incorrect_unit_difference
// VERIFY-DAG: error: verification failed: dynamic_distinct_difference
// VERIFY-DAG: error: verification failed: dangling_pointer_difference
// VERIFY-DAG: error: verification failed: copied_offset_difference
// VERIFY-DAG: error: verification failed: offset_beyond_complete_object
// VERIFY-DAG: error: verification failed: negative_offset_without_extent
