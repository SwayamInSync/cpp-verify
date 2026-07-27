// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

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

// VERIFY-DAG: error: verification failed: use_after_delete
// VERIFY-DAG: error: verification failed: double_delete
// VERIFY-DAG: error: verification failed: uninitialized_read
// VERIFY-DAG: error: verification failed: simultaneous_allocations_are_equal
// VERIFY-DAG: error: verification failed: path_sensitive_double_delete
// VERIFY-DAG: error: verification failed: path_sensitive_uninitialized_read
// VERIFY-DAG: error: verification failed: stale_pointer_after_reuse
