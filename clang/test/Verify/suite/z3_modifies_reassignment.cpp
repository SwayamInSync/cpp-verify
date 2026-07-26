// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void write_value(int *p, int value)
  pre(p != nullptr)
  modifies(*p)
  post(*p == value)
{
  *p = value;
}

void valid_reassigned_pointer(int *p, int *q)
  pre(p != nullptr && q != nullptr)
  modifies(*p, *q)
{
  p = q;
  *p = 123;
}

void invalid_reassigned_store(int *p, int *q)
  pre(p != nullptr && q != nullptr)
  modifies(*p)
{
  p = q;
  *p = 123;
}

void invalid_reassigned_call(int *p, int *q)
  pre(p != nullptr && q != nullptr)
  modifies(*p)
{
  p = q;
  write_value(p, 123);
}

// VERIFY-DAG: Verified: write_value
// VERIFY-DAG: Verified: valid_reassigned_pointer
// VERIFY-DAG: error: verification failed: invalid_reassigned_store
// VERIFY-DAG: error: verification failed: invalid_reassigned_call
