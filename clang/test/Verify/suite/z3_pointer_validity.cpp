// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=DUMP

int *identity_pointer(int *p)
  post(result == p)
{
  return p;
}

int read_identity(int *p)
  pre(p != nullptr)
  post(result == *p)
{
  int *q = identity_pointer(p);
  return *q;
}

// VERIFY-DAG: Verified: identity_pointer
// VERIFY-DAG: Verified: read_identity
// DUMP: valid_ptr
