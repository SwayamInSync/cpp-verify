// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int first;
  int second;
};

unsigned long valid_sizeof()
  post(result == 8)
{
  return sizeof(Pair);
}

unsigned long valid_alignof()
  post(result == 4)
{
  return alignof(Pair);
}

unsigned long valid_unevaluated_dereference(int *pointer)
  post(result == 4)
{
  return sizeof(*pointer);
}

unsigned long valid_reference_type_layout()
  post(result == 4)
{
  return sizeof(int &);
}

unsigned long invalid_sizeof_claim()
  post(result == 4)
{
  return sizeof(Pair);
}

// VERIFY-DAG: Verified: valid_sizeof
// VERIFY-DAG: Verified: valid_alignof
// VERIFY-DAG: Verified: valid_unevaluated_dereference
// VERIFY-DAG: Verified: valid_reference_type_layout
// VERIFY-DAG: error: verification failed: invalid_sizeof_claim
