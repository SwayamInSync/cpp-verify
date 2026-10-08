// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int first;
  int second;
};

void set_second(Pair *p, int value)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->second)
  cppverify::post(p->first == cppverify::old(p->first))
  cppverify::post(p->second == value)
{
  p->second = value;
}

void valid_pointer_field_client(Pair *p)
  cppverify::pre(p != nullptr && p->first == 3)
  cppverify::modifies(p->second)
  cppverify::post(p->first == 3 && p->second == 7)
{
  set_second(p, 7);
}

void valid_explicit_dereference_field(Pair *p, int value)
  cppverify::pre(p != nullptr)
  cppverify::modifies((*p).first)
  cppverify::post((*p).first == value)
{
  (*p).first = value;
}

void invalid_pointer_field_modifies(Pair *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->first)
{
  p->second = 7;
}

void invalid_pointer_field_claim(Pair *p)
  cppverify::pre(p != nullptr && p->first == 3)
  cppverify::modifies(p->second)
  cppverify::post(p->first == 4)
{
  set_second(p, 7);
}

// VERIFY-DAG: Verified: set_second
// VERIFY-DAG: Verified: valid_pointer_field_client
// VERIFY-DAG: Verified: valid_explicit_dereference_field
// VERIFY-DAG: error: verification failed: invalid_pointer_field_modifies
// VERIFY-DAG: error: verification failed: invalid_pointer_field_claim
