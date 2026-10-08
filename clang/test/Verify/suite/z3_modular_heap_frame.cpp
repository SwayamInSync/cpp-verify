// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int *p, int value)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == value)
{
  *p = value;
}

void region_frame_keeps_other_object(int *p, int *q)
  cppverify::pre(p != nullptr && q != nullptr && p != q)
  cppverify::pre(*q == 9)
  cppverify::modifies(*p)
  cppverify::post(*p == 7 && *q == 9)
{
  set_value(p, 7);
}

void increment_value(int *p)
  cppverify::pre(p != nullptr && *p < 2147483647)
  cppverify::modifies(*p)
  cppverify::post(*p == cppverify::old(*p) + 1)
{
  *p = *p + 1;
}

void valid_old_uses_call_entry(int *p)
  cppverify::pre(p != nullptr && *p == 4)
  cppverify::modifies(*p)
  cppverify::post(*p == 6)
{
  increment_value(p);
  increment_value(p);
}

void invalid_unframed_claim(int *p, int *q)
  cppverify::pre(p != nullptr && q != nullptr && p != q)
  cppverify::modifies(*p)
  cppverify::post(*q == 9)
{
  set_value(p, 7);
}

void invalid_caller_modifies(int *p, int *q)
  cppverify::pre(p != nullptr && q != nullptr)
  cppverify::modifies(*q)
{
  set_value(p, 7);
}

void invalid_missing_modifies(int *p)
  cppverify::pre(p != nullptr)
{
  *p = 7;
}

// VERIFY-DAG: Verified: set_value
// A region-style `modifies(*p)` covers p's object. Distinct pointer
// parameters address separate objects, so the call keeps *q.
// VERIFY-DAG: Verified: region_frame_keeps_other_object
// VERIFY-DAG: Verified: increment_value
// VERIFY-DAG: Verified: valid_old_uses_call_entry
// VERIFY-DAG: error: verification failed: invalid_unframed_claim
// VERIFY-DAG: error: verification failed: invalid_caller_modifies
// VERIFY-DAG: error: verification failed: invalid_missing_modifies
