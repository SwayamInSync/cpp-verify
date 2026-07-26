// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int *p, int value)
  pre(p != nullptr)
  modifies(*p)
  post(*p == value)
{
  *p = value;
}

void valid_preserves_unmodified(int *p, int *q)
  pre(p != nullptr && q != nullptr && p != q)
  pre(*q == 9)
  modifies(*p)
  post(*p == 7 && *q == 9)
{
  set_value(p, 7);
}

void increment_value(int *p)
  pre(p != nullptr && *p < 2147483647)
  modifies(*p)
  post(*p == old(*p) + 1)
{
  *p = *p + 1;
}

void valid_old_uses_call_entry(int *p)
  pre(p != nullptr && *p == 4)
  modifies(*p)
  post(*p == 6)
{
  increment_value(p);
  increment_value(p);
}

void invalid_unframed_claim(int *p, int *q)
  pre(p != nullptr && q != nullptr && p != q)
  modifies(*p)
  post(*q == 9)
{
  set_value(p, 7);
}

void invalid_caller_modifies(int *p, int *q)
  pre(p != nullptr && q != nullptr)
  modifies(*q)
{
  set_value(p, 7);
}

void invalid_missing_modifies(int *p)
  pre(p != nullptr)
{
  *p = 7;
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: valid_preserves_unmodified
// VERIFY-DAG: Verified: increment_value
// VERIFY-DAG: Verified: valid_old_uses_call_entry
// VERIFY-DAG: error: verification failed: invalid_unframed_claim
// VERIFY-DAG: error: verification failed: invalid_caller_modifies
// VERIFY-DAG: error: verification failed: invalid_missing_modifies
