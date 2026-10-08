// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int &value, int next)
  cppverify::modifies(value)
  cppverify::post(value == next)
{
  value = next;
}

void set_pair(int &left, int &right, int next)
  cppverify::modifies(left, right)
  cppverify::post(left == next && right == next)
{
  left = next;
  right = next;
}

void wrong_reference_post(int &value)
  cppverify::modifies(value)
  cppverify::post(value == 2)
{
  value = 1;
}

void missing_reference_modifies(int &value)
  cppverify::post(value == 1)
{
  value = 1;
}

void wrong_reference_old(int &value)
  cppverify::pre(value < 2147483647)
  cppverify::modifies(value)
  cppverify::post(value == cppverify::old(value))
{
  ++value;
}

void wrong_reference_frame(int &allowed, int &forbidden)
  cppverify::modifies(allowed)
{
  forbidden = 1;
}

void alias_without_permission(int *value)
  cppverify::pre(value != nullptr)
  cppverify::modifies(*value)
{
  set_pair(*value, *value, 4);
}

void nullable_reference_actual(int *value)
  cppverify::modifies(*value)
{
  set_value(*value, 3);
}

void opaque_second(int &first, int &second)
  cppverify::post(second == 1);

void implicit_effect_exceeds_frame(int *allowed, int *preserved)
  cppverify::pre(allowed != nullptr && preserved != nullptr && *preserved == 0)
  cppverify::modifies(allowed[0])
  cppverify::post(*preserved == 0)
{
  opaque_second(*allowed, *preserved);
}

void nonterminating_reference_store(int &value)
  cppverify::pre(value == 0)
  cppverify::modifies(value)
  cppverify::decreases(0)
{
  value = 1;
  if (value == 1) {
    value = 0;
    nonterminating_reference_store(value);
  }
}

void opaque_loop_effect(int &value)
  cppverify::pre(value == value);

void implicit_effect_in_loop(int &value)
  cppverify::pre(value == 0)
  cppverify::post(value == 0)
{
  int iteration = 0;
  while (iteration < 1)
    cppverify::invariant(iteration >= 0 && iteration <= 1)
    cppverify::decreases(1 - iteration)
  {
    opaque_loop_effect(value);
    ++iteration;
  }
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: set_pair
// VERIFY-DAG: error: verification failed: wrong_reference_post
// VERIFY-DAG: error: verification failed: missing_reference_modifies
// VERIFY-DAG: error: verification failed: wrong_reference_old
// VERIFY-DAG: error: verification failed: wrong_reference_frame
// VERIFY-DAG: error: verification failed: alias_without_permission
// VERIFY-DAG: error: verification failed: nullable_reference_actual
// VERIFY-DAG: error: verification failed: implicit_effect_exceeds_frame
// VERIFY-DAG: error: verification failed: nonterminating_reference_store [{{.*}}::termination@
// VERIFY-DAG: error: verification failed: implicit_effect_in_loop
