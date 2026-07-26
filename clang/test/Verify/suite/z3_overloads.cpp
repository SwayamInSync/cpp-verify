// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int overloaded_identity(int x)
  post(result == x)
{
  return x;
}

long overloaded_identity(long x)
  pre(x < 9223372036854775807L)
  post(result == x + 1)
{
  return x + 1;
}

int call_int_overload()
  post(result == 7)
{
  return overloaded_identity(7);
}

long call_long_overload()
  post(result == 8)
{
  return overloaded_identity(7L);
}

spec int overloaded_spec(int x) {
  return x + 1;
}

spec long overloaded_spec(long x) {
  return x + 2;
}

spec int overloaded_countdown(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return overloaded_countdown(n - 1);
}

spec long overloaded_countdown(long n)
  decreases(n)
{
  return n;
}

int use_int_spec_overload()
  post(overloaded_spec(3) == 4)
{
  return 0;
}

int use_long_spec_overload()
  post(overloaded_spec(3L) == 5)
{
  return 0;
}

// VERIFY-DAG: Verified: call_int_overload
// VERIFY-DAG: Verified: call_long_overload
// VERIFY-DAG: Verified: spec decreases: overloaded_countdown
// VERIFY-DAG: Verified: spec axiom: overloaded_countdown
// VERIFY-DAG: Verified: use_int_spec_overload
// VERIFY-DAG: Verified: use_long_spec_overload
