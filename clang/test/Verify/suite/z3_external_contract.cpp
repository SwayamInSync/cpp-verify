// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
//
// A contract without a definition is assumed only when the declaration says
// so with [[cppverify::trusted]]. Unmarked, nothing verifies its callers.

[[cppverify::trusted]] int external_increment(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1);

int valid_external_call(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1)
{
  return external_increment(value);
}

int invalid_external_call(int value)
  cppverify::post(cppverify::result == value + 1)
{
  return external_increment(value);
}

int unmarked_increment(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1);

int unmarked_call(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1)
{
  return unmarked_increment(value);
}

// VERIFY-DAG: Trusted: external_increment (contract assumed, not verified)
// VERIFY-DAG: Verified: valid_external_call [backend=z3] [trusts=external_increment]
// VERIFY-DAG: error: verification failed: invalid_external_call
// VERIFY-DAG: warning: unmarked_increment has a contract but no definition, so its callers are not verified; mark the declaration {{\[\[}}cppverify::trusted]] to assume the contract
// VERIFY-DAG: Unresolved: unmarked_call [backend=z3] [reason=callee.contract] (relies on the contract of unmarked_increment (no definition; mark it {{\[\[}}cppverify::trusted]] to assume it), which is not established)
