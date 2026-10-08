// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --timeout=1 %s 2>&1 | FileCheck %s --check-prefix=LOWER

int valid_countdown(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result == 0)
  cppverify::decreases(n)
{
  if (n == 0)
    return 0;
  return valid_countdown(n - 1);
}

int invalid_nonterminating_exec(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result == 0)
  cppverify::post(cppverify::result == 1)
  cppverify::decreases(n)
{
  return invalid_nonterminating_exec(n);
}

// VERIFY-DAG: Verified: valid_countdown
// VERIFY-DAG: error: verification failed: invalid_nonterminating_exec [{{.*}}::termination@

// LOWER-DAG: Lowered: valid_countdown
// LOWER-DAG: Lowered: invalid_nonterminating_exec
// LOWER-NOT: Verified:
// LOWER-NOT: error:
// LOWER-NOT: Unresolved:
