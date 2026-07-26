// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int positive_only(int value)
  pre(value > 0)
  post(result == value)
{
  return value;
}

int invalid_contract_expression_call()
  post(positive_only(0) == 0)
{
  return 0;
}

// VERIFY: error: invalid_contract_expression_call: executable call is unsupported in this expression context: positive_only
// VERIFY-NOT: Verified: invalid_contract_expression_call
