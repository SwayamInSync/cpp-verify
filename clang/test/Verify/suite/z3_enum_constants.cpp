// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

enum Status : unsigned char {
  Ready = 3,
  Complete = 9,
};

int enum_constant_value()
  post(result == 9)
{
  return Complete;
}

// VERIFY: Verified: enum_constant_value
