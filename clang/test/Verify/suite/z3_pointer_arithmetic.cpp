// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

bool supported_pointer_arithmetic(int *pointer)
  post(result)
{
  return pointer + 1 != pointer;
}

// VERIFY: Verified: supported_pointer_arithmetic
