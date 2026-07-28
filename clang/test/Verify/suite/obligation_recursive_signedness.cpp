// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only %s 2>&1 | FileCheck %s

spec unsigned int recursive_unsigned_cast(int x)
  decreases(x)
{
  if (x > 0)
    return recursive_unsigned_cast(x - 1);
  return (unsigned int)x;
}

// CHECK: Lowered: spec decreases: recursive_unsigned_cast
