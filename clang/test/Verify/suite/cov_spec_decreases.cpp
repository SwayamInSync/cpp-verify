// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int dec(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return dec(n - 1) + 1;
}

// VERIFY: spec decreases: dec