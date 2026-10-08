// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=CHECK

int counter()
  cppverify::pre(true)
  cppverify::post(cppverify::result == 0)
{
  int x = 0;
  int i = 0;
  while (i < 5)
    cppverify::invariant(true)
  {
    x = x + 1;
    i = i + 1;
  }
  return x;
}

int immediate_bug()
  cppverify::post(cppverify::result >= 0)
{
  int i = 0;
  while (i < 3)
    cppverify::invariant(true)
  {
    cppverify::check(i != 1);
    i = i + 1;
  }
  return i;
}

// CHECK-DAG: BoundedSafe: counter [backend=bmc, bound=3] [reason=bmc.incomplete-bound]
// CHECK-DAG: error: verification failed: immediate_bug