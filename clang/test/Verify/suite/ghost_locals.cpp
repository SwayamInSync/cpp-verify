// RUN: %clang -std=c++17 -fverify-contracts -fno-verify -c -o %t.o %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s
//
// `ghost T x = e;` declares a variable for the rest of the function: loop
// invariants, assertions, and later ghost blocks may use it, and compilation
// erases it.

int add_ten(int x)
  cppverify::pre(x >= 0 && x <= 100)
  cppverify::post(cppverify::result == x + 10)
{
  int y = x;
  cppverify::ghost int start = y;
  int i = 0;
  while (i < 3)
    cppverify::invariant(0 <= i && i <= 3 && y == start + i)
    cppverify::decreases(3 - i)
  {
    y = y + 1;
    i = i + 1;
  }
  return y + 7;
}
// CHECK-DAG: Verified: add_ten

int doubled(int x)
  cppverify::pre(x >= 0 && x < 1000)
  cppverify::post(cppverify::result == 2 * x)
{
  cppverify::ghost int before = x;
  x = x * 2;
  cppverify::ghost { before = before * 2; }
  cppverify::check(x == before);
  return x;
}
// CHECK-DAG: Verified: doubled

int remembers_wrong(int x)
  cppverify::pre(x >= 0 && x < 1000)
{
  cppverify::ghost int before = x;
  x = x + 1;
  cppverify::check(x == before);
  return x;
}
// CHECK-DAG: error: verification failed: remembers_wrong [{{.*}}::assertion@
