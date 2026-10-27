// RUN: %clang_cc1 -std=c++20 -fverify-contracts -verify %s
//
// cppverify::index is the position of a range-based for loop, named in that
// loop's contract only.

int body(int n)
  cppverify::pre(cppverify::index > 0) // expected-error {{'cppverify::index' is the position of a range-based for loop, in its contract}}
{
  return cppverify::index; // expected-error {{'cppverify::index' is the position of a range-based for loop, in its contract}}
}

int counted(int n) {
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    cppverify::decreases(n - i)
    cppverify::invariant(cppverify::index >= 0) // expected-error {{'cppverify::index' is the position of a range-based for loop, in its contract}}
    s = s + 1;
  return s;
}

int ranged() {
  int a[3] = {1, 2, 3};
  int s = 0;
  for (int v : a)
    cppverify::invariant(0 <= cppverify::index && cppverify::index <= 3)
    cppverify::decreases(3 - cppverify::index)
  {
    cppverify::check(cppverify::index < 3); // expected-error {{'cppverify::index' is the position of a range-based for loop, in its contract}}
    s = s + v;
  }
  return s;
}

// Unqualified, index is an ordinary name.
int index = 0;
int plain() { return index; }
