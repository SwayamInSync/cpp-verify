// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Negative tests: cppverify::result and cppverify::old used outside their
// supported contexts.
// These are context errors caught by the parser.

// ---------------------------------------------------------------------------
// 1. result in function body (not in postcondition)
// ---------------------------------------------------------------------------
int f1(int x)
  cppverify::pre(x > 0)
{
  return cppverify::result; // expected-error {{'cppverify::result' can only be used in postconditions}}
}

// ---------------------------------------------------------------------------
// 2. old() in function body (not in postcondition or loop invariant)
// ---------------------------------------------------------------------------
int f2(int x)
  cppverify::pre(x > 0)
{
  return cppverify::old(x); // expected-error {{'cppverify::old' can only be used in postconditions and loop invariants}}
}

// ---------------------------------------------------------------------------
// 3. result in precondition
// ---------------------------------------------------------------------------
int f3(int x)
  cppverify::pre(cppverify::result > 0) // expected-error {{'cppverify::result' can only be used in postconditions}}
{
  return x;
}

// ---------------------------------------------------------------------------
// 4. old() in precondition
// ---------------------------------------------------------------------------
int f4(int x)
  cppverify::pre(cppverify::old(x) > 0) // expected-error {{'cppverify::old' can only be used in postconditions and loop invariants}}
{
  return x;
}

// ---------------------------------------------------------------------------
// 5. result in loop invariant
// ---------------------------------------------------------------------------
int f5(int n)
  cppverify::pre(n >= 0)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(cppverify::result >= 0) // expected-error {{'cppverify::result' can only be used in postconditions}}
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 6. old() in a loop invariant denotes function entry.
// ---------------------------------------------------------------------------
int f6(int n)
  cppverify::pre(n >= 0)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(cppverify::old(n) == n)
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 7. result has no function-entry value for old()
// ---------------------------------------------------------------------------
int f7(int x)
  cppverify::post(cppverify::old(cppverify::result) == x) // expected-error {{'cppverify::result' has no value in the function pre-state}}
{
  return x;
}

// ---------------------------------------------------------------------------
// 8. Bare result and old are ordinary names.
// ---------------------------------------------------------------------------
int old(int v) { return v; }
int f8(int x)
  cppverify::post(cppverify::result == x)
{
  int result = old(x);
  return result;
}
