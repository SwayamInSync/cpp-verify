// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Negative tests: result and old used outside their supported contexts.
// These are context errors caught by the parser.

// ---------------------------------------------------------------------------
// 1. result in function body (not in postcondition)
// ---------------------------------------------------------------------------
int f1(int x)
  pre(x > 0)
{
  return result; // expected-error {{'result' can only be used in postconditions}}
}

// ---------------------------------------------------------------------------
// 2. old() in function body (not in postcondition or loop invariant)
// ---------------------------------------------------------------------------
int f2(int x)
  pre(x > 0)
{
  return old(x); // expected-error {{'old' can only be used in postconditions and loop invariants}}
}

// ---------------------------------------------------------------------------
// 3. result in precondition
// ---------------------------------------------------------------------------
int f3(int x)
  pre(result > 0) // expected-error {{'result' can only be used in postconditions}}
{
  return x;
}

// ---------------------------------------------------------------------------
// 4. old() in precondition
// ---------------------------------------------------------------------------
int f4(int x)
  pre(old(x) > 0) // expected-error {{'old' can only be used in postconditions and loop invariants}}
{
  return x;
}

// ---------------------------------------------------------------------------
// 5. result in loop invariant
// ---------------------------------------------------------------------------
int f5(int n)
  pre(n >= 0)
{
  int i = 0;
  while (i < n)
    invariant(result >= 0) // expected-error {{'result' can only be used in postconditions}}
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 6. old() in a loop invariant denotes function entry.
// ---------------------------------------------------------------------------
int f6(int n)
  pre(n >= 0)
{
  int i = 0;
  while (i < n)
    invariant(old(n) == n)
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 7. result has no function-entry value for old()
// ---------------------------------------------------------------------------
int f7(int x)
  post(old(result) == x) // expected-error {{'result' has no value in the function pre-state}}
{
  return x;
}
