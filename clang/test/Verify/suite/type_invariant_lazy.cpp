// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Coordinate {
  int x;
  int y;
  type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
};

// Reads x: injects p.x in [0,1000] and p.y in [0,1000] as preconditions.
// The postcondition is *only* provable from the injected invariant (returning
// p.x is not in itself >= 0), so this exercises injection rather than passing
// trivially.
int bounded_x(Coordinate p)
  post(result >= 0 && result <= 1000)
{
  return p.x;
}

// Reads both fields; sum is bounded only because both invariants are injected.
int sum_bounded(Coordinate p)
  post(result >= 0 && result <= 2000)
{
  return p.x + p.y;
}

// Never reads p.x/p.y: no type_invariant injection, still verifies.
int ignore_coords(Coordinate p)
  post(result == 0)
{
  (void)p;
  return 0;
}

// VERIFY: Verified: bounded_x
// VERIFY: Verified: sum_bounded
// VERIFY: Verified: ignore_coords
