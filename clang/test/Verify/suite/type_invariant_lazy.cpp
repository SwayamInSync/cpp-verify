// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Coordinate {
  int x;
  int y;
  type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
};

// Reads x: injects p.x in [0,1000] and p.y in [0,1000] as preconditions.
int read_x(Coordinate p)
  post(result == p.x)
{
  return p.x;
}

// Never reads p.x/p.y: no type_invariant injection.
int ignore_coords(Coordinate p)
  post(result == 0)
{
  (void)p;
  return 0;
}

// VERIFY: Verified: read_x
// VERIFY: Verified: ignore_coords