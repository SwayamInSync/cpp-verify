// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Point {
  int x;
  int y;
};

Point make_origin()
  post(result.x == 0)
  post(result.y == 0)
{
  Point p;
  p.x = 0;
  p.y = 0;
  return p;
}

int point_sum(Point p)
  pre(p.x >= 0 && p.y >= 0 && p.x <= 100 && p.y <= 100)
  post(result == p.x + p.y)
{
  return p.x + p.y;
}

// VERIFY-DAG: verified: make_origin
// VERIFY-DAG: verified: point_sum