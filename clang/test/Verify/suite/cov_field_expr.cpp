// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Point {
  int x;
  int y;
};

int sum_point(Point p)
  cppverify::pre(p.x >= 0 && p.y >= 0 && p.x <= 10 && p.y <= 10)
  cppverify::post(cppverify::result == p.x + p.y)
{
  return p.x + p.y;
}

// VERIFY: Verified: sum_point