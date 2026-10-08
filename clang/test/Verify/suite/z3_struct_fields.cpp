// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Point {
  int x;
  int y;
};

cppverify::spec int point_metric(Point p) {
  return p.x + p.y;
}

Point make_origin()
  cppverify::post(cppverify::result.x == 0)
  cppverify::post(cppverify::result.y == 0)
{
  Point p;
  p.x = 0;
  p.y = 0;
  return p;
}

int point_sum(Point p)
  cppverify::pre(p.x >= 0 && p.y >= 0 && p.x <= 100 && p.y <= 100)
  cppverify::post(cppverify::result == p.x + p.y)
{
  return p.x + p.y;
}

int call_point_sum()
  cppverify::post(cppverify::result == 7)
{
  Point p;
  p.x = 3;
  p.y = 4;
  return point_sum(p);
}

int use_struct_return()
  cppverify::post(cppverify::result == 0)
{
  Point p = make_origin();
  return p.x + p.y;
}

Point forward_struct_return()
  cppverify::post(cppverify::result.x == 0)
  cppverify::post(cppverify::result.y == 0)
{
  return make_origin();
}

int use_aggregate_spec_parameter(Point p)
  cppverify::pre(p.x >= 0 && p.y >= 0 && p.x <= 100 && p.y <= 100)
  cppverify::post(point_metric(p) == p.x + p.y)
{
  return 0;
}

// VERIFY-DAG: Verified: make_origin
// VERIFY-DAG: Verified: point_sum
// VERIFY-DAG: Verified: call_point_sum
// VERIFY-DAG: Verified: use_struct_return
// VERIFY-DAG: Verified: forward_struct_return
// VERIFY-DAG: Verified: use_aggregate_spec_parameter