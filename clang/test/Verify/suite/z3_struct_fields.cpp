// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Point {
  int x;
  int y;
};

spec int point_metric(Point p) {
  return p.x + p.y;
}

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

int call_point_sum()
  post(result == 7)
{
  Point p;
  p.x = 3;
  p.y = 4;
  return point_sum(p);
}

int use_struct_return()
  post(result == 0)
{
  Point p = make_origin();
  return p.x + p.y;
}

Point forward_struct_return()
  post(result.x == 0)
  post(result.y == 0)
{
  return make_origin();
}

int use_aggregate_spec_parameter(Point p)
  pre(p.x >= 0 && p.y >= 0 && p.x <= 100 && p.y <= 100)
  post(point_metric(p) == p.x + p.y)
{
  return 0;
}

// VERIFY-DAG: Verified: make_origin
// VERIFY-DAG: Verified: point_sum
// VERIFY-DAG: Verified: call_point_sum
// VERIFY-DAG: Verified: use_struct_return
// VERIFY-DAG: Verified: forward_struct_return
// VERIFY-DAG: Verified: use_aggregate_spec_parameter