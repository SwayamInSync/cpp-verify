// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Point {
  int x;
  int y;
};

Point valid_early_struct_return(bool choose_first)
  post(result.x == (choose_first ? 1 : 3))
  post(result.y == (choose_first ? 2 : 4))
{
  Point first;
  first.x = 1;
  first.y = 2;
  Point second;
  second.x = 3;
  second.y = 4;
  if (choose_first)
    return first;
  return second;
}

Point invalid_early_struct_return(bool choose_first)
  post(result.x == 1)
{
  Point first;
  first.x = 1;
  first.y = 0;
  Point second;
  second.x = 3;
  second.y = 0;
  if (choose_first)
    return first;
  return second;
}

Point valid_conditional_struct_return(bool choose_first, Point first,
                                      Point second)
  post(result.x == (choose_first ? first.x : second.x))
  post(result.y == (choose_first ? first.y : second.y))
{
  return choose_first ? first : second;
}

Point invalid_conditional_struct_return(bool choose_first, Point first,
                                        Point second)
  post(result.x == first.x)
{
  return choose_first ? first : second;
}

// VERIFY-DAG: Verified: valid_early_struct_return
// VERIFY-DAG: Verified: valid_conditional_struct_return
// VERIFY-DAG: error: verification failed: invalid_early_struct_return
// VERIFY-DAG: error: verification failed: invalid_conditional_struct_return
