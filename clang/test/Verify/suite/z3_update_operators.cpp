// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

int compound_add(int x)
  pre(x == 10)
  post(result == 15)
{
  x += 5;
  return x;
}

int prefix_increment(int x)
  pre(x == 10)
  post(result == 11)
{
  ++x;
  return x;
}

int postfix_increment(int x)
  pre(x == 10)
  post(result == 11)
{
  x++;
  return x;
}

int reject_old_compound_model(int x)
  pre(x == 10)
  post(result == 5)
{
  x += 5;
  return x;
}

int reject_dropped_increment(int x)
  pre(x == 10)
  post(result == 10)
{
  x++;
  return x;
}

// CHECK-DAG: Verified: compound_add
// CHECK-DAG: Verified: prefix_increment
// CHECK-DAG: Verified: postfix_increment
// CHECK-DAG: error: verification failed: reject_old_compound_model
// CHECK-DAG: error: verification failed: reject_dropped_increment
