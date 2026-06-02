// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=FAIL

spec int id_spec(int a)
  recommends(a >= 0)
{
  return a;
}

int bad_call(int a)
  pre(true)
  post(result == a)
{
  return id_spec(-1);
}

// FAIL: verification failed: bad_call
// FAIL: recommends