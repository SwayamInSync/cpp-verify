// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=FAIL \
// RUN:   --implicit-check-not="recommends not implied" \
// RUN:   --implicit-check-not="call in good_call"

spec int id_spec(int a)
  recommends(a >= 0)
{
  return a;
}

int good_call(int a)
  pre(a >= 0 && a <= 100)
  post(result == a)
{
  return id_spec(a);
}

int bad_call(int a)
  pre(true)
  post(result == a)
{
  return id_spec(-1);
}

int bad_nested_call(int a)
  pre(a == -1)
  post(result == 0)
{
  int value = 0;
  if (a == -1)
    value = (short)id_spec(a);
  return value;
}

// FAIL-DAG: Verified: good_call
// FAIL-DAG: error: verification failed: bad_call
// FAIL-DAG: error: verification failed: bad_nested_call
// FAIL-DAG: warning: recommends of spec id_spec may be violated at call in bad_call
// FAIL-DAG: warning: recommends of spec id_spec may be violated at call in bad_nested_call