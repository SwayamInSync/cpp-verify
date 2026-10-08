// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=FAIL \
// RUN:   --implicit-check-not="recommends not implied" \
// RUN:   --implicit-check-not="call in good_call"

cppverify::spec int id_spec(int a)
  cppverify::recommends(a >= 0)
{
  return a;
}

int good_call(int a)
  cppverify::pre(a >= 0 && a <= 100)
  cppverify::post(cppverify::result == id_spec(a))
{
  return a;
}

int bad_call(int a)
  cppverify::pre(true)
  cppverify::post(cppverify::result == id_spec(-1))
{
  return a;
}

int bad_nested_call(int a)
  cppverify::pre(a == -1)
  cppverify::post(cppverify::result == 0)
{
  cppverify::ghost {
    int value = 0;
    if (a == -1)
      value = (short)id_spec(a);
    cppverify::check(value == 0);
  }
  return 0;
}

// FAIL-DAG: Verified: good_call
// FAIL-DAG: error: verification failed: bad_call
// FAIL-DAG: error: verification failed: bad_nested_call
// FAIL-DAG: warning: recommends of spec id_spec may be violated at call in bad_call
// FAIL-DAG: warning: recommends of spec id_spec may be violated at call in bad_nested_call