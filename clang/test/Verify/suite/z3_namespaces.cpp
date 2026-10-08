// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

namespace left {
int project(int x)
  cppverify::pre(x < 2147483647)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

cppverify::spec int measure(int x) {
  return x + 10;
}
} // namespace left

namespace right {
int project(int x)
  cppverify::pre(x < 2147483646)
  cppverify::post(cppverify::result == x + 2)
{
  return x + 2;
}

cppverify::spec int measure(int x) {
  return x + 20;
}
} // namespace right

int call_left_namespace()
  cppverify::post(cppverify::result == 4)
{
  return left::project(3);
}

int call_right_namespace()
  cppverify::post(cppverify::result == 5)
{
  return right::project(3);
}

int use_namespaced_specs()
  cppverify::post(left::measure(1) == 11)
  cppverify::post(right::measure(1) == 21)
{
  return 0;
}

// VERIFY-DAG: Verified: call_left_namespace
// VERIFY-DAG: Verified: call_right_namespace
// VERIFY-DAG: Verified: use_namespaced_specs
