// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 %s -- -DSPEC 2>&1 | FileCheck %s --check-prefix=SPEC
//
// [[cppverify::trusted]] on a declaration says that callers which see no
// definition assume the contract. A definition that only inherits the mark
// from such a declaration is verified, so a wrong body is found; on a
// definition itself, the mark leaves the body unverified.

namespace cv = cppverify;

// As a header declares it.
[[cppverify::trusted]] int clamp100(int x)
  cv::post(cv::result >= 0 && cv::result <= 100);

int clamp100(int x)
{
  if (x < 0)
    return 0;
  if (x > 100)
    return 101;
  return x;
}

int scaled(int x)
  cv::post(cv::result >= 0 && cv::result <= 200)
{
  return 2 * clamp100(x);
}

[[cppverify::trusted]] int halved(int x)
  cv::pre(x >= 0)
  cv::post(cv::result >= 0)
{
  return x - 1;
}

[[cppverify::trusted]] int above(int x)
  cv::post(cv::result > x);

int uses_above(int x)
  cv::pre(x < 100)
  cv::post(cv::result > x)
{
  return above(x);
}

// CHECK: trusted_declarations.cpp:13:28: error: verification failed: clamp100 [{{.*}}::postcondition@13:28] (counterexample: {{.*}}result [ssa={{.*}}] [type=i32] = 101
// CHECK: Unresolved: scaled [backend=z3] [reason=callee.contract] (relies on the contract of clamp100, which is not established)
// CHECK: Trusted: halved (contract assumed, not verified)
// CHECK: Trusted: above (contract assumed, not verified)
// CHECK: Verified: uses_above [backend=z3] [trusts=above]

// A spec cannot be trusted, on any of its declarations.
#ifdef SPEC
[[cppverify::trusted]] cv::spec int twice(int x);

cv::spec int twice(int x) { return 2 * x; }
#endif
// SPEC: error: twice: {{\[\[cppverify::trusted\]\]}} does not apply to a spec function, whose definition is its meaning
