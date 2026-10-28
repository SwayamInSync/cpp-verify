// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --check-prefix=DEFAULT --implicit-check-not='spec axiom'
// RUN: not %cpp-verify --jobs=1 --quiet %s -- 2>&1 | FileCheck %s --check-prefix=QUIET --implicit-check-not=Verified --implicit-check-not=Trusted
// RUN: not %cpp-verify --jobs=1 --verbose %s -- 2>&1 | FileCheck %s --check-prefix=VERBOSE
// RUN: %cpp-verify --list-functions %s -- 2>&1 | FileCheck %s --check-prefix=LIST
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: %cpp-verify --help | FileCheck %s --check-prefix=HELP
//
// A run ends with one line that counts its verdicts by kind, with the
// reasons of the unresolved ones. --quiet prints only what needs attention,
// --verbose also the spec functions that need no check, and
// --list-functions what a run would verify, without verifying it.

namespace cv = cppverify;

cv::spec int twice(int x) { return 2 * x; }

cv::spec int down(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : down(n - 1);
}

cv::proof void down_zero(int n)
  cv::pre(n <= 0)
  cv::post(down(n) == 0)
{
}

int add_one(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

int add_two(int x)
  cv::pre(x < 100)
  cv::post(cv::result == twice(x))
{
  return x + 2;
}

int lookup(int x)
  cv::post(true)
{
  goto done;
done:
  return x;
}

[[cppverify::trusted]] int clamp(int x)
  cv::post(0 <= cv::result && cv::result <= 255);

int first(const int *p)
  cv::pre(cv::valid(p, 1))
  cv::post(cv::result == p[0])
{
  return p[0];
}

// DEFAULT: error: lookup: goto is unsupported
// DEFAULT: error: lookup: labels are unsupported
// DEFAULT: Verified: spec decreases: down
// DEFAULT-NEXT: Verified: down_zero [backend=z3]
// DEFAULT-NEXT: Verified: add_one [backend=z3]
// DEFAULT-NEXT: error: verification failed: add_two
// DEFAULT: Trusted: clamp
// DEFAULT-NEXT: Verified: first [backend=z3]
// DEFAULT-NEXT: Summary: 4 verified, 1 failed, 1 unresolved (construct.unsupported 1), 1 trusted in {{[0-9]+\.[0-9]}} s
// DEFAULT-NOT: {{.}}

// QUIET: error: lookup: goto is unsupported
// QUIET: error: lookup: labels are unsupported
// QUIET: error: verification failed: add_two
// QUIET: Summary: 4 verified, 1 failed, 1 unresolved (construct.unsupported 1), 1 trusted in

// VERBOSE: Verified: spec axiom: twice
// VERBOSE-NEXT: Verified: spec decreases: down
// VERBOSE-NEXT: Verified: down_zero [backend=z3]
// VERBOSE: Summary: 4 verified, 1 failed

// LIST: command_line.cpp:15:14: spec twice
// LIST-NEXT: command_line.cpp:17:14: spec down
// LIST-NEXT: command_line.cpp:23:16: proof down_zero
// LIST-NEXT: command_line.cpp:29:5: function add_one
// LIST-NEXT: command_line.cpp:36:5: function add_two
// LIST-NEXT: command_line.cpp:43:5: function lookup
// LIST-NEXT: command_line.cpp:51:28: trusted clamp
// LIST-NEXT: command_line.cpp:54:5: function first
// LIST-NEXT: command_line.cpp:46:3: error: lookup: goto is unsupported
// LIST-NOT: Verified
// LIST-NOT: Summary

// JSON-NOT: Summary

// HELP: --list-functions
// HELP: --quiet
// HELP: --timeout=<uint> {{.*}}(default 30000, 0 = no limit)
// HELP: --verbose
