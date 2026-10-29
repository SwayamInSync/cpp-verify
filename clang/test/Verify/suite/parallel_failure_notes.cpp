// RUN: not %cpp-verify --jobs=4 %s -- 2>&1 | FileCheck %s
//
// Functions verified at once each fail with a counterexample through a loop
// whose invariant is too weak, so the notes of each failure unroll its loop
// bound by bound, each bound's module annotated with its sources, beside the
// other functions' lookups. Every lookup takes the verifier's source lock:
// the source manager caches its last lookups, and these raced on that cache.
// Under ThreadSanitizer, without the lock, most runs report the race.

namespace cv = cppverify;

int steps_of_1(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 1)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 1)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 1;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_1 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_2(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 2)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 2)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 2;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_2 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_3(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 3)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 3)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 3;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_3 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_4(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 4)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 4)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 4;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_4 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_5(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 5)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 5)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 5;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_5 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_6(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 6)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 6)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 6;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_6 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_7(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 7)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 7)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 7;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_7 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_8(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 8)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 8)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 8;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_8 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_9(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 9)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 9)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 9;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_9 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_10(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 10)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 10)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 10;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_10 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_11(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 11)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 11)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 11;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_11 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_12(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 12)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 12)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 12;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_12 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_13(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 13)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 13)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 13;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_13 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_14(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 14)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 14)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 14;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_14 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_15(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 15)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 15)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 15;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_15 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

int steps_of_16(int n)
  cv::pre(0 <= n && n <= 9)
  cv::post(cv::result == n * 16)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cv::invariant(0 <= i && s == i * 16)
    cv::decreases(n - i)
  {
    i = i + 1;
    s = s + 16;
  }
  return s;
}
//      CHECK: parallel_failure_notes.cpp:[[@LINE-13]]:23: error: verification failed: steps_of_16 [postcondition]
//      CHECK: note: the counterexample's state at the loop at [[@LINE-10]]:3 is any state its invariants allow, not necessarily one an execution reaches
// CHECK-NEXT: note: no execution fails this check: every loop ends within 9 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof
