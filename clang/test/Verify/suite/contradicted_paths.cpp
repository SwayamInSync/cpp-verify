// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: grep 'warning:' %t | FileCheck %s --check-prefix=WARN --implicit-check-not=warning:
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- | FileCheck %s --check-prefix=JSON
//
// The facts the verifier adds about the specs a program applies (their
// definitions, postconditions, unfoldings, and choices' axioms) are meant to
// be theorems. A path the code alone reaches that they close is either dead
// code or a sign that a fact is wrong, as a definition that cannot hold made
// a path impossible in F38, so that every claim on it held vacuously; the
// first such point of a verified function is reported. A path dead by the
// code itself, its preconditions and checks included, is not.

namespace cv = cppverify;

cv::spec int tri(int n)
  cv::decreases(n)
  cv::post(cv::result >= 0)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

cv::spec int steps(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : steps(n - 1) + 1;
}

// Closed by tri's postcondition.
int checked_tri(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::result >= 0)
{
  if (t < 0)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: checked_tri: the facts about tri contradict the path to the true branch here, which the code alone reaches, so every claim on that path holds vacuously; either the path cannot happen, and it is dead code, or a fact about tri is wrong
    return -1;
  return t;
}
// CHECK-DAG: Verified: checked_tri [backend=z3]

// Closed by steps's definition.
int checked_steps(int n, int t)
  cv::pre(n == 0 && t == steps(n))
  cv::post(cv::result >= 0)
{
  if (t < 0)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: checked_steps: the facts about steps contradict the path to the true branch here
    return -1;
  return t;
}

// A return closed by a fact, in a loop's body: the first point reported.
int first_negative(const int *a, int n, int t)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::result >= -1)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    if (t + i < 0)
      // WARN: contradicted_paths.cpp:[[@LINE-1]]:5: warning: first_negative: the facts about tri contradict the path to the true branch here
      return i;
  }
  return -1;
}

// A loop's body closed by a fact.
int drain(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::result >= 0)
{
  int s = t;
  while (s < 0)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: drain: the facts about tri contradict the path to the loop's body here
    cv::invariant(t <= s)
    cv::decreases(-s)
  {
    s = s + 1;
  }
  return s;
}

// A loop left only by its return: the path after it is closed.
int climb(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n) && t <= 6)
  cv::post(cv::result > 5)
{
  int s = t;
  while (s >= 0)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: climb: the facts about tri contradict the path to the loop's exit here
    cv::invariant(t <= s && s <= 6)
    cv::decreases(6 - s)
  {
    if (s > 5)
      return s;
    s = s + 1;
  }
  return 6;
}

// Closed by a choice's axiom.
cv::spec int pick(int n) { return cv::choose(k, 0, 10, k == n); }

int picked(int n, int h)
  cv::pre(0 <= n && n < 10 && h == pick(n))
  cv::post(cv::result == n)
{
  if (h != n)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: picked: the facts about cppverify::choose contradict the path to the true branch here
    return n;
  return h;
}

// Closed by the induction hypothesis of a cluster: total's postcondition
// where its measure is below the lemma's.
cv::proof void total_nonneg(int n);

cv::spec int total(int n)
  cv::decreases(n, 0)
  cv::post(cv::result >= 0) by { if (n > 0) total_nonneg(n - 1); }
{
  return n <= 0 ? 0 : total(n - 1) + n;
}

cv::proof void total_nonneg(int n)
  cv::decreases(n, 1)
  cv::post(total(n) >= 0)
{
  if (total(n) < 0)
    // WARN: contradicted_paths.cpp:[[@LINE-1]]:3: warning: total_nonneg: the facts about total contradict the path to the true branch here
    return;
  if (n > 0)
    total_nonneg(n - 1);
}
// CHECK-DAG: Verified: total_nonneg [backend=z3]

// A fact about builtin specs alone is the language's: the length of a
// reverse, here, in a function that also applies a spec of its own.
cv::proof void rev_len(cv::seq s, int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(s.reverse().len() == s.len())
{
  if (s.reverse().len() != s.len())
    return;
}
// CHECK-DAG: Verified: rev_len [backend=z3]

// And so is the definition of a builtin spec.
cv::proof void rev_empty(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::seq_empty().reverse().len() == 0)
{
  if (cv::seq_empty().reverse().len() != 0)
    return;
}
// CHECK-DAG: Verified: rev_empty [backend=z3]

// A postcondition that does not hold closes the path: the verdict that rests
// on it is not established (a recursive spec proves its postcondition with
// its termination), and the finding goes with it.
cv::spec int wrong(int n)
  cv::decreases(n)
  cv::post(cv::result > 0)
{
  return n <= 0 ? 0 : wrong(n - 1) + 1;
}
// CHECK-DAG: error: spec decreases and post failed: wrong

int uses_wrong(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == wrong(n))
  cv::post(cv::result >= 0)
{
  if (t <= 0)
    return 0;
  return t;
}
// CHECK-DAG: Unresolved: uses_wrong [backend=z3] [reason=spec.termination]

// Dead by the precondition itself: nothing to report.
int defensive(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n) && t >= 0)
  cv::post(cv::result == t)
{
  if (t < 0)
    return -1;
  return t;
}
// CHECK-DAG: Verified: defensive [backend=z3]

// The fact stated where the path ends, so the code says it.
int stated(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::result >= 0)
{
  cv::check(t >= 0);
  if (t < 0)
    return -1;
  return t;
}
// CHECK-DAG: Verified: stated [backend=z3]

// Every path reached.
int plain(int n, int t)
  cv::pre(0 <= n && n <= 100 && t == tri(n))
  cv::post(cv::result == t + 1)
{
  if (t > 5)
    return t + 1;
  return t + 1;
}
// CHECK-DAG: Verified: plain [backend=z3]

// No spec, so no fact to check: a precondition closes this path.
int no_spec(int x)
  cv::pre(x >= 0)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    return -1;
  return x;
}
// CHECK-DAG: Verified: no_spec [backend=z3]

// JSON: "function":"checked_tri",{{.*}}"severity":"warning"
