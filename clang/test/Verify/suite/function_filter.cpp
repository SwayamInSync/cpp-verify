// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --check-prefix=ALL
// RUN: not %cpp-verify --jobs=1 --function=uses_wrong %s -- 2>&1 | FileCheck %s --check-prefix=ONE --implicit-check-not=Verified --implicit-check-not=error:
// RUN: %cpp-verify --jobs=1 --function='add_*' %s -- 2>&1 | FileCheck %s --check-prefix=GLOB --implicit-check-not=uses_ --implicit-check-not=error:
// RUN: rm -f %t.cpv
// RUN: not %cpp-verify --jobs=1 --function=uses_wrong --obligation-out=%t.cpv %s -- > /dev/null 2>&1
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 | FileCheck %s --check-prefix=RAN --implicit-check-not=add_two
// RUN: %cpp-verify --jobs=1 --function=uses_add %s -- 2>&1 | FileCheck %s --check-prefix=CALLEE --implicit-check-not=Verified
// RUN: not %cpp-verify --jobs=1 --function=uses_bad %s -- 2>&1 | FileCheck %s --check-prefix=SPEC --implicit-check-not=error:
// RUN: %cpp-verify --jobs=1 --function=reach %s -- 2>&1 | FileCheck %s --check-prefix=PREDICATE --implicit-check-not=Verified
// RUN: not %cpp-verify --jobs=1 --function=climbs %s -- 2>&1 | FileCheck %s --check-prefix=STEP
// RUN: not %cpp-verify --jobs=1 --solver-rlimit=1 --function=reach %s -- 2>&1 | FileCheck %s --check-prefix=RULES
// RUN: not %cpp-verify --jobs=1 --function=nothing %s -- 2>&1 | FileCheck %s --check-prefix=NONE
// RUN: %cpp-verify --list-functions --function='add_*' %s -- 2>&1 | FileCheck %s --check-prefix=LIST --implicit-check-not=uses_
//
// --function reports only the functions whose names match: a glob pattern,
// repeatable. What their verdicts rely on is verified too, so each verdict
// is the one a run of the whole file gives; what they do not rely on is not
// verified at all.

namespace cv = cppverify;

int add_one(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

int add_two(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 2)
{
  return x + 2;
}

int wrong(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x)
{
  return x + 1;
}

int uses_wrong(int x)
  cv::pre(x < 50)
  cv::post(cv::result == x + 1)
{
  int y = wrong(x);
  return y + 1;
}

int uses_add(int x)
  cv::pre(x < 50)
  cv::post(cv::result == x + 2)
{
  int y = add_one(x);
  return y + 1;
}

// A spec whose termination fails has no definition, whoever is selected.
cv::spec int bad(int n)
  cv::decreases(n)
{
  return n > 100 ? 0 : bad(n + 1);
}

int uses_bad(int x)
  cv::post(bad(x) == bad(x) + 0)
{
  return x;
}

int jumps(int x)
  cv::post(true)
{
  goto done;
done:
  return x;
}

cv::spec bool edge(int a, int b) { return b == a + 1; }

cv::spec bool reach(int a, int b)
  cv::inductive
{
  return a == b || cv::exists(c, edge(a, c) && reach(c, b));
}

// Its postcondition is false at a == b; the induction that refutes it is
// a generated function.
cv::spec bool climbs(int a, int b)
  cv::inductive
  cv::post(!cv::result || a < b)
{
  return a == b || cv::exists(c, edge(a, c) && climbs(c, b));
}

// ALL: Verified: add_one [backend=z3]
// ALL: Verified: add_two [backend=z3]
// ALL: error: verification failed: wrong
// ALL: Unresolved: uses_wrong [backend=z3] [reason=callee.contract] (relies on the contract of wrong, which is not established)
// ALL: Verified: uses_add [backend=z3]
// ALL: error: spec decreases failed: bad
// ALL: Unresolved: uses_bad [backend=z3] [reason=spec.termination]
// ALL: Verified: inductive predicate: reach
// ALL: Verified: inductive predicate: climbs
// ALL: Unresolved: spec post: climbs [reason=spec.post]
// ALL: error: spec post by induction failed: climbs
// ALL: Summary: 5 verified, 3 failed, 4 unresolved (callee.contract 1, construct.unsupported 1, spec.post 1, spec.termination 1)

// The same verdict, alone: wrong is verified, and its failure demotes it.
// ONE: Unresolved: uses_wrong [backend=z3] [reason=callee.contract] (relies on the contract of wrong, which is not established)
// ONE-NEXT: Summary: 1 unresolved (callee.contract 1)

// GLOB: Verified: add_one [backend=z3]
// GLOB-NEXT: Verified: add_two [backend=z3]
// GLOB-NEXT: Summary: 2 verified

// Only uses_wrong and what it relies on were verified.
// RAN-DAG: wrong
// RAN-DAG: uses_wrong

// A callee that verifies is verified, so its caller is.
// CALLEE: Verified: uses_add [backend=z3]
// CALLEE-NEXT: Summary: 1 verified

// SPEC: Unresolved: uses_bad [backend=z3] [reason=spec.termination] (relies on the definition of bad, whose termination is not established)
// SPEC-NEXT: Summary: 1 unresolved (spec.termination 1)

// An inductive predicate is reported with its rules.
// PREDICATE: Verified: inductive predicate: reach
// PREDICATE-NEXT: Summary: 1 verified

// Its step and rule proofs are reported with it when they do not hold.
// RULES: Unresolved: inductive predicate: reach [reason=spec.inductive] (its rules are not established: monotonicity, case analysis, introduction)
// RULES-NEXT: function_filter.cpp:[[#]]:3: Unresolved: spec decreases unresolved: reach
// RULES-NEXT: function_filter.cpp:[[#]]:3: Unresolved: reach (monotonicity)
// RULES-NEXT: function_filter.cpp:[[#]]:3: Unresolved: reach (case analysis)
// RULES-NEXT: function_filter.cpp:[[#]]:3: Unresolved: reach (introduction)
// RULES-NEXT: Summary: 5 unresolved ({{.*}}spec.inductive 1)

// The induction of a generated function is reported with its predicate.
// STEP: Verified: inductive predicate: climbs
// STEP-NEXT: Unresolved: spec post: climbs [reason=spec.post] (relies on the postcondition of climbs.step, which is not established)
// STEP-NEXT: function_filter.cpp:92:24: error: spec post by induction failed: climbs
// STEP: Summary: 1 verified, 1 failed, 1 unresolved (spec.post 1)

// NONE: error: no function matches --function=nothing

// LIST: function_filter.cpp:22:5: function add_one
// LIST-NEXT: function_filter.cpp:29:5: function add_two
