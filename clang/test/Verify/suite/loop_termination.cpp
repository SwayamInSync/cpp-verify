// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
// RUN: not %cpp-verify --backend=bmc --unroll=4 %s 2>&1 | FileCheck %s --check-prefixes=CHECK,BMC
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 | FileCheck %s --check-prefix=JSON
//
// Total correctness: every loop needs a termination measure, and every call
// within a recursion cycle must lower the caller's. decreases(*) allows a
// loop or an executable function to diverge, and a proof then covers only
// the executions that terminate, as does a proof of any caller.

// Without a measure the loop's termination is not established. A bounded
// proof of its unwinding does establish it.
int count_up(int n)
  cppverify::pre(n >= 0 && n <= 3)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
  {
    i = i + 1;
  }
  return i;
}
// DEDUCTIVE-DAG: Unresolved: count_up [backend=z3] [reason=decreases.missing] (the loop at 17:3 has no decreases clause: give it a measure, or cppverify::decreases(*) to allow it to diverge)
// BMC-DAG: Verified: count_up [backend=bmc, bound={{[0-9]+}}]
// JSON-DAG: "function":"count_up"{{.*}}"reason":"decreases.missing"{{.*}}"status":"unresolved"

int count_measured(int n)
  cppverify::pre(n >= 0 && n <= 3)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK-DAG: Verified: count_measured

// The measure need only be nonnegative before a step: from 1 it may reach -1.
int converge(int n)
  cppverify::pre(n >= 0 && n <= 1000)
  cppverify::post(cppverify::result >= 0)
{
  int i = 0;
  int j = n;
  while (i < j)
    cppverify::invariant(0 <= i && i <= n && j <= n && j >= i - 1)
    cppverify::decreases(j - i)
  {
    i = i + 1;
    j = j - 1;
  }
  return i;
}
// DEDUCTIVE-DAG: Verified: converge [backend=z3]

int search(int n)
  cppverify::pre(n >= 1 && n < 1000)
  cppverify::post(cppverify::result >= 0)
{
  int steps = 0;
  while (n != 1)
    cppverify::invariant(steps >= 0 && n >= 1)
    cppverify::decreases(*)
  {
    n = n % 2 == 0 ? n / 2 : (n < 1000 ? 3 * n + 1 : 1);
    if (steps < 1000000)
      steps = steps + 1;
  }
  return steps;
}
// DEDUCTIVE-DAG: Verified: search [backend=z3] [partial]
// DEDUCTIVE-DAG: warning: search: proved only for executions that terminate: cppverify::decreases(*) at 68:26 allows it to diverge
// JSON-DAG: "function":"search"{{.*}}"partial":true{{.*}}"status":"verified"

int uses_search(int n)
  cppverify::pre(n >= 1 && n < 1000)
  cppverify::post(cppverify::result >= 0)
{
  return search(n);
}
// DEDUCTIVE-DAG: Verified: uses_search [backend=z3] [partial]
// DEDUCTIVE-DAG: warning: uses_search: proved only for executions that terminate: it calls search, which may diverge

int spin(int n)
  cppverify::decreases(*)
  cppverify::post(cppverify::result == 0)
{
  if (n == 0)
    return 0;
  return spin(n);
}
// DEDUCTIVE-DAG: Verified: spin [backend=z3] [partial]

// Recursion through a heap store is checked at the call.
void fill(int &value, int n)
  cppverify::pre(n >= 0)
  cppverify::modifies(value)
  cppverify::decreases(n)
{
  value = n;
  if (n > 0)
    fill(value, n - 1);
}
// CHECK-DAG: Verified: fill

void refill(int &value, int n)
  cppverify::pre(n >= 0)
  cppverify::modifies(value)
  cppverify::decreases(n)
{
  value = n;
  if (n > 0)
    refill(value, n);
}
// CHECK-DAG: error: verification failed: refill [{{.*}}::termination@118:5]
