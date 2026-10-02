// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
// RUN: not %cpp-verify --backend=bmc --unroll=5 --check-ub %s 2>&1 | FileCheck %s --check-prefixes=CHECK,BMC
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC

// Every correct function below has a wrong twin that must be refuted.

spec bool valid(const int *p, int n) { return true; }
spec bool valid(int *p, int n) { return true; }

int find(const int *p, int n, int target)
  pre(n >= 0 && n <= 4 && valid(p, n))
  post(result >= -1 && result < n)
  post(result < 0 || p[result] == target)
  post(result >= 0 || forall(k, 0, n, p[k] != target))
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    invariant(forall(k, 0, i, p[k] != target))
    decreases(n - i)
  {
    if (p[i] == target)
      return i;
    i = i + 1;
  }
  return -1;
}

int find_wrong(const int *p, int n, int target)
  pre(n >= 0 && n <= 4 && valid(p, n))
  post(result == -1)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    if (p[i] == target)
      return i;
    i = i + 1;
  }
  return -1;
}

int return_state(int n)
  pre(n >= 1 && n <= 4)
  post(result == 3)
{
  int i = 0;
  int x = 0;
  while (i < n)
    invariant(0 <= i && i <= 0)
    decreases(n - i)
  {
    x = 3;
    if (i == 0)
      return x;
    x = 9;
    i = i + 1;
  }
  return 7;
}

int return_state_wrong(int n)
  pre(n >= 1 && n <= 4)
  post(result == 9)
{
  int i = 0;
  int x = 0;
  while (i < n)
    invariant(0 <= i && i <= 0)
    decreases(n - i)
  {
    x = 3;
    if (i == 0)
      return x;
    x = 9;
    i = i + 1;
  }
  return 7;
}

int break_state(int n)
  pre(n >= 2 && n <= 4)
  post(result == 5)
{
  int i = 0;
  int x = 0;
  while (i < n)
    invariant(0 <= i && i <= 1)
    decreases(n - i)
  {
    x = 5;
    if (i == 1)
      break;
    x = 0;
    i = i + 1;
  }
  return x;
}

int break_state_wrong(int n)
  pre(n >= 2 && n <= 4)
  post(result == 0)
{
  int i = 0;
  int x = 0;
  while (i < n)
    invariant(0 <= i && i <= 1)
    decreases(n - i)
  {
    x = 5;
    if (i == 1)
      break;
    x = 0;
    i = i + 1;
  }
  return x;
}

void break_heap(int *p)
  pre(valid(p, 4))
  modifies(*p)
  post(p[0] == 1 && p[1] == 1 && p[2] == old(p[2]))
{
  int i = 0;
  while (i < 4)
    invariant(0 <= i && i <= 1)
    invariant(forall(k, 0, i, p[k] == 1))
    invariant(p[2] == old(p[2]) && p[3] == old(p[3]))
    decreases(4 - i)
  {
    p[i] = 1;
    if (i == 1)
      break;
    i = i + 1;
  }
}

void break_heap_wrong(int *p)
  pre(valid(p, 4))
  modifies(*p)
  post(p[2] == 1)
{
  int i = 0;
  while (i < 4)
    invariant(0 <= i && i <= 1)
    invariant(forall(k, 0, i, p[k] == 1))
    decreases(4 - i)
  {
    p[i] = 1;
    if (i == 1)
      break;
    i = i + 1;
  }
}

int count_odd(int n)
  pre(n >= 0 && n <= 4)
  post(result >= 0 && result <= n)
{
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && 0 <= c && c <= i)
    decreases(n - i)
  {
    if (i % 2 == 0)
      continue;
    c = c + 1;
  }
  return c;
}

int continue_without_step(int n)
  pre(n >= 0 && n <= 4)
  post(true)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    if (i % 2 == 0)
      continue;
    i = i + 1;
  }
  return i;
}

int continue_wrong_invariant(int n)
  pre(n >= 0 && n <= 4)
  post(true)
{
  int i = 0;
  int c = 0;
  while (i < n)
    invariant(0 <= i && i <= n && c == i)
    decreases(n - i)
  {
    i = i + 1;
    if (i % 2 == 0)
      continue;
    c = c + 1;
  }
  return c;
}

int inner_break(int n)
  pre(n >= 0 && n <= 3)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    int j = 0;
    while (j < 3)
      invariant(0 <= j && j <= 3)
      decreases(3 - j)
    {
      if (j == 1)
        break;
      j = j + 1;
    }
    i = i + 1;
  }
  return i;
}

int while_return(bool stop)
  post(result == 0 || result == 1)
{
  while (stop)
    invariant(true)
    decreases(0)
  {
    return 1;
  }
  return 0;
}

int do_return(bool stop)
  post(result == 0 || result == 1)
{
  do {
    if (stop)
      return 1;
  } while (false)
    invariant(true)
    decreases(0);
  return 0;
}

int for_return(bool stop)
  post(result == 0 || result == 1)
{
  for (int index = 0; index < 1; ++index)
    invariant(index >= 0 && index <= 1)
    decreases(1 - index)
  {
    if (stop)
      return 1;
  }
  return 0;
}

// A return or break leaves the loop without re-establishing the invariant.
// PASSIVE-LABEL: passive return_state
// PASSIVE: assert invariant-entry
// PASSIVE: assert invariant-preserved
// PASSIVE-NOT: assert invariant-preserved
// PASSIVE: assert missing-return
// PASSIVE-LABEL: passive break_state
// PASSIVE: assert invariant-entry
// PASSIVE: assert invariant-preserved
// PASSIVE-NOT: assert invariant-preserved
// PASSIVE: assert missing-return

// A continue re-establishes the invariant and decreases the measure, then the
// body end does the same.
// PASSIVE-LABEL: passive count_odd
// PASSIVE: assert invariant-entry
// PASSIVE: assert invariant-preserved
// PASSIVE: assert termination
// PASSIVE: assert invariant-preserved
// PASSIVE: assert termination
// PASSIVE-NOT: assert invariant-preserved
// PASSIVE: assert missing-return
// VC-LABEL: vc count_odd
// VC: obligation {{.*}} invariant-entry
// VC: obligation {{.*}} invariant-preserved
// VC: obligation {{.*}} termination
// VC: obligation {{.*}} invariant-preserved
// VC: obligation {{.*}} termination
// VC: obligation {{.*}} postcondition

// The for increment runs before continue.
// VCR-LABEL: fn count_odd
// VCR: {{^ +}}if
// VCR: assign i
// VCR-NEXT: +
// VCR-NEXT: i
// VCR-NEXT: 1
// VCR-NEXT: continue

// CHECK-DAG: Verified: find
// CHECK-DAG: verification failed: find_wrong
// CHECK-DAG: Verified: return_state
// CHECK-DAG: verification failed: return_state_wrong
// CHECK-DAG: Verified: break_state
// CHECK-DAG: verification failed: break_state_wrong
// CHECK-DAG: Verified: break_heap
// CHECK-DAG: verification failed: break_heap_wrong
// CHECK-DAG: Verified: count_odd
// DEDUCTIVE-DAG: verification failed: continue_without_step
// BMC-DAG: BoundedSafe: continue_without_step
// DEDUCTIVE-DAG: verification failed: continue_wrong_invariant
// BMC-DAG: Verified: continue_wrong_invariant
// CHECK-DAG: Verified: inner_break
// CHECK-DAG: Verified: while_return
// CHECK-DAG: Verified: do_return
// CHECK-DAG: Verified: for_return
