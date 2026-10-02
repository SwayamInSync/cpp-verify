// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=1,2,3 %s 2>&1 | FileCheck %s --check-prefix=IR
//
// A loop writes only the objects its stores and calls reach, so every other
// cell keeps its value without an invariant saying so. A loop's modifies
// names what it may write, read in each iteration's state (ACSL's loop
// assigns): every iteration starts with the cells outside it unchanged since
// the loop began, and must end that way.

spec bool valid(int *p, int n) { return true; }
spec bool valid(const int *p, int n) { return true; }

void keeps_input(int *a, const int *b, int n)
  pre(n >= 1 && n <= 100 && valid(a, n) && valid(b, 1))
  modifies(*a)
  post(b[0] == old(b[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    a[i] = 0;
  }
}
// CHECK-DAG: Verified: keeps_input

void writes_input(int *a, int *b, int n)
  pre(n >= 1 && n <= 100 && valid(a, n) && valid(b, 1))
  modifies(*a, *b)
  post(b[0] == old(b[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    a[i] = 0;
    b[0] = i;
  }
}
// CHECK-DAG: error: verification failed: writes_input [{{.*}}::postcondition@

// The loop writes only a[0..n), so a[n] keeps its value.
void keeps_tail(int *a, int n)
  pre(valid(a, n + 1) && n >= 1 && n <= 1000)
  modifies(*a)
  post(a[n] == old(a[n]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    modifies(a[0 : n])
    decreases(n - i)
  {
    a[i] = 0;
  }
}
// CHECK-DAG: Verified: keeps_tail

// Without the loop's modifies the tail is part of the written object.
void loses_tail(int *a, int n)
  pre(valid(a, n + 1) && n >= 1 && n <= 1000)
  modifies(*a)
  post(a[n] == old(a[n]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    a[i] = 0;
  }
}
// CHECK-DAG: error: verification failed: loses_tail [{{.*}}::postcondition@

// Read in each iteration, a[0 : i] is the prefix written so far.
void untouched_suffix(int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  modifies(*a)
  post(forall(k, 0, n, a[k] == 1))
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n && forall(k, 0, i, a[k] == 1))
    modifies(a[0 : i])
    decreases(n - i)
  {
    a[i] = 1;
    i = i + 1;
  }
}
// CHECK-DAG: Verified: untouched_suffix

void writes_ahead(int *a, int n)
  pre(valid(a, n + 1) && n >= 1 && n <= 1000)
  modifies(*a)
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    modifies(a[0 : i])
    decreases(n - i)
  {
    a[i + 1] = 0;
  }
}
// CHECK-DAG: error: verification failed: writes_ahead [{{.*}}::frame@[[@LINE-6]]:14]

// A continue ends the iteration, so the frame is checked there too.
void writes_then_continues(int *a, int *b, int n)
  pre(valid(a, n) && valid(b, 1) && n >= 1 && n <= 1000)
  modifies(*a, *b)
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    modifies(*a)
    decreases(n - i)
  {
    if (i == 0) {
      b[0] = 1;
      continue;
    }
    a[i] = 0;
  }
}
// CHECK-DAG: error: verification failed: writes_then_continues [{{.*}}::frame@[[@LINE-10]]:14]

void set(int *x)
  pre(x != nullptr)
  modifies(*x)
  post(*x == 0)
{
  *x = 0;
}

// A call in the loop writes only what its modifies names.
void calls_keep_input(int *a, const int *b, int n)
  pre(valid(a, n) && valid(b, 1) && n >= 1 && n <= 1000)
  modifies(*a)
  post(b[0] == old(b[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    modifies(*a)
    decreases(n - i)
  {
    set(a + i);
  }
}
// CHECK-DAG: Verified: calls_keep_input

// A spec over memory the loop does not write keeps its value.
spec int total(const int *a, int n)
  reads(a, n)
  decreases(n)
{
  return n <= 0 ? 0 : total(a, n - 1) + a[n - 1];
}

void keeps_sum(int *out, const int *in, int n)
  pre(valid(out, n) && valid(in, n) && n >= 0 && n <= 1000)
  modifies(*out)
  post(total(in, n) == old(total(in, n)))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    out[i] = 1;
  }
}
// CHECK-DAG: Verified: keeps_sum

// A loop that writes a parameter's object only at the parameter writes one
// cell.
void counts(int *count, const int *a, int n)
  pre(count != nullptr && valid(a, n) && n >= 1 && n <= 1000)
  pre(*count == 0)
  modifies(*count)
  post(*count >= 0 && *count <= n && a[0] == old(a[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && 0 <= *count && *count <= i)
    decreases(n - i)
  {
    if (a[i] > 0)
      *count = *count + 1;
  }
}
// CHECK-DAG: Verified: counts

void counts_wrongly(int *count, int *a, int n)
  pre(count != nullptr && valid(a, n) && n >= 1 && n <= 1000 && *count == 0)
  modifies(*count, *a)
  post(a[0] == old(a[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    *count = i;
    *a = i;
  }
}
// CHECK-DAG: error: verification failed: counts_wrongly [{{.*}}::postcondition@

// A store's object is found from its address: a pointer walking through a
// stays in a, so b keeps its value.
void walks(int *a, int *b, int n)
  pre(valid(a, n) && valid(b, 1) && n >= 1 && n <= 1000)
  modifies(*a)
  post(b[0] == old(b[0]))
{
  int *q = a;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && q == a + i)
    decreases(n - i)
  {
    *q = 0;
    q = q + 1;
  }
}
// CHECK-DAG: Verified: walks

// A pointer chosen among the parameters: the loop is framed by the
// function's modifies, so c keeps its value.
void chosen_keeps_other(int *a, int *b, int *c, int n, bool first)
  pre(valid(a, n) && valid(b, n) && valid(c, 1) && n >= 1 && n <= 1000)
  modifies(*a, *b)
  post(c[0] == old(c[0]))
{
  int *p = first ? a : b;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    p[i] = 0;
  }
}
// CHECK-DAG: Verified: chosen_keeps_other

// The chosen object may be b.
void chosen_writes_b(int *a, int *b, int n, bool first)
  pre(valid(a, n) && valid(b, n) && n >= 1 && n <= 1000)
  modifies(*a, *b)
  post(b[0] == old(b[0]))
{
  int *p = first ? a : b;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    p[i] = 0;
  }
}
// CHECK-DAG: error: verification failed: chosen_writes_b [{{.*}}::postcondition@

// With aliases(a, b), a may be b.
void aliased_writes(int *a, int *b, int n)
  aliases(a, b)
  pre(valid(a, n) && valid(b, 1) && n >= 1 && n <= 1000)
  modifies(*a, *b)
  post(b[0] == old(b[0]))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    a[i] = 0;
  }
}
// CHECK-DAG: error: verification failed: aliased_writes [{{.*}}::postcondition@

// IR: fn untouched_suffix
// IR: while
// IR: modifies
// IR-NEXT: load
// IR: range 4
// IR: heap_frame __heap_{{[0-9]+}} -> __heap_{{[0-9]+}} except
// IR: heap_frame
