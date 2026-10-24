// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=5 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// An invariant holds at a loop's head together with its definedness: both
// are checked on entry and at the end of every iteration, so the reads it
// makes are initialized and in bounds there. A loop starts no lifetime, so
// it only initializes storage: what was initialized before it still is.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

int filled()
  cppverify::post(cppverify::result == 0)
{
  int a[4];
  for (int i = 0; i < 4; i = i + 1)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::invariant(cppverify::forall(k, 0, i, a[k] == 0))
    cppverify::decreases(4 - i)
  {
    a[i] = 0;
  }
  return a[3];
}
// CHECK-DAG: Verified: filled [backend=z3]
// BMC-DAG: Verified: filled [backend=bmc, bound=4]

// The loop reads what was initialized before it, which no invariant states.
void incremented()
{
  int a[4];
  for (int j = 0; j < 4; j = j + 1)
    cppverify::invariant(0 <= j && j <= 4)
    cppverify::invariant(cppverify::forall(k, 0, j, a[k] == 1))
    cppverify::decreases(4 - j)
  {
    a[j] = 1;
  }
  for (int i = 0; i < 4; i = i + 1)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::decreases(4 - i)
  {
    a[i] = a[i] / 2;
  }
}
// CHECK-DAG: Verified: incremented [backend=z3]

// Storage the loop does not write stays initialized.
int kept()
{
  int x = 5;
  int &r = x;
  int a[2];
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    a[i] = i;
  }
  return r;
}
// CHECK-DAG: Verified: kept [backend=z3]

// An element the loop never writes is not initialized after it.
int partially_filled()
{
  int a[4];
  for (int i = 0; i < 3; i = i + 1)
    cppverify::invariant(0 <= i && i <= 3)
    cppverify::invariant(cppverify::forall(k, 0, i, a[k] == 0))
    cppverify::decreases(3 - i)
  {
    a[i] = 0;
  }
  return a[3];
}
// CHECK-DAG: error: verification failed: partially_filled [{{.*}}::initialization@[[@LINE-2]]:3]

// Nor is one it reads before writing.
int read_first()
{
  int a[4];
  int s = 0;
  for (int i = 0; i < 4; i = i + 1)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::decreases(4 - i)
  {
    s = a[i];
    a[i] = s;
  }
  return 0;
}
// CHECK-DAG: error: verification failed: read_first [{{.*}}::initialization@[[@LINE-5]]:7]

// Reading p[i] in an invariant bounds i at the head.
int last(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n > 0)
  cppverify::post(cppverify::result == p[n - 1])
{
  int i = 0;
  while (i + 1 < n)
    cppverify::invariant(p[i] + 0 == p[i])
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return p[i];
}
// CHECK-DAG: Verified: last [backend=z3]

// So does a shift: its amount is in range at the head.
int log2_floor(int n)
  cppverify::pre(n >= 1)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 31)
{
  int k = 0;
  while (k < 30 && (1 << (k + 1)) <= n)
    cppverify::invariant((1 << k) <= n)
    cppverify::decreases(30 - k)
  {
    k = k + 1;
  }
  return k;
}
// CHECK-DAG: Verified: log2_floor [backend=z3]

// The definedness is still checked where the invariant is.
void overrun()
{
  int c[4];
  c[0] = 0;
  c[1] = 0;
  c[2] = 0;
  c[3] = 0;
  int i = 0;
  while (i < 4)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::invariant(c[i] == 0)
    cppverify::decreases(4 - i)
  {
    i = i + 1;
  }
}
// CHECK-DAG: error: verification failed: overrun [{{.*}}::dereference@[[@LINE-6]]:31#2]
