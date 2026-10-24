// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=5 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// A loop that writes local or dynamic storage through the pointer its
// allocation defined writes only that object: every other object keeps its
// value across the loop without an invariant saying so.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

int kept_value()
  cppverify::post(cppverify::result == 5)
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
// CHECK-DAG: Verified: kept_value [backend=z3]
// BMC-DAG: Verified: kept_value [backend=bmc, bound=2]

int other_array()
  cppverify::post(cppverify::result == 7)
{
  int a[3];
  int b[2];
  b[0] = 3;
  b[1] = 4;
  for (int i = 0; i < 3; i = i + 1)
    cppverify::invariant(0 <= i && i <= 3)
    cppverify::decreases(3 - i)
  {
    a[i] = 0;
  }
  return b[0] + b[1];
}
// CHECK-DAG: Verified: other_array [backend=z3]

struct Pair {
  int a;
  int b;
};

// The loop reads one local record, kept in memory for its reference, and
// writes another object.
int record_read()
  cppverify::post(cppverify::result == 2)
{
  Pair p;
  p.a = 1;
  p.b = 2;
  int &pb = p.b;
  int a[3];
  for (int i = 0; i < 3; i = i + 1)
    cppverify::invariant(0 <= i && i <= 3)
    cppverify::decreases(3 - i)
  {
    a[i] = p.a;
  }
  return pb;
}
// CHECK-DAG: Verified: record_read [backend=z3]

// A loop that writes a parameter's object and a local one keeps a third.
int with_parameter(int *q)
  cppverify::pre(q != nullptr)
  cppverify::modifies(*q)
  cppverify::post(cppverify::result == 9)
{
  int keep[1];
  keep[0] = 9;
  int a[2];
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    a[i] = i;
    *q = i;
  }
  return keep[0];
}
// CHECK-DAG: Verified: with_parameter [backend=z3]

void set(int &r, int v)
  cppverify::modifies(r)
  cppverify::post(r == v)
{
  r = v;
}

// A call in the loop writes an element of the local it is given.
int through_call()
  cppverify::post(cppverify::result == 4)
{
  int x = 4;
  int &r = x;
  int a[2];
  a[0] = 1;
  a[1] = 1;
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    set(a[i], 0);
  }
  return r;
}
// CHECK-DAG: Verified: through_call [backend=z3]

// A dynamic object the loop does not write keeps its value too.
int dynamic_kept()
  cppverify::post(cppverify::result == 6)
{
  int *p = new int(6);
  int a[2];
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    a[i] = i;
  }
  int v = *p;
  delete p;
  return v;
}
// CHECK-DAG: Verified: dynamic_kept [backend=z3]

// A store through a reference to a local writes the one cell it binds.
int reference_written()
  cppverify::post(cppverify::result == 3)
{
  int x = 0;
  int &r = x;
  int y = 3;
  int &s = y;
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    r = i;
  }
  return s;
}
// CHECK-DAG: Verified: reference_written [backend=z3]

// So does a call given that reference.
int reference_call()
  cppverify::post(cppverify::result == 3)
{
  int x = 0;
  int &r = x;
  int y = 3;
  int &s = y;
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    set(r, i);
  }
  return s;
}
// CHECK-DAG: Verified: reference_call [backend=z3]

// What the loop writes is not kept.
int overwritten()
  cppverify::post(cppverify::result == 7)
{
  int a[4];
  a[3] = 7;
  for (int i = 0; i < 4; i = i + 1)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::decreases(4 - i)
  {
    a[i] = 0;
  }
  return a[3];
}
// CHECK-DAG: error: verification failed: overwritten [{{.*}}::postcondition@

// Nor is a local written through a reference to it.
int through_reference()
  cppverify::post(cppverify::result == 5)
{
  int x = 5;
  int &r = x;
  int a[2];
  for (int i = 0; i < 2; i = i + 1)
    cppverify::invariant(0 <= i && i <= 2)
    cppverify::decreases(2 - i)
  {
    a[i] = 0;
    r = i;
  }
  return x;
}
// CHECK-DAG: error: verification failed: through_reference [{{.*}}::postcondition@
