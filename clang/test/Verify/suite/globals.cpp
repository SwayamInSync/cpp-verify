// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify %S/Inputs/globals_spec.cpp 2>&1 | FileCheck %s --check-prefix=SPEC
//
// A const integral global with a constant initializer is its value. A mutable
// scalar global is a memory cell of its own: functions read it, write it only
// within their modifies clause, and calls frame it exactly.

const int LIMIT = 10;
constexpr unsigned MASK = 0xff;
int counter = 0;
long total;

int clamp(int x)
  post(result <= LIMIT)
{
  return x > LIMIT ? LIMIT : x;
}
// CHECK-DAG: Verified: clamp

unsigned low_byte(unsigned x)
  post(result <= MASK)
{
  return x & MASK;
}
// CHECK-DAG: Verified: low_byte

void bump()
  pre(counter < 1000)
  modifies(counter)
  post(counter == old(counter) + 1)
{
  counter = counter + 1;
}
// CHECK-DAG: Verified: bump

void bump_unframed()
  pre(counter < 1000)
{
  counter = counter + 1;
}
// CHECK-DAG: error: verification failed: bump_unframed [{{.*}}::frame@

int twice()
  pre(counter < 100)
  modifies(counter)
  post(counter == old(counter) + 2)
{
  bump();
  bump();
  return counter;
}
// CHECK-DAG: Verified: twice

void keeps_others(int *p)
  pre(p != nullptr && counter < 1000)
  modifies(counter)
  post(total == old(total) && *p == old(*p))
{
  bump();
}
// CHECK-DAG: Verified: keeps_others

void frames_wrong(int *p)
  pre(p != nullptr && counter < 1000)
  modifies(*p)
{
  bump();
}
// CHECK-DAG: error: verification failed: frames_wrong [{{.*}}::frame@

void forgets_old()
  pre(counter < 1000)
  modifies(counter)
  post(counter == old(counter))
{
  bump();
}
// CHECK-DAG: error: verification failed: forgets_old [{{.*}}::postcondition@

// SPEC: error: reads_counter: a spec function cannot read the mutable global counter; pass its value as a parameter
