// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// A reads range is a pointer and an element count fixed by the arguments: a
// range that moved with the heap could not frame it.

spec int depends_on_heap(const int *p)
  reads(p, p[0])
{
  return p[0];
}
// CHECK-DAG: error: depends_on_heap: a reads range cannot depend on the heap

spec int boolean_count(const int *p)
  reads(p, true)
{
  return p[0];
}
// CHECK-DAG: error: boolean_count: reads takes a pointer and an integer count, and only on a spec function

int executable(const int *p)
  reads(p, 1)
{
  return p[0];
}
// CHECK-DAG: error: executable: reads takes a pointer and an integer count, and only on a spec function
