// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s

// Binding a reference or passing a pointer reads nothing ([dcl.init.ref],
// [conv.lval]); only reading an indeterminate value is undefined
// ([basic.indet]). A local's initialization is checked where it is read.
// A function is still verified as reading its pointer and reference
// parameters' storage, and its callers its pointer result's, as initialized,
// so a call or return that cannot show it is unsupported, not a failure.

void init_ref(int &r)
  cppverify::modifies(r)
  cppverify::post(r == 0)
{
  r = 0;
}
// CHECK: Verified: init_ref

void init_ptr(int *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == 0)
{
  *p = 0;
}
// CHECK: Verified: init_ptr

int read_ref(const int &r)
  cppverify::post(cppverify::result == r)
{
  return r;
}
// CHECK: Verified: read_ref

int scalar_out()
  cppverify::post(cppverify::result == 0)
{
  int a;
  init_ref(a);
  return a;
}
// CHECK: Unresolved: scalar_out {{.*}}[reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, since the callee is verified as reading initialized storage)

int array_out()
  cppverify::post(cppverify::result == 0)
{
  int a[2];
  init_ref(a[0]);
  return a[0];
}
// CHECK: Unresolved: array_out {{.*}}[reason=construct.unsupported]

int heap_out()
  cppverify::post(cppverify::result == 0)
{
  int *p = new int;
  init_ptr(p);
  int v = *p;
  delete p;
  return v;
}
// CHECK: Unresolved: heap_out {{.*}}[reason=construct.unsupported]

int initialized_argument()
  cppverify::post(cppverify::result == 0)
{
  int a = 7;
  init_ref(a);
  return a;
}
// CHECK: Verified: initialized_argument

int written_through_local_reference()
  cppverify::post(cppverify::result == 3)
{
  int a;
  int &r = a;
  r = 3;
  return a;
}
// CHECK: Verified: written_through_local_reference

int read_before_written()
  cppverify::post(cppverify::result == 3)
{
  int a;
  int &r = a;
  int v = r;
  return v;
}
// CHECK: error: verification failed: read_before_written {{.*}}initialization@[[@LINE-3]]:3

int *fresh()
  cppverify::post(cppverify::result != nullptr)
{
  int *p = new int;
  return p;
}
// CHECK: Unresolved: fresh {{.*}}[reason=construct.unsupported] (the verifier cannot model a construct here: returning a pointer to storage that is not initialized, since callers read a returned pointer's storage as initialized)

// The callee reads the indeterminate value, which is undefined, but its
// verification cannot say that it reads before it writes: unsupported too.
int reads_uninitialized()
  cppverify::post(cppverify::result == 0)
{
  int a;
  return read_ref(a);
}
// CHECK: Unresolved: reads_uninitialized {{.*}}[reason=construct.unsupported]
