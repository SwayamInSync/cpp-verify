// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int *escape_pointer()
  post(true)
{
  int *p = new int(1);
  return p;
}

int copy_pointer()
  post(result == 1)
{
  int *p = new int(1);
  int *q = p;
  return *q;
}

int pointer_arithmetic()
  post(result == 1)
{
  int *p = new int(1);
  return *(p + 0);
}

int pointer_parameter(int *external)
  post(result == 1)
{
  int *p = new int(1);
  delete p;
  return 1;
}

int array_allocation()
  post(result == 1)
{
  int *p = new int[2]{1, 2};
  delete[] p;
  return 1;
}

int allocation_in_loop()
  post(result == 0)
{
  for (int i = 0; i < 1; ++i) {
    int *p = new int(i);
    delete p;
  }
  return 0;
}

int void_pointer_target()
  post(result == 0)
{
  void *p = new int(1);
  delete p;
  return 0;
}

int subscript_store()
  post(result == 1)
{
  int *p = new int;
  p[0] = 1;
  int observed = *p;
  delete p;
  return observed;
}

int offset_store()
  post(result == 1)
{
  int *p = new int;
  *(p + 0) = 1;
  int observed = *p;
  delete p;
  return observed;
}

spec bool dynamic_nonnull(int *p)
{
  return p != nullptr;
}

int spec_call_boundary()
  post(result == 1)
{
  int *p = new int(1);
  bool nonnull = dynamic_nonnull(p);
  delete p;
  return nonnull;
}

// VERIFY-DAG: error: escape_pointer: dynamic-storage pointers cannot escape through a return
// VERIFY-DAG: error: copy_pointer: copying a dynamic-storage pointer is unsupported
// VERIFY-DAG: error: pointer_arithmetic: dynamic-storage dereference requires its direct allocation pointer
// VERIFY-DAG: error: pointer_parameter: dynamic allocation in functions with pointer parameters is not yet supported
// VERIFY-DAG: error: array_allocation: unsupported C++ type in verification: int[2]
// VERIFY-DAG: error: allocation_in_loop: dynamic allocation inside loops is unsupported
// VERIFY-DAG: error: allocation_in_loop: dynamic deallocation inside loops is unsupported
// VERIFY-DAG: error: void_pointer_target: new result must directly initialize a matching typed pointer
// VERIFY-DAG: error: subscript_store: subscripting dynamic-storage pointers is unsupported
// VERIFY-DAG: error: offset_store: dynamic-storage dereference requires its direct allocation pointer
// VERIFY-DAG: error: spec_call_boundary: dynamic-storage pointers cannot cross a function-call boundary
