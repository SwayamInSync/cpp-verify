// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --check-ub --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s --check-prefix=BMC

cppverify::spec bool valid(int *pointer, int count) { return true; }

struct PointerBox {
  int tag;
  int *pointer;
};

int preserve_incoming_slice(int *pointer)
  cppverify::pre(valid(pointer, 2) && pointer[1] == 3)
  cppverify::post(cppverify::result == 3)
{
  {
    int local[1] = {7};
    local[0] = 8;
  }
  return pointer[1];
}

[[cppverify::trusted]] int *external_pointer()
  cppverify::post(cppverify::result != nullptr);

int *unevaluated_factory(int value)
  cppverify::post(cppverify::result != nullptr)
  cppverify::post(*cppverify::result == value)
{
  int *owner = new int(value);
  return owner;
}

int *forward_external_pointer()
  cppverify::post(cppverify::result != nullptr)
{
  return external_pointer();
}

int *forward_external_pointer_again()
  cppverify::post(cppverify::result != nullptr)
{
  return forward_external_pointer();
}

int *forward_external_pointer_with_unevaluated_new()
  cppverify::post(cppverify::result != nullptr)
{
  int ignored = sizeof(new int);
  return external_pointer();
}

int consume_unevaluated_new_wrapper()
  cppverify::post(true)
{
  int *pointer = forward_external_pointer_with_unevaluated_new();
  return *pointer;
}

int *ignore_unevaluated_factory_assignment()
  cppverify::post(cppverify::result != nullptr)
{
  int *pointer = external_pointer();
  unsigned long ignored = sizeof(pointer = unevaluated_factory(1));
  return pointer;
}

int consume_unevaluated_factory_assignment()
  cppverify::post(true)
{
  int *pointer = ignore_unevaluated_factory_assignment();
  return *pointer;
}

int *ignore_unevaluated_factory_type()
  cppverify::post(cppverify::result != nullptr)
{
  int *pointer = external_pointer();
  decltype((pointer = unevaluated_factory(1), 0)) ignored = 0;
  return pointer;
}

int consume_unevaluated_factory_type()
  cppverify::post(true)
{
  int *pointer = ignore_unevaluated_factory_type();
  return *pointer;
}

int *null_pointer_wrapper()
  cppverify::post(cppverify::result == nullptr)
{
  return nullptr;
}

bool consume_null_pointer_wrapper()
  cppverify::post(cppverify::result)
{
  int *pointer = null_pointer_wrapper();
  return pointer == nullptr;
}

int delete_null_pointer_wrapper()
  cppverify::post(true)
{
  int *pointer = null_pointer_wrapper();
  delete pointer;
  return 0;
}

int preserve_prior_call_result()
  cppverify::post(true)
{
  int *pointer = external_pointer();
  {
    int local[1] = {7};
    local[0] = 8;
  }
  return *pointer;
}

int preserve_stored_abstract_pointer(int *pointer)
  cppverify::pre(pointer != nullptr && *pointer == 5)
  cppverify::post(cppverify::result == 5)
{
  PointerBox box{0, pointer};
  int &promote = box.tag;
  promote = 1;
  pointer = nullptr;
  {
    int local[1] = {7};
    local[0] = 8;
  }
  return *box.pointer;
}

int skipped_parameter_conditional(int *pointer, int index, bool take)
  cppverify::pre(valid(pointer, 1) && index == 1 && !take)
  cppverify::post(cppverify::result == 0)
{
  return take ? pointer[index] : 0;
}

bool skipped_parameter_and(int *pointer, int index, bool take)
  cppverify::pre(valid(pointer, 1) && index == 1 && !take)
  cppverify::post(!cppverify::result)
{
  return take && pointer[index] > 0;
}

bool skipped_parameter_or(int *pointer, int index, bool take)
  cppverify::pre(valid(pointer, 1) && index == 1 && take)
  cppverify::post(cppverify::result)
{
  return take || pointer[index] > 0;
}

int skipped_local_conditional(bool take, int divisor)
  cppverify::pre(!take && divisor == 0)
  cppverify::post(cppverify::result == 0)
{
  int values[1] = {7};
  return take ? values[1 / divisor] : 0;
}

// VERIFY-DAG: Verified: preserve_incoming_slice
// VERIFY-DAG: Verified: unevaluated_factory
// VERIFY-DAG: Verified: forward_external_pointer
// VERIFY-DAG: Verified: forward_external_pointer_again
// VERIFY-DAG: Verified: forward_external_pointer_with_unevaluated_new
// VERIFY-DAG: Verified: consume_unevaluated_new_wrapper
// VERIFY-DAG: Verified: ignore_unevaluated_factory_assignment
// VERIFY-DAG: Verified: consume_unevaluated_factory_assignment
// VERIFY-DAG: Verified: ignore_unevaluated_factory_type
// VERIFY-DAG: Verified: consume_unevaluated_factory_type
// VERIFY-DAG: Verified: null_pointer_wrapper
// VERIFY-DAG: Verified: consume_null_pointer_wrapper
// VERIFY-DAG: Verified: delete_null_pointer_wrapper
// VERIFY-DAG: Verified: preserve_prior_call_result
// VERIFY-DAG: Verified: preserve_stored_abstract_pointer
// VERIFY-DAG: Verified: skipped_parameter_conditional
// VERIFY-DAG: Verified: skipped_parameter_and
// VERIFY-DAG: Verified: skipped_parameter_or
// VERIFY-DAG: Verified: skipped_local_conditional

// BMC-DAG: Verified: preserve_incoming_slice
// BMC-DAG: Verified: unevaluated_factory
// BMC-DAG: Verified: forward_external_pointer
// BMC-DAG: Verified: forward_external_pointer_again
// BMC-DAG: Verified: forward_external_pointer_with_unevaluated_new
// BMC-DAG: Verified: consume_unevaluated_new_wrapper
// BMC-DAG: Verified: ignore_unevaluated_factory_assignment
// BMC-DAG: Verified: consume_unevaluated_factory_assignment
// BMC-DAG: Verified: ignore_unevaluated_factory_type
// BMC-DAG: Verified: consume_unevaluated_factory_type
// BMC-DAG: Verified: null_pointer_wrapper
// BMC-DAG: Verified: consume_null_pointer_wrapper
// BMC-DAG: Verified: delete_null_pointer_wrapper
// BMC-DAG: Verified: preserve_prior_call_result
// BMC-DAG: Verified: preserve_stored_abstract_pointer
// BMC-DAG: Verified: skipped_parameter_conditional
// BMC-DAG: Verified: skipped_parameter_and
// BMC-DAG: Verified: skipped_parameter_or
// BMC-DAG: Verified: skipped_local_conditional
