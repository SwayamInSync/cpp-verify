// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

long offset_beyond_complete_object(int *pointer)
  pre(pointer != nullptr)
  post(true)
{
  return (pointer + 2) - pointer;
}

long negative_offset_without_extent(int *pointer)
  pre(pointer != nullptr)
  post(true)
{
  return (pointer - 1) - pointer;
}

spec long spec_pointer_difference(int *pointer) {
  return pointer - pointer;
}

constexpr long constexpr_pointer_difference(int *pointer) {
  return (pointer + 1) - pointer;
}

// VERIFY-DAG: error: offset_beyond_complete_object: pointer difference operands must be direct pointers or +0/+1 positions within one complete object
// VERIFY-DAG: error: negative_offset_without_extent: pointer difference operands must be direct pointers or +0/+1 positions within one complete object
// VERIFY-DAG: error: spec_pointer_difference: pointer difference in spec or lifted constexpr functions is unsupported
// VERIFY-DAG: error: constexpr_pointer_difference: pointer difference in spec or lifted constexpr functions is unsupported
