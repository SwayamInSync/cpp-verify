// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

int negative_result()
  post(result == 0)
{
  return -1;
}

unsigned maximum_result()
  post(result == 0)
{
  return static_cast<unsigned>(-1);
}

// CHECK: error: verification failed: negative_result
// CHECK-SAME: result [ssa=__result_1] [type=i32] = -1
// CHECK: error: verification failed: maximum_result
// CHECK-SAME: result [ssa=__result_1] [type=u32] = 4294967295
