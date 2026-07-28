// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --check-ub --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC

spec bool valid(int *p, int count) { return true; }
spec bool valid(int *p, unsigned long count) { return true; }

int read_first(int *p, int count)
  pre(valid(p, count) && count >= 1)
  post(result == p[0])
{
  return p[0];
}

long consume_difference(long value)
  pre(true)
  post(result == value)
{
  return value;
}

int read_complete_object(int *p)
  pre(p != nullptr)
  post(result == *p)
{
  return *p;
}

long unsafe_difference_precondition(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      (p + (count + 1)) - p == count + 1)
  post(true)
{
  return 0;
}

void overwrite_region(int *p, int count)
  pre(valid(p, count) && count >= 1)
  modifies(*p)
{
  p[0] = 1;
}

int insufficient_slice(int *p, int count, int offset, int length)
  pre(valid(p, count) && count >= 0 && offset >= 0 && offset <= count &&
      length >= 1)
  post(true)
{
  return read_first(p + offset, length);
}

int one_past_nonempty_slice(int *p, int count)
  pre(valid(p, count) && count >= 0 && count <= 1000)
  post(true)
{
  return read_first(p + count, 1);
}

int missing_caller_extent(int *p)
  pre(p != nullptr)
  post(true)
{
  return read_first(p, 1);
}

long out_of_bounds_difference(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000)
  post(true)
{
  return (p + (count + 1)) - p;
}

long negative_position_difference(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 1 && count <= 1000)
  post(true)
{
  return (p - 1) - p;
}

long unrepresentable_pointer_difference(int *p, unsigned long count)
  pre(valid(p, count) && p != nullptr && count == 9223372036854775808UL)
  post(true)
{
  return (p + count) - p;
}

long cross_origin_difference(int *left, int left_count, int *right,
                             int right_count)
  pre(valid(left, left_count) && valid(right, right_count) &&
      left_count >= 1 && right_count >= 1 && left != nullptr &&
      right != nullptr)
  post(true)
{
  return (left + 1) - right;
}

long wrong_slice_difference(int *p, int count, int left, int right)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      left >= 0 && left <= count && right >= 0 && right <= count)
  post(result == right - left)
{
  return (p + left) - (p + right);
}

long unsafe_difference_argument(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000)
  post(true)
{
  return consume_difference((p + (count + 1)) - p);
}

long unsafe_difference_postcondition(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000)
  post((p + (count + 1)) - p == count + 1)
{
  return 0;
}

int missing_extent_pointer_forward(int *p)
  pre(p != nullptr && p + 2 != nullptr)
  post(true)
{
  return read_complete_object(p + 2);
}

long call_unsafe_difference_precondition(int *p, int count)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000)
  post(true)
{
  return unsafe_difference_precondition(p, count);
}

void unbounded_slice_write(int *p, int count, int offset)
  pre(valid(p, count) && count >= 1 && offset >= 0 && offset < count)
  modifies(*p)
{
  overwrite_region(p + offset, count - offset);
}

// VERIFY-DAG: error: verification failed: insufficient_slice
// VERIFY-DAG: error: verification failed: one_past_nonempty_slice
// VERIFY-DAG: error: verification failed: missing_caller_extent
// VERIFY-DAG: error: verification failed: out_of_bounds_difference
// VERIFY-DAG: error: verification failed: negative_position_difference
// VERIFY-DAG: error: verification failed: unrepresentable_pointer_difference
// VERIFY-DAG: error: verification failed: cross_origin_difference
// VERIFY-DAG: error: verification failed: wrong_slice_difference
// VERIFY-DAG: error: verification failed: unsafe_difference_argument
// VERIFY-DAG: error: verification failed: unsafe_difference_postcondition
// VERIFY-DAG: error: verification failed: missing_extent_pointer_forward
// VERIFY-DAG: error: verification failed: call_unsafe_difference_precondition
// VERIFY-DAG: error: verification failed: unbounded_slice_write

// BMC-DAG: error: verification failed: insufficient_slice
// BMC-DAG: error: verification failed: one_past_nonempty_slice
// BMC-DAG: error: verification failed: missing_caller_extent
// BMC-DAG: error: verification failed: out_of_bounds_difference
// BMC-DAG: error: verification failed: negative_position_difference
// BMC-DAG: error: verification failed: unrepresentable_pointer_difference
// BMC-DAG: error: verification failed: cross_origin_difference
// BMC-DAG: error: verification failed: wrong_slice_difference
// BMC-DAG: error: verification failed: unsafe_difference_argument
// BMC-DAG: error: verification failed: unsafe_difference_postcondition
// BMC-DAG: error: verification failed: missing_extent_pointer_forward
// BMC-DAG: error: verification failed: call_unsafe_difference_precondition
// BMC-DAG: error: verification failed: unbounded_slice_write
