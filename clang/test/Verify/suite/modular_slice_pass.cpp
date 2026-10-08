// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --check-ub --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s --check-prefix=BMC

cppverify::spec bool valid(int *p, int count) { return true; }
cppverify::spec bool valid(int *p, unsigned count) { return true; }
cppverify::spec bool valid(int *p, long count) { return true; }
cppverify::spec bool valid(int *p, unsigned long count) { return true; }

int read_first(int *p, int count)
  cppverify::pre(valid(p, count) && count >= 1)
  cppverify::post(cppverify::result == p[0])
{
  return p[0];
}

int read_slice(int *p, int count, int offset, int length)
  cppverify::pre(valid(p, count) && count >= 0 && count <= 1000 && offset >= 0 &&
      offset <= count && length >= 1 && length <= count - offset)
  cppverify::post(cppverify::result == p[offset])
{
  return read_first(p + offset, length);
}

int forward_slice(int *p, int count, int first, int second)
  cppverify::pre(valid(p, count) && count >= 0 && count <= 1000 && first >= 0 &&
      first <= count && second >= 0 && second < count - first)
  cppverify::post(cppverify::result == p[first + second])
{
  return read_slice(p + first, count - first, second, 1);
}

int accept_empty_slice(int *p, int count)
  cppverify::pre(valid(p, count) && count == 0)
  cppverify::post(cppverify::result == 0)
{
  return 0;
}

int pass_one_past_empty(int *p, int count)
  cppverify::pre(valid(p, count) && count >= 0 && count <= 1000)
  cppverify::post(cppverify::result == 0)
{
  return accept_empty_slice(p + count, 0);
}

void set_first(int *p, int count, int value)
  cppverify::pre(valid(p, count) && count >= 1)
  cppverify::modifies(p[0])
  cppverify::post(p[0] == value)
{
  p[0] = value;
}

void set_slice_cell(int *p, int count, int offset, int value)
  cppverify::pre(valid(p, count) && count >= 1 && count <= 1000 && offset >= 0 &&
      offset < count)
  cppverify::modifies(p[offset])
  cppverify::post(p[offset] == value)
{
  set_first(p + offset, count - offset, value);
}

long slice_difference(int *p, int count, int left, int right)
  cppverify::pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      left >= 0 && left <= count && right >= 0 && right <= count)
  cppverify::post(cppverify::result == left - right)
{
  return (p + left) - (p + right);
}

long composed_index_difference(int *p, int count, int base, int left,
                               int right)
  cppverify::pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      base >= 0 && base <= count && left >= 0 && left <= count - base &&
      right >= 0 && right <= count - base)
  cppverify::post(cppverify::result == left - right)
{
  return (p + (base + left)) - (p + (base + right));
}

long unsigned_slice_difference(int *p, unsigned count, unsigned left,
                               unsigned right)
  cppverify::pre(valid(p, count) && p != nullptr && count <= 1000U && left <= count &&
      right <= count)
  cppverify::post(cppverify::result == static_cast<long>(left) - static_cast<long>(right))
{
  return (p + left) - (p + right);
}

long wide_unsigned_slice_difference(int *p, unsigned long count,
                                    unsigned long left, unsigned long right)
  cppverify::pre(valid(p, count) && p != nullptr && count <= 1000UL && left <= count &&
      right <= count)
  cppverify::post(cppverify::result == static_cast<long>(left) - static_cast<long>(right))
{
  return (p + left) - (p + right);
}

long wide_signed_slice_difference(int *p, long count, long left, long right)
  cppverify::pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      left >= 0 && left <= count && right >= 0 && right <= count)
  cppverify::post(cppverify::result == left - right)
{
  return (p + left) - (p + right);
}

// VERIFY-DAG: Verified: read_first
// VERIFY-DAG: Verified: read_slice
// VERIFY-DAG: Verified: forward_slice
// VERIFY-DAG: Verified: accept_empty_slice
// VERIFY-DAG: Verified: pass_one_past_empty
// VERIFY-DAG: Verified: set_first
// VERIFY-DAG: Verified: set_slice_cell
// VERIFY-DAG: Verified: slice_difference
// VERIFY-DAG: Verified: composed_index_difference
// VERIFY-DAG: Verified: unsigned_slice_difference
// VERIFY-DAG: Verified: wide_unsigned_slice_difference
// VERIFY-DAG: Verified: wide_signed_slice_difference

// BMC-DAG: Verified: read_first
// BMC-DAG: Verified: read_slice
// BMC-DAG: Verified: forward_slice
// BMC-DAG: Verified: accept_empty_slice
// BMC-DAG: Verified: pass_one_past_empty
// BMC-DAG: Verified: set_first
// BMC-DAG: Verified: set_slice_cell
// BMC-DAG: Verified: slice_difference
// BMC-DAG: Verified: composed_index_difference
// BMC-DAG: Verified: unsigned_slice_difference
// BMC-DAG: Verified: wide_unsigned_slice_difference
// BMC-DAG: Verified: wide_signed_slice_difference
