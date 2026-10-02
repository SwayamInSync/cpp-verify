// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
//
// Pointer expressions and implicit pointee-object ranges must use the same byte
// unit. For int*, q == p + 1 places q immediately after p's int object, so the
// implicit non-overlap condition is satisfiable and the false return is exposed.
spec bool valid(int *p, int n) { return true; }

bool valid_adjacent_equality(int *p, int *q)
  pre(p != nullptr && q != nullptr && q == p + 1)
  post(result)
{
  return q == p + 1;
}

bool invalid_adjacent_inequality(int *p, int *q)
  pre(p != nullptr && q != nullptr && q == p + 1)
  post(result)
{
  return q != p + 1;
}

int valid_reversed_subscript(int *p, int n, int i, int value)
  pre(valid(p, n) && 0 <= i && i < n)
  modifies(*p)
  post(result == value && p[i] == value)
{
  i[p] = value;
  return p[i];
}

bool valid_nested_offsets(int *p, int i, int j)
  pre(valid(p, 201) && 0 <= i && i <= 100 && 0 <= j && j <= 100)
  post(result)
{
  return (p + i) + j == p + (i + j);
}

bool valid_subtracted_offset(int *p, int i)
  pre(valid(p, 101) && 0 <= i && i <= 100)
  post(result)
{
  return (p + i) - i == p;
}

bool invalid_char_adjacent_inequality(char *p, char *q)
  pre(p != nullptr && q != nullptr && q == p + 1)
  post(result)
{
  return q != p + 1;
}

struct Pair {
  int first;
  int second;
};

spec bool valid(const Pair *p, int n) { return true; }

bool valid_record_stride(const Pair *p, const Pair *q)
  pre(valid(p, 2) && q == p + 1)
  post(result)
{
  return (p + 1)->second == q->second;
}

bool invalid_record_stride(const Pair *p, const Pair *q)
  pre(valid(p, 2) && q == p + 1)
  post(result)
{
  return (p + 1)->second != q->second;
}

// The element after a single object is not part of it, whatever lies there.
bool past_object_record(const Pair *p, const Pair *q)
  pre(p != nullptr && q != nullptr && q == p + 1)
  post(result)
{
  return (p + 1)->second == q->second;
}

// VERIFY-DAG: Verified: valid_adjacent_equality
// VERIFY-DAG: Verified: valid_reversed_subscript
// VERIFY-DAG: Verified: valid_nested_offsets
// VERIFY-DAG: Verified: valid_subtracted_offset
// VERIFY-DAG: Verified: valid_record_stride
// VERIFY-DAG: error: verification failed: invalid_adjacent_inequality
// VERIFY-DAG: error: verification failed: invalid_char_adjacent_inequality
// VERIFY-DAG: error: verification failed: invalid_record_stride
// VERIFY-DAG: error: verification failed: past_object_record [{{.*}}::bounds@
