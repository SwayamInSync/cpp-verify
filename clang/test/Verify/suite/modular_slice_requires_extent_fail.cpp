// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=NO-EXTENT

spec bool valid(int *p, int count) { return true; }

int read_one(int *p, int count)
  pre(valid(p, count) && count >= 1)
  post(result == p[0])
{
  return p[0];
}

int read_subslice(int *p, int count, int offset)
  pre(valid(p, count) && count >= 1 && count <= 1000 && offset >= 0 &&
      offset < count)
  post(result == p[offset])
{
  return read_one(p + offset, count - offset);
}

long subtract_positions(int *p, int count, int left, int right)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      left >= 0 && left <= count && right >= 0 && right <= count)
  post(result == left - right)
{
  return (p + left) - (p + right);
}

// NO-EXTENT-DAG: error: verification failed: read_subslice
// NO-EXTENT-DAG: error: verification failed: subtract_positions
