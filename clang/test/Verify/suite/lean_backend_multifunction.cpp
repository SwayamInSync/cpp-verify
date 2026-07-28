// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s > %t.out 2>&1
// RUN: FileCheck %s < %t.out
// RUN: grep '^abbrev CppHeap ' %t.lean | count 1
// RUN: grep -E '^theorem cppverify_overloaded_fn_[0-9a-f]+_correct' %t.lean | sort -u | count 2
// RUN: not grep -q '^Verified:' %t.out

int overloaded(int x)
  post(result == x)
{
  return x;
}

long overloaded(long x)
  post(result == x)
{
  return x;
}

// CHECK-COUNT-2: Exported: lean obligation: overloaded
