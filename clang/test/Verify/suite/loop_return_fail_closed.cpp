// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s

// Supported loop exits are tested in loop_exits.cpp, and a switch's in
// switch_statements.cpp.

int reject_ghost_switch_break(int x)
  cppverify::post(cppverify::result == x)
{
  switch (x) {
  case 0:
    cppverify::ghost {
      break;
    }
  }
  return x;
}

int reject_ghost_break(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    cppverify::ghost {
      if (i == 0)
        break;
    }
    i = i + 1;
  }
  return i;
}

// CHECK-DAG: error: reject_ghost_switch_break: ghost code cannot leave an executable switch
// CHECK-DAG: error: reject_ghost_break: ghost code cannot leave an executable loop
