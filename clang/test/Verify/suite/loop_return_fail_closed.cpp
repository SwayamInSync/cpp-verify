// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

// Supported loop exits are tested in loop_exits.cpp.

int reject_do_break(bool stop)
  cppverify::post(cppverify::result == 0)
{
  do {
    if (stop)
      break;
  } while (false)
    cppverify::invariant(true);
  return 0;
}

int reject_do_continue(bool stop)
  cppverify::post(cppverify::result == 0)
{
  do {
    if (stop)
      continue;
  } while (false)
    cppverify::invariant(true);
  return 0;
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

// CHECK-DAG: error: reject_do_break: break and continue in do loops are unsupported
// CHECK-DAG: error: reject_do_continue: break and continue in do loops are unsupported
// CHECK-DAG: error: reject_ghost_break: ghost code cannot leave an executable loop
