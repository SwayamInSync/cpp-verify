// RUN: c-index-test -test-load-source all %s -std=c++17 -fverify-contracts -fno-verify -isystem %resource_dir | FileCheck %s
//
// libclang exposes each contract construct as an unexposed expression or
// statement, with its operands as children.

cppverify::spec int down(int x) cppverify::decreases(x) { return x <= 0 ? 0 : down(x - 1); }

int f(int n)
  cppverify::pre(cppverify::forall(k, 0, n, k >= 0))
  cppverify::post(cppverify::result >= cppverify::old(n))
{
  cppverify::ghost { int g = cppverify::choose(j, 0, 2, j == 1); }
  cppverify::check(cppverify::exists(k, 0, 1, k == 0));
  cppverify::hide(down);
  cppverify::reveal(down);
  cppverify::reveal_with_fuel(down, 2);
  return n;
}

// CHECK: cppverify-cursors.cpp:9:18: UnexposedExpr= Extent=[9:18 - 9:52]
// CHECK: cppverify-cursors.cpp:9:45: BinaryOperator=>= Extent=[9:45 - 9:51]
// CHECK: cppverify-cursors.cpp:10:19: UnexposedExpr= Extent=[10:19 - 10:36]
// CHECK: cppverify-cursors.cpp:10:40: UnexposedExpr= Extent=[10:40 - 10:57]
// CHECK: cppverify-cursors.cpp:10:55: DeclRefExpr=n:8:11 Extent=[10:55 - 10:56]
// CHECK: cppverify-cursors.cpp:12:3: UnexposedStmt= Extent=[12:3 - 12:67]
// CHECK: cppverify-cursors.cpp:12:30: UnexposedExpr= Extent=[12:30 - 12:64]
// CHECK: cppverify-cursors.cpp:12:57: BinaryOperator=== Extent=[12:57 - 12:63]
// CHECK: cppverify-cursors.cpp:13:3: UnexposedStmt= Extent=[13:3 - 13:55]
// CHECK: cppverify-cursors.cpp:13:20: UnexposedExpr= Extent=[13:20 - 13:54]
// CHECK: cppverify-cursors.cpp:13:47: BinaryOperator=== Extent=[13:47 - 13:53]
// CHECK: cppverify-cursors.cpp:14:3: UnexposedStmt= Extent=[14:3 - 14:24]
// CHECK: cppverify-cursors.cpp:14:19: DeclRefExpr=down:6:21 Extent=[14:19 - 14:23]
// CHECK: cppverify-cursors.cpp:15:3: UnexposedStmt= Extent=[15:3 - 15:26]
// CHECK: cppverify-cursors.cpp:15:21: DeclRefExpr=down:6:21 Extent=[15:21 - 15:25]
// CHECK: cppverify-cursors.cpp:16:3: UnexposedStmt= Extent=[16:3 - 16:39]
// CHECK: cppverify-cursors.cpp:16:31: DeclRefExpr=down:6:21 Extent=[16:31 - 16:35]
// CHECK: cppverify-cursors.cpp:16:37: IntegerLiteral= Extent=[16:37 - 16:38]

int g(const int (&a)[2]) {
  int s = 0;
  for (int v : a)
    cppverify::invariant(s >= 0)
    s = v;
  return s;
}

// The clauses of a range-based for loop are children of the loop.
// CHECK: cppverify-cursors.cpp:[[@LINE-7]]:3: CXXForRangeStmt= Extent=[[[@LINE-7]]:3 - [[@LINE-5]]:10]
// CHECK: cppverify-cursors.cpp:[[@LINE-7]]:26: BinaryOperator=>= Extent=[[[@LINE-7]]:26 - [[@LINE-7]]:32]
