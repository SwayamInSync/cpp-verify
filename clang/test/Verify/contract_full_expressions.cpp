// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Each clause argument, assertion, and calc term is a full-expression: the
// temporaries it creates end with it and leave nothing to the code after it.

using cppverify::seq;

cppverify::proof void length_post(seq s) cppverify::post((s + s).len() >= 0);
int after_clause = 0;
// CHECK:      VarDecl {{.*}} after_clause 'int' cinit
// CHECK-NEXT: IntegerLiteral {{.*}} 'int' 0

cppverify::proof void assertion(seq s, int n) {
  cppverify::check((s + s).len() >= 0);
  int after_check = n;
  int i = 0;
  while (i < n)
    cppverify::invariant((s + s).len() >= 0)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  cppverify::calc {
    s.push(n);
    == s + cppverify::seq_of(n);
  }
  int after_calc = n;
}
// CHECK-LABEL: FunctionDecl {{.*}} assertion
// CHECK:      ContractAssertStmt
// CHECK-NEXT: ExprWithCleanups {{.*}} 'bool'
// CHECK:      VarDecl {{.*}} after_check 'int' cinit
// CHECK-NEXT: ImplicitCastExpr
// CHECK:      WhileStmt
// CHECK:      CompoundStmt
// CHECK-NEXT: BinaryOperator {{.*}} 'int' lvalue '='
// CHECK:      ContractAssertStmt
// CHECK-NEXT: ExprWithCleanups {{.*}} 'bool'
// CHECK:      VarDecl {{.*}} after_calc 'int' cinit
// CHECK-NEXT: ImplicitCastExpr
