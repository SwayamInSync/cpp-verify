// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
//
// Test implicit type conversions in contract expressions.
// Int to bool conversion, unsigned comparisons, etc.

// ---------------------------------------------------------------------------
// 1. Integer pre condition (implicitly converted to bool)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} int_to_bool 'int (int)'
// CHECK: pre: ImplicitCastExpr {{.*}} 'bool' <IntegralToBoolean>
int int_to_bool(int x)
  cppverify::pre(x)
  cppverify::post(cppverify::result >= 0)
{
  return x > 0 ? x : -x;
}

// ---------------------------------------------------------------------------
// 2. Integer postcondition (result implicitly converted to bool)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} result_to_bool 'int (int)'
// CHECK: post: ImplicitCastExpr {{.*}} 'bool' <IntegralToBoolean>
// CHECK:   ResultExpr {{.*}} 'int'
int result_to_bool(int x)
  cppverify::pre(x > 0)
  cppverify::post(cppverify::result)
{
  return x;
}

// ---------------------------------------------------------------------------
// 3. Unsigned integer contracts
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} unsigned_contracts 'unsigned int (unsigned int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool' '<'
// CHECK: post: BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ResultExpr {{.*}} 'unsigned int'
unsigned int unsigned_contracts(unsigned int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 4. Mixed signed/unsigned in contract
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} mixed_sign 'int (int, unsigned int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool'
int mixed_sign(int a, unsigned int b)
  cppverify::pre(a >= 0)
  cppverify::post(cppverify::result >= 0)
{
  return a + b;
}

// ---------------------------------------------------------------------------
// 5. Bool return type — result is bool
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} bool_result 'bool (int)'
// CHECK: post: BinaryOperator {{.*}} 'bool' '=='
// CHECK:   ResultExpr {{.*}} 'bool'
bool bool_result(int x)
  cppverify::post(cppverify::result == (x > 0))
{
  return x > 0;
}

// ---------------------------------------------------------------------------
// 6. contract_assert with integer (auto bool conversion)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} assert_int 'int (int)'
// CHECK: ContractAssertStmt
// CHECK:   ImplicitCastExpr {{.*}} 'bool' <IntegralToBoolean>
int assert_int(int x)
  cppverify::pre(x > 0)
{
  cppverify::ghost {
    cppverify::check(x);
  }
  return x;
}

// ---------------------------------------------------------------------------
// 7. Loop invariant with integer (auto bool conversion)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} inv_int 'int (int)'
// CHECK: invariant: ImplicitCastExpr {{.*}} 'bool' <IntegralToBoolean>
int inv_int(int n)
  cppverify::pre(n > 0)
{
  int i = 1;
  while (i < n)
    cppverify::invariant(i)
    cppverify::decreases(n - i)
  {
    i++;
  }
  return i;
}
