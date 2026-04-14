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
  pre(x)
  post(result >= 0)
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
  pre(x > 0)
  post(result)
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
  pre(x < 100)
  post(result >= 0)
{
  return x;
}

// ---------------------------------------------------------------------------
// 4. Mixed signed/unsigned in contract
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} mixed_sign 'int (int, unsigned int)'
// CHECK: pre: BinaryOperator {{.*}} 'bool'
int mixed_sign(int a, unsigned int b)
  pre(a >= 0)
  post(result >= 0)
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
  post(result == (x > 0))
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
  pre(x > 0)
{
  ghost {
    contract_assert(x);
  }
  return x;
}

// ---------------------------------------------------------------------------
// 7. Loop invariant with integer (auto bool conversion)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} inv_int 'int (int)'
// CHECK: invariant: ImplicitCastExpr {{.*}} 'bool' <IntegralToBoolean>
int inv_int(int n)
  pre(n > 0)
{
  int i = 1;
  while (i < n)
    invariant(i)
    decreases(n - i)
  {
    i++;
  }
  return i;
}
