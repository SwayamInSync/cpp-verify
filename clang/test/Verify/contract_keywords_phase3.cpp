// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s

// CHECK: FunctionDecl {{.*}} with_modifies 'void (int *, int *)'
// CHECK: modifies
void with_modifies(int *a, int *b)
  cppverify::pre(a != nullptr && b != nullptr)
  cppverify::modifies(*a, *b)
  cppverify::post(true)
{
}

// CHECK: aliases
void with_aliases(int *dst, int *src)
  cppverify::aliases(dst, src)
  cppverify::pre(true)
  cppverify::post(true)
{
}

cppverify::spec int div_spec(int a, int b)
  cppverify::recommends(b != 0)
{
  return a / b;
}

// CHECK: RevealWithFuelStmt
void use_reveal() {
  cppverify::ghost { cppverify::reveal_with_fuel(div_spec, 2); }
}