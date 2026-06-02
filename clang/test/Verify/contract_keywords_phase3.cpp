// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s

// CHECK: FunctionDecl {{.*}} with_modifies 'void (int *, int *)'
// CHECK: modifies
void with_modifies(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(true)
{
}

// CHECK: aliases
void with_aliases(int *dst, int *src)
  aliases(dst, src)
  pre(true)
  post(true)
{
}

spec int div_spec(int a, int b)
  recommends(b != 0)
{
  return a / b;
}

// CHECK: RevealWithFuelStmt
void use_reveal() {
  ghost { reveal_with_fuel(div_spec, 2); }
}