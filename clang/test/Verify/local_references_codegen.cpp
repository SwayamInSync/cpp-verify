// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-obj -o %t.o %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-obj -o %t2.o %s

void set_value(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int local_reference_codegen(int value)
  post(result == value)
{
  int local = 0;
  int &alias = local;
  set_value(alias, value);
  return local;
}
