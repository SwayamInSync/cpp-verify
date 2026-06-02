// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-obj -o %t.o %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-obj -o %t2.o %s

int id(int x)
  pre(true)
  post(result == x)
{
  return x;
}