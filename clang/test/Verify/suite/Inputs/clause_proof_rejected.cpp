#include <cppverify.h>

int exec_fn(int x) cppverify::post(cppverify::result == x) by { cppverify::check(true); } { return x; }

cppverify::spec int when_block(int n) cppverify::when(n > 0) by { cppverify::check(true); } {
  return n;
}

cppverify::spec int declared(int n) cppverify::post(cppverify::result >= 0) by { cppverify::check(true); };
