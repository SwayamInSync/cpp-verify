// RUN: rm -rf %t && mkdir -p %t
// RUN: cp %s %t/input.h
// RUN: %cpp-verify %t/input.h -- 2>&1 | FileCheck %s --check-prefix=HEADER --implicit-check-not=error:
// RUN: cp %s %t/input.c
// RUN: not %cpp-verify %t/input.c -- 2>&1 | FileCheck %s --check-prefix=C --implicit-check-not=Verified
// RUN: not %cpp-verify %s -- -fbogus-flag 2>&1 | FileCheck %s --check-prefix=FLAG --implicit-check-not=Verified
//
// A header given as input is C++, and an error in a command line stops its
// file, as it stops clang.

inline int twice_small(int x)
  cppverify::pre(x >= 0 && x < 100)
  cppverify::post(cppverify::result == 2 * x)
{
  return 2 * x;
}

// HEADER: Verified: twice_small [backend=z3]
// C: error: invalid argument '-std=c++17' not allowed with 'C'
// FLAG: error: unknown argument: '-fbogus-flag'
