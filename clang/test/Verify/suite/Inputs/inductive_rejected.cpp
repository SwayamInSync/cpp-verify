#include <cppverify.h>

cppverify::spec bool negated(int n) cppverify::inductive { return n == 0 || !negated(n - 1); }

cppverify::spec bool compared(int n) cppverify::inductive {
  return n == 0 || compared(n - 1) == false;
}

cppverify::spec bool everywhere(int n) cppverify::inductive {
  return n == 0 || cppverify::forall(k, everywhere(k));
}

cppverify::spec bool chosen(int n) cppverify::inductive { return chosen(n - 1) ? n > 0 : n == 0; }

cppverify::spec int counted(int n) cppverify::inductive { return n; }

cppverify::spec bool measured(int n) cppverify::inductive cppverify::decreases(n) { return n == 0; }

cppverify::spec bool through(int n);
cppverify::spec bool helper(int n) { return through(n - 1); }
cppverify::spec bool through(int n) cppverify::inductive { return n == 0 || helper(n); }

cppverify::spec bool exact(int n) cppverify::inductive cppverify::post(cppverify::result == (n == 0)) { return n == 0; }
