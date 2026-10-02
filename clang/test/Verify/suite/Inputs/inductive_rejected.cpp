#include <cppverify.h>

spec bool negated(int n) inductive { return n == 0 || !negated(n - 1); }

spec bool compared(int n) inductive {
  return n == 0 || compared(n - 1) == false;
}

spec bool everywhere(int n) inductive {
  return n == 0 || forall(k, everywhere(k));
}

spec bool chosen(int n) inductive { return chosen(n - 1) ? n > 0 : n == 0; }

spec int counted(int n) inductive { return n; }

spec bool measured(int n) inductive decreases(n) { return n == 0; }

spec bool through(int n);
spec bool helper(int n) { return through(n - 1); }
spec bool through(int n) inductive { return n == 0 || helper(n); }

spec bool exact(int n) inductive post(result == (n == 0)) { return n == 0; }
