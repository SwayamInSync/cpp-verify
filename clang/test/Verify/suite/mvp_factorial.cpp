// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %clang -std=c++17 -fverify-contracts -DCPPVERIFY_POSITIVE_ONLY \
// RUN:   -c %s -o %t.o
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int math_factorial(int n)
  cppverify::decreases(n)
{
  if (n <= 1)
    return 1;
  return n * math_factorial(n - 1);
}

constexpr bool machine_factorial_value(int n, int value) {
  return (n == 0 && value == 1) ||
         (n == 1 && value == 1) ||
         (n == 2 && value == 2) ||
         (n == 3 && value == 6) ||
         (n == 4 && value == 24) ||
         (n == 5 && value == 120) ||
         (n == 6 && value == 720) ||
         (n == 7 && value == 5040) ||
         (n == 8 && value == 40320) ||
         (n == 9 && value == 362880) ||
         (n == 10 && value == 3628800) ||
         (n == 11 && value == 39916800) ||
         (n == 12 && value == 479001600);
}

cppverify::proof void lemma_factorial_constants()
  cppverify::post(math_factorial(0) == 1)
  cppverify::post(math_factorial(1) == 1)
  cppverify::post(math_factorial(2) == 2)
  cppverify::post(math_factorial(3) == 6)
  cppverify::post(math_factorial(4) == 24)
  cppverify::post(math_factorial(5) == 120)
  cppverify::post(math_factorial(6) == 720)
  cppverify::post(math_factorial(7) == 5040)
  cppverify::post(math_factorial(8) == 40320)
  cppverify::post(math_factorial(9) == 362880)
  cppverify::post(math_factorial(10) == 3628800)
  cppverify::post(math_factorial(11) == 39916800)
  cppverify::post(math_factorial(12) == 479001600)
{
  cppverify::reveal_with_fuel(math_factorial, 12);
}

int recursive_factorial(int n)
  cppverify::pre(n >= 0 && n <= 12)
  cppverify::post(machine_factorial_value(n, cppverify::result))
  cppverify::post(cppverify::result == math_factorial(n))
  cppverify::decreases(n)
{
  cppverify::ghost {
    cppverify::hide(math_factorial);
  }
  int answer = 1;
  if (n > 1) {
    int previous = recursive_factorial(n - 1);
    answer = n * previous;
  }
  cppverify::ghost {
    lemma_factorial_constants();
  }
  return answer;
}

int iterative_factorial(int n)
  cppverify::pre(n >= 0 && n <= 12)
  cppverify::post(machine_factorial_value(n, cppverify::result))
  cppverify::post(cppverify::result == math_factorial(n))
{
  cppverify::ghost {
    cppverify::hide(math_factorial);
  }
  int accumulator = 1;
  int i = 1;
  while (i <= n)
    cppverify::invariant(i >= 1 && i <= n + 1)
    cppverify::invariant(machine_factorial_value(i - 1, accumulator))
    cppverify::decreases(n - i + 1)
  {
    accumulator = accumulator * i;
    i = i + 1;
  }
  cppverify::ghost {
    lemma_factorial_constants();
  }
  return accumulator;
}

int factorial_twelve()
  cppverify::post(cppverify::result == 479001600)
{
  return recursive_factorial(12);
}

void write_factorial(int n, int *out, int *preserved)
  cppverify::pre(n >= 0 && n <= 12)
  cppverify::pre(out != nullptr && preserved != nullptr)
  cppverify::modifies(*out)
  cppverify::post(*out == math_factorial(n))
  cppverify::post(*preserved == cppverify::old(*preserved))
{
  *out = iterative_factorial(n);
}

#ifndef CPPVERIFY_POSITIVE_ONLY
int factorial_thirteen_overflows()
  cppverify::post(cppverify::result == cppverify::result)
{
  int factorial_twelve = recursive_factorial(12);
  return factorial_twelve * 13;
}
#endif

// VERIFY-DAG: spec decreases: math_factorial
// VERIFY-DAG: Verified: lemma_factorial_constants
// VERIFY-DAG: Verified: recursive_factorial
// VERIFY-DAG: Verified: iterative_factorial
// VERIFY-DAG: Verified: factorial_twelve
// VERIFY-DAG: Verified: write_factorial
// VERIFY-DAG: error: verification failed: factorial_thirteen_overflows
// VERIFY-DAG: Verified: constexpr spec axiom: machine_factorial_value
