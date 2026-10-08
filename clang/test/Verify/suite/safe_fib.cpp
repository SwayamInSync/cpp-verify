// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %clang -std=c++17 -fverify-contracts -DCPPVERIFY_POSITIVE_ONLY \
// RUN:   -c %s -o %t.o
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int math_fibonacci(int n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  if (n == 1)
    return 1;
  return math_fibonacci(n - 1) + math_fibonacci(n - 2);
}

cppverify::spec int math_value(int value) {
  return value;
}

constexpr bool machine_fibonacci_value(int n, int value) {
  return (n == 0 && value == 0) ||
         (n == 1 && value == 1) ||
         (n == 2 && value == 1) ||
         (n == 3 && value == 2) ||
         (n == 4 && value == 3) ||
         (n == 5 && value == 5) ||
         (n == 6 && value == 8) ||
         (n == 7 && value == 13) ||
         (n == 8 && value == 21) ||
         (n == 9 && value == 34) ||
         (n == 10 && value == 55) ||
         (n == 11 && value == 89) ||
         (n == 12 && value == 144) ||
         (n == 13 && value == 233) ||
         (n == 14 && value == 377) ||
         (n == 15 && value == 610) ||
         (n == 16 && value == 987) ||
         (n == 17 && value == 1597) ||
         (n == 18 && value == 2584) ||
         (n == 19 && value == 4181) ||
         (n == 20 && value == 6765) ||
         (n == 21 && value == 10946) ||
         (n == 22 && value == 17711) ||
         (n == 23 && value == 28657) ||
         (n == 24 && value == 46368) ||
         (n == 25 && value == 75025) ||
         (n == 26 && value == 121393) ||
         (n == 27 && value == 196418) ||
         (n == 28 && value == 317811) ||
         (n == 29 && value == 514229) ||
         (n == 30 && value == 832040) ||
         (n == 31 && value == 1346269) ||
         (n == 32 && value == 2178309) ||
         (n == 33 && value == 3524578) ||
         (n == 34 && value == 5702887) ||
         (n == 35 && value == 9227465) ||
         (n == 36 && value == 14930352) ||
         (n == 37 && value == 24157817) ||
         (n == 38 && value == 39088169) ||
         (n == 39 && value == 63245986) ||
         (n == 40 && value == 102334155) ||
         (n == 41 && value == 165580141) ||
         (n == 42 && value == 267914296) ||
         (n == 43 && value == 433494437) ||
         (n == 44 && value == 701408733) ||
         (n == 45 && value == 1134903170) ||
         (n == 46 && value == 1836311903);
}

cppverify::proof void lemma_fibonacci_step(int n)
  cppverify::pre(n >= 2)
  cppverify::post(math_fibonacci(n) ==
       math_fibonacci(n - 1) + math_fibonacci(n - 2))
{
  cppverify::reveal_with_fuel(math_fibonacci, 1);
}

cppverify::proof void lemma_fibonacci_base(int n)
  cppverify::pre(n >= 0 && n <= 1)
  cppverify::post(math_fibonacci(n) == math_value(n))
{
  cppverify::reveal_with_fuel(math_fibonacci, 1);
}

cppverify::proof void lemma_fibonacci_machine_step(int i, int previous, int current)
  cppverify::pre(i >= 1 && i < 46)
  cppverify::pre(previous >= 0 && previous <= 701408733)
  cppverify::pre(current >= 0 && current <= 1134903170)
  cppverify::pre(math_value(previous) == math_fibonacci(i - 1))
  cppverify::pre(math_value(current) == math_fibonacci(i))
  cppverify::post(math_value(previous + current) == math_fibonacci(i + 1))
{
  lemma_fibonacci_step(i + 1);
  // Materialize the addition to check both machine definedness and its
  // exact mathematical value.
  int sum = previous + current;
}

int recursive_fibonacci(int n)
  cppverify::pre(n >= 0 && n <= 46)
  cppverify::post(machine_fibonacci_value(n, cppverify::result))
  cppverify::post(cppverify::result == math_fibonacci(n))
  cppverify::decreases(n)
{
  cppverify::ghost {
    cppverify::hide(math_fibonacci);
  }
  int answer = n;
  if (n <= 1) {
    cppverify::ghost {
      lemma_fibonacci_base(n);
    }
  } else {
    int previous = recursive_fibonacci(n - 1);
    int before_previous = recursive_fibonacci(n - 2);
    cppverify::ghost {
      lemma_fibonacci_machine_step(n - 1, before_previous, previous);
    }
    answer = previous + before_previous;
    cppverify::ghost {
      cppverify::check(math_value(answer) == math_fibonacci(n));
    }
  }
  return answer;
}

int iterative_fibonacci(int n)
  cppverify::pre(n >= 0 && n <= 46)
  cppverify::post(machine_fibonacci_value(n, cppverify::result))
  cppverify::post(cppverify::result == math_fibonacci(n))
{
  cppverify::ghost {
    cppverify::hide(math_fibonacci);
  }
  if (n <= 1) {
    cppverify::ghost {
      lemma_fibonacci_base(n);
    }
    return n;
  }
  cppverify::ghost {
    lemma_fibonacci_base(0);
    lemma_fibonacci_base(1);
  }

  int previous = 0;
  int current = 1;
  int i = 1;
  while (i < n)
    cppverify::invariant(i >= 1 && i <= n)
    cppverify::invariant(machine_fibonacci_value(i - 1, previous))
    cppverify::invariant(machine_fibonacci_value(i, current))
    cppverify::invariant(math_value(previous) == math_fibonacci(i - 1))
    cppverify::invariant(math_value(current) == math_fibonacci(i))
    cppverify::decreases(n - i)
  {
    cppverify::ghost {
      lemma_fibonacci_machine_step(i, previous, current);
    }
    int next = previous + current;
    cppverify::ghost {
      cppverify::check(math_value(next) == math_fibonacci(i + 1));
    }
    previous = current;
    current = next;
    i = i + 1;
  }
  return current;
}

int fibonacci_forty_six()
  cppverify::post(cppverify::result == 1836311903)
{
  return iterative_fibonacci(46);
}

#ifndef CPPVERIFY_POSITIVE_ONLY
int fibonacci_forty_seven_overflows()
  cppverify::post(cppverify::result == cppverify::result)
{
  int fibonacci_forty_six = recursive_fibonacci(46);
  int fibonacci_forty_five = iterative_fibonacci(45);
  return fibonacci_forty_six + fibonacci_forty_five;
}
#endif

// VERIFY-DAG: Verified: spec decreases: math_fibonacci
// VERIFY-DAG: Verified: spec axiom: math_value
// VERIFY-DAG: Verified: lemma_fibonacci_step
// VERIFY-DAG: Verified: lemma_fibonacci_base
// VERIFY-DAG: Verified: lemma_fibonacci_machine_step
// VERIFY-DAG: Verified: recursive_fibonacci
// VERIFY-DAG: Verified: iterative_fibonacci
// VERIFY-DAG: Verified: fibonacci_forty_six
// VERIFY-DAG: error: verification failed: fibonacci_forty_seven_overflows
// VERIFY-DAG: Verified: constexpr spec axiom: machine_fibonacci_value
