// REQUIRES: cvc5
// RUN: not %cpp-verify --backend=cvc5 --jobs=4 --timeout=10000 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=CVC5
// RUN: not %cpp-verify --backend=portfolio --jobs=4 --timeout=10000 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=PORTFOLIO
// RUN: %cpp-verify --backend=cvc5 --lower-only %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LOWER
// RUN: not %cpp-verify --obligation-out=%t.obligations %s > /dev/null 2>&1
// RUN: not %cpp-verify --backend=portfolio --jobs=4 --timeout=10000 \
// RUN:   --obligation-in=%t.obligations 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY

spec int quotient(int value, int divisor) {
  return value / divisor;
}

spec int remainder(int value, int divisor) {
  return value % divisor;
}

spec int answer() {
  return 42;
}

int valid_spec_arithmetic()
  post(quotient(-5, 2) == -2)
  post(remainder(-5, 2) == -1)
  post(quotient(5, 0) == 0)
  post(remainder(5, 0) == 5)
{
  return 0;
}

int valid_zero_arity_spec()
  post(answer() == 42)
{
  return 0;
}

int valid_unsigned(unsigned x)
  pre(x == 0xffffffffU)
  post(x / 2U == 0x7fffffffU)
  post(x % 2U == 1U)
{
  return 0;
}

int valid_quantifier(int n)
  pre(n > 0 && n <= 3)
  pre(forall(i, 0, n, i >= 0))
  pre(exists(j, 0, n, j == 0))
  post(result == n)
{
  return n;
}

int read_pointer(int *p)
  pre(p != nullptr)
  post(result == *p)
{
  return *p;
}

void write_pointer(int *p)
  pre(p != nullptr)
  modifies(*p)
  post(*p == 7)
{
  *p = 7;
}

int unsafe_add(int x)
  post(result > x)
{
  return x + 1;
}

int invalid_unsigned(unsigned x)
  post(x <= 0x7fffffffU)
{
  return 0;
}

int invalid_spec_arithmetic()
  post(quotient(-5, 2) == -3)
{
  return 0;
}

// CVC5-DAG: Verified: spec axiom: quotient
// CVC5-DAG: Verified: spec axiom: remainder
// CVC5-DAG: Verified: spec axiom: answer
// CVC5-DAG: Verified: valid_spec_arithmetic [backend=cvc5]
// CVC5-DAG: Verified: valid_zero_arity_spec [backend=cvc5]
// CVC5-DAG: Verified: valid_unsigned [backend=cvc5]
// CVC5-DAG: Verified: valid_quantifier [backend=cvc5]
// CVC5-DAG: Verified: read_pointer [backend=cvc5]
// CVC5-DAG: Verified: write_pointer [backend=cvc5]
// CVC5-DAG: error: verification failed: unsafe_add
// CVC5-DAG: error: verification failed: invalid_unsigned
// CVC5-DAG: error: verification failed: invalid_spec_arithmetic
// CVC5-NOT: backend disagreement

// PORTFOLIO-DAG: Verified: valid_spec_arithmetic [backend=portfolio]
// PORTFOLIO-DAG: Verified: valid_zero_arity_spec [backend=portfolio]
// PORTFOLIO-DAG: Verified: valid_unsigned [backend=portfolio]
// PORTFOLIO-DAG: Verified: valid_quantifier [backend=portfolio]
// PORTFOLIO-DAG: Verified: read_pointer [backend=portfolio]
// PORTFOLIO-DAG: Verified: write_pointer [backend=portfolio]
// PORTFOLIO-DAG: error: verification failed: unsafe_add
// PORTFOLIO-DAG: error: verification failed: invalid_unsigned
// PORTFOLIO-DAG: error: verification failed: invalid_spec_arithmetic
// PORTFOLIO-NOT: backend disagreement

// LOWER-DAG: Lowered: valid_spec_arithmetic
// LOWER-DAG: Lowered: unsafe_add
// LOWER-NOT: Verified:

// REPLAY-DAG: Verified: valid_spec_arithmetic [backend=portfolio]
// REPLAY-DAG: Verified: valid_zero_arity_spec [backend=portfolio]
// REPLAY-DAG: Verified: write_pointer [backend=portfolio]
// REPLAY-DAG: error: verification failed: unsafe_add
// REPLAY-DAG: error: verification failed: invalid_unsigned
// REPLAY-DAG: error: verification failed: invalid_spec_arithmetic
