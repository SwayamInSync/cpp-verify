// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int unsupported_comma_contract(int x)
  post((x, result) == x)
{
  return x;
}

spec int unsupported_math_bitwise(int x) {
  return x & 1;
}

spec int unsupported_heap_read(int *p) {
  return *p;
}

spec int unsupported_loop_spec(int x) {
  while (x > 0)
    x = x - 1;
  return x;
}

spec int unsupported_recursive_spec(int n) {
  if (n > 0)
    return unsupported_recursive_spec(n - 1);
  return 0;
}

spec int unsupported_mutual_b(int n);

spec int unsupported_mutual_a(int n) {
  return unsupported_mutual_b(n);
}

spec int unsupported_mutual_b(int n) {
  return unsupported_mutual_a(n);
}

// VERIFY-DAG: error: unsupported_comma_contract: unsupported expression in post
// VERIFY-DAG: error: unsupported_math_bitwise: bitwise operators are unsupported in mathematical spec functions
// VERIFY-DAG: error: unsupported_heap_read: heap-reading spec functions are unsupported
// VERIFY-DAG: error: unsupported_loop_spec: spec function body is unsupported by axiomatic lowering
// VERIFY-DAG: error: unsupported_recursive_spec: recursive spec and proof functions require decreases
// VERIFY-DAG: error: unsupported_mutual_a: mutually recursive spec and proof functions are unsupported
// VERIFY-DAG: error: unsupported_mutual_b: mutually recursive spec and proof functions are unsupported
