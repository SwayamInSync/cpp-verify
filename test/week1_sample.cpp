// week1_sample.cpp — CppVerify Week 1 milestone verification
//
// This file is written in CONTRACT SYNTAX. It requires -fverify-contracts.
// Without the flag the parser sees unknown type names and fails — that is
// expected and correct: contract files are not plain C++.
//
// ─────────────────────────────────────────────────────────────────────────────
// WHAT WEEK 1 PROVES
// ─────────────────────────────────────────────────────────────────────────────
//  1. Keyword recognition (-fverify-contracts -Xclang -dump-tokens):
//       pre, post, invariant, decreases, ghost, spec, proof,
//       contract_assert, forall, exists, old, result
//     all appear as keyword tokens, not 'identifier' tokens.
//
//  2. Backward compatibility (see week1_compat.cpp):
//     Existing C++ code that uses these words as identifiers compiles
//     unchanged without -fverify-contracts.
//
//  3. Parse errors with the flag (Week 2's job):
//     -fverify-contracts makes the lexer emit keyword tokens, but the
//     parser doesn't yet understand them → parse errors are expected now.
// ─────────────────────────────────────────────────────────────────────────────
// COMMANDS TO RUN
// ─────────────────────────────────────────────────────────────────────────────
//
// ① Verify keyword tokens (lex-only, no parsing):
//   ./build/bin/clang -std=c++20 -fverify-contracts -Xclang -dump-tokens \
//       test/week1_sample.cpp 2>&1 \
//     | grep -E "^(pre|post|invariant|decreases|ghost|spec|proof|contract_assert|forall|exists|old|result) '"
//
// ② Confirm parse errors are expected (Week 2's job):
//   ./build/bin/clang -std=c++20 -fverify-contracts -c test/week1_sample.cpp
//   # → errors like "expected function body after function declarator"
//
// ③ Confirm backward compat (see week1_compat.cpp):
//   ./build/bin/clang -std=c++20 -c test/week1_compat.cpp -o /dev/null
//   # → exit 0, compiles clean
// ─────────────────────────────────────────────────────────────────────────────

// Spec function: pure mathematical model of factorial
spec int factorial(int n)
  decreases(n)
{
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

// Proof function: establish a lemma
proof void lemma_factorial_positive(int n)
  pre(n >= 1)
  post(factorial(n) >= 1)
  decreases(n)
{
    if (n == 1) {
        // base case
    } else {
        lemma_factorial_positive(n - 1);
    }
}

// Normal function with pre/post contracts
int safe_factorial(int n)
  pre(n >= 0)
  pre(n <= 12)
  post(result == factorial(n))
  post(result >= 1)
{
    if (n == 0) return 1;

    int acc = 1;
    int i = 1;

    while (i <= n)
      invariant(1 <= i && i <= n + 1)
      invariant(acc == factorial(i - 1))
      decreases(n - i + 1)
    {
        ghost {
            lemma_factorial_positive(i);
            contract_assert(acc * i >= acc);
        }

        acc = acc * i;
        i = i + 1;
    }

    return acc;
}

// Quantifier syntax
spec bool all_positive(int arr[], int n)
{
    return forall(i, 0, n, arr[i] > 0);
}

spec bool has_zero(int arr[], int n)
{
    return exists(i, 0, n, arr[i] == 0);
}

// old() and result in postconditions
int increment(int x)
  pre(x < 2147483647)
  post(result == old(x) + 1)
{
    return x + 1;
}
