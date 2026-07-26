// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int first;
  int second;
};

int pair_sum(Pair pair)
  pre(pair.first >= 0 && pair.second >= 0)
  pre(pair.first <= 100 && pair.second <= 100)
  post(result == pair.first + pair.second)
{
  return pair.first + pair.second;
}

int invalid_aggregate_argument_substitution()
  post(result == 8)
{
  Pair pair;
  pair.first = 3;
  pair.second = 4;
  return pair_sum(pair);
}

int valid_conditional_aggregate_argument(bool choose_first, Pair first,
                                         Pair second)
  pre(first.first >= 0 && first.second >= 0)
  pre(first.first <= 100 && first.second <= 100)
  pre(second.first >= 0 && second.second >= 0)
  pre(second.first <= 100 && second.second <= 100)
  post(result == (choose_first ? first.first + first.second
                              : second.first + second.second))
{
  return pair_sum(choose_first ? first : second);
}

// VERIFY-DAG: Verified: pair_sum
// VERIFY-DAG: Verified: valid_conditional_aggregate_argument
// VERIFY-DAG: error: verification failed: invalid_aggregate_argument_substitution
