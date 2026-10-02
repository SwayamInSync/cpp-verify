proof void assigns_arbitrary(int n)
  pre(n >= 0)
{
  contract_assert(forall(k, 0, n, k >= 0)) by {
    k = 0;
  }
}
// ASSIGN: error: assigns_arbitrary: k stands for every value of its forall and cannot be assigned
