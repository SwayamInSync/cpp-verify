int obligation_hash_scope(int x)
  pre(x >= 0)
  post(result >= 0)
{
  contract_assert(x >= 0);
  contract_assert(forall(i, 0, x, i >= 0));
  return x;
}
