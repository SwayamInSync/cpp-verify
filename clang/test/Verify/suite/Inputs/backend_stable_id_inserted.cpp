int stable_identity(int value)
  post(result == 0)
{
  contract_assert(value == value);
  return value;
}
