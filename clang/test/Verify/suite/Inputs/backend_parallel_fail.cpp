int parallel_failure(int value)
    pre(value >= 0 && value <= 100)
    post(result == value) {
  contract_assert(value < 0);
  contract_assert(value == 101);
  return value;
}
