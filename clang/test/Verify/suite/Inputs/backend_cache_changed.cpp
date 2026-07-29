int cached_identity(int value)
    pre(value >= 0 && value <= 100)
    post(result == value) {
  contract_assert(value >= 0);
  return value;
}

int cached_offset(int value)
    pre(value >= 0 && value <= 100)
    post(result == value + 2) {
  contract_assert(value + 2 > value);
  return value + 2;
}
