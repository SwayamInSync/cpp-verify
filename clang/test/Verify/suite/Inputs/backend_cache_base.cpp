int cached_identity(int value)
    cppverify::pre(value >= 0 && value <= 100)
    cppverify::post(cppverify::result == value) {
  cppverify::check(value >= 0);
  return value;
}

int cached_offset(int value)
    cppverify::pre(value >= 0 && value <= 100)
    cppverify::post(cppverify::result == value + 1) {
  cppverify::check(value + 1 > value);
  return value + 1;
}
