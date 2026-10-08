int parallel_failure(int value)
    cppverify::pre(value >= 0 && value <= 100)
    cppverify::post(cppverify::result == value) {
  cppverify::check(value < 50);
  cppverify::check(value == 101);
  return value;
}
