cppverify::spec bool always_false(int value) { return false; }

int inlined_source(int value)
  cppverify::post(always_false(value))
{
  return value;
}
