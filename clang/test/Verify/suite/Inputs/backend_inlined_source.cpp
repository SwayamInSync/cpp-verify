spec bool always_false(int value) { return false; }

int inlined_source(int value)
  post(always_false(value))
{
  return value;
}
