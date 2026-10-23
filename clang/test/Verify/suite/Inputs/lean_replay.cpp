// A program whose archive replays into a Lean project, for lean_replay.test.

cppverify::spec int tri(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

cppverify::proof void tri_nonneg(int n)
  cppverify::post(tri(n) >= 0)
{
}

// A measure that applies a spec: its module keeps the spec it applies.
cppverify::spec int size(int n) { return n; }

cppverify::spec int down(int n)
  cppverify::decreases(size(n))
{
  return n <= 0 ? 0 : down(n - 1);
}

cppverify::proof void down_zero()
  cppverify::post(down(0) == 0)
{
}

int inc(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}
