// Certified failures shown in Lean, for lean_refutation.test.

int add_one(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 2;
}

int below_three()
  cppverify::post(cppverify::forall(i, 0, 4, i < 3))
{
  return 0;
}

void zero_first(int *p)
  cppverify::pre(cppverify::valid(p, 2))
  cppverify::modifies(*p)
  cppverify::post(p[0] == 1)
{
  p[0] = 0;
}

cppverify::spec int tri(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

cppverify::proof void tri_three()
  cppverify::post(tri(3) == 7)
{
}

// A choice is opaque in Lean, so its counterexample is not decided there.
cppverify::proof void pick_one()
  cppverify::post(cppverify::choose(k, 0, 2, k == 1) == 0)
{
}
