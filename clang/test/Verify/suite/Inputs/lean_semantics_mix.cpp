unsigned mix(unsigned a, unsigned b)
  cppverify::post(true)
{
  unsigned r = (a ^ b) + 1u;
  unsigned s = a ^ (b + 1u);
  cppverify::check(r == s);
  return r;
}
