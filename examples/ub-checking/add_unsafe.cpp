// Nothing bounds a and b, so a + b can overflow, and signed overflow is
// undefined behavior: verification fails with a counterexample.
int add(int a, int b)
  cppverify::post(cppverify::result == a + b)
{
  return a + b;
}
