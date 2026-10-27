int ping(int n)
  cppverify::pre(n >= 0 && n < 1000)
  cppverify::post(cppverify::result == 0);

int pong(int n)
  cppverify::pre(n >= 0 && n < 1000)
  cppverify::post(cppverify::result == 0)
{
  return n == 0 ? 0 : ping(n - 1);
}
