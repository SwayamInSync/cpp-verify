// A declaration that states another contract than the one mathx.cpp's
// definition is verified against.
int clamp100(int x)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 50);

int halved(int x)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 50)
{
  return clamp100(x);
}
