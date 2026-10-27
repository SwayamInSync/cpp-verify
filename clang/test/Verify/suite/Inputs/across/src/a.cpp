#include "mathx.h"

int scaled(int x)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 200)
{
  return 2 * clamp100(x);
}

int twice_scaled(int x)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 400)
{
  return 2 * scaled(x);
}
