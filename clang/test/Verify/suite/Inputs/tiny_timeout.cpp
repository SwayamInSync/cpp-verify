#include <cppverify.h>
using cppverify::valid;

void copy(const int *a, int *out, int n)
  cppverify::pre(n >= 0 && valid(a, n) && valid(out, n))
  cppverify::modifies(*out)
  cppverify::post(cppverify::forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(cppverify::forall(j, 0, i, out[j] == a[j]))
    cppverify::decreases(n - i)
  {
    out[i] = a[i];
    i = i + 1;
  }
}
