#include <cppverify.h>
using cppverify::valid;

void copy(const int *a, int *out, int n)
  pre(n >= 0 && valid(a, n) && valid(out, n))
  modifies(*out)
  post(forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    invariant(forall(j, 0, i, out[j] == a[j]))
    decreases(n - i)
  {
    out[i] = a[i];
    i = i + 1;
  }
}
