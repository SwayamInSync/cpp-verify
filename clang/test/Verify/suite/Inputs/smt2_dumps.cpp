// Queries for smt2_dumps.test: a proof, a failure, a proof whose query has
// a quantifier, and a failure about a recursive spec, whose queries are
// checked again with definition instances.

namespace cv = cppverify;

int inc(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

int clamp(int x)
  cv::pre(x > -100 && x < 100)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    return x + 1;
  return x;
}

int second(const int *a, int n)
  cv::pre(cv::valid(a, n) && n > 2)
  cv::pre(cv::forall(k, 0, n, a[k] >= 0))
  cv::post(cv::result >= 0)
{
  return a[1];
}

cppverify::spec int tri(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

int closed(int n)
  cv::pre(0 <= n && n <= 3)
  cv::post(cv::result == tri(n))
{
  return n;
}

// Overloads, whose queries are kept apart.
int half(int x)
  cv::pre(x >= 0)
  cv::post(cv::result <= x)
{
  return x / 2;
}

long half(long x)
  cv::pre(x >= 0)
  cv::post(cv::result <= x)
{
  return x / 2;
}
