// For smt2_dumps.test: a counterexample whose quantifier range is too wide
// to check is sought again, on the same solver, with a narrower range.

namespace cv = cppverify;

int first_positive_bitwise(const int *p, int n)
  cv::pre(n >= 2000000 && n <= 3000000 && cv::valid(p, n))
  cv::pre(cv::forall(i, 0, n, (i ^ 1431655765) < 0 || p[i] >= 0))
  cv::post(cv::result > 0)
{
  return p[0];
}
