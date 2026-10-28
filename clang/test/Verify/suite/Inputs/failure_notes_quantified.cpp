// A failure whose query cvc5 answers unknown, with a model the certifier
// checks, for failure_notes_cvc5.test.

namespace cv = cppverify;

int first(const int *a, int n)
  cv::pre(cv::valid(a, n) && n > 2)
  cv::pre(cv::forall(k, 0, n, a[k] >= 0))
  cv::post(cv::result > 0)
{
  int r = a[1];
  if (r > 5)
    r = r - 1;
  return r;
}
