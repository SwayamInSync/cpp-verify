namespace cv = cppverify;

int wrong(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x)
{
  return x + 1;
}

cv::spec int count(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : count(n - 1) + 1;
}
