namespace cv = cppverify;

int inc(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

int clamp(int x)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    return x + 1;
  return x;
}

int never(int x)
  cv::pre(x > 0 && x < 0)
  cv::post(cv::result == 1)
{
  return 0;
}

int assigns(int x) {
  if (x = 1)
    return 0;
  return 1;
}
