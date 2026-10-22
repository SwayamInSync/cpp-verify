[[cppverify::trusted]] int sensor(int channel)
  cppverify::pre(channel >= 0 && channel < 8)
  cppverify::pre(100 / (channel + 1) > 0);

int reading()
  cppverify::post(true)
{
  return sensor(3);
}
