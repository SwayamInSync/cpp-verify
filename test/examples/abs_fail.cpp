int abs_bad(int x)
  pre(true)
  post(result >= 0)
{
  return x; // wrong when x < 0
}