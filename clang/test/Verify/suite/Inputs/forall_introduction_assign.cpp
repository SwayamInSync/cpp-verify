cppverify::proof void assigns_arbitrary(int n)
  cppverify::pre(n >= 0)
{
  cppverify::check(cppverify::forall(k, 0, n, k >= 0)) by {
    k = 0;
  }
}
// ASSIGN: error: assigns_arbitrary: k stands for every value of its forall and cannot be assigned
