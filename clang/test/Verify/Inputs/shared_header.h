#ifndef SHARED_HEADER_H
#define SHARED_HEADER_H

#ifdef __cppverify__
#define CPPVERIFY(...) __VA_ARGS__
#else
#define CPPVERIFY(...)
#endif

#ifdef __cppverify__
cppverify::spec int twice(int n)
{
  return 2 * n;
}
#endif

inline int clamp(int x, int lo, int hi)
  CPPVERIFY(cppverify::pre(lo <= hi))
  CPPVERIFY(cppverify::post(lo <= cppverify::result && cppverify::result <= hi))
{
  return x < lo ? lo : x > hi ? hi : x;
}

inline int double_by_steps(int n)
  CPPVERIFY(cppverify::pre(0 <= n && n <= 1000))
  CPPVERIFY(cppverify::post(cppverify::result == twice(n)))
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    CPPVERIFY(cppverify::invariant(0 <= i && i <= n && s == twice(i)))
    CPPVERIFY(cppverify::decreases(n - i))
  {
    s = s + 2;
    CPPVERIFY(cppverify::check(s <= 2 * n));
  }
  CPPVERIFY(cppverify::ghost {
    int t = twice(n);
    cppverify::check(s == t);
  })
  return s;
}

inline int halve(int x)
  CPPVERIFY(cppverify::post(2 * cppverify::result == x))
{
  return x / 2;
}

#ifdef __cppverify__
#define NONNEGATIVE cppverify::post(cppverify::result >= 0)
#else
#define NONNEGATIVE
#endif

inline int decrement(int x)
  NONNEGATIVE
{
  return x > 0 ? x - 1 : x;
}

#endif
