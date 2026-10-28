"""Scalar loops (break/continue/return, do-while, nested, termination)."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

def d1(lo, hi, extra=()):
    return [(v,) for v in sorted(set(list(range(lo, hi)) + list(extra)))]

INTB = [-2**31, -2**31 + 1, 2**31 - 1, 2**31 - 2, 65535, 65536, 46340, 46341, 100000, 1000000]

def tri(n):
    return n * (n + 1) // 2

case('l_sum', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     '''int s = 0;
for (int i = 1; i <= n; i++)
  cppverify::invariant(1 <= i && i <= n + 1 && s == (i - 1) * i / 2)
  cppverify::decreases(n + 1 - i)
{ s += i; }
return s;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == tri(n), domain=d1(-5, 1010))
case('l_sum_overflow', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 100000)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     '''int s = 0;
for (int i = 1; i <= n; i++)
  cppverify::invariant(1 <= i && i <= n + 1 && s == (i - 1) * i / 2)
  cppverify::decreases(n + 1 - i)
{ s += i; }
return s;''', pre=lambda n: 0 <= n <= 100000, post=lambda n, r: r == tri(n),
     domain=d1(65530, 65540, [0, 1, 1000, 65535, 65536, 92681, 100000]))
case('l_counter_overflow', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0)\ncppverify::post(%s == n + 1)' % R,
     '''int c = 0;
for (int i = 0; i <= n; i++)
  cppverify::invariant(0 <= i && i <= n + 1 && c == i)
  cppverify::decreases(n + 1 - i)
{ c++; }
return c;''', pre=lambda n: n >= 0, post=lambda n, r: r == n + 1,
     domain=d1(0, 50, [10**6, 2**31 - 1]), alarm_ms=20000)
case('l_u8_counter', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 300)\ncppverify::post(%s == n)' % R,
     '''int c = 0;
for (uint8_t i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i)
  cppverify::decreases(n - i)
{ c++; }
return c;''', pre=lambda n: 0 <= n <= 300, post=lambda n, r: r == n,
     domain=d1(250, 260, [0, 1, 255, 256, 300]), alarm_ms=300)
case('l_u8_counter_le', [('uint8_t', 'n')], 'int',
     'cppverify::post(%s == n + 1)' % R,
     '''int c = 0;
for (uint8_t i = 0; i <= n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i)
  cppverify::decreases(n - i)
{ c++; if (i == n) break; }
return c;''', post=lambda n, r: r == n + 1, alarm_ms=300)
case('l_u8_counter_le_nobreak', [('uint8_t', 'n')], 'int',
     'cppverify::post(%s == n + 1)' % R,
     '''int c = 0;
uint8_t i = 0;
while (i <= n)
  cppverify::invariant(c == i && i <= n + 1)
  cppverify::decreases(n + 1 - i)
{ c++; i++; }
return c;''', post=lambda n, r: r == n + 1, alarm_ms=300)
case('l_break_find', [('int', 'n'), ('int', 't')], 'int',
     'cppverify::pre(n >= 0 && n <= 100 && t >= 0)\ncppverify::post(t < n ? %s == t : %s == n)' % (R, R),
     '''int i = 0;
while (i < n)
  cppverify::invariant(0 <= i && i <= n && (i <= t))
  cppverify::decreases(n - i)
{ if (i == t) break; i++; }
return i;''', pre=lambda n, t: 0 <= n <= 100 and t >= 0, post=lambda n, t, r: r == (t if t < n else n),
     domain=[(n, t) for n in range(-1, 30) for t in range(-1, 35)])
case('l_continue_sum_even', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == (n / 2) * (n / 2 + 1))' % R,
     '''int s = 0;
for (int i = 0; i <= n; i++)
  cppverify::invariant(0 <= i && i <= n + 1 && s == ((i + 1) / 2 - 1) * ((i + 1) / 2))
  cppverify::decreases(n + 1 - i)
{ if (i % 2 != 0) continue; s += i; }
return s;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == (n // 2) * (n // 2 + 1), domain=d1(-2, 1005))
case('l_continue_simple', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == n / 2)' % R,
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i / 2)
  cppverify::decreases(n - i)
{ if (i % 2 == 0) continue; c++; }
return c;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == n // 2, domain=d1(-2, 1005))
case('l_continue_wrong', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == (n + 1) / 2)' % R,
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == (i + 1) / 2)
  cppverify::decreases(n - i)
{ if (i % 2 == 0) continue; c++; }
return c;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == (n + 1) // 2, domain=d1(-2, 1005))
case('l_early_return', [('int', 'n'), ('int', 't')], 'int',
     'cppverify::pre(n >= 0 && n <= 100)\ncppverify::post((0 <= t && t < n) ? %s == t * 2 : %s == -1)' % (R, R),
     '''for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && (t < 0 || t >= i))
  cppverify::decreases(n - i)
{ if (i == t) return i * 2; }
return -1;''', pre=lambda n, t: 0 <= n <= 100, post=lambda n, t, r: r == (2 * t if 0 <= t < n else -1),
     domain=[(n, t) for n in range(-1, 30) for t in range(-3, 35)])
case('l_do_while', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == (n == 0 ? 1 : n))' % R,
     '''int i = 0;
do {
  i = i + 1;
} while (i < n)
  cppverify::invariant(i >= 1 && (i <= n || i == 1))
  cppverify::decreases(n - i);
return i;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == (1 if n == 0 else n), domain=d1(-2, 1005))
case('l_do_while_wrong', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == n)' % R,
     '''int i = 0;
do {
  i = i + 1;
} while (i < n)
  cppverify::invariant(i >= 1 && (i <= n || i == 1))
  cppverify::decreases(n - i);
return i;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == n, domain=d1(-2, 1005))
case('l_do_while_overflow', [('int', 'x')], 'int',
     'cppverify::post(%s >= x)' % R,
     '''do {
  x = x + 1;
} while (x < 10)
  cppverify::invariant(true)
  cppverify::decreases(10 - x);
return x;''', post=lambda x, r: r >= x, domain=d1(-50, 50, INTB))
case('l_nested', [('int', 'n'), ('int', 'm')], 'int',
     'cppverify::pre(n >= 0 && n <= 50 && m >= 0 && m <= 50)\ncppverify::post(%s == n * m)' % R,
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i * m)
  cppverify::decreases(n - i)
{
  for (int j = 0; j < m; j++)
    cppverify::invariant(0 <= j && j <= m && c == i * m + j)
    cppverify::decreases(m - j)
  { c++; }
}
return c;''', pre=lambda n, m: 0 <= n <= 50 and 0 <= m <= 50, post=lambda n, m, r: r == n * m,
     domain=[(n, m) for n in range(-1, 53) for m in range(-1, 53)])
case('l_nested_break', [('int', 'n')], 'int',
     'cppverify::pre(n >= 1 && n <= 50)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i * (i + 1) / 2)
  cppverify::decreases(n - i)
{
  int j = 0;
  while (true)
    cppverify::invariant(0 <= j && j <= i && c == i * (i + 1) / 2 + j)
    cppverify::decreases(i - j)
  { c++; if (j == i) break; j++; }
}
return c;''', pre=lambda n: 1 <= n <= 50, post=lambda n, r: r == tri(n), domain=d1(-1, 55))
case('l_nested_break_wrong', [('int', 'n')], 'int',
     'cppverify::pre(n >= 1 && n <= 50)\ncppverify::post(%s == n * (n - 1) / 2)' % R,
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c == i * (i + 1) / 2)
  cppverify::decreases(n - i)
{
  int j = 0;
  while (true)
    cppverify::invariant(0 <= j && j <= i && c == i * (i + 1) / 2 + j)
    cppverify::decreases(i - j)
  { c++; if (j == i) break; j++; }
}
return c;''', pre=lambda n: 1 <= n <= 50, post=lambda n, r: r == n * (n - 1) // 2, domain=d1(-1, 55))
case('l_while_true_return', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x <= 1000)\ncppverify::post(%s == x %% 7)' % R,
     '''while (true)
  cppverify::invariant(x >= 0 && x % 7 == cppverify::old(x) % 7)
  cppverify::decreases(x)
{ if (x < 7) return x; x -= 7; }''', pre=lambda x: 0 <= x <= 1000, post=lambda x, r: r == x % 7, domain=d1(-3, 1003))
case('l_cond_ub', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0)\ncppverify::post(%s * %s <= n)' % (R, R),
     '''int i = 0;
while ((i + 1) * (i + 1) <= n)
  cppverify::invariant(i >= 0 && i * i <= n)
  cppverify::decreases(n - i)
{ i++; }
return i;''', pre=lambda n: n >= 0, post=lambda n, r: r * r <= n,
     domain=d1(0, 100, [2**31 - 1, 2**31 - 2, 2147395600, 2147395599, 2147488281 - 2**31 + 2**31 - 1]))
case('l_step2_neq', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 100)\ncppverify::post(%s == n)' % R,
     '''int i = 0;
while (i != n)
  cppverify::invariant(i >= 0 && i <= n)
  cppverify::decreases(n - i)
{ i += 2; }
return i;''', pre=lambda n: 0 <= n <= 100, post=lambda n, r: r == n, domain=d1(0, 10), alarm_ms=300)
case('l_post_assign_param', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == 2 * n)' % R,
     '''int r = 0;
while (n > 0)
  cppverify::invariant(n >= 0 && r == 2 * (cppverify::old(n) - n))
  cppverify::decreases(n)
{ n--; r += 2; }
return r;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == 2 * n, domain=d1(-2, 1003))
case('l_small_type_acc', [('uint8_t', 'n')], 'uint8_t',
     'cppverify::post(%s == (n * (n + 1) / 2) %% 256)' % R,
     '''uint8_t s = 0;
for (int i = 1; i <= n; i++)
  cppverify::invariant(1 <= i && i <= n + 1 && s == ((i - 1) * i / 2) % 256)
  cppverify::decreases(n + 1 - i)
{ s += i; }
return s;''', post=lambda n, r: r == tri(n) % 256)
case('l_short_acc', [('int', 'n')], 'short',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == ((n * (n + 1) / 2 + 32768) %% 65536) - 32768)' % R,
     '''short s = 0;
for (int i = 1; i <= n; i++)
  cppverify::invariant(1 <= i && i <= n + 1 && s == (((i - 1) * i / 2 + 32768) % 65536) - 32768)
  cppverify::decreases(n + 1 - i)
{ s += i; }
return s;''', pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == wrap(tri(n), 'short'), domain=d1(-2, 1003))
case('l_mul_acc_overflow', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 20)\ncppverify::post(%s >= 1)' % R,
     '''int p = 1;
for (int i = 1; i <= n; i++)
  cppverify::invariant(1 <= i && i <= n + 1 && p >= 1)
  cppverify::decreases(n + 1 - i)
{ p *= i; }
return p;''', pre=lambda n: 0 <= n <= 20, post=lambda n, r: r >= 1, domain=d1(-1, 22))
case('l_decreases_wrong_sign', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 100)\ncppverify::post(%s == n)' % R,
     '''int i = 0;
while (i < n)
  cppverify::invariant(0 <= i && i <= n)
  cppverify::decreases(i)
{ i++; }
return i;''', pre=lambda n: 0 <= n <= 100, post=lambda n, r: r == n, domain=d1(0, 101))
case('l_decreases_lex', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 20)\ncppverify::post(%s == n * 3)' % R,
     '''int a = n; int b = 0; int c = 0;
while (a > 0 || b > 0)
  cppverify::invariant(a >= 0 && b >= 0 && b <= 2 && c == (n - a) * 3 - b)
  cppverify::decreases(a, b)
{ if (b > 0) { b--; c++; } else { a--; b = 2; c++; } }
return c;''', pre=lambda n: 0 <= n <= 20, post=lambda n, r: r == 3 * n, domain=d1(-1, 22))

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
