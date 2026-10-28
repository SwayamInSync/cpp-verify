"""BMC backend on loops whose trip count the precondition bounds."""
import differential as diff
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

def tri(n):
    return n * (n + 1) // 2

case('b_sum', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     'int s = 0;\nfor (int i = 1; i <= n; i++) { s += i; }\nreturn s;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == tri(n), domain=[(n,) for n in range(-3, 10)])
case('b_sum_wrong_at4', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     'int s = 0;\nfor (int i = 1; i <= n; i++) { if (i == 4) s += 1; s += i; }\nreturn s;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == tri(n), domain=[(n,) for n in range(-3, 10)])
case('b_continue', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == n / 2)' % R,
     'int c = 0;\nfor (int i = 0; i < n; i++) { if (i % 2 == 0) continue; c++; }\nreturn c;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == n // 2, domain=[(n,) for n in range(-3, 10)])
case('b_continue_wrong', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == (n + 1) / 2)' % R,
     'int c = 0;\nfor (int i = 0; i < n; i++) { if (i % 2 == 0) continue; c++; }\nreturn c;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == (n + 1) // 2, domain=[(n,) for n in range(-3, 10)])
case('b_continue_while', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == n - n / 2)' % R,
     'int c = 0; int i = 0;\nwhile (i < n) { i++; if (i % 2 == 0) continue; c++; }\nreturn c;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == n - n // 2, domain=[(n,) for n in range(-3, 10)])
case('b_break', [('int', 'n'), ('int', 't')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == (t >= 0 && t < n ? t : n))' % R,
     'int i = 0;\nwhile (i < n) { if (i == t) break; i++; }\nreturn i;',
     pre=lambda n, t: 0 <= n <= 5, post=lambda n, t, r: r == (t if 0 <= t < n else n),
     domain=[(n, t) for n in range(-1, 8) for t in range(-2, 8)])
case('b_break_wrong', [('int', 'n'), ('int', 't')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == (t >= 0 && t <= n ? t : n))' % R,
     'int i = 0;\nwhile (i < n) { if (i == t) break; i++; }\nreturn i;',
     pre=lambda n, t: 0 <= n <= 5, post=lambda n, t, r: r == (t if 0 <= t <= n else n),
     domain=[(n, t) for n in range(-1, 8) for t in range(-2, 8)])
case('b_return_in_loop', [('int', 'n'), ('int', 't')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == (t >= 0 && t < n ? 2 * t : -1))' % R,
     'for (int i = 0; i < n; i++) { if (i == t) return 2 * i; }\nreturn -1;',
     pre=lambda n, t: 0 <= n <= 5, post=lambda n, t, r: r == (2 * t if 0 <= t < n else -1),
     domain=[(n, t) for n in range(-1, 8) for t in range(-2, 8)])
case('b_do_while', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == (n == 0 ? 1 : n))' % R,
     'int i = 0;\ndo { i = i + 1; } while (i < n);\nreturn i;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == (1 if n == 0 else n), domain=[(n,) for n in range(-3, 10)])
case('b_do_while_wrong', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 5)\ncppverify::post(%s == n)' % R,
     'int i = 0;\ndo { i = i + 1; } while (i < n);\nreturn i;',
     pre=lambda n: 0 <= n <= 5, post=lambda n, r: r == n, domain=[(n,) for n in range(-3, 10)])
case('b_nested', [('int', 'n'), ('int', 'm')], 'int',
     'cppverify::pre(n >= 0 && n <= 3 && m >= 0 && m <= 3)\ncppverify::post(%s == n * m)' % R,
     'int c = 0;\nfor (int i = 0; i < n; i++) { for (int j = 0; j < m; j++) { c++; } }\nreturn c;',
     pre=lambda n, m: 0 <= n <= 3 and 0 <= m <= 3, post=lambda n, m, r: r == n * m,
     domain=[(n, m) for n in range(-1, 6) for m in range(-1, 6)])
case('b_nested_break_inner', [('int', 'n')], 'int',
     'cppverify::pre(n >= 1 && n <= 3)\ncppverify::post(%s == n * (n + 1) / 2)' % R,
     'int c = 0;\nfor (int i = 0; i < n; i++) { int j = 0; while (true) { c++; if (j == i) break; j++; } }\nreturn c;',
     pre=lambda n: 1 <= n <= 3, post=lambda n, r: r == tri(n), domain=[(n,) for n in range(-1, 6)])
case('b_nested_continue_outer', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 4)\ncppverify::post(%s == (n / 2) * n)' % R,
     'int c = 0;\nfor (int i = 0; i < n; i++) { if (i % 2 == 0) continue; for (int j = 0; j < n; j++) c++; }\nreturn c;',
     pre=lambda n: 0 <= n <= 4, post=lambda n, r: r == (n // 2) * n, domain=[(n,) for n in range(-1, 7)])
case('b_overflow_iter3', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0)\ncppverify::post(true)',
     'int r = x;\nfor (int i = 0; i < 3; i++) { r = r * 2; }\nreturn r;',
     pre=lambda x: x >= 0, post=lambda x, r: True)
case('b_overflow_guarded', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x < 100000000)\ncppverify::post(%s == 8 * x)' % R,
     'int r = x;\nfor (int i = 0; i < 3; i++) { r = r * 2; }\nreturn r;',
     pre=lambda x: 0 <= x < 10**8, post=lambda x, r: r == 8 * x)
case('b_unbounded_loop', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0)\ncppverify::post(%s == n)' % R,
     'int i = 0;\nwhile (i < n) { i++; }\nreturn i;',
     pre=lambda n: n >= 0, post=lambda n, r: r == n, domain=[(n,) for n in range(0, 200)] + [(2**31 - 1,)], alarm_ms=20000)
case('b_unbounded_bug_late', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 100)\ncppverify::post(%s == n)' % R,
     'int i = 0;\nwhile (i < n) { if (i == 50) i++; i++; }\nreturn i;',
     pre=lambda n: 0 <= n <= 100, post=lambda n, r: r == n, domain=[(n,) for n in range(0, 101)])
case('b_while_cond_side', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 4)\ncppverify::post(%s == n)' % R,
     'int i = 0; int c = 0;\nwhile (i < n && c < 100) { i++; c++; }\nreturn c;',
     pre=lambda n: 0 <= n <= 4, post=lambda n, r: r == n, domain=[(n,) for n in range(-1, 7)])
case('b_u8_wrap_loop', [('uint8_t', 'n')], 'int',
     'cppverify::pre(n <= 4)\ncppverify::post(%s == n)' % R,
     'int c = 0;\nfor (uint8_t i = n; i != 0; i--) { c++; }\nreturn c;',
     pre=lambda n: n <= 4, post=lambda n, r: r == n)
case('b_dec_unsigned', [('unsigned', 'n')], 'int',
     'cppverify::pre(n <= 4)\ncppverify::post(%s == n)' % R,
     'int c = 0;\nfor (unsigned i = n; i > 0; --i) { c++; }\nreturn c;',
     pre=lambda n: n <= 4, post=lambda n, r: r == n, domain=[(n,) for n in range(0, 10)] + [(2**32 - 1,)], alarm_ms=60000)
case('b_last_iter_ub', [('int', 'n')], 'int',
     'cppverify::pre(n >= 1 && n <= 5)\ncppverify::post(true)',
     'int r = 0;\nfor (int i = 0; i < n; i++) { r = 100 / (4 - i); }\nreturn r;',
     pre=lambda n: 1 <= n <= 5, post=lambda n, r: True, domain=[(n,) for n in range(-1, 8)])
case('b_last_iter_ub_ok', [('int', 'n')], 'int',
     'cppverify::pre(n >= 1 && n <= 4)\ncppverify::post(true)',
     'int r = 0;\nfor (int i = 0; i < n; i++) { r = 100 / (4 - i); }\nreturn r;',
     pre=lambda n: 1 <= n <= 4, post=lambda n, r: True, domain=[(n,) for n in range(-1, 8)])

CASES = C
CONFIGS = ('bmc6', 'bmc10', 'bmc6bv')
