"""_BitInt(N) (no integer promotion; rank by width)."""
import differential as diff
from differential import *  # noqa: F401,F403

for n in (2, 3, 7, 13, 31, 33, 63, 65, 127):
    diff.TYPES['_BitInt(%d)' % n] = (n, True)
for n in (1, 3, 7, 13, 31, 33, 63, 65, 127):
    diff.TYPES['unsigned _BitInt(%d)' % n] = (n, False)

def wrap_n(v, n):
    v &= (1 << n) - 1
    return v - (1 << n) if v >= 1 << (n - 1) else v

def boundary_n(n):
    lo, hi = -(1 << (n - 1)), (1 << (n - 1)) - 1
    return sorted(set(v for v in [lo, lo + 1, -1, 0, 1, 2, hi - 1, hi, -5, 5] if lo <= v <= hi))


R = 'cppverify::result'
C = []

def case(*a, **k):
    k.setdefault('vflags', ['--extra-arg=-Wno-bit-int-extension'])
    C.append(Case(*a, **k))

def M(n):
    # 2^63 and above have no C++ literal.
    return '%d' % (1 << n) if n < 63 else '((__int128)1 << %d)' % n

for n in (3, 7, 13, 33, 65):
    u = 'unsigned _BitInt(%d)' % n
    s = '_BitInt(%d)' % n
    ret = '__int128'
    case('bi_uadd_%d' % n, [(u, 'a'), (u, 'b')], ret,
         'cppverify::post(%s == (a + b) %% %s)' % (R, M(n)), 'return a + b;',
         post=lambda a, b, r, n=n: r == (a + b) % (1 << n))
    case('bi_umul_%d' % n, [(u, 'a'), (u, 'b')], ret,
         'cppverify::post(%s == (a * b) %% %s)' % (R, M(n)), 'return a * b;',
         post=lambda a, b, r, n=n: r == (a * b) % (1 << n))
    case('bi_usub_%d' % n, [(u, 'a'), (u, 'b')], ret,
         'cppverify::post(%s == (a - b + %s) %% %s)' % (R, M(n), M(n)), 'return a - b;',
         post=lambda a, b, r, n=n: r == (a - b) % (1 << n))
    case('bi_sadd_%d' % n, [(s, 'a'), (s, 'b')], ret,
         'cppverify::post(%s == a + b)' % R, 'return a + b;',
         post=lambda a, b, r: r == a + b)
    case('bi_sadd_guard_%d' % n, [(s, 'a'), (s, 'b')], ret,
         'cppverify::pre(a + b >= -%s && a + b < %s)\ncppverify::post(%s == a + b)' % (M(n - 1), M(n - 1), R), 'return a + b;',
         pre=lambda a, b, n=n: -(1 << (n - 1)) <= a + b < (1 << (n - 1)), post=lambda a, b, r: r == a + b)
    case('bi_sdiv_%d' % n, [(s, 'a'), (s, 'b')], ret,
         'cppverify::pre(b != 0)\ncppverify::post(%s == a / b)' % R, 'return a / b;',
         pre=lambda a, b: b != 0, post=lambda a, b, r: r == tdiv(a, b))
    case('bi_srem_%d' % n, [(s, 'a'), (s, 'b')], ret,
         'cppverify::pre(b != 0 && !(a == -%s && b == -1))\ncppverify::post(%s == a %% b)' % (M(n - 1), R), 'return a % b;',
         pre=lambda a, b, n=n: b != 0 and not (a == -(1 << (n - 1)) and b == -1), post=lambda a, b, r: r == tmod(a, b))
    case('bi_sneg_%d' % n, [(s, 'a')], ret,
         'cppverify::post(%s == -a)' % R, 'return -a;', post=lambda a, r: r == -a)
    case('bi_conv_from_long_%d' % n, [('long', 'x')], ret,
         'cppverify::post(%s >= -%s && %s < %s)' % (R, M(n - 1), R, M(n - 1)), 'return (%s)x;' % s,
         post=lambda x, r, n=n: -(1 << (n - 1)) <= r < (1 << (n - 1)))
    case('bi_conv_val_%d' % n, [('long', 'x')], ret,
         'cppverify::post(%s == ((x %% %s) + %s + %s) %% %s - %s)' % (R, M(n), M(n), M(n - 1), M(n), M(n - 1)), 'return (%s)x;' % s,
         post=lambda x, r, n=n: r == wrap_n(x, n))
    case('bi_mix_int_%d' % n, [(s, 'a'), ('int', 'b')], ret,
         'cppverify::pre(b > -1000 && b < 1000)\ncppverify::post(%s == a + b || true)' % R, 'return a + b;',
         pre=lambda a, b: -1000 < b < 1000, post=lambda a, b, r: True)
    case('bi_inc_%d' % n, [(s, 'a')], ret,
         'cppverify::post(true)', 'a++; return a;', post=lambda a, r: True)
    case('bi_cmp_us_%d' % n, [(u, 'a'), (s, 'b')], 'bool',
         'cppverify::post(%s == (a < (b < 0 ? b + %s : b)))' % (R, M(n)), 'return a < b;',
         post=lambda a, b, r, n=n: r == (1 if a < b % (1 << n) else 0))
    case('bi_shl_%d' % n, [(s, 'a'), ('int', 'k')], ret,
         'cppverify::pre(k >= 0 && k < %d && a >= 0 && a < 2)\ncppverify::post(%s == (k == %d ? -%s : a * (((__int128)1) << k)) || a == 0)' % (n, R, n - 1, M(n - 1)),
         'return a << k;', pre=lambda a, k, n=n: 0 <= k < n and 0 <= a < 2,
         post=lambda a, k, r, n=n: a == 0 or r == (-(1 << (n - 1)) if k == n - 1 else a << k),
         domain=[(a, k) for a in (-1, 0, 1) for k in range(-1, n + 2)])
    case('bi_shr_%d' % n, [(s, 'a'), ('int', 'k')], ret,
         'cppverify::pre(k >= 0 && k < %d)\ncppverify::post(%s * (((__int128)1) << k) <= a && a < (%s + 1) * (((__int128)1) << k))' % (n, R, R),
         'return a >> k;', pre=lambda a, k, n=n: 0 <= k < n,
         post=lambda a, k, r: r * 2**k <= a < (r + 1) * 2**k,
         domain=[(a, k) for a in boundary_n(n) for k in range(-1, n + 2)])

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
