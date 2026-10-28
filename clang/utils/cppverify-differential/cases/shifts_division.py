"""Shifts, division/modulo, __int128, enums, character types."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

def shdom(xt, lo=-3, hi=40):
    xs = boundary(xt) + list(range(-20, 21))
    xs = sorted(set(v for v in xs if in_range(v, xt)))
    return [(x, s) for x in xs for s in range(lo, hi)]

W32 = '((%s) + 2147483648) %% 4294967296 - 2147483648'

# --- left shifts -----------------------------------------------------------
for std in ('c++17', 'c++20'):
    sfx = std[-2:]
    case('shl_any_' + sfx, [('int', 'x'), ('int', 's')], 'int',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s == %s)' % (R, W32 % ('x * (1L << s) % 4294967296 + 4294967296')),
         'return x << s;', pre=lambda x, s: 0 <= s < 32,
         post=lambda x, s, r: r == wrap(x << s, 'int'), std=std, domain=shdom('int'))
    case('shl_u8_' + sfx, [('uint8_t', 'a'), ('int', 's')], 'int',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s == %s)' % (R, W32 % ('a * (1L << s) % 4294967296')),
         'return a << s;', pre=lambda a, s: 0 <= s < 32,
         post=lambda a, s, r: r == wrap(a << s, 'int'), std=std,
         domain=[(a, s) for a in range(256) for s in range(-2, 34)])
    case('shl_i8_' + sfx, [('int8_t', 'a'), ('int', 's')], 'int',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s == %s)' % (R, W32 % ('a * (1L << s) % 4294967296 + 4294967296')),
         'return a << s;', pre=lambda a, s: 0 <= s < 32,
         post=lambda a, s, r: r == wrap(a << s, 'int'), std=std,
         domain=[(a, s) for a in range(-128, 128) for s in range(-2, 34)])
    case('shl_assign_i8_' + sfx, [('int8_t', 'a'), ('int', 's')], 'int8_t',
         'cppverify::pre(0 <= s && s < 8)\ncppverify::post(%s == (a * (1 << s) %% 256 + 384) %% 256 - 128)' % R,
         'a <<= s; return a;', pre=lambda a, s: 0 <= s < 8,
         post=lambda a, s, r: r == wrap(a << s, 'int8_t'), std=std,
         domain=[(a, s) for a in range(-128, 128) for s in range(-2, 12)])
    case('shl_long_' + sfx, [('long', 'x'), ('int', 's')], 'long',
         'cppverify::pre(0 <= s && s < 64 && x >= 0 && x <= (9223372036854775807L >> s))\ncppverify::post(%s >= x)' % R,
         'return x << s;', pre=lambda x, s: 0 <= s < 64 and 0 <= x <= ((2**63 - 1) >> s),
         post=lambda x, s, r: r >= x, std=std, domain=shdom('long', -2, 70))
    case('shr_neg_' + sfx, [('int', 'x'), ('int', 's')], 'int',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s * (1L << s) <= x && x < (%s + 1) * (1L << s))' % (R, R),
         'return x >> s;', pre=lambda x, s: 0 <= s < 32,
         post=lambda x, s, r: r * 2**s <= x < (r + 1) * 2**s, std=std, domain=shdom('int'))
    case('shr_i8_' + sfx, [('int8_t', 'x'), ('int', 's')], 'int8_t',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s * (1L << s) <= x && x < (%s + 1) * (1L << s))' % (R, R),
         'x >>= s; return x;', pre=lambda x, s: 0 <= s < 32,
         post=lambda x, s, r: r * 2**s <= x < (r + 1) * 2**s, std=std,
         domain=[(a, s) for a in range(-128, 128) for s in range(-2, 34)])
    case('shl_unsigned_' + sfx, [('unsigned', 'x'), ('unsigned', 's')], 'unsigned',
         'cppverify::pre(s < 32)\ncppverify::post(%s == x * (1L << s) %% 4294967296)' % R,
         'return x << s;', pre=lambda x, s: s < 32,
         post=lambda x, s, r: r == (x << s) % 2**32, std=std,
         domain=[(x, s) for x in boundary('unsigned') for s in range(0, 40)])
    case('shl_one31_' + sfx, [('int', 's')], 'int',
         'cppverify::pre(s >= 0 && s <= 31)\ncppverify::post(s == 31 ? %s == -2147483647 - 1 : %s == (1L << s))' % (R, R),
         'return 1 << s;', pre=lambda s: 0 <= s <= 31,
         post=lambda s, r: r == wrap(1 << s, 'int'), std=std, domain=[(s,) for s in range(-5, 40)])
    case('shl_two31_' + sfx, [('int', 's')], 'int',
         'cppverify::pre(s >= 0 && s <= 31)\ncppverify::post(true)',
         'return 2 << s;', pre=lambda s: 0 <= s <= 31,
         post=lambda s, r: True, std=std, domain=[(s,) for s in range(-5, 40)])
    case('shl_amount_u8_' + sfx, [('int', 'x'), ('uint8_t', 's')], 'int',
         'cppverify::pre(x >= 0 && x <= 1 && s <= 30)\ncppverify::post(%s == x * (1L << s))' % R,
         'return x << s;', pre=lambda x, s: 0 <= x <= 1 and s <= 30,
         post=lambda x, s, r: r == x * 2**s, std=std, domain=[(x, s) for x in range(-2, 4) for s in range(256)])
    case('shl_amount_long_' + sfx, [('int', 'x'), ('long', 's')], 'int',
         'cppverify::pre(x == 1 && s >= 0 && s <= 30)\ncppverify::post(%s == (1L << s))' % R,
         'return x << s;', pre=lambda x, s: x == 1 and 0 <= s <= 30,
         post=lambda x, s, r: r == 2**s, std=std,
         domain=[(x, s) for x in range(-2, 4) for s in list(range(-3, 70)) + [2**32, 2**32 + 1, -2**63, 2**63 - 1]])
    case('shl_large_amount_' + sfx, [('int', 'x'), ('int', 's')], 'int',
         'cppverify::pre(x == 0 && s >= 0 && s < 40)\ncppverify::post(%s == 0)' % R,
         'return x << s;', pre=lambda x, s: x == 0 and 0 <= s < 40,
         post=lambda x, s, r: r == 0, std=std, domain=[(x, s) for x in (0, 1) for s in range(-3, 45)])
    case('shr_large_amount_' + sfx, [('unsigned', 'x'), ('int', 's')], 'unsigned',
         'cppverify::pre(s >= 0 && s <= 32)\ncppverify::post(%s <= x)' % R,
         'return x >> s;', pre=lambda x, s: 0 <= s <= 32,
         post=lambda x, s, r: r <= x, std=std, domain=[(x, s) for x in boundary('unsigned') for s in range(-3, 40)])
    case('shl_u64_' + sfx, [('uint64_t', 'x'), ('int', 's')], 'uint64_t',
         'cppverify::pre(s >= 0 && s < 64)\ncppverify::post(%s == x * (1UL << s) %% 18446744073709551615 + 0 || true)' % R,
         'return x << s;', pre=lambda x, s: 0 <= s < 64,
         post=lambda x, s, r: True, std=std, domain=[(x, s) for x in boundary('uint64_t') for s in range(-2, 70)])
    case('shl_u16_assign_' + sfx, [('uint16_t', 'a'), ('int', 's')], 'uint16_t',
         'cppverify::pre(0 <= s && s < 32)\ncppverify::post(%s == a * (1L << s) %% 65536)' % R,
         'a <<= s; return a;', pre=lambda a, s: 0 <= s < 32,
         post=lambda a, s, r: r == (a << s) % 65536, std=std,
         domain=[(a, s) for a in list(range(0, 300)) + list(range(32700, 32800)) + list(range(65000, 65536)) for s in range(-2, 34)])

# --- division / modulo -----------------------------------------------------
case('div_int', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x / y)' % R, 'return x / y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tdiv(x, y))
case('rem_int', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x %% y)' % R, 'return x % y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tmod(x, y))
case('rem_int_noguard_minus1', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::pre(y != 0 && x != -2147483647 - 1)\ncppverify::post(%s == x - (x / y) * y)' % R, 'return x % y;',
     pre=lambda x, y: y != 0 and x != -2**31, post=lambda x, y, r: r == x - tdiv(x, y) * y)
case('rem_long', [('long', 'x'), ('long', 'y')], 'long',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x %% y)' % R, 'return x % y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tmod(x, y))
case('div_i8', [('int8_t', 'x'), ('int8_t', 'y')], 'int',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x / y)' % R, 'return x / y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tdiv(x, y))
case('rem_i8', [('int8_t', 'x'), ('int8_t', 'y')], 'int8_t',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x %% y)' % R, 'return x % y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tmod(x, y))
case('div_i8_ret8', [('int8_t', 'x'), ('int8_t', 'y')], 'int8_t',
     'cppverify::pre(y != 0)\ncppverify::post(x == -128 && y == -1 ? %s == -128 : %s == x / y)' % (R, R),
     'return x / y;', pre=lambda x, y: y != 0, post=lambda x, y, r: r == wrap(tdiv(x, y), 'int8_t'))
case('div_assign_i8', [('int8_t', 'x'), ('int8_t', 'y')], 'int8_t',
     'cppverify::pre(y != 0)\ncppverify::post(x == -128 && y == -1 ? %s == -128 : %s == x / y)' % (R, R),
     'x /= y; return x;', pre=lambda x, y: y != 0, post=lambda x, y, r: r == wrap(tdiv(x, y), 'int8_t'))
case('rem_assign_i16', [('int16_t', 'x'), ('int16_t', 'y')], 'int16_t',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x %% y)' % R,
     'x %= y; return x;', pre=lambda x, y: y != 0, post=lambda x, y, r: r == tmod(x, y))
case('div_mixed', [('int', 'a'), ('unsigned', 'b')], 'unsigned',
     'cppverify::pre(b != 0)\ncppverify::post(%s == (a < 0 ? a + 4294967296 : a) / b)' % R, 'return a / b;',
     pre=lambda a, b: b != 0, post=lambda a, b, r: r == (a % 2**32) // b)
case('rem_mixed', [('int', 'a'), ('unsigned', 'b')], 'unsigned',
     'cppverify::pre(b != 0)\ncppverify::post(%s == (a < 0 ? a + 4294967296 : a) %% b)' % R, 'return a % b;',
     pre=lambda a, b: b != 0, post=lambda a, b, r: r == (a % 2**32) % b)
case('div_int_by_long', [('int', 'x'), ('long', 'y')], 'long',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x / y)' % R, 'return x / y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tdiv(x, y))
case('div_long', [('long', 'x'), ('long', 'y')], 'long',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x / y)' % R, 'return x / y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tdiv(x, y))
case('urem_neg3', [('unsigned', 'u')], 'unsigned',
     'cppverify::post(%s == u %% 4294967293)' % R, 'return u % -3;',
     post=lambda u, r: r == u % 4294967293)
case('div_u16', [('uint16_t', 'a'), ('uint16_t', 'b')], 'int',
     'cppverify::pre(b != 0)\ncppverify::post(%s == a / b)' % R, 'return a / b;',
     pre=lambda a, b: b != 0, post=lambda a, b, r: r == a // b)
case('div_short_circuit', [('int', 'x'), ('int', 'y')], 'bool',
     'cppverify::post(%s == (y != 0 && y != -1 && x / y > 1))' % R, 'return y != 0 && y != -1 && x / y > 1;',
     post=lambda x, y, r: r == (1 if (y != 0 and y != -1 and tdiv(x, y) > 1) else 0))
case('div_short_circuit_bad', [('int', 'x'), ('int', 'y')], 'bool',
     'cppverify::post(true)', 'return y != 0 && x / y > 1;',
     post=lambda x, y, r: True)
case('rem_ternary_guard', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::post(true)', 'return (y == 0 || y == -1) ? 0 : x % y;',
     post=lambda x, y, r: True)
case('rem_or_guard', [('int', 'x'), ('int', 'y')], 'bool',
     'cppverify::post(true)', 'return y == 0 || x % y == 0;',
     post=lambda x, y, r: True)
case('div_by_constant_neg', [('int', 'x')], 'int',
     'cppverify::post(%s == x / -7)' % R, 'return x / -7;',
     post=lambda x, r: r == tdiv(x, -7))
case('rem_by_constant_neg', [('int', 'x')], 'int',
     'cppverify::post(%s == x %% -7)' % R, 'return x % -7;',
     post=lambda x, r: r == tmod(x, -7))

# --- __int128 --------------------------------------------------------------
case('i128_mul64', [('long', 'a'), ('long', 'b')], '__int128',
     'cppverify::post(%s == a * b)' % R, 'return (__int128)a * b;',
     post=lambda a, b, r: r == a * b)
case('i128_add', [('__int128', 'a'), ('__int128', 'b')], '__int128',
     'cppverify::post(%s == a + b)' % R, 'return a + b;',
     post=lambda a, b, r: r == a + b)
case('u128_add', [('unsigned __int128', 'a'), ('unsigned __int128', 'b')], 'unsigned __int128',
     'cppverify::post(%s == (a + b) %% (((unsigned __int128)1) << 127) || true)' % R, 'return a + b;',
     post=lambda a, b, r: True)
case('i128_hi', [('__int128', 'x')], 'long',
     'cppverify::post(true)', 'return (long)(x >> 64);',
     post=lambda x, r: r == x >> 64)
case('i128_hi_eq', [('__int128', 'x')], 'long',
     'cppverify::post(%s * 18446744073709551615 + %s <= x)' % (R, R), 'return (long)(x >> 64);',
     post=lambda x, r: r * 2**64 <= x)
case('i128_to_long', [('__int128', 'x')], 'long',
     'cppverify::pre(x >= 0 && x < 18446744073709551615)\ncppverify::post(x > 9223372036854775807 ? %s < 0 : %s == x)' % (R, R),
     'return (long)x;', pre=lambda x: 0 <= x < 2**64 - 1,
     post=lambda x, r: r < 0 if x > 2**63 - 1 else r == x)
case('i128_div', [('__int128', 'x'), ('__int128', 'y')], '__int128',
     'cppverify::pre(y != 0)\ncppverify::post(%s == x / y)' % R, 'return x / y;',
     pre=lambda x, y: y != 0, post=lambda x, y, r: r == tdiv(x, y))
case('i128_shl', [('__int128', 'x'), ('int', 's')], '__int128',
     'cppverify::pre(s >= 0 && s < 128 && x >= 0 && x < 2)\ncppverify::post(%s >= 0 || s == 127)' % R,
     'return x << s;', pre=lambda x, s: 0 <= s < 128 and 0 <= x < 2,
     post=lambda x, s, r: r >= 0 or s == 127, domain=[(x, s) for x in (-1, 0, 1, 2) for s in range(-2, 132)])

# --- enums -----------------------------------------------------------------
case('enum_range', [('int', 'v')], 'int',
     'cppverify::pre(v >= 0 && v <= 3)\ncppverify::post(%s != 3)' % R, 'E e = (E)v; return e;',
     prelude='enum E { A, B, C };',
     pre=lambda v: 0 <= v <= 3, post=lambda v, r: r != 3, domain=[(v,) for v in range(-3, 10)])
case('enum_param', [('E', 'e')], 'int',
     'cppverify::post(%s <= 2)' % R, 'return e;',
     prelude='enum E { A, B, C };',
     post=lambda e, r: r <= 2, domain=[(v,) for v in range(0, 4)])
case('enum_param_neg', [('G', 'g')], 'int',
     'cppverify::post(%s >= -1)' % R, 'return g;',
     prelude='enum G { M = -1, N = 1 };',
     post=lambda g, r: r >= -1, domain=[(v,) for v in range(-2, 2)])
case('enum_fixed', [('F', 'f')], 'int',
     'cppverify::post(%s == 1 || %s == 2)' % (R, R), 'return (int)f;',
     prelude='enum class F : uint8_t { X = 1, Y = 2 };',
     post=lambda f, r: r in (1, 2), domain=[(v,) for v in range(0, 256)])
case('enum_from_int_oob', [('int', 'v')], 'int',
     'cppverify::post(true)', 'E e = (E)v; return e;',
     prelude='enum E { A, B, C };',
     post=lambda v, r: True, domain=[(v,) for v in range(-3, 10)])
case('enum_cmp', [('E', 'e')], 'bool',
     'cppverify::post(%s == (e == A || e == B || e == C))' % R, 'return e < 3;',
     prelude='enum E { A, B, C };',
     post=lambda e, r: r == (1 if e in (0, 1, 2) else 0), domain=[(v,) for v in range(0, 4)])

# --- character types ---------------------------------------------------------
case('char16_mul', [('char16_t', 'a'), ('char16_t', 'b')], 'int',
     'cppverify::post(%s == a * b)' % R, 'return a * b;', post=lambda a, b, r: r == a * b)
case('char32_add', [('char32_t', 'a')], 'unsigned',
     'cppverify::post(%s == (a + 1) %% 4294967296)' % R, 'return a + 1;', post=lambda a, r: r == (a + 1) % 2**32)
case('char32_add_int', [('char32_t', 'a')], 'long',
     'cppverify::post(%s == a + 1)' % R, 'return a + 1;', post=lambda a, r: r == a + 1)
case('wchar_add', [('wchar_t', 'a')], 'int',
     'cppverify::post(%s == a + 1)' % R, 'return a + 1;', post=lambda a, r: r == a + 1)
case('wchar_neg', [('wchar_t', 'a')], 'bool',
     'cppverify::post(%s == (a < 0))' % R, 'return a < 0;', post=lambda a, r: r == (1 if a < 0 else 0))

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
