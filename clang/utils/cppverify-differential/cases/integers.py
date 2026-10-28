"""Integer promotions, small types, conversions, shifts, division."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

# --- promotions of small types -------------------------------------------
case('u16mul', [('uint16_t', 'a'), ('uint16_t', 'b')], 'int',
     'cppverify::post(%s == a * b)' % R, 'return a * b;',
     post=lambda a, b, r: r == a * b)
case('u16mul_u', [('uint16_t', 'a'), ('uint16_t', 'b')], 'unsigned',
     'cppverify::post(%s == (a * b) %% 4294967296)' % R, 'return a * b;',
     post=lambda a, b, r: r == (a * b) % 2**32)
case('u16mul_compound', [('uint16_t', 'a')], 'uint16_t',
     'cppverify::post(%s == (a * a) %% 65536)' % R, 'a *= a; return a;',
     post=lambda a, r: r == (a * a) % 65536)
case('u16mul_guard', [('uint16_t', 'a'), ('uint16_t', 'b')], 'int',
     'cppverify::pre(a <= 46340 && b <= 46340)\ncppverify::post(%s == a * b)' % R, 'return a * b;',
     pre=lambda a, b: a <= 46340 and b <= 46340, post=lambda a, b, r: r == a * b)
case('u8add', [('uint8_t', 'a'), ('uint8_t', 'b')], 'int',
     'cppverify::post(%s == a + b)' % R, 'return a + b;',
     post=lambda a, b, r: r == a + b)
case('u8sub_int', [('uint8_t', 'a'), ('uint8_t', 'b')], 'int',
     'cppverify::post(%s == a - b)' % R, 'return a - b;',
     post=lambda a, b, r: r == a - b)
case('u8sub_u8', [('uint8_t', 'a'), ('uint8_t', 'b')], 'uint8_t',
     'cppverify::post(%s == (a - b + 256) %% 256)' % R, 'return a - b;',
     post=lambda a, b, r: r == (a - b) % 256)
case('u8sub_unsigned', [('uint8_t', 'a'), ('uint8_t', 'b')], 'unsigned',
     'cppverify::post(a >= b ? %s == a - b : %s == 4294967296 + a - b)' % (R, R), 'return a - b;',
     post=lambda a, b, r: r == (a - b) % 2**32)
case('i8neg', [('int8_t', 'x')], 'int8_t',
     'cppverify::post(x == -128 ? %s == -128 : %s == -x)' % (R, R), 'return -x;',
     post=lambda x, r: r == wrap(-x, 'int8_t'))
case('i8neg_int', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == -x)' % R, 'return -x;',
     post=lambda x, r: r == -x)
case('i8_compound_add', [('int8_t', 'x'), ('int8_t', 'y')], 'int8_t',
     'cppverify::post(%s == ((x + y + 384) %% 256) - 128)' % R, 'x += y; return x;',
     post=lambda x, y, r: r == wrap(x + y, 'int8_t'))
case('i8_inc', [('int8_t', 'x')], 'int8_t',
     'cppverify::post(x == 127 ? %s == -128 : %s == x + 1)' % (R, R), 'x++; return x;',
     post=lambda x, r: r == wrap(x + 1, 'int8_t'))
case('i8_postinc_val', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == x + (x == 127 ? -128 : x + 1))' % R, 'int8_t y = x++; return y + x;',
     post=lambda x, r: r == x + wrap(x + 1, 'int8_t'))
case('u8_dec', [('uint8_t', 'x')], 'uint8_t',
     'cppverify::post(x == 0 ? %s == 255 : %s == x - 1)' % (R, R), '--x; return x;',
     post=lambda x, r: r == (x - 1) % 256)
case('i16_mul_compound', [('int16_t', 'x')], 'int16_t',
     'cppverify::post(%s == ((x * x + 32768) %% 65536) - 32768)' % R, 'x *= x; return x;',
     post=lambda x, r: r == wrap(x * x, 'int16_t'))
case('i16_cube', [('int16_t', 'x')], 'int',
     'cppverify::post(%s == x * x * x)' % R, 'return x * x * x;',
     post=lambda x, r: r == x ** 3)
case('i8_pow4', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == x * x * x * x)' % R, 'return x * x * x * x;',
     post=lambda x, r: r == x ** 4)
case('u8_mul_back', [('uint8_t', 'a'), ('uint8_t', 'b')], 'uint8_t',
     'cppverify::post(%s == (a * b) %% 256)' % R, 'uint8_t c = a * b; return c;',
     post=lambda a, b, r: r == (a * b) % 256)

# --- char signedness and narrowing ----------------------------------------
case('char_sign', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x <= 255)\ncppverify::post(x >= 128 ? %s == x - 256 : %s == x)' % (R, R),
     'char c = x; return c;', pre=lambda x: 0 <= x <= 255, post=lambda x, r: r == wrap(x, 'int8_t'),
     domain=[(x,) for x in range(-5, 300)])
case('char_lt0', [('char', 'c')], 'bool',
     'cppverify::post(%s == (c < 0))' % R, 'return c < 0;',
     post=lambda c, r: r == (1 if c < 0 else 0))
case('uchar_from_int', [('int', 'x')], 'unsigned char',
     'cppverify::post(%s == ((x %% 256) + 256) %% 256)' % R, 'return x;',
     post=lambda x, r: r == x % 256)
case('schar_from_uint', [('unsigned', 'x')], 'signed char',
     'cppverify::post(%s == ((x + 128) %% 256) - 128)' % R, 'return x;',
     post=lambda x, r: r == wrap(x, 'int8_t'))
case('int_from_long', [('long', 'x')], 'int',
     'cppverify::post(%s == ((x %% 4294967296 + 4294967296 + 2147483648) %% 4294967296) - 2147483648)' % R,
     'return x;', post=lambda x, r: r == wrap(x, 'int'))
case('uint_from_long', [('long', 'x')], 'unsigned',
     'cppverify::post(%s == (x %% 4294967296 + 4294967296) %% 4294967296)' % R,
     'return x;', post=lambda x, r: r == x % 2**32)
case('long_from_ulong', [('unsigned long', 'x')], 'long',
     'cppverify::post(x > 9223372036854775807 ? %s == x - 18446744073709551615 - 1 : %s == x)' % (R, R),
     'return x;', post=lambda x, r: r == wrap(x, 'long'))
case('i8_to_u8_to_int', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == (x < 0 ? x + 256 : x))' % R, 'return (uint8_t)x;',
     post=lambda x, r: r == x % 256)
case('u8_to_i8_to_int', [('uint8_t', 'x')], 'int',
     'cppverify::post(%s == (x > 127 ? x - 256 : x))' % R, 'return (int8_t)x;',
     post=lambda x, r: r == wrap(x, 'int8_t'))
case('u16_to_short', [('uint16_t', 'x')], 'int',
     'cppverify::post(%s == (x > 32767 ? x - 65536 : x))' % R, 'short s = x; return s;',
     post=lambda x, r: r == wrap(x, 'int16_t'))

# --- bool conversions ---------------------------------------------------------
case('bool_from_int', [('int', 'x')], 'bool',
     'cppverify::post(%s == (x != 0))' % R, 'return x;',
     post=lambda x, r: r == (1 if x != 0 else 0))
case('bool_from_u8', [('uint8_t', 'x')], 'int',
     'cppverify::post(%s == (x != 0 ? 1 : 0))' % R, 'bool b = x; return b;',
     post=lambda x, r: r == (1 if x != 0 else 0))
case('bool_from_long_even', [('long', 'x')], 'int',
     'cppverify::post(%s == (x != 0 ? 1 : 0))' % R, 'bool b = (bool)x; return b + 0;',
     post=lambda x, r: r == (1 if x != 0 else 0))
case('bool_arith', [('bool', 'a'), ('bool', 'b')], 'int',
     'cppverify::post(%s == a + b + a)' % R, 'return a + b + a;',
     post=lambda a, b, r: r == 2 * a + b)
case('bool_compound_sub', [('bool', 'a')], 'bool',
     'cppverify::post(%s == true)' % R, 'a -= 1; a -= 1; return a;',
     post=lambda a, r: r == 1)
case('bool_compound_add', [('bool', 'a'), ('int', 'k')], 'bool',
     'cppverify::post(%s == (a + k != 0))' % R, 'a += k; return a;',
     post=lambda a, k, r: r == (1 if a + k != 0 else 0))
case('bool_neg', [('bool', 'a')], 'int',
     'cppverify::post(%s == -a)' % R, 'return -a;', post=lambda a, r: r == -a)
case('bool_not_int', [('int', 'x')], 'int',
     'cppverify::post(%s == (x == 0 ? 1 : 0))' % R, 'return !x;', post=lambda x, r: r == (1 if x == 0 else 0))
case('bool_bitnot', [('bool', 'a')], 'int',
     'cppverify::post(%s == -1 - a)' % R, 'return ~a;', post=lambda a, r: r == -1 - a)

# --- mixed signed/unsigned -------------------------------------------------
case('mixed_lt', [('int', 'x'), ('unsigned', 'u')], 'bool',
     'cppverify::post(%s == ((x < 0 ? x + 4294967296 : x) < u))' % R, 'return x < u;',
     post=lambda x, u, r: r == (1 if (x % 2**32) < u else 0))
case('mixed_lt_long_uint', [('long', 'x'), ('unsigned', 'u')], 'bool',
     'cppverify::post(%s == (x < u))' % R, 'return x < u;',
     post=lambda x, u, r: r == (1 if x < u else 0))
case('mixed_lt_ll_ul', [('long long', 'x'), ('unsigned long', 'u')], 'bool',
     'cppverify::post(%s == ((x < 0 ? x + 18446744073709551615 + 1 : x) < u))' % R, 'return x < u;',
     post=lambda x, u, r: r == (1 if (x % 2**64) < u else 0))
case('mixed_add_long', [('int', 'x'), ('unsigned', 'u')], 'long',
     'cppverify::post(%s == (x + u + 4294967296) %% 4294967296)' % R, 'long l = x + u; return l;',
     post=lambda x, u, r: r == (x + u) % 2**32)
case('mixed_eq_neg1', [('unsigned', 'u')], 'bool',
     'cppverify::post(%s == (u == 4294967295))' % R, 'return u == -1;',
     post=lambda u, r: r == (1 if u == 2**32 - 1 else 0))
case('mixed_u8_vs_i8', [('uint8_t', 'a'), ('int8_t', 'b')], 'bool',
     'cppverify::post(%s == (a < b))' % R, 'return a < b;',
     post=lambda a, b, r: r == (1 if a < b else 0))
case('mixed_u32_vs_i8', [('unsigned', 'a'), ('int8_t', 'b')], 'bool',
     'cppverify::post(%s == (a < (b < 0 ? b + 4294967296 : b)))' % R, 'return a < b;',
     post=lambda a, b, r: r == (1 if a < b % 2**32 else 0))
case('int_plus_1u', [('int', 'x')], 'int',
     'cppverify::post(x == 2147483647 ? %s == -2147483647 - 1 : %s == x + 1)' % (R, R), 'x += 1u; return x;',
     post=lambda x, r: r == wrap(x + 1, 'int'))
case('int_times_2u', [('int', 'x')], 'int',
     'cppverify::post(%s == ((2 * x %% 4294967296 + 4294967296 + 2147483648) %% 4294967296) - 2147483648)' % R,
     'x = x * 2u; return x;', post=lambda x, r: r == wrap(2 * x, 'int'))
case('long_plus_1u', [('long', 'x')], 'long',
     'cppverify::post(%s == x + 1)' % R, 'x += 1u; return x;', post=lambda x, r: r == x + 1)
case('ternary_mixed', [('bool', 'c')], 'long',
     'cppverify::post(c ? %s == 4294967295 : %s == 0)' % (R, R), 'return c ? -1 : 0u;',
     post=lambda c, r: r == (2**32 - 1 if c else 0))
case('ternary_small', [('bool', 'c'), ('int8_t', 'a'), ('uint8_t', 'b')], 'int',
     'cppverify::post(%s == (c ? a : b))' % R, 'return c ? a : b;',
     post=lambda c, a, b, r: r == (a if c else b), domain=[(c, a, b) for c in (0, 1) for a in range(-128, 128, 3) for b in range(0, 256, 3)])
case('ternary_int_uint', [('bool', 'c'), ('int', 'a'), ('unsigned', 'b')], 'long',
     'cppverify::post(%s == (c ? (a < 0 ? a + 4294967296 : a) : b))' % R, 'return c ? a : b;',
     post=lambda c, a, b, r: r == (a % 2**32 if c else b))
case('ternary_long_uint', [('bool', 'c'), ('long', 'a'), ('unsigned', 'b')], 'long',
     'cppverify::post(%s == (c ? a : b))' % R, 'return c ? a : b;',
     post=lambda c, a, b, r: r == (a if c else b))

# --- unary on unsigned -----------------------------------------------------
case('neg_unsigned', [('unsigned', 'u')], 'unsigned',
     'cppverify::post(%s == (4294967296 - u) %% 4294967296)' % R, 'return -u;',
     post=lambda u, r: r == (-u) % 2**32)
case('neg_u8', [('uint8_t', 'u')], 'int',
     'cppverify::post(%s == -u)' % R, 'return -u;', post=lambda u, r: r == -u)
case('bitnot_u8', [('uint8_t', 'u')], 'int',
     'cppverify::post(%s == -1 - u)' % R, 'return ~u;', post=lambda u, r: r == -1 - u)
case('bitnot_u8_back', [('uint8_t', 'u')], 'uint8_t',
     'cppverify::post(%s == 255 - u)' % R, 'return ~u;', post=lambda u, r: r == 255 - u)
case('bitnot_u16_cmp', [('uint16_t', 'u')], 'bool',
     'cppverify::post(%s == false)' % R, 'return ~u == 65535 - u;',
     post=lambda u, r: r == 0)
case('neg_ulong', [('unsigned long', 'u')], 'unsigned long',
     'cppverify::post(%s == (u == 0 ? 0 : 18446744073709551615 - u + 1))' % R, 'return -u;',
     post=lambda u, r: r == (-u) % 2**64)

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
