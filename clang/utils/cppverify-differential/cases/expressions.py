"""Switch, literal types, assignment/comma expressions, bitwise identities."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

# --- integer literal types --------------------------------------------------
case('lit_hex_unsigned_cmp', [('int', 'x')], 'bool',
     'cppverify::post(%s == (x >= 0))' % R, 'return x < 0x80000000;',
     post=lambda x, r: r == (1 if x >= 0 else 0))
case('lit_hex_eq', [('int', 'x')], 'bool',
     'cppverify::post(%s == (x == -1))' % R, 'return x == 0xFFFFFFFF;',
     post=lambda x, r: r == (1 if x == -1 else 0))
case('lit_dec_long', [('int', 'x')], 'bool',
     'cppverify::post(%s == true)' % R, 'return x < 2147483648;',
     post=lambda x, r: r == 1)
case('lit_neg_long', [('int', 'x')], 'bool',
     'cppverify::post(%s == true)' % R, 'return x >= -2147483648;',
     post=lambda x, r: r == 1)
case('lit_hex_long', [('int', 'x')], 'long',
     'cppverify::post(%s == 4294967295)' % R, 'long l = 0xFFFFFFFF; return l + 0 * x;',
     post=lambda x, r: r == 4294967295)
case('lit_int_from_hex', [('int', 'x')], 'int',
     'cppverify::post(%s == -1)' % R, 'int v = 0xFFFFFFFF; return v + 0 * x;',
     post=lambda x, r: r == -1)
case('lit_char_xff', [('int', 'x')], 'int',
     'cppverify::post(%s == -1)' % R, "char c = '\\xff'; return c + 0 * x;",
     post=lambda x, r: r == -1)
case('lit_uchar_cmp', [('unsigned char', 'c')], 'bool',
     'cppverify::post(%s == false)' % R, "return c == '\\xff';",
     post=lambda c, r: r == 0)
case('lit_octal', [('int', 'x')], 'int',
     'cppverify::post(%s == 8)' % R, 'return 010 + 0 * x;', post=lambda x, r: r == 8)
case('lit_u_suffix_mix', [('int', 'x')], 'bool',
     'cppverify::post(%s == (x == 0))' % R, 'return x * 0 - 1 > 0u + (unsigned)x * 0 + 4294967294u - 4294967294u + (x != 0 ? 4294967295u : 0u);',
     post=lambda x, r: r == (1 if x == 0 else 0))
case('lit_sizeof', [('int', 'x')], 'bool',
     'cppverify::post(%s == false)' % R, 'return -1 < sizeof(int) + 0 * x;',
     post=lambda x, r: r == 0)
case('lit_ll_ul', [('long long', 'x')], 'bool',
     'cppverify::post(%s == (x >= 0))' % R, 'return x < 9223372036854775808ULL;',
     post=lambda x, r: r == (1 if x >= 0 else 0))

# --- switch ---------------------------------------------------------------------
case('sw_basic', [('int', 'x')], 'int',
     'cppverify::post(x == 1 ? %s == 10 : x == 2 ? %s == 20 : %s == 0)' % (R, R, R),
     'switch (x) { case 1: return 10; case 2: return 20; default: return 0; }',
     post=lambda x, r: r == (10 if x == 1 else 20 if x == 2 else 0))
case('sw_fallthrough', [('int', 'x')], 'int',
     'cppverify::post(x == 1 ? %s == 3 : x == 2 ? %s == 2 : %s == 0)' % (R, R, R),
     'int r = 0; switch (x) { case 1: r += 1; case 2: r += 2; break; default: r = 0; } return r;',
     post=lambda x, r: r == (3 if x == 1 else 2 if x == 2 else 0))
case('sw_u8_cond', [('uint8_t', 'c')], 'int',
     'cppverify::post(%s == (c == 255 ? 1 : 0))' % R,
     'switch (c) { case 255: return 1; case -1: return 2; default: return 0; }',
     post=lambda c, r: r == (1 if c == 255 else 0))
case('sw_char_cond', [('char', 'c')], 'int',
     'cppverify::post(%s == (c == -1 ? 2 : 0))' % R,
     "switch (c) { case 255: return 1; case -1: return 2; default: return 0; }",
     post=lambda c, r: r == (2 if c == -1 else 0))
case('sw_default_first', [('int', 'x')], 'int',
     'cppverify::post(x == 5 ? %s == 1 : %s == 2)' % (R, R),
     'int r = 0; switch (x) { default: r = 2; break; case 5: r = 1; } return r;',
     post=lambda x, r: r == (1 if x == 5 else 2))
case('sw_no_default', [('int', 'x')], 'int',
     'cppverify::post(x == 3 ? %s == 7 : %s == 9)' % (R, R),
     'int r = 9; switch (x) { case 3: r = 7; } return r;',
     post=lambda x, r: r == (7 if x == 3 else 9))
case('sw_long_cond', [('long', 'x')], 'int',
     'cppverify::post(%s == (x == 4294967296 ? 1 : 0))' % R,
     'switch (x) { case 4294967296L: return 1; case 0: return 0; default: return 0; }',
     post=lambda x, r: r == (1 if x == 2**32 else 0))

# --- assignment / comma expressions ----------------------------------------------
case('ex_chain_assign', [('int', 'x')], 'int',
     'cppverify::post(%s == 2 * ((x + 128) %% 256 - 128 + 256) %% 256 - 0 || true)' % R,
     'int8_t a; int b; b = a = x; return a + b;',
     post=lambda x, r: r == 2 * wrap(x, 'int8_t'))
case('ex_chain_assign_val', [('int', 'x')], 'int',
     'cppverify::post(%s == 2 * (((x %% 256) + 384) %% 256 - 128))' % R,
     'int8_t a; int b; b = a = x; return a + b;',
     post=lambda x, r: r == 2 * wrap(x, 'int8_t'))
case('ex_comma', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == x + 2)' % R,
     'int y = (x++, x + 1); return y;', pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == x + 2)
case('ex_assign_in_cond', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == (x + 1 > 0 ? x + 1 : -1))' % R,
     'int y; if ((y = x + 1) > 0) return y; return -1;', pre=lambda x: -1000 < x < 1000,
     post=lambda x, r: r == (x + 1 if x + 1 > 0 else -1))
case('ex_compound_value', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == 2 * x + 10)' % R,
     'int y = (x += 5); return x + y;', pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == 2 * x + 10)
case('ex_preinc_value', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == 2 * (x == 127 ? -128 : x + 1))' % R,
     'int y = ++x; return x + y;', post=lambda x, r: r == 2 * wrap(x + 1, 'int8_t'))
case('ex_short_circuit_side', [('int', 'x')], 'int',
     'cppverify::post(%s == (x > 0 ? 5 : 0))' % R,
     'int y = 0; if (x > 0 && (y = 5) > 0) { } return y;', post=lambda x, r: r == (5 if x > 0 else 0))
case('ex_or_side', [('int', 'x')], 'int',
     'cppverify::post(%s == (x > 0 ? 0 : 5))' % R,
     'int y = 0; if (x > 0 || (y = 5) > 0) { } return y;', post=lambda x, r: r == (0 if x > 0 else 5))
case('ex_ternary_lvalue', [('bool', 'c')], 'int',
     'cppverify::post(%s == (c ? 5 : 50))' % R,
     'int a = 0, b = 0; (c ? a : b) = 5; return a + 10 * b;', post=lambda c, r: r == (5 if c else 50))
case('ex_sub_assign_unsigned', [('unsigned', 'u')], 'unsigned',
     'cppverify::post(%s == (u + 1) %% 4294967296)' % R, 'u -= -1; return u;',
     post=lambda u, r: r == (u + 1) % 2**32)
case('ex_int_minus_assign_neg_unsigned', [('int', 'x')], 'int',
     'cppverify::post(x == 2147483647 ? %s == -2147483647 - 1 : %s == x + 1)' % (R, R), 'x -= -1u; return x;',
     post=lambda x, r: r == wrap(x + 1, 'int'))

# --- bitwise identities across mixed types -----------------------------------------
TYPEPAIRS = [('int8_t', 'int8_t'), ('uint8_t', 'int8_t'), ('int8_t', 'uint16_t'), ('int', 'unsigned'),
             ('long', 'unsigned'), ('unsigned long', 'int'), ('int16_t', 'unsigned'), ('char', 'bool')]
def ctype_of(ta, tb):
    """usual arithmetic conversions after promotion (LP64)."""
    def prom(t):
        b, s = TYPES[t]
        if b < 32:
            return 'int'
        return t
    pa, pb = prom(ta), prom(tb)
    rank = {'int': 1, 'unsigned': 1, 'long': 2, 'unsigned long': 2}
    canon = {'int': 'int', 'unsigned': 'unsigned', 'long': 'long', 'unsigned long': 'unsigned long', 'int32_t': 'int', 'uint32_t': 'unsigned', 'int64_t': 'long', 'uint64_t': 'unsigned long'}
    pa, pb = canon[pa], canon[pb]
    if pa == pb:
        return pa
    sa, sb = TYPES[pa][1], TYPES[pb][1]
    if sa == sb:
        return pa if rank[pa] > rank[pb] else pb
    u, s = (pa, pb) if not sa else (pb, pa)
    if rank[u] >= rank[s]:
        return u
    if TYPES[s][0] > TYPES[u][0]:
        return s
    return {'long': 'unsigned long'}[s]
for ta, tb in TYPEPAIRS:
    ct = ctype_of(ta, tb)
    nm = (ta + '_' + tb).replace(' ', '')
    case('bw_andor_' + nm, [(ta, 'a'), (tb, 'b')], 'long',
         'cppverify::post(%s + (a | b) == a + b || %s)' % (R, 'false'),
         'return a & b;', post=lambda a, b, r, ct=ct: r + wrap(wrap(a, ct) | wrap(b, ct), ct) == a + b)
    case('bw_xor_' + nm, [(ta, 'a'), (tb, 'b')], 'long',
         'cppverify::post(%s + 2 * (a & b) == (a | b) + (a & b))' % R,
         'return a ^ b;', post=lambda a, b, r, ct=ct: r + 2 * (wrap(a, ct) & wrap(b, ct)) == (wrap(a, ct) | wrap(b, ct)) + (wrap(a, ct) & wrap(b, ct)))
    case('bw_val_and_' + nm, [(ta, 'a'), (tb, 'b')], 'long',
         'cppverify::post(%s == (a & b))' % R,
         'return a & b;', post=lambda a, b, r, ct=ct: r == wrap(wrap(a, ct) & wrap(b, ct), ct))
    case('bw_val_or_' + nm, [(ta, 'a'), (tb, 'b')], 'long',
         'cppverify::post(%s == (a | b))' % R,
         'return a | b;', post=lambda a, b, r, ct=ct: r == wrap(wrap(a, ct) | wrap(b, ct), ct))
    case('bw_ret_xor_cmp_' + nm, [(ta, 'a'), (tb, 'b')], 'bool',
         'cppverify::post(%s == ((a ^ b) < 0))' % R,
         'return (a ^ b) < 0;', post=lambda a, b, r, ct=ct: r == (1 if wrap(wrap(a, ct) ^ wrap(b, ct), ct) < 0 else 0))
for t in ('int8_t', 'uint8_t', 'int16_t', 'uint16_t', 'int', 'unsigned', 'long', 'unsigned long', 'bool', 'char'):
    nm = t.replace(' ', '')
    pt = 'int' if TYPES[t][0] < 32 else t
    case('bw_not_' + nm, [(t, 'a')], 'long',
         'cppverify::post(%s == ~a)' % R, 'return ~a;',
         post=lambda a, r, pt=pt: r == wrap(~a, pt))
    case('bw_not_id_' + nm, [(t, 'a')], 'bool',
         'cppverify::post(%s == true)' % R, 'return (~a & a) == 0 && (~a | a) == ~0 * 0 + (%s)~(%s)0;' % (pt, pt),
         post=lambda a, r: r == 1)
    case('bw_shr_floor_' + nm, [(t, 'a'), ('int', 'k')], 'long',
         'cppverify::pre(k >= 0 && k < %d)\ncppverify::post(%s * (1L << k) <= a && a < (%s + 1) * (1L << k))' % (min(TYPES[pt][0], 63), R, R),
         'return a >> k;', pre=lambda a, k, pt=pt: 0 <= k < min(TYPES[pt][0], 63),
         post=lambda a, k, r: r * 2**k <= a < (r + 1) * 2**k,
         domain=[(a, k) for a in boundary(t) for k in range(-1, TYPES[pt][0] + 1)])
    case('bw_shr_mask_' + nm, [(t, 'a'), ('int', 'k')], 'bool',
         'cppverify::pre(k >= 0 && k < 31)\ncppverify::post(%s == true)' % R,
         'return (a >> k) * (1L << k) + (a & ((1L << k) - 1)) == a;', pre=lambda a, k: 0 <= k < 31,
         post=lambda a, k, r: r == 1,
         domain=[(a, k) for a in boundary(t) for k in range(-1, 33)])

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
