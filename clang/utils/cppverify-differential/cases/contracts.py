"""Contract-expression semantics, old/result, constexpr vs spec."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
O = 'cppverify::old'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

# contract arithmetic is mathematical
case('c_inc_gt', [('int', 'x')], 'int',
     'cppverify::pre(x < 2147483647)\ncppverify::post(%s + 1 > %s)' % (R, R), 'return x + 1;',
     pre=lambda x: x < 2**31 - 1, post=lambda x, r: r + 1 > r)
case('c_neg_unsigned', [('unsigned', 'x')], 'unsigned',
     'cppverify::post(%s == -x)' % R, 'return -x;',
     post=lambda x, r: r == -x)
case('c_sum_u_math', [('unsigned', 'a'), ('unsigned', 'b')], 'unsigned',
     'cppverify::post(%s == a + b || %s == a + b - 4294967296)' % (R, R), 'return a + b;',
     post=lambda a, b, r: r == a + b or r == a + b - 2**32)
case('c_mixed_cmp', [('int', 'x'), ('unsigned', 'u')], 'bool',
     'cppverify::post(%s == (x < 0 || x < u))' % R, 'return x < 0 || (unsigned)x < u;',
     post=lambda x, u, r: r == (1 if (x < 0 or x < u) else 0))
case('c_mixed_cmp_wrong', [('int', 'x'), ('unsigned', 'u')], 'bool',
     'cppverify::post(%s == (x < u))' % R, 'return x < u;',
     post=lambda x, u, r: r == (1 if x < u else 0))
case('c_div_intmin', [('int', 'x')], 'int',
     'cppverify::pre(x != -2147483647 - 1)\ncppverify::post(%s == x / -1)' % R, 'return -x;',
     pre=lambda x: x != -2**31, post=lambda x, r: r == -x)
case('c_div_math', [('int', 'x')], 'long',
     'cppverify::post(%s == x / -1)' % R, 'return -(long)x;',
     post=lambda x, r: r == -x)
case('c_mod_sign', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::pre(y > 0)\ncppverify::post(x >= 0 ? %s >= 0 : %s <= 0)' % (R, R), 'return x % y;',
     pre=lambda x, y: y > 0, post=lambda x, y, r: (r >= 0) if x >= 0 else (r <= 0))
case('c_div_by_zero_in_post', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::post(y == 0 || %s == x / y || true)' % R, 'return 0;',
     post=lambda x, y, r: True)
case('c_div_by_zero_unguarded', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::post(%s == x / y || true)' % R, 'return 0;',
     post=lambda x, y, r: True)
# bitwise ops and shifts in contracts are machine operations
case('c_bitand', [('int', 'x')], 'int',
     'cppverify::post((%s & 255) == (x & 255))' % R, 'return x;',
     post=lambda x, r: (r & 255) == (x & 255))
case('c_bitand_math_operand', [('int', 'x')], 'int',
     'cppverify::post(((x + 1) & 1) == 0 || ((x + 1) & 1) == 1)', 'return 0;',
     post=lambda x, r: True)
case('c_shl_contract', [('int', 'x')], 'int',
     'cppverify::post(%s == (x << 1))' % R, 'return x * 2;',
     post=lambda x, r: True)
case('c_shr_contract', [('int', 'x')], 'int',
     'cppverify::post(%s == (x >> 1))' % R, 'return x >= 0 ? x / 2 : (x - 1) / 2;',
     post=lambda x, r: r == x >> 1)
case('c_bitnot_contract_u', [('unsigned', 'x')], 'unsigned',
     'cppverify::post(%s == ~x)' % R, 'return 4294967295u - x;',
     post=lambda x, r: r == 2**32 - 1 - x)
case('c_bitnot_contract_u8', [('uint8_t', 'x')], 'int',
     'cppverify::post(%s == ~x)' % R, 'return -1 - x;',
     post=lambda x, r: r == -1 - x)
case('c_xor_contract', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::post(%s == (x ^ y))' % R, 'return (x | y) & ~(x & y);',
     post=lambda x, y, r: r == x ^ y)
case('c_cast_contract', [('int', 'x')], 'int',
     'cppverify::post((unsigned char)%s == (unsigned char)x)' % R, 'return x + 256 * (x > 0 ? -1 : 1);',
     post=lambda x, r: True)
case('c_cast_contract_signed', [('unsigned', 'x')], 'int',
     'cppverify::post(%s == (int)x)' % R, 'return x;',
     post=lambda x, r: r == wrap(x, 'int'))
case('c_cast_contract_narrow_math', [('int', 'x')], 'int',
     'cppverify::post((int)(x + 1) == x + 1 || x == 2147483647)', 'return 0;',
     post=lambda x, r: True)
# old and parameters reassigned
case('c_old_param', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == %s(x) + 1 && %s == x + 1)' % (R, O, R),
     'x = x + 1; return x;', pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == x + 1)
case('c_old_param_loop', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == n)' % R,
     'int c = 0;\nwhile (n > 0)\n  cppverify::invariant(n >= 0 && c + n == cppverify::old(n))\n  cppverify::decreases(n)\n{ n = n - 1; c = c + 1; }\nreturn c;',
     pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == n)
case('c_old_param_wrong', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == x)' % R,
     'x = x + 1; return x;', pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == x)
case('c_result_small', [('int', 'x')], 'int8_t',
     'cppverify::post(%s != 200)' % R, 'return x;', post=lambda x, r: r != 200)
case('c_result_u8_cmp_neg', [('int', 'x')], 'uint8_t',
     'cppverify::post(%s > -1)' % R, 'return x;', post=lambda x, r: r > -1)
case('c_bool_result', [('int', 'x')], 'bool',
     'cppverify::post(%s == (x > 0))' % R, 'return x > 0;', post=lambda x, r: r == (1 if x > 0 else 0))
case('c_bool_plus', [('bool', 'a')], 'bool',
     'cppverify::post(%s + %s == 2 * a)' % (R, R), 'return a;', post=lambda a, r: 2 * r == 2 * a)
# constexpr helper (machine) vs spec (mathematical)
case('c_constexpr_sq', [('int', 'x')], 'int',
     'cppverify::post(sq(x) >= 0)', 'return 0;',
     prelude='constexpr int sq(int v) { return v * v; }', post=lambda x, r: True)
case('c_constexpr_sq_guard', [('int', 'x')], 'int',
     'cppverify::pre(x > -46000 && x < 46000)\ncppverify::post(sq(x) >= 0)', 'return 0;',
     prelude='constexpr int sq(int v) { return v * v; }', pre=lambda x: -46000 < x < 46000, post=lambda x, r: True)
case('c_spec_sq', [('int', 'x')], 'int',
     'cppverify::post(sq(x) >= 0)', 'return 0;',
     prelude='cppverify::spec int sq(int v) { return v * v; }', post=lambda x, r: True)
case('c_constexpr_wrap', [('unsigned', 'x')], 'unsigned',
     'cppverify::post(%s == inc(x))' % R, 'return x + 1;',
     prelude='constexpr unsigned inc(unsigned v) { return v + 1; }', post=lambda x, r: r == (x + 1) % 2**32)
case('c_constexpr_narrow_arg', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x < 1000)\ncppverify::post(%s == g(x))' % R, 'return x % 256;',
     prelude='constexpr int g(uint8_t v) { return v; }', pre=lambda x: 0 <= x < 1000, post=lambda x, r: r == x % 256)
case('c_constexpr_shift', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x < 31)\ncppverify::post(%s == p2(x))' % R, 'return 1 << x;',
     prelude='constexpr int p2(int v) { return 1 << v; }', pre=lambda x: 0 <= x < 31, post=lambda x, r: r == 2**x)
case('c_constexpr_branch_ub', [('int', 'x')], 'int',
     'cppverify::post(f(x) >= -1)', 'return 0;',
     prelude='constexpr int f(int v) { return v > 0 ? v + 1 : -1; }', post=lambda x, r: True)
case('c_spec_div', [('int', 'x')], 'int',
     'cppverify::post(%s == half(x))' % R, 'return x / 2;',
     prelude='cppverify::spec int half(int v) { return v / 2; }', post=lambda x, r: r == tdiv(x, 2))
case('c_spec_mod_neg', [('int', 'x')], 'int',
     'cppverify::post(%s == m3(x))' % R, 'return x % -3;',
     prelude='cppverify::spec int m3(int v) { return v % -3; }', post=lambda x, r: r == tmod(x, -3))
case('c_spec_u8_param', [('int', 'x')], 'int',
     'cppverify::pre(x == 300)\ncppverify::post(id8(x) == 300)', 'return 0;',
     prelude='cppverify::spec int id8(uint8_t v) { return v; }', pre=lambda x: x == 300, post=lambda x, r: True,
     domain=[(300,)])
case('c_spec_bool_ret', [('int', 'x')], 'int',
     'cppverify::post(b(x) == (x != 0))', 'return 0;',
     prelude='cppverify::spec bool b(int v) { return v; }', post=lambda x, r: True)
case('c_spec_u_ret', [('int', 'x')], 'int',
     'cppverify::post(u(x) >= 0)', 'return 0;',
     prelude='cppverify::spec unsigned u(int v) { return v; }',
     # A spec's integers are mathematical: u(x) is x, whatever its type.
     post=lambda x, r: x >= 0)
case('c_spec_shift', [('int', 'x')], 'int',
     'cppverify::pre(x >= 0 && x < 40)\ncppverify::post(sh(x) > 0)', 'return 0;',
     prelude='cppverify::spec long sh(int v) { return 1L << v; }', pre=lambda x: 0 <= x < 40, post=lambda x, r: True)
case('c_ternary_mixed_contract', [('bool', 'c')], 'long',
     'cppverify::post(%s == (c ? -1 : 0u))' % R, 'return c ? -1 : 0;',
     post=lambda c, r: r == (-1 if c else 0))

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
