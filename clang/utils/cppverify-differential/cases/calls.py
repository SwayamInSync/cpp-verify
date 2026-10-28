"""Modular calls, argument/result conversions, recursion."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

INC8 = '''int8_t inc8(int8_t x)
  cppverify::pre(x < 127)
  cppverify::post(cppverify::result == x + 1)
{ return x + 1; }'''
case('m_conv_arg_ok', [('int', 'y')], 'int',
     'cppverify::pre(y == 200)\ncppverify::post(%s == -55)' % R, 'return inc8(y);',
     prelude=INC8, pre=lambda y: y == 200, post=lambda y, r: r == -55, domain=[(200,), (199,), (201,)])
case('m_conv_arg_wrong', [('int', 'y')], 'int',
     'cppverify::pre(y == 200)\ncppverify::post(%s == 201)' % R, 'return inc8(y);',
     prelude=INC8, pre=lambda y: y == 200, post=lambda y, r: r == 201, domain=[(200,)])
case('m_conv_arg_range', [('int', 'y')], 'int',
     'cppverify::pre(y >= 0 && y < 1000 && y %% 256 != 127)\ncppverify::post(%s == ((y + 128) %% 256) - 128 + 1)' % R,
     'return inc8(y);', prelude=INC8, pre=lambda y: 0 <= y < 1000 and y % 256 != 127,
     post=lambda y, r: r == wrap(y, 'int8_t') + 1, domain=[(y,) for y in range(-5, 1005)])
case('m_conv_arg_pre_violated', [('int', 'y')], 'int',
     'cppverify::pre(y == 383)\ncppverify::post(true)', 'return inc8(y);',
     prelude=INC8, pre=lambda y: y == 383, post=lambda y, r: True, domain=[(383,)])
TW = '''unsigned twice(unsigned x)
  cppverify::pre(x < 1000)
  cppverify::post(cppverify::result == 2 * x)
{ return 2 * x; }'''
case('m_unsigned_arg_neg', [('int', 'y')], 'unsigned',
     'cppverify::pre(y > -5 && y < 5)\ncppverify::post(%s < 10)' % R, 'return twice(y);',
     prelude=TW, pre=lambda y: -5 < y < 5, post=lambda y, r: r < 10, domain=[(y,) for y in range(-10, 10)])
LONGRET = '''long big(int x)
  cppverify::post(cppverify::result == x * 1000L)
{ return x * 1000L; }'''
case('m_ret_narrow', [('int', 'x')], 'int8_t',
     'cppverify::pre(x >= 0 && x < 100)\ncppverify::post(%s == x * 1000)' % R, 'int8_t r = big(x); return r;',
     prelude=LONGRET, pre=lambda x: 0 <= x < 100, post=lambda x, r: r == x * 1000, domain=[(x,) for x in range(-2, 102)])
case('m_ret_narrow_ok', [('int', 'x')], 'int8_t',
     'cppverify::pre(x >= 0 && x < 100)\ncppverify::post(%s == ((x * 1000 + 128) %% 256) - 128)' % R, 'int8_t r = big(x); return r;',
     prelude=LONGRET, pre=lambda x: 0 <= x < 100, post=lambda x, r: r == wrap(x * 1000, 'int8_t'), domain=[(x,) for x in range(-2, 102)])
BOOLP = '''int b2i(bool b)
  cppverify::post(cppverify::result == (b ? 1 : 0))
{ return b ? 1 : 0; }'''
case('m_bool_arg', [('int', 'x')], 'int',
     'cppverify::post(%s == (x != 0 ? 1 : 0))' % R, 'return b2i(x);',
     prelude=BOOLP, post=lambda x, r: r == (1 if x != 0 else 0))
case('m_bool_arg_wrong', [('int', 'x')], 'int',
     'cppverify::post(%s == x %% 2)' % R, 'return b2i(x);',
     prelude=BOOLP, post=lambda x, r: r == tmod(x, 2), domain=[(x,) for x in range(-3, 300)])
REASSIGN = '''int bump(int x)
  cppverify::pre(x < 1000 && x > -1000)
  cppverify::post(cppverify::result == x + 1)
{ x = x + 1; return x; }'''
case('m_callee_reassigns', [('int', 'y')], 'int',
     'cppverify::pre(y > -100 && y < 100)\ncppverify::post(%s == y + 2)' % R, 'return bump(bump(y));',
     prelude=REASSIGN, pre=lambda y: -100 < y < 100, post=lambda y, r: r == y + 2, domain=[(y,) for y in range(-105, 105)])
case('m_callee_reassigns_wrong', [('int', 'y')], 'int',
     'cppverify::pre(y > -100 && y < 100)\ncppverify::post(%s == y + 3)' % R, 'return bump(bump(y));',
     prelude=REASSIGN, pre=lambda y: -100 < y < 100, post=lambda y, r: r == y + 3, domain=[(y,) for y in range(-105, 105)])
case('m_nested_pre', [('int', 'y')], 'int',
     'cppverify::pre(y == 998)\ncppverify::post(true)', 'return bump(bump(y));',
     prelude=REASSIGN, pre=lambda y: y == 998, post=lambda y, r: True, domain=[(998,)])
HELPER = '''int helper(int x) { return x * 2; }'''
case('m_uncontracted_callee', [('int', 'x')], 'int',
     'cppverify::post(%s == 2 * x)' % R, 'return helper(x);',
     prelude=HELPER, post=lambda x, r: r == 2 * x)
case('m_uncontracted_callee_guard', [('int', 'x')], 'int',
     'cppverify::pre(x > -1000 && x < 1000)\ncppverify::post(%s == 2 * x)' % R, 'return helper(x);',
     prelude=HELPER, pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == 2 * x)
case('m_uncontracted_callee_wrong', [('int', 'x')], 'int',
     'cppverify::pre(x > -1000 && x < 1000)\ncppverify::post(%s == 3 * x)' % R, 'return helper(x);',
     prelude=HELPER, pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == 3 * x)
CEX = '''constexpr int cx(int x) { return x * 2; }'''
case('m_constexpr_callee_exec', [('int', 'x')], 'int',
     'cppverify::post(%s == 2 * x)' % R, 'return cx(x);',
     prelude=CEX, post=lambda x, r: r == 2 * x)
case('m_constexpr_callee_exec_wrong', [('int', 'x')], 'int',
     'cppverify::pre(x > -1000 && x < 1000)\ncppverify::post(%s == 3 * x)' % R, 'return cx(x);',
     prelude=CEX, pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == 3 * x)
FACT = '''int fact(int n)
  cppverify::pre(n >= 0 && n <= 12)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 1)
{ if (n == 0) return 1; int r = fact(n - 1); return n * r; }'''
case('m_rec_fact', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 12)\ncppverify::post(%s >= 1)' % R, 'return fact(n);',
     prelude=FACT, pre=lambda n: 0 <= n <= 12, post=lambda n, r: r >= 1, domain=[(n,) for n in range(-2, 15)])
FACT13 = '''int fact13(int n)
  cppverify::pre(n >= 0 && n <= 13)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 1)
{ if (n == 0) return 1; int r = fact13(n - 1); return n * r; }'''
case('m_rec_fact13', [('int', 'n')], 'int',
     'cppverify::pre(n >= 0 && n <= 13)\ncppverify::post(%s >= 1)' % R, 'return fact13(n);',
     prelude=FACT13, pre=lambda n: 0 <= n <= 13, post=lambda n, r: r >= 1, domain=[(n,) for n in range(-2, 15)])
EVENODD = '''bool is_odd(int n);
bool is_even(int n)
  cppverify::pre(n >= 0)
  cppverify::decreases(n)
  cppverify::post(cppverify::result == (n % 2 == 0))
{ if (n == 0) return true; return is_odd(n - 1); }
bool is_odd(int n)
  cppverify::pre(n >= 0)
  cppverify::decreases(n)
  cppverify::post(cppverify::result == (n % 2 == 1))
{ if (n == 0) return false; return is_even(n - 1); }'''
case('m_mutual_rec', [('int', 'n')], 'bool',
     'cppverify::pre(n >= 0 && n <= 1000)\ncppverify::post(%s == (n %% 2 == 0))' % R, 'return is_even(n);',
     prelude=EVENODD,
     pre=lambda n: 0 <= n <= 1000, post=lambda n, r: r == (1 if n % 2 == 0 else 0), domain=[(n,) for n in range(0, 1001)])
DEFARG = '''int addd(int x, int y = 5)
  cppverify::pre(x < 1000 && x > -1000)
  cppverify::post(cppverify::result == x + y)
{ return x + y; }'''
case('m_default_arg', [('int', 'x')], 'int',
     'cppverify::pre(x < 1000 && x > -1000)\ncppverify::post(%s == x + 5)' % R, 'return addd(x);',
     prelude=DEFARG,
     pre=lambda x: -1000 < x < 1000, post=lambda x, r: r == x + 5)
case('m_default_arg_ub', [('int', 'x')], 'int',
     'cppverify::post(true)', 'return addd(1, x);',
     prelude=DEFARG,
     post=lambda x, r: True)
OVL = '''int ov(int x) cppverify::post(cppverify::result == 1) { return 1; }
int ov(long x) cppverify::post(cppverify::result == 2) { return 2; }
int ov(unsigned x) cppverify::post(cppverify::result == 3) { return 3; }'''
case('m_overload', [('int8_t', 'x')], 'int',
     'cppverify::post(%s == 1)' % R, 'return ov(x);', prelude=OVL, post=lambda x, r: r == 1)
case('m_overload_u8', [('uint8_t', 'x')], 'int',
     'cppverify::post(%s == 1)' % R, 'return ov(x);', prelude=OVL, post=lambda x, r: r == 1)
case('m_overload_long', [('long', 'x')], 'int',
     'cppverify::post(%s == 2)' % R, 'return ov(x);', prelude=OVL, post=lambda x, r: r == 2)
case('m_overload_u', [('uint16_t', 'x')], 'int',
     'cppverify::post(%s == 3)' % R, 'return ov(x + 0u);', prelude=OVL, post=lambda x, r: r == 3)
SDIV = '''int sdiv(int x, int y)
  cppverify::pre(y != 0 && !(x == -2147483647 - 1 && y == -1))
  cppverify::post(cppverify::result == x / y)
{ return x / y; }'''
case('m_short_circuit_call', [('int', 'x'), ('int', 'y')], 'bool',
     'cppverify::post(true)', 'return y != 0 && y != -1 && sdiv(x, y) > 0;',
     prelude=SDIV, post=lambda x, y, r: True)
case('m_short_circuit_call_bad', [('int', 'x'), ('int', 'y')], 'bool',
     'cppverify::post(true)', 'return y != 0 && sdiv(x, y) > 0;',
     prelude=SDIV, post=lambda x, y, r: True)
case('m_ternary_call', [('int', 'x'), ('int', 'y')], 'int',
     'cppverify::post(y == 0 || y == -1 || %s == x / y)' % R, 'return (y == 0 || y == -1) ? 0 : sdiv(x, y);',
     prelude=SDIV, post=lambda x, y, r: y == 0 or y == -1 or r == tdiv(x, y))
WEAK = '''int weak(int x)
  cppverify::post(cppverify::result >= x)
{ return x < 100 ? 100 : x; }'''
case('m_weak_post', [('int', 'x')], 'int',
     'cppverify::post(%s >= 100)' % R, 'return weak(x);',
     prelude=WEAK, post=lambda x, r: r >= 100)
case('m_arg_eval_conv', [('uint8_t', 'a'), ('uint8_t', 'b')], 'int',
     'cppverify::post(%s == a + b)' % R, 'return sum16(a + b);',
     prelude='int sum16(int16_t v) cppverify::post(cppverify::result == v) { return v; }',
     post=lambda a, b, r: r == a + b)
case('m_arg_conv_u16', [('int', 'x')], 'int',
     'cppverify::pre(x >= 65530 && x <= 65540)\ncppverify::post(%s == x)' % R, 'return idu16(x);',
     prelude='int idu16(uint16_t v) cppverify::post(cppverify::result == v) { return v; }',
     pre=lambda x: 65530 <= x <= 65540, post=lambda x, r: r == x, domain=[(x,) for x in range(65525, 65545)])

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
