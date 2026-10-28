"""Structs by value with small-type fields, struct returns, nested structs."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
C = []

def case(*a, **k):
    C.append(Case(*a, **k))

S = 'struct S { int8_t a; uint16_t b; int c; };'
case('st_fields_promote', [('int8_t', 'a'), ('uint16_t', 'b')], 'int',
     'cppverify::post(%s == a * b)' % R, 'S s; s.a = a; s.b = b; s.c = 0; return s.a * s.b;',
     prelude=S, post=lambda a, b, r: r == a * b,
     domain=[(a, b) for a in range(-128, 128) for b in (0, 1, 2, 255, 256, 32767, 32768, 65534, 65535)])
case('st_field_compound', [('int8_t', 'a'), ('int', 'k')], 'int',
     'cppverify::pre(k > -1000 && k < 1000)\ncppverify::post(%s == ((a + k) %% 256 + 256 + 128) %% 256 - 128)' % R,
     'S s; s.a = a; s.b = 0; s.c = 0; s.a += k; return s.a;', prelude=S,
     pre=lambda a, k: -1000 < k < 1000, post=lambda a, k, r: r == wrap(a + k, 'int8_t'),
     domain=[(a, k) for a in range(-128, 128) for k in (-999, -300, -129, -128, -1, 0, 1, 127, 128, 255, 256, 999)])
case('st_field_inc_u16', [('uint16_t', 'b')], 'int',
     'cppverify::post(%s == (b + 1) %% 65536)' % R, 'S s; s.a = 0; s.b = b; s.c = 0; s.b++; return s.b;',
     prelude=S, post=lambda b, r: r == (b + 1) % 65536)
case('st_field_mul_u16', [('uint16_t', 'b')], 'int',
     'cppverify::post(%s == (b * b) %% 65536)' % R, 'S s; s.a = 0; s.b = b; s.c = 0; s.b *= s.b; return s.b;',
     prelude=S, post=lambda b, r: r == (b * b) % 65536)
SP = S + '''
S mk(int8_t a, uint16_t b, int c)
  cppverify::post(cppverify::result.a == a && cppverify::result.b == b && cppverify::result.c == c)
{ S s; s.a = a; s.b = b; s.c = c; return s; }'''
case('st_ret_use', [('int', 'x')], 'int',
     'cppverify::post(%s == ((x %% 256) + 384) %% 256 - 128)' % R, 'S s = mk(x, 0, 0); return s.a;',
     prelude=SP, post=lambda x, r: r == wrap(x, 'int8_t'))
case('st_ret_use_wrong', [('int', 'x')], 'int',
     'cppverify::post(%s == x)' % R, 'S s = mk(x, 0, 0); return s.a;',
     prelude=SP, post=lambda x, r: r == x)
SPASS = S + '''
int sum3(S s)
  cppverify::post(cppverify::result == s.a + s.b + s.c || true)
{ return s.a + s.b; }'''
case('st_pass_by_value', [('int8_t', 'a'), ('uint16_t', 'b')], 'int',
     'cppverify::post(%s == a + b)' % R, 'S s; s.a = a; s.b = b; s.c = 7; int r = sum3(s); return r;',
     prelude=SPASS, post=lambda a, b, r: True)
SMOD = S + '''
S bump(S s)
  cppverify::pre(s.c < 1000 && s.c > -1000)
  cppverify::post(cppverify::result.c == s.c + 1 && cppverify::result.a == s.a)
{ s.c = s.c + 1; return s; }'''
case('st_callee_modifies_copy', [('int', 'c')], 'int',
     'cppverify::pre(c < 900 && c > -900)\ncppverify::post(%s == c)' % R, 'S s; s.a = 1; s.b = 2; s.c = c; S t = bump(s); return s.c;',
     prelude=SMOD, pre=lambda c: -900 < c < 900, post=lambda c, r: r == c, domain=[(c,) for c in range(-905, 905)])
case('st_callee_result', [('int', 'c')], 'int',
     'cppverify::pre(c < 900 && c > -900)\ncppverify::post(%s == c + 1)' % R, 'S s; s.a = 1; s.b = 2; s.c = c; S t = bump(s); return t.c;',
     prelude=SMOD, pre=lambda c: -900 < c < 900, post=lambda c, r: r == c + 1, domain=[(c,) for c in range(-905, 905)])
case('st_copy_independent', [('int', 'c')], 'int',
     'cppverify::post(%s == c)' % R, 'S s; s.a = 1; s.b = 2; s.c = c; S t = s; t.c = 0; return s.c;',
     prelude=S, post=lambda c, r: r == c)
case('st_assign_copy', [('int', 'c')], 'int',
     'cppverify::post(%s == 0)' % R, 'S s; s.a = 1; s.b = 2; s.c = c; S t; t = s; t.c = 0; return t.c;',
     prelude=S, post=lambda c, r: r == 0)
NEST = 'struct In { int8_t v; }; struct Out { In i; uint8_t w; };'
case('st_nested', [('int', 'x')], 'int',
     'cppverify::post(%s == (((x %% 256) + 384) %% 256 - 128) + (x %% 256 + 256) %% 256)' % R,
     'Out o; o.i.v = x; o.w = x; return o.i.v + o.w;', prelude=NEST,
     post=lambda x, r: r == wrap(x, 'int8_t') + x % 256)
case('st_uninit_field', [('int', 'x')], 'int',
     'cppverify::post(true)', 'S s; s.a = 1; return s.c;', prelude=S, post=lambda x, r: True)
case('st_bool_field', [('int', 'x')], 'int',
     'cppverify::post(%s == (x != 0 ? 2 : 0))' % R,
     'struct B { bool f; } b; b.f = x; return b.f + b.f;', post=lambda x, r: r == (2 if x != 0 else 0))

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
