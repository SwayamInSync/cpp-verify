"""Pointers, buffers, frames, aliasing, references."""
import itertools
import random
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
O = 'cppverify::old'
FA = 'cppverify::forall'
EX = 'cppverify::exists'
V = 'cppverify::valid'
C = []


def rbuf(rng, n, t, lo=None, hi=None):
    a, b = trange(t)
    if lo is not None:
        a = max(a, lo)
    if hi is not None:
        b = min(b, hi)
    out = []
    for _ in range(n):
        r = rng.random()
        if r < 0.15:
            out.append(rng.choice([a, b, 0, 1, -1 if a < 0 else 0]))
        elif r < 0.6:
            out.append(rng.randint(max(a, -20), min(b, 20)))
        else:
            out.append(rng.randint(a, b))
    return out

def case(*a, **k):
    C.append(PCase(*a, **k))

def gen_buf_n(t, nmax=8, count=400, lo=None, hi=None, extra_scalars=None, seed=1):
    def g():
        rng = random.Random(seed)
        out = []
        for _ in range(count):
            n = rng.randint(0, nmax)
            d = {'n': n, 'a': rbuf(rng, n, t, lo, hi)}
            if extra_scalars:
                for k, f in extra_scalars.items():
                    d[k] = f(rng)
            out.append(d)
        return out
    return g

def objs(t, names, vals):
    return [dict(zip(names, combo)) for combo in itertools.product(vals, repeat=len(names))]

IV = [-2**31, -2**31 + 1, -1000, -1, 0, 1, 7, 1000, 2**31 - 2, 2**31 - 1]

case('p_swap', [('o', 'int', 'a'), ('o', 'int', 'b')], 'void',
     'cppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a, *b)\ncppverify::post(*a == %s(*b) && *b == %s(*a))' % (O, O),
     'int t = *a; *a = *b; *b = t;', inputs=objs('int', ['a', 'b'], IV),
     post=lambda i, b, r: b[0] == [i['b']] and b[1] == [i['a']])
case('p_frame_violation', [('o', 'int', 'a'), ('o', 'int', 'b')], 'void',
     'cppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a)\ncppverify::post(*a == 1)',
     '*a = 1; *b = 2;', inputs=objs('int', ['a', 'b'], [0, 1]),
     post=lambda i, b, r: b[0] == [1])
case('p_frame_ok', [('o', 'int', 'a'), ('o', 'int', 'b')], 'void',
     'cppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a)\ncppverify::post(*b == %s(*b) && *a == 1)' % O,
     '*a = 1;', inputs=objs('int', ['a', 'b'], IV),
     post=lambda i, b, r: b[1] == [i['b']] and b[0] == [1])
case('p_no_modifies_write', [('o', 'int', 'a')], 'void',
     'cppverify::pre(a != nullptr)\ncppverify::post(true)',
     '*a = 1;', inputs=objs('int', ['a'], [0]), post=lambda i, b, r: True)
case('p_inc_i8', [('o', 'int8_t', 'p')], 'void',
     'cppverify::pre(p != nullptr)\ncppverify::modifies(*p)\ncppverify::post(*p == (%s(*p) == 127 ? -128 : %s(*p) + 1))' % (O, O),
     '++*p;', inputs=[{'p': v} for v in range(-128, 128)],
     post=lambda i, b, r: b[0] == [wrap(i['p'] + 1, 'int8_t')])
case('p_compound_u16', [('o', 'uint16_t', 'p')], 'void',
     'cppverify::pre(p != nullptr)\ncppverify::modifies(*p)\ncppverify::post(*p == (%s(*p) * %s(*p)) %% 65536)' % (O, O),
     '*p *= *p;', inputs=[{'p': v} for v in range(0, 65536, 7)] + [{'p': 65535}, {'p': 46341}, {'p': 46340}],
     post=lambda i, b, r: b[0] == [(i['p'] ** 2) % 65536])
case('p_compound_i16_ptrs', [('o', 'int16_t', 'p'), ('o', 'int16_t', 'q')], 'void',
     'cppverify::pre(p != nullptr && q != nullptr)\ncppverify::modifies(*p)\ncppverify::post(*p == ((%s(*p) * *q) %% 65536 + 65536 + 32768) %% 65536 - 32768)' % O,
     '*p = *p * *q;', inputs=objs('int16_t', ['p', 'q'], [-32768, -32767, -1, 0, 1, 255, 32767]),
     post=lambda i, b, r: b[0] == [wrap(i['p'] * i['q'], 'int16_t')])
case('p_sum_bounded', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000 && %s(k, 0, n, a[k] >= -1000 && a[k] <= 1000))\ncppverify::post(%s >= -1000 * n && %s <= 1000 * n)' % (V, FA, R, R),
     '''int s = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && s >= -1000 * i && s <= 1000 * i)
  cppverify::decreases(n - i)
{ s += a[i]; }
return s;''', inputs=gen_buf_n('int', lo=-1000, hi=1000),
     pre=lambda i: True, post=lambda i, b, r: -1000 * i['n'] <= r <= 1000 * i['n'])
case('p_sum_unbounded', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(true)' % V,
     '''int s = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n)
  cppverify::decreases(n - i)
{ s += a[i]; }
return s;''', inputs=gen_buf_n('int'), post=lambda i, b, r: True)
case('p_oob_read', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(true)' % V,
     '''int s = 0;
for (int i = 0; i <= n; i++)
  cppverify::invariant(0 <= i && i <= n + 1)
  cppverify::decreases(n + 1 - i)
{ s = a[i]; }
return s;''', inputs=gen_buf_n('int'), post=lambda i, b, r: True)
case('p_reverse', [('b', 'int', 'a', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 100000)\ncppverify::modifies(*a)\ncppverify::post(%s(k, 0, n, a[k] == %s(a[n - 1 - k])))' % (V, FA, O),
     '''int i = 0;
int j = n - 1;
while (i < j)
  cppverify::invariant(0 <= i && i <= n && j == n - 1 - i && i <= j + 1)
  cppverify::invariant(cppverify::forall(k, 0, i, a[k] == cppverify::old(a[n - 1 - k])))
  cppverify::invariant(cppverify::forall(k, j + 1, n, a[k] == cppverify::old(a[n - 1 - k])))
  cppverify::invariant(cppverify::forall(k, i, j + 1, a[k] == cppverify::old(a[k])))
  cppverify::decreases(j - i)
{ int t = a[i]; a[i] = a[j]; a[j] = t; i = i + 1; j = j - 1; }''', inputs=gen_buf_n('int'),
     post=lambda i, b, r: b[0] == list(reversed(i['a'])))
case('p_max', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 1 && n <= 1000)\ncppverify::post(%s(k, 0, n, %s >= a[k]) && %s(k, 0, n, %s == a[k]))' % (V, FA, R, EX, R),
     '''int m = a[0];
for (int i = 1; i < n; i++)
  cppverify::invariant(1 <= i && i <= n && cppverify::forall(k, 0, i, m >= a[k]) && cppverify::exists(k, 0, i, m == a[k]))
  cppverify::decreases(n - i)
{ if (a[i] > m) m = a[i]; }
return m;''', inputs=gen_buf_n('int'), pre=lambda i: i['n'] >= 1,
     post=lambda i, b, r: r == max(i['a']))
case('p_find', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'x')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(%s == -1 ? %s(k, 0, n, a[k] != x) : (0 <= %s && %s < n && a[%s] == x && %s(k, 0, %s, a[k] != x)))' % (V, R, FA, R, R, R, FA, R),
     '''for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && cppverify::forall(k, 0, i, a[k] != x))
  cppverify::decreases(n - i)
{ if (a[i] == x) return i; }
return -1;''', inputs=gen_buf_n('int', lo=-3, hi=3, extra_scalars={'x': lambda r: r.randint(-3, 3)}),
     post=lambda i, b, r: r == (i['a'].index(i['x']) if i['x'] in i['a'] else -1))
case('p_count_bad_post', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'x')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(%s < n)' % (V, R),
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && 0 <= c && c <= i)
  cppverify::decreases(n - i)
{ if (a[i] == x) c++; }
return c;''', inputs=gen_buf_n('int', lo=-2, hi=2, extra_scalars={'x': lambda r: r.randint(-2, 2)}),
     post=lambda i, b, r: r < i['n'])
case('p_copy', [('b', 'int', 'd', 'n'), ('b', 'const int', 's', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(d, n) && %s(s, n) && n >= 0 && n <= 1000)\ncppverify::modifies(*d)\ncppverify::post(%s(k, 0, n, d[k] == s[k]))' % (V, V, FA),
     '''int j = 0;
while (j < n)
  cppverify::invariant(0 <= j && j <= n && cppverify::forall(k, 0, j, d[k] == s[k]))
  cppverify::decreases(n - j)
{ d[j] = s[j]; j = j + 1; }''',
     inputs=lambda: [{'n': n, 'd': [0] * n, 's': list(range(n))} for n in range(0, 9)],
     post=lambda i, b, r: b[0] == i['s'])
case('p_write_read_other', [('o', 'int', 'a'), ('o', 'int', 'b')], 'int',
     'cppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a)\ncppverify::post(%s == %s(*b))' % (R, O),
     '*a = 5; return *b;', inputs=objs('int', ['a', 'b'], [0, 5, 7]), post=lambda i, b, r: r == i['b'])
case('p_alias_opt_out', [('o', 'int', 'a'), ('a', 'int', 'b', 'a')], 'int',
     'cppverify::aliases(a, b)\ncppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a)\ncppverify::post(%s == %s(*b))' % (R, O),
     '*a = 5; return *b;', inputs=objs('int', ['a'], [0, 5, 7]), post=lambda i, b, r: r == i['a'])
case('p_alias_ok', [('o', 'int', 'a'), ('a', 'int', 'b', 'a')], 'int',
     'cppverify::aliases(a, b)\ncppverify::pre(a != nullptr && b != nullptr)\ncppverify::modifies(*a)\ncppverify::post(%s == 5 || %s == %s(*b))' % (R, R, O),
     '*a = 5; return *b;', inputs=objs('int', ['a'], [0, 5, 7]), post=lambda i, b, r: r == 5 or r == i['a'])
case('p_null_deref', [('n', 'int', 'p')], 'int',
     'cppverify::post(true)', 'return *p;', inputs=[{}], post=lambda i, b, r: True)
case('p_single_obj_idx1', [('o', 'int', 'p')], 'int',
     'cppverify::pre(p != nullptr)\ncppverify::post(true)', 'return p[1];', inputs=[{'p': 3}], post=lambda i, b, r: True)
case('p_arith_past_end', [('b', 'int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 1 && n <= 100)\ncppverify::post(true)' % V,
     'int *q = a + n + 1; return q == a ? 1 : 0;', inputs=gen_buf_n('int', count=20), pre=lambda i: i['n'] >= 1,
     post=lambda i, b, r: True)
case('p_one_past_end_ok', [('b', 'int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 1 && n <= 100)\ncppverify::post(%s == 0)' % (V, R),
     'int *q = a + n; return q == a ? 1 : 0;', inputs=gen_buf_n('int', count=20), pre=lambda i: i['n'] >= 1,
     post=lambda i, b, r: r == 0)
case('p_ref_inc', [('r', 'int', 'x')], 'void',
     'cppverify::pre(x < 100)\ncppverify::modifies(x)\ncppverify::post(x == %s(x) + 1)' % O,
     'x++;', inputs=[{'x': v} for v in IV], pre=lambda i: i['x'] < 100, post=lambda i, b, r: b[0] == [i['x'] + 1])
case('p_ref_frame', [('r', 'int', 'x'), ('r', 'int', 'y')], 'void',
     'cppverify::modifies(x)\ncppverify::post(x == 1)', 'x = 1; y = 2;', inputs=[{'x': 0, 'y': 0}],
     post=lambda i, b, r: b[0] == [1])
case('p_ref_i8_compound', [('r', 'int8_t', 'x'), ('s', 'int', 'k')], 'void',
     'cppverify::modifies(x)\ncppverify::post(x == ((%s(x) + k) %% 256 + 256 + 128) %% 256 - 128)' % O,
     'x += k;', inputs=[{'x': x, 'k': k} for x in (-128, -1, 0, 1, 127) for k in IV + [128, 255, 256, -129]],
     post=lambda i, b, r: b[0] == [wrap(i['x'] + i['k'], 'int8_t')])
case('p_struct_swap', [('o', 'S', 's')], 'void',
     'cppverify::pre(s != nullptr)\ncppverify::modifies(*s)\ncppverify::post(s->x == %s(s->y) && s->y == %s(s->x))' % (O, O),
     'int t = s->x; s->x = s->y; s->y = t;',
     prelude='struct S { int x; int y; };', inputs=[], post=None)
case('p_u8_sum', [('b', 'const uint8_t', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(%s >= 0 && %s <= 255 * n)' % (V, R, R),
     '''int s = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && s >= 0 && s <= 255 * i)
  cppverify::decreases(n - i)
{ s += a[i]; }
return s;''', inputs=gen_buf_n('uint8_t'), post=lambda i, b, r: r == sum(i['a']))
case('p_char_neg_count', [('b', 'const char', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(%s >= 0 && %s <= n)' % (V, R, R),
     '''int c = 0;
for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && c >= 0 && c <= i)
  cppverify::decreases(n - i)
{ if (a[i] < 0) c++; }
return c;''', inputs=gen_buf_n('char'), post=lambda i, b, r: r == sum(1 for v in i['a'] if v < 0))
case('p_memset_u8', [('b', 'uint8_t', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'v')], 'void',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::modifies(*a)\ncppverify::post(%s(k, 0, n, a[k] == (uint8_t)v))' % (V, FA),
     '''for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && cppverify::forall(k, 0, i, a[k] == (uint8_t)v))
  cppverify::decreases(n - i)
{ a[i] = v; }''', inputs=gen_buf_n('uint8_t', extra_scalars={'v': lambda r: r.choice([-1, 0, 255, 256, 300, -129, 2**31 - 1])}),
     post=lambda i, b, r: b[0] == [i['v'] % 256] * i['n'])
case('p_memset_u8_wrong', [('b', 'uint8_t', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'v')], 'void',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::modifies(*a)\ncppverify::post(%s(k, 0, n, a[k] == v))' % (V, FA),
     '''for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n && cppverify::forall(k, 0, i, a[k] == (uint8_t)v))
  cppverify::decreases(n - i)
{ a[i] = v; }''', inputs=gen_buf_n('uint8_t', extra_scalars={'v': lambda r: r.choice([-1, 0, 255, 256, 300, -129])}),
     post=lambda i, b, r: all(x == i['v'] for x in b[0]))
case('p_incall', [('b', 'int', 'a', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 100 && %s(k, 0, n, a[k] < 1000))\ncppverify::modifies(*a)\ncppverify::post(%s(k, 0, n, a[k] == %s(a[k]) + 1))' % (V, FA, FA, O),
     '''for (int i = 0; i < n; i++)
  cppverify::invariant(0 <= i && i <= n)
  cppverify::invariant(cppverify::forall(k, 0, i, a[k] == cppverify::old(a[k]) + 1))
  cppverify::invariant(cppverify::forall(k, i, n, a[k] == cppverify::old(a[k])))
  cppverify::decreases(n - i)
{ a[i] = a[i] + 1; }''', inputs=gen_buf_n('int', hi=999), post=lambda i, b, r: b[0] == [x + 1 for x in i['a']])
case('p_index_u8', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'i')], 'int',
     'cppverify::pre(%s(a, n) && n >= 1 && n <= 300 && i >= 0 && i < n)\ncppverify::post(%s == a[(uint8_t)i])' % (V, R),
     'return a[(uint8_t)i];',
     inputs=lambda: [{'n': n, 'a': list(range(n)), 'i': i} for n in (1, 2, 255, 256, 257, 300) for i in range(0, n, 1 if n < 10 else 13)],
     pre=lambda i: 1 <= i['n'] <= 300 and 0 <= i['i'] < i['n'], post=lambda i, b, r: r == i['a'][i['i'] % 256])
case('p_index_neg', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'i')], 'int',
     'cppverify::pre(%s(a, n) && n >= 1 && n <= 10 && i >= -1 && i < n)\ncppverify::post(true)' % V,
     'return a[i];', inputs=lambda: [{'n': n, 'a': list(range(n)), 'i': i} for n in (1, 3) for i in range(-1, n)],
     pre=lambda i: True, post=lambda i, b, r: True)
case('p_ptr_walk', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000 && %s(k, 0, n, a[k] >= 0 && a[k] <= 10))\ncppverify::post(%s >= 0 && %s <= 10 * n)' % (V, FA, R, R),
     '''int s = 0;
const int *q = a;
int i = 0;
while (i < n)
  cppverify::invariant(0 <= i && i <= n && q == a + i && s >= 0 && s <= 10 * i)
  cppverify::decreases(n - i)
{ s += *q; q = q + 1; i = i + 1; }
return s;''', inputs=gen_buf_n('int', lo=0, hi=10), post=lambda i, b, r: r == sum(i['a']))
case('p_ptr_walk_oob', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(a, n) && n >= 0 && n <= 1000)\ncppverify::post(true)' % V,
     '''int s = 0;
const int *q = a;
int i = 0;
while (i <= n)
  cppverify::invariant(0 <= i && i <= n + 1 && q == a + i)
  cppverify::decreases(n + 1 - i)
{ s = *q; q = q + 1; i = i + 1; }
return s;''', inputs=gen_buf_n('int'), post=lambda i, b, r: True)

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
