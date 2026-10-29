"""The C library's memcpy, memmove, memset, memcmp, and abs against their
models: each contract below is verified with the model's trust, so a run
that breaks it is a model the library does not conform to (UNSOUND), and the
false claims must not verify."""
import random
from differential import *  # noqa: F401,F403

R = 'cppverify::result'
O = 'cppverify::old'
FA = 'cppverify::forall'
V = 'cppverify::valid'
C = []


def case(*a, **k):
    C.append(PCase(*a, **k))


def values(rng, n, t):
    a, b = trange(t)
    return [rng.choice([a, b, 0, 1, -1 if a < 0 else 0]) if rng.random() < 0.3
            else rng.randint(a, b) for _ in range(n)]


def two_buffers(t, count=200, seed=11, same=False):
    def g():
        rng = random.Random(seed)
        out = []
        for _ in range(count):
            n = rng.randint(0, 8)
            d = values(rng, n, t)
            s = list(d) if same and rng.random() < 0.5 else values(rng, n, t)
            if same and n and rng.random() < 0.3:
                s[rng.randrange(n)] = d[rng.randrange(n)]
            out.append({'n': n, 'd': d, 's': s})
        return out
    return g


def one_buffer(t, count=200, seed=13, scalar=None):
    def g():
        rng = random.Random(seed)
        out = []
        for _ in range(count):
            n = rng.randint(0, 8)
            d = {'n': n, 'a': values(rng, n, t)}
            if scalar:
                d[scalar] = rng.choice([0, 1, 0xff, 0x80, 0x7f, -1, 256, 0x1234,
                                        rng.randint(-2**31, 2**31 - 1)])
            out.append(d)
        return out
    return g


def repeated(c, t):
    """The value of a t whose every byte is (unsigned char)c."""
    bits, _ = TYPES[t]
    v = 0
    for _ in range(bits // 8):
        v = (v << 8) | (c & 255)
    return wrap(v, t)


def memset_value(t):
    """The byte (unsigned char)c repeated in a t, in contract arithmetic."""
    bits, signed = TYPES[t]
    value = '(c & 255) * %dULL' % sum(256 ** j for j in range(bits // 8))
    if signed:
        whole = '2 * 9223372036854775808ULL' if bits == 64 else str(2 ** bits)
        value = '(%s - ((c & 128) != 0 ? %s : 0))' % (value, whole)
    return value


TYPES_UNDER_TEST = ['char', 'signed char', 'unsigned char', 'short',
                    'unsigned short', 'int', 'unsigned', 'long',
                    'unsigned long long']

for t in TYPES_UNDER_TEST:
    tag = t.replace(' ', '_')
    case('l_memcpy_' + tag,
         [('b', t, 'd', 'n'), ('b', 'const ' + t, 's', 'n'), ('s', 'int', 'n')], 'void',
         'cppverify::pre(%s(d, n) && %s(s, n) && 0 <= n && n <= 1000)\n'
         'cppverify::modifies(d[0 : n])\n'
         'cppverify::post(%s(k, 0, n, d[k] == s[k]))' % (V, V, FA),
         'memcpy(d, s, n * sizeof(%s));' % t, inputs=two_buffers(t),
         prelude='#include <cstring>',
         post=lambda i, b, r: b[0] == i['s'] and b[1] == i['s'])
    case('l_memset_' + tag,
         [('b', t, 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'c')], 'void',
         'cppverify::pre(%s(a, n) && 0 <= n && n <= 1000)\n'
         'cppverify::modifies(a[0 : n])\n'
         'cppverify::post(%s(k, 0, n, a[k] == %s))' % (V, FA, memset_value(t)),
         'memset(a, c, n * sizeof(%s));' % t, inputs=one_buffer(t, scalar='c'),
         prelude='#include <cstring>',
         post=(lambda t: lambda i, b, r: b[0] == [repeated(i['c'], t)] * i['n'])(t))
    case('l_memcmp_' + tag,
         [('b', 'const ' + t, 'd', 'n'), ('b', 'const ' + t, 's', 'n'), ('s', 'int', 'n')], 'int',
         'cppverify::pre(%s(d, n) && %s(s, n) && 0 <= n && n <= 1000)\n'
         'cppverify::post((%s == 0) == %s(k, 0, n, d[k] == s[k]))' % (V, V, R, FA),
         'return memcmp(d, s, n * sizeof(%s));' % t, inputs=two_buffers(t, same=True),
         prelude='#include <cstring>',
         post=lambda i, b, r: (r == 0) == (i['d'] == i['s']))

case('l_memmove_left', [('b', 'int', 'a', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(a, n) && 1 <= n && n <= 1000)\n'
     'cppverify::modifies(a[0 : n])\n'
     'cppverify::post(%s(k, 0, n - 1, a[k] == %s(a[k + 1])))' % (V, FA, O),
     'memmove(a, a + 1, (n - 1) * sizeof(int));',
     inputs=lambda: [d for d in one_buffer('int')() if d['n'] >= 1],
     prelude='#include <cstring>',
     post=lambda i, b, r: b[0][:-1] == i['a'][1:])
case('l_memmove_right', [('b', 'short', 'a', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(a, n) && 1 <= n && n <= 1000)\n'
     'cppverify::modifies(a[0 : n])\n'
     'cppverify::post(%s(k, 1, n, a[k] == %s(a[k - 1])))' % (V, FA, O),
     'memmove(a + 1, a, (n - 1) * sizeof(short));',
     inputs=lambda: [d for d in one_buffer('short')() if d['n'] >= 1],
     prelude='#include <cstring>',
     post=lambda i, b, r: b[0][1:] == i['a'][:-1])
case('l_memcmp_order', [('b', 'const unsigned char', 'd', 'n'),
                        ('b', 'const unsigned char', 's', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(d, n) && %s(s, n) && 0 <= n && n <= 1000)\n'
     'cppverify::post(%s(j, 0, n, !%s(i, 0, j, d[i] == s[i]) || d[j] == s[j] || '
     '(%s < 0) == (d[j] < s[j])))' % (V, V, FA, FA, R),
     'return memcmp(d, s, n);', inputs=two_buffers('unsigned char', same=True),
     prelude='#include <cstring>',
     post=lambda i, b, r: (r < 0) == (i['d'] < i['s']) and (r == 0) == (i['d'] == i['s']))
case('l_abs', [('s', 'int', 'x')], 'int',
     'cppverify::pre(x != -2147483647 - 1)\n'
     'cppverify::post(%s == (x < 0 ? -x : x))' % R,
     'return abs(x);', prelude='#include <cstdlib>',
     inputs=[{'x': x} for x in [-2**31 + 1, -1000, -1, 0, 1, 1000, 2**31 - 1]],
     pre=lambda i: i['x'] != -2**31, post=lambda i, b, r: r == abs(i['x']))
case('l_labs', [('s', 'long', 'x')], 'long',
     'cppverify::pre(x != -9223372036854775807L - 1)\n'
     'cppverify::post(%s == (x < 0 ? -x : x))' % R,
     'return std::abs(x);', prelude='#include <cstdlib>',
     inputs=[{'x': x} for x in [-2**63 + 1, -2**40, -1, 0, 1, 2**40, 2**63 - 1]],
     pre=lambda i: i['x'] != -2**63, post=lambda i, b, r: r == abs(i['x']))

# False claims: none may verify, and a counterexample must be a real one.
case('l_memcpy_false', [('b', 'int', 'd', 'n'), ('b', 'const int', 's', 'n'), ('s', 'int', 'n')], 'void',
     'cppverify::pre(%s(d, n) && %s(s, n) && 1 <= n && n <= 1000)\n'
     'cppverify::modifies(d[0 : n])\n'
     'cppverify::post(d[0] == %s(d[0]))' % (V, V, O),
     'memcpy(d, s, n * sizeof(int));', inputs=two_buffers('int'),
     prelude='#include <cstring>',
     pre=lambda i: i['n'] >= 1,
     post=lambda i, b, r: b[0][0] == i['d'][0])
case('l_memset_false', [('b', 'int', 'a', 'n'), ('s', 'int', 'n'), ('s', 'int', 'c')], 'void',
     'cppverify::pre(%s(a, n) && 1 <= n && n <= 1000)\n'
     'cppverify::modifies(a[0 : n])\n'
     'cppverify::post(a[0] == c)' % V,
     'memset(a, c, n * sizeof(int));', inputs=one_buffer('int', scalar='c'),
     prelude='#include <cstring>',
     pre=lambda i: i['n'] >= 1,
     post=lambda i, b, r: b[0][0] == i['c'])
case('l_memcmp_false', [('b', 'const int', 'd', 'n'), ('b', 'const int', 's', 'n'), ('s', 'int', 'n')], 'int',
     'cppverify::pre(%s(d, n) && %s(s, n) && 0 <= n && n <= 1000)\n'
     'cppverify::post(%s == 0)' % (V, V, R),
     'return memcmp(d, s, n * sizeof(int));', inputs=two_buffers('int', same=True),
     prelude='#include <cstring>',
     post=lambda i, b, r: r == 0)
case('l_abs_min', [('s', 'int', 'x')], 'int',
     'cppverify::post(%s >= 0)' % R,
     'return abs(x);', prelude='#include <cstdlib>',
     inputs=[{'x': x} for x in [-2**31, -1, 0, 2**31 - 1]],
     post=lambda i, b, r: r >= 0)

CASES = C
CONFIGS = ('z3', 'bv', 'int', 'cvc5')
