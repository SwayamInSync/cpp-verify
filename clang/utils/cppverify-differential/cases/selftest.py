"""Cases that check the tool itself. Two restate their contract wrongly in
Python on purpose, so that a right verdict reads as a problem: the tool must
report it."""
from differential import *  # noqa: F401,F403

R = 'cppverify::result'

CASES = [
    Case('self_add', [('int8_t', 'x'), ('int8_t', 'y')], 'int',
         'cppverify::post(%s == x + y)' % R, 'return x + y;',
         post=lambda x, y, r: r == x + y),
    Case('self_overflow', [('int', 'x')], 'int',
         'cppverify::post(%s == x + 1)' % R, 'return x + 1;',
         post=lambda x, r: r == x + 1),
    Case('self_bound', [('int16_t', 'x')], 'int16_t',
         'cppverify::pre(x >= 0)\ncppverify::post(%s >= 0)' % R, 'return x;',
         pre=lambda x: x >= 0, post=lambda x, r: r > 0),
    Case('self_wrong_at_5', [('int8_t', 'x')], 'int',
         'cppverify::post(%s == x)' % R, 'return x == 5 ? 6 : x;',
         post=lambda x, r: True),
    Case('self_contract_div', [('int8_t', 'x')], 'int',
         'cppverify::post(100 / x == 100 / x)', 'return 0;'),
    PCase('self_read_past', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'int',
          'cppverify::pre(cppverify::valid(a, n) && n >= 1 && n <= 4)',
          'return a[n];',
          [{'n': n, 'a': [7] * n} for n in range(1, 5)],
          pre=lambda inp: 1 <= inp['n'] <= 4),
    PCase('self_sum', [('b', 'const int', 'a', 'n'), ('s', 'int', 'n')], 'long',
          'cppverify::pre(cppverify::valid(a, n) && n >= 0 && n <= 4)\n'
          'cppverify::post(%s >= -8589934592 && %s <= 8589934588)' % (R, R),
          'long s = 0;\nfor (int i = 0; i < n; i++)\n'
          '  cppverify::invariant(0 <= i && i <= n && s >= -2147483648L * i && s <= 2147483647L * i)\n'
          '  cppverify::decreases(n - i)\n'
          '{ s += a[i]; }\nreturn s;',
          [{'n': n, 'a': [v] * n} for n in range(5) for v in (-2**31, -1, 0, 1, 2**31 - 1)],
          pre=lambda inp: 0 <= inp['n'] <= 4,
          post=lambda inp, bufs, r: -8589934592 <= r <= 8589934588),
]
CONFIGS = ('z3',)
