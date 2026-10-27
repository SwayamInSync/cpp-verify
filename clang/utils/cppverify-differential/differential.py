"""Differential execution: cpp-verify's verdicts against the C++ they are about.

A case is a contracted C++ function. cpp-verify verifies it in each
configuration (a backend and an integer encoding). The same source, compiled by
clang with -fverify-contracts -fno-verify (contracts emit no code) and
-fsanitize=undefined in trap mode, runs on every input of a domain: every value
of small parameter types, otherwise boundary values and samples. The case's
precondition and postcondition, restated in Python over mathematical integers
as contract arithmetic is, judge each run. A problem is:

- UNSOUND: a configuration verified the function, or found it bounded-safe
  where the input stays within the bound, yet an admitted input runs into
  undefined behavior or breaks the postcondition;
- BADCEX: a certified counterexample whose input the precondition rejects, or
  on which the function runs without undefined behavior and meets its
  postcondition;
- DISAGREE: two configurations reach different decisive verdicts.
"""
import itertools
import json
import os
import random
import subprocess
import zlib

TYPES = {
    'bool': (1, False),
    'char': (8, True),
    'signed char': (8, True), 'int8_t': (8, True),
    'unsigned char': (8, False), 'uint8_t': (8, False),
    'short': (16, True), 'int16_t': (16, True),
    'unsigned short': (16, False), 'uint16_t': (16, False), 'char16_t': (16, False),
    'int': (32, True), 'int32_t': (32, True), 'wchar_t': (32, True),
    'unsigned': (32, False), 'unsigned int': (32, False), 'uint32_t': (32, False),
    'char32_t': (32, False),
    'long': (64, True), 'long long': (64, True), 'int64_t': (64, True),
    'unsigned long': (64, False), 'unsigned long long': (64, False),
    'uint64_t': (64, False), 'size_t': (64, False),
    '__int128': (128, True), 'unsigned __int128': (128, False),
}

CONFIGS = {
    'z3': [],
    'bv': ['--int-encoding=bitvector'],
    'int': ['--int-encoding=integer'],
    'cvc5': ['--backend=cvc5'],
    'bmc6': ['--backend=bmc', '--unroll=6'],
    'bmc10': ['--backend=bmc', '--unroll=10'],
    'bmc6bv': ['--backend=bmc', '--unroll=6', '--int-encoding=bitvector'],
    'bmc10bv': ['--backend=bmc', '--unroll=10', '--int-encoding=bitvector'],
}

DECISIVE = ('verified', 'failed')

# The failures a run can show: a broken postcondition, or undefined behavior
# that UBSan, a guard page, or the alarm stops. Others are claims about
# annotations (checks, invariants, measures, frames, callees' preconditions)
# or undefined behavior UBSan does not see (uninitialized reads).
OBSERVABLE = ('postcondition', 'overflow', 'division-by-zero', 'shift', 'bounds',
              'dereference', 'missing-return', 'unreachable')


def bound_of(config):
    for flag in CONFIGS[config]:
        if flag.startswith('--unroll='):
            return int(flag.split('=')[1])
    return None


def trange(t):
    bits, signed = TYPES[t]
    if t == 'bool':
        return 0, 1
    if signed:
        return -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    return 0, (1 << bits) - 1


def boundary(t):
    lo, hi = trange(t)
    if t == 'bool':
        return [0, 1]
    bits, _ = TYPES[t]
    vals = {lo, lo + 1, lo + 2, hi, hi - 1, hi - 2, 0, 1, 2, 3, -1, -2, -3, 5, 7,
            10, 100, -100}
    for k in range(0, bits + 1):
        for d in (-1, 0, 1):
            vals.add((1 << k) + d)
            vals.add(-(1 << k) + d)
    for k in (8, 16, 32, 64):
        if k < bits:
            vals.add((1 << k) - 1)
    return sorted(v for v in vals if lo <= v <= hi)


def wrap(v, t):
    """The C++ conversion of a mathematical value to integer type t."""
    if t == 'bool':
        return 1 if v != 0 else 0
    bits, signed = TYPES[t]
    v &= (1 << bits) - 1
    if signed and v >= 1 << (bits - 1):
        v -= 1 << bits
    return v


def in_range(v, t):
    lo, hi = trange(t)
    return lo <= v <= hi


def tdiv(a, b):
    """C++ division, truncating toward zero."""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def tmod(a, b):
    return a - b * tdiv(a, b)


def seeded(name):
    return random.Random(zlib.crc32(name.encode()))


HARNESS_HEAD = r'''
#include <csignal>
#include <csetjmp>
#include <cstdio>
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <cstdlib>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/time.h>
static sigjmp_buf cv_env;
static void cv_handler(int s) { siglongjmp(cv_env, s); }
static __int128 cv_parse(const char *s) {
  bool neg = false; if (*s == '-') { neg = true; ++s; }
  unsigned __int128 v = 0; while (*s >= '0' && *s <= '9') { v = v * 10 + (*s - '0'); ++s; }
  return (__int128)(neg ? (unsigned __int128)0 - v : v);
}
static void cv_print(__int128 v) {
  char buf[64]; int n = 0; bool neg = v < 0;
  unsigned __int128 u = neg ? -(unsigned __int128)v : (unsigned __int128)v;
  if (u == 0) buf[n++] = '0';
  while (u) { buf[n++] = '0' + (int)(u % 10); u /= 10; }
  if (neg) putchar('-');
  while (n) putchar(buf[--n]);
}
static char cv_altstack[1 << 16];
static void cv_install() {
  stack_t ss; ss.ss_sp = cv_altstack; ss.ss_size = sizeof cv_altstack; ss.ss_flags = 0;
  sigaltstack(&ss, nullptr);
  struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_handler = cv_handler;
  sigemptyset(&sa.sa_mask); sa.sa_flags = SA_NODEFER | SA_ONSTACK;
  int sigs[] = {SIGILL, SIGFPE, SIGSEGV, SIGTRAP, SIGBUS, SIGALRM};
  for (int s : sigs) sigaction(s, &sa, nullptr);
}
static void cv_alarm(int ms) {
  struct itimerval it; memset(&it, 0, sizeof it);
  it.it_value.tv_sec = ms / 1000; it.it_value.tv_usec = (ms % 1000) * 1000;
  setitimer(ITIMER_REAL, &it, nullptr);
}
struct cv_guard { char *base; size_t total; };
static void *cv_galloc(size_t bytes, int layout, cv_guard *g) {
  size_t pg = 4096; size_t dp = (bytes + pg - 1) / pg; if (dp == 0) dp = 1;
  g->total = (dp + 2) * pg;
  g->base = (char *)mmap(nullptr, g->total, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  char *data = g->base + pg; mprotect(data, dp * pg, PROT_READ | PROT_WRITE);
  return layout == 0 ? (void *)(data + dp * pg - bytes) : (void *)data;
}
static void cv_gfree(cv_guard *g) { munmap(g->base, g->total); }
'''


class Tools:
    def __init__(self, cpp_verify, clang, workdir, timeout_ms=30000):
        self.cpp_verify = cpp_verify
        self.clang = clang
        self.workdir = workdir
        self.timeout_ms = timeout_ms


class Case:
    """A function over integer parameters [(type, name)]."""

    def __init__(self, name, params, ret, contract, body, pre=None, post=None,
                 prelude='', std='c++17', domain=None, vflags=None, nsamples=20000,
                 call=None, alarm_ms=1000, iterations=None):
        self.name = name
        self.params = params
        self.ret = ret
        self.contract = contract
        self.body = body
        self.pre = pre
        self.post = post
        self.prelude = prelude
        self.std = std
        self.domain = domain
        self.vflags = vflags or []
        self.nsamples = nsamples
        self.call = call
        self.alarm_ms = alarm_ms
        self.iterations = iterations

    def sig(self):
        params = ', '.join('%s %s' % (t, n) for t, n in self.params)
        return '%s %s(%s)' % (self.ret, self.name, params)

    def source(self):
        return ('#include <cstdint>\n#include <cstddef>\n' + self.prelude + '\n' +
                self.sig() + '\n' + self.contract + '\n{\n' + self.body + '\n}\n')

    def contract_lines(self):
        first = ('#include <cstdint>\n#include <cstddef>\n' + self.prelude + '\n' +
                 self.sig() + '\n').count('\n') + 1
        return range(first, first + self.contract.count('\n') + 1)

    def harness(self):
        args = ', '.join('(%s)cv_parse(tok[%d])' % (t, i)
                         for i, (t, _) in enumerate(self.params))
        call = self.call or '%s(%s)' % (self.name, args)
        if self.ret == 'void':
            run = '%s; printf("R 0\\n");' % call
        else:
            run = '__int128 r = (__int128)(%s); printf("R "); cv_print(r); printf("\\n");' % call
        return HARNESS_HEAD + self.source() + r'''
int main() {
  cv_install();
  static char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    const char *tok[16]; int nt = 0; char *p = strtok(line, " \n");
    while (p && nt < 16) { tok[nt++] = p; p = strtok(nullptr, " \n"); }
    int s = sigsetjmp(cv_env, 1);
    if (s == 0) {
      cv_alarm(%d);
      %s
      cv_alarm(0);
    } else { cv_alarm(0); printf("U %%d\n", s); }
  }
  return 0;
}
''' % (self.alarm_ms, run)

    def inputs(self):
        if self.domain is not None:
            dom = self.domain() if callable(self.domain) else self.domain
            return [tuple(x) for x in dom]
        types = [t for t, _ in self.params]
        total = 1
        for t in types:
            lo, hi = trange(t)
            total *= hi - lo + 1
        if total <= 70000:
            return list(itertools.product(*[range(trange(t)[0], trange(t)[1] + 1)
                                            for t in types]))
        rng = seeded(self.name)
        bounds = [boundary(t) for t in types]
        count = 1
        for b in bounds:
            count *= len(b)
        out = []
        if count <= 200000:
            out.extend(itertools.product(*bounds))
        else:
            out.extend(tuple(rng.choice(b) for b in bounds) for _ in range(100000))
        for _ in range(self.nsamples):
            tup = []
            for t, b in zip(types, bounds):
                lo, hi = trange(t)
                r = rng.random()
                if r < 0.3:
                    tup.append(rng.choice(b))
                elif r < 0.6:
                    tup.append(rng.randint(max(lo, -300), min(hi, 300)))
                else:
                    tup.append(rng.randint(lo, hi))
            out.append(tuple(tup))
        return out

    def encode(self, inp):
        return [' '.join(str(v) for v in inp)]

    def parse(self, line):
        kind, value = line.split()
        return ('UB', int(value), None) if kind == 'U' else ('R', int(value), None)

    def admitted(self, inp):
        return self.pre is None or bool(self.pre(*inp))

    def holds(self, inp, result, buffers):
        return self.post is None or bool(self.post(*inp, result))

    def model_input(self, entry):
        """The parameters' entry values in a counterexample, 0 where undetermined."""
        if not entry.get('model'):
            return None
        values = {}
        for m in entry.get('model') or []:
            values.setdefault(m.get('name'), {})[m.get('ssa_name', '')] = m.get('value')
        tup = []
        for _, n in self.params:
            cand = values.get(n)
            v = None
            if cand:
                v = cand.get(n + '_0', cand[sorted(cand)[0]])
            if v in (None, '<unknown>'):
                v = 0
            if v in ('true', 'false'):
                v = int(v == 'true')
            tup.append(int(v))
        return tuple(tup)


class PCase(Case):
    """A function over scalars and memory. Each parameter is one of:

      ('s', type, name)               a scalar
      ('b', elem, name, length)       a buffer of exactly `length` elements
      ('o', type, name)               a pointer to one object
      ('r', type, name)               a reference to one object
      ('n', type, name)               a null pointer to type
      ('a', type, name, other)        a pointer to the memory of parameter other

    An input is a dict {name: int | list}. Each input runs twice, with every
    buffer ending at an inaccessible page and then starting after one.
    """

    def __init__(self, name, params, ret, contract, body, inputs, pre=None, post=None,
                 prelude='', std='c++17', vflags=None, alarm_ms=1000, iterations=None):
        super().__init__(name, params, ret, contract, body, pre=pre, post=post,
                         prelude=prelude, std=std, vflags=vflags, alarm_ms=alarm_ms,
                         iterations=iterations)
        self.domain = inputs

    def decl(self, p):
        if p[0] == 's':
            return '%s %s' % (p[1], p[2])
        if p[0] == 'r':
            return '%s &%s' % (p[1], p[2])
        return '%s *%s' % (p[1], p[2])

    def sig(self):
        return '%s %s(%s)' % (self.ret, self.name, ', '.join(self.decl(p) for p in self.params))

    def harness(self):
        decls, args, frees, prints = [], [], [], []
        for i, p in enumerate(self.params):
            k = p[0]
            if k == 's':
                decls.append('    %s v%d = (%s)cv_parse(tok[ti++]);' % (p[1], i, p[1]))
                args.append('v%d' % i)
            elif k in ('b', 'o', 'r'):
                t = p[1].replace('const ', '')
                decls.append('    long c%d = (long)cv_parse(tok[ti++]); cv_guard g%d; '
                             '%s *v%d = (%s *)cv_galloc(c%d * sizeof(%s), layout, &g%d);'
                             % (i, i, t, i, t, i, t, i))
                decls.append('    for (long j = 0; j < c%d; ++j) v%d[j] = (%s)cv_parse(tok[ti++]);'
                             % (i, i, t))
                args.append('*v%d' % i if k == 'r' else 'v%d' % i)
                frees.append('cv_gfree(&g%d);' % i)
                prints.append('    printf(" |"); for (long j = 0; j < c%d; ++j) '
                              '{ printf(" "); cv_print((__int128)v%d[j]); }' % (i, i))
            elif k == 'n':
                args.append('(%s *)nullptr' % p[1])
            elif k == 'a':
                args.append('v%d' % [q[2] for q in self.params].index(p[3]))
        call = '%s(%s)' % (self.name, ', '.join(args))
        if self.ret == 'void':
            run = '%s; cv_alarm(0); printf("R 0");' % call
        else:
            run = '__int128 r = (__int128)(%s); cv_alarm(0); printf("R "); cv_print(r);' % call
        return (HARNESS_HEAD + self.source() +
                'int main() {\n  cv_install();\n  static char line[1 << 16];\n'
                '  while (fgets(line, sizeof line, stdin)) {\n'
                '    const char *tok[4096]; int nt = 0; char *p = strtok(line, " \\n");\n'
                '    while (p && nt < 4096) { tok[nt++] = p; p = strtok(nullptr, " \\n"); }\n'
                '    int ti = 0; int layout = (int)cv_parse(tok[ti++]);\n' +
                '\n'.join(decls) + '\n'
                '    int s = sigsetjmp(cv_env, 1);\n    if (s == 0) {\n'
                '      cv_alarm(%d);\n      %s\n' % (self.alarm_ms, run) +
                '\n'.join(prints) + '\n'
                '      printf("\\n");\n    } else { cv_alarm(0); printf("U %d\\n", s); }\n'
                '    ' + ' '.join(frees) + '\n  }\n  return 0;\n}\n')

    def inputs(self):
        return list(self.domain() if callable(self.domain) else self.domain)

    def encode(self, inp):
        lines = []
        for layout in (0, 1):
            toks = [str(layout)]
            for p in self.params:
                if p[0] == 's':
                    toks.append(str(inp[p[2]]))
                elif p[0] in ('b', 'o', 'r'):
                    vals = inp[p[2]]
                    if not isinstance(vals, list):
                        vals = [vals]
                    toks.append(str(len(vals)))
                    toks.extend(str(v) for v in vals)
            lines.append(' '.join(toks))
        return lines

    def parse(self, line):
        if line.startswith('U '):
            return ('UB', int(line.split()[1]), None)
        parts = line[2:].split(' |')
        return ('R', int(parts[0]), [[int(x) for x in q.split()] for q in parts[1:]])

    def admitted(self, inp):
        return self.pre is None or bool(self.pre(inp))

    def holds(self, inp, result, buffers):
        return self.post is None or bool(self.post(inp, buffers, result))

    def model_input(self, entry):
        return None


def run_verifier(tools, path, std, flags):
    cmd = ([tools.cpp_verify, '--diagnostics-format=json', '--timeout=%d' % tools.timeout_ms] +
           flags + [path, '--', '-std=' + std])
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=10 * tools.timeout_ms / 1000 + 60)
    except subprocess.TimeoutExpired:
        return None, cmd
    records = {}
    for line in p.stdout.splitlines():
        line = line.strip()
        if not line.startswith('{'):
            continue
        try:
            record = json.loads(line)
        except ValueError:
            continue
        records.setdefault(record.get('function'), []).append(record)
    return records, cmd


def verdict_of(records):
    for record in records:
        if record.get('status') in ('verified', 'failed', 'unresolved', 'bounded-safe', 'trusted'):
            return record.get('status'), record
    if records:
        return records[0].get('status'), records[0]
    return 'missing', None


def label(status, record):
    if status == 'failed' and record:
        return 'failed:' + (record.get('obligation') or {}).get('kind', '?')
    if status == 'unresolved' and record:
        return 'unresolved:' + str(record.get('reason'))
    return status


def disagreement(verdicts):
    if len({v[0] for v in verdicts.values() if v[0] in DECISIVE}) > 1:
        return ['DISAGREE: %s' % {c: v[0] for c, v in verdicts.items()}]
    return []


def abstracted(record):
    """Whether a counterexample passes a call or an arbitrary loop iteration,
    where it is relative to a callee's contract or a loop's invariant."""
    return any(e.get('kind') == 'call' or
               (e.get('kind') == 'loop' and e.get('message') == 'inductive iteration')
               for e in record.get('trace') or [])


def run_case(tools, case, configs):
    base = os.path.join(tools.workdir, case.name)
    with open(base + '.cpp', 'w') as f:
        f.write(case.source())
    verdicts = {}
    for config in configs:
        records, cmd = run_verifier(tools, base + '.cpp', case.std, CONFIGS[config] + case.vflags)
        if records is None:
            verdicts[config] = ('timeout', None)
            continue
        verdicts[config] = verdict_of(records.get(case.name, []))

    inputs = [inp for inp in case.inputs() if case.admitted(inp)]
    if not inputs:
        line = '%-40s %s (no inputs to run)' % (
            case.name, ' '.join('%s=%s' % (c, label(*v)) for c, v in verdicts.items()))
        return {'case': case.name, 'verdicts': {c: label(*v) for c, v in verdicts.items()},
                'admitted': 0, 'violations': 0, 'counterexamples': {},
                'problems': disagreement(verdicts), 'line': line}

    with open(base + '.harness.cpp', 'w') as f:
        f.write(case.harness())
    p = subprocess.run([tools.clang, '--driver-mode=g++', '-std=' + case.std, '-O0', '-w',
                        '-fverify-contracts', '-fno-verify', '-fsanitize=undefined',
                        '-fno-sanitize=vptr,function', '-fsanitize-trap=undefined',
                        base + '.harness.cpp', '-o', base + '.harness'],
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError('the harness does not compile:\n' + p.stderr[:3000])

    counterexamples = {}
    for config, (status, record) in verdicts.items():
        if status == 'failed' and record is not None:
            counterexamples[config] = case.model_input(record)
    extra = [c for c in counterexamples.values() if c is not None and case.admitted(c)]
    encoded = [case.encode(inp) for inp in inputs + extra]
    lines = [line for runs in encoded for line in runs]
    q = subprocess.run([base + '.harness'], input='\n'.join(lines) + '\n',
                       capture_output=True, text=True, timeout=3600)
    results = q.stdout.splitlines()
    if len(results) != len(lines):
        raise RuntimeError('the harness ran %d of %d inputs: %s'
                           % (len(results), len(lines), q.stderr[:2000]))
    outs, at = [], 0
    for runs in encoded:
        outs.append([case.parse(line) for line in results[at:at + len(runs)]])
        at += len(runs)

    admitted, violations = len(inputs), []
    for inp, runs in zip(inputs, outs):
        for kind, result, buffers in runs:
            if kind == 'UB':
                violations.append((inp, 'UB', result))
                break
            if not case.holds(inp, result, buffers):
                violations.append((inp, 'POST', result))
                break

    problems = []
    checked = {}
    for config, (status, record) in verdicts.items():
        bound = bound_of(config)
        if status == 'verified' or (status == 'bounded-safe' and case.iterations is not None):
            within = violations
            if status == 'bounded-safe':
                within = [v for v in violations if case.iterations(v[0]) < bound]
            if within:
                problems.append('UNSOUND[%s]: %s, yet %d admitted inputs misbehave, such as %s'
                                % (config, status, len(within), within[:3]))
        if status != 'failed' or record is None:
            continue
        obligation = record.get('obligation') or {}
        kind = obligation.get('kind', '')
        if kind not in OBSERVABLE:
            checked[config] = 'not observable by running (%s)' % kind
            continue
        if (kind != 'postcondition' and
                (obligation.get('source') or {}).get('line') in case.contract_lines()):
            checked[config] = 'the contract is undefined there (%s)' % kind
            continue
        cex = counterexamples.get(config)
        if cex is None:
            checked[config] = 'no input values'
            continue
        if not case.admitted(cex):
            problems.append('BADCEX[%s]: %s, which the precondition rejects' % (config, cex))
            continue
        k, r, _ = outs[len(inputs) + extra.index(cex)][0]
        if k == 'UB':
            checked[config] = 'confirmed: undefined behavior at %s' % (cex,)
        elif not case.holds(cex, r, None):
            checked[config] = 'confirmed: %s returns %d' % (cex, r)
        elif abstracted(record):
            checked[config] = ('not reproduced at %s, relative to the contract of a callee '
                               'or a loop invariant' % (cex,))
        else:
            problems.append('BADCEX[%s]: %s returns %d and meets the contract (%s)'
                            % (config, cex, r, (record.get('message') or '')[:300]))
    problems += disagreement(verdicts)
    line = '%-40s %s admitted=%d violations=%d' % (
        case.name, ' '.join('%s=%s' % (c, label(*v)) for c, v in verdicts.items()),
        admitted, len(violations))
    if checked:
        line += ' counterexamples: ' + '; '.join('%s %s' % c for c in checked.items())
    return {'case': case.name, 'verdicts': {c: label(*v) for c, v in verdicts.items()},
            'admitted': admitted, 'violations': len(violations), 'counterexamples': checked,
            'problems': problems, 'line': line}
