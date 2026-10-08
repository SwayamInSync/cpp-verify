#!/usr/bin/env python3
"""Rewrite C++ sources from cpp-verify's keyword syntax to the qualified one.

    cppverify-migrate.py [--prefix=cv] FILE...

Each construct written as a keyword (pre, post, invariant, decreases, ghost,
spec, proof, forall, exists, modifies, aliases, recommends, reveal_with_fuel,
hide, reveal) or contextually (result, old, choose, trigger, calc, reads,
when, inductive, behavior, complete_behaviors, disjoint_behaviors) gains the
qualifier, cppverify:: by default; contract_assert becomes cppverify::check.
Comments and string literals are left alone. With --prefix=cv, declare the
alias yourself (namespace cv = cppverify;) before the first construct.

Files are rewritten in place; review the diff and compile with
-fverify-contracts: a construct the script missed is an error whose fix-it
inserts the qualifier.
"""

import re
import sys

KEYWORDS = {'pre', 'post', 'invariant', 'type_invariant', 'decreases', 'ghost',
            'spec', 'proof', 'contract_assert', 'forall', 'exists', 'modifies',
            'aliases', 'recommends', 'reveal_with_fuel', 'hide', 'reveal'}
RENAMED = {'contract_assert': 'check'}
CLAUSE_WORDS = {'reads', 'when', 'behavior', 'complete_behaviors',
                'disjoint_behaviors', 'inductive'}
TOKEN = re.compile(r'''
    (?P<ws>\s+)
  | (?P<comment>//[^\n]*|/\*.*?\*/)
  | (?P<raw>R"(?P<delim>[^(\s]*)\(.*?\)(?P=delim)")
  | (?P<str>(?:u8|u|U|L)?"(?:\\.|[^"\\\n])*")
  | (?P<chr>(?:u8|u|U|L)?'(?:\\.|[^'\\\n])+')
  | (?P<num>\.?\d(?:[\w.']|[eEpP][+-])*)
  | (?P<id>[A-Za-z_]\w*)
  | (?P<punct>::|->|\.\.\.|==|!=|<=|>=|&&|\|\||.)
''', re.S | re.X)


def tokens(text):
    out = []
    for m in TOKEN.finditer(text):
        kind = m.lastgroup if m.lastgroup != 'delim' else 'raw'
        if kind in ('str', 'chr', 'raw', 'num'):
            out.append(('lit', m.group(), m.start()))
        elif kind in ('id', 'punct'):
            out.append((kind, m.group(), m.start()))
    return out


def migrate(text, prefix):
    toks = tokens(text)
    edits = []
    # Open brackets, with the clause word before a parenthesis; brace blocks
    # that are a post's proof.
    stack = []
    by_post = False
    after_post = False
    for i, (kind, word, off) in enumerate(toks):
        prev = toks[i - 1][1] if i else ''
        nxt = toks[i + 1][1] if i + 1 < len(toks) else ''
        if kind == 'punct':
            if word in '([{':
                opener = prev if word == '(' and i and toks[i - 1][0] == 'id' else ''
                if word == '{' and by_post:
                    opener, by_post = 'post-proof', False
                stack.append((word, opener))
            elif word in ')]}':
                if stack:
                    bracket, opener = stack.pop()
                    after_post = bracket == '(' and opener == 'post'
                continue
            after_post = False
            continue
        if kind != 'id' or prev in ('.', '->', '::') or nxt == '::':
            if kind != 'id' or word != 'by':
                after_post = False
            continue
        if word == 'by' and after_post and nxt == '{':
            by_post = True
            continue
        after_post = False
        parens = [opener for (bracket, opener) in stack if bracket == '(']
        braces = [opener for (bracket, opener) in stack if bracket == '{']
        new = None
        if word in KEYWORDS:
            new = RENAMED.get(word, word)
        elif word == 'result' and ('post' in parens or 'post-proof' in braces):
            new = word
        elif word == 'old' and nxt == '(' and ('post' in parens or
                                               'invariant' in parens or
                                               'post-proof' in braces):
            new = word
        elif word == 'choose' and nxt == '(':
            new = word
        elif word == 'trigger' and nxt == '(' and (
                'forall' in parens or 'exists' in parens or 'choose' in parens):
            new = word
        elif word == 'calc' and nxt == '{' and prev in (';', '{', '}', ')', ''):
            new = word
        elif word in CLAUSE_WORDS and prev in (')', 'inductive',
                                               'complete_behaviors',
                                               'disjoint_behaviors', 'const',
                                               'noexcept'):
            if word in ('reads', 'when', 'behavior') and nxt != '(':
                continue
            if word == 'inductive' and nxt == '(':
                continue
            new = word
        if new is not None:
            edits.append((off, word, prefix + '::' + new))
    for off, old, new in sorted(edits, reverse=True):
        text = text[:off] + new + text[off + len(old):]
    return text, len(edits)


def main(argv):
    prefix = 'cppverify'
    files = []
    for arg in argv:
        if arg.startswith('--prefix='):
            prefix = arg.split('=', 1)[1]
        elif arg in ('-h', '--help'):
            print(__doc__)
            return 0
        else:
            files.append(arg)
    if not files:
        print(__doc__, file=sys.stderr)
        return 1
    total = 0
    for path in files:
        with open(path) as f:
            text = f.read()
        new, count = migrate(text, prefix)
        if count:
            with open(path, 'w') as f:
                f.write(new)
        total += count
        print('%5d %s' % (count, path))
    print('%5d total' % total)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
