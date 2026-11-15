"""The sequence benchmark of the Z3 gate (gate.sh): one abstract workload of
valid and false claims over sequences, written in several exact SMT-LIB
encodings, among them cpp-verify's own (NT) and the plain sequence theory (N).
It comes from the sequence-encoding study that chose cpp-verify's encoding.

usage: seqbench.py OUT_DIR

Semantics (cppverify::seq): finite sequences of integers; s[i] is 0 outside
[0, len); update outside [0, len) changes nothing; subrange(lo, hi) clamps lo
into [0, len] and hi into [lo, len]; == is element-wise equality.
"""
import itertools, os, sys

# ---- abstract terms -------------------------------------------------------
# ('svar',n) ('ivar',n) ('int',k) ('len',s) ('at',s,i) ('push',s,x)
# ('upd',s,i,x) ('cat',s,t) ('sub',s,lo,hi) ('empty',) ('unit',x)
# ('contains',s,x) ('seq=',a,b) ('=',a,b) ('<',a,b) ('<=',a,b) ('+',a,b)
# ('-',a,b) ('and',*) ('or',*) ('not',a) ('=>',a,b) ('forall',k,body)
# ('forallr',k,lo,hi,body) ('existsr',k,lo,hi,body) ('app',f,args) ('fn',f,args)
# 'app' is a recursive spec over sequences; 'fn' an uninterpreted Int function.

def S(n): return ('svar', n)
def I(n): return ('ivar', n)
def K(k): return ('int', k)
def L(s): return ('len', s)
def At(s, i): return ('at', s, i)
def Push(s, x): return ('push', s, x)
def Upd(s, i, x): return ('upd', s, i, x)
def Cat(s, t): return ('cat', s, t)
def Sub(s, lo, hi): return ('sub', s, lo, hi)
def SEq(a, b): return ('seq=', a, b)
def Eq(a, b): return ('=', a, b)
def Lt(a, b): return ('<', a, b)
def Le(a, b): return ('<=', a, b)
def Add(a, b): return ('+', a, b)
def Minus(a, b): return ('-', a, b)
def And(*a): return ('and',) + a
def Or(*a): return ('or',) + a
def Not(a): return ('not', a)
def Imp(a, b): return ('=>', a, b)
def Forall(k, b): return ('forall', k, b)
def ForallR(k, lo, hi, b): return ('forallr', k, lo, hi, b)
def ExistsR(k, lo, hi, b): return ('existsr', k, lo, hi, b)
def App(f, *a): return ('app', f, a)
def Fn(f, *a): return ('fn', f, a)
def Contains(s, x): return ('contains', s, x)
EMPTY = ('empty',)

def free_vars(t, acc, bound=()):
    k = t[0]
    if k == 'svar': acc.setdefault(t[1], 'seq')
    elif k == 'ivar':
        if t[1] not in bound: acc.setdefault(t[1], 'int')
    elif k in ('forall',):
        free_vars(t[2], acc, bound + (t[1],))
    elif k in ('forallr', 'existsr'):
        free_vars(t[2], acc, bound); free_vars(t[3], acc, bound)
        free_vars(t[4], acc, bound + (t[1],))
    elif k in ('app', 'fn'):
        for a in t[2]: free_vars(a, acc, bound)
    else:
        for a in t[1:]:
            if isinstance(a, tuple): free_vars(a, acc, bound)

# ---- recursive specs (sequence parameter s, extra int params) -------------
SPECS = {
 # total(s) = total(s[0, len - 1]) + s[len - 1]
 'total': (['s'], [], lambda s: ('ite', Le(L(s), K(0)), K(0),
            Add(App('total', Sub(s, K(0), Minus(L(s), K(1)))), At(s, Minus(L(s), K(1)))))),
 # count(s, x) = occurrences of x
 'count': (['s'], ['x'], lambda s, x: ('ite', Le(L(s), K(0)), K(0),
            Add(App('count', Sub(s, K(0), Minus(L(s), K(1))), x),
                ('ite', Eq(At(s, Minus(L(s), K(1))), x), K(1), K(0))))),
}

# ---- workloads --------------------------------------------------------------
s, t, u = S('s'), S('t'), S('u')
x, i, j, k, n, lo, hi, a_, b_, c_, d_ = (I(v) for v in 'x i j k n lo hi a b c d'.split())
def in_range(v, lo_, hi_): return And(Le(lo_, v), Lt(v, hi_))
def sorted_(q): return ForallR('i1', K(0), L(q), ForallR('j1', I('i1'), L(q), Le(At(q, I('i1')), At(q, I('j1')))))

W = {}
def wl(name, hyps, ok, bad):
    W[name] = (hyps, ok, bad)

# W1 ground algebra
wl('g1_len_push', [], Eq(L(Push(s, x)), Add(L(s), K(1))), Eq(L(Push(s, x)), L(s)))
wl('g2_at_push', [], Eq(At(Push(s, x), L(s)), x), Eq(At(Push(s, x), Add(L(s), K(1))), x))
wl('g3_at_upd', [in_range(i, K(0), L(s))], Eq(At(Upd(s, i, x), i), x),
   Imp(Lt(Add(i, K(1)), L(s)), Eq(At(Upd(s, i, x), Add(i, K(1))), x)))
wl('g4_len_cat', [], Eq(L(Cat(s, t)), Add(L(s), L(t))), Eq(L(Cat(s, t)), L(s)))
wl('g5_len_sub', [Le(K(0), lo), Le(lo, hi), Le(hi, L(s))], Eq(L(Sub(s, lo, hi)), Minus(hi, lo)),
   Eq(L(Sub(s, lo, hi)), hi))
wl('g6_at_sub', [Le(K(0), lo), Le(lo, hi), Le(hi, L(s)), in_range(k, K(0), Minus(hi, lo))],
   Eq(At(Sub(s, lo, hi), k), At(s, Add(lo, k))), Eq(At(Sub(s, lo, hi), k), At(s, k)))
# W2 sequence equalities
wl('e1_cat_assoc', [], SEq(Cat(Cat(s, t), u), Cat(s, Cat(t, u))), SEq(Cat(Cat(s, t), u), Cat(Cat(t, s), u)))
wl('e2_take_cat', [], SEq(Sub(Cat(s, t), K(0), L(s)), s), SEq(Sub(Cat(s, t), K(0), L(s)), t))
wl('e3_drop_last_cat', [Lt(K(0), L(t))],
   SEq(Sub(Cat(s, t), K(0), Minus(L(Cat(s, t)), K(1))), Cat(s, Sub(t, K(0), Minus(L(t), K(1))))),
   SEq(Sub(Cat(s, t), K(0), Minus(L(Cat(s, t)), K(1))), Cat(s, Sub(t, K(1), L(t)))))
wl('e4_take_push', [], SEq(Sub(Push(s, x), K(0), L(s)), s), SEq(Sub(Push(s, x), K(1), Add(L(s), K(1))), s))
wl('e5_upd_same', [in_range(i, K(0), L(s))], SEq(Upd(s, i, At(s, i)), s), SEq(Upd(s, i, Add(At(s, i), K(1))), s))
wl('e6_sub_sub', [Le(K(0), a_), Le(a_, b_), Le(b_, L(s)), Le(K(0), c_), Le(c_, d_), Le(d_, Minus(b_, a_))],
   SEq(Sub(Sub(s, a_, b_), c_, d_), Sub(s, Add(a_, c_), Add(a_, d_))),
   Imp(Lt(K(0), a_), SEq(Sub(Sub(s, a_, b_), c_, d_), Sub(s, c_, d_))))
wl('e7_ext', [Eq(L(s), L(t))],
   Imp(ForallR('m', K(0), L(s), Eq(At(s, I('m')), At(t, I('m')))), SEq(s, t)),
   SEq(s, t))
wl('e8_split', [Le(K(0), k), Le(k, L(s))], SEq(s, Cat(Sub(s, K(0), k), Sub(s, k, L(s)))),
   SEq(s, Cat(Sub(s, k, L(s)), Sub(s, K(0), k))))
# W3 quantified element facts
wl('q1_inv_push', [Eq(L(s), n), Le(K(0), n), ForallR('m', K(0), n, Eq(At(s, I('m')), Fn('a', I('m'))))],
   ForallR('m', K(0), Add(n, K(1)), Eq(At(Push(s, Fn('a', n)), I('m')), Fn('a', I('m')))),
   ForallR('m', K(0), Add(n, K(1)), Eq(At(Push(s, Add(Fn('a', n), K(1))), I('m')), Fn('a', I('m')))))
wl('q2_all_upd', [Forall('m', Le(K(0), At(s, I('m'))))],
   Forall('m', Le(K(0), At(Upd(s, i, K(5)), I('m')))),
   Imp(in_range(i, K(0), L(s)), Forall('m', Le(K(0), At(Upd(s, i, K(-5)), I('m'))))))
wl('q3_contains', [], ('iff', Contains(s, x), ExistsR('m', K(0), L(s), Eq(At(s, I('m')), x))),
   Imp(Contains(s, x), Eq(At(s, K(0)), x)))
wl('q4_sorted_sub', [sorted_(s), Le(K(0), lo), Le(lo, hi), Le(hi, L(s))], sorted_(Sub(s, lo, hi)),
   Imp(Le(K(2), L(s)), sorted_(Upd(s, K(0), Add(At(s, K(1)), K(1))))))
# W4 recursive specs
wl('r1_total_push', [], Eq(App('total', Push(s, x)), Add(App('total', s), x)),
   Eq(App('total', Push(s, x)), App('total', s)))
U = Sub(t, K(0), Minus(L(t), K(1)))
IH = Eq(App('total', Cat(s, U)), Add(App('total', s), App('total', U)))
HINT1 = SEq(Sub(Cat(s, t), K(0), Minus(L(Cat(s, t)), K(1))), Cat(s, U))
HINT2 = Eq(At(Cat(s, t), Minus(L(Cat(s, t)), K(1))), At(t, Minus(L(t), K(1))))
GOAL = Eq(App('total', Cat(s, t)), Add(App('total', s), App('total', t)))
BADG = Eq(App('total', Cat(s, t)), Add(Add(App('total', s), App('total', t)), K(1)))
wl('r2_concat_hinted', [Lt(K(0), L(t)), IH, HINT1, HINT2], GOAL, BADG)
wl('r3_concat_unhinted', [Lt(K(0), L(t)), IH], GOAL, BADG)
wl('r4_count_push', [], Eq(App('count', Push(s, x), x), Add(App('count', s, x), K(1))),
   Eq(App('count', Push(s, Add(x, K(1))), x), Add(App('count', s, x), K(1))))
# W5 scale: a chain of pushes
def chain(m):
    hyps = [SEq(S('c0'), EMPTY)] + [SEq(S(f'c{q+1}'), Push(S(f'c{q}'), K(q))) for q in range(m)]
    last = S(f'c{m}')
    return hyps, Eq(At(last, K(m // 2)), K(m // 2)), Eq(At(last, K(m // 2)), K(m // 2 + 1))
for m in (50, 200):
    h, ok, bad = chain(m); wl(f'c{m}_push_chain', h, ok, bad)

# ---- encoders -------------------------------------------------------------
def clamp_lo(lo_, ln): return f"(ite (< {lo_} 0) 0 (ite (> {lo_} {ln}) {ln} {lo_}))"
def clamp_hi(hi_, lo2, ln): return f"(ite (< {hi_} {lo2}) {lo2} (ite (> {hi_} {ln}) {ln} {hi_}))"

class Native:
    """Z3/cvc5 sequences, as cpp-verify encodes them (seq_at recfun)."""
    name = 'N'
    def __init__(self, lemmas=False, inline_at=False, element=False, split=False):
        self.lemmas = lemmas or element; self.inline_at = inline_at
        self.element = element
        self.split = split
        self.extra = []
        if lemmas: self.name = 'NL'
        if inline_at: self.name = 'Ni'
        if element: self.name = 'NX' + ('i' if inline_at else '')
        if split: self.name = ('NX' + ('i' if inline_at else '') if element else 'N') + 'S'
    def sort(self): return "(Seq Int)"
    def preamble(self):
        out = []
        if not self.inline_at:
            out.append("(define-fun-rec seq_at ((x (Seq Int)) (i Int)) Int (ite (and (<= 0 i) (< i (seq.len x))) (seq.nth x i) 0))")
        if self.lemmas and self.inline_at:
            at = lambda q, i: f"(ite (and (<= 0 {i}) (< {i} (seq.len {q}))) (seq.nth {q} {i}) 0)"
            out.append(f"(assert (forall ((a (Seq Int)) (b (Seq Int)) (k Int)) (! (= {at('(seq.++ a b)', 'k')} (ite (< k (seq.len a)) {at('a', 'k')} {at('b', '(- k (seq.len a))')})) :pattern ((seq.nth (seq.++ a b) k)))))")
            out.append(f"(assert (forall ((x Int) (k Int)) (! (= {at('(seq.unit x)', 'k')} (ite (= k 0) x 0)) :pattern ((seq.nth (seq.unit x) k)))))")
            out.append(f"(assert (forall ((a (Seq Int)) (o Int) (n Int) (k Int)) (! (=> (and (<= 0 o) (<= 0 n) (<= (+ o n) (seq.len a))) (= {at('(seq.extract a o n)', 'k')} (ite (and (<= 0 k) (< k n)) {at('a', '(+ o k)')} 0))) :pattern ((seq.nth (seq.extract a o n) k)))))")
        elif self.lemmas:
            out.append("(assert (forall ((a (Seq Int)) (b (Seq Int)) (k Int)) (! (= (seq_at (seq.++ a b) k) (ite (< k (seq.len a)) (seq_at a k) (seq_at b (- k (seq.len a))))) :pattern ((seq_at (seq.++ a b) k)))))")
            out.append("(assert (forall ((x Int) (k Int)) (! (= (seq_at (seq.unit x) k) (ite (= k 0) x 0)) :pattern ((seq_at (seq.unit x) k)))))")
            out.append("(assert (forall ((a (Seq Int)) (o Int) (n Int) (k Int)) (! (=> (and (<= 0 o) (<= 0 n) (<= (+ o n) (seq.len a))) (= (seq_at (seq.extract a o n) k) (ite (and (<= 0 k) (< k n)) (seq_at a (+ o k)) 0))) :pattern ((seq_at (seq.extract a o n) k)))))")
        return out
    def var_facts(self, v): return []
    def e(self, t):
        k = t[0]; E = self.e
        if k == 'svar': return t[1]
        if k == 'ivar': return t[1]
        if k == 'int': return str(t[1]) if t[1] >= 0 else f"(- {-t[1]})"
        if k == 'empty': return "(as seq.empty (Seq Int))"
        if k == 'unit': return f"(seq.unit {E(t[1])})"
        if k == 'len': return f"(seq.len {E(t[1])})"
        if k == 'at':
            q, ix = E(t[1]), E(t[2])
            if self.inline_at: return f"(ite (and (<= 0 {ix}) (< {ix} (seq.len {q}))) (seq.nth {q} {ix}) 0)"
            return f"(seq_at {q} {ix})"
        if k == 'push': return f"(seq.++ {E(t[1])} (seq.unit {E(t[2])}))"
        if k == 'upd':
            q, ix, v = E(t[1]), E(t[2]), E(t[3])
            return (f"(ite (and (<= 0 {ix}) (< {ix} (seq.len {q}))) (seq.++ (seq.extract {q} 0 {ix}) (seq.unit {v}) "
                    f"(seq.extract {q} (+ {ix} 1) (- (seq.len {q}) {ix} 1))) {q})")
        if k == 'cat': return f"(seq.++ {E(t[1])} {E(t[2])})"
        if k == 'sub':
            q, l_, h_ = E(t[1]), E(t[2]), E(t[3])
            if t[2][0] == 'int' and t[2][1] >= 0:
                self.split_fact(t[1], l_, f"(- {h_} {l_})")
                return f"(seq.extract {q} {l_} (- {h_} {l_}))"
            self.split_fact(t[1], l_, f"(- {h_} {l_})")
            return f"(ite (< {l_} 0) (seq.extract {q} 0 {h_}) (seq.extract {q} {l_} (- {h_} {l_})))"
        if k == 'contains':
            q, v = E(t[1]), E(t[2])
            c = f"(seq.contains {q} (seq.unit {v}))"
            if self.element:
                self.extra.append(f"(assert (= {c} (exists ((ck Int)) (and (<= 0 ck) (< ck (seq.len {q})) (= {self.at(q, 'ck')} {v})))))")
            return c
        if k == 'seq=':
            a, b = E(t[1]), E(t[2])
            if self.element:
                self.extra.append(f"(assert (=> (and (= (seq.len {a}) (seq.len {b})) (forall ((ei Int)) (=> (and (<= 0 ei) (< ei (seq.len {a}))) (= {self.at(a, 'ei')} {self.at(b, 'ei')})))) (= {a} {b})))")
            return f"(= {a} {b})"
        return common(self, t)
    def split_fact(self, src, i, n):
        """extract(a ++ b, i, n) for i >= 0 lies in b, in a, or across both."""
        if not self.split: return
        if src[0] == 'push': a, b = self.e(src[1]), f"(seq.unit {self.e(src[2])})"
        elif src[0] == 'cat': a, b = self.e(src[1]), self.e(src[2])
        else: return
        whole = f"(seq.extract (seq.++ {a} {b}) {i} {n})"
        la = f"(seq.len {a})"
        split = (f"(ite (>= {i} {la}) (seq.extract {b} (- {i} {la}) {n}) "
                 f"(ite (<= (+ {i} {n}) {la}) (seq.extract {a} {i} {n}) "
                 f"(seq.++ (seq.extract {a} {i} (- {la} {i})) (seq.extract {b} 0 (- {n} (- {la} {i}))))))")
        self.extra.append(f"(assert (=> (<= 0 {i}) (= {whole} {split})))")
    def at(self, q, ix):
        if self.inline_at: return f"(ite (and (<= 0 {ix}) (< {ix} (seq.len {q}))) (seq.nth {q} {ix}) 0)"
        return f"(seq_at {q} {ix})"

class Terms(Native):
    """cpp-verify's encoding: per-term index facts quantified over the index,
    extract split facts, the contains bridge, extensionality for refuted
    equalities, and update as its spec body."""
    name = 'NT'
    def __init__(self):
        super().__init__(split=True)
        self.name = 'NT'
        self.polarity = 1
        self.named = {}
    def term_fact(self, term, element):
        if '(ite' in term:
            if term not in self.named:
                c = f"nt_t{len(self.named)}"
                self.named[term] = c
                self.extra.append(f"(declare-const {c} (Seq Int))")
                self.extra.append(f"(assert (= {c} {term}))")
            pat = self.named[term]
        else:
            pat = term
        self.extra.append(f"(assert (forall ((tk Int)) (! (= (seq_at {pat} tk) {element('tk')}) :pattern ((seq_at {pat} tk)) :qid fact!index)))")
    def e(self, t):
        k = t[0]; E = self.e
        if k == 'push':
            q, v = E(t[1]), E(t[2])
            term = f"(seq.++ {q} (seq.unit {v}))"
            self.term_fact(term, lambda K: f"(ite (= {K} (seq.len {q})) {v} (seq_at {q} {K}))")
            return term
        if k == 'cat':
            a, b = E(t[1]), E(t[2])
            term = f"(seq.++ {a} {b})"
            self.term_fact(term, lambda K: f"(ite (< {K} (seq.len {a})) (seq_at {a} {K}) (seq_at {b} (- {K} (seq.len {a}))))")
            return term
        if k == 'sub':
            term = super().e(t)
            q, l_, h_ = E(t[1]), E(t[2]), E(t[3])
            ln = f"(seq.len {q})"
            fr = clamp_lo(l_, ln); to = clamp_hi(h_, fr, ln)
            self.term_fact(term, lambda K: f"(ite (and (<= 0 {K}) (< {K} (- {to} {fr}))) (seq_at {q} (+ {fr} {K})) 0)")
            return term
        if k == 'upd':
            s_, i_, x_ = t[1], t[2], t[3]
            body = ('ite', And(Le(K(0), i_), Lt(i_, L(s_))),
                    Cat(Push(Sub(s_, K(0), i_), x_), Sub(s_, Add(i_, K(1)), L(s_))), s_)
            return E(body)
        if k == 'contains':
            q, v = E(t[1]), E(t[2])
            c = f"(seq.contains {q} (seq.unit {v}))"
            w = f"nt_w{len(self.extra)}"
            self.extra.append(f"(declare-const {w} Int)")
            self.extra.append(f"(assert (=> {c} (and (<= 0 {w}) (< {w} (seq.len {q})) (= (seq_at {q} {w}) {v}))))")
            self.extra.append(f"(assert (forall ((ck Int)) (! (=> (and (<= 0 ck) (< ck (seq.len {q})) (= (seq_at {q} ck) {v})) {c}) :pattern ((seq_at {q} ck)) :qid fact!contains)))")
            return c
        if k == 'seq=':
            a, b = E(t[1]), E(t[2])
            if self.polarity < 0:
                ext = f"(and (= (seq.len {a}) (seq.len {b})) (forall ((ei Int)) (! (=> (and (<= 0 ei) (< ei (seq.len {a}))) (= (seq_at {a} ei) (seq_at {b} ei))) :qid q)))"
                return f"(or (= {a} {b}) {ext})"
            return f"(= {a} {b})"
        if k == 'not':
            self.polarity = -self.polarity
            r = f"(not {E(t[1])})"
            self.polarity = -self.polarity
            return r
        if k == '=>':
            self.polarity = -self.polarity
            l = E(t[1])
            self.polarity = -self.polarity
            return f"(=> {l} {E(t[2])})"
        if k == 'forall':
            return f"(forall (({t[1]} Int)) (! {E(t[2])} :qid q))"
        if k == 'forallr':
            return f"(forall (({t[1]} Int)) (! (=> (and (<= {E(t[2])} {t[1]}) (< {t[1]} {E(t[3])})) {E(t[4])}) :qid q))"
        if k == 'existsr':
            return f"(exists (({t[1]} Int)) (! (and (<= {E(t[2])} {t[1]}) (< {t[1]} {E(t[3])}) {E(t[4])}) :qid q))"
        if k in ('iff', '=', 'ite'):
            saved = self.polarity; self.polarity = 0
            r = common(self, t) if k != 'ite' else f"(ite {E(t[1])} {E(t[2])} {E(t[3])})"
            self.polarity = saved
            return r
        return super().e(t)

class Axioms:
    """Dafny/Verus style: an uninterpreted ASeq sort with triggered axioms; == on
    sequences is Seq.Equal (extensional), as Dafny translates source ==."""
    name = 'AX'
    def sort(self): return "ASeq"
    def preamble(self):
        return """(declare-sort ASeq 0)
(declare-fun Len (ASeq) Int)
(declare-fun At (ASeq Int) Int)
(declare-fun Push (ASeq Int) ASeq)
(declare-fun Upd (ASeq Int Int) ASeq)
(declare-fun Cat (ASeq ASeq) ASeq)
(declare-fun Sub (ASeq Int Int) ASeq)
(declare-fun Unit (Int) ASeq)
(declare-fun Empty () ASeq)
(declare-fun Contains (ASeq Int) Bool)
(declare-fun Equal (ASeq ASeq) Bool)
(assert (forall ((s ASeq)) (! (<= 0 (Len s)) :pattern ((Len s)))))
(assert (= (Len Empty) 0))
(assert (forall ((s ASeq)) (! (=> (= (Len s) 0) (= s Empty)) :pattern ((Len s)))))
(assert (forall ((s ASeq) (i Int)) (! (=> (or (< i 0) (<= (Len s) i)) (= (At s i) 0)) :pattern ((At s i)))))
(assert (forall ((s ASeq) (v Int)) (! (= (Len (Push s v)) (+ 1 (Len s))) :pattern ((Push s v)))))
(assert (forall ((s ASeq) (v Int) (i Int)) (! (= (At (Push s v) i) (ite (= i (Len s)) v (At s i))) :pattern ((At (Push s v) i)))))
(assert (forall ((v Int)) (! (and (= (Len (Unit v)) 1) (= (At (Unit v) 0) v)) :pattern ((Unit v)))))
(assert (forall ((s ASeq) (i Int) (v Int)) (! (= (Len (Upd s i v)) (Len s)) :pattern ((Upd s i v)))))
(assert (forall ((s ASeq) (i Int) (v Int) (j Int)) (! (= (At (Upd s i v) j) (ite (and (<= 0 i) (< i (Len s)) (= j i)) v (At s j))) :pattern ((At (Upd s i v) j)))))
(assert (forall ((a ASeq) (b ASeq)) (! (= (Len (Cat a b)) (+ (Len a) (Len b))) :pattern ((Cat a b)))))
(assert (forall ((a ASeq) (b ASeq) (k Int)) (! (= (At (Cat a b) k) (ite (< k (Len a)) (At a k) (At b (- k (Len a))))) :pattern ((At (Cat a b) k)))))
(define-fun lo2 ((s ASeq) (lo Int)) Int (ite (< lo 0) 0 (ite (> lo (Len s)) (Len s) lo)))
(define-fun hi2 ((s ASeq) (lo Int) (hi Int)) Int (ite (< hi (lo2 s lo)) (lo2 s lo) (ite (> hi (Len s)) (Len s) hi)))
(assert (forall ((s ASeq) (lo Int) (hi Int)) (! (= (Len (Sub s lo hi)) (- (hi2 s lo hi) (lo2 s lo))) :pattern ((Sub s lo hi)))))
(assert (forall ((s ASeq) (lo Int) (hi Int) (k Int)) (! (= (At (Sub s lo hi) k) (ite (and (<= 0 k) (< k (- (hi2 s lo hi) (lo2 s lo)))) (At s (+ (lo2 s lo) k)) 0)) :pattern ((At (Sub s lo hi) k)))))
(assert (forall ((s ASeq) (x Int)) (! (= (Contains s x) (exists ((k Int)) (! (and (<= 0 k) (< k (Len s)) (= (At s k) x)) :pattern ((At s k))))) :pattern ((Contains s x)))))
(assert (forall ((a ASeq) (b ASeq)) (! (= (Equal a b) (and (= (Len a) (Len b)) (forall ((j Int)) (! (=> (and (<= 0 j) (< j (Len a))) (= (At a j) (At b j))) :pattern ((At a j)) :pattern ((At b j)))))) :pattern ((Equal a b)))))
(assert (forall ((a ASeq) (b ASeq)) (! (=> (Equal a b) (= a b)) :pattern ((Equal a b)))))
(assert (forall ((a ASeq) (b ASeq)) (! (and (= (Sub (Cat a b) 0 (Len a)) a) (= (Sub (Cat a b) (Len a) (+ (Len a) (Len b))) b)) :pattern ((Cat a b)))))""".split('\n')
    def var_facts(self, v): return []
    def e(self, t):
        k = t[0]; E = self.e
        if k == 'svar': return t[1]
        if k in ('ivar',): return t[1]
        if k == 'int': return str(t[1]) if t[1] >= 0 else f"(- {-t[1]})"
        if k == 'empty': return "Empty"
        if k == 'unit': return f"(Unit {E(t[1])})"
        if k == 'len': return f"(Len {E(t[1])})"
        if k == 'at': return f"(At {E(t[1])} {E(t[2])})"
        if k == 'push': return f"(Push {E(t[1])} {E(t[2])})"
        if k == 'upd': return f"(Upd {E(t[1])} {E(t[2])} {E(t[3])})"
        if k == 'cat': return f"(Cat {E(t[1])} {E(t[2])})"
        if k == 'sub': return f"(Sub {E(t[1])} {E(t[2])} {E(t[3])})"
        if k == 'contains': return f"(Contains {E(t[1])} {E(t[2])})"
        if k == 'seq=': return f"(Equal {E(t[1])} {E(t[2])})"
        return common(self, t)

class Arrays:
    """(length, array) with the array 0 outside [0, length)."""
    name = 'A'
    def sort(self): return None
    def preamble(self): return []
    def var_facts(self, v):
        return [f"(>= l_{v} 0)", f"(forall ((i Int)) (=> (or (< i 0) (>= i l_{v})) (= (select a_{v} i) 0)))"]
    def p(self, t):
        """(len, array) strings of a sequence term."""
        k = t[0]; E = self.e; P = self.p
        if k == 'svar': return (f"l_{t[1]}", f"a_{t[1]}")
        if k == 'empty': return ("0", "((as const (Array Int Int)) 0)")
        if k == 'unit': return ("1", f"(store ((as const (Array Int Int)) 0) 0 {E(t[1])})")
        if k == 'push':
            l, a = P(t[1]); return (f"(+ {l} 1)", f"(store {a} {l} {E(t[2])})")
        if k == 'upd':
            l, a = P(t[1]); ix, v = E(t[2]), E(t[3])
            return (l, f"(ite (and (<= 0 {ix}) (< {ix} {l})) (store {a} {ix} {v}) {a})")
        if k == 'cat':
            (l1, a1), (l2, a2) = P(t[1]), P(t[2])
            return (f"(+ {l1} {l2})", f"(lambda ((q Int)) (ite (< q {l1}) (select {a1} q) (select {a2} (- q {l1}))))")
        if k == 'sub':
            l, a = P(t[1]); lo_, hi_ = E(t[2]), E(t[3])
            l2 = clamp_lo(lo_, l); h2 = clamp_hi(hi_, l2, l)
            return (f"(- {h2} {l2})", f"(lambda ((q Int)) (ite (and (<= 0 q) (< q (- {h2} {l2}))) (select {a} (+ {l2} q)) 0))")
        if k == 'app_seq': raise NotImplementedError
        raise ValueError(k)
    def e(self, t):
        k = t[0]; E = self.e; P = self.p
        if k == 'ivar': return t[1]
        if k == 'int': return str(t[1]) if t[1] >= 0 else f"(- {-t[1]})"
        if k == 'len': return P(t[1])[0]
        if k == 'at': return f"(select {P(t[1])[1]} {E(t[2])})"
        if k == 'contains':
            l, a = P(t[1]); return f"(exists ((q Int)) (and (<= 0 q) (< q {l}) (= (select {a} q) {E(t[2])})))"
        if k == 'seq=':
            (l1, a1), (l2, a2) = P(t[1]), P(t[2]); return f"(and (= {l1} {l2}) (= {a1} {a2}))"
        if k == 'app':
            args = []
            for arg in t[2]:
                if arg[0] in ('svar', 'empty', 'unit', 'push', 'upd', 'cat', 'sub'):
                    l, a = P(arg); args += [l, a]
                else: args.append(E(arg))
            return f"({t[1]} {' '.join(args)})"
        return common(self, t)

def common(enc, t):
    k = t[0]; E = enc.e
    if k in ('=', '<', '<=', '+', '-', '=>'): return f"({k} {E(t[1])} {E(t[2])})"
    if k == 'iff': return f"(= {E(t[1])} {E(t[2])})"
    if k in ('and', 'or'): return f"({k} {' '.join(E(a) for a in t[1:])})"
    if k == 'not': return f"(not {E(t[1])})"
    if k == 'ite': return f"(ite {E(t[1])} {E(t[2])} {E(t[3])})"
    if k == 'forall': return f"(forall (({t[1]} Int)) {E(t[2])})"
    if k == 'forallr': return f"(forall (({t[1]} Int)) (=> (and (<= {E(t[2])} {t[1]}) (< {t[1]} {E(t[3])})) {E(t[4])}))"
    if k == 'existsr': return f"(exists (({t[1]} Int)) (and (<= {E(t[2])} {t[1]}) (< {t[1]} {E(t[3])}) {E(t[4])}))"
    if k == 'fn': return f"({t[1]} {' '.join(E(a) for a in t[2])})"
    if k == 'app':
        return f"({t[1]} {' '.join(E(a) for a in t[2])})"
    if k == 'ivar': return t[1]
    raise ValueError(k)

def spec_defs(enc, used):
    out = []
    for f in sorted(used):
        sparams, iparams, body = SPECS[f]
        args = [S(p) for p in sparams] + [I(p) for p in iparams]
        b = enc.e(body(*args))
        if isinstance(enc, Arrays):
            ps = ' '.join(f"(l_{p} Int) (a_{p} (Array Int Int))" for p in sparams)
        else:
            ps = ' '.join(f"({p} {enc.sort()})" for p in sparams)
        ps += ''.join(f" ({p} Int)" for p in iparams)
        out.append(f"(define-fun-rec {f} ({ps}) Int {b})")
    return out

def used_specs(t, acc):
    if not isinstance(t, tuple): return
    if t[0] == 'app':
        acc.add(t[1])
        for a in t[2]: used_specs(a, acc)
        return
    for a in t[1:]:
        if isinstance(a, tuple): used_specs(a, acc)

def emit(enc, name, hyps, goal, logic):
    fv = {}
    for h in hyps: free_vars(h, fv)
    free_vars(goal, fv)
    used = set()
    for h in hyps + [goal]: used_specs(h, used)
    for f in used:
        sp, ip, body = SPECS[f]
        used_specs(body(*([S(p) for p in sp] + [I(p) for p in ip])), used)
    lines = [f"(set-logic {logic})"]
    lines += enc.preamble()
    fns = set()
    def fnames(t):
        if not isinstance(t, tuple): return
        if t[0] == 'fn': fns.add((t[1], len(t[2])))
        for a in t[1:]:
            if isinstance(a, tuple): fnames(a)
            elif isinstance(a, (list,)): [fnames(b) for b in a]
        if t[0] in ('fn', 'app'):
            for b in t[2]: fnames(b)
    for h in hyps + [goal]: fnames(h)
    for f, ar in sorted(fns): lines.append(f"(declare-fun {f} ({' '.join(['Int'] * ar)}) Int)")
    for v, srt in sorted(fv.items()):
        if srt == 'seq':
            if isinstance(enc, Arrays):
                lines.append(f"(declare-const l_{v} Int)"); lines.append(f"(declare-const a_{v} (Array Int Int))")
                lines += [f"(assert {f})" for f in enc.var_facts(v)]
            else:
                lines.append(f"(declare-const {v} {enc.sort()})")
        else:
            lines.append(f"(declare-const {v} Int)")
    if hasattr(enc, 'extra'): enc.extra = []
    if hasattr(enc, 'named'): enc.named = {}
    lines += spec_defs(enc, used)
    for h in hyps: lines.append(f"(assert {enc.e(h)})")
    if hasattr(enc, 'polarity'): enc.polarity = -1
    lines.append(f"(assert (not {enc.e(goal)}))")
    if hasattr(enc, 'polarity'): enc.polarity = 1
    if hasattr(enc, 'extra'): lines += list(dict.fromkeys(enc.extra))
    lines.append("(check-sat)")
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    encs = [Native(), Native(lemmas=True), Native(inline_at=True), Native(element=True),
            Native(element=True, inline_at=True), Native(split=True),
            Native(element=True, inline_at=True, split=True), Terms(), Axioms(),
            Arrays()]
    count = 0
    for wname, (hyps, ok, bad) in W.items():
        for verdict, goal in (('ok', ok), ('bad', bad)):
            for enc in encs:
                for solver, logic in (('z3', 'ALL'), ('cvc5', 'ALL')):
                    if solver == 'cvc5' and isinstance(enc, Arrays):
                        continue
                    try:
                        text = emit(enc, wname, hyps, goal, logic)
                    except NotImplementedError:
                        continue
                    open(os.path.join(out, f"{wname}.{verdict}.{enc.name}.{solver}.smt2"), 'w').write(text)
                    count += 1
    print(count, 'files')
