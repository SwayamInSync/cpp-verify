# Contract Syntax & Language Design

## Enabling Contracts

All contract syntax is enabled with `-fverify-contracts`, and every construct
is written qualified by the namespace `cppverify`: `cppverify::pre(x > 0)`,
`cppverify::check(e)`, `cppverify::forall(k, ...)`. The parser recognizes a
construct when the qualifier names the global namespace `cppverify`, directly,
as `::cppverify::`, or through any namespace alias (`namespace cv =
cppverify;`, then `cv::pre`). No word is reserved: `pre`, `result`, `ghost`,
or `check` without the qualifier is ordinary C++, so every standard header and
every existing name keeps working, and C++26 contracts (`pre`, `post`,
`contract_assert`) are left to the compiler. `using namespace cppverify;` does
not make bare words constructs. With the flag, `<cppverify.h>` is included
implicitly; without it, the constructs are not recognized.

## Contract Syntax Overview

| Syntax | Where | Meaning |
|---|---|---|
| `cppverify::pre(expr)` | After function `)` | Precondition — caller must satisfy |
| `cppverify::post(expr)` | After function `)` | Postcondition — callee must establish; may use `cppverify::result` and `cppverify::old(x)` |
| `cppverify::modifies(lvalue, ...)` | After function `)`, or after a loop's invariants | Frame condition — the cells, ranges `p[lo : n]`, or objects this function or loop may write |
| `cppverify::aliases(p, q)` | After function `)` | Opts out of implicit non-aliasing for a supported same-pointee pointer/reference address pair |
| `cppverify::recommends(expr)` | After function `)` (spec only) | Soft precondition for spec functions; reported on verification failure |
| `cppverify::inductive` | After function `)` (spec returning `bool` only) | The least predicate the body defines: true where a finite derivation shows it |
| `cppverify::post(...) by { ... }`, `cppverify::decreases(...) by { ... }`, `cppverify::reads(...) by { ... }` | After a spec's clause | Proof steps for that clause's check (lemma calls, assertions) |
| `cppverify::behavior(name, assumes)` | After function `)`, followed by its `cppverify::pre`/`cppverify::post` | A case of the contract (ACSL behavior) |
| `cppverify::complete_behaviors` / `cppverify::disjoint_behaviors` | After the behaviors | Some behavior / at most one behavior applies to every admitted input |
| `cppverify::invariant(expr)` | After a `while`/`for` condition or a `do` loop's trailing condition | Loop invariant |
| `cppverify::decreases(expr [, expr...])` | After loop `)` or function `)` | Termination measure. Tuple form is lex-ordered. Required on executable loops. |
| `cppverify::decreases(*)` | After an executable loop or function | Allows divergence; proofs then cover terminating executions (`[partial]`) |
| `cppverify::type_invariant(expr)` | Inside class/struct body | Per-instance invariant injected at function boundaries |
| `cppverify::ghost { ... }` | Statement | Ghost block — proof steps, stripped by CodeGen |
| `cppverify::ghost T x = e;` | Statement | Function-scoped ghost variable |
| `cppverify::check(expr)` | Statement | Verification condition (not a runtime check) |
| `cppverify::check(expr) by { ... }` | Statement | Proves `expr` from a local proof whose other facts are discarded |
| `cppverify::calc { e0; op { ... } e1; ... }` | Statement | Chain of proved steps concluding `e0 R en` |
| `cppverify::reveal_with_fuel(fn, n)` | Inside ghost blocks | Locally raise Z3 unfolding depth for spec function `fn` |
| `cppverify::spec T f(...)` | Declaration | Pure spec function — interpreted by verifier only |
| `cppverify::proof void f(...)` | Declaration | Ghost proof function — establishes lemmas |
| `cppverify::forall(i, lo, hi, expr)` | Expression | Bounded universal quantifier |
| `cppverify::exists(i, lo, hi, expr)` | Expression | Bounded existential quantifier |
| `cppverify::forall(i, expr)` / `cppverify::exists(i, expr)` | Expression | Quantifier over all mathematical integers |
| `cppverify::trigger(term)` | Inside a quantifier body | Makes `term` the pattern that instantiates the quantifier |
| `cppverify::choose(i, [lo, hi,] expr)` | Expression | Some integer satisfying `expr` (Hilbert ε) |
| `cppverify::old(expr)` | Inside `cppverify::post` or `cppverify::invariant` | Value of `expr` at function entry |
| `cppverify::result` | Inside `cppverify::post` | Return value of the enclosing function |
| `cppverify::seq`, `set`, `multiset`, `map` | `<cppverify.h>` | Mathematical collections for specifications and ghost code |

## Function Contracts: pre / post / modifies / aliases / recommends

```cpp
void swap(int* a, int* b)
  cppverify::pre(a != nullptr && b != nullptr)
  cppverify::modifies(*a, *b)
  cppverify::post(*a == cppverify::old(*b) && *b == cppverify::old(*a))
{
    int t = *a; *a = *b; *b = t;
}
```

- `cppverify::pre(expr)`: precondition. `expr` must be contextually convertible to bool.
- `cppverify::post(expr)`: postcondition. `expr` may reference `cppverify::result` (return value) and `cppverify::old(x)` (pre-state).
- `cppverify::modifies(lvalue, ...)`: frame condition — see §Pointers and Memory below.
- `cppverify::aliases(p, q)`: see §Pointers and Memory below.
- Multiple `cppverify::pre` / `cppverify::post` / `cppverify::modifies` clauses are conjuncted.
- Parsed after the function declarator's `)` and before `{`.
- A parameter named in `cppverify::post` denotes its value at entry, as in ACSL, even
  when the body assigns the parameter; callers can therefore use the
  postcondition.

### Behaviors

```cpp
int abs_value(int x)
  cppverify::behavior(nonnegative, x >= 0)
    cppverify::post(cppverify::result == x)
  cppverify::behavior(negative, x < 0)
    cppverify::pre(x > -2147483647 - 1)
    cppverify::post(cppverify::result == -x)
  cppverify::complete_behaviors
  cppverify::disjoint_behaviors
{
  return x < 0 ? -x : x;
}
```

- `cppverify::behavior(name, assumes)` starts a case, as ACSL behaviors do. The `cppverify::pre`
  and `cppverify::post` clauses after it, up to the next behavior, apply where the
  assumption holds: `assumes -> pre`, and `old(assumes) -> post`.
- `cppverify::complete_behaviors` requires that some behavior applies to every input the
  preconditions admit; `cppverify::disjoint_behaviors` that no two do. Either may list
  the behaviors it relates, e.g. `cppverify::disjoint_behaviors(low, high)`. Both are
  checked at function entry.

### Verdicts that rest on other contracts

A caller's proof uses its callees' contracts. When a callee's own
verification does not establish its contract, a caller whose proof relies on
it is `Unresolved` with reason `callee.contract`.

```cpp
[[cppverify::trusted]] int clamp_byte(int v)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 255);
```

`[[cppverify::trusted]]` (a standard C++ attribute, like Verus's
`#[verifier::external_body]`) marks a contract as assumed: on a declaration
the contract holds at every call (whose preconditions are still checked); on
a definition the body is compiled but not verified; on a proof function the
postcondition is an axiom. A spec cannot be trusted, since its definition is
its meaning. The mark is written on each function: `#pragma clang attribute`
cannot apply it to a region. A trusted function reports `Trusted: f (contract assumed, not
verified)`, and every verdict that relies on it, directly or through verified
callees, carries `[trusts=f]`. A contract without a definition and without
the mark is not assumed: a warning names it, and its callers are
`Unresolved` with reason `callee.contract`. A trusted contract writes only
its `cppverify::modifies` footprints; without them it writes nothing through a pointer
or reference to const, and is taken to write the whole heap through a
mutable one (see `cppverify::modifies` below).

A function the verifier does not verify (no contract, assertion, ghost code,
or loop contract) may call a contracted one. Its precondition is then
assumed at that call, not checked, and the callee's verdict says so, as
Frama-C reports a property valid under hypotheses:
`Verified: f [backend=z3] (its precondition is assumed, not checked, at calls
from unverified g, h)` (JSON `unverified_callers`). Nothing else changes: the
callee's proof stands for every call that establishes its precondition.

A proof that holds only because no execution reaches the claim is reported
with `[vacuous]` and a warning. Assumptions enter a proof only at the
preconditions and type invariants, behavior assumptions, and trusted
contracts (a verified callee always returns), so every `Verified` result is
checked at each: an unsatisfiable precondition, a function whose end no
execution reaches, a behavior whose assumption contradicts the preconditions
(its postconditions are never checked; warning only), and a trusted call
whose contract contradicts the state of the call. Unreachable code alone
is not flagged. Under BMC the same checks run on the program unrolled to
the bound, as Kani reports an unreachable check, and a `BoundedSafe`
result that no execution finishes within the bound is `[vacuous]` too
(`no execution finishes within N loop iterations`).

A proof never rests on itself. Every fact a proof assumes (a callee's
contract, a spec's definition, frame, or postcondition, an inductive
predicate's unfolding) is established only by verdicts whose own facts are
established, starting from none. Proofs may rely on each other only through
a checked measure, as in Dafny's clusters: specs and proof functions that
reach each other through bodies, contracts, and proof blocks, and share
`cppverify::decreases` clauses of one length, form a cluster. Every call between them
must lower the measure, and each uses another's postcondition, and a
recursive spec's definition, only where that one's measure is lower, so
their proofs hold together by well-founded induction. A lemma about a spec
that the spec's own proof uses therefore works with lexicographic measures:

```cpp
cppverify::proof void total_nonneg(int n);

cppverify::spec int total(int n)
  cppverify::decreases(n, 0)
  cppverify::post(cppverify::result >= 0) by { if (n > 0) total_nonneg(n - 1); }
{
  return n <= 0 ? 0 : total(n - 1) + n;
}

cppverify::proof void total_nonneg(int n)
  cppverify::decreases(n, 1)
  cppverify::post(total(n) >= 0)
{
  if (n > 0)
    total_nonneg(n - 1);
}
```

The lemma may unfold `total(n)` since `(n, 0)` is below `(n, 1)`, and the
block may call the lemma at `n - 1` since `(n - 1, 1)` is below `(n, 0)`.
Without a shared measure such proofs are a circle, and every verdict on it
is `Unresolved` with reason `proof.cycle`. Frames (`cppverify::reads`) are never used
this way.

## Loop Contracts: invariant / decreases

<!-- cppverify-example: fragment -->

```cpp
while (i < n)
  cppverify::invariant(2 <= i && i <= n)
  cppverify::invariant(fib.size() == i)
  cppverify::decreases(n - i)
{ ... }
```

- `cppverify::invariant(expr)`: must hold on entry and be preserved by each iteration.
- `cppverify::decreases(expr [, expr...])`: termination measure. Single expression must be non-negative and strictly decreasing. Tuple form is lex-ordered: `cppverify::decreases(a, b)` means `(a, b)` strictly decreases lexicographically, and only the first component that changes must stay non-negative.
- Verification is total correctness, as in Verus: every executable loop needs
  `cppverify::decreases`. Without one the function is `Unresolved` with reason
  `decreases.missing`, unless BMC proves the loop's unwinding.
  `cppverify::decreases(*)` on a loop or an executable function allows divergence; the
  proof then covers only executions that terminate, and that function and
  every caller are reported `Verified ... [partial]` with a warning (JSON
  `"partial": true`). Ghost and proof loops cannot use `cppverify::decreases(*)`.
- `cppverify::modifies(...)` after a loop's invariants is ACSL's `loop assigns`: the
  cells, ranges, and objects the loop may write, read in each iteration's
  state. Each iteration starts with every other cell unchanged since the loop
  began, and must end (and `continue`) that way, so a range such as
  `a[0 : i]` can describe progress:

<!-- cppverify-example: fragment -->

```cpp
for (int i = 0; i < n; i = i + 1)
  cppverify::invariant(0 <= i && i <= n)
  cppverify::modifies(a[0 : n])
  cppverify::decreases(n - i)
{
  a[i] = 0;
}
```

  Without `cppverify::modifies`, a loop writes only the objects its stores and calls
  reach, inferred from the body: every other object keeps its value without
  an invariant saying so.

`do` loops place the clauses between the trailing condition and its semicolon:

<!-- cppverify-example: fragment -->

```cpp
do {
    i = i + 1;
} while (i < n)
  cppverify::invariant(i >= 1 && i <= n)
  cppverify::decreases(n - i);
```

The body executes once before invariant establishment. CppVerify verifies that
mandatory execution from the concrete incoming state, establishes the invariant
after it, and then applies the ordinary modular `while` rule to every subsequent
iteration. `cppverify::old(expr)` in any loop invariant denotes the enclosing function's
entry state, not the previous iteration. A function local has no value at
function entry and is rejected inside `cppverify::old(...)`; snapshot such a value in an
ordinary local and refer to that snapshot without `cppverify::old`.

`return`, `break`, and `continue` may leave a `while` or `for` loop from an
arbitrary inductive iteration. A return checks the postcondition in its own
state, a break continues after the loop in its own state, and a continue ends
the iteration: it re-establishes the invariant and decreases the measure, after
running a `for` increment. `break` and `continue` in a `do` loop, whose first
iteration is lowered outside the loop, and ghost code leaving an executable
loop fail closed.

## Assertions: cppverify::check

<!-- cppverify-example: fragment -->

```cpp
cppverify::check(x > 0);
```

- Generates a verification condition (not a runtime check).
- In ghost blocks, used for proof steps: once proved, the condition is
  assumed for the rest of the function.
- A function without contract clauses is still verified when its body has a
  `cppverify::check`, ghost code, or a loop contract.

<!-- cppverify-example: fragment -->

```cpp
cppverify::check(sq(a) <= sq(b)) by {
    sq_monotone(a, b);
}
```

- `cppverify::check(c) by { proof }` proves `c` from a ghost proof, as Verus's
  `assert ... by` and Dafny's `assert ... by` do: the proof's facts (lemma
  posts, its own assertions, its locals) stay inside it, and only `c` holds
  afterwards. It is encoded as `if (*) { proof; assert c; assume false }
  assume c`, with the choice fresh in every execution, so BMC unrolling stays
  sound.

<!-- cppverify-example: fragment -->

```cpp
cppverify::check(cppverify::forall(k, 0, n, a[k] <= a[n - 1])) by {
    pair_ordered(a, n, k, n - 1);
}
```

- With a `cppverify::forall` as the condition, the proof is about one arbitrary value of
  its variable, as Verus's `assert forall ... by`: inside the block `k` is in
  scope, lies in `[lo, hi)`, and cannot be assigned; the block must establish
  the body for that `k`, and the whole `cppverify::forall` holds afterwards (universal
  generalization). An implication is a branch: `if (A(k)) lemma(k);`.

<!-- cppverify-example: fragment -->

```cpp
cppverify::calc {
    sq(a);
    <= { sq_monotone(a, b); }
    sq(b);
    == b * b;
}
```

- `cppverify::calc { e0; op { proof } e1; ...; en; }` proves each step `e(k-1) op ek`
  as an assert-by (the block is optional) and concludes `e0 R en`: `==` when
  every step is `==`, `<` or `>` when some step is strict, else `<=` or `>=`.
  Mixing `<`-like and `>`-like steps is rejected.

## Ghost Blocks

<!-- cppverify-example: fragment -->

```cpp
cppverify::ghost {
    lemma_fibo_monotonic(i, n);
    cppverify::check(fibo(i) <= fibo(n));
    cppverify::reveal_with_fuel(fibo, 3);
}
```

- Code inside `cppverify::ghost { }` exists only for verification.
- May contain `cppverify::check`, `cppverify::reveal_with_fuel`, spec/proof function calls, ghost variable declarations.
- May assign only ghost-local variables and their direct dot-fields; executable
  locals, globals, pointees, executable calls, and enclosing-function returns
  are rejected.
- Ghost loops require `cppverify::decreases`, because the loop is absent at runtime.
- Stripped entirely by CodeGen — zero runtime cost.
- `cppverify::ghost T x = e;` declares a ghost variable in the enclosing function scope,
  like Verus's `let ghost`: later ghost code, assertions, and loop invariants
  may name it, so an invariant can refer to a value from before the loop.
  Sema rejects any use from executable code.

## Spec Functions

<!-- cppverify-example: label fibo -->

```cpp
cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
    if (n <= 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}
```

- Pure mathematical functions used in contracts.
- Usable only in contracts, ghost code, and other `cppverify::spec` or `cppverify::proof`
  functions. A spec is never compiled, so Sema rejects a reference from
  executable code (a body, initializer, or default argument).
- Must be total (all paths return, termination proven via `cppverify::decreases`).
- No side effects, no mutation, no I/O. A spec may read memory through its
  pointer parameters but never write it; each call is evaluated in the heap
  state a load at that point would read (the current state, the entry state
  inside `cppverify::old(...)`, or the call-site state of a callee contract).
- Can be recursive (with `cppverify::decreases`). Its termination is proved without its
  own definition, so every recursive call must lower the measure whatever the
  spec's other calls return; a call inside `cppverify::forall` or `cppverify::exists` must lower it
  for every bound value. Functions of one kind (spec, proof, or executable)
  may recurse through each other when they share a measure of one length that
  every call within the cycle lowers.
- May declare `cppverify::reads(p, n)`: the cells `p[0..n)` it depends on, checked
  against its body (every load, and every range a heap-reading callee reads,
  lies inside). A write outside them leaves every application unchanged, and
  callers receive that frame at each store without unfolding the spec.
- Takes no `cppverify::pre`, `cppverify::modifies`, or `cppverify::aliases`: a spec is defined for every
  argument, and `cppverify::recommends` states its intended domain.
- May declare `cppverify::post(...)`, proved with its termination by well-founded
  induction on the measure (a recursive call assumes the post only where its
  measure is lower) and assumed at every application, including those
  inside the unfoldings of its definition that a proof receives (as Dafny's
  function postconditions): a lemma about `fibo(j)` may use
  `fibo(j - 2) >= 0` without naming it. A failed post demotes
  the proofs that relied on it (`spec.post`, or `spec.termination` for a
  recursive spec).
- Any `cppverify::post`, `cppverify::decreases`, or `cppverify::reads` clause of a spec definition may be
  followed by a proof block, `cppverify::post(Q) by { ... }`: ghost code that runs in
  that clause's check, after the facts the check assumes and before its
  obligations, as a proof function's body runs before its postcondition.
  It is where the solver gets the step it cannot find, such as a lemma at
  a chosen argument:

<!-- cppverify-example: fragment -->

```cpp
cppverify::spec int area(int a, int b)
  cppverify::post(a < 0 || b < 0 || cppverify::result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
{
  return mul(a, b);
}
```

  In a post block, `cppverify::result` is the value the body returns. An application
  of the spec (or of its recursion cycle) in a block assumes its
  postconditions where the measure is lower, which states the induction
  hypothesis at an argument of the user's choice. The block is ghost code:
  it may declare and assign its own locals, branch, assert, and call proof
  functions (whose preconditions it must establish), but not return, write
  memory, or assign a parameter. Its facts reach every obligation of the
  check. A block belongs to the definition, not to a declaration, and only
  a spec's clauses take one: other functions prove their contracts in their
  bodies.
- May declare `cppverify::when(c)`: the body defines the spec only where `c` holds,
  termination is checked there, and elsewhere its value is an uninterpreted
  function of its arguments. A post holds within the domain.
- **Integer semantics: mathematical (unbounded `Int` in Z3) by default.** See §Integer Semantics.
- Body is interpreted by the verifier as an axiom; not compiled.
- Can call other spec functions.
- Type-checked by Clang Sema like normal functions.

**Why termination must be verified:** A non-terminating spec function introduces a logical contradiction — Z3 can derive `bad(0) == bad(0) + 1`, therefore `0 == 1`, and from that prove anything. The `cppverify::decreases` clause is the only thing about a spec function that needs verification. Its body is the mathematical definition and is axiomatically true by construction once the spec terminates, which is why the termination check cannot use it: a diverging spec's equations can be contradictory exactly where it diverges. Non-recursive spec functions need no verification at all.

### Inductive predicates

```cpp
cppverify::spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

cppverify::spec bool reach(int a, int b)
  cppverify::inductive
  cppverify::post(!cppverify::result || a < 0 || a <= b)
{
  return a == b || cppverify::exists(c, edge(a, c) && reach(c, b));
}
```

- `cppverify::inductive` makes a spec returning `bool` the least predicate its body
  defines, as Dafny's `least predicate` and Coq's inductive propositions: it
  holds exactly where a finite derivation shows it. It needs no measure, so
  it describes reachability, derivability, or a process that may run forever
  (`n == 1 || (n > 1 && reaches_one(next(n)))`).
- The body returns a condition, under `if` and `else` at most, in which the
  predicate occurs only positively: as a conjunct or disjunct, a branch of
  `?:`, under `cppverify::exists`, or under a bounded `cppverify::forall`; never negated, compared,
  converted, in a condition, in an argument, or under a `cppverify::forall` without
  bounds. It takes no `cppverify::decreases` or `cppverify::when`, and it may read memory.
  Predicates that apply each other are defined together, each under the same
  conditions; a predicate never applies itself through a spec that is not
  inductive, since the conditions could not be checked there.
- Meaning: with `F` its body, `P(x)` is `cppverify::exists(h, P.step(h, x))`, where the
  generated spec `P.step(h, x)` is `h > 0 && F` with each application `Q(a)`
  of a predicate of its group read as `Q.step(h - 1, a)`: `F` applied `h`
  times to false. The conditions above make `F` monotone and continuous, so
  this union is the least fixpoint (Kleene's theorem).
- Proofs see `P` through its unfolding `P(x) == F(x)`, assumed at every
  application: one unfolding, both ways (introduction and inversion), in
  the memory state where the application is evaluated. An application that
  appears only inside an unfolding is unfolded once it is named, as in
  `cppverify::check(reach(2, 4));`. `cppverify::reveal(P)` gives the definition
  instead.
- Deeper unfolding, as Stainless unrolls recursive functions:
  `cppverify::reveal_with_fuel(P, n)` unfolds the applications inside unfoldings `n`
  levels deep, and a verdict that still depends on `P` (`spec.fuel`,
  `spec.hidden`, `counterexample.unchecked`) is retried with one more level
  at a time, up to four. An application at constant arguments, such as
  `cppverify::post(reach(1, 4))`, is decided by the counterexample check before
  solving, and the solver receives the unfoldings along the derivation it
  found. Every unfolding is a proved theorem, so none of this can make a
  false claim verify.
- The unfolding is not assumed on trust. As Isabelle's inductive package
  does, the verifier generates three proof functions for each predicate and
  proves them before any proof may rely on it:
  - monotonicity: a derivation of height `h` is one of every height
    `j >= h`, by induction on `h`;
  - case analysis: `P(x)` implies `F(x)`;
  - introduction: `F(x)` implies `P(x)`, at a height built for it: one more
    than the heights of the applications `F` uses, at the witnesses chosen
    for its existentials and the largest over its bounded universals (a
    generated recursive spec `P.bound` computes it).
  Every height and witness these proofs need is named, and every universal
  is introduced from a fresh value, so no solver has to invent one. They
  quantify only over the parameters an application changes. Success shows
  as `Verified: inductive predicate: P`; a failed rule is reported (as
  `P (monotonicity)`, `P (case analysis)`, or `P (introduction)`), `P` is
  `Unresolved` with reason `spec.inductive`, and so is every proof that
  relies on its unfolding.
- A postcondition states what every derivation satisfies and has the form
  `!cppverify::result || Q`. It is proved for `P.step` by induction on `h`, which is
  induction on derivations: with the definition of `P.step` visible, each
  premise (an application at a lower height) may assume it and is itself a
  derivation of its predicate. It then holds at every application of `P`. A
  failure is reported as `spec post by induction failed: P`, and proofs
  that rely on it are `spec.post`. A proof block on it,
  `cppverify::post(!cppverify::result || Q) by { ... }`, is the induction step: it runs for a
  derivation of `x` whose premises satisfy `Q`, and in it `P` is the
  predicate itself (a premise is a derivation of it).
- `Q` may apply `P` and the predicates defined with it, as in transitivity:
  `cppverify::post(!cppverify::result || cppverify::forall(c, !reach(b, c) || reach(a, c)))`. There they are
  seen through their unfoldings, which rest on the proved rules, never
  through the postcondition being proved: `cppverify::post(!cppverify::result || !bad(n))` on a
  predicate with `bad(0)` true fails.
- A counterexample is certified against the true definition of `P` either
  way. When the arguments `P`'s derivations can reach from `v` are finitely
  many, the check computes the least fixpoint over them: every value starts
  false and becomes true once its body holds, until nothing changes (an
  existential's witnesses are found where its body's comparisons change,
  with the premises taken as true). This decides `climb(3, 4)` false,
  mutual predicates, and walks over memory. Otherwise `P(v)` true is shown
  by a derivation height found by trying heights, and `P(v)` false by a
  postcondition of `P` that excludes it; the counterexample then rests on
  that postcondition, and if it is not established the failure is
  `Unresolved` with reason `spec.post`. When none of these decides, the
  message names the application (`whether odd(4) holds: ...`) and the kind
  of postcondition that would.
- When unfolding cannot settle a claim, the reason says so.
  `backend.invalid-result` means the solver's model breaks a fact the
  solver was given. A model that keeps every fact but needs `P(v)` true
  where the least fixpoint is false (derivations that go round forever)
  is `spec.fuel`: `every counterexample found needs P(v) to hold, but no
  derivation shows it`, which only induction shows; a postcondition
  `!cppverify::result || Q` or a lemma proved by induction supplies it.

### Automatic induction and counterexamples too large to compute

When no finite unfolding settles a claim about a recursive spec, the verifier
tries well-founded inductions over it, as Dafny's automatic induction and
Lean's and Isabelle's functional induction do: the claim at every value
smaller in a measure, everything else fixed. The measure is a recursive
spec's own `cppverify::decreases` at the application the claim makes, and the
hypothesis is also given at the values the spec's recursion reaches, through
the other members of its recursion group and under quantifiers; strong
induction on an integer variable is tried too. Smaller means smaller by the
decrease relation of termination checks, which has no infinite descending
chain, so no induction proves a false claim; the hypothesis is the
function's own claim, without the facts the verifier added. A verified
result names the induction:

```cpp
cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
    if (n <= 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}

cppverify::proof void grows(int n)   // Verified ... [by induction following fibo]
  cppverify::pre(n >= 3)
  cppverify::post(fibo(n) >= n - 1)
{
}
```

A claim whose step needs a stronger statement (an accumulator, say) stays
`spec.fuel`; the message names the inductions tried and, for a proof
function, shows a body to start a proof by induction from.

A counterexample whose spec values cannot be computed (`pow2(1000000000)`
has a billion bits) is confirmed by a proof at its input once every function
is verified: with its values fixed, the facts its query states assumed, and
the postconditions of the established proof functions instantiated where
they speak of the same applications, the solver proves that the claim fails
there. The failure rests on those facts and contracts:

<!-- cppverify-example: fails small_power -->

```cpp
cppverify::spec int pow2(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= n + 1)
{
    return n <= 0 ? 1 : 2 * pow2(n - 1);
}

cppverify::proof void small_power(int n)   // fails at n >= 1000000000, confirmed by proof
  cppverify::pre(n >= 1000000000)
  cppverify::post(pow2(n) < 1000)
{
}
```

Where no proved fact settles it, the claim may as well be true for want of a
lemma: it stays `spec.fuel`, and the message shows the proposed input and
says both. A lemma that refutes the claim settles it:

<!-- cppverify-example: fails fibo_small -->

```cpp
cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
    if (n <= 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}

cppverify::proof void fibo_at_least_5(int n)
  cppverify::pre(n >= 5)
  cppverify::post(fibo(n) >= 5)
  cppverify::decreases(n)
{
    if (n >= 6)
        fibo_at_least_5(n - 1);
}

cppverify::proof void fibo_small(int n)   // fails at n = 1000000000, confirmed with
  cppverify::pre(n >= 1000000000)         // the contract of fibo_at_least_5
  cppverify::post(fibo(n) < 5)
{
}
```

A lemma is instantiated where its postcondition speaks of the same spec
application as the claim, and what is instantiated is what its verification
proved: its postconditions wherever every assumption its proof started from
holds, the generated ones included (a pointer parameter is null or valid,
`valid(p, n)` gives `n >= 0`, mutable pointers are distinct objects, a record
satisfies its type invariant). A parameter the match leaves open ranges over
every value. So a lemma is never used where an assumption of its proof fails,
whatever its parameters' types, and it applies wherever some value of the
open parameters meets those assumptions.

### `cppverify::recommends` — soft preconditions for spec functions

```cpp
cppverify::spec int safe_div(int a, int b)
  cppverify::recommends(b != 0)
{
    return a / b;
}
```

- `cppverify::recommends` clauses do **not** generate VCs at call sites. Spec functions remain total.
- They are checked only on verification failure of any function calling the spec, and reported as warnings.
- Cheap UX recovery — gives users feedback that they probably misused a spec function without imposing real preconditions.

## `constexpr` Functions as Automatic Spec Functions

<!-- cppverify-example: fragment -->

```cpp
constexpr bool is_power_of_two(int n) {
    return n > 0 && (n & (n - 1)) == 0;
}

void allocate(int n)
  cppverify::pre(is_power_of_two(n))
{ ... }
```

Any uncontracted `constexpr` definition is automatically available as a spec
function — no `cppverify::spec` or re-declaration. It is lifted where
verification uses it: in a contract, a verified body, a type invariant, or
another lifted function. The `constexpr` functions of a header that nothing
verified uses are never examined. A `constexpr` function with
`cppverify::pre`/`cppverify::post` clauses remains a modular executable function so its contract
cannot be bypassed through implicit lifting.

**Soundness:** Clang enforces the restrictions on a `constexpr` definition.
CppVerify additionally unfolds symbolic calls for path-sensitive C++ definedness
and uses finite call-site equations, so recursive calls do not introduce an
unbounded self-triggering axiom.

**Integer semantics — machine integers:** A lifted `constexpr` function
retains C++ integer semantics — `int` has its target width, unsigned arithmetic
wraps, and signed overflow is undefined. The verifier uses machine-integer
values but unfolds the function into the path-sensitive definedness checker at every call;
an overflowing call is rejected rather than interpreted as signed wraparound.
For C++17 signed left shift, a nonnegative value may set the sign bit when the
shifted mathematical value fits the corresponding unsigned type.

**Contrast with explicit `cppverify::spec`:** `cppverify::spec int fibo(int n)` uses mathematical integers (Z3 `Int`, unbounded). Users pick:
- Want fast verification with abstract math semantics → write `cppverify::spec`.
- Want code reuse with runtime-honest semantics → write `constexpr` (and accept the machine-integer encoding cost).

Calls retain the callee's integer semantics, in contracts and in ghost and
proof code alike: a mathematical spec result (or collection length, element,
or count) stays unbounded, operations involving it are exact, and the
implicit usual arithmetic conversions do not bound it. A mathematical value
never wraps into a machine type. Storing it in a ghost or proof variable,
passing it to a machine parameter (of a proof function or a lifted
`constexpr`), returning it, casting it explicitly, or using it as a bitwise
operand converts it, and that conversion carries an `overflow` obligation
that the value fits. So in a proof function `s.subrange(0, s.len() - 1)` is
exact, while `int x = s[0];` must show that the element fits in an `int`.

This is genuinely a CppVerify advantage over Verus — Verus forces users to maintain two separate bodies; we let one body do double duty *or* let users opt into a clean math-integer spec.

**Compile-time partial evaluation:** When a contract contains a `constexpr` call with all-concrete arguments, Clang evaluates it at compile time before the verifier sees it:

<!-- cppverify-example: fragment -->

```cpp
write_data(buf, 512);
// At this call site, Clang evaluates is_power_of_two(512) → true.
// Z3 receives pre(true) for this site — no SMT reasoning needed.
```

This is unique to being inside the compiler.

## Proof Functions

<!-- cppverify-example: with fibo -->

```cpp
cppverify::proof void lemma_fibo_monotonic(int i, int j)
  cppverify::pre(i <= j)
  cppverify::post(fibo(i) <= fibo(j))
  cppverify::decreases(j - i)
{
    if (i < j)
        lemma_fibo_monotonic(i, j - 1);  // fibo(i) <= fibo(j - 1) <= fibo(j)
}
```

- Ghost functions that serve as proofs.
- Must terminate (proven via `cppverify::decreases`).
- Body establishes that precondition implies postcondition.
- Can call other proof functions and spec functions.
- May mutate local proof values, but cannot write executable memory/global
  state or call executable functions.
- Every proof-function loop requires `cppverify::decreases`.
- Not compiled — exist only for verification.
- **Integer semantics:** machine integers (matches `exec`).

## Quantifiers: forall / exists

<!-- cppverify-example: fragment -->

```cpp
cppverify::post(cppverify::forall(i, 2, n, ret[i] == ret[i-1] + ret[i-2]))
//   forall(binder, lo, hi, body)
//   means: ∀i. lo ≤ i < hi → body

cppverify::pre(cppverify::exists(j, 0, n, arr[j] == target))
//   means: ∃j. 0 ≤ j < n ∧ body

cppverify::post(cppverify::forall(k, sq(k) >= 0))
//   forall(binder, body): ∀k ∈ ℤ. body
```

- `binder` is a fresh mathematical integer, scoped to `body`.
- `lo` and `hi` must be integer; `body` must be bool.
- Without bounds the quantifier ranges over all mathematical integers. A
  counterexample to one is certified exactly when its body depends on its
  binders through linear arithmetic, comparisons, memory and collection
  reads, and other quantifiers, nested to any depth: once the model fixes
  everything else, each read is one of finitely many constant pieces, which
  leaves a sentence of Presburger arithmetic that the certifier decides. A
  spec applied to a binder is unfolded by its definition, or, where the
  body is monotone or antitone in it, taken as true or false: when the body
  can hold (or fail) at finitely many binder values only, found where its
  comparisons change, evaluating it there decides the quantifier. A witness
  among the values where those comparisons change, or near zero, also
  decides it. Otherwise (a product or quotient of binders, say) it is
  `counterexample.unchecked`.

### Triggers

<!-- cppverify-example: fragment -->

```cpp
cppverify::pre(cppverify::forall(k, 0, n, cppverify::trigger(a[k]) > 0))
```

- `cppverify::trigger(term)` marks `term` as the pattern that instantiates the
  quantifier, as Verus's `#[trigger]` does. It must be a memory read, a
  collection read (`s[k]`, `contains`, `count`, map `[]`), or a call of a
  recursive spec function, and it must mention a quantified variable; other
  marks are ignored with a warning (a non-recursive spec is replaced by its
  body, so mark a term of the body). Several marks in one body form one
  multi-pattern. Without marks the solver chooses patterns itself.
- `--profile-quantifiers` reruns each query the solver left unresolved and
  reports how often each quantifier was instantiated, and up to which
  generation (`note: the quantifier at L:C was instantiated N times, up to
  generation G`; JSON `quantifier_profile`), which exposes matching loops.
- Patterns steer the solver; they never change meaning. They are not part
  of archives or semantic hashes.

### choose

```cpp
cppverify::spec int half(int n) { return cppverify::choose(k, 2 * k == n); }
cppverify::spec int index_of(const int *a, int n, int x) { return cppverify::choose(k, 0, n, a[k] == x); }
```

- `cppverify::choose(k, body)` is an integer for which `body` holds, when one exists,
  and otherwise an unspecified integer (Hilbert ε); `cppverify::choose(k, lo, hi, body)`
  chooses in `[lo, hi)`. Each `cppverify::choose` is a function of the values its body
  mentions, so it is the same for the same values.
- The verifier knows only that: a claim true for some choices but not all
  fails with a certified counterexample for another choice.
- `cppverify::choose` exists only for verification; Sema rejects it in executable code.

## Pointers and Memory

CppVerify supports verification of pointer-manipulating code in the MVP via three coupled mechanisms.

### 1. Heap model

The verifier represents memory as a Z3 array (the "heap"). Pointer dereferences become array operations:

- `*p = v` → conceptually `mem' = store(mem, p, v)`
- `*p` (read) → `select(mem, p)`

This is internal to the verifier — users never write the heap directly. Aliasing correctness comes for free from Z3's array theory: if `p == q`, then `select(mem, p) == select(mem, q)`.

Pointer addition/subtraction and array subscripting use mathematical target-byte
addresses, so address arithmetic itself cannot wrap. A typed `T*` step is
multiplied by Clang's target `sizeof(T)` and record fields add their target
byte-layout offset. The supported buffer fragment includes `p + i`, `p - i`,
`*(p + i)`, and `p[i]`. Executable pointer-pointer subtraction is additionally
supported for positions in one object. Both operands must have one origin
(below), and each must lie in its origin's object, one past the end included:
`[0, n]` for a `valid(p, n)` extent, `[0, 1]` for a single object. Pointers
into local or dynamic storage share an origin when they share a lifetime
identity. Pointers into different parameters' or globals' objects may still
lie in one caller array, which the object model does not describe, so their
difference is `construct.unsupported`, not an error. The target-byte
difference is divided by `sizeof(T)`, proved representable by target
`ptrdiff_t`, and then materialized as a machine value. Pointers loaded from
memory (no known origin), subtraction inside explicit specs or lifted
`constexpr` functions, pointer compound assignment, and forged pointer/integer
casts remain rejected.

At modular calls, a callee `valid(q, length)` extent can be instantiated from
`q = p + offset` only after proving a same-root nonnegative subrange with
`offset + length <= n`. Empty one-past slices, acyclic read-only forwarding,
exact-cell slice writes, and writes to a whole sub-slice or a symbolic range
are supported; the call frames every cell outside the written region.

For direct local scalar `new`/`delete`, the value heap is accompanied by
SSA-versioned metadata maps:

- address → allocation lifetime identity;
- allocation identity → numeric base, live/dead, target size, and target
  alignment;
- allocation identity → issued/not-issued, so a dead lifetime token is never
  reused;
- address → initialized/uninitialized.

Ordinary throwing scalar `new` chooses a non-null aligned base whose target-byte
range has no live owner, records the metadata, and initializes the value only
when C++ initialization does. A read requires current liveness and
initialization. Each supported local pointer has an SSA provenance companion
that retains its producing lifetime identity. Matching-pointee copies,
reassignment, conditional selection, and `nullptr` update address and
provenance together. A store requires the byte owner to match the current
companion and marks owned storage initialized. `delete` requires null or the
matching direct live allocation base and ends the identity in a fresh liveness
version. This permits numeric-address reuse without contradictory timeless
validity assumptions or revival of a dangling pointer, and proves simultaneous
allocations disjoint.

The direct allocation boundary covers complete non-volatile integer/enum
objects up to 256 target bytes, direct local pointer initialization,
same-pointee local copies/reassignment/conditionals/null, direct
dereference/store/delete, and equality/null observation. Aliases retain the
same identity, so deletion through any alias invalidates all of them.
Type-erasing or indirect copies, arithmetic-derived ownership, arrays,
placement/nothrow allocation, non-trivial objects, pointer reassignment in
loops, and allocation/deallocation inside loops fail closed.

A checked modular interface admits a direct dynamic pointer argument to a
verified, non-allocating executable callee with a matching scalar pointer
parameter. Identity is substituted into call-site validity checks, and
ordinary pre/`cppverify::modifies`/post abstraction controls the value heap. A recursive
VCR scan admits direct scalar access, acyclic direct-pointer forwarding, and
executable/spec helpers over loaded scalar values. It rejects offset/subscript
access, pointer copies/rebinding, deallocation, recursive scan cycles, nested
pointer-result calls, ghost use, proof/external contracts, and other ways the
scalar identity or extent could be lost.

Direct/conditional/null returns of dynamic formals are supported. The modular
call freshens address and provenance result targets together; generated
validity binds the provenance to the byte owner, while an explicit result
equality relates the returned address to a caller argument. Frame containment
and subsequent modular writes additionally require that provenance to equal an
identity in the caller's owned-allocation set. A foreign or weakly specified
result therefore cannot manufacture ownership merely by being assigned to a
previously dynamic local.

VCR also carries an inferred `FreshOwnedReturn` effect for a narrow factory
boundary. The effect is never accepted from contract text. A body-present,
non-external, non-proof executable function receives it only when a
conservative acyclic VCR analysis proves that every path returns null or the
exact live base of its sole fresh scalar allocation, fully initialized, with
no pointer parameter, secondary escape, explicit frame, arithmetic-derived
result, extra allocation, or intervening unsupported call. A direct store may
complete initialization. Calls to an already inferred factory can be returned
directly or through matching local aliases, so factory forwarding composes
only along an acyclic call graph.

At such a call, passivization creates a never-issued lifetime identity and a
fresh pointer result, proves target alignment and disjointness from all live
represented storage and declared extents, installs base/size/alignment,
byte-owner, liveness, and initialization metadata, and changes only the new
scalar cell in the value heap. A nullable summary guards those updates. The
callee's ordinary postconditions still specify null correlation and the
pointee value; ownership inference supplies lifetime authority, not an
unstated functional result. The caller may mutate and delete the result, while
double delete and every stale alias remain rejected.

Memory accesses are checked by default on every backend (`--check-ub`, the
default; `--no-check-ub` turns it off, leaving only the core expression
definedness checks). `valid(p, n)` in a precondition declares a buffer
extent: `p` points to `n` objects. `<cppverify.h>` provides it as
`cppverify::valid` for every pointee type (verification-only, like the spec
collections); a user-declared `cppverify::spec bool valid(T *p, int n)` is the same
marker. It entails `n >= 0`; a positive extent
entails non-null abstractly valid storage, while extent zero permits null.
Every access rooted at `p` must then prove its index lies in `[0, n)`.
Modular sub-slices prove nonnegative containment, and pointer difference
positions prove the inclusive one-past range `[0, n]`.

A pointer without a declared extent addresses one object, as Frama-C's RTE
`\valid` guards and Verus permissions require. An access through it must lie
in that object: the object its origin names when the origin is known (a
parameter's entry object, however the pointer was stepped, copied, or
chosen), otherwise some parameter's object or the single object at a base
known to be valid (a callee or external result).
Pointer arithmetic must stay within the same object's closed range
`[0, size]`, so forming `p + 10` from `valid(p, 2)` fails even without a
dereference. Objects lie at positive addresses below `2^64`. A caller
discharges a callee's single-object validity by showing its argument lies in
one of its own objects. Abstract storage is initialized; represented local
and dynamic storage keeps its metadata checks.

**Pointer origins.** Every pointer variable has, at every point, the objects it
may address: its origins, as CompCert's blocks and Frama-C's base addresses.
A pointer parameter starts with its entry object and a global's address with
the global; arithmetic keeps the origin, assignment copies it, and branches
and loops join the possibilities. A pointer loaded from memory or returned by
a call has no known origin. Origins decide three things:

- an access or a step must stay in its origin's object, so `*q` one past the
  end of `a` is rejected even where another object starts;
- a pointer difference needs one origin on both sides;
- a loop writes only its stores' origins (and, with a function `cppverify::modifies`,
  only where they meet it), so every other object keeps its value without
  an invariant.

A variable that may hold either of two origins carries a hidden companion
that names which. A loop that moves a pointer gets two generated invariants,
proved like the user's: such a companion stays among the possible origins,
and the pointer stays a whole number of elements from its origin's start. An
invariant still bounds pointers by address, and an address alone does not say
where a pointer came from: when a walker may be in either of two objects,
relate it to the condition that chose, as in `s ? q == a + i : q == b + i`.

The marker must be a positive top-level conjunction clause on a bare pointer to
a complete object type. At most one marker may describe each pointer. Shifted,
disjunctive, conditional, or duplicate markers fail closed rather than creating
unconditional extent assumptions.

### 2. Implicit non-aliasing default

When a function has multiple mutable address parameters, the verifier
*implicitly* assumes their complete object ranges do not overlap at function
entry. Address parameters currently include raw pointers and supported scalar
lvalue references.

```
cppverify::pre(p != q && p != r && q != r && ...)   // for all distinct mut ptr/ref pairs
```

- The caller's verification must establish these inequalities. Calling `swap(p, p)` fails the call's `aliasing` check.
- A pointer carrying a `valid(p, n)` extent contributes the
  whole extent (`n * sizeof(T)` bytes) as its complete object, so the pair is
  disjoint unless either pointer is null or either extent is empty. Callers
  prove disjointness of the extents they pass. An `cppverify::aliases` pair keeps the
  single-object rule and may share storage, as `memmove` does.
- **This is NOT the C++ `__restrict__` keyword.** `__restrict__` is a compiler optimization hint affecting codegen; the implicit assumption above is a verification-level precondition affecting correctness. The keyword `__restrict__`, if present, is a no-op for verification.

### 3. `cppverify::aliases(p, q)` opt-out

If a function legitimately accepts aliased parameters, declare it:

```cpp
void copy_or_self(int* dst, int* src)
  cppverify::aliases(dst, src)
  cppverify::pre(dst != nullptr && src != nullptr)
  cppverify::modifies(*dst)
  cppverify::post(*dst == cppverify::old(*src))
{
    *dst = *src;
}
```

The `cppverify::aliases(dst, src)` clause disables the implicit `dst != src` precondition
for this function. The body must verify under both `dst == src` and `dst != src`.
The same rule applies to supported scalar lvalue-reference parameters.

### 3a. Scalar lvalue references and automatic scalar objects

Contracted executable free functions support `T&` and `const T&` parameters
when `T` is `bool`, integral, or enum. The reference binding lowers to an
immutable VCR address. A value use is a heap load, assignment is a heap store,
and `cppverify::old(ref)` reads through the same address in the entry heap.

Every reference receives a generated non-null, live, and initialized entry
precondition. Distinct address parameters are object-range disjoint by default
when at least one is mutable; `cppverify::aliases` permits the same complete object.
`cppverify::modifies(ref)` is an open region rooted at the referent, matching
`cppverify::modifies(*p)`.

A reference formal may bind to another supported reference, an initialized
ordinary scalar local, or a direct pointer dereference. Local `T&`/`const T&`
declarations may bind the same direct forms, may chain through other local
references, and snapshot a raw pointer's address at the declaration. Reassigning
that pointer therefore does not rebind the reference.

Only locals whose addresses are needed are spilled out of scalar SSA. Each such
local becomes an automatic `VAllocateStmt` with a fresh lifetime identity,
target size/alignment, byte ownership, liveness, and initialization metadata.
It is disjoint from incoming address parameters and every simultaneously live
allocation. All reads and writes then use heap loads/stores; a defensive VCR
check rejects accidental scalar use of the same local. Lifetime is
conservatively extended to function return, which is unobservable under the
non-escaping boundary.

A provenance-backed scalar actual permits an open-region `cppverify::modifies(ref)` or
`cppverify::modifies(*p)` footprint to be framed as its exact scalar cell only after the
callee passes the structural non-escape scan. Immutable local reference aliases
are tracked transitively by that scan and retain the same owned lifetime
identity.

Addressable local declarations inside loops, `cppverify::old(local)`, `cppverify::old(local_ref)`,
subscript/field/conditional bindings, temporaries, reference returns,
address-taking, rvalue references, and non-scalar referents remain fail-closed.
An outer automatic local and a local reference declaration may be used inside a
loop. Recursive executable bodies that allocate an automatic object or store
through references fail closed until the termination collector models heap
state updates.

### 4. `cppverify::modifies(...)` frame condition

```cpp
void incr_first(int* a, int* b)
  cppverify::pre(a != nullptr && b != nullptr && *a < 2147483647)
  cppverify::modifies(*a)              // promises: only writes to *a; *b unchanged
  cppverify::post(*a == cppverify::old(*a) + 1)
{
    *a = *a + 1;
}
```

- `cppverify::modifies(X, Y, Z)` lists every footprint the function may write to.
  Anything not listed is preserved.
- Every store to memory the function did not create itself (its own locals
  and allocations) must lie in a footprint, as Frama-C's WP checks
  `assigns`; a function without `cppverify::modifies` stores only to its own storage.
- A callee whose writes are not stated, because its contract has no
  `cppverify::modifies` while it takes a mutable pointer or reference and may write
  (a trusted contract, or a verified function that calls such a callee), is
  treated as writing the whole heap at a call: a caller with its own
  `cppverify::modifies` cannot call it, and a caller without one forgets every cell.
  With a `valid` extent on such a callee the call is not supported.
- Footprints:
  - a cell: scalar `ref`, `p->field`, or `p[i]`, at its exact address;
  - a range `p[lo : n]`: the `n` elements from `p[lo]`, half-open
    `[lo, lo + n)` (Clang's array-section syntax);
  - a region `*p`: the object `p` addresses, which is its `valid(p, n)`
    extent when it has one and otherwise one object. A region of a single
    scalar object is one cell.
- Inside the callee every store must lie in a footprint, read in the entry
  state, so reassigning a pointer cannot widen the frame; a footprint of a
  callee must lie within the caller's own frame (index-based containment of
  ranges and extents).
- At a call, the caller's heap changes only inside the callee's footprints
  instantiated with the arguments: a cell or range is exactly those cells, a
  region is the argument's extent (or one object). Every other cell keeps its
  value, and specs with `cppverify::reads` clauses outside the footprints keep theirs.
  When every footprint is a cell, the effect is a chain of stores of fresh
  values; otherwise it is a frame relation over the regions. Region
  footprints need the object model: under `--no-check-ub` a call with one
  forgets the whole heap.
- Preconditions and `cppverify::old(parameter)` use entry actual arguments, and so does
  a parameter named in a postcondition.
- General reference binding and member-function effects are not yet in the
  verified subset.

### Worked example

```cpp
void swap(int& a, int& b)
  cppverify::modifies(a, b)
  cppverify::post(a == cppverify::old(b) && b == cppverify::old(a))
{
    int t = a;
    a = b;
    b = t;
}

int compute() {
    int x = 5;
    int y = 10;
    int z = 100;
    swap(x, y);
    // Verifier knows:
    //  - x and y are distinct objects (implicit non-aliasing default)
    //  - swap modified only x and y
    //  - therefore z is unchanged
    cppverify::check(z == 100);          // verifies
    cppverify::check(x == 10 && y == 5); // verifies from post
    return x + y + z;
}
```

`swap(x, x)` from a verified function fails the call's `aliasing` check.
Binding a reference to a local is supported; taking a local's raw address
(`&x`) is not, until lexical lifetimes and escapes are modeled.

## Type Invariants

```cpp
struct Coordinate {
    int x;
    int y;
    // must appear after the fields it names
    cppverify::type_invariant(x >= 0 && x <= 10000 && y >= 0 && y <= 10000);
};

int dist_sq(Coordinate p, Coordinate q)
  cppverify::post(cppverify::result >= 0)
{
    // Verifier auto-injects (lazy — only because the body accesses .x and .y):
    //   assume(p.x >= 0 && p.y >= 0);
    //   assume(q.x >= 0 && q.y >= 0);
    int dx = p.x - q.x;
    int dy = p.y - q.y;
    return dx*dx + dy*dy;
}
```

- `cppverify::type_invariant(expr)`: holds for every instance of the type at all times.
- `expr` may reference any field of the enclosing type by name.
- Must be contextually convertible to bool.

### Lazy injection

The verifier injects assume/assert only where they matter:

- `assume(invariant)` at the *first use* of an invariant-named field within a function body — not blindly at the function entry. A function that takes a `Coordinate` parameter but never reads `c.x` or `c.y` gets no injection.
- `assert(invariant_holds_after_assignment)` after assignments to fields named in the invariant — not after every assignment.
- Return values of invariant-bearing types: `assert(invariant)` at every return point that constructs a value of that type.

This is purely an optimization — correctness is identical to eager injection. The win is that VCs stay tight on large structs and rarely-touched fields.

### Status

- Parser: implemented in Weeks 4.5 (after Weeks 3-4 core IR).
- Written `cppverify::type_invariant(...)` in the class body (see Construct
  recognition below).
- `TypeContractInfo` side table on `RecordDecl` in `ASTContext`.
- The clause must appear **after** the fields it names (it is parsed eagerly;
  late parsing is future work).
- Implemented: `assume(invariant)` at the first use of an invariant-named field
  for by-value flat-record parameters. Because the
  invariant is injected as a precondition, callers must *establish* it at call
  sites (the modular precondition check), which is sound.
- Implemented: `assert(invariant)` at every `return s;` where `s` is a struct
  variable of an invariant-bearing type. The invariant is checked over `s`'s
  fields just before the return, so a function that constructs and returns a
  struct violating its invariant is rejected. Struct construction/mutation/return
  is modelled by the backend (field stores become `var.field` SSA assignments).
- By design, the invariant is **not** asserted after each individual field write.
  Asserting the whole invariant mid-construction would spuriously fail while a
  multi-field struct is being initialised one field at a time (the other fields
  are still unconstrained). The return (the encapsulation boundary) is the
  checkpoint — matching how Dafny/Verus check constructors.
- Pointer-to-record parameters are not injected (their field access lowers to a
  heap Load).

## View Functions (idiomatic spec abstraction)

When verifying code over a concrete data structure, define `cppverify::spec` functions that produce a mathematical view of the data. Specs are then written against the view, not the internals.

```cpp
struct Interval {
    int lo;
    int hi;
};

// abstract view: what the structure means mathematically
cppverify::spec int size(Interval r) { return r.hi - r.lo; }
cppverify::spec bool has(Interval r, int x) { return r.lo <= x && x < r.hi; }

bool contains(Interval r, int x)
  cppverify::pre(size(r) >= 0)
  cppverify::post(cppverify::result == has(r, x))
{
    return r.lo <= x && x < r.hi;
}

Interval shift(Interval r, int d)
  cppverify::pre(-1000 <= d && d <= 1000)
  cppverify::pre(-1000000 <= r.lo && r.lo <= r.hi && r.hi <= 1000000)
  cppverify::post(size(cppverify::result) == size(r))
  cppverify::post(cppverify::forall(x, has(r, x) == has(cppverify::result, x + d)))
{
    Interval s;
    s.lo = r.lo + d;
    s.hi = r.hi + d;
    return s;
}
```

- No new syntax. `cppverify::spec` functions named `view()`, `elem()`, `size()`, etc. are a documented convention.
- The verifier treats these spec function bodies as axioms (definitions), not as code to execute.
- This is Verus's main abstraction idiom and the recommended style for non-trivial data structures.
- Records are passed by value with scalar fields; a record holding an array
  or a pointer is not yet in the verified subset, so a view of a buffer is a
  spec over the pointer and its length (`cppverify::spec int sum(const int *p, int n)`).

## Integer Semantics — summary

| Function kind | Integer semantics | Solver encoding |
|---|---|---|
| `cppverify::spec` function (explicit) | Mathematical (unbounded) | `Int` |
| `constexpr` lifted as spec | Machine (overflow happens) | `BitVec(N)` or range-checked `Int` |
| `cppverify::proof` function | Machine | `BitVec(N)` or range-checked `Int` |
| `exec` (regular) function | Machine | `BitVec(N)` or range-checked `Int` |
| Contract arithmetic (`cppverify::pre`, `cppverify::post`, invariants, assertions) | Mathematical | `Int` |

- Contracts are mathematical, as in ACSL and Verus: `+`, `-`, `*`, `/`, `%`,
  and unary `-` on the values of C++ expressions are exact, so
  `cppverify::post(cppverify::result + 1 > cppverify::result)` holds. An implicit conversion whose result C++
  could change (a narrowing, a sign change) keeps the value; a value-preserving
  one is a machine extension. Quantifier binders are mathematical. A negative
  constant converted to an unsigned type draws a warning. An explicit cast
  still converts and is checked; write wraparound as `% 2^N`.
- Comparisons between a machine value and a mathematical one are exact. A
  mathematical operand that mentions a quantifier binder or a collection is
  compared over the integers; otherwise a value outside the machine range
  decides the comparison and one inside it is compared as a machine value.
- Conversion at boundaries is explicit. Machine to mathematical is exact.
  Mathematical to machine (materialization in a ghost or proof variable, a
  machine parameter, a return value, an explicit cast, or a bitwise operand)
  is an `overflow` obligation that the value fits; it never wraps. Until
  then, in contracts and in ghost and proof code, implicit C++ conversions
  keep a mathematical value unbounded and arithmetic on it is exact.
- Mathematical `cppverify::spec` division and remainder are unbounded but use C++'s
  truncate-toward-zero sign convention. At a zero divisor their total logical
  extension is quotient zero and remainder equal to the dividend; evaluated
  executable and contract expressions must still prove a nonzero divisor.
- `--int-encoding` selects how machine integers reach the solver: `auto`
  (default; integers unless a query needs the bits of a non-constant
  operand), `integer`, or `bitvector`. Every choice is exact, so it changes
  solver performance, never semantics. A query left unresolved under a forced
  `bitvector` encoding is retried with `auto`.

## old() Expression

<!-- cppverify-example: fragment -->

```cpp
cppverify::post(cppverify::result == cppverify::old(x) + 1)
cppverify::post(cppverify::result == cppverify::old(*p))
```

- Refers to the value of an expression at function entry.
- Valid in postconditions and loop invariants. In either location it denotes
  the enclosing function's entry state, not the previous iteration.
- The inner expression is evaluated in the pre-state. For pointer-typed expressions, `cppverify::old(*p)` is the value at the pre-state heap.

## result Expression

<!-- cppverify-example: fragment -->

```cpp
cppverify::post(cppverify::result > 0)
cppverify::post(cppverify::result.size() == n)
```

- Refers to the return value of the enclosing function.
- Only valid in postconditions.
- Type is computed via `Sema::GetTypeForDeclarator` from the full Declarator.
- Supports postfix operators: `result.x`, `cppverify::result[i]`.

## reveal_with_fuel (control recursive spec unfolding)

<!-- cppverify-example: fragment -->

```cpp
cppverify::spec int fibo(int n) cppverify::decreases(n) { ... }

int safe_fib(int n) cppverify::pre(...) cppverify::post(cppverify::result == fibo(n)) {
    cppverify::ghost {
        cppverify::reveal_with_fuel(fibo, 5);  // unfold fibo up to 5 levels in this VC
    }
    ...
}
```

- Default fuel for any recursive spec: **1**.
- `cppverify::reveal_with_fuel(fn, n)` locally raises the unfolding depth Z3 uses for `fn` within the enclosing function's VC.
- For an inductive predicate it unfolds the applications inside its
  unfoldings `n` levels deep, the predicate staying hidden behind proved
  unfoldings (see Inductive predicates). The verifier also deepens on its
  own, up to four levels, when a verdict still depends on the predicate.
- Without this, recursive `cppverify::spec` axioms cause Z3 matching loops.
- Inside ghost blocks only.

## hide / reveal

- `cppverify::hide(fn_name)` and `cppverify::reveal(fn_name)` in ghost blocks selectively control whether the body of a spec function is visible to Z3.
- Default for non-recursive specs: visible (body inlined into queries).
- Default for recursive specs: one finite unfolding step. Deeper unfolding
  requires `cppverify::reveal_with_fuel`.
- `cppverify::hide` suppresses defining equations while leaving the function application
  available to contracts and imported lemma postconditions. This is useful
  after a finite lemma has established all facts needed by a large arithmetic
  proof: irrelevant recursive equations can otherwise dominate solver time.
- `cppverify::hide` withholds the definition from proofs, not from the meaning of the
  program. A counterexample must still hold under the hidden function's true
  definition; a query that only its definition would settle is `Unresolved`
  with reason `spec.hidden`, never `Failed` and never `Verified`.
- Both constructs are implemented and are verification-only no-ops in CodeGen.

## Faithful verdicts

- `Verified`: every fact given to a solver is a consequence of the program's
  semantics: definitions, C++ machine arithmetic, and declared contracts.
- `Failed`: a counterexample that holds when every logical function is
  evaluated at its true definition. It is relative to the declared
  abstractions only: callee contracts, loop invariants, and `cppverify::modifies`
  frames.
- Anything else is `Unresolved` with a reason. `spec.fuel`: every
  counterexample found relies on a recursive spec beyond what refinement could
  unfold, the automatic inductions did not prove it, and no counterexample
  could be confirmed by a proof from proved facts; `spec.hidden`: it relies on a hidden spec's value;
  `counterexample.unchecked`: the counterexample could not be checked within
  the certifier's budgets, among them the time one check may take
  (`--certify-timeout`, by default half the query timeout); `backend.invalid-result`: the solver's answer
  contradicts the query or a fact it was given, which is a solver fault and
  says nothing about the program; `spec.termination`: the proof relies on a spec
  whose termination check did not pass, so that spec has no definition;
  `spec.reads`: the proof relies on a spec whose `cppverify::reads` check did not pass,
  so its frames are not facts; `spec.post`: it relies on a spec whose
  postcondition is not established; `spec.inductive`: it relies on the
  unfolding of an inductive predicate whose rules are not proved;
  `proof.cycle`: it relies on facts whose own proofs rely on it, as when a
  spec's proof block calls a lemma that is proved from that spec's
  postcondition; only recursion through a checked measure (a function's
  recursion cycle, a spec's induction hypothesis, a cluster sharing one
  measure) may make proofs rest on each other;
  `callee.contract`: it relies on a
  callee contract that nothing establishes: the callee's verification
  failed, or it has a contract but no definition and no trust mark;
  `decreases.missing`: a loop has no termination measure;
  `construct.unsupported`: the obligation that failed stands for a construct
  the verifier does not model, so its counterexample says nothing about the
  program; the message names the construct (for example "the operands of
  this pointer difference may address the objects of different parameters
  or globals, which may be one caller array").
- Qualifiers: `[partial]` (proved for terminating executions only, after
  `cppverify::decreases(*)`), `[trusts=f]` (relies on the contract of `f`, marked
  `[[cppverify::trusted]]`), `[vacuous]` (no execution reaches the claim).

## Spec Collections

<!-- cppverify-example: label sum -->

```cpp
using cppverify::seq;

cppverify::spec int sum(seq s)
  cppverify::decreases(s.len())
{
  return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}

int count_positive(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 0 && n <= 1000)
  cppverify::post(0 <= cppverify::result && cppverify::result <= n)
{
  cppverify::ghost seq seen = cppverify::seq_empty();
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n && 0 <= c && c <= i)
    cppverify::invariant(seen.len() == i)
    cppverify::invariant(cppverify::forall(k, 0, i, seen[k] == a[k]))
    cppverify::decreases(n - i)
  {
    if (a[i] > 0)
      c = c + 1;
    cppverify::ghost { seen = seen.push(a[i]); }
  }
  return c;
}
```

`<cppverify.h>` declares four collections of mathematical integers, the
counterparts of Verus's `Seq`, `Set`, `Multiset`, and `Map`:

| Type | Operations |
|---|---|
| `seq` | `seq_empty()`, `seq_of(x)`, `len()`, `s[i]`, `push(x)`, `update(i, x)`, `reverse()`, `subrange(lo, hi)`, `s + t`, `contains(x)` |
| `set` | `set_empty()`, `insert(x)`, `remove(x)`, `contains(x)`, `unite(t)`, `intersect(t)`, `difference(t)`, `subset_of(t)` |
| `multiset` | `multiset_empty()`, `insert(x)`, `remove(x)`, `count(x)` |
| `map` | `map_empty()`, `insert(k, v)`, `remove(k)`, `contains(k)`, `m[k]` |

- Every operation is total. A sequence index outside `[0, len())` reads 0,
  an update there changes nothing, and `subrange` clamps both bounds; a key
  outside a map's domain maps to 0; removing an absent multiset element
  changes nothing.
- Sequences are finite. Sets, multisets, and maps range over all integers and
  may be infinite (a set may hold every integer).
- `==` and `!=` compare elements in order, members, counts, or domain and
  values.
- `update` and `reverse` are spec functions of `<cppverify.h>` over the
  other operations, so every backend that decides sequences supports them:
  `s.update(i, x)` is `s.subrange(0, i).push(x) + s.subrange(i + 1, len)`
  for `i` in `[0, len())` and `s` otherwise; `s.reverse()` is `s` when empty
  and otherwise `s.subrange(1, len).reverse().push(s[0])`, with the
  postcondition `s.reverse().len() == s.len()`, proved with its termination.
  Facts about the elements of a reverse are proved by induction, like those
  of any recursive spec.
- A sequence equality that a proof must establish (in an assertion, a
  postcondition, an invariant) may also be proved element by element: equal
  lengths and equal elements imply equality, as Verus's `=~=` and Dafny's
  sequence equality. A stated `cppverify::check(a == b)` is therefore a hint
  where the solver needs one.
- Induction over a sequence is written by the user, as in Verus and Dafny: a
  recursive proof function with `cppverify::decreases(s.len())` that cites itself on a
  shorter sequence:

<!-- cppverify-example: with sum -->

```cpp
cppverify::proof void sum_concat(seq s, seq t)
  cppverify::post(sum(s + t) == sum(s) + sum(t))
  cppverify::decreases(t.len())
{
  if (t.len() > 0)
    sum_concat(s, t.subrange(0, t.len() - 1));
}
```

- A query over collections gets `--collection-timeout` milliseconds (by
  default twice `--timeout`): their theories need more search than integer
  arithmetic. With more than one job (the default), a query over sequences
  is also solved in the plain sequence theory, which refutes false claims
  much faster than the encoding tuned for proofs.
- Collections exist only for verification: they may appear in contracts,
  ghost code (`cppverify::ghost seq s = ...;`, assignment in ghost blocks), and as
  parameters and results of spec and proof functions. Sema rejects every use
  in executable code (declarations, operations, parameters, results).
- A collection read can be a trigger, and counterexamples show collection
  values: `[1, 2]`, `{1, 3..5}` (a run), `{2: 3}` (counts), `{1 -> 7}`, and
  `{..}` (every integer).
- Backends: Z3 and cvc5 decide all four (cvc5 settles fewer goals that
  need an infinite set or ghost collections in loops). Lean does not
  support them yet (`logic.unsupported`); that is planned for a future
  release.

## Clang Modification Details

### Construct recognition

The lexer reserves nothing. `clang/include/clang/Basic/CppVerifyConstructs.def`
lists the 28 construct words and the positions each may take (function
clause, loop clause, class member, declaration specifier, statement,
expression). At each position the parser calls `tryAnnotateCppVerify`
(`clang/lib/Parse/ParseCppVerify.cpp`), which looks ahead for
`[::] (name ::)+ word` with `word` a construct, resolves the qualifier with
Clang's own scope annotation (so aliases and `::cppverify::` work through
ordinary name lookup), and, when the qualifier denotes the global namespace
`cppverify`, replaces the qualified name with one `annot_cppverify` token
spanning it. The token carries the construct and a `DeclRefExpr` to the
construct's declaration in `<cppverify.h>`, which tools use for hover,
go-to-definition, rename, and references. A name that Clang's own
disambiguation already resolved (an `annot_non_type` or `annot_overload_set`
after the scope) is recognized the same way.

`<cppverify.h>` declares every construct, documented: call-like ones as
deleted functions (`void pre(bool condition) = delete;`) and the others as
unavailable enumerators (`result`, `inductive`, `spec`, ...), so any use the
parser does not take as a construct is an error. `InitPreprocessor` includes
the header in every C++ translation unit compiled with `-fverify-contracts`.

Misuse is diagnosed where the parser would otherwise fail: a construct in the
wrong position (`'cppverify::pre' follows a function's parameter list`), an
unknown word after `cppverify::` in clause position (with a suggestion), a
construct word written bare where only the construct fits (with a fix-it
inserting the qualifier; for `pre`/`post` after a declarator, the message
names C++26 contracts), and the header missing from the include path.

### AST Nodes

**Expressions (inherit from Expr):**

| Node | Fields | Type |
|---|---|---|
| ForallExpr | BoundVar, Lo, Hi (both null when unbounded), Body | BoolTy |
| ExistsExpr | BoundVar, Lo, Hi (both null when unbounded), Body | BoolTy |
| ContractChooseExpr | BoundVar, Lo, Hi (optional), Body | the binder's type |
| OldExpr | Inner | Inner->getType() |
| ResultExpr | — | enclosing function's return type |

A range footprint `p[lo : n]` reuses Clang's `ArraySectionExpr`; Sema accepts
it only as a whole `cppverify::modifies` footprint. A `cppverify::trigger(term)` mark leaves `term`
in place and records it in an `ASTContext` side table.

**Statements (inherit from Stmt):**

| Node | Fields |
|---|---|
| ContractAssertStmt | Expr (the condition), optional CompoundStmt (the `by` proof); `cppverify::calc` builds nested ones |
| GhostBlockStmt | CompoundStmt (the body); `cppverify::ghost T x = e;` wraps its declaration |
| RevealWithFuelStmt | FunctionDecl* fn, int fuel |

**Side-table info on existing nodes:**

| Existing Node | New Data |
|---|---|
| FunctionDecl (via ASTContext side table) | preconditions, postconditions, modifies, aliases, recommends, isSpec, isProof, decreases, behavior checks |
| WhileStmt / ForStmt / DoStmt | invariants, decreases, modifies |
| RecordDecl | type_invariants |
| VarDecl | ghost marker |

### Parser Entry Points

All in `clang/lib/Parse/ParseCppVerify.cpp`; each upstream parse function has
a one-line hook.

| Syntax Position | Parser Method | Hook in |
|---|---|---|
| After a function declarator | `ParseFunctionContractClauses`, `attachFunctionContract`, `ParseContractClauseProofs` | `ParseFunctionDefinition` (Parser.cpp) |
| After a while/for head or a do-loop condition | `ParseLoopContractClauses`, `attachLoopContract` | `ParseWhileStatement`, `ParseForStatement`, `ParseDoStatement` |
| Statements (`ghost`, `check`, `calc`, `reveal_with_fuel`, `hide`, `reveal`) | `ParseCppVerifyStatement` | `ParseStatementOrDeclarationAfterAttributes` |
| `cppverify::spec` / `cppverify::proof` | `ParseCppVerifySpecifier` | `ParseDeclarationSpecifiers` |
| `cppverify::type_invariant(...)` | `ParseTypeInvariant` | `ParseCXXMemberSpecification` |
| Expressions (`forall`, `exists`, `choose`, `old`, `result`, `trigger`) | `ParseCppVerifyExpression` | `ParseCastExpression` |

### Sema Rules

1. All contract expressions must be contextually convertible to bool (except `cppverify::decreases` which must be integer; and `cppverify::modifies` lvalues which need ordinary lvalue typing).
2. `cppverify::old(expr)` is only valid in postconditions and loop invariants; both use
   the enclosing function's entry state.
3. `cppverify::result` is only valid in postconditions. Its type matches the enclosing function's return type.
4. Quantifier binders are pushed into scope during body type-checking, popped after.
5. Spec functions must have no side effects (no assignments to non-local state, no I/O calls).
6. Proof functions must return void.
7. Ghost blocks may only contain ghost-safe statements. They can update
   ghost-local variables/direct dot-fields and call proof functions, but cannot
   mutate executable state, call executable functions, return from the
   enclosing function, or contain a loop without `cppverify::decreases`.
8. `cppverify::modifies` lvalues must be ordinary lvalues; the parser computes their alias keys for the encoder.
9. `cppverify::aliases(p, q)` arguments must be pointer/reference-typed parameters of the enclosing function.
10. `cppverify::recommends` is only valid on `cppverify::spec` functions.
11. A `cppverify::spec` function may be referenced only from contracts, ghost code, and
    `cppverify::spec` or `cppverify::proof` functions; executable code, including initializers and
    default arguments, may not reference one. Unevaluated operands
    (`sizeof`, `decltype`) are exempt.
12. The same holds for ghost variables, `cppverify::choose`, and the `cppverify`
    collections (their types as executable declarations, parameters, or
    results, and every operation).
13. A range `p[lo : n]` needs a pointer to a complete object type and
    integer bounds, and is valid only as a whole `cppverify::modifies` footprint.

### CodeGen Rules

- `GhostBlockStmt` → emit nothing
- `ContractAssertStmt` → emit nothing (or optionally emit runtime assert in debug mode)
- `RevealWithFuelStmt` → emit nothing
- Functions with `isSpec` or `isProof` → skip entirely (already gated in CodeGenModule)
- All contract clauses on FunctionDecl → ignored by codegen
- Loop invariants/decreases → ignored by codegen
- `cppverify::type_invariant` on RecordDecl → ignored by codegen

## Backend-Neutral Obligation Contract

CppVerify lowers C++ semantics exactly once:

```
Clang AST -> typed VCR -> passive SSA -> ObligationModule -> backend adapter
```

`ObligationModule` is the production/research boundary. It contains matching
direct correctness and counterexample terms, deterministic internal IDs,
source-anchored public IDs named by a precise obligation kind (such as
`precondition`, `invariant-preserved`, `overflow`, `bounds`, `aliasing`, or
`unwinding`), inclusive source
ranges, original-name typed model metadata, guarded diagnostic trace events,
required logic features, equivalent ordered queries, and owned typed
logical-function declarations with compact step definitions and exact finite
fuel levels. Layer 3 dumps this exact module; Layer 4 and ordinary verification
encode the same in-memory object. There is no separate dump-only
weakest-precondition implementation and no backend may borrow VCR declarations.

Diagnostic metadata is non-semantic: names, source ranges, internal positional
and public source-anchored IDs, and trace events survive archive replay but do
not change semantic hashes. Model and trace
evaluation never requests Z3 model completion. Undetermined values remain
unknown, false-guarded events are omitted, and undetermined guards remain
explicitly unknown rather than selecting a path.

The consumer header contains no VCR/passive types. Canonical integer sorts own
signedness and the originating C++ width needed by explicit
machine/mathematical conversions; backend adapters derive all representation
choices from those sorts.

Module construction is fail-closed. Null, unsupported, malformed, or untyped
terms return an error before backend dispatch. Every free symbol, including
diagnostic model and trace expressions, has one module-wide logic sort.
Conflicting reuse is rejected before a solver can observe it. Every backend
declares supported logical features; a missing capability yields `unknown`,
never an approximation.

Before publication or dispatch, a shared fail-closed canonicalizer applies a
deliberately narrow set of semantics-preserving rewrites: Boolean constants,
double negation, constant conditionals, and reflexive equality/inequality. It
simplifies logical definitions, removes declarations unreachable transitively
from the ordered goals, rebuilds exact per-obligation and complete
goal/counterexample pairs, recomputes features, and revalidates. The same step
runs after archive decoding, so adapters never depend on producer-specific
dead declarations or trivial Boolean structure. It does not rewrite
arithmetic, quantifiers, pointer/heap expressions, or assumptions.

`--obligation-out=FILE` publishes deterministic, concatenable
`cppverify.obligation/2` binary records with stable wire tags and portable
source attribution; schema v1 records remain readable. Publication includes an
exact serialize/deserialize/validate/reserialize check. SHA-256 module and
per-obligation semantic hashes exclude source paths, display-only names, both
positional and source-anchored obligation IDs, and every obligation kind except
`unwinding`; individual hashes include the transitive logical declarations
reachable from that goal. Their format version is independent of the archive
wire version. Canonicalization introduced semantic-hash format v2, excluding
diagnostic identities advanced it to v3, and excluding diagnostic kinds
advances it to v4.
`--obligation-in=FILE` validates and replays the records through Z3, cvc5,
strict Z3+cvc5 portfolio, lower-only/Layer 3-4 dumps, or Lean scratch export
without reparsing C++.
BMC-produced records carry their unroll bound in semantics and replay through
the BMC result aggregator; untransformed records cannot acquire BMC semantics
after this boundary. Lean scratch replay of bounded records is rejected.
Failure-only `cppverify::recommends` diagnostics do not alter archive contents.
Imported records are untrusted input: bounded parsing precedes structural,
scope, sort, signature, feature, canonical-payload, exact-negation, and
complete-versus-ordered-goal validation. Module-local finite fuel may differ
across concatenated records, but a reused logical identity must keep the same
parameter and result signature.

Backend results carry stable machine-readable reason codes independently of
their human message: `counterexample`, `solver.timeout`, `solver.unknown`,
`solver.resource-limit`, `solver.unavailable`, `solver.invocation-failed`,
`solver.malformed-output`, `query.size-limit`, `encoding.failed`,
`obligation.invalid`, `logic.unsupported`, `query.missing`,
`backend.invalid-result`, `backend.inconsistent-results`,
`bmc.incomplete-bound`, `lean.export-failed`, `cache.corrupt`,
`cache.io-failed`, `spec.fuel`, `spec.hidden`, `spec.termination`,
`spec.reads`, `spec.post`, `spec.inductive`, `proof.cycle`, and
`counterexample.unchecked`.
`--diagnostics-format=json` serializes verification results as versioned JSON
Lines (`cppverify.diagnostic/1`) for both source verification and archive
replay.

`--jobs=N` runs one pool of exactly `N` workers (default: every core, or
`CPPVERIFY_JOBS`; the compile-time verifier uses one). Functions are verified
as tasks on it, each with its own backends; a function's obligations are
tasks on the same pool, and with workers to spare its whole query races the
obligations solved one by one, a proof by either interrupting the other; a
query over sequences is also solved in the plain sequence theory, which
finds counterexamples faster. Each task constructs a distinct Z3 context/solver, and dumps, archive
records, and diagnostics are buffered per function and published in
canonical source order, so concurrency cannot choose which failure is public.
`--function-timeout` (by default ten times `--timeout`) bounds all queries
of one function together, in wall-clock time; once it is spent no further
query starts and the function is `Unresolved` (`solver.timeout`). AST/VCR lowering and Lean emission remain serial.
`--solver-rlimit` adds a deterministic per-query Z3 budget, while
`--max-query-nodes` rejects an oversized canonical module before
verification, lower-only encoding, or a requested Z3 dump; neither limit can
become success.

`--proof-cache=DIR` stores only successful individual proofs. The key binds an
obligation's dependency-scoped semantic hash to hash format v4, the backend
namespace and adapter revision, and the exact Z3 version. Relevant C++ target,
UB, fuel, transform, and bound choices are already represented in the canonical
goal and reachable declarations; BMC additionally has a distinct namespace.
Entries are immutable and atomically installed. Corruption and I/O errors are
reported fail-closed when reading a requested proof, while store/prune errors
after a fresh proof are explicit telemetry and do not replace that verdict.
Pruning still runs after errors, retries capacity-limited writes after eviction,
and removes abandoned atomic-write files after 24 hours. Failed, unresolved,
resource-limited, and `BoundedSafe` results are never stored. Source verification
and archive replay therefore share proofs only when they consume the same
canonical semantics.
The opt-in directory is trusted local memoization, not a proof-object
certificate or an untrusted shared-service boundary; Lean remains the
independently kernel-checked path.

The optional cvc5 adapter independently serializes canonical obligations to
standalone SMT-LIB2. It explicitly reproduces C++ truncate-toward-zero
mathematical division/remainder (including the total zero-divisor extension),
signed/unsigned bit-vector operations and conversions, overflow predicates,
`Array Int Int` heap cells, bounded quantifiers, and only the finite ground spec
equations owned by the module. It runs an installed executable with deterministic
seed/resource options and bounded output; missing tools, invocation failures,
timeouts, `unknown`, extra diagnostics, and malformed tokens are unresolved.
The model cvc5 prints after `sat` is checked by the same certifier as Z3's, and
refinement re-runs cvc5 with definition instances. Once a hidden instance has
been given, non-recursive definitions are given whole; recursive ones never
are, because cvc5 does not decide queries over them.

`--backend=portfolio` runs ordered Z3 and cvc5 queries over that same module.
Only `unsat`/`unsat` is `Verified`; only two certified counterexamples are
`Failed`; a decisive split is `backend.inconsistent-results`; and an
unresolved side keeps the portfolio unresolved. Agreed failures retain Z3's
typed source model and trace.
`--backend=race` runs the same Z3 and cvc5 adapters at once and trusts
either alone, as Frama-C's prover list does: a proof is sound and a
counterexample is certified whichever solver found it, so the first
decisive answer stands and cancels the other (`VerifyBackend::cancel`
interrupts every running Z3 encoder and stops the cvc5 process). When
neither settles a module, the obligations each proved are joined, every
obligation being a query of its own, and the module is `Verified`
(`[backend=z3+cvc5]`) when they cover all of them.
The persistent cache, when requested, memoizes only the portfolio's
namespace-separated Z3 component and never skips cvc5. BMC remains Z3-backed,
and bounded archives must replay through the BMC aggregator.

BMC remains a VCR loop transformation followed by the shared passive,
obligation, and Z3 path. A spec's own checks (termination, postcondition,
induction, reads, and their proof blocks) contain no loops, so under BMC
they are solved exactly as on the default Z3 path and reported as `z3`;
their archived modules keep the bound, so a BMC archive replays as before.
Source verification treats `--unroll=N` as a maximum
and explores bounds `0..N` in order. A failed safety query terminates as
`Failed`; complete unwinding terminates as `Verified`; an unresolved query
terminates fail-closed; and a failed unwinding query at `N` is
`BoundedSafe(N)`. Only previously `Verified` dependency-scoped prefix queries
are reused across bounds. Their in-process identity omits the enclosing bound
but includes the exact transformed query and reachable declarations; persistent
cache records retain explicit bound provenance. Terminal source diagnostics
publish explored bounds, reuse counts, and numbered loop-iteration traces.
Archives contain only each function's terminal bounded module and replay that
exact bound without pretending to rerun source-level incremental exploration.

Lean consumes the same module. Standalone output is an unchecked scratch-pad.
Editable project mode pins Lean 4.32.2, overwrites only generated semantics and
the active check module, and preserves reusable user lemmas and one proof file
per stable obligation goal. Initial generation is `Exported`. Certification
compiles the user module and every active proof with `sorry` as an error, then
checks aggregate theorem types and axiom dependencies. Only foundational Lean
axioms are permitted; user `axiom`/`opaque` proof shortcuts, stale proof types,
missing proofs, malformed output, and toolchain failures remain `Unresolved`.
Only complete success is `Certified`.

`--check-ub` extent instrumentation is applied before all Z3, cvc5, portfolio,
BMC, and Lean obligation construction. Direct Lean export and canonical archive
replay therefore name and state the same bounds obligations. The automated
backend fidelity gate also kernel-builds the generated Lean semantics, checks
stable theorem/proof-module identities, compares source and replay exports, and
requires source-identical failed obligations across every automated backend.

The default remains Z3 alone. `--lean-fallback=DIR` is an explicit opt-in that
exports only Z3 `Unresolved` modules; SAT counterexamples remain failures. It
exports only the obligations the solver did not prove individually, reporting
the split (`[z3: 18 of 20 proved; lean: 2 exported]`);
`--lean-fallback-scope=all` exports every obligation. A rerun with
`--lean-certify` can replace those unresolved results only after the preserved
Lean proofs pass the kernel gate: a split result becomes `Proved (z3+lean)`
(JSON `mixed-proof`, with per-obligation evidence), never `Verified`, and only
a complete Lean export becomes `Certified`.

## MVP Acceptance Programs

The MVP gate is implemented as permanent end-to-end regressions rather than a
documentation-only example:

| Program | Proved range | Rejected boundary | Features exercised |
|---|---:|---:|---|
| Factorial | `0..12` | `13!` | mathematical spec, executable recursion, loop invariant, termination, signed multiplication overflow |
| Fibonacci | `0..46` | `F(47)` | mathematical recurrence, proof lemmas, executable recursion, loop invariant, termination, signed addition overflow |
| Framed output | factorial range | null or out-of-frame writes | non-null pointers, `cppverify::modifies(*out)`, `cppverify::old(*preserved)`, heap framing |

Both arithmetic programs have recursive and iterative executable
implementations with exact 32-bit signed-`int` contracts. They are proved equal
to unbounded mathematical specifications while every executable operation
retains C++ machine semantics. The first out-of-range operation is deliberately
kept as a negative regression and must be rejected.

The source-of-truth tests are:

- `clang/test/Verify/suite/mvp_factorial.cpp`
- `clang/test/Verify/suite/safe_fib.cpp`

Feature acceptance is layered. Real C++ positive/negative programs establish
user-visible behavior, while `cpp-verify --lower-only --dump-ir=1,2,3,4`
provides solver-independent VCR, passive, VC, and Z3 encoding oracles.
`Lowered` means only that encoding succeeded; only an ordinary backend
`Verified` result certifies the obligations. The executable sweep performs
this lowering preflight for every solver-positive example before invoking its
backend.

This gate established the integer/control-flow/pointer core of the MVP.
Subsequent bounded lifetime checkpoints added scalar `new`/`delete`,
initialized-storage checks, aligned disjoint allocation,
use-after-delete/double-delete rejection, first-class local provenance, and
inferred fresh-owned scalar factory returns. Bounded promoted local objects,
fixed arrays, scalar subobject references, modular slices, and general
same-array pointer difference under `valid(p, n)` are also supported.
Provenance across ownership-taking or recursive interfaces, pointer
reinterpretation/cross-object arithmetic, aggregate/rvalue references,
by-value pointer-bearing records, and general arrays remains unsupported.
