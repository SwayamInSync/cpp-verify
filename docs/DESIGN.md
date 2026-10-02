# Contract Syntax & Language Design

## Enabling Contracts

All contract syntax is enabled with `-fverify-contracts`. Without this flag, the new keywords are not reserved and existing C++ code compiles normally.

## Contract Syntax Overview

| Syntax | Where | Meaning |
|---|---|---|
| `pre(expr)` | After function `)` | Precondition — caller must satisfy |
| `post(expr)` | After function `)` | Postcondition — callee must establish; may use `result` and `old(x)` |
| `modifies(lvalue, ...)` | After function `)`, or after a loop's invariants | Frame condition — the cells, ranges `p[lo : n]`, or objects this function or loop may write |
| `aliases(p, q)` | After function `)` | Opts out of implicit non-aliasing for a supported same-pointee pointer/reference address pair |
| `recommends(expr)` | After function `)` (spec only) | Soft precondition for spec functions; reported on verification failure |
| `inductive` | After function `)` (spec returning `bool` only) | The least predicate the body defines: true where a finite derivation shows it |
| `behavior(name, assumes)` | After function `)`, followed by its `pre`/`post` | A case of the contract (ACSL behavior) |
| `complete_behaviors` / `disjoint_behaviors` | After the behaviors | Some behavior / at most one behavior applies to every admitted input |
| `invariant(expr)` | After a `while`/`for` condition or a `do` loop's trailing condition | Loop invariant |
| `decreases(expr [, expr...])` | After loop `)` or function `)` | Termination measure. Tuple form is lex-ordered. Required on executable loops. |
| `decreases(*)` | After an executable loop or function | Allows divergence; proofs then cover terminating executions (`[partial]`) |
| `type_invariant(expr)` | Inside class/struct body | Per-instance invariant injected at function boundaries |
| `ghost { ... }` | Statement | Ghost block — proof steps, stripped by CodeGen |
| `ghost T x = e;` | Statement | Function-scoped ghost variable |
| `contract_assert(expr)` | Statement | Verification condition (not a runtime check) |
| `contract_assert(expr) by { ... }` | Statement | Proves `expr` from a local proof whose other facts are discarded |
| `calc { e0; op { ... } e1; ... }` | Statement | Chain of proved steps concluding `e0 R en` |
| `reveal_with_fuel(fn, n)` | Inside ghost blocks | Locally raise Z3 unfolding depth for spec function `fn` |
| `spec T f(...)` | Declaration | Pure spec function — interpreted by verifier only |
| `proof void f(...)` | Declaration | Ghost proof function — establishes lemmas |
| `forall(i, lo, hi, expr)` | Expression | Bounded universal quantifier |
| `exists(i, lo, hi, expr)` | Expression | Bounded existential quantifier |
| `forall(i, expr)` / `exists(i, expr)` | Expression | Quantifier over all mathematical integers |
| `trigger(term)` | Inside a quantifier body | Makes `term` the pattern that instantiates the quantifier |
| `choose(i, [lo, hi,] expr)` | Expression | Some integer satisfying `expr` (Hilbert ε) |
| `old(expr)` | Inside `post` or `invariant` | Value of `expr` at function entry |
| `result` | Inside `post` | Return value of the enclosing function |
| `cppverify::seq`, `set`, `multiset`, `map` | `<cppverify.h>` | Mathematical collections for specifications and ghost code |

## Function Contracts: pre / post / modifies / aliases / recommends

```cpp
void swap(int* a, int* b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
    int t = *a; *a = *b; *b = t;
}
```

- `pre(expr)`: precondition. `expr` must be contextually convertible to bool.
- `post(expr)`: postcondition. `expr` may reference `result` (return value) and `old(x)` (pre-state).
- `modifies(lvalue, ...)`: frame condition — see §Pointers and Memory below.
- `aliases(p, q)`: see §Pointers and Memory below.
- Multiple `pre` / `post` / `modifies` clauses are conjuncted.
- Parsed after the function declarator's `)` and before `{`.
- A parameter named in `post` denotes its value at entry, as in ACSL, even
  when the body assigns the parameter; callers can therefore use the
  postcondition.

### Behaviors

```cpp
int abs_value(int x)
  behavior(nonnegative, x >= 0)
    post(result == x)
  behavior(negative, x < 0)
    pre(x > -2147483647 - 1)
    post(result == -x)
  complete_behaviors
  disjoint_behaviors
{
  return x < 0 ? -x : x;
}
```

- `behavior(name, assumes)` starts a case, as ACSL behaviors do. The `pre`
  and `post` clauses after it, up to the next behavior, apply where the
  assumption holds: `assumes -> pre`, and `old(assumes) -> post`.
- `complete_behaviors` requires that some behavior applies to every input the
  preconditions admit; `disjoint_behaviors` that no two do. Either may list
  the behaviors it relates, e.g. `disjoint_behaviors(low, high)`. Both are
  checked at function entry.

### Verdicts that rest on other contracts

A caller's proof uses its callees' contracts. When a callee's own
verification does not establish its contract, a caller whose proof relies on
it is `Unresolved` with reason `callee.contract`.

```cpp
[[cppverify::trusted]] int clamp_byte(int v)
  post(0 <= result && result <= 255);
```

`[[cppverify::trusted]]` (a standard C++ attribute, like Verus's
`#[verifier::external_body]`) marks a contract as assumed: on a declaration
the contract holds at every call (whose preconditions are still checked); on
a definition the body is compiled but not verified; on a proof function the
postcondition is an axiom. A spec cannot be trusted, since its definition is
its meaning. A trusted function reports `Trusted: f (contract assumed, not
verified)`, and every verdict that relies on it, directly or through verified
callees, carries `[trusts=f]`. A contract without a definition and without
the mark is not assumed: a warning names it, and its callers are
`Unresolved` with reason `callee.contract`. A trusted contract writes only
its `modifies` footprints; without them it writes nothing through a pointer
or reference to const, and is taken to write the whole heap through a
mutable one (see `modifies` below).

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
is not flagged.

## Loop Contracts: invariant / decreases

```cpp
while (i < n)
  invariant(2 <= i && i <= n)
  invariant(fib.size() == i)
  decreases(n - i)
{ ... }
```

- `invariant(expr)`: must hold on entry and be preserved by each iteration.
- `decreases(expr [, expr...])`: termination measure. Single expression must be non-negative and strictly decreasing. Tuple form is lex-ordered: `decreases(a, b)` means `(a, b)` strictly decreases lexicographically, and only the first component that changes must stay non-negative.
- Verification is total correctness, as in Verus: every executable loop needs
  `decreases`. Without one the function is `Unresolved` with reason
  `decreases.missing`, unless BMC proves the loop's unwinding.
  `decreases(*)` on a loop or an executable function allows divergence; the
  proof then covers only executions that terminate, and that function and
  every caller are reported `Verified ... [partial]` with a warning (JSON
  `"partial": true`). Ghost and proof loops cannot use `decreases(*)`.
- `modifies(...)` after a loop's invariants is ACSL's `loop assigns`: the
  cells, ranges, and objects the loop may write, read in each iteration's
  state. Each iteration starts with every other cell unchanged since the loop
  began, and must end (and `continue`) that way, so a range such as
  `a[0 : i]` can describe progress:

```cpp
for (int i = 0; i < n; i = i + 1)
  invariant(0 <= i && i <= n)
  modifies(a[0 : n])
  decreases(n - i)
{
  a[i] = 0;
}
```

  Without `modifies`, a loop writes only the objects its stores and calls
  reach, inferred from the body: every other object keeps its value without
  an invariant saying so.

`do` loops place the clauses between the trailing condition and its semicolon:

```cpp
do {
    i = i + 1;
} while (i < n)
  invariant(i >= 1 && i <= n)
  decreases(n - i);
```

The body executes once before invariant establishment. CppVerify verifies that
mandatory execution from the concrete incoming state, establishes the invariant
after it, and then applies the ordinary modular `while` rule to every subsequent
iteration. `old(expr)` in any loop invariant denotes the enclosing function's
entry state, not the previous iteration. A function local has no value at
function entry and is rejected inside `old(...)`; snapshot such a value in an
ordinary local and refer to that snapshot without `old`.

`return`, `break`, and `continue` may leave a `while` or `for` loop from an
arbitrary inductive iteration. A return checks the postcondition in its own
state, a break continues after the loop in its own state, and a continue ends
the iteration: it re-establishes the invariant and decreases the measure, after
running a `for` increment. `break` and `continue` in a `do` loop, whose first
iteration is lowered outside the loop, and ghost code leaving an executable
loop fail closed.

## Assertions: contract_assert

```cpp
contract_assert(x > 0);
```

- Generates a verification condition (not a runtime check).
- In ghost blocks, used for proof steps: once proved, the condition is
  assumed for the rest of the function.
- A function without contract clauses is still verified when its body has a
  `contract_assert`, ghost code, or a loop contract.

```cpp
contract_assert(sq(a) <= sq(b)) by {
    sq_monotone(a, b);
}
```

- `contract_assert(c) by { proof }` proves `c` from a ghost proof, as Verus's
  `assert ... by` and Dafny's `assert ... by` do: the proof's facts (lemma
  posts, its own assertions, its locals) stay inside it, and only `c` holds
  afterwards. It is encoded as `if (*) { proof; assert c; assume false }
  assume c`, with the choice fresh in every execution, so BMC unrolling stays
  sound.

```cpp
contract_assert(forall(k, 0, n, a[k] <= a[n - 1])) by {
    pair_ordered(a, n, k, n - 1);
}
```

- With a `forall` as the condition, the proof is about one arbitrary value of
  its variable, as Verus's `assert forall ... by`: inside the block `k` is in
  scope, lies in `[lo, hi)`, and cannot be assigned; the block must establish
  the body for that `k`, and the whole `forall` holds afterwards (universal
  generalization). An implication is a branch: `if (A(k)) lemma(k);`.

```cpp
calc {
    sq(a);
    <= { sq_monotone(a, b); }
    sq(b);
    == b * b;
}
```

- `calc { e0; op { proof } e1; ...; en; }` proves each step `e(k-1) op ek`
  as an assert-by (the block is optional) and concludes `e0 R en`: `==` when
  every step is `==`, `<` or `>` when some step is strict, else `<=` or `>=`.
  Mixing `<`-like and `>`-like steps is rejected. `calc` is contextual: a
  type or variable named `calc` keeps its meaning.

## Ghost Blocks

```cpp
ghost {
    lemma_fibo_monotonic(i, n);
    contract_assert(fibo(i) <= fibo(n));
    reveal_with_fuel(fibo, 3);
}
```

- Code inside `ghost { }` exists only for verification.
- May contain `contract_assert`, `reveal_with_fuel`, spec/proof function calls, ghost variable declarations.
- May assign only ghost-local variables and their direct dot-fields; executable
  locals, globals, pointees, executable calls, and enclosing-function returns
  are rejected.
- Ghost loops require `decreases`, because the loop is absent at runtime.
- Stripped entirely by CodeGen — zero runtime cost.
- `ghost T x = e;` declares a ghost variable in the enclosing function scope,
  like Verus's `let ghost`: later ghost code, assertions, and loop invariants
  may name it, so an invariant can refer to a value from before the loop.
  Sema rejects any use from executable code.

## Spec Functions

```cpp
spec int fibo(int n)
  decreases(n)
{
    if (n == 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}
```

- Pure mathematical functions used in contracts.
- Usable only in contracts, ghost code, and other `spec` or `proof`
  functions. A spec is never compiled, so Sema rejects a reference from
  executable code (a body, initializer, or default argument).
- Must be total (all paths return, termination proven via `decreases`).
- No side effects, no mutation, no I/O. A spec may read memory through its
  pointer parameters but never write it; each call is evaluated in the heap
  state a load at that point would read (the current state, the entry state
  inside `old(...)`, or the call-site state of a callee contract).
- Can be recursive (with `decreases`). Its termination is proved without its
  own definition, so every recursive call must lower the measure whatever the
  spec's other calls return; a call inside `forall` or `exists` must lower it
  for every bound value. Functions of one kind (spec, proof, or executable)
  may recurse through each other when they share a measure of one length that
  every call within the cycle lowers.
- May declare `reads(p, n)`: the cells `p[0..n)` it depends on, checked
  against its body (every load, and every range a heap-reading callee reads,
  lies inside). A write outside them leaves every application unchanged, and
  callers receive that frame at each store without unfolding the spec.
- Takes no `pre`, `modifies`, or `aliases`: a spec is defined for every
  argument, and `recommends` states its intended domain.
- May declare `post(...)`, proved with its termination by well-founded
  induction on the measure (a recursive call assumes the post only where its
  measure is lower) and assumed at every application. A failed post demotes
  the proofs that relied on it (`spec.post`, or `spec.termination` for a
  recursive spec).
- May declare `when(c)`: the body defines the spec only where `c` holds,
  termination is checked there, and elsewhere its value is an uninterpreted
  function of its arguments. A post holds within the domain.
- **Integer semantics: mathematical (unbounded `Int` in Z3) by default.** See §Integer Semantics.
- Body is interpreted by the verifier as an axiom; not compiled.
- Can call other spec functions.
- Type-checked by Clang Sema like normal functions.

**Why termination must be verified:** A non-terminating spec function introduces a logical contradiction — Z3 can derive `bad(0) == bad(0) + 1`, therefore `0 == 1`, and from that prove anything. The `decreases` clause is the only thing about a spec function that needs verification. Its body is the mathematical definition and is axiomatically true by construction once the spec terminates, which is why the termination check cannot use it: a diverging spec's equations can be contradictory exactly where it diverges. Non-recursive spec functions need no verification at all.

### Inductive predicates

```cpp
spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

spec bool reach(int a, int b)
  inductive
  post(!result || a < 0 || a <= b)
{
  return a == b || exists(c, edge(a, c) && reach(c, b));
}
```

- `inductive` makes a spec returning `bool` the least predicate its body
  defines, as Dafny's `least predicate` and Coq's inductive propositions: it
  holds exactly where a finite derivation shows it. It needs no measure, so
  it describes reachability, derivability, or a process that may run forever
  (`n == 1 || (n > 1 && reaches_one(next(n)))`). `inductive` is contextual,
  like `reads`.
- The body returns a condition, under `if` and `else` at most, in which the
  predicate occurs only positively: as a conjunct or disjunct, a branch of
  `?:`, under `exists`, or under a bounded `forall`; never negated, compared,
  converted, in a condition, in an argument, or under a `forall` without
  bounds. The predicate applies itself only directly, reads no memory, and
  takes no `decreases` or `when`.
- Meaning: with `F` its body, `P(x)` is `exists(h, P.step(h, x))`, where the
  generated spec `P.step(h, x)` is `h > 0 && F` with each `P(a)` read as
  `P.step(h - 1, a)`: `F` applied `h` times to false. The conditions above
  make `F` monotone and continuous, so this union is the least fixpoint
  (Kleene's theorem) and `P(x) == F(x)` is a theorem.
- Proofs see `P` through that equation, assumed at every application: one
  unfolding, both ways (introduction and inversion). An application that
  appears only inside an unfolding is unfolded once it is named, as in
  `contract_assert(reach(2, 4));`. `reveal(P)` gives the definition instead.
- A postcondition states what every derivation satisfies and has the form
  `!result || Q`, where `Q` does not apply `P`. It is proved for `P.step` by
  induction on `h`, which is induction on derivations, together with the
  termination of `P.step`, and it holds at every application of `P`. A
  failure is reported as `spec post by induction failed: P`, and proofs that
  rely on it are `spec.post`.
- A counterexample that needs `P(v)` true is certified by a derivation, a
  height `h` with `P.step(h, v)`, found by trying heights. One that needs
  `P(v)` false is `counterexample.unchecked` unless the quantifier analysis
  decides it, since no height shows that no derivation exists.

### `recommends` — soft preconditions for spec functions

```cpp
spec int safe_div(int a, int b)
  recommends(b != 0)
{
    return a / b;
}
```

- `recommends` clauses do **not** generate VCs at call sites. Spec functions remain total.
- They are checked only on verification failure of any function calling the spec, and reported as warnings.
- Cheap UX recovery — gives users feedback that they probably misused a spec function without imposing real preconditions.

## `constexpr` Functions as Automatic Spec Functions

```cpp
constexpr bool is_power_of_two(int n) {
    return n > 0 && (n & (n - 1)) == 0;
}

void allocate(int n)
  pre(is_power_of_two(n))
{ ... }
```

Any uncontracted `constexpr` definition is automatically available as a spec
function — no `spec` keyword or re-declaration. A `constexpr` function with
`pre`/`post` clauses remains a modular executable function so its contract
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

**Contrast with explicit `spec`:** `spec int fibo(int n)` uses mathematical integers (Z3 `Int`, unbounded). Users pick:
- Want fast verification with abstract math semantics → write `spec`.
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

```cpp
write_data(buf, 512);
// At this call site, Clang evaluates is_power_of_two(512) → true.
// Z3 receives pre(true) for this site — no SMT reasoning needed.
```

This is unique to being inside the compiler.

## Proof Functions

```cpp
proof void lemma_fibo_monotonic(int i, int j)
  pre(i <= j)
  post(fibo(i) <= fibo(j))
  decreases(j - i)
{
    if (i < 2 && j < 2) {
    } else if (i == j) {
    } else if (i == j - 1) {
        lemma_fibo_monotonic(i, j - 1);
    } else {
        lemma_fibo_monotonic(i, j - 1);
        lemma_fibo_monotonic(i, j - 2);
    }
}
```

- Ghost functions that serve as proofs.
- Must terminate (proven via `decreases`).
- Body establishes that precondition implies postcondition.
- Can call other proof functions and spec functions.
- May mutate local proof values, but cannot write executable memory/global
  state or call executable functions.
- Every proof-function loop requires `decreases`.
- Not compiled — exist only for verification.
- **Integer semantics:** machine integers (matches `exec`).

## Quantifiers: forall / exists

```cpp
post(forall(i, 2, n, ret[i] == ret[i-1] + ret[i-2]))
//   forall(binder, lo, hi, body)
//   means: ∀i. lo ≤ i < hi → body

pre(exists(j, 0, n, arr[j] == target))
//   means: ∃j. 0 ≤ j < n ∧ body

post(forall(k, sq(k) >= 0))
//   forall(binder, body): ∀k ∈ ℤ. body
```

- `binder` is a fresh mathematical integer, scoped to `body`.
- `lo` and `hi` must be integer; `body` must be bool.
- Without bounds the quantifier ranges over all mathematical integers. A
  counterexample to one is certified exactly when its body depends on its
  binders through linear arithmetic, comparisons, memory and collection
  reads, and other quantifiers, nested to any depth: once the model fixes
  everything else, each read is one of finitely many constant pieces, which
  leaves a sentence of Presburger arithmetic that the certifier decides.
  Otherwise (a product or quotient of binders, or a spec applied to a binder)
  it is `counterexample.unchecked`.

### Triggers

```cpp
pre(forall(k, 0, n, trigger(a[k]) > 0))
```

- `trigger(term)` marks `term` as the pattern that instantiates the
  quantifier, as Verus's `#[trigger]` does. It must be a memory read, a
  collection read (`s[k]`, `contains`, `count`, map `[]`), or a call of a
  recursive spec function, and it must mention a quantified variable; other
  marks are ignored with a warning (a non-recursive spec is replaced by its
  body, so mark a term of the body). Several marks in one body form one
  multi-pattern. Without marks the solver chooses patterns itself.
- `trigger` is contextual: a function or variable named `trigger` keeps its
  meaning.
- `--profile-quantifiers` reruns each query the solver left unresolved and
  reports how often each quantifier was instantiated, and up to which
  generation (`note: the quantifier at L:C was instantiated N times, up to
  generation G`; JSON `quantifier_profile`), which exposes matching loops.
- Patterns steer the solver; they never change meaning. They are not part
  of archives or semantic hashes.

### choose

```cpp
spec int half(int n) { return choose(k, 2 * k == n); }
spec int index_of(const int *a, int n, int x) { return choose(k, 0, n, a[k] == x); }
```

- `choose(k, body)` is an integer for which `body` holds, when one exists,
  and otherwise an unspecified integer (Hilbert ε); `choose(k, lo, hi, body)`
  chooses in `[lo, hi)`. Each `choose` is a function of the values its body
  mentions, so it is the same for the same values.
- The verifier knows only that: a claim true for some choices but not all
  fails with a certified counterexample for another choice.
- `choose` exists only for verification; Sema rejects it in executable code.
  It is contextual, like `trigger`.

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
ordinary pre/`modifies`/post abstraction controls the value heap. A recursive
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
collections); a user-declared `spec bool valid(T *p, int n)` is the same
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
- a loop writes only its stores' origins (and, with a function `modifies`,
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
pre(p != q && p != r && q != r && ...)   // for all distinct mut ptr/ref pairs
```

- The caller's verification must establish these inequalities. Calling `swap(&x, &x)` produces a precondition failure.
- A pointer carrying a `valid(p, n)` extent contributes the
  whole extent (`n * sizeof(T)` bytes) as its complete object, so the pair is
  disjoint unless either pointer is null or either extent is empty. Callers
  prove disjointness of the extents they pass. An `aliases` pair keeps the
  single-object rule and may share storage, as `memmove` does.
- **This is NOT the C++ `__restrict__` keyword.** `__restrict__` is a compiler optimization hint affecting codegen; the implicit assumption above is a verification-level precondition affecting correctness. The keyword `__restrict__`, if present, is a no-op for verification.

### 3. `aliases(p, q)` opt-out

If a function legitimately accepts aliased parameters, declare it:

```cpp
void copy_or_self(int* dst, int* src)
  aliases(dst, src)
  pre(dst != nullptr && src != nullptr)
  modifies(*dst)
  post(*dst == old(*src))
{
    *dst = *src;
}
```

The `aliases(dst, src)` clause disables the implicit `dst != src` precondition
for this function. The body must verify under both `dst == src` and `dst != src`.
The same rule applies to supported scalar lvalue-reference parameters.

### 3a. Scalar lvalue references and automatic scalar objects

Contracted executable free functions support `T&` and `const T&` parameters
when `T` is `bool`, integral, or enum. The reference binding lowers to an
immutable VCR address. A value use is a heap load, assignment is a heap store,
and `old(ref)` reads through the same address in the entry heap.

Every reference receives a generated non-null, live, and initialized entry
precondition. Distinct address parameters are object-range disjoint by default
when at least one is mutable; `aliases` permits the same complete object.
`modifies(ref)` is an open region rooted at the referent, matching
`modifies(*p)`.

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

A provenance-backed scalar actual permits an open-region `modifies(ref)` or
`modifies(*p)` footprint to be framed as its exact scalar cell only after the
callee passes the structural non-escape scan. Immutable local reference aliases
are tracked transitively by that scan and retain the same owned lifetime
identity.

Addressable local declarations inside loops, `old(local)`, `old(local_ref)`,
subscript/field/conditional bindings, temporaries, reference returns,
address-taking, rvalue references, and non-scalar referents remain fail-closed.
An outer automatic local and a local reference declaration may be used inside a
loop. Recursive executable bodies that allocate an automatic object or store
through references fail closed until the termination collector models heap
state updates.

### 4. `modifies(...)` frame condition

```cpp
void incr_first(int* a, int* b)
  modifies(*a)              // promises: only writes to *a; *b unchanged
  post(*a == old(*a) + 1)
{
    *a = *a + 1;
}
```

- `modifies(X, Y, Z)` lists every footprint the function may write to.
  Anything not listed is preserved.
- Every store to memory the function did not create itself (its own locals
  and allocations) must lie in a footprint, as Frama-C's WP checks
  `assigns`; a function without `modifies` stores only to its own storage.
- A callee whose writes are not stated, because its contract has no
  `modifies` while it takes a mutable pointer or reference and may write
  (a trusted contract, or a verified function that calls such a callee), is
  treated as writing the whole heap at a call: a caller with its own
  `modifies` cannot call it, and a caller without one forgets every cell.
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
  value, and specs with `reads` clauses outside the footprints keep theirs.
  When every footprint is a cell, the effect is a chain of stores of fresh
  values; otherwise it is a frame relation over the regions. Region
  footprints need the object model: under `--no-check-ub` a call with one
  forgets the whole heap.
- Preconditions and `old(parameter)` use entry actual arguments, and so does
  a parameter named in a postcondition.
- General reference binding and member-function effects are not yet in the
  verified subset.

### Worked example

```cpp
void swap(int* a, int* b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}

int compute() {
    int x = 5;
    int y = 10;
    int z = 100;
    swap(&x, &y);
    // Verifier knows:
    //  - x and y are non-aliased (implicit default) OK
    //  - swap modified only *(&x) and *(&y)
    //  - therefore z is unchanged
    contract_assert(z == 100);          // verifies
    contract_assert(x == 10 && y == 5); // verifies from post
    return x + y + z;
}
```

## Type Invariants

```cpp
class Coordinate {
    int x;
    int y;
    type_invariant(x >= 0 && y >= 0);   // must appear after the fields it names
};

int dist_sq(Coordinate p, Coordinate q) {
    // Verifier auto-injects (lazy — only because the body accesses .x and .y):
    //   assume(p.x >= 0 && p.y >= 0);
    //   assume(q.x >= 0 && q.y >= 0);
    int dx = p.x - q.x;
    int dy = p.y - q.y;
    return dx*dx + dy*dy;
}
```

- `type_invariant(expr)`: holds for every instance of the type at all times.
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
- New keyword `type_invariant` in `TokenKinds.def` under KEYCONTRACT.
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

When verifying code over a concrete data structure, define `spec` functions that produce a mathematical view of the data. Specs are then written against the view, not the internals.

```cpp
class SortedArray {
    int data[100];
    int len;
};

// abstract view: what the structure means mathematically
spec int elem(SortedArray a, int i) { return a.data[i]; }
spec int size(SortedArray a) { return a.len; }

bool contains(SortedArray a, int target)
  pre(size(a) > 0 && size(a) <= 100)
  post(result == exists(i, 0, size(a), elem(a, i) == target))
{ ... }
```

- No new syntax. `spec` functions named `view()`, `elem()`, `size()`, etc. are a documented convention.
- The verifier treats these spec function bodies as axioms (definitions), not as code to execute.
- This is Verus's main abstraction idiom and the recommended style for non-trivial data structures.

## Integer Semantics — summary

| Function kind | Integer semantics | Solver encoding |
|---|---|---|
| `spec` function (explicit) | Mathematical (unbounded) | `Int` |
| `constexpr` lifted as spec | Machine (overflow happens) | `BitVec(N)` or range-checked `Int` |
| `proof` function | Machine | `BitVec(N)` or range-checked `Int` |
| `exec` (regular) function | Machine | `BitVec(N)` or range-checked `Int` |
| Contract arithmetic (`pre`, `post`, invariants, assertions) | Mathematical | `Int` |

- Contracts are mathematical, as in ACSL and Verus: `+`, `-`, `*`, `/`, `%`,
  and unary `-` on the values of C++ expressions are exact, so
  `post(result + 1 > result)` holds. An implicit conversion whose result C++
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
- Mathematical `spec` division and remainder are unbounded but use C++'s
  truncate-toward-zero sign convention. At a zero divisor their total logical
  extension is quotient zero and remainder equal to the dividend; evaluated
  executable and contract expressions must still prove a nonzero divisor.
- `--int-encoding` selects how machine integers reach the solver: `auto`
  (default; integers unless a query needs the bits of a non-constant
  operand), `integer`, or `bitvector`. Every choice is exact, so it changes
  solver performance, never semantics. A query left unresolved under a forced
  `bitvector` encoding is retried with `auto`.

## old() Expression

```cpp
post(result == old(x) + 1)
post(result == old(*p))
```

- Refers to the value of an expression at function entry.
- Valid in postconditions and loop invariants. In either location it denotes
  the enclosing function's entry state, not the previous iteration.
- The inner expression is evaluated in the pre-state. For pointer-typed expressions, `old(*p)` is the value at the pre-state heap.

## result Expression

```cpp
post(result > 0)
post(result.size() == n)
```

- Refers to the return value of the enclosing function.
- Only valid in postconditions.
- Type is computed via `Sema::GetTypeForDeclarator` from the full Declarator.
- Supports postfix operators: `result.x`, `result[i]`.

## reveal_with_fuel (control recursive spec unfolding)

```cpp
spec int fibo(int n) decreases(n) { ... }

int safe_fib(int n) pre(...) post(result == fibo(n)) {
    ghost {
        reveal_with_fuel(fibo, 5);  // unfold fibo up to 5 levels in this VC
    }
    ...
}
```

- Default fuel for any recursive spec: **1**.
- `reveal_with_fuel(fn, n)` locally raises the unfolding depth Z3 uses for `fn` within the enclosing function's VC.
- Without this, recursive `spec` axioms cause Z3 matching loops.
- Inside ghost blocks only.

## hide / reveal

- `hide(fn_name)` and `reveal(fn_name)` in ghost blocks selectively control whether the body of a spec function is visible to Z3.
- Default for non-recursive specs: visible (body inlined into queries).
- Default for recursive specs: one finite unfolding step. Deeper unfolding
  requires `reveal_with_fuel`.
- `hide` suppresses defining equations while leaving the function application
  available to contracts and imported lemma postconditions. This is useful
  after a finite lemma has established all facts needed by a large arithmetic
  proof: irrelevant recursive equations can otherwise dominate solver time.
- `hide` withholds the definition from proofs, not from the meaning of the
  program. A counterexample must still hold under the hidden function's true
  definition; a query that only its definition would settle is `Unresolved`
  with reason `spec.hidden`, never `Failed` and never `Verified`.
- Both constructs are implemented and are verification-only no-ops in CodeGen.

## Faithful verdicts

- `Verified`: every fact given to a solver is a consequence of the program's
  semantics: definitions, C++ machine arithmetic, and declared contracts.
- `Failed`: a counterexample that holds when every logical function is
  evaluated at its true definition. It is relative to the declared
  abstractions only: callee contracts, loop invariants, and `modifies`
  frames.
- Anything else is `Unresolved` with a reason. `spec.fuel`: every
  counterexample found relies on a recursive spec beyond what refinement could
  unfold, and strong induction on the query's integer variables did not
  prove it; `spec.hidden`: it relies on a hidden spec's value;
  `counterexample.unchecked`: the counterexample could not be checked within
  the certifier's budgets; `spec.termination`: the proof relies on a spec
  whose termination check did not pass, so that spec has no definition;
  `spec.reads`: the proof relies on a spec whose `reads` check did not pass,
  so its frames are not facts; `spec.post`: it relies on a spec whose
  postcondition is not established; `callee.contract`: it relies on a
  callee contract that nothing establishes: the callee's verification
  failed, or it has a contract but no definition and no trust mark;
  `decreases.missing`: a loop has no termination measure;
  `construct.unsupported`: the obligation that failed stands for a construct
  the verifier does not model, so its counterexample says nothing about the
  program; the message names the construct (for example "the operands of
  this pointer difference may address the objects of different parameters
  or globals, which may be one caller array").
- Qualifiers: `[partial]` (proved for terminating executions only, after
  `decreases(*)`), `[trusts=f]` (relies on the contract of `f`, marked
  `[[cppverify::trusted]]`), `[vacuous]` (no execution reaches the claim).

## Spec Collections

```cpp
#include <cppverify.h>
using cppverify::seq;

spec int sum(seq s)
  decreases(s.len())
{
  return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}

int count_positive(const int *a, int n)
  pre(valid(a, n) && n >= 0 && n <= 1000)
  post(0 <= result && result <= n)
{
  ghost seq seen = cppverify::seq_empty();
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && 0 <= c && c <= i)
    invariant(seen.len() == i)
    invariant(forall(k, 0, i, seen[k] == a[k]))
    decreases(n - i)
  {
    if (a[i] > 0)
      c = c + 1;
    ghost { seen = seen.push(a[i]); }
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
  sequence equality. A stated `contract_assert(a == b)` is therefore a hint
  where the solver needs one.
- Induction over a sequence is written by the user, as in Verus and Dafny: a
  recursive proof function with `decreases(s.len())` that cites itself on a
  shorter sequence:

```cpp
proof void sum_concat(seq s, seq t)
  post(sum(s + t) == sum(s) + sum(t))
  decreases(t.len())
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
  ghost code (`ghost seq s = ...;`, assignment in ghost blocks), and as
  parameters and results of spec and proof functions. Sema rejects every use
  in executable code (declarations, operations, parameters, results).
- A collection read can be a trigger, and counterexamples show collection
  values: `[1, 2]`, `{1, 3..5}` (a run), `{2: 3}` (counts), `{1 -> 7}`, and
  `{..}` (every integer).
- Backends: Z3 decides all four. cvc5 decides sequences; sets, multisets,
  and maps are `logic.unsupported` there, and Lean supports none.

## Clang Modification Details

### New Keywords (TokenKinds.def — KEYCONTRACT)

```
KEYWORD(pre,              KEYCONTRACT)
KEYWORD(post,             KEYCONTRACT)
KEYWORD(modifies,         KEYCONTRACT)
KEYWORD(aliases,          KEYCONTRACT)
KEYWORD(recommends,       KEYCONTRACT)
KEYWORD(invariant,        KEYCONTRACT)
KEYWORD(decreases,        KEYCONTRACT)
KEYWORD(type_invariant,   KEYCONTRACT)
KEYWORD(ghost,            KEYCONTRACT)
KEYWORD(spec,             KEYCONTRACT)
KEYWORD(proof,            KEYCONTRACT)
KEYWORD(contract_assert,  KEYCONTRACT)
KEYWORD(reveal_with_fuel, KEYCONTRACT)
KEYWORD(forall,           KEYCONTRACT)
KEYWORD(exists,           KEYCONTRACT)
KEYWORD(old,              KEYCONTRACT)
KEYWORD(result,           KEYCONTRACT)
```

KEYCONTRACT flag: only active when `-fverify-contracts` is passed. Otherwise these are valid identifiers.

`reads`, `when`, `inductive`, `behavior`, `complete_behaviors`,
`disjoint_behaviors`, `calc`, `trigger`, and `choose` are contextual: they are recognized only in
their contract positions (and `calc`, `trigger`, `choose` only when no
declaration of that name is visible), so ordinary code keeps those names.

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
it only as a whole `modifies` footprint. A `trigger(term)` mark leaves `term`
in place and records it in an `ASTContext` side table.

**Statements (inherit from Stmt):**

| Node | Fields |
|---|---|
| ContractAssertStmt | Expr (the condition), optional CompoundStmt (the `by` proof); `calc` builds nested ones |
| GhostBlockStmt | CompoundStmt (the body); `ghost T x = e;` wraps its declaration |
| RevealWithFuelStmt | FunctionDecl* fn, int fuel |

**Side-table info on existing nodes:**

| Existing Node | New Data |
|---|---|
| FunctionDecl (via ASTContext side table) | preconditions, postconditions, modifies, aliases, recommends, isSpec, isProof, decreases, behavior checks |
| WhileStmt / ForStmt / DoStmt | invariants, decreases, modifies |
| RecordDecl | type_invariants |
| VarDecl | ghost marker |

### Parser Entry Points

| Syntax Position | Parser Method | File |
|---|---|---|
| After function declarator `)` | ParseContractClauses() | ParseDecl.cpp |
| After a while/for condition or a do-loop trailing condition | ParseLoopContracts() | ParseStmt.cpp |
| `ghost { ... }` | ParseGhostBlock() | ParseStmt.cpp |
| `contract_assert(...)` | ParseContractAssert() | ParseStmt.cpp |
| `reveal_with_fuel(...)` | ParseRevealWithFuel() | ParseStmt.cpp |
| `spec type name(...)` | ParseSpecFunction() | ParseDecl.cpp |
| `proof void name(...)` | ParseProofFunction() | ParseDecl.cpp |
| `forall(...)` / `exists(...)` | ParseQuantifierExpr() | ParseExpr.cpp |
| `old(...)` | ParseOldExpr() | ParseExpr.cpp |
| `result` | ParseResultExpr() | ParseExpr.cpp |
| `type_invariant(...)` inside record | ParseTypeInvariant() | ParseDecl.cpp |

### Sema Rules

1. All contract expressions must be contextually convertible to bool (except `decreases` which must be integer; and `modifies` lvalues which need ordinary lvalue typing).
2. `old(expr)` is only valid in postconditions and loop invariants; both use
   the enclosing function's entry state.
3. `result` is only valid in postconditions. Its type matches the enclosing function's return type.
4. Quantifier binders are pushed into scope during body type-checking, popped after.
5. Spec functions must have no side effects (no assignments to non-local state, no I/O calls).
6. Proof functions must return void.
7. Ghost blocks may only contain ghost-safe statements. They can update
   ghost-local variables/direct dot-fields and call proof functions, but cannot
   mutate executable state, call executable functions, return from the
   enclosing function, or contain a loop without `decreases`.
8. `modifies` lvalues must be ordinary lvalues; the parser computes their alias keys for the encoder.
9. `aliases(p, q)` arguments must be pointer/reference-typed parameters of the enclosing function.
10. `recommends` is only valid on `spec` functions.
11. A `spec` function may be referenced only from contracts, ghost code, and
    `spec` or `proof` functions; executable code, including initializers and
    default arguments, may not reference one. Unevaluated operands
    (`sizeof`, `decltype`) are exempt.
12. The same holds for ghost variables, `choose`, and the `cppverify`
    collections (their types as executable declarations, parameters, or
    results, and every operation).
13. A range `p[lo : n]` needs a pointer to a complete object type and
    integer bounds, and is valid only as a whole `modifies` footprint.

### CodeGen Rules

- `GhostBlockStmt` → emit nothing
- `ContractAssertStmt` → emit nothing (or optionally emit runtime assert in debug mode)
- `RevealWithFuelStmt` → emit nothing
- Functions with `isSpec` or `isProof` → skip entirely (already gated in CodeGenModule)
- All contract clauses on FunctionDecl → ignored by codegen
- Loop invariants/decreases → ignored by codegen
- `type_invariant` on RecordDecl → ignored by codegen

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
Failure-only `recommends` diagnostics do not alter archive contents.
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
`spec.reads`, `spec.post`, and `counterexample.unchecked`.
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
The persistent cache, when requested, memoizes only the portfolio's
namespace-separated Z3 component and never skips cvc5. BMC remains Z3-backed,
and bounded archives must replay through the BMC aggregator.

BMC remains a VCR loop transformation followed by the shared passive,
obligation, and Z3 path. Source verification treats `--unroll=N` as a maximum
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
| Framed output | factorial range | null or out-of-frame writes | non-null pointers, `modifies(*out)`, `old(*preserved)`, heap framing |

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
