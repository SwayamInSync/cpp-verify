# Locked Design Decisions

This file supersedes `open-decisions.md`. All decisions below are committed and reflected in `docs/DESIGN.md`, `docs/ARCHITECTURE.md`, and `docs/ROADMAP.md`. Rationale draws on the Verus paper analysis in `verus-paper-analysis.md`.

Decided: 2026-05-13.

---

## Decision 1 — Spec integer semantics: **two-tier system**

| Construct | Integer semantics | Z3 encoding |
|---|---|---|
| Explicit `spec` function | Mathematical (unbounded) | `Int` |
| Lifted `constexpr` function | Machine (overflow-aware) | `BitVec(N)` |
| `proof` and `exec` function | Machine | `BitVec(N)` (or `Int` with explicit `uInv 64` invariants — pick later) |

**Escape hatch (optional, post-MVP):** `spec bv int foo(int n) {...}` to force BitVec semantics on an otherwise-math spec function.

### Rationale

- Verus made math integers the default for specs because Z3 is 10–100× faster on `Int` than on `BitVec`. We adopt this for explicit `spec`.
- BUT `constexpr` is the *same code that runs at compile time*. Silently switching it to math integers would mean the verifier disagrees with the C++ evaluator. The "single source of truth" claim breaks. So lifted `constexpr` keeps machine semantics.
- The CppVerify edge over Verus: Verus forces one body and one semantics. We give the user a choice — write `spec` for fast math reasoning, write `constexpr` for runtime-honest reasoning.

### Implementation impact

- Layer 1 VType integers carry a `VIntMode` tag (`Math` | `Machine`).
- ASTConverter sets the tag based on whether the enclosing function is `spec` (Math) or `constexpr`-lifted (Machine).
- Z3 encoder branches on the tag.

---

## Decision 2 — Pointer reasoning: **heap model + implicit non-aliasing + `modifies(...)`**

This is three coupled mechanisms.

### 2a. Heap model

- Memory is encoded as a Z3 array: `(declare-const mem (Array Int Int))` conceptually (typed arrays for non-int data).
- `*p = v` → `(store mem p v)` produces a new heap `mem'`.
- `*p` (read) → `(select mem p)`.
- Z3's array theory handles aliasing correctness for free: if `p == q` then `(select mem p) == (select mem q)`.
- Layer 1 IR: `VPtr(inner: VType)`, `VLoad(ptr, type)`, `VStore(ptr, value)`.
- Layer 2 IR: heap is SSA-versioned just like a variable — `mem_0`, `mem_1`, ...

### 2b. Implicit non-aliasing default

- The verifier inserts an implicit `pre(p != q && p != /* other mut ptrs */)` at the start of every function with multiple mutable pointer/reference parameters.
- Caller's responsibility to honour this — calling `swap(&x, &x)` produces a precondition failure.
- **Opt-out:** `aliases(p, q)` clause on the function signature disables the implicit precondition for the named pair.
- **Not the same as C++ `__restrict__`.** `__restrict__` is a compiler-optimization hint affecting codegen; ours is a verification precondition affecting correctness. The `__restrict__` keyword is treated as a no-op for verification (the default already provides the assumption).

### 2c. `modifies(...)` clause

- New contract clause on function declarations.
- `modifies(X, Y, Z)` declares that the function may write to lvalues `X`, `Y`, `Z` and no others.
- Default if absent: pure functions modify nothing; functions with mutable pointer/reference parameters implicitly modify everything reachable via those parameters (conservative). Users narrow with explicit `modifies(...)`.
- Used by the verifier for framing: callers may assume any memory not listed is preserved.

### Rationale

- C++ has no borrow checker → Verus's "free aliasing from types" trick is unavailable.
- Heap model is the principled foundation: correct for any aliasing pattern. Z3 array theory is well-supported.
- Non-aliasing default matches modern C++ practice (most functions don't expect aliased parameters) and dramatically reduces SMT case-splitting.
- `modifies` is essential for modular verification: without it, every function call invalidates all caller state.

### Implementation impact

- `clang/include/clang/Basic/TokenKinds.def`: add `modifies`, `aliases` to KEYCONTRACT.
- `FunctionContractInfo` gains `Modifies: [Expr*]` and `Aliases: [(Expr*, Expr*)]` lists.
- Parser: extend ParseContractClauses to accept `modifies(...)` and `aliases(...)`.
- Layer 1 IR: pointer type, load/store, modifies/aliases recorded on VFunction.
- Z3 encoder: array sorts for heap, sign/zero-extension on pointer arithmetic if needed.

---

## Decision 3 — Quantifiers: **bounded-only for MVP**

- Only `forall(i, lo, hi, body)` and `exists(i, lo, hi, body)`. The `[lo, hi)` bound is the implicit trigger; Z3 instantiates for the bounded range only.
- No unbounded quantifiers or manual trigger annotations in MVP.
- Post-MVP: add unbounded `forall(i: T, body)` with optional `trigger(...)` syntax.
- Z3 quantifier-instantiation profiling wired into verifier diagnostics from day one.

### Rationale

- ~90% of useful spec predicates are bounded.
- Bounded quantifiers don't need user-supplied triggers — the range bound encodes them.
- Simpler mental model for users; we don't expose SMT internals.

---

## Decision 4 — `reveal_with_fuel(fn, depth)`: **adopt from Verus**

- New ghost statement parsable inside `ghost { }` blocks and at function-body top level.
- Default fuel per recursive spec function: **1** (matches Verus).
- User raises it locally: `ghost { reveal_with_fuel(fibo, 5); }`.
- Effect: the Z3 encoder emits up to `depth` levels of axiom-driven unfolding for the named spec function within the enclosing function's VC.

### Rationale

- Recursive `spec` functions encoded as Z3 axioms cause matching loops / unbounded unfolding without explicit control.
- Not optional for correctness — this is *the* mechanism that makes recursive specs work.

### Implementation impact

- New KEYCONTRACT keyword `reveal_with_fuel`.
- New `VRevealStmt(fn_name, depth)` in Layer 1 IR.
- Z3 encoder caches per-spec-function unfolding depth.

---

## Decision 5 — `recommends(...)`: **adopt from Verus**

- New contract clause for spec functions only.
- Parsed like `pre(expr)` but does NOT generate a VC at call sites.
- On verification failure of an enclosing function, the verifier performs a separate pass to check whether any `recommends` clauses of called spec functions were violated, and emits warnings.

### Rationale

- Spec functions are total → no real preconditions → users get no UX feedback when misusing them.
- `recommends` recovers that feedback at near-zero cost.

### Implementation impact

- New KEYCONTRACT keyword `recommends`.
- New field on `FunctionContractInfo`.
- Two-pass verification mode in the verifier driver.

---

## Decision 6 — `type_invariant`: **keep, but lazy injection**

- Syntax unchanged from existing plan: `type_invariant(expr)` inside a class/struct body.
- The verifier auto-injects assume/assert pairs at function boundaries — **but only for fields actually referenced in the function body**, not for every field with an invariant.
- For mutation points: `assert(invariant_holds_after_assignment)` is injected only for assignments to fields named in the invariant.

### Rationale

- Type invariants are a real ergonomic win over Verus (which has nothing equivalent).
- Eager injection (the naive approach) bloats VCs for functions that don't actually use the invariant fields. Lazy injection keeps VCs tight.
- For typical structs (2–5 invariant fields), the perf delta over eager injection is small but measurable on large codebases.

### Implementation impact

- `RecordDecl` side table for type invariants (per existing Weeks 4.5 plan).
- ASTConverter tracks which fields the current function body references; emits injection only for those.

---

## Decision 7 — Pointer contracts: **fully supported in MVP**

(Supersedes earlier "parsed but unverified" plan.)

- Pointer-typed contract clauses are verified end-to-end as part of the MVP, using the heap model from Decision 2.
- Weeks 3-4 will land: heap model in Layer 1 IR, `VLoad`/`VStore` nodes, Z3 array-theory encoding, wp rules for pointer assignments, and verification of a `swap(int* a, int* b)`-style example.

### Rationale

- An MVP that can't verify any function taking a pointer is not a useful tool. Most realistic C++ uses pointers somewhere.
- The heap model is well-understood (Boogie/Dafny have used it for years); the cost is mostly in IR design, not in unsolved research.

### Implementation impact

- Increases Weeks 3-4 scope. Realistic milestone: verify `abs(int)` AND `swap(int*, int*)` end-to-end by end of Week 4.

---

## Additional commitments

### Lexicographic `decreases`
- `decreases(a, b, c)` interpreted as lex order. **In MVP** — needed for non-trivial recursive proofs.

### View functions
- Convention documented in DESIGN.md: `spec` functions named `view()`, `elem()`, `size()` are the idiom for abstracting concrete types in specs. No new syntax — just convention + worked examples.

### `hide` / `reveal`
- Designed in DESIGN.md, implemented post-MVP.
- Default for non-recursive specs: visible (body inlined into queries).
- Default for recursive specs: hidden (only revealed via `reveal_with_fuel`).

### `choose` (Hilbert ε)
- Post-MVP feature. Documented as future work in DESIGN.md.

### Bitvector mode flag
- `--bv` flag flips machine-integer-mode globally. Cast nodes already carry fromType/toType (per architecture plan) so the encoder switch is mechanical.
- Post-MVP feature, but designed in from day one.

---

## Cross-references

- Full Verus rationale: [`verus-paper-analysis.md`](verus-paper-analysis.md)
- Updated DESIGN spec: [`../docs/DESIGN.md`](../docs/DESIGN.md)
- Updated pipeline architecture: [`../docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md)
- Updated milestone roadmap: [`../docs/ROADMAP.md`](../docs/ROADMAP.md)
