# Verus Paper — Deep Analysis for CppVerify

Source: Lattuada et al., "Verus: Verifying Rust Programs using Linear Ghost Types" (extended version, 2303.05491v2).
Read fully on 2026-05-13. This document is the persistent reference for what we learned and what it means for CppVerify's plan.

---

## 1. Verus in one paragraph

Verus extends Rust with a deductive verification layer built on Z3 via weakest-precondition reasoning. Its key novelty is a **mode system** (spec / proof / exec) that distinguishes ghost mathematical code from ghost ownership-tracked code from real executable code, combined with **linear ghost permissions** (PPtr, PCell, PermData) that piggyback on Rust's borrow checker to verify low-level pointer code without separation logic. Verus forked the Rust compiler, added hooks, and built a separate driver that emits SMT-LIB to Z3.

---

## 2. Architectural ideas (relevant to CppVerify)

### 2.1 The mode system (Sections 2, 10)

Three modes with strict ordering `exec ⊑ proof ⊑ spec`:

|                             | spec              | proof            | exec              |
| --------------------------- | ----------------- | ---------------- | ----------------- |
| compiled                    | erased            | erased           | compiled          |
| style                       | purely functional | mutation OK      | mutation OK       |
| linearity/borrowing checked | **no**            | **yes**          | **yes**           |
| can call                    | spec              | spec, proof      | spec, proof, exec |
| determinism                 | deterministic     | nondeterministic | nondeterministic  |
| termination                 | must              | must             | optional          |
| pre/post                    | **none**          | requires/ensures | requires/ensures  |

**Why this matters:**

- spec functions are **total** by design → encoded as single SMT functions with one defining axiom. No precondition checks at call sites = no extra VCs = fast SMT.
- proof is the unique mode between: ghost but linearity-checked, so proof variables can carry abstract linear ownership (e.g., a `PermData<T>` is a proof variable).
- exec is real code.

**CppVerify analog:** We have spec/proof/ghost vocabulary but no linearity check on proof. C++ has no borrow checker, so this distinction is _not directly transferable_ — see §3 below.

### 2.2 Pipeline (Section 7, Figure 3)

Verus's pipeline: Rust AST → **AIR** (Verus's IR) → SMT-LIB. Conceptually:

- Spec functions → SMT function declarations + axiom definitions
- Exec/proof functions → SSA-renamed assignments to SMT constants
- `&mut T` parameter → pair `(pre_a, a)` SMT constants
- `&T` parameter → single SMT constant
- Polymorphism via a `Poly` sort + `I/%I` cast functions (Boogie-style)
- Machine-width invariants via `uInv 64 x` predicates

**Borrow checker buys aliasing-freedom for free** → encoding can treat references as values, no heap model needed for safe code.

**Maps to CppVerify:** Same pipeline shape (Clang AST → VCR Layer 1 → Passive Layer 2 → wp → Z3). The "no heap model for safe code" trick is **not available to us** — see §3.

### 2.3 Linear ghost permissions (Sections 4–6) — Verus's structural moat

`PPtr<T>` + `PermData<T>` pattern:

- `PPtr<T>` is a runtime pointer (compiled to a raw pointer).
- `PermData<T>` is a _proof variable_ — linear, ghost, erased — that records `(view().pptr, view().value: Option<T>)`.
- `PPtr::write(&mut perm, v)` requires linear ownership of `perm`.
- `PPtr::read(&perm)` takes a shared borrow.

Rust's borrow checker enforces linearity on the permission, so the verifier doesn't need separation logic or a heap model. Pointers are values in the SMT encoding. This is how Verus verifies XOR doubly-linked lists, lock-free FIFO queues, and reader-writer locks.

**This trick requires linear types or a borrow checker. C++ has neither.** Replicating PPtr in CppVerify would need either separation logic (heavy) or restrictive ownership rules (e.g., unique_ptr only, no raw aliasing) or user-declared `modifies` clauses (Frama-C style).

### 2.4 Termination, fuel, defaults

- `decreases(expr)` required on every recursive spec/proof. Each recursive call must strictly decrease.
- **Lexicographic decreases** (decreases tuple, lex-ordered) supported.
- `reveal_with_fuel(fibo, 2)` controls **how deep Z3 unfolds a recursive spec definition**. Without fuel, recursive specs → divergence or matching loops.
- Spec functions are **total**, so `default(τ)` exists for every type (`int defaults_to 0`, `Never defaults_to ⊥`).
- `Never` value `⊥` exists only in spec; `crash_never(e)` ensures it never leaks to exec.
- **Positivity restrictions** on recursive types — but only in spec/proof modes. Exec allows non-positive recursion (because it's allowed to diverge).

### 2.5 Quantifiers (Section 1, intro listing features)

- Bounded `forall(i, lo, hi, body)` and `exists`.
- Verus has both **automated and manual SMT trigger selection** for quantifiers.
- Integrated quantifier profiling to diagnose SMT performance.
- `choose` (Hilbert's ε) for spec functions — useful when you need _some_ witness.

**Triggers are not optional for performance.** Without them, Z3 either over-instantiates (slow) or under-instantiates (incomplete). CppVerify's DESIGN.md does not mention triggers — gap.

### 2.6 Spec encoding strategy (Section 2.2, Figure 3 walkthrough)

For the example `swap_odd(a: &mut u64, b: &u64)`:

```
(declare-fun is_odd.? (Poly) Bool)
(assert (forall ((n@ Poly)) (= (is_odd.? n@) (= (mod (%I n@) 2) 1))))

(declare-fun req%swap_odd. (Int Int) Bool)
(assert (forall ((pre%a@ Int) (b@ Int))
  (= (req%swap_odd. pre%a@ b@)
     (and (< (+ pre%a@ b@) 18446744073709551615)
          (is_odd.? (I b@))))))

(declare-fun ens%swap_odd. (Int Int Int) Bool)
(assert (forall ((pre%a@ Int) (a@ Int) (b@ Int))
  (= (ens%swap_odd. pre%a@ a@ b@)
     (and (uInv 64 a@)
          (= (is_odd.? (I a@)) (not (is_odd.? (I pre%a@))))))))

; VC for main:
(push)
(declare-const v@0 Int) (declare-const v@1 Int) (declare-const w@ Int)
(assert (not (=> (= v@0 0) (=> (= w@ 3)
  (and (req%swap_odd. v@0 w@)
       (=> (uInv 64 v@1)
          (=> (ens%swap_odd. v@0 v@1 w@)
              (and (is_odd.? (I v@1)) (is_odd.? (I w@))))))))))
(pop)
```

**Lessons:**

- Each spec function gets a single uninterpreted SMT function + an axiom defining it.
- Each exec/proof function gets a `req%foo.` predicate and an `ens%foo.` predicate.
- Local variables become SSA-numbered SMT constants.
- VC is generated by asking Z3 to falsify the implication; UNSAT = verified.

### 2.7 Math vs machine integers

Verus has **`int` (Z)** and **`nat` (N)** as first-class types — but **only usable in spec/proof code**. Exec code uses Rust's `u64`, `i32`, etc. Conversions are explicit (`n as nat`).

**Why:** Z3 is _dramatically_ faster on `Int` than on bit-vectors. Bit-vector spec reasoning means every `+` requires modeling overflow.

CppVerify's current plan: lifted `constexpr` uses BitVec by default; explicit `spec` uses... not specified, but the design doc implies math integers. Worth re-examining.

### 2.8 UX features

- **`recommends`**: soft preconditions on spec functions. Spec is total → no real preconditions. But `recommends` lets you attach hints; checked only on verification failure for warnings. Cheap UX win.
- **`view()` convention**: spec function from concrete type → math abstraction (DList → Seq). Specs are written against the view.
- **Borrow checker pre-empts Z3**: aliasing bugs surface as compile-time errors, not as obscure SMT failures. Verus authors contrast this with Dafny, where aliasing becomes a postcondition-failure mystery.
- Verus emits Clang-quality diagnostics with source pointers.

### 2.9 Implementation

- Forked rustc; built a separate driver linked against the Rust compiler.
- Z3 via SMT-LIB.
- Small examples: 0.1s–5s verification time. 200–500 line programs.

---

## 3. CppVerify alignment & gaps

### ✅ Where CppVerify is on the right track

1. **Clang-modification + first-class syntax** — analogous to Verus's rustc fork. Right architecture.
2. **Pipeline shape** (AST → VCR Layer 1 → Passive Layer 2 → wp → Z3) — same as Verus's AIR pipeline.
3. **Modular verification** — caller asserts pre / assumes post; callee assumes pre / proves post. Same as Verus.
4. **Total spec functions** (per DESIGN.md). Critical for cheap SMT encoding.
5. **`decreases` for termination** on recursive spec/proof. Matches Verus.
6. **Ghost code stripped at CodeGen** — already implemented and tested.
7. **Bounded quantifiers `forall(i, lo, hi, body)`** — matches Verus.
8. **`old()` / `result`** in postconditions.
9. **SourceLocation tracking on every AST/IR node** (per CLAUDE.md conventions) — enables counterexample diagnostics.

### ⚠️ Missing-but-important features (should be in MVP or near-MVP)

| Feature                                 | Why critical                                                                                       | Where to add                     |
| --------------------------------------- | -------------------------------------------------------------------------------------------------- | -------------------------------- |
| **`reveal_with_fuel`**                  | Recursive specs will diverge in Z3 without bounded unfolding. Not optional.                        | Weeks 5-6 spec-function encoding |
| **`recommends`** (soft preconditions)   | Spec functions are total → no built-in early UX feedback. recommends gives diagnostics on failure. | Weeks 5-6                        |
| **Quantifier triggers** (auto + manual) | Performance critical. Without explicit triggers, Z3 over- or under-instantiates.                   | DESIGN.md + Weeks 5-6            |
| **Lexicographic `decreases`**           | Needed for non-trivial recursion (e.g., Ackermann).                                                | Weeks 5-6                        |
| **`hide` / `reveal`**                   | Selectively unfold specs. Performance knob for big proofs.                                         | Post-MVP                         |
| **View functions convention**           | Establish `view()` idiom early — not in roadmap yet.                                               | Weeks 5-6 + examples             |
| **Math integer types for spec**         | Verus's `int`/`nat`. Without them, BitVec arithmetic dominates.                                    | Decision needed (see §4 below)   |
| **`choose` (Hilbert ε)**                | Useful in specs for "some witness" patterns.                                                       | Post-MVP                         |

### ❌ Questionable plan decisions (re-examine)

#### Decision A: `constexpr`-as-spec with BitVec semantics by default

`DESIGN.md` says any `constexpr` becomes a spec automatically, _using machine integer semantics_. Two problems:

1. **Verus deliberately separates `const fn` and `spec fn`** with the specific argument that mathematical-integer specs are faster and more usable for verification.
2. **BitVec everywhere = slow Z3**. Multiplication/division in BitVec mode is much harder than in `Int` mode. The "single source of truth" win is real but the verification-performance cost is also real.

**Suggested re-think:**

- Either keep `constexpr`-as-spec but lift integer ops to `Int` mode in contracts unless `--bv` is set.
- Or make `constexpr`-as-spec opt-in, not default. Default to explicit `spec` functions.

This decision is _not yet implemented_ — re-litigate before Weeks 3-4 lock in the IR shape.

#### Decision B: Pointers parsed in contracts but not verified

CLAUDE.md says pointer parsing is supported but verification is "TBD." A user writing `post(result != nullptr)` will get a parser/Sema pass but no actual verification, or worse, a verifier that treats the pointer as fresh symbolic data. This is worse UX than rejecting pointer contracts outright.

**Suggested fix:** Add a loud diagnostic for pointer-typed contract clauses until the verifier supports them, OR gate pointer-typed contracts behind a flag.

#### Decision C: `type_invariant` injection

CppVerify proposes type-level invariants auto-injected at every function boundary. Verus does _not_ have type invariants — it uses `view()` predicates and `InvCell<T>` (value-carrying invariants).

**Trade-off:**

- type_invariant is more ergonomic ("don't repeat `pre(x >= 0)` everywhere").
- But every parameter of type `Coordinate` injects assume + assert per invariant field → VC bloat.
- Verus's view-function approach is more explicit; users pay the annotation cost only when they want to.

Not necessarily wrong, but the verification-cost downside should be acknowledged.

### ❌ The hard one: no borrow checker → no linear ghost permissions

Verus's PPtr/PermData trick is the structural reason it verifies low-level pointer code well. Without a borrow checker, CppVerify has three architecturally-different choices:

1. **Full separation logic** (Frama-C / VeriFast / Viper) — heavy SMT, hard contract syntax, doesn't match the "C++ that feels natural" goal.
2. **Severely restricted aliasing** — e.g., `unique_ptr` only, no raw pointer aliasing in contracts. MVP-feasible, doesn't match "real C++" promise long-term.
3. **User-declared frame conditions** — `modifies(...)` clauses (Frama-C style). Familiar to ACSL users. Annotation burden grows.

**This is the #1 architectural decision deferred.** Decision should be made _now_ (direction, not implementation), because it shapes Layer 1 IR.

---

## 4. Critical decisions to make before locking Weeks 3-4

1. **Spec integer semantics**: BitVec by default vs `Int` by default for `spec` functions and lifted `constexpr`. Recommend `Int` for explicit `spec`, leave `constexpr` lifting as an open question.
2. **Heap/pointer direction**: separation logic vs restricted-aliasing vs frame conditions. Pick the direction, even if implementation is in Ring 2.
3. **Quantifier trigger syntax**: bounded `forall(i, lo, hi, body)` is fine for MVP, but design a trigger-attachment syntax now (e.g., `forall(i, lo, hi, body, trigger(...))`).
4. **`reveal_with_fuel` syntax**: must be in the parser before recursive specs work. Plan it.
5. **`recommends` syntax**: easy add to ParseContractClauses — schedule for Weeks 5-6.

---

## 5. What is fundamentally harder for CppVerify than for Verus

- **No borrow checker** → no free aliasing analysis → can't have linear ghost permissions naturally → heap reasoning will require explicit modeling (separation logic OR ownership annotations OR frame conditions).
- **No closed type system** → templates, multiple inheritance, virtual dispatch are open semantic problems. MVP correctly excludes them.
- **No effect system** → proof functions are ghost by convention, not by structural typing. Sema must check "spec functions have no side effects" ad-hoc.
- **C++ default semantics include overflow, pointer arithmetic, undefined behaviour** → spec writers must reason about more than Rust spec writers do.

## 6. What CppVerify can offer that Verus cannot

- **C++26 contract syntax alignment** (P2900) — positions us for standards integration.
- **`constexpr` bridge** — if we get the integer semantics right, the single-body argument is real and powerful.
- **Clang's full type machinery** — templates, typedefs, struct layout, qualified types are all available with no plugin gymnastics.
- **C++ installed base in safety-critical industries** — automotive, aerospace, finance, OS kernels.

---

## 7. Reading list / forward links

- Verus supplementary materials: https://doi.org/10.5281/zenodo.7718486
- Verus repo: https://github.com/verus-lang/verus
- Verus docs: https://verus-lang.github.io/verus/guide/
- Linear Dafny [Li et al. 2022] — the formal grandparent of Verus's linearity rules.
- Creusot [Denis et al. 2022] — closest peer to Verus; uses Why3.
- RustHorn [Matsushita et al. 2020] — CHC-based; alternative encoding strategy.
- Prusti [Astrauskas et al. 2022] — Viper-based, separation logic.
- RustBelt [Jung et al. 2018a] — Coq foundation for Rust type safety.
- L3 [Morrisett et al. 2005] — original linear capabilities idea.
- Boogie polymorphism encoding [Leino & Rümmer 2010] — Verus's `Poly` sort technique.
