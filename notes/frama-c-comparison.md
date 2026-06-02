# Frama-C vs CppVerify — Comparison and Edges

Sources: https://frama-c.com/, https://frama-c.com/fc-plugins/frama-clang.html, ACSL Reference Manual (public).
Written: 2026-05-13. Companion to `verus-paper-analysis.md` and `boogie-paper-analysis.md` — completes the picture of the deductive-verification landscape we operate in.

---

## 1. What Frama-C is, structurally

Frama-C is an **analysis platform** for C — not a single verifier. It's a framework into which multiple analysis plugins are loaded; each plugin brings a different technique. The three load-bearing plugins:

| Plugin | Technique | What it proves |
|---|---|---|
| **WP** | Weakest-precondition + SMT (Alt-Ergo / CVC5 / Z3 via Why3) | Functional correctness against ACSL contracts |
| **EVA** | Abstract interpretation | Absence of runtime errors (no UB, no overflow, no null deref) — *without* contracts |
| **E-ACSL** | Code instrumentation | Compiles ACSL annotations into runtime asserts |

WP is our direct architectural peer. EVA is a different paradigm. E-ACSL is orthogonal.

Maturity: 15+ years. Used in **DO-178C**-certified avionics, **IEC 60880**-certified nuclear, **Common Criteria EAL 6-7** evaluations. WP reportedly auto-discharges 98% of VCs on real projects.

---

## 2. Architecture comparison

| Aspect | Frama-C / WP | CppVerify |
|---|---|---|
| Source language | C99 (first-class) | C++20+ (first-class) |
| Frontend | Custom OCaml C parser + CIL | Clang (forked at `llvmorg-22.1.3`) |
| C++ support | Frama-Clang plugin — explicitly experimental; translates C++ → C losing type info | Native: Clang Sema + full `QualType` propagation |
| Intermediate language | Why3 (multi-prover IVL) | VCR Layer 1 → Layer 2 (custom Boogie-like IVL) |
| Provers | Alt-Ergo, CVC5, Z3 — pick best per VC | Z3 only (MVP); multi-prover post-MVP |
| Backend automation | 98% auto-discharge (mature) | TBD — MVP target |
| Coq escape hatch | Yes — drop to interactive proof for hard VCs | No |

**Frama-Clang reality check:** their own docs say "currently in an early stage of development. It is known to be incomplete and comes without any bug-freeness guarantees." It translates C++ to C, dropping templates / inheritance / move semantics / RAII. After translation the verifier sees C, not the C++ program written.

---

## 3. Specification language comparison

### ACSL (Frama-C)
- Comment-based: `/*@ requires ...; ensures ...; */` — invisible to the C compiler.
- Backslash namespace: `\result`, `\old`, `\valid`, `\separated`, `\forall`, `\exists`.
- Distinct logic language: `axiomatic`, `logic`, `predicate`, `lemma`, `inductive`.
- Mathematical integers (`integer`, `real`) as first-class types.

### CppVerify
- First-class keywords: `pre`, `post`, `result`, `old`, `forall`, etc. — real tokens.
- No backslashes, no separate namespace.
- Unified language: `spec` functions ARE C++ functions, annotated.
- Two-tier integer semantics: explicit `spec` uses math `Int`; lifted `constexpr` uses machine `BitVec`.
- `constexpr` IS a spec — single body for runtime and verification.

**Deepest difference:** ACSL is a second language living in comments. CppVerify contracts are C++ that Clang parses and type-checks. There is no second language and no wall.

---

## 4. C++ support — the structural moat

This is where CppVerify has the largest gap to close on Frama-C (we have zero years of maturity), but also where Frama-C has the largest STRUCTURAL gap to us (their C++ story is a prototype).

Frama-Clang:
- Translates C++ → C, losing type information.
- Templates: instantiate but constraints don't propagate.
- Inheritance: flattened.
- `unique_ptr<T>`: becomes a struct of pointers (ownership semantics vanish).
- ACSL++ exists, but most C++ type info is invisible to it.
- No native support for: concepts, fold expressions, ranges, coroutines, modules, C++20 contracts (P2900), C++26 reflection.

CppVerify:
- Clang's full C++ frontend, riding standards evolution.
- Contracts carry full `QualType` — bit-widths, signedness, template parameters, struct layout, typedef chains.
- Templates, lambdas, `constexpr`, references, `unique_ptr` are all there at the IR level.

---

## 5. Pipeline comparison

```
Frama-C/WP:  C source + ACSL comments
              → CIL (Frama-C's IR)
              → WP plugin (computes VCs)
              → Why3 (multi-prover IVL)
              → Alt-Ergo / CVC5 / Z3 (chooses best)
              → result + counterexample

CppVerify:    C++ source + contracts
              → Clang AST (full type info preserved)
              → VCR Layer 1 IR (Boogie-like)
              → Passive Layer 2 IR (SSA + heap-SSA)
              → WP calculus
              → Z3 (single solver, MVP)
              → result + counterexample
```

Frama-C's Why3 → multi-prover routing is more flexible than our Z3-only path. **Real advantage they have.** Adding Why3-style routing is a viable post-MVP step for us.

---

## 6. Memory and framing comparison

| Concern | Frama-C/WP | CppVerify |
|---|---|---|
| Heap models | Multiple ("Typed", "Bytes", "Hoare") — pluggable | Single Z3 array per type (Boogie §5.0 Pattern 2, simplified) |
| Aliasing default | User declares `\separated(p, q)` explicitly | Implicit non-aliasing; opt-out with `aliases(p, q)` |
| Framing | `assigns` clause | `modifies(...)` clause |
| Type invariants | ACSL `type invariant`, **eagerly injected** | `type_invariant`, **lazily injected** |
| Pointer arithmetic | Fully supported | MVP: simple pointers; arithmetic post-MVP |

---

## 7. Where Frama-C clearly beats us (honest assessment)

1. **15+ years of maturity** vs our zero.
2. **Multi-prover via Why3** — Alt-Ergo, CVC5, Z3; we have only Z3.
3. **Abstract interpretation (EVA)** — fully automatic, no contracts needed.
4. **Coq escape hatch** for the hardest VCs.
5. **Runtime checking via E-ACSL** — compile contracts to runtime asserts.
6. **Certification track record** — DO-178C, IEC 60880, EAL 6-7.
7. **C99 fragment is essentially complete** — pointers, unions, function pointers, casts, bit-fields, variadic.
8. **Mature memory models** — typed/bytes/hoare are pluggable.
9. **Strong ACSL standardization** — stable reference manual.
10. **Plugin ecosystem** — WCET analysis, slicing, dependency analysis, taint, security policy.

None of these are MVP-reachable. Some we never need to match (different focus). Several (Why3, EVA, Coq) are reachable post-MVP if we want.

---

## 8. The ten structural edges of CppVerify over Frama-C

These follow from CppVerify's architecture and **cannot be reproduced by Frama-C without rewriting major parts of their stack.**

### Edge 1 — Native C++ via Clang
Frama-Clang translates C++ → C, losing template parameters, virtual dispatch, RAII, move semantics, lifetimes, concept constraints. We operate on the actual Clang AST.

### Edge 2 — First-class syntax type-checked by the host compiler
ACSL lives in comments; renames/type changes can silently desync. Our contracts are real keywords — Sema catches errors immediately, clangd's rename refactoring updates them, type errors propagate.

### Edge 3 — `constexpr` as single source of truth
The C++ runtime body and the verification spec are the same body. They can never drift. Frama-C requires duplicate ACSL `logic` definitions plus bridging lemmas.

### Edge 4 — Compile-time partial evaluation
We use Clang's `Expr::EvaluateAsInt()` directly on contract subexpressions — concrete-argument `constexpr` calls fold before reaching Z3. Frama-C cannot access Clang's evaluator.

### Edge 5 — Zero-cost incremental adoption
Just `-fverify-contracts` on the existing build. Per-TU opt-in. Without the flag, contracts are valid identifiers, binary is unchanged. Frama-C requires a separate pipeline.

### Edge 6 — Lazy `type_invariant` injection
We inject `assume`/`assert` only at fields actually referenced. Frama-C's ACSL `type invariant` is eagerly injected at every parameter/return — VC bloat scales with field count, not field use.

### Edge 7 — LSP-native toolchain via clangd
Contracts are real C++, so clangd already parses them. VSCode/CLion/Vim integration is automatic. Frama-C has a Qt GUI but no LSP.

### Edge 8 — P2900 alignment for C++26 contracts
Our syntax is deliberately aligned with the ISO C++26 contract proposal. Code written for CppVerify will be standard C++ when the standard ships. ACSL is its own non-standard annotation language.

### Edge 9 — Sema-time contract type errors
Contract type errors surface from Clang Sema at the same severity as any C++ error, with full context. Frama-C surfaces them only when WP runs — longer feedback loop.

### Edge 10 — Free leverage from the Clang ecosystem
clang-format, clang-tidy, AddressSanitizer, all target architectures, all build systems, all future C++ standards — we get them automatically. Frama-C built their OCaml ecosystem from scratch; they don't get this leverage.

---

## 9. Summary table — what each edge requires Frama-C to do to match

| Edge | Can Frama-C ever match? |
|---|---|
| 1. Native C++ via Clang | Only by rebuilding their pipeline on Clang (Frama-Clang attempted; stalled) |
| 2. First-class syntax + Sema | No, requires source-level integration |
| 3. `constexpr` as spec | **No** — requires being the host compiler |
| 4. Compile-time partial eval | **No** — requires being the host compiler |
| 5. Zero-cost adoption | No, separate analyzer needs separate pipeline |
| 6. Lazy type_invariant | Theoretically yes; requires rewriting their type-invariant handling |
| 7. LSP-native | No, requires Clang-based parser |
| 8. P2900 alignment | No, ACSL is a separate standard |
| 9. Sema-time errors | No, requires source-level integration |
| 10. Clang ecosystem | No, separate toolchain by definition |

**Structurally impossible for Frama-C without being us:** edges 1, 3, 4, 5, 10.
**Reachable but expensive for them:** edges 2, 6, 7, 8, 9.

---

## 10. Honest positioning

> Frama-C is the mature, multi-paradigm analysis platform for C. CppVerify is the Clang-native deductive verifier for modern C++. Frama-C will keep being the right answer for C99 codebases in regulated industries that have already standardized on it. CppVerify will be the right answer for any C++ codebase that wants verification as a natural extension of the existing build — and for any code where templates, `constexpr`, `unique_ptr`, or other modern C++ features need to be reasoned about, not flattened away.

The two tools don't compete for the same market. Frama-C owns regulated-C verification. We aim to own C++ verification — a market they (and everyone else) have failed to capture.

---

## 11. Implications for CppVerify's design

- **Prove the C++-specific advantages early.** The first compelling demo must show `constexpr` lifting, template-instantiated specs, `unique_ptr` ownership, or `consteval` precondition folding — things Frama-C structurally cannot do well.
- **Don't try to match Frama-C on C99 maturity.** Pure C codebases have a great answer in Frama-C; we shouldn't try to compete there.
- **Why3 (multi-prover) is post-MVP, not pre-MVP.** Z3-only is enough to demonstrate the C++ edges; we can add multi-prover later if the proof-failure rate justifies it.
- **EVA-equivalent (abstract interpretation) is post-MVP.** It would be a meaningful addition (catches whole-class-of-bugs without contracts) but it's a major engineering effort orthogonal to the deductive path.
- **The 10 edges should appear in marketing.** "Why CppVerify, not Frama-C" is a real question — these edges are the answer.
