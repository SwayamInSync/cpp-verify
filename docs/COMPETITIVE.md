# Competitive Landscape

## Existing Tools for C/C++ Verification

| Tool | Approach | C++ Support | Frontend | Contract Syntax | Status |
|------|----------|-------------|----------|----------------|--------|
| Frama-C | Deductive (wp + SMT) | Prototype only (Frama-Clang) | Custom OCaml parser | ACSL comments | Active |
| VCC | Deductive (Boogie/Z3) | No (C only) | Custom | Annotation macros | Dead (~2015) |
| VeriFast | Deductive (separation logic) | No | Custom | Annotation comments | Slow development |
| CBMC | Bounded model checking | Partial | Custom (goto-cc) | User assertions only | Active |
| Kani | Bounded model checking | No (Rust only) | Rust MIR | Rust macros | Active |
| Verus | Deductive (SMT) | No (Rust only) | Rust compiler | First-class syntax | Active |
| **CppVerify** | **Deductive (wp + Z3)** | **Native, first-class** | **Clang (modified)** | **First-class syntax** | **In development** |

## Our Differentiators

1. **Only deductive verifier built on Clang** — all others use custom parsers that lag behind C++ evolution
2. **Only tool with native C++ support** — not C, not Rust, not a prototype plugin
3. **First-class contract syntax** — not comments, not macros. Full type checking via Clang Sema.
4. **C++26 contracts alignment** — syntax inspired by P2900, positioned for future standards integration
5. **Verus-like proof language** — spec functions, proof functions, ghost blocks. No other C++ tool has this.
6. **Type-preserving verification** — contracts carry full QualType from Clang. Signedness, bit-width, struct layout all available for precise VC generation.
7. **`constexpr` → single source of truth** — any `constexpr` function is automatically usable in contracts with no re-declaration. The key advantage is maintenance integrity: Verus developers maintain two separate bodies (`const fn` for execution, `spec fn` for verification) that can silently diverge when one is updated. We have one body. Purity and termination are already enforced by Clang's evaluator — no `decreases` clause needed for `constexpr`. Note: lifted `constexpr` functions use machine integer semantics (32-bit `int`, overflow-aware) by default — we do not silently switch to unbounded integers. Explicit `spec` functions use mathematical integers.
8. **Compile-time partial evaluation of contracts** — `constexpr` subexpressions with concrete arguments are evaluated by Clang before Z3 sees them. For concrete callsites, Z3 is never involved. No plugin-based verifier has access to the host compiler's constant evaluator.
9. **Zero-cost incremental adoption** — without `-fverify-contracts`, the binary is identical to standard C++. Existing codebases add contracts one function at a time with zero disruption. Verus requires wrapping all code in `verus! { }` which changes operator precedence and produces non-standard Rust that regular tooling cannot process.

## Verus Specifically: What We Have That They Can't

Verus is the closest architectural peer (deductive, SMT-based, first-class syntax). The gap is not maturity — it is structural:

| Capability | Verus | CppVerify |
|---|---|---|
| Reuse existing helper functions in specs | ❌ must re-declare as `spec fn` | ✅ `constexpr` usable directly |
| Single body for spec and execution | ❌ two bodies that can diverge silently | ✅ one `constexpr` body, always in sync |
| Termination proof for constexpr specs | ❌ must write `decreases` always | ✅ Clang's step-limit is the proof |
| Default integer semantics | Mathematical (`nat`/`int`, unbounded) | Machine (`int` = 32-bit, honest overflow) |
| Compile-time spec evaluation | ❌ separate evaluation worlds | ✅ Clang evaluates constexpr in contracts |
| Zero-annotation-change adoption | ❌ requires `verus! { }` wrapper | ✅ `-fverify-contracts` flag only |
| Target language installed base | Rust (~4M devs) | C++ (~12M devs, safety-critical industries) |

## Honest Assessment

- Frama-C has 15+ years of engineering maturity. Our MVP won't match its proof automation.
- VeriFast's separation logic gives it heap reasoning we won't have initially.
- CBMC handles full C semantics including pointers, casts, unions — our initial fragment is tiny.
- Verus has a richer standard library (vstd) and parallel verification. We won't match these at MVP.
- Our advantage is structural (Clang-native, C++, constexpr bridge) and market (C++ has no competitor).

## Positioning

"The only deductive verification tool for modern C++ built on Clang — where your existing `constexpr` functions become verification specs for free."
