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

## Current Differentiators and Research Hypotheses

1. **Compiler-native architecture** — CppVerify extends Clang rather than
   maintaining a separate C++ parser and type checker.
2. **First-class syntax for a documented C++ subset** — contracts are parsed
   and type-checked by Clang Sema. This is not a claim of general C++ coverage.
3. **Typed verifier boundary** — contracts retain Clang `QualType`,
   signedness, bit width, layout, conversions, and source locations when
   lowering to VCR.
4. **Verification-only language** — spec functions, proof functions, ghost
   blocks, and loop/function contracts are explicit AST constructs and emit no
   runtime code.
5. **Machine-faithful arithmetic** — executable and proof code retain
   fixed-width integer semantics and explicit undefined-operation checks;
   explicit spec functions use mathematical integers.
6. **Experimental `constexpr` bridge** — concretely evaluatable calls can use
   Clang constant evaluation, while a supported symbolic body can be lowered
   with machine integer semantics. Before this becomes a soundness claim,
   symbolic lifting must enforce a conservative totality criterion or reject
   the helper. Clang's evaluation step limit is not a termination proof.
7. **Explicit evidence modes** — unbounded deductive proof, strict
   solver-portfolio proof, bounded safety, export, certification, timeout, and
   solver `unknown` remain distinct results.
8. **Incremental source adoption** — unannotated C++ remains ordinary C++ and
   individual supported functions can be contracted. First-class annotations
   themselves require the modified Clang frontend and
   `-fverify-contracts`; they are not standard C++ accepted unchanged by an
   upstream compiler.

## Comparison with Verus

Verus is the closest architectural comparator: it integrates deductive
verification with Rust and separates executable, proof, and specification
code. The systems make different tradeoffs rather than one strictly subsuming
the other.

| Concern | Verus | CppVerify |
|---|---|---|
| Host frontend | Rust compiler integration | Modified Clang frontend |
| Verification language | Rust-oriented exec/proof/spec modes | C++ contracts plus proof/spec/ghost constructs |
| Integer modeling | Explicit mathematical and machine-oriented types | Mathematical explicit specs; machine executable/proof and lifted `constexpr` |
| Recursive specifications | Checked termination measures | Explicit spec recursion requires `decreases`; automatic `constexpr` lifting still needs a closed totality policy |
| Executable helper reuse | Uses Verus's mode and specification mechanisms | Experiments with selected `constexpr` helpers and Clang constant evaluation |
| Current maturity | Evaluated research verifier with substantial examples and formal core | Research prototype with one flagship real-code extraction; broader evaluation and formalization remain open |

## Honest Assessment

- Frama-C has 15+ years of engineering maturity. Our MVP won't match its proof automation.
- VeriFast's separation logic gives it heap reasoning we won't have initially.
- CBMC handles full C semantics including pointers, casts, unions — our initial fragment is tiny.
- Verus has a richer standard library, broader evaluation, and a published
  formal core. CppVerify does not currently match that evidence.
- CppVerify's hypothesis is structural: sharing Clang's typed frontend may
  reduce semantic duplication for a useful C++ subset. A multi-project corpus
  and a formal translation result are still needed to establish it.

## Positioning

"A Clang-native deductive verifier that makes its supported C++ boundary,
machine semantics, and proof status explicit."
