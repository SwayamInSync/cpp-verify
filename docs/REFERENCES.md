# References & Reading List

## Essential Reading (in order of priority)

### 1. "This is Boogie 2" — K. Rustan M. Leino (MSR, 2008)
- **PDF**: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf
- **Why**: Defines the intermediate verification language our VCR IR is modeled after. Covers havoc, assume, assert, two-state contexts (old/result), modular verification, quantifiers. Read sections 2, 4, 6, 7, 9.
- **Read before**: writing any IR code.

### 2. "Program Proofs" — K. Rustan M. Leino (MIT Press, 2023)
- **Why**: Textbook by the creator of Dafny/Boogie. Covers Hoare logic, wp calculus, loop invariants, termination proofs, quantifier reasoning with full rigor and worked examples. The single most relevant book.
- **Read during**: weeks 1-4, while building VCGen.

### 3. "The Calculus of Computation" — Bradley & Manna
- **Why**: Covers propositional logic, first-order logic, program verification, and SMT encoding. Reference for when stuck on specific VC generation problems.
- **Key chapters**: 2 (propositional logic), 4 (FOL), 5 (program verification), 7 (SMT).

### 4. Z3 Guide
- **URL**: https://microsoft.github.io/z3guide/
- **Why**: Official tutorial for the Z3 C++ API. Covers sorts, solvers, tactics, model extraction.
- **Read when**: wiring up Z3 (weeks 3-5).

### 5. "Crafting Interpreters" — Bob Nystrom (free online)
- **URL**: https://craftinginterpreters.com/
- **Why**: Chapters 1-6 give you vocabulary for tokens, AST, visitors, tree-walking. Makes Clang's parser code readable.
- **Read**: skim chapters 1-6 in week 1.

### 6. Clang AST Tutorial (LLVM Dev Meeting 2019)
- **Search**: "The Clang AST - a Tutorial" on YouTube, ~45 min
- **Why**: Explains QualType, canonical types, type sugar, AST traversal. Watch before modifying Sema.

### 7. TAPL — "Types and Programming Languages" by Benjamin Pierce
- **Why**: Chapters 1-11 for operational semantics, type systems, inference rules. Reference for designing type-checking rules for forall, old(), result.
- **Read**: as needed, not cover-to-cover.

## Secondary References

### Dafny
- Source: https://github.com/dafny-lang/dafny
- Tutorial: https://dafny.org/latest/OnlineTutorial/guide
- Study: how Dafny lowers to Boogie IR, how it encodes quantifiers, how it handles termination.

### Verus
- Source: https://github.com/verus-lang/verus
- Relevant because our design is "Verus for C++". Study spec/proof function design, ghost code erasure.

### Frama-C / ACSL
- URL: https://frama-c.com/
- WP plugin manual: most similar existing tool (deductive verification + wp calculus + SMT)
- ACSL spec language: reference for annotation language design decisions
- Note: Frama-C targets C, not C++. Uses comment-based annotations. Custom parser.

### VCC (dead, but architecturally relevant)
- Was built at MSR for verifying concurrent C via Boogie/Z3.
- Papers describe memory model encoding for C — useful when adding pointer support.

### CBMC
- URL: https://www.cprover.org/cbmc/
- Paper: https://arxiv.org/abs/2302.02384
- Different paradigm (bounded model checking, not deductive). Useful reference for:
  - Bit-precise C semantics encoding
  - Automatic property generation (bounds checks, overflow, null deref)
  - Future BMC backend for our tool

### Boogie2 Paper — "Weakest-Precondition of Unstructured Programs" (Barnett, Leino, PASTE 2005)
- How to compute wp for goto-based control flow (relevant if you encounter unstructured CFGs)

## Clang/LLVM References

- Clang Internals Manual: https://clang.llvm.org/docs/InternalsManual.html
- LLVM Programmer's Manual: https://llvm.org/docs/ProgrammersManual.html
- Clang source: study `ParseStmt.cpp`, `ParseDecl.cpp`, `Stmt.h`, `Expr.h`, `TokenKinds.def`
- Eric Fiselier's Clang contracts fork (P2900): available on Compiler Explorer, reference for how contracts are parsed in practice

## Key Concepts Glossary

- **SSA (Static Single Assignment)**: every variable assigned exactly once. Enables direct mapping to Z3 constants. Branches use phi/conditional merge.
- **Havoc**: replace variable with fresh unconstrained symbol ("forget everything about it"). Used for loop desugaring and function call abstraction.
- **Assert**: generate a proof obligation (Z3 must prove this).
- **Assume**: add a hypothesis (Z3 gets to use this without proving it).
- **WP (Weakest Precondition)**: walk backward from postcondition through statements, substituting, to derive the weakest condition that guarantees the postcondition.
- **Verification Condition (VC)**: the logical formula produced by wp. If valid, the program is correct.
- **Modular Verification**: verify each function independently. Caller asserts pre, assumes post. Callee assumes pre, proves post.
- **Two-state context**: postconditions reference both pre-state (`old(x)`) and post-state (`x`, `result`).
- **Ghost code**: code that exists only for verification (spec/proof functions, ghost blocks). Zero runtime cost.
- **QualType**: Clang's type representation. Carries const/volatile qualifiers, signedness, bit-width. Your IR's VType is populated from QualType.
