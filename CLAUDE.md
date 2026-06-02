# CppVerify — Deductive Verification for C++ via Contracts + SMT

## What This Is

A **custom Clang frontend extension** that adds first-class contract syntax (pre/post/modifies/aliases/invariant/decreases/recommends/ghost/spec/proof/reveal_with_fuel) to C++, combined with a verification backend that generates verification conditions via weakest-precondition calculus and discharges them with Z3. Pointer reasoning uses a Z3-array-theory heap model with implicit non-aliasing defaults. Think "Verus for C++, built on Clang."

This is **not** a separate tool that parses comments or macros. We extend Clang's parser, AST, and Sema directly so contracts are type-checked by Clang and carry full `QualType` information.

## Why This Exists

No deductive verification tool exists for modern C++ that is:

- Built on Clang (all existing tools — Frama-C, VCC, VeriFast — roll custom C/C++ parsers)
- Natively supports C++ (Frama-C targets C99, VCC is dead, VeriFast doesn't do C++)
- Uses first-class contract syntax (not comments or macros)
- Provides a Verus-like proof language (spec functions, proof functions, ghost blocks)

We occupy an entirely uncontested niche. See @docs/COMPETITIVE.md for the full landscape.

## Architecture Overview

See @docs/ARCHITECTURE.md for full details. The high-level pipeline:

```
C++ source with contracts
    → Clang Frontend (modified Parser + Sema + AST)
    → VCR IR (Layer 1: typed, control flow preserved)
    → Passive IR (Layer 2: SSA, havoc/assume/assert, no control flow)
    → Z3 verification conditions
    → Diagnostics with source locations + counterexamples
```

Normal compilation path: CodeGen simply skips all ghost/contract AST nodes → zero runtime overhead.

## Project Structure

```
cpp-verify/                 # Git root (LLVM monorepo + CppVerify)
├── website/                # Published docs
├── docs/                   # DESIGN.md, ARCHITECTURE.md, REPO_LAYOUT.md
├── third_party/z3/         # Z3 submodule
├── setup.sh
├── clang/lib/Verify/       # verification engine
└── llvm/                   # CMake entry
```

Clone: `git clone --recurse-submodules`. See `docs/REPO_LAYOUT.md`. Remote `upstream` → llvm/llvm-project.

## Build

```bash
# First time — builds Clang, cpp-verify, and vendored Z3 (no system Z3 required)
./setup.sh

# Cross-target dev:
LLVM_TARGETS="X86;AArch64" ./setup.sh

# Incremental rebuild after modifying clang source
ninja -C build clang cpp-verify

# Run verifier
./build/bin/cpp-verify example.cpp
```

Z3 is vendored by default (`CPPVERIFY_VENDOR_Z3=ON`, `CPPVERIFY_PREFER_SYSTEM_Z3=OFF`).
Optional offline: `git submodule update --init third_party/z3`. System Z3: `-DCPPVERIFY_PREFER_SYSTEM_Z3=ON`.

## C++ Subset Supported (MVP)

Ring 1 (MVP target):

- Integer types: int, unsigned, int8_t..int64_t, uint8_t..uint64_t
- bool
- Simple structs (by value, no inheritance, no virtual)
- **Pointers and references — fully verified via Z3 array-theory heap model**
- **`unique_ptr<T>` — owned, no aliasing**
- Typedefs (resolved through Sema's full type computation)
- Control flow: if/else, while/for, return
- Function calls (modular; recursion via `decreases` + `reveal_with_fuel` for specs)
- Local variables; pointer/reference parameters
- **No**: heap allocation (new/delete), templates, exceptions, lambdas, virtual dispatch, multiple inheritance

Note: The frontend (parser + AST) correctly handles the full `result` return type for all declarator forms — pointers, structs, and typedefs — via `Sema::GetTypeForDeclarator`. The verifier backend supports pointers (via heap model) starting in Weeks 3-4.

See @docs/DESIGN.md for the contract syntax spec and @notes/locked-decisions.md for the rationale behind integer semantics, pointer/heap, and contract-vocabulary decisions.

## Key Design Decisions

1. **First-class syntax via Clang modification** — not comments, not macros. Contracts go through Clang's full type-checking pipeline. Enabled with `-fverify-contracts` flag.
2. **Two-layer IR** — Layer 1 (VCR) preserves control flow and types; Layer 2 (Passive) is SSA with havoc/assume/assert for mechanical wp transformation. The **heap is SSA-versioned** alongside locals.
3. **Two-tier integer semantics** — explicit `spec` functions use mathematical integers (Z3 `Int`, fast); lifted `constexpr` and all `proof`/`exec` code use machine integers (Z3 `BitVec`, runtime-honest). Users pick by choosing the function kind.
4. **Pointer reasoning via heap model + non-aliasing default + `modifies`** — Z3 array theory backs all dereferences; the verifier implicitly assumes distinct mutable pointer parameters don't alias (opt-out: `aliases(p, q)`); `modifies(...)` declares which lvalues a function may write. See `notes/locked-decisions.md` Decision 2.
5. **Ghost code stripped in CodeGen** — spec functions, proof functions, ghost blocks exist only in the AST. CodeGen skips them. Zero runtime cost.
6. **Modular verification** — functions verified independently using contracts as interfaces. Caller asserts precondition + implicit non-aliasing, assumes postcondition. Callee assumes precondition, proves postcondition.
7. **Lazy type_invariant injection** — `assume`/`assert` for type invariants is injected only at fields actually referenced (or assigned) within a function body, not eagerly at function boundaries. Keeps VCs tight.
8. **`reveal_with_fuel` for recursive specs** — bounded Z3 unfolding to prevent matching loops. Default fuel 1.
9. **`recommends` for spec UX** — soft preconditions on spec functions; checked only on verification failure of the caller; reported as warnings.
10. **Future extensibility** — Layer 1 IR is the stable interface. New verification backends (BMC, symbolic execution) consume Layer 1 differently. New language features add AST nodes and Layer 1 IR types.

## Clang-Specific Patterns

When modifying Clang, follow these patterns:

- **New keywords**: Add to `clang/include/clang/Basic/TokenKinds.def` with a `KEYCONTRACT` flag, enabled only with `-fverify-contracts`
- **New AST nodes**: Inherit from `Expr` (for expressions) or `Stmt` (for statements). Implement in both `.h` (under `include/clang/AST/`) and `.cpp` (under `lib/AST/`). Every node needs a `StmtClass` enum entry.
- **Parser changes**: Clang uses recursive descent. Study `ParseWhileStatement` and `ParseFunctionDeclarator` as templates.
- **Sema changes**: All contract expressions must be contextually convertible to bool. Use `PerformContextuallyConvertToBool()`.
- **CodeGen**: Ghost nodes → emit nothing. Just add a case that returns early.
- **Source locations**: Carry `SourceLocation` through every AST node and IR node. This is how diagnostics map back to user code.

## Key Files to Study in Clang

Before modifying anything, read these:

- `clang/lib/Parse/ParseStmt.cpp` — how control flow is parsed
- `clang/lib/Parse/ParseDecl.cpp` — how function declarators work
- `clang/include/clang/AST/Stmt.h` — existing statement AST nodes
- `clang/include/clang/AST/Expr.h` — existing expression AST nodes
- `clang/include/clang/Basic/TokenKinds.def` — all keywords
- `clang/lib/Sema/SemaChecking.cpp` — semantic validation examples
- `clang/lib/CodeGen/CodeGenFunction.cpp` — how statements are emitted

## Conventions

- C++ code in the verifier follows LLVM coding style (no `using namespace`, `camelCase` for functions, `CamelCase` for types)
- Every new AST node must have source location tracking
- Every IR node must preserve the VType (type information from Sema)
- Test with small example `.cpp` files in `test/Verify/` directory
- When in doubt about Clang internals, grep the codebase — it's well-commented
