# Roadmap

## Current product checkpoint

The end-to-end MVP gate is achieved and permanently exercises:

- recursive and iterative factorial for every signed-`int` input in `0..12`,
  with `13!` rejected at the first overflow;
- recursive and iterative Fibonacci through `F(46)`, with `F(47)` rejected;
- mathematical specs, proof lemmas, executable/spec termination, loop
  induction, exact machine conversions, framed pointer output, scalar pointer
  arithmetic, buffer indexing, bounded quantified heap loops, and
  `valid(p, n)` bounds checks;
- fail-closed unsupported lowering and encoding, including honest `unknown` for
  quantified obligations Z3 cannot decide.

Since the MVP, the verified subset has grown to bounded scalar `new`/`delete`
with allocation identity, lifetime, provenance, and initialization; scalar
lvalue references; promoted local objects and fixed arrays; modular slices and
same-array pointer difference; `return`, `break`, and `continue` in `while` and
`for` loops; spec functions that read the heap; and whole-extent separation of
`valid(p, n)` buffers. Machine integers reach the solver through an exact
`--int-encoding` (integers by default, bit-vectors for bit-level queries), and
every obligation carries a precise kind in its public ID.

Every construct is written qualified (`cppverify::pre`, or `cv::pre` through a
namespace alias), and `-fverify-contracts` includes `<cppverify.h>` implicitly.
No word is reserved, so every standard header compiles. clangd, libclang, the
index, the AST printer, and clang-format understand the constructs, and
`cpp-verify --version` reports the release, the LLVM release it is built on,
and the backend versions.

Current boundaries are listed in the
[limitations reference](https://swayaminsync.github.io/cpp-verify/language/limitations.html).
The next frontiers are floating-point semantics, member functions and
templates, `break`/`continue` in `do` loops, and general arrays and provenance
across ownership-taking interfaces.

## Historical 2-Month MVP Timeline

The original plan, kept for history. Its checkboxes were not maintained; the
checkpoint above and the list below track current status. The planned `--bv`
flag was superseded by `--int-encoding`. The plan predates the qualified
syntax: its constructs are keywords (`KEYCONTRACT` in `TokenKinds.def`), which
became `cppverify::`-qualified names in October 2026 (DESIGN, "Construct
recognition").

### Weeks 1-2: Clang Frontend + Hello World — **COMPLETE**

**Goal**: Parse contract syntax, build annotated AST, verify round-trip.

- [x] Clone llvm-project (tag llvmorg-22.1.3)
- [x] Build Clang with Ninja (Release)
- [x] Add KEYCONTRACT keywords to TokenKinds.def
- [x] Add `-fverify-contracts` flag to enable them
- [x] Implement ParseContractClauses() — pre/post after function declarator
- [x] Implement ParseLoopContracts() — invariant/decreases on while/for
- [x] Implement ParseGhostBlock() — ghost { }
- [x] Implement ParseContractAssert() — contract_assert()
- [x] Side-table `FunctionContractInfo` (pre/post/decreases/isSpec/isProof)
- [x] Side-table `LoopContractInfo` (invariants/decreases)
- [x] AST nodes: ForallExpr, ExistsExpr, OldExpr, ResultExpr, ContractAssertStmt, GhostBlockStmt
- [x] Basic Sema: contract exprs convert to bool; result/old context checks
- [x] CodeGen: skip ghost/contract nodes; spec/proof functions skipped at module level
- [x] Test: 20 test files in `clang/test/Verify/`

**Milestone**: `clang++ -fverify-contracts -ast-dump example.cpp` shows contract nodes in AST; `clang++ example.cpp` (without flag) compiles normally ignoring them. **Achieved.**

### Weeks 3-4: VCR IR + WP for Straight-Line Code + Pointers + Heap Model

**Goal**: Verify first integer and first pointer function end-to-end.

**New keywords landed in this phase:**
- [ ] Add `modifies`, `aliases`, `recommends`, `reveal_with_fuel` to `TokenKinds.def` under KEYCONTRACT
- [ ] Extend `FunctionContractInfo` to carry `cppverify::modifies`, `cppverify::aliases`, `cppverify::recommends`
- [ ] Extend `ParseContractClauses` for the new clauses
- [ ] Implement `RevealWithFuelStmt` AST node + parser entry point
- [ ] Sema: `cppverify::recommends` allowed only on `cppverify::spec` functions; `cppverify::aliases` arguments must be pointer/reference parameters of the enclosing function

**Layer 1 VCR IR — core:**
- [ ] Define `VType` with `VIntMode` tag (Math | Machine)
- [ ] Define `VExpr` nodes: Literal, Var, BinOp, UnaryOp, Cast, FieldAccess, ArrayIndex, **Load**, **AddrOf**, FnCall, Forall, Exists, Old, Result, Conditional
- [ ] Define `VStmt` nodes: VarDecl, Assign, **Store**, If, While, Assert, Assume, Return, GhostBlock, **RevealWithFuel**, Call
- [ ] Define `VFunction` with `params: [(name, VType, ParamMode)]`, `cppverify::modifies`, `cppverify::aliases`, `cppverify::recommends`, `intMode`
- [ ] Implement `VType::fromQualType` — bit-width, signedness, struct fields, typedef peeling, **pointer types**
- [ ] Implement ASTConverter: Clang AST → Layer 1 VCR IR
- [ ] Preserve `ImplicitCastExpr` as explicit `Cast(inner, fromType, toType)` nodes
- [ ] Set `intMode = Math` for explicit `cppverify::spec` function bodies; `Machine` elsewhere
- [ ] `constexpr` → automatic spec elevation: in ASTConverter, `isSpecSafe(FD)` returns true if `FD->isConstexpr()`. Lifted `constexpr` retains `Machine` int mode
- [ ] Compile-time partial evaluation: for `constexpr` calls with concrete arguments, call `Expr::EvaluateAsInt()` / `Expr::EvaluateAsBooleanCondition()` and replace with `VLiteral` if it evaluates

**Layer 2 Passivize:**
- [ ] Implement SSA renaming for locals
- [ ] Implement heap SSA — `mem_0`, `mem_1`, ... versions across `Store` operations
- [ ] If/else branch merging via Conditional nodes
- [ ] Function-call abstraction: assert pre + implicit non-aliasing pre, havoc modifies, assume post

**WP Calculus:**
- [ ] Implement wp for: assignment, store, sequential composition, if/else, assert, assume, havoc

**Z3 Encoding:**
- [ ] `VType` → Z3 sort. `Int*(Math)` → `Int`; `Int*(Machine)` → `BitVec(N)`; `Ptr(T)` → `Int` with heap `Array(Int, T_enc)`
- [ ] `VExpr` → Z3 expr (with cast handling, load/store via array theory)
- [ ] Wire up Z3 solver: `add(!VC)`, `check()`, extract model on SAT
- [ ] Implement `ForallExpr` / `ExistsExpr` encoding with implicit `[lo, hi)` triggers
- [ ] Implement `OldExpr` / `ResultExpr` encoding via entry-state SSA versions

**Verifier driver:**
- [ ] Create `clang/lib/Verify/` with subdirectories: IR/, Frontend/, Transform/, Backend/, Driver/
- [ ] Create `clang/tools/cpp-verify/` binary
- [ ] Wire driver: parse → ASTConverter → Passivize → WP → Z3 → diagnostics
- [ ] Basic diagnostics: print "verified" or "counterexample: x = ..." with source locations
- [ ] Two-pass mode: on failure, re-run with `cppverify::recommends` checks → warnings

**Test targets:**
- [ ] Verify `int abs(int x) cppverify::pre(x >= -2147483647) cppverify::post(cppverify::result >= 0)` end-to-end
- [ ] Verify `void swap(int* a, int* b) cppverify::pre(a != nullptr && b != nullptr) cppverify::modifies(*a, *b) cppverify::post(*a == cppverify::old(*b) && *b == cppverify::old(*a))` end-to-end
- [ ] Verify a function that incorrectly modifies an unlisted location → counterexample with framing failure

**Milestone**: `cpp-verify abs.cpp` and `cpp-verify swap.cpp` print "Verified" or provide counterexample.

### Weeks 4.5: Type Invariants with Lazy Injection

**Goal**: Reduce per-function annotation burden for custom types.

- [ ] Add `type_invariant` keyword to `TokenKinds.def`
- [ ] Add `TypeContractInfo` side table on `RecordDecl` in `ASTContext`
- [ ] Parse `cppverify::type_invariant(expr)` inside record/class body in `ParseDecl.cpp`
- [ ] ASTConverter: track which fields the function body references; inject `assume(invariant)` only at the first use of an invariant-named field — **not eagerly at function entry**
- [ ] ASTConverter: inject `assert(invariant_holds_after_assignment)` after assignments to fields named in the invariant
- [ ] ASTConverter: inject `assert(invariant)` at return points constructing values of invariant-bearing types
- [ ] Test: `Coordinate` with `cppverify::type_invariant(x >= 0 && y >= 0)` — verify functions need no pre() for structural validity, and that functions not touching x/y get zero injection

**Milestone**: Functions taking custom types require zero pre() annotations for structural validity properties; VC size scales with field use, not field count.

### Weeks 5-6: Loops + Spec Functions + Proof Functions + Modular Verification

**Goal**: Verify the safe_fib example from DESIGN.md.

- [ ] Implement while loop desugaring (havoc/assume/assert pattern); heap is havocked alongside modified locals
- [ ] Implement `cppverify::decreases` termination checking
- [ ] Implement lexicographic `cppverify::decreases(a, b, c)` — lex order on tuple
- [ ] Parse and represent `spec` functions (existing keyword)
- [ ] Implement spec function encoding: `(declare-fun)` + axiom; recursion depth gated by per-call-site fuel
- [ ] Implement `RevealWithFuel` semantics: locally raise the unfolding depth for a named spec function within the enclosing function's VC
- [ ] Parse and represent `cppverify::proof` functions
- [ ] Implement modular verification protocol: function call → assert pre + implicit non-aliasing + type_invariants, havoc modifies + heap, assume post
- [ ] Implement struct support: field access in IR + flattened Z3 encoding (or Z3 datatypes)
- [ ] Implement `cppverify::recommends` two-pass diagnostic mode
- [ ] Test: verify `safe_fib` from DESIGN.md with spec fibo, proof lemma, ghost blocks, reveal_with_fuel

**Milestone**: `safe_fib` example from DESIGN.md verifies end-to-end.

### Weeks 7-8: Polish + Demo Suite

**Goal**: Presentable MVP.

- [ ] Clang-style diagnostic output with source locations and counterexamples
- [ ] Colored output (error/warning/note)
- [ ] Heap-aware counterexamples (show aliasing failures, framing failures)
- [ ] Build demo suite (10-15 example programs covering all features)
- [ ] Edge cases: empty functions, multiple returns, nested ifs, mixed pointer/struct
- [ ] Add `--bv` flag to globally force BitVec mode for all integers (Cast nodes already designed for this)
- [ ] Add `cppverify::hide(fn)` / `cppverify::reveal(fn)` ghost statements (post-MVP design becomes MVP if time permits)
- [ ] Write README with examples, build instructions, and design overview
- [ ] Optional: basic LSP integration (underline unverified contracts)

**Milestone**: Public-ready demo with clean examples and documentation.

## Post-MVP Roadmap (ever-living project)

### Ring 2: Memory Safety Extensions

- [x] Bounded direct local scalar `new`/`delete` with allocation identity,
  liveness, initialization, alignment, disjointness, and reuse
- [x] First-class local scalar provenance through matching-typed copies,
  reassignment, conditional selection, null, branch merges, and restricted
  verified scalar callees
- [x] Checked provenance through acyclic direct-pointer forwarding,
  scalar-value nested/spec helpers, and direct/conditional/null pointer results
- [x] Body-derived fresh-owned scalar results through direct/local aliases and
  acyclic nested factory calls, with nullable transfer and caller deletion
- General provenance through ownership-taking parameters, recursive calls,
  type-erasing/indirect copies, external summaries, and aggregate interfaces
- [x] General same-array pointer difference for compositional positions under
  declared extents, plus complete-object dynamic positions
- [x] Fixed local arrays and scalar element/subobject lifetimes
- General arrays, returned/stored pointer positions, and non-trivial destruction
- `unique_ptr` with stricter ownership tracking (move semantics in IR)
- `shared_ptr` reference-count tracking (post-MVP design)
- [x] Array bounds checking (auto-generated VCs from `valid(p, n)` extents)
- [x] Null-deref auto-checks for dereferences without explicit `p != nullptr` precondition
- [x] Whole-extent separation of `valid(p, n)` buffers
- Separation-logic mode as alternative heap encoding (heavyweight, opt-in)

### Ring 3: Container Models

- Abstract model for `std::vector` (length + Z3 array)
- Abstract model for `std::array`
- Iterator contracts
- `view()` convention applied to standard containers

### Ring 4: Advanced Quantifiers and Specs

- Unbounded quantifiers `cppverify::forall(i: T, body)`
- Manual trigger annotations `cppverify::trigger(...)`
- `cppverify::choose` (Hilbert ε) for spec functions
- [x] Heap-reading spec functions
- `cppverify::reads` frames for heap-reading specs
- Floating-point semantics (IEEE 754 through SMT floating-point theories)
- Quantifier-instantiation profiling exposed via verifier flags

### Ring 5: Advanced Backends

- [x] BMC backend (loop unrolling, no invariants needed)
- [x] cvc5, strict Z3+cvc5 portfolio, and Lean export/certification backends
- [x] Exact machine-integer encodings (`--int-encoding`)
- Symbolic execution backend for test generation
- Compositional verification across translation units

### Ring 6: Concurrency

- `std::atomic` with memory ordering annotations
- Happens-before relation encoding
- Data race detection via contracts

### Ring 7: Ecosystem

- Clang-tidy integration
- IDE plugin (VSCode) with inline diagnostics
- CI/CD integration mode
- Contract documentation generation
