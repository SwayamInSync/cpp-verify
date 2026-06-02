# Roadmap

## 2-Month MVP Timeline

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
- [ ] Extend `FunctionContractInfo` to carry `modifies`, `aliases`, `recommends`
- [ ] Extend `ParseContractClauses` for the new clauses
- [ ] Implement `RevealWithFuelStmt` AST node + parser entry point
- [ ] Sema: `recommends` allowed only on `spec` functions; `aliases` arguments must be pointer/reference parameters of the enclosing function

**Layer 1 VCR IR — core:**
- [ ] Define `VType` with `VIntMode` tag (Math | Machine)
- [ ] Define `VExpr` nodes: Literal, Var, BinOp, UnaryOp, Cast, FieldAccess, ArrayIndex, **Load**, **AddrOf**, FnCall, Forall, Exists, Old, Result, Conditional
- [ ] Define `VStmt` nodes: VarDecl, Assign, **Store**, If, While, Assert, Assume, Return, GhostBlock, **RevealWithFuel**, Call
- [ ] Define `VFunction` with `params: [(name, VType, ParamMode)]`, `modifies`, `aliases`, `recommends`, `intMode`
- [ ] Implement `VType::fromQualType` — bit-width, signedness, struct fields, typedef peeling, **pointer types**
- [ ] Implement ASTConverter: Clang AST → Layer 1 VCR IR
- [ ] Preserve `ImplicitCastExpr` as explicit `Cast(inner, fromType, toType)` nodes
- [ ] Set `intMode = Math` for explicit `spec` function bodies; `Machine` elsewhere
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
- [ ] Two-pass mode: on failure, re-run with `recommends` checks → warnings

**Test targets:**
- [ ] Verify `int abs(int x) pre(true) post(result >= 0)` end-to-end
- [ ] Verify `void swap(int* a, int* b) pre(a != nullptr && b != nullptr) modifies(*a, *b) post(*a == old(*b) && *b == old(*a))` end-to-end
- [ ] Verify a function that incorrectly modifies an unlisted location → counterexample with framing failure

**Milestone**: `cpp-verify abs.cpp` and `cpp-verify swap.cpp` print "Verified" or provide counterexample.

### Weeks 4.5: Type Invariants with Lazy Injection

**Goal**: Reduce per-function annotation burden for custom types.

- [ ] Add `type_invariant` keyword to `TokenKinds.def`
- [ ] Add `TypeContractInfo` side table on `RecordDecl` in `ASTContext`
- [ ] Parse `type_invariant(expr)` inside record/class body in `ParseDecl.cpp`
- [ ] ASTConverter: track which fields the function body references; inject `assume(invariant)` only at the first use of an invariant-named field — **not eagerly at function entry**
- [ ] ASTConverter: inject `assert(invariant_holds_after_assignment)` after assignments to fields named in the invariant
- [ ] ASTConverter: inject `assert(invariant)` at return points constructing values of invariant-bearing types
- [ ] Test: `Coordinate` with `type_invariant(x >= 0 && y >= 0)` — verify functions need no pre() for structural validity, and that functions not touching x/y get zero injection

**Milestone**: Functions taking custom types require zero pre() annotations for structural validity properties; VC size scales with field use, not field count.

### Weeks 5-6: Loops + Spec Functions + Proof Functions + Modular Verification

**Goal**: Verify the safe_fib example from DESIGN.md.

- [ ] Implement while loop desugaring (havoc/assume/assert pattern); heap is havocked alongside modified locals
- [ ] Implement `decreases` termination checking
- [ ] Implement lexicographic `decreases(a, b, c)` — lex order on tuple
- [ ] Parse and represent `spec` functions (existing keyword)
- [ ] Implement spec function encoding: `(declare-fun)` + axiom; recursion depth gated by per-call-site fuel
- [ ] Implement `RevealWithFuel` semantics: locally raise the unfolding depth for a named spec function within the enclosing function's VC
- [ ] Parse and represent `proof` functions
- [ ] Implement modular verification protocol: function call → assert pre + implicit non-aliasing + type_invariants, havoc modifies + heap, assume post
- [ ] Implement struct support: field access in IR + flattened Z3 encoding (or Z3 datatypes)
- [ ] Implement `recommends` two-pass diagnostic mode
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
- [ ] Add `hide(fn)` / `reveal(fn)` ghost statements (post-MVP design becomes MVP if time permits)
- [ ] Write README with examples, build instructions, and design overview
- [ ] Optional: basic LSP integration (underline unverified contracts)

**Milestone**: Public-ready demo with clean examples and documentation.

## Post-MVP Roadmap (ever-living project)

### Ring 2: Memory Safety Extensions

- `unique_ptr` with stricter ownership tracking (move semantics in IR)
- `shared_ptr` reference-count tracking (post-MVP design)
- Array bounds checking (auto-generated VCs)
- Null-deref auto-checks for dereferences without explicit `p != nullptr` precondition
- Separation-logic mode as alternative heap encoding (heavyweight, opt-in)

### Ring 3: Container Models

- Abstract model for `std::vector` (length + Z3 array)
- Abstract model for `std::array`
- Iterator contracts
- `view()` convention applied to standard containers

### Ring 4: Advanced Quantifiers and Specs

- Unbounded quantifiers `forall(i: T, body)`
- Manual trigger annotations `trigger(...)`
- `choose` (Hilbert ε) for spec functions
- Quantifier-instantiation profiling exposed via verifier flags

### Ring 5: Advanced Backends

- BMC backend (loop unrolling, no invariants needed)
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
