# Architecture

## Pipeline Overview

```
C++ source with contracts
        │
        ▼
┌──────────────────────────┐
│  Stage 1: Clang Frontend │
│  (Modified Parser + Sema)│
│  - Parses contract syntax│
│  - Type-checks contracts │
│  - Builds annotated AST  │
└──────────┬───────────────┘
           │ Clang AST with contract nodes
           ▼
┌──────────────────────────┐
│  Stage 2: AST → VCR IR   │
│  (ASTConverter)          │
│  - Maps Clang AST subset │
│    to Layer 1 VCR IR     │
│  - Preserves types       │
│  - Preserves contracts   │
│  - Preserves ghost code  │
│  - Emits load/store for  │
│    pointer dereferences  │
└──────────┬───────────────┘
           │ VCR IR (Layer 1)
           ▼
┌──────────────────────────┐
│  Stage 3: Passivize      │
│  (Layer 1 → Layer 2)     │
│  - SSA renaming          │
│  - Loop desugaring via   │
│    havoc/assume/assert   │
│  - Branch merging via    │
│    conditional exprs     │
│  - Heap SSA: mem_0,      │
│    mem_1, ... versions   │
└──────────┬───────────────┘
           │ Passive IR (Layer 2)
           ▼
┌──────────────────────────┐
│ Stage 4: Obligation IR   │
│ - One checked WP fold    │
│ - Explicit logic sorts   │
│ - Stable IDs + ranges    │
│ - Diagnostic trace data  │
│ - Whole + ordered queries│
└──────────┬───────────────┘
           │ ObligationModule (Layer 3)
           ▼
┌──────────────────────────┐
│ Stage 5: Backend adapter │
│ - Validate capabilities  │
│ - Z3: encode + solve     │
│ - BMC: VCR unroll, then  │
│   the same obligation/Z3 │
│ - Lean: export / certify │
└──────────┬───────────────┘
           │ verified / failed / unresolved / bounded-safe / exported / certified
           ▼
┌──────────────────────────┐
│  Stage 6: Diagnostics    │
│  - Source names + types  │
│  - Guarded event traces  │
│  - Stable reason codes   │
│  - Text or JSON Lines    │
│  - Re-check recommends   │
│    on failure → warnings │
└──────────────────────────┘
```

## Parallel Path: Normal Compilation

The same modified Clang can also compile the program normally. CodeGen simply skips:
- All `GhostBlockStmt` nodes
- All `ContractAssertStmt` nodes
- All `RevealWithFuelStmt` nodes
- All `spec_fn` / `proof_fn` function declarations (gated in CodeGenModule)
- All contract clauses (pre/post/modifies/aliases/invariant/decreases/recommends/type_invariant)

Result: standard binary with zero overhead from contracts.

## Layer 1: VCR IR (Verified C Representation)

Purpose: clean, typed, control-flow-preserving representation of the verified program. 1:1 with a subset of the Clang AST but stripped of C++-specific noise (declaration contexts, template sugar). **Implicit type conversions are preserved as explicit Cast nodes** — not stripped — so the Z3 encoder can decide whether to emit `sign_extend`/`zero_extend` (BitVec mode) or silently ignore them (mathematical integer mode).

### Type Propagation from Clang

Every `VExpr` carries a `VType` populated automatically from canonical Clang
`QualType` data during `ASTConverter`; users never re-annotate contract terms.
`VType::fromQualType` recognizes booleans, void, pointers/references, integral
and enum widths/signedness, and a record marker. Record fields are flattened by
the converter where supported. Arrays do **not** have a first-class `VType`
today and fail closed outside the supported pointer/index lowering.

### Types (VType)

```
VIntMode = Math | Machine

VType =
  | Bool
  | Int32(IntMode, bitWidth, isSigned)
  | Int64(IntMode, bitWidth, isSigned)
  | Struct
  | Ptr(pointeeSizeBytes)                    // raw pointer / reference
  | Seq | Set | Multiset | Map                 // <cppverify.h> collections
  | Void
  | Unsupported
```

- `Int32` and `Int64` are current storage-class names, not a restriction to two
  exact widths. `bitWidth` carries the target width, including 8/16/128-bit
  integers; `isSigned` selects signed operations.
- Every `VExpr` carries a `VType`. Populated from Clang's `QualType` during ASTConverter.
- The `IntMode` tag on integer types is set by ASTConverter:
  - In `spec` function bodies → `Math` (Z3 `Int`)
  - In `proof`/`exec`/lifted-`constexpr` function bodies → `Machine` (Z3 `BitVec`)
- `Ptr(pointeeSizeBytes)` retains Clang's target `sizeof(T)`. Typed pointer
  arithmetic scales element offsets by this stride before entering the
  mathematical-address heap; record fields add Clang's target byte offset.
- A `cppverify::seq`, `set`, `multiset`, or `map` is one value of its
  collection type, never a flattened record; its elements are mathematical
  integers.

### Expressions (VExpr)

```
VExpr =
  | Literal(value, type)
  | Var(name, type, allocationIdentity?)
  | BinOp(op, lhs: VExpr, rhs: VExpr, type)
  | UnaryOp(op, operand: VExpr, type)
  | ValidPtr(ptr, allocationHeap?, livenessHeap?)
  | InitializedPtr(ptr, initializationHeap?)
  | Cast(inner: VExpr, fromType: VType, toType: VType)
  | FieldAccess(base: VExpr, field: string, type)
  | Load(ptr: VExpr, type)                       // *p in an expression context
  | HeapStore(before, after, ptr, value)          // passive heap relation
  | HeapFrame(before, after, [(lo, hi)])          // passive frame relation
  | SpecCall(identity, args: [VExpr], type)
  | OverflowCheck(op, lhs, rhs?)
  | Forall(binder: VarDecl, lo: VExpr?, hi: VExpr?, body: VExpr)
  | Exists(binder: VarDecl, lo: VExpr?, hi: VExpr?, body: VExpr)
  | Old(inner: VExpr)
  | Result(type)
  | Conditional(cond: VExpr, then: VExpr, else: VExpr, type)
```

All carry `SourceLocation` for diagnostics.

**Cast node rationale:** Clang inserts `ImplicitCastExpr` aggressively for integral promotions, sign conversions, and widening. Stripping these is safe only in mathematical integer mode (`z3::Int`). In BitVec mode, `(int64_t)x + y` and `x + y` differ when `x` is `int32_t`. By preserving casts as explicit `Cast(inner, fromType, toType)` nodes, the Z3 encoder makes the mode decision once — emit `sign_extend`/`zero_extend` or no-op — without requiring a second pass over the IR.

**Load node:** Reads through a pointer in expression contexts. `*p` →
`Load(p, T)` where `T` is the pointee type. The Z3 encoder maps this to
`(select mem p)`. For `p[i]`, the selected address is
`p + mathematical_value(i) * pointeeSizeBytes`.

**Quantifiers, triggers, choices, collections:** a quantifier without bounds
ranges over all mathematical integers. A `trigger(term)` mark is an identity
`Cast` flagged `IsTrigger` around the term. Each `choose` is lifted to a
synthesized uninterpreted spec function (`IsChoice`) of the values its body
mentions, whose postcondition is the Hilbert axiom `!exists(k, P) || P(result)`
(with the range for a bounded choose). A collection operation is a `SpecCall`
whose identity is `__cppverify.<op>`, such as `__cppverify.seq.push`.
`cppverify::valid(p, n)` becomes a call of the synthesized builtin spec
`__cppverify_valid(p, n)` (body `true`, marked `IsBuiltin` and never
reported), so the extent marker scan treats it exactly like a user-declared
`valid`.

**Mathematical values in ghost and proof code:** a spec result or a
collection length, element, or count keeps its mathematical type wherever
it is used, as in contracts; arithmetic with it is exact
(`evaluatedIntMode`). The frontend converts it, with a `Cast` that
passivization guards by an `overflow` obligation, only where it is stored in
a machine-typed object: an initializer, an assignment, a record field, a
call argument for a machine parameter, or a return value.

**HeapFrame:** produced by passivization only: `after` equals `before` at
every address outside the half-open regions.

### Statements (VStmt)

```
VStmt =
  | VarDecl(name, type, init: VExpr?)
  | Assign(target, value: VExpr)                          // local variable
  | Store(ptr: VExpr, value: VExpr)                       // *p = value
  | Allocate(target, allocatedType, init?, sizeBytes, alignBytes)
  | Free(ptr: VExpr)
  | If(cond: VExpr, then: [VStmt], else: [VStmt])
  | While(cond: VExpr, invariants: [VExpr], decreases: VExpr?, modifies: [VFootprint], body: [VStmt])
  | Assert(expr: VExpr)
  | Assume(expr: VExpr)
  | Return(value: VExpr?)
  | GhostBlock(body: [VStmt])
  | RevealWithFuel(fn: VFunction*, fuel: int)
  | Call(name, args: [VExpr], result_var: string?)
```

- `Store(ptr, value)`: writes through a pointer. Layer 2 turns this into a heap-array update.
- `Allocate`: starts a bounded scalar object's lifetime and updates the
  allocation, liveness, initialization, size, alignment, and value heaps.
- `Free`: proves that its operand is null or the live allocation base, then
  ends that lifetime in a fresh liveness-heap version.
- `RevealWithFuel`: locally raises Z3 unfolding depth for the named recursive spec function within the enclosing function's VC.

### Functions (VFunction)

```
VFunction =
  name: string
  identity: string
  params: [(name, VType)]
  returnType: VType
  preconditions: [VExpr]
  postconditions: [VExpr]
  modifies: [VFootprint]               // explicit frame, or inferred conservative default
  aliases: [(VarName, VarName)]        // opted-in aliasing pairs
  recommends: [VExpr]                  // spec functions only
  body: [VStmt]
  isSpec: bool
  isProof: bool
  usesDynamicStorage: bool
  freshOwnedReturn: (allocatedType, size, alignment, nullable)? // inferred
  decreases: [VExpr]                   // tuple → lex-ordered
  intMode: VIntMode                    // Math for explicit spec; Machine otherwise
  isTrusted: bool                      // [[cppverify::trusted]] on any declaration
  isExternalContract: bool             // no definition, or trusted: body not verified
  constAddressParams: {name}           // pointers/references to const
  behaviors: [(name, assumes)]         // for the vacuity check
  inductiveLoc, unfolding: VExpr?      // inductive: the least fixpoint of unfolding
  inductiveStepOf: string              // the generated step-indexed definition of it
  inductiveRuleOf: string              // a generated proof of that predicate's rules
  factsWithheld: {identity}            // specs whose facts this proof may not assume
  totalExpressions: bool               // no definedness obligations, as in specs
  clauseProofs: [(post|decreases|reads, [VStmt])]  // a spec's proof blocks
```

- Parameter ownership/borrowing is not yet represented by a `ParamMode` field.
  Pointer/reference behavior, mutability, alias opt-outs, and provenance are
  carried by the lowered expressions, contracts, and companion metadata.
- `freshOwnedReturn` is a derived VCR effect, never a trusted contract claim.
  `Ownership.cpp` computes it by a conservative acyclic path analysis and
  cloning, loop unrolling, dumps, and every backend preserve it.
- `identity` includes the canonical signature, so overloads with the same
  source spelling remain distinct through modular calls and SMT symbols.
- `aliases` empty means the implicit non-aliasing precondition applies to all mutable pointer/reference parameter pairs.
- A `VFootprint` is a target lvalue with an optional element count and
  element size: a cell (`p[i]`, `p->f`, a reference), a range `p[lo : n]`
  (target `p[lo]`, count `n`), or a region `*p` (the object `p` addresses).
- Behaviors are desugared in the frontend: each scoped `pre` becomes
  `!assumes || pre`, each scoped `post` `!old(assumes) || post`, and
  `complete_behaviors`/`disjoint_behaviors` become assertions at body entry.
- `contract_assert(c) by { proof }` is desugared to
  `Assign(k, false); Havoc(k); if (k) { proof; assert c; assume false }
  assume c`; `calc` to nested assert-by steps. When `c` is
  `forall(x, lo, hi, P)`, the parser puts `x` in scope for the block, and the
  branch starts with `Havoc(x')` and `Assume(lo <= x' && x' < hi)` for a
  fresh mathematical `x'`, the block reads `x` as `x'` (assigning it is an
  error), and it asserts `P[x := x']` instead of `c`.

## Layer 2: Passive IR

Purpose: eliminate control flow so wp calculus can operate mechanically. All variables assigned exactly once (SSA). Loops replaced by havoc/assume/assert. The value heap and every allocation-metadata heap are also SSA-versioned.

### Key Transformations

**Sequential statements → SSA renaming:**
```
x = 5;          →    x_0 = 5;
x = x + 1;      →    x_1 = x_0 + 1;
```

**Pointer store → heap SSA:**
```
*p = v;         →    mem_1 = store(mem_0, p_0, v_0);
y = *p;         →    y_0 = select(mem_1, p_0);
```

**Scalar allocation/lifetime → metadata-heap SSA:**
```
int *p = new int(v);

→ assume(p != 0 && p % alignof(int) == 0);
  assume(each target byte at p has no live owner);
  alloc_1     = store each target byte's owner with fresh_identity;
  base_1      = store(base_0, fresh_identity, p);
  size_1      = store(size_0, fresh_identity, sizeof(int));
  align_1     = store(align_0, fresh_identity, alignof(int));
  live_1      = store(live_0, fresh_identity, true);
  init_1      = store(init_0, p, true);
  mem_1       = store(mem_0, p, v);

delete p;

→ assert(p is null or
         (alloc_k[p] == p.identity &&
          base_k[p.identity] == p &&
          live_k[p.identity]));
  live_{k+1}  = store(live_k, alloc_k[p], false);
```

The direct local scalar subset is bounded to objects of at most 256 target
bytes, so byte ownership is expanded finitely. Default-initialized storage
starts with `init[p] == false`; a supported store changes it to `true`. Loads
assert non-nullness, current liveness, and initialization before selecting the
value heap. The allocation result and direct matching-typed local aliases retain
the same static identity, so deletion invalidates every alias and reusing the
same numeric address for a later lifetime cannot revive a dangling pointer.

**Fresh-owned modular return → caller materialization:**

```
int *p = make(v);  // make has inferred freshOwnedReturn(int, 4, 4)

→ fresh p.identity;
  assume(p.identity != 0 && !issued[p.identity] && !live[p.identity]);
  assume(p is null only when the inferred effect is nullable);
  assume(p is aligned and disjoint from every live object/declared extent);
  issued_1 = store(issued_0, p.identity, true);
  alloc_1  = store each non-null result byte's owner with p.identity;
  base_1   = store(base_0, p.identity, p);
  size_1   = store(size_0, p.identity, sizeof(int));
  align_1  = store(align_0, p.identity, alignof(int));
  live_1   = store(live_0, p.identity, p != null);
  init_1   = store(init_0, p, p == null ? init_0[p] : true);
  mem_1    = store(mem_0, p, p == null ? mem_0[p] : fresh_value);
  assume(make's postconditions);
```

The inference accepts only body-present executable functions with no pointer
parameters or explicit frame whose every path returns null or one exact live,
fully initialized fresh scalar base. Extra allocations, deallocation,
secondary calls/escapes, pointer arithmetic, external bodies, and recursive
cycles prevent the effect. Already inferred factories may be forwarded,
yielding a fixed-point over acyclic calls. Guarded heap updates explicitly
equal their predecessor on inactive paths, so an early-return factory keeps
the heap state at that return rather than introducing unconstrained arrays.

Ownership discovery deliberately runs before call-result provenance is
attached. A neutral AST-to-VCR conversion computes the body-derived fixed
point; a second conversion receives only those confirmed callable identities
and may then attach owned-result provenance at their call sites. The production
VCR is analyzed again and carries the inferred effect into every transform and
backend. This prevents syntax, arbitrary pointer-return contracts, and external
declarations from manufacturing ownership during lowering.

**If/else → guarded SSA with conditional merge** (heap follows the same pattern):
```
if (c) { x = a; } else { x = b; }
y = x + 1;

→

x_1 = a_0;
x_2 = b_0;
x_3 = c_0 ? x_1 : x_2;
y_0 = x_3 + 1;
```

**While loop → havoc + assume invariant + one-iteration check:**
```
// while (cond) invariant(I) decreases(D) { body }

assert(I);                         // 1. invariant on entry
havoc(modified_vars + mem);        // 2. forget loop-modified state + heap
assume(frame(mem_entry, mem));     //    cells outside the loop's write set kept
assume(I);                         // 3. inductive hypothesis
if (cond) {                        // 4. if loop continues:
    [body in SSA]                  //    execute one iteration
    assert(I);                     //    invariant preserved
    assert(D_new < D_old);         //    termination measure decreases
    assert(frame(mem_entry, mem)); //    explicit loop modifies respected
    assume(false);                 //    cut path
} else {
    // continue with I ∧ ¬cond
}
```

**Loop frames.** In the object model the heap havoc is framed by the loop's
write set: its explicit `modifies` footprints, read in each iteration's state
(ACSL `loop assigns`), else the objects its stores and calls reach: the entry
objects of their pointers' origins (below). With a function `modifies` too,
both frames are assumed, so only cells inside both may change; when an
origin is unknown the function's frame alone bounds the loop, since every
store is checked against it. When every written region is a single cell the
frame is a chain of stores of fresh values; otherwise it is a
`HeapFrame(mem_entry, mem_head, regions)` relation.
An explicit loop `modifies` is also asserted at the end of each iteration and
at each `continue` (obligation kind `frame`, located at the footprint).

**Termination.** An executable loop without `decreases` contributes no
measure obligation, and the driver reports the function `Unresolved` with
`decreases.missing` unless BMC proved the unwinding. `decreases(*)` marks the
function as possibly divergent: its proof, and the proof of every caller, is
reported `[partial]`. Calls within an executable or proof recursion cycle
assert the decrease of the shared measure at the call site.

**Loop exits.** A `break` or `return` inside the body leaves from the
inductive iteration: its path guard is recorded and the path ends. After the
loop the continuation assumes `(¬choice ∧ ¬cond) ∨ break₁ ∨ … ∨ return₁ ∨ …`.
Because every later state version equals its predecessor on an ended path,
each variable changed by the body merges as `choice ? v_end : v_head`, which
is the exit state on break and return paths. Return paths then leave the active
guard, so the function-end postcondition check sees them in their return
state. A `continue` asserts the invariant and the measure decrease in its own
state and ends the path; the frontend emits a `for` increment before it. BMC
unrolling lowers `break` and `continue` to flag assignments that guard the
remaining statements and the next iteration.

**Assertions → assert, then assume:** `contract_assert(P)` is proved where it
stands and assumed from there on, so later obligations can use it as a proof
step. Other obligations stay independent of each other.

**Function calls → assert precondition, havoc modifies, assume postcondition:**
```
// y = foo(x)  where foo has pre(P) modifies(M) post(Q)

assert(P[params := args] ∧ /* implicit non-aliasing pre, if applicable */);
havoc(M);                              // forget the locations declared in modifies
havoc(y);
assume(Q[Result := y, Old(params) := args]);
```

- The heap version increments only across the modifies set: `mem_{k+1}(loc) = mem_k(loc)` for `loc ∉ modifies`.
  Cell footprints become stores of fresh values (no quantifier). In the
  object model, ranges and regions (the actual's `valid` extent, else one
  object) become `HeapFrame(mem_k, mem_{k+1}, regions)`; each footprint of
  the callee must lie inside the caller's own frame (index-based
  containment).
- If `modifies` is the conservative default (all reachable through mut params), the entire heap is havocked.
- A `freshOwnedReturn` call is not a whole-heap havoc. It preserves every old
  cell, materializes one disjoint initialized scalar object, then assumes the
  ordinary postconditions against that new heap.

## Layer 3: Canonical Obligation IR

`buildObligationModule` is the only passive-to-logic lowering path. It folds the
ordered `PassiveProgram` once and publishes:

- a typed `LogicExpr` tree with explicit `Bool`, mathematical integer,
  width-indexed bit-vector, pointer, heap-array, and collection (`seq`, `set`,
  `multiset`, `map`) sorts; integer sorts retain
  canonical signedness and originating C++ width for explicit mode conversion,
  without exposing VCR enums to adapters;
- one complete **counterexample query** (satisfiable iff some proof obligation
  can fail);
- the matching direct **correctness goal**, plus direct and negated forms for
  every individual source obligation;
- equivalent ordered queries using entry assumptions and only preceding
  `assume` statements;
- deterministic function-scoped obligation IDs, a precise `ObligationKind`
  (contract clauses such as `precondition` or `invariant-preserved`,
  definedness categories such as `overflow` or `bounds`, generated interface
  checks such as `aliasing` or `frame`, `unwinding`, and `unsupported`), and
  resolved file/line/column metadata. Passivization splits an expression's
  definedness into one check per category, each under its own short-circuit,
  conditional, quantifier, and `old` guards, so the conjunction is unchanged;
- owned logical-function declarations, typed signatures, compact one-step
  definitions, and exact finite definition levels for the caller's fuel;
- the logical features required by the module for capability validation.

Construction returns `llvm::Expected`. A null, unhandled, malformed, or
untyped term prevents publication of the module and is reported as `unknown`;
it is never replaced by `true`.

Every source-built or replayed module then passes through one fail-closed
canonicalization step before hashing or backend dispatch. The pass folds only
sort-preserving Boolean constants, double negation, constant conditionals, and
reflexive equality/inequality. It simplifies owned finite-fuel definitions and
removes logical declarations unreachable transitively from every ordered
obligation. It then rebuilds each exact counterexample negation, the complete
ordered goal/query, and required feature set before revalidation. Arithmetic,
quantifiers, pointer/heap terms, and assumptions are not rewritten. Layer 3
reports before/after node counts, rewrite count, and removed declarations for
source-built modules.

Terms added for the R3 language features:

- `HeapFrame(before, after, lo1, hi1, ...)`: `after[a] == before[a]` for
  every integer address `a` outside the half-open regions. It is
  deliberately unbounded: a quantifier over `[0, 2^64)` defeats Z3's
  model-based instantiation (a failing copy loop took 50 s instead of
  0.9 s), and it is sound because verified stores lie inside objects in
  `(0, 2^64)`. Adapters encode it as an unbounded universal quantifier; the
  certifier compares the piecewise-constant heaps exactly.
- A quantifier with one child (its body) ranges over all integers.
- `Patterns`: the trigger terms of a quantifier (memory reads, collection
  reads, recursive spec applications). They steer instantiation only and are
  neither serialized nor hashed.
- `Collection(op, operands)`: one of 25 operations (`seq.push`, `set.union`,
  `multiset.count`, `map.get`, ...), with the total semantics of
  `<cppverify.h>`. Collections of sequences require the `sequences` feature,
  the others `collections`. Sequence `update` and `reverse` are not
  operations: the frontend defines them as specs over the operations
  (`__cppverify_seq_update`, `__cppverify_seq_reverse`, marked `IsBuiltin`),
  so they reach every backend as ordinary logical functions, and the
  driver checks the termination and length postcondition of `reverse` like
  any recursive spec's, reporting only a failure.
- A logical function marked `Choice` is a lifted `choose`: uninterpreted,
  with the Hilbert axiom as its postcondition. The certifier reads its
  value from the model, so a claim true only for some choices fails
  certified.
- A comparison between a machine and a mathematical operand is lifted to
  the integers when the mathematical side mentions a quantifier binder or a
  collection, and otherwise split by range so the machine side keeps its
  sort.

`Obligation.h` is a VCR-free consumer boundary. VCR/passive lowering APIs live
in `ObligationLowering.h`; Z3, cvc5, Lean, serialization, dumps, and future adapters
depend only on canonical sorts, expressions, declarations, sources, features,
and obligation kinds.

### Canonical archives and semantic identity

`--obligation-out=FILE` writes one or more deterministic
`cppverify.obligation/2` records after source attribution. The binary format has
the `CPVOBL\r\n` magic, an explicit schema version, little-endian fixed-width
integers, length-delimited strings/collections, and stable hand-assigned wire
tags rather than C++ enum ordinals. The reader bounds strings, collections,
expression depth, and total nodes, then revalidates every sort, term, call
signature, logical declaration, feature bit, and identity. The driver refuses
to publish a record unless deserialize/validate/reserialize is byte-exact and
preserves semantic identity. `HeapFrame` has expression tag 38 and
`Collection` tag 39 (followed by its operation's tag, from a fixed table in
which tag 6, the former sequence update, is reserved); the collection sorts
`seq`, `set`, `multiset`, and `map` have sort tags 6 to 9. Trigger patterns
and the `Choice` marker of a logical function are not archived, so a
replayed module instantiates quantifiers by the solver's own patterns and
treats a choice as an ordinary uninterpreted function.

Schema v2 adds the precise obligation kinds and still reads schema v1, whose
records name only assertions, postconditions, and unwinding checks. Records
limit strings to 64 MiB, collections and expression
nodes/edges to 100,000 per record, expression nesting to 4096, canonical
integer numerals to 4096 decimal characters, and integer sorts to 4096 bits.
Parsing stops at the first malformed field before reserving nested storage.
Validation also rejects embedded NULs, inactive expression payloads,
ill-scoped or inconsistently typed variables, non-canonical numerals,
counterexample terms that are not exact goal negations, and complete goals
that are not the conjunction of their ordered obligations.

Every module and individual obligation has a SHA-256 semantic hash. Semantic
hashes omit source paths, display-only function names, internal positional
or public source-anchored obligation IDs, and every obligation kind except
`unwinding` (the only kind that changes result semantics), so moving identical
C++ source or
inserting an unrelated earlier obligation does not invalidate an individual
goal's proof identity. Per-obligation hashes include only the transitive
logical-function declarations reachable from that goal;
module hashes cover the complete module. Portable archives retain
file/line/column attribution for diagnostics and every expression node. The
semantic-hash format has its own version independent of the archive wire
version, preventing a wire-only format change from invalidating proof
identities. Canonical simplification established semantic-hash format v2,
identifier-independent hashes advanced the preimage to format v3, and
kind-independent hashes advance it to format v4.

`--obligation-in=FILE` validates and replays concatenated records without
parsing C++:

```bash
cpp-verify --obligation-in=goals.cpv --backend=z3
cpp-verify --obligation-in=goals.cpv --backend=portfolio
cpp-verify --obligation-in=goals.cpv --lower-only --dump-ir=3,4
cpp-verify --obligation-in=goals.cpv --backend=lean --lean-out=goals.lean
```

Replay treats decoded records as untrusted input: validation happens before
canonicalization, and the canonicalized module is revalidated before it can
reach any adapter. Semantically equivalent records that differ only by
supported constant structure or unreachable logical declarations therefore
converge to the same backend module and semantic identity.

BMC-produced modules retain the unroll bound as semantic transform provenance.
Replay aggregates those modules with BMC unwinding semantics even when Z3 is
the selected solver, so an exhausted frontier remains `BoundedSafe(N)` rather
than becoming an ordinary program failure or an unbounded proof. Applying BMC
to an untransformed archive is rejected because loop unrolling must precede
obligation construction. Lean scratch export of a bounded archive is also
rejected until bounded theorem provenance is represented in generated Lean.
Failure-triggered `recommends` diagnostics are excluded from archives, keeping
archive contents independent of solver outcomes.

Concatenated records may use different reveal fuel for the same logical
function. Fuel and finite unfoldings are module-local; shared identities must
have compatible parameter/result signatures. Z3 declaration caches are reset
per record, and Lean gives module-local bodies and colliding theorem names
distinct generated prefixes.

The weakest-precondition laws implemented by the builder are:

```
wp(assert(P), Q)           = P ∧ Q
wp(assume(P), Q)           = P → Q
```

SSA renaming, heap stores, havoc, calls, branches, and loops have already been
expressed as terms and ordered `assume`/`assert` statements in Layer 2. The old
parallel `WPCalc` dump implementation was removed: Layer 3 now prints the exact
canonical module that lower-only and the selected backend consume.

## Z3 Encoding

| Logic sort | Z3 sort |
|---|---|
| `Bool` | `Bool` |
| `MathematicalInteger` | `Int` |
| `BitVector(N)` | `BitVec(N)`, or `Int` in the integer encoding |
| `Pointer` | `Int` (mathematical target-byte address) |
| `Heap` | `Array(Int, Int)`; typed reads convert cells at the boundary |
| `Seq` | `Seq(Int)` |
| `Set` | `Array(Int, Bool)` |
| `Multiset` | `Array(Int, Int)`; a count is `max(0, cell)` |
| `Map` | `Array(Int, cppverify.option)`, the datatype `none \| some(value)` |

| VExpr | Z3 Expr |
|---|---|
| BinOp(+, a, b) | `a + b` (Int) or `bvadd a b` (BitVec) |
| BinOp(&&, a, b) | `(and a b)` |
| Cast(inner, Int32, Int64) | math mode: identity — BitVec mode: `(sign_ext 32 inner)` |
| Cast(inner, UInt32, UInt64) | math mode: identity — BitVec mode: `(zero_ext 32 inner)` |
| Load(p, T) | `(select mem_k p)` for the current heap version k |
| Forall(x, lo, hi, P) | `(forall ((x Int)) (=> (and (<= lo x) (< x hi)) P))` — bound is the implicit trigger |
| Forall(x, P) | `(forall ((x Int)) P)`; marked triggers become `:pattern`, and the quantifier id is `q@line:col` |
| HeapFrame(h, h', lo, hi, ...) | `(forall ((a Int)) (or (and (<= lo a) (< a hi)) ... (= (select h' a) (select h a))))` |
| `s[i]` | `(cppverify.seq_at s i)`, see below |
| `s.push(x)`, `s + t` | `seq.++`, `seq.unit`, with index facts, see below |
| `s.subrange(lo, hi)` | `(seq.extract s lo (- hi lo))`, or `(seq.extract s 0 hi)` when `lo < 0`, see below |
| `a.insert(x)`, `a.unite(b)`, `m.count(x)` | `store`, `set.union`, `(ite (>= c 0) c 0)` over the arrays |
| Old(x) | `x_entry` (SSA version at function entry) |
| Old(*p) | `(select mem_0 p_entry)` |
| Result | `result_var` (SSA version of return value) |

**Sequence reads.** `s[i]` is `cppverify.seq_at(s, i)`, a recursive-function
definition `(ite (and (<= 0 i) (< i (seq.len s))) (seq.nth s i) 0)`. The
definition is a recursive-function definition rather than a quantified axiom
so that models interpret it exactly: model-based instantiation cannot check a
quantifier over sequences, and every satisfiable query timed out with one.

**Index facts.** Z3's sequence theory decides lengths and word equations, but
not what an element of a built sequence is: its own `seq.nth` gives
quantifiers nothing to match. For each closed push, concatenation, and
subrange term of the query, the adapter asserts beside it the element meaning
of that term, quantified over the index only and triggered by a read of the
term: `forall k. seq_at(s.push(x), k) == (k == len(s) ? x : seq_at(s, k))`,
`seq_at(a ++ b, k)` reads `a` below `len(a)` and `b` beyond, and a subrange
reads its source at the clamped offset. Each is a theorem of the sequence
theory, so no verdict can change. The quantifier ranges over an integer, which
model search can check, and its trigger names a term the program wrote, never
one Z3 creates while solving word equations. Lemmas quantified over sequences
(`forall a b k. seq_at(a ++ b, k) == ...`) fired on those internal terms:
every concatenation proof timed out with them and some counterexamples were
lost. On a corpus of 102 sequence functions, the index facts verify every
function the lemmas did and more (78 against 70), keep all 22 certified
counterexamples, and take 141 s instead of 801 s. A pattern cannot contain
`ite`, so a term with one (a subrange whose start may be negative, or a term
built around one) is named by a fresh constant defined as it.

**Encoding race.** The facts help proofs but slow model search: a false
claim about one element of a chain of 200 pushes took 139 s with them and
0.1 s without. With more than one job, every query over sequences (the
complete query, each obligation, and the complete-query retry) is therefore
also solved in the plain sequence theory (`Z3Encoder::setSequenceFacts`,
which omits the index, membership, and split facts and the extensionality
instances), on the same pool (`Z3VerifyBackend::solveQuery`). Both encodings
are exact, so the first proof or certified counterexample stands and
interrupts the other. With one job only the facts' encoding runs.

**Subranges.** `seq.extract` already clamps: from a start in `[0, len)` it
stops at the end, and it is empty from any other start or for a count below
one. `subrange(lo, hi)` is therefore exactly `extract(s, lo, hi - lo)` for
`lo >= 0` and `extract(s, 0, hi)` below, with no case split for a literal
`lo >= 0`. Every extract of a concatenation `a ++ b` also receives, as a
ground fact beside the query, the theorem that splits it: from a start
`i >= 0` it lies in `b` (`i >= len(a)`), in `a` (`i + n <= len(a)`), or is
`extract(a, i, len(a) - i) ++ extract(b, 0, n - (len(a) - i))`. Z3's word
equations rarely find that split themselves (dropping the last element of
`s + t` took 30 s and now takes 50 ms); a quantified form of the theorem
would leave satisfiable queries to model-based instantiation, which cannot
check it. The fact is stated once per extract term.

**Membership.** `s.contains(x)` is `seq.contains(s, unit(x))`, and each closed
membership term receives both directions of its meaning: it implies a read
of `x` at a fresh witness index in range, and a read of `x` at any index in
range implies it (triggered by the read).

**Typed loads.** In the integer encoding of a query over collections, a
typed load is `cppverify.cell_<sort>(select(mem, p))`, a recursive-function
definition of the exact reduction of a cell into the load's sort. A
collection element read from a cell is then equal to a load of that cell by
congruence once the indices are; with the reduction inline, the arithmetic
explored its `mod` under every quantifier instance (a ghost-sequence copy
invariant was `unknown` after 10 s and now takes 4 ms). Other queries keep
the reduction inline, because model search over heap frames is much slower
through the definition (a frame counterexample went from 8 ms to over 20 s).

**Instances at reads.** A quantifier over a buffer reads `p + S * k`; the
solver instantiates it at the reads of the query that match that pattern,
but its rewriter folds a read at a constant or compound index (`p[2]` is
`p + 2 * 4`, then `p + 8`; `p[i + 1]` is flattened), which no longer
matches. Before encoding, each Z3 and cvc5 adapter therefore joins every
quantifier with its instances at the closed reads of the query in the same
heap whose address is `Base + S * t` for the quantifier's own base and
stride (`instantiateAtReads`): `forall k. B` becomes `forall k. B && B(t)`,
and `exists k. B` becomes `exists k. B || B(t)`. Both are equivalences in
any polarity, so no verdict can change; the canonical module, its hashes,
and the certifier never see them. Instances are taken once (never from other
instances), at most 16 per quantifier and 50,000 added nodes per query.
Without them, `forall(k, 0, n, p[k] >= 0)` did not prove `p[2] >= 0` on Z3
or even `p[0] >= 0` on cvc5.

**Extensionality.** A sequence equality the query refutes (an `a == b` it
asserts the negation of, or an asserted `a != b`, with no bound variable)
is joined with its extensionality instance before Z3 encoding
(`instantiateExtensionality`): `a == b` becomes `a == b || (len(a) ==
len(b) && forall k in [0, len(a)). a[k] == b[k])`. The two are equivalent,
and the quantifier occurs negatively, so the solver introduces one witness
index rather than instantiating it. Z3 then proves an equality from equal
elements, as Verus's `=~=` and Dafny's sequence equality do, and a stated
`contract_assert(a == b)` works as a hint. Equalities the query assumes, such
as ghost assignments, are left alone. cvc5 decides extensionality itself and
does not receive the instances: in the sequence benchmark, given them
together with membership witnesses, it returned no model for any false
claim.

### Machine-integer encodings

A `BitVector(N)` logic sort fixes the C++ meaning of a machine value; each SMT
adapter chooses how the solver represents it (`--int-encoding`). Every choice is
exact, so a decided verdict or counterexample never depends on it.

| Encoding | Representation |
|---|---|
| `bitvector` | `BitVec(N)` with SMT-LIB bit-vector operators |
| `integer` | `Int` holding the canonical value in the sort's signed or unsigned range |
| `auto` (default) | `integer` for a query unless it needs the bits of a non-constant operand, then `bitvector` |

In the integer encoding each free machine variable has a range fact
(`-2^(N-1) <= x < 2^(N-1)` or `0 <= x < 2^N`) asserted beside the goal, and
every operation stays in range by construction:

- `+`, `-`, `*`, unary `-`, truncation, and mathematical-to-machine conversion
  reduce modulo `2^N` (`mod(x + 2^(N-1), 2^N) - 2^(N-1)` when signed). Z3
  receives each reduction as `ite(inRange(x), x, reduced)`, so that `mod`
  drops out of the arithmetic whenever it knows an operation does not wrap;
  cvc5 keeps the plain form, which it handles better;
- `/` and `%` truncate toward zero and follow the SMT-LIB zero-divisor extension
  of the bit-vector encoding (`bvsdiv x 0` is `-1` or `1`, `bvudiv x 0` is all
  ones, and both remainders are the dividend);
- same-width signedness changes and extensions are `ite` reinterpretations,
  `~x` is `-x - 1` (or `2^N - 1 - x`), `x & (2^k - 1)` is `mod(x, 2^k)`, and a
  constant shift multiplies or floor-divides by `2^k`;
- other bitwise operators and symbolic shifts need operand bits. Z3 names a
  ground operand by a fresh bit-vector `b` defined by `bv2int(b) == x`, guarded
  by the operand sort's range so that it can never make a query vacuous; an
  operand that mentions a quantifier binder, and every cvc5 operand, uses
  `int2bv`. A shift amount is read in its own sort;
- signed-overflow predicates compare the exact mathematical result with the
  signed range;
- heap cells hold the unsigned bit pattern, exactly as in the bit-vector
  encoding, and a typed load reduces the cell into the load's sort;
- an opaque machine-sorted spec application is reduced into its sort's range.

Mode conversions are stated in Layer 3, not by an adapter. Machine to
mathematical is exact. Mathematical to machine is reduced directly into the
destination sort, and the reduction is pushed through `+`, `-`, `*`, negation,
and `ite`, so a converted polynomial stays bit-vector arithmetic; passivization
guards every such conversion with an `overflow` obligation that the value fits.
Equality and ordering between a machine and a mathematical operand do not lift
the machine side: a mathematical value outside the machine range decides the
comparison, and one inside it is compared as a machine value. Operands that
mention a quantifier binder or a collection are lifted instead.

Range facts make Z3 assign every machine variable. Counterexample extraction
therefore reports a variable as undetermined (`<unknown>`) when the goal and
spec equations still evaluate to true with it, and every variable freed before
it, replaced by an unassigned symbol. Layer 4 dumps print the range facts and
bit-vector definitions before the goal.

**Spec functions → owned logical functions:** while VCR is still available,
`SpecAxioms` materializes every reachable typed declaration and finite
definition level into `ObligationModule`. A visible non-recursive definition
is exact and finite, so Z3 substitutes it at every application, under a
quantifier too, and cvc5 receives it as `define-fun`; a recursive one gets
equations only at concrete logical call sites. Recursive leaves remain
applications of the opaque logical function, and `reveal_with_fuel` controls
the exact finite depth. An application's arguments take the integer mode of
the callee's parameters (mathematical for an explicit spec), not that of its
result: with the result's mode, a `bool` spec's argument `a + 1` was reduced
to 32 bits, which proved `!above(a + 1)` for `a == 2147483647` and refuted
`above(a + 1)` with a false counterexample. Adapters never borrow `VFunction`
metadata.

**Heap-reading specs:** a spec that reads memory, directly or through another
spec, becomes a logical function with a leading `__spec_heap` parameter of sort
`Heap`; its definitions read through that parameter. Each call site passes the
heap version passivization resolves for it, exactly as for a load, and
modules containing such functions require the `heap-functions` logic feature.
A spec with `reads(p, n)` clauses is checked in its own module (`spec reads:`,
the spec and its recursion cycle opaque): every load address under its path
guard, and every range a heap-reading callee reads, lies in the declared
ranges. Since the spec then depends only on those cells (by induction on its
terminating definition), passivization adds, for each application `f(H', a)`
and each store `H' = store(H, q, v)` reached backwards through the heap
versions, the assumption `q outside R(a) -> f(H', a) == f(H, a)` under the
store's guard. The driver demotes a proof that relies on a spec whose reads
check did not pass to `Unresolved` with reason `spec.reads`.

**Spec postconditions and domains:** a spec's `post` is checked in its
termination module (its own module `spec post:` when it is not recursive):
each call within the recursion cycle contributes the assumption
`dec(a) < dec(x) -> post(a, f(a))` under the cycle's well-founded relation,
each call of another spec its post, and every return value must satisfy the
post. Since the facts at lower measures are the induction hypothesis, a
proof establishes termination and the post together. Passivization then
assumes `post(t, f(t))` at every application `f(t)` in a function, the
preconditions included, quantified like the application, and at every
application inside the definition levels the module gives the solver for
the applications it names (`specDefinitionLevels`, the same levels as
`SpecAxioms`, at the call's arguments and memory), as Dafny's function
postconditions hold at every application: `fibo(j - 1) <= fibo(j)` needs
`fibo(j - 2) >= 0`, which only the unfolding of `fibo(j)` names. Spec check
modules add the same facts for the applications their definitions expose
(`addPostApplicationFacts`). These are proved facts recorded in
`AssumedPosts`, so they cannot make a false claim verify; each puts its
application into the query, whose definition levels the solver then also
receives. `when(c)` is desugared in the frontend: the body
becomes `if (c) body else return f.unspecified(params)`, where
`f.unspecified` is a logical function without a definition (Z3 and cvc5
declare it; the certifier cannot evaluate it, so a counterexample that needs
its value is `counterexample.unchecked`), and each post becomes `!c || post`.

**Inductive predicates:** `inductive` on a spec returning `bool` sets
`VFunction::InductiveLoc`. After conversion, `expandInductivePredicates`
(`Transform/Inductive.cpp`) turns each body into one condition `F` (returns
under `if`/`else`), groups predicates that apply each other (strongly
connected components), checks that the members occur in each body only
positively and continuously (conjuncts, disjuncts, `?:` branches, `exists`,
bounded `forall`; never under negation, in a comparison, conversion,
condition, argument, quantifier bound, or unbounded `forall`), and generates
for each member the recursive spec `P.step(h, x)` (`InductiveStepOf`,
`decreases(h)`, mathematical `h`) with body `h > 0 && F[Q(a) := Q.step(h -
1, a)]` for every member `Q`. `P`'s body becomes `exists(h, P.step(h, x))`,
its true definition, and `F` is kept as `VFunction::Unfolding`. `P` is
hidden in every function that does not `reveal` it, and
`specApplicationFacts` assumes `P(t) == F[t]` beside its postconditions at
each application, in function bodies (`addSpecPostInstances`) and in spec
checks (`addSpecPostChecks`). The unfolding reads memory at the
application's heap version, and the facts of an application are keyed by
callee, arguments, and heap version, so the same application before and
after a store has facts of its own. The applications inside an unfolding
get none at depth one, so each named application unfolds once; at depth
`d` the applications of inductive predicates inside the unfoldings of
level `l < d` get theirs too (`Passivizer::setUnfoldingDepth`, and per
predicate `reveal_with_fuel(P, d)`, which keeps `P` hidden). A predicate
reached again through a spec outside its group is rejected, since its
occurrences there escape the positivity check.

The driver deepens automatically, as Stainless unrolls: a function verdict
`Unresolved` with `spec.fuel`, `spec.hidden`, or
`counterexample.unchecked` whose module assumed unfoldings is passivized
again at depth 2, 3, and 4 (`MaxUnfoldingDepth`), skipping depths that
`reveal_with_fuel` already reached; the first `Verified` or `Failed`
verdict replaces it, and its module replaces the archived one. Every level
adds only proved unfoldings, so a proof stays sound and a counterexample is
still certified against the true definitions. It does not deepen a verdict
marked `VerifyResult::InductionOnly`: the goal needs a predicate false where
its derivations go round forever, and every fixpoint, the greatest
included, keeps every unfolding; or checking it needs a value too deep to
evaluate (no derivation among the heights tried, and no finite fixpoint),
which four more levels cannot change. A deeper attempt that finds the
first of these replaces the reason and ends the search. Unfoldings under an unbounded binder (the
`exists` of `reach`) are quantified facts, which help proofs but can keep
the solver from finding a model, so after `reveal_with_fuel` an unresolved
verdict is also tried at depth one without the fuel.

Unfolding nests a body inside itself, so every substitution under a binder
renames the binder apart when a substituted value mentions its name
(`substParamsInExpr`, the spec inliner, and the certifier's own unfolding):
the second level of `reach` once read `edge(c, c)` for `edge(c, c')`, which
stated `reach(c, b) == (c == b || reach(0, b))` and proved a false claim.

The equation is a theorem only of this construction, so it is proved per
predicate by three generated proof functions (`InductiveRuleOf`), in
mathematical integers, with every member revealed:

- `P (monotonicity)`, `P::monotone(h, j, x)`: `pre(P.step(h, x) && h <= j)`,
  `post(P.step(j, x))`, `decreases(h)`. For `h > 0` it states the induction
  hypothesis for each member `Q` that `F` applies, `forall y. Q.step(h - 1,
  y) -> Q.step(j - 1, y)`, by generalization: a fresh `y` is havocked in a
  branch that calls `Q::monotone(h - 1, j - 1, y)`, asserts the instance, and
  ends in `assume false`; the universal is assumed after it. Bounded
  universals in `F` are carried from `h - 1` to `j - 1` the same way, and an
  existential above one is fixed at a chosen witness (`P::transportN`).
- `P (case analysis)`, `P::inversion(x)`: `pre(P(x))`, `post(F)`. It names
  the height `P.height(x)`, a Hilbert choice (`IsChoice`) with axiom
  `!exists(h, P.step(h, x)) || P.step(result, x)`, asserts `P.step` there,
  proves `forall y. Q.step(H - 1, y) -> Q(y)` by generalization, and
  transports `F`.
- `P (introduction)`, `P::introduction(x)`: `pre(F)`, `post(P(x))`. The
  bound `B` is the height of `F`, clamped at zero: `Q.height(a)` for an
  application, the larger of two parts, the height at the chosen witness
  (`P::witnessN`) for an existential, and for a bounded universal the
  generated spec `P::boundN(lo, hi, v)` = `lo >= hi ? 0 : max(height[w :=
  lo], bound(lo + 1, hi, v))`, `decreases(hi - lo)`, whose postcondition
  bounds the height at every `w` in range. Each application is raised to `B`
  by a guarded `Q::monotone` call, and `P.step(B + 1, x)` is asserted.

The binders of these universals range only over parameter positions that
some application changes: a position where every application passes the
enclosing member's parameter of the same name and type is fixed (as
Isabelle's `for` parameters). A pointer binder lowers to the address
`0 + k` of an integer binder `k`, since pointers are integer addresses in
every adapter. The proofs set `TotalExpressions`, so, like spec
definitions, they carry no definedness obligations and no UB
instrumentation, and `FactsWithheld` (every member and step), so neither
the unfoldings nor the postconditions they are proving are assumed in
them; `SpecReliance::Withheld` exempts them from the demotions that follow.
They are reported only on failure (`VerifyDiagnostic::Quiet`). The driver
then settles the rules in a fixpoint with the callee contracts: a predicate
whose rule proofs do not all hold prints `Unresolved: inductive predicate:
P` with reason `spec.inductive`, and every verdict that relied on its
unfolding is demoted with that reason.

A postcondition `!result || Q` is copied to `P.step` and proved by
induction on `h` in a module of its own (`buildInductionChecks`): the
definition of `P.step` is visible, each application at a lower measure
assumes the postcondition, each application `Q.step(k, y)` also gives
`Q(y)`, and `P.step(h, x)` gives `P(x)` (both by the definition of `Q` and
`P` as existentials over heights). Termination of `P.step` is checked
separately and first, without its postconditions, so a slow induction
cannot spend the function's time before it. A failure is reported as `spec post
by induction failed: P`, and `P`'s own post module derives the
postcondition from `P.step`'s under the existential.

In every spec check module (termination, post, induction), the applications
a postcondition makes receive facts as the body's do
(`addPostApplicationFacts`), quantified like the application, one level
deep: the spec itself and its recursion cycle get none (they are opaque or
covered by the induction hypothesis), and, in a step's induction and in a
predicate's own post module, the predicates of its group give their
unfoldings only, so a lemma such as transitivity can mention its own
predicate without assuming itself. A step's bare termination check assumes
nothing of its cycle's postconditions, which are proved after it.

**Proof blocks of spec clauses:** `post(...) by { ... }`, and the same
after `decreases` and `reads`, on a spec definition. The parser caches the
block's tokens (`PendingClauseProofs`) and parses each, once
`ActOnStartOfFunctionDef` has put the parameters in scope, as a compound
statement before the body (`post` blocks with `result` enabled), into
`FunctionContractInfo::ClauseProofs`; a block on another clause, on a
non-spec, or on a declaration is an error. The converter lowers it as ghost
code in the spec's mathematical mode into `VFunction::ClauseProofs`, so the
ghost rules apply (no return, store, or assignment but to its own locals).
An inductive predicate's `post` and `reads` blocks move to its step.
`withClauseProofs` (`Transform/SpecInline.cpp`) turns a check with blocks
into one generated proof function, `TotalExpressions`, with the spec's
parameters and visibility: the check's assumptions as `assume` statements,
the blocks, then the check's obligations as `assert` statements of their
kinds (an `unsupported` obligation is kept as it is), passivized normally,
with the spec, its cycle, and its group's predicates in `FactsWithheld`.
In a `post` block, `result` is replaced by the body's value (its returns as
nested conditionals); each application of the spec's recursion cycle in
the passivized program assumes the callee's postcondition under the
measure's decrease (the induction hypothesis at the block's arguments).
The driver applies it to the post module (`post` blocks), the termination
module (`decreases` and, unless a step's bare check, `post` blocks), a
step's induction module (`post`), and the reads module (`reads`), and
records the proof functions the blocks call as dependencies of that check.

The certifier evaluates `P(v)` (`Evaluator::definition`) first as the least
fixpoint of the group's unfoldings over the arguments the derivations from
`v` reach (`leastFixpoint`; `LogicFunctionDecl::Unfolding`, lowered by
`SpecAxioms`, not archived): a worklist of (member, arguments) nodes, each
false until its unfolding holds, an application of a member read from the
table (a new one added as a node), and a node that becomes true re-queued
for its readers. A quantifier over premises is decided by its witnesses
(`fixpointQuantifier`): a universal is bounded and expanded, an
existential's witnesses must be finitely many (`witnessesOf`, below). The
fixpoint is complete only when every node is evaluated within 1024 nodes;
its values are then exact and cached, and otherwise the state is restored
and `P(v)` is evaluated by its definition, `exists(h, P.step(h, v))`, which
finds a height for a true `P(v)`. Where a definition runs out, a bool
function's postconditions (`LogicFunctionDecl::Postconditions`, over
`ResultVariable`, not archived) decide its value if they allow only one;
the identity is recorded (`CertifyResult::Evidence`,
`VerifyResult::CertifiedWith`), and the driver demotes a failure whose
evidence postcondition is not established to `Unresolved` (`spec.post`).
Functions only these refer to are materialized in an error-tolerant second
phase and kept in `ObligationModule::EvidenceFunctions` when simplification
removes them, never encoded, archived, or hashed. An application whose
definition could not be decided is remembered (`Undecided`) and fails at
once when met again; once the time or step budget is spent no failure is
recovered from (`Exhausted`). When deciding it read nothing from the model
(no choice, constant, or pointer validity), the failure is a fact about the
definition, and the module keeps it (`ObligationModule::Undecided`, shared
by the module's copies like `Given`): its other checks, its inductions, and
its confirmation then do not evaluate the application again. In
`certify_timeout`, deciding each of `odd(4)`, `odd(2)`, and `odd(0)` fails
after about 1.4 s, and every check of `four_is_odd` repeated them: the
function took 10 s and its confirmation 5 s; they now take 3 s and 1.5 s. The message for an undecided inductive
predicate names the application and the postcondition that would decide
it.

`witnessesOf` decides a quantifier whose body applies specs at its binder:
the body (negated for a `forall`) is unfolded at the binder, non-recursive
definitions first, then one and two levels of recursive ones (definitions
are equations, so each try is exact), within 20000 terms; each remaining
application at the binder, and each quantifier over it, becomes `true`
where the body is monotone in it and `false` where antitone
(`approximate`; any other position gives up), and binder-free conditions
are folded to constants. The result follows from the body and depends on
the binder only through comparisons, so the distinguished values show
where it can hold: if that is finitely many values (a stretch of at most
`DirectExpansion` between two of them counts), evaluating the true body
there decides the quantifier. Otherwise the certifier tries candidate
witnesses where the comparisons of the unfolded bodies change, then binder
values `0, -1, 1, -2, ...` up to `QuantifierProbe` on each side: a value
where an `exists` body holds, or a `forall` body fails, decides it.

**`recommends`:** parsed and stored; not emitted into the main VC. On
verification failure, a second pass adds `recommends` checks and reports
violations as warnings. These diagnostic-only second-pass modules are not
serialized into canonical archives.

**Verification:** each module already contains a counterexample query. Z3
asserts that query directly. UNSAT means every encoded obligation holds;
UNKNOWN is reported honestly. A SAT model is a counterexample only after the
certifier (`Certify.cpp`) confirms it: it evaluates the canonical query, not a
solver's encoding, with every free symbol at its model value and every logical
function at its definition, using exact integer, machine-integer, heap, and
bounded-quantifier semantics under step, nesting, and time budgets. Every
module carries each logical function's definition, a hidden one included;
fuel and `hide` only decide which unfoldings a solver receives.

When a model interprets an application differently from its definition, the
adapter adds the definition instances `f(v) = body[v]` at the disputed
arguments and solves again. The certifier chooses the points, but the
instances come from the definitions, so a later UNSAT is a proof whatever the
certifier computed. Instances of a hidden function only steer the search: a
counterexample found with them is reported, but an UNSAT that may rely on
them is `spec.hidden`, never `Verified`. A round that needs thousands of
instances is chasing an unbounded argument, as an induction goal makes a
solver do, and ends as `spec.fuel` at once, with a message that the goal needs
an induction lemma.

Every value the certifier computes carries the facts that justify it
(`DefinitionInstance`, of kind `Definition`, `Unfolding`, or
`Postcondition`): a definition instance; for an inductive predicate the
unfoldings along its derivation when it holds (the true nodes the
derivation read), and the unfoldings of every argument its derivations
reach when it does not; or the proved postcondition that decided it. A
dispute carries these facts, and refinement gives them to the solver, which
is how a predicate's value at closed arguments, such as `reach(1, 4)`, is
proved without the user naming its premises. Unfoldings and postconditions
are theorems: the adapter records each one it gives
(`ObligationModule::Given`, shared by a module's copies), and the driver adds
them to the verdict's dependencies (`AssumedUnfoldings`, `AssumedPosts`), so
a rule or postcondition that later fails demotes it. When a round adds no
fact that was not given before, the outcome depends on whether the model
keeps them (`Evaluator::keeps`): a model that breaks one is
`backend.invalid-result`, a wrong solver answer; a model that keeps every
one needs a value no finite set of instances fixes, which is `spec.fuel`,
and when that value is an inductive predicate's, false where derivations go
round forever, the message names the application and asks for a
postcondition `!result || Q`, since only induction shows it. An unfolding
at a memory value the model chose speaks of that memory only, never of the
program's symbolic memory, so a round whose only new facts are such
unfoldings stops at once (`spec.fuel`, without the native pass): the
driver's deeper unfolding at the program's memory takes over. Refining at
model memory instead spent the whole budget (`both_states` took 30 s, now
0.3 s).

Two cases are settled by instances without a model-by-model search. An
application at closed arguments is evaluated before the first check, within
the time of one check (`--certify-timeout`), and the solver receives the
instances at every application the evaluation reaches (at most 20000), so
`sum(15000) == 112507500` is computed. On the first disputed
model, Z3 also asks for the least and greatest values the query allows for
each integer argument of a disputed application, doubling a step until the
solver proves no further value exists. When both ends are proved, the models
there are certified and their disputes all become instances, which covers a
bounded domain such as `0 <= n <= 200` in one round. The check that follows
runs in a fresh solver with the remaining budget, since Z3's incremental core
is much slower on thousands of ground equations. The probe only chooses
models: an end the solver cannot prove adds nothing, and a model at an end
that holds under the definitions pins the search to that counterexample.

A race interrupts the losing encoder's context, possibly while its
certifier reads a model; Z3 then evaluates a term to nothing. Every model
evaluation goes through `Z3Encoder::evaluated`, which reads an empty result
as an opaque constant (undetermined), and a certification made by an
encoder that was stopped is discarded (`Z3Encoder::certify`). Before this,
about one run in six over sequences crashed on the empty term.

Z3 gives refinement a short slice of the query budget (5%, at least half a
second) and at most eight rounds that only search among hidden values. It
then solves the query again with whole definitions in the remaining time and
certifies any model it returns: a non-recursive function is replaced by its
definition and a recursive one becomes a native recursive definition
(`RecAddDefinition`) when its recursion is guarded: `&&` and `||` over a
recursive application become `ite`s, and every recursive application must
lie in a branch of an `ite` whose branches apply a recursive function
outside quantifiers. Z3 splits a recursive definition into cases only at
such `ite`s, neither inside a quantifier nor at one whose branches apply
recursion only under one, and a definition with one case is a macro, which
Z3 expands at every application without bound and without honoring an
interrupt (an inductive predicate's step, whose recursion is under an
`exists`, hung a query for ten minutes). A function whose recursion is not
guarded stays declared, and refinement gives its instances. Hidden
functions are defined there too, so after a
hidden-spec stop that pass gets only a short slice and its UNSAT is
`spec.hidden`. cvc5 prints its model after `sat` (`--dump-models`), and
often after `unknown` (with quantified axioms, say); the same certifier
checks either, and only a certified one is a counterexample. Arrays print
as `store` chains over a constant array, with `Bool`, `Int`, or option
(`cppverify.none`, `(cppverify.some v)`) cells (cvc5 1.1 prints a sequence
value last element first,
`(str.++ (seq.unit 2) (seq.unit 1))` for `[1, 2]`, so the adapter asks each
cvc5 executable once how it prints a sequence of known order and reads its
models accordingly), and refinement re-runs cvc5 with the instances within a
fifth of the budget (at least two seconds). cvc5 does not decide queries over
recursive definitions, so recursive functions stay declared there; once a
hidden instance has been given, every non-recursive function is defined whole
(`define-fun`).

A model may give a bounded quantifier a range too wide to expand. When the
body uses the binder only in affine load addresses and in comparisons between
polynomials in it (degree at most eight; machine operations, conversions, and
resizes count when each provably stays within its sort over the range, since
it then equals the exact one), the certifier evaluates the binder values
that reach an explicitly assigned heap cell or where a comparison may change,
plus one value between each two of them: the body is constant in between. For
an affine comparison that is its root; for a polynomial, the sign changes of
left minus right are isolated by bisection, bounding the polynomial on each
interval exactly by its expansion around the midpoint
(`d0 -/+ sum |dk| h^k`), so an interval whose bound excludes zero has one sign
and the rest is split down to single values; adjacent intervals of different
sign add their boundary. The same bound decides that a machine value does
not wrap. Otherwise it probes both ends of the range. If that does not
decide a quantifier outside every binder, the adapter asks the solver for a
model whose range is at most 4096. Failing to find one settles nothing.

The same analysis decides a quantifier without bounds: the distinguished
values, one value between each two, and one beyond each end cover every
integer, provided every converted value is constant in the binder (a
polynomial comparison's roots lie within the Cauchy bound
`1 + max|a_i| / |a_n|`). Collection reads count as loads: a sequence is 0
before index 0, its elements, then 0 from its length on, and sets,
multisets, and maps are already piecewise constant over the integers. A
`HeapFrame` is compared segment by segment over the heaps' breakpoints. A
lifted `choose` is read from the model, like an uninterpreted function.

A quantifier the distinguished values do not cover, such as one whose body
holds another quantifier over its binder, is decided as Presburger
arithmetic (`Backend/Presburger.cpp`). With the model fixed, every binder-free
term is a number; a term over binders becomes pieces of linear terms under
linear guards: a read at a linear address or key is the value of each run of
its heap or collection where the address falls in that run, an `ite` splits
on its condition, and machine operations, conversions, and division are
evaluated only on constant pieces. Comparisons become linear atoms over the
pairs of pieces, nested quantifiers (renamed apart) and their bounds stay
quantifiers, and the sentence is decided by Cooper's elimination, innermost
quantifier first (`forall` as `not exists not`): after scaling the binder's
coefficients to one, `exists x. F` is the disjunction of `F` with `x` far
below every bound at one residue per period of its divisibility atoms, and
of `F` at each lower bound plus each such residue (or the same from above,
whichever side has fewer bounds). A product or quotient of binders, a
machine operation on a binder, or a spec at a binder is outside the fragment,
as is a blowup beyond 200,000 nodes. A quantifier outside the fragment is
still decided by its finitely many witnesses (`witnessesOf`, above) or by a
witness among the candidate values and binder values `0, -1, 1, -2, ...`,
up to `QuantifierProbe` on each side (with the outer binder fixed, an
inner quantifier often becomes linear). Otherwise the counterexample stays
`counterexample.unchecked`. Unit tests cross-check the decisions
against Z3 on random sentences.

`--profile-quantifiers` reruns a quantified Z3 query that stayed unresolved
with `qi.profile`, one rerun at a time, capturing what Z3 writes to file
descriptor 2. Each quantifier's instance count and greatest generation are
reported by its id `q@line:col` (text notes and JSON `quantifier_profile`),
the busiest first. The profile needs a POSIX host.

A bounded domain found by Z3 under the bit-vector encoding is settled by a
fresh encoder in the integer encoding with the remaining budget: both are
exact, and thousands of definition instances over bit-blasted machine
arithmetic would otherwise exhaust the budget.

A model that fails the query even under its own interpretation is
`backend.invalid-result`; one that cannot be checked within the budgets is
`counterexample.unchecked`, or `spec.fuel` when checking it needs unbounded
unfolding. One check may take at most `--certify-timeout` milliseconds (by
default half the query timeout; `CertifyLimits::CheckTimeoutMs` names it in
the reason), so a model whose check is slow leaves time to others and to
the later stages instead of spending the query.

The certifier evaluates `&&` and `||` in Kleene's strong logic: operands
without applications or quantifiers first, and an operand that decides the
connective decides it whatever the others are, so an undecidable operand
settles nothing only when no operand decides. Wherever several
evaluations may each decide a value (the operands of a connective, a
quantifier's instances, its candidate witnesses, the binder values near
zero), they run fairly (`Evaluator::fairly`): each gets a slice of
evaluation steps in turn, doubling every round, and a search nested in a
slice divides that slice among its own tries. A cheap decision is then
found whatever the order, as dovetailing finds a halting computation among
many: refuting an induction hypothesis `forall c. !reach.step(38, c, b) ||
!reach(c, b)` at `c = 7718` took 4 s once candidates near zero, whose
derivations branch without end, could no longer take the whole budget
first. Steps count the terms built by unfolding definitions for witness
analysis and by Presburger decisions, so a slice measures work. A failure
caused by a spent slice is never cached as undecided and is recovered from
only by the search that set the slice. Slices start at 65536 steps, so an
ordinary finite chain of definitions finishes in its first try. A try's
slice is what remains of the round divided among the tries left, so a try after cheap ones gets nearly
all of it and a deep chain of searches costs linear work. An application
whose definition needs its own value (`f(1) == !f(1)` for a spec whose
termination fails) is undecided at once, as a definition limit, instead of
recursing to the nesting limit. If the complete query is unresolved, Z3 may solve the module-owned
ordered queries. It does not reconstruct alternate passive programs.

**Induction.** A module left `Unresolved` with `spec.fuel` (or marked
`InductionOnly`) is retried by well-founded inductions in
`VerifyBackend::verify`, the entry every caller and backend shares; composite
backends call `verifyDirect` on their solvers, so the step runs once, over
the composite (`Backend/Induction.cpp`). The claim of a module is its
obligations other than unwinding ones without the theorems added to them: each
passive assumption is labeled where it comes from (`PassiveStmt::Theorem` for
a proved spec postcondition or unfolding instance or a reads frame, which
hold at every value of every variable; the leading `PreconditionCount` entry
assumptions are the function's preconditions), and Layer 3 keeps copies of
those assumptions, simplified like the goals (`ObligationModule::Theorems`,
`Preconditions`; never archived or hashed, so an archive replays with every
assumption a premise, as before). A scheme (`InductionScheme`) is a measure
over some variables: the `decreases` of a recursive spec applied in the claim
at that application (`LogicFunctionDecl::Decreases`, lowered by `SpecAxioms`),
or one integer variable (strong induction). Its induction module is the
module with a hypothesis assumed by every obligation other than unwinding
ones: the claim, with the definitions it assumes substituted
(`(x == t && A) -> B` becomes `(A -> B)[x := t]`, which only adds models),
at every value of the variables smaller by the decrease relation of
termination checks (`(lower_I == upper_I for I < J) && upper_J >= 0 &&
lower_J < upper_J` for some J), which has no infinite descending chain, so
the hypothesis holds of a least counterexample whatever the measure. The
whole hypothesis is one quantifier where the variables are integers (canonical
quantifiers range over integers); beside it come instances at the values the
spec's recursion reaches, found by walking its step definition with the
conditions on the path (an `ite` branch, the operands an `&&` or `||` passes),
through the step definitions of the other members of its recursion group
(computed from the step definitions, at most three deep), and under
quantifiers as quantified instances with the binder's range, each guarded by
the decrease and joined by the theorems restated at its values. A heap
argument stays fixed; an argument that is a variable or its conversion to the
parameter's sort gives the variable's value. Only `Verified` and
`BoundedSafe` are taken from an induction module: its models satisfy
hypotheses foreign to the program, so a counterexample is left to the
module's own search. Each attempt is marked `ModuleAttempt::Induction`,
and `verifyDirect` gives every attempt a deadline a sixth of the query
budget away (at least two seconds, `attemptBudgetMs`), which all its queries
share: the whole query, the obligations, refinement rounds, and the native
pass. The inductions of a module together get at most two such slices,
since the loop lowers the backend's deadline for them (`setDeadline` keeps
the function's, `applyDeadline` passes the one in force to the solvers).
Before, the slice bounded each query, and one attempt of `not_inductive`
took 30 s. An attempt also gets the integer encoding, no domain probing,
and refinement rounds of at most `MaxProofRoundInstances` (200) instances:
thousands of ground instances can keep Z3 from noticing a timeout (a round
of 1799 instances of `triangle` ran 6 s past a deadline of 5 s), while the
instances a proof by induction needs are few (at most 7 in the tests). At
most three schemes by a spec and two by a variable are tried. The result names the induction that
settled it (`InductionUsed`) or those tried (`InductionTried`). In cvc5's
integer encoding a binder whose range fits a machine sort converts to that
sort as itself rather than through the modular reduction, so its
applications stay visible to instantiation.

**Confirming a counterexample by proof.** When the certifier cannot evaluate
an application a candidate needs (`DefinitionTooDeep`), the adapter records
the candidate's values of the source variables (every non-heap variable for a
module that names none), the application with its arguments' values, and the
reason (`VerifyResult::Unchecked`, `UncheckedApplication`,
`UncheckedReason`). After every function is verified and the reasons and the
cycle fixpoint are settled, the driver confirms each such verdict, in
parallel, when the spec facts its module assumes are established: it fixes
the candidate's values, removes every variable an equation of the query
defines (the one-point rule: `x == t` with `x` not in `t`), assumes the
query's theorems, assumes what only constrains the remaining free variables
without applying a spec once a certified model of it exists (a separate
query whose `Failed` result shows it can hold), instantiates the
postconditions of the established proof functions where their spec
applications match the query's (a machine parameter seen as `bv_to_int(p)`
matches an integer term `t` with `p := int_to_bv(t)`; a proof function with
a pointer or reference parameter is left out, since its implicit
preconditions, valid storage and distinct objects, are not stated by its
declared ones), and asks the same
backend to prove the rest of the query (`ModuleAttempt::Confirmation`, with
an attempt's slice, as above). A
proof shows the claim fails at that input for some values of the free
variables, so the verdict becomes `Failed`, its message saying it was
confirmed by proof and naming the contracts used (`ConfirmedWithContracts`,
JSON `confirmed_with`); it rests on the definitions, postconditions, and
unfoldings the query used (`CertifiedWith`) and on those contracts, all
established when it is made. A verdict that stays unresolved says in plain
words what was proposed and could not be checked, that either the claim is
false there or it needs a proof by induction, which inductions were tried,
and, for a proof function, a body that starts one: a call at each value the
recursion reaches, under the condition reaching it and the precondition
there (`proofOutline`, printed from logic terms with source names).

## Counterexample Extraction

When Z3 returns SAT, CppVerify evaluates source-attributed SSA variables without
model completion. Diagnostic metadata supplies the original display name,
exact logic sort, internal SSA identity, and declaration range. Signed and
unsigned bit-vectors are rendered as source-level decimal values, and
collections as their elements, members, counts, or entries in order, a run of
equal cells as `lo..hi` with a missing bound for an unbounded run (`[1, 2]`,
`{1, 3..5}`, `{2: 3}`, `{1 -> 7, 4.. -> 2}`, `{..}`), at most 64 items. A
value that the model does not determine is reported as `<unknown>` in text
and JSON `null`; the verifier never invents a convenient value.

Passivization also records guarded branch, modular-call, loop, heap-write,
allocation, lifetime-end, deletion, and return events. Each obligation owns the
event prefix that existed when it was emitted. The Z3 model removes events with
false guards, retains true events, and marks undetermined guards explicitly
unknown. Addresses, stored values, allocation identities, and return values use
the same typed, non-completing evaluation. A complete-query counterexample is
attributed to a specific ordered obligation whenever its model evaluates that
obligation's counterexample query to true.

Public obligation identities are source anchored:
`function-identity::kind@line:column`, with `#N` only for obligations sharing
one anchor. This keeps later IDs stable when an unrelated obligation is inserted
or reordered without moving the source anchor. The ordinary diagnostic is
Clang-style text; `--diagnostics-format=json` emits one
`cppverify.diagnostic/1` JSON object per verification result, including source
ranges, typed model values, trace events, backend/bound, and a stable reason
code. Command-line/frontend errors and output combined with IR dumps are not a
pure JSON stream.

## Modular Verification Protocol

1. Build VFunction for each function in source order.
2. For each VFunction:
   a. Build Layer 1 IR.
   b. Passivize to Layer 2 (SSA + havoc/assume/assert + heap versioning).
   c. Build and validate one canonical `ObligationModule`.
   d. Validate the selected backend's declared logical capabilities.
   e. Submit the complete query and, when it does not settle the module,
      the ordered queries to the backend; with more than one job both run
      at once, and with a proof cache only the ordered queries run.
   f. Report verified / counterexample / unresolved / bounded-safe / exported,
      or kernel-certified.
3. For each failure, run a second pass with `recommends` checks → warnings.
4. Qualify each verdict by what it rests on:
   - a trusted function reports `Trusted`; an unmarked contract without a
     definition draws a warning, and every caller whose proof relies on it
     (or on any callee contract whose verification failed) is demoted to
     `Unresolved` with reason `callee.contract`;
   - `[trusts=...]` lists the trusted contracts a proof uses, closed
     transitively over verified callees (JSON `"trusts"`);
   - one fixpoint settles the reasons: a verdict relying on a spec whose
     termination, reads, or postcondition is not established, on an
     inductive predicate whose rule proofs are not, or on a callee contract
     that is not, is demoted (`spec.termination`, `spec.reads`,
     `spec.post`, `spec.inductive`, `callee.contract`), and a demoted check
     of a spec stops establishing its facts (`SpecReliance::Establishes`), a
     demoted function its contract, until nothing changes;
   - a least fixpoint then rejects circles: starting from no established
     fact, a verdict is sound once every fact it needs is, and a fact once
     every verdict producing it is sound. It needs its callees' contracts
     and its proof blocks' callees, the definitions and frames of the specs
     it mentions, and the postconditions and unfoldings its module assumes
     (`PassiveProgram`/`ObligationModule::AssumedPosts` and
     `AssumedUnfoldings`, recorded where the facts are added, never
     archived), except within a recursion cycle and for the spec it checks.
     A verdict left unsound is `Unresolved` with reason `proof.cycle`.
     Clusters (`VFunction::Cluster`, computed in the frontend) relax this
     as Dafny does: the specs and proof functions that reach each other
     through bodies, contracts (pre, post, decreases), and proof blocks,
     when all share `decreases` clauses of one length. A call to a member
     asserts the decrease (the passivizer's call-site check, which a
     spec's generated block function gets by taking the spec's measure);
     a member's postcondition, and a recursive member's one-step
     definition, are assumed only under the decrease of the callee's
     measure below the user's at entry (`specInductionFacts`, recorded as
     `InductivePosts`); and recursive members are hidden from each other,
     so no definition reaches the solver unguarded. The fixpoint then
     needs no contract, postcondition, or definition fact of a member;
     frames are not guarded and stay needed. Every use descends the shared
     measure, so the members' facts hold by well-founded induction, and
     the failure of one still demotes the others through the first
     fixpoint;
   - an `Unresolved` verdict whose solver proposed a counterexample its
     check could not evaluate is then confirmed by proof where it can be,
     from the contracts and spec facts now known to be established (see
     "Confirming a counterexample by proof"); it becomes `Failed`, which
     changes no other verdict, since neither establishes a contract;
   - every `Verified` result gets the vacuity checks, small queries over the
     same passive program: `false` at the end of the function (the whole
     proof is vacuous), each behavior's `pre && assumes` (a behavior that
     never applies), and, for each call of a trusted contract, whether its
     path is reachable before the postcondition assumptions and unreachable
     after them (the trusted contract contradicts that call). Passivization
     marks the first assumption of a trusted callee's postcondition with the
     callee, its clause count, and the call's path condition for this.
     Under BMC the passive program is the one unrolled to the final bound,
     so the same checks apply there, and a `BoundedSafe` result whose end
     no execution reaches within the bound is `[vacuous]` with a warning
     naming the bound;

## Verification Backends (`VerifyBackend`)

The driver selects a backend via `VerifyOptions` (`Verifier.h` / `cpp-verify --backend`):

| Backend | Implementation | Notes |
|---------|----------------|-------|
| **Z3** | `Z3VerifyBackend` | Default. Consumes `ObligationModule`; counterexamples come from models. |
| **cvc5** | `CVC5VerifyBackend` + standalone SMT-LIB2 | Encodes the same canonical sorts, C++ truncating math division/remainder, bit-vectors, signed overflow, total heap, bounded and unbounded quantifiers (marked triggers as `:pattern`), heap frames, sequences (`full-saturate-quant` when sequences meet quantifiers), and finite ground spec equations. Sets, multisets, and maps are arrays over all integers, as for Z3 (cvc5's own set theory is finite, which would prove facts false of an infinite set): `(Array Int Bool)`, `(Array Int Int)` with a count of `max(0, cell)` and equality count by count, and `(Array Int cppverify.option)` over a declared `none | some(value)` datatype; union, intersection, and difference are declared functions each defined pointwise by one quantified axiom, exact by array extensionality, and subset is a quantified formula. A model cvc5 prints with `unknown` is certified like one after `sat`. Solver process failures and malformed output are unresolved. |
| **Strict portfolio** | `PortfolioVerifyBackend` | Runs ordered Z3 and cvc5 queries. Matching UNSAT proves; matching certified counterexamples fail and retain the Z3 model; disagreement or an unresolved side is unresolved. |
| **Race** | `RaceVerifyBackend` | Runs the Z3 and cvc5 backends at once; the first proof or certified counterexample stands and cancels the other (`cancel`/`resume`: a backend-wide `Race` of Z3 encoders, each forwarding an interrupt to the pass it runs, and a flag the cvc5 process loop polls). Otherwise the obligations either proved are joined, `Verified` (`z3+cvc5`) when they cover the module. |
| **BMC** | `LoopUnroll` on VCR, then shared obligation/Z3 path | Source verification grows bounds from zero through `--unroll=N`, stopping on a counterexample, complete unwinding, unresolved query, or the maximum frontier. Safety with failed unwinding is `BoundedSafe(N)`; only proved unwinding is `Verified`. A spec's checks have no loops: the driver solves them with a Z3 backend (`SpecBackend`), as on the default path, and keeps the bound on their archived modules for replay. |
| **Lean** | `exportLeanScratchPad` / project certification | Standalone mode emits unchecked theorem stubs. Project mode emits direct source goals, total functional heaps, typed bit-vector/integer operations, and compact finite-fuel spec bodies into generated files while preserving user proofs. Export is `Exported`; only the pinned admission-free kernel/axiom check is `Certified`. Collections are `logic.unsupported` (planned for a future release). |

Each backend declares supported `LogicFeature`s. Central dispatch rejects a
module requiring an unavailable feature before backend execution. Spec
inlining runs before passivization on Z3/cvc5/portfolio/BMC
(`SpecInliner::prepareFunction` or `prepareFunctionAxiomatic` for recursive
specs). `--lean-fallback=DIR` keeps Z3 or strict portfolio as the primary
backend and sends only `Unresolved` modules through the same canonical Lean
adapter. An unresolved Z3 or portfolio result lists the obligations it did not
prove individually, and by default only those are exported, under their
complete-export goal names (`--lean-fallback-scope=all` exports every
obligation). Once they kernel-check, the result is `MixedProof`
(`Proved (z3+lean)`, JSON `mixed-proof`) with `ProofEvidence` recording the
split; `Certified` still means Lean checked every obligation. SAT
counterexamples are never fallback successes.

Z3-backed execution accepts explicit timeout, deterministic solver-resource,
canonical query-node, job-count, and proof-cache budgets. A module that
requires the `sequences` or `collections` feature gets the collection
timeout (`--collection-timeout`, by default twice `--timeout`) on every
solver backend. The driver verifies each function as a task (its own backend,
smoke backend, passivizer, and buffers for diagnostics, dumps, and archive
records) on one `llvm::StdThreadPool` of exactly `--jobs` workers, which the
Z3 and cvc5 backends also receive (`BackendExecutionOptions::Pool`) for their
obligations: a task waiting on its obligation group runs those tasks itself,
so nesting never exceeds the pool. With more than one job and obligation, Z3
solves the obligations beside the whole query (`Z3VerifyBackend::Race`): a
proved whole query interrupts the obligation encoders, and a complete set of
proved obligations interrupts the whole query, which then runs in an encoder
of its own because a Z3 interrupt can outlive the check it stops. Otherwise
the obligations decide, exactly as after a whole query alone, so the verdict
does not depend on the jobs. A proof cache stores proofs of single
obligations, so with one only the obligations are solved.
Results merge in source order, with each function's dependency indices
offset; spec termination, callee contracts, trust, and unverified callers are
resolved after all functions. A per-function deadline
(`VerifyBackend::setDeadline`, `--function-timeout`, by default ten times
`--timeout`) caps every query at the time the function has left, and no
query starts once it has passed. Four times `--timeout` was too little: the
bit-vector run of `extent_separation`'s `copy` needs 32 s of queries at
`--timeout=5000`. Z3 forgets a timeout that fires inside one of its nested
resource scopes (leaving a scope clears the cancellation; a check given one
or two milliseconds never returned), so `Z3Encoder::check` interrupts a
check again, every 50 ms from 100 ms past its time, until it returns.
`Z3Encoder::interrupt`, which races use, is sticky the same way: a stopped
encoder's checks return `unknown` at once, and a running one is interrupted
until it returns. Source-location annotation takes a lock, since
the source manager caches its last lookup. Lean stays serial, and the
compile-time verifier keeps a single job.

cvc5 execution resolves an explicit `--cvc5-path` or searches `PATH`, writes one
bounded temporary SMT-LIB2 query, invokes the executable without a shell under
the same timeout/resource policy, accepts only one exact `sat`, `unsat`, or
`unknown` verdict, reads the model printed after `sat`, bounds captured output,
and removes query/output files. cvc5 processes may run concurrently; each exact
child is polled, bounded, terminated, and reaped independently, while results
remain source ordered. Portfolio mode uses a separate Z3 cache namespace for its Z3
component and always reruns cvc5, so a cached single-solver proof cannot bypass
independent agreement.

The persistent cache contains only successful individual proofs. Its immutable
entry binds the dependency-scoped semantic hash to semantic-hash format v4, the
Z3/BMC backend namespace, adapter revision, and exact Z3 version. BMC bound
provenance is part of the semantic hash. Writes use temporary files plus atomic
replacement; malformed/incompatible or unreadable entries are fail-closed
`Unresolved`, never cache misses or proofs. Store/prune failures after a fresh
solver proof remain explicit telemetry rather than invalidating that proof.
Size and entry-count pruning proceeds independently of cache errors, retries a
capacity-limited write after eviction, touches only CppVerify-prefixed records,
and removes abandoned atomic-write files after 24 hours. Failed, unknown,
resource-limited, and `BoundedSafe` results are not cached.

Incremental BMC retains one `BMCVerifyBackend` across bounds. It reuses only
ordered queries already proved `Verified` in that process. The reuse identity
contains the exact transformed goal and reachable logical declarations but
omits the enclosing frontier number; therefore identical prefix obligations can
be reused while every changed or unwinding query is solved again. Persistent
cache records remain bound-separated. The driver archives and dumps only the
terminal module, with its actual bound. Archive replay consumes that one bound
and does not claim to repeat incremental source exploration. Loop trace events
carry one-based iteration numbers at the original source location.

## Modular Exec Calls

`ASTConverter` lowers contracted **exec** calls to `VCallStmt` nodes. Nested calls in expressions (e.g. `return f(g(x))`) are flattened into a sequence of calls with temporaries (`__nested_N`) so `Passivize::emitCallStmt` can apply callee `pre`/`post` at each site.

At each call the passivizer:

1. Maps actual arguments into the callee parameter namespace.
2. `assert`s callee preconditions (including implicit non-aliasing from the callee's contract).
3. Changes the value heap only inside the callee's `modifies` footprints.
4. `assume`s callee postconditions (including `result` linkage), where a
   formal, inside or outside `old`, denotes its entry actual.

Calls to functions marked `usesDynamicStorage` fail closed unless they carry
the inferred `freshOwnedReturn` summary. That one effect materializes a fresh
caller-side lifetime as described above; no arbitrary callee metadata-heap
transition is imported. General allocation/deallocation and escape contracts
remain unsupported.

The inverse checked boundary is supported: a caller-owned dynamic scalar
identity may substitute a matching pointer parameter of a verified,
non-allocating callee. A recursive VCR safety scan admits direct scalar
dereference/comparison, acyclic forwarding through matching verified pointer
parameters, and executable/spec calls on already loaded scalar values. It
rejects offset/subscript access, pointer copies/rebinding, recursive scan
cycles, borrowed pointer-result intermediates without an owned summary, ghost
access, proof/external contracts, and deallocation.

A pointer-returning callee may return a direct dynamic formal, null, or a
conditional selection of direct dynamic formals. `VCallStmt` carries a
`ResultProvenanceTarget` alongside `ResultTarget`; passivization freshens both
and substitutes the paired result into generated validity and initialization
postconditions. A source-level result equality then relates the returned
address to the caller input, while the metadata owner map determines its
lifetime identity. Returned local copies and foreign pointer sources fail the
structural scan.

The callee may update the value heap under its ordinary `modifies` contract;
metadata heaps remain with the caller. A provenance-bearing footprint is not
accepted merely by shape: its identity must equal one of
`OwnedAllocationIdentities`. This prevents a fresh or foreign pointer result
from acquiring caller-owned write/delete authority. Allocation identity and
pointer-result targets are preserved through cloning, spec preparation, loop
unrolling, and all Z3/BMC/Lean paths.

Within a dynamic-storage caller, provenance is first-class VCR state.
`VVarExpr` names the pointer's SSA companion identity, and `VAllocateStmt`
defines both a fresh address and a never-reused lifetime token. Matching-pointee
copies, assignment, conditional selection, and `nullptr` update address and
provenance together; ordinary branch merging therefore merges both values.
Supported modular pointer results define and merge the same two SSA components.
Loads, stores, and `delete` compare the current byte owner with that companion,
so reassigning a pointer cannot revive an old lifetime or transfer ownership to
the wrong allocation.

The same allocation metadata represents bounded automatic objects.
`ASTConverter` performs a conservative whole-body address-use discovery for
supported scalar locals, fixed arrays, and trivial standard-layout enclosing
records. If any supported subobject needs an address, the complete enclosing
object lowers to `VAllocateStmt(IsAutomatic=true)` and thereafter has only one
heap representation; unaffected locals remain scalar SSA. A post-lowering
invariant scan rejects any parallel scalar representation of a promoted object.

Automatic objects receive fresh lifetime identities, target size/alignment,
byte ownership, liveness, and per-leaf initialization. Passivization makes them
disjoint from incoming address parameters, complete declared extents, stored
pointer cells, and every live represented object. Their lifetimes end at the
lexical closing brace and on each supported early return in reverse construction
order, after materializing any heap-reading return value. Scalar references may
bind fields and fixed-array elements with access-local nested bounds. General
escape, raw array decay/address-taking, aggregate references, and addressable
declarations inside loops remain fail-closed. Automatic metadata transitions
are private and a modular caller may frame them away.

Local reference declarations snapshot their VCR address in a marked
`VAssignStmt`. The marker survives cloning and BMC loop unrolling and lets the
checked-scalar callee scan track immutable aliases transitively without
admitting general pointer copies or rebinding. Provenance-backed reference
actuals can therefore use exact scalar-cell framing after the same scan rejects
offset access, escape, recursion cycles, and unsupported boundaries.

**Pointer origins.** Before UB instrumentation the driver runs
`annotatePointerOrigins` (`Transform/Origins.cpp`) on each executable and
proof function: an abstract interpretation over the structured VCR body that
records on every occurrence of a pointer variable (`VVarExpr::Origins`) the
objects it may address there. A pointer parameter with an object starts with
it (its name), a global's address is `@address/size`, null is the empty set,
and a load, a call result, or an allocation is unknown (represented storage
keeps its lifetime companion instead). Arithmetic keeps the origin,
assignment copies it, an `if` joins its branches, and a loop's head is the
least fixpoint over its body and `continue`s; sets above eight origins
become unknown. Every clone copies the annotation. An origin's identity is a
literal: a global's address, or the negated base-256 number of a
parameter's name, so distinct origins never compare equal. A variable whose
occurrence may hold several origins gets a companion `name.__origin`,
assigned beside it (not on a step, which keeps it), initialized for a
parameter at entry. For each loop the pass adds two invariants, proved like
any other: a companion the loop assigns stays among the head's origins, and
a pointer the loop assigns is null or `q % S == o % S` for each origin `o`
of `S`-byte elements, since typed steps move by whole elements and objects
lie at positive addresses.

The annotations are consumed in three places. UB instrumentation requires an
access or step through a pointer with known origins to lie in one of those
objects (guarded by the companion when there are several), instead of in
some parameter's object. Loop write sets use the origins' entry objects. And
pointer difference requires one origin.

Executable pointer difference consumes the same identity model. `ASTConverter`
admits matching complete pointee types with recursively compositional pointer
arithmetic. VCR first subtracts mathematical target-byte addresses and divides
by the Clang target `sizeof(T)`. Passivization asserts non-null/live bases,
one origin, in-range positions, and target-`ptrdiff_t` representability
before normalizing recoverable same-base indices to machine subtraction.
Represented storage compares lifetime identities (a mismatch is a
`pointer-difference` error). Otherwise both operands' origin terms must be
equal, an obligation of kind `unsupported`: different parameters' objects
may be one caller array, which the object model does not describe. Each
position must lie in its origin's entry object, one past the end included
(`[0, n]` of a `VValidExtent`, else `[0, 1]`). Explicit specs and lifted
`constexpr` functions still reject pointer difference.

The driver builds a UB-instrumented interface map before passivization so
callee `VValidExtent` summaries are available at call sites. A slice actual is
lowered only after proving structural same-origin containment, including
nonnegative offset/length and the one-past empty case. A conservative transitive
body scan distinguishes acyclic read-only callees from unknown, recursive, or
writing effects. Exact-cell writes reuse ordinary frame substitution; symbolic
writable ranges and unbounded region writes through a sub-slice fail closed
until passive/obligation IR has a quantified range-frame primitive.

Ghost blocks and proof functions share the VCR statement vocabulary but are
erased by CodeGen. Frontend isolation therefore permits assignments only to
ghost/proof-local values, rejects executable calls and runtime-memory/global
writes, and requires `decreases` on proof-only loops. This prevents erased
mutation, returns, or nontermination from changing executable verification
semantics.

## Compile-Time Integration

`CppVerifyIntegration` (`clang/lib/Verify/Driver/CppVerifyIntegration.cpp`) hooks **CodeGen**: when `-fverify-contracts` is on and `-fno-verify` is off, verification runs asynchronously while LLVM IR is generated. Failures surface as `diag::err_fe_cppverify_failed`. Zero ghost/spec code in the object file.

## IR Debugging (`--dump-ir`)

`DumpIR.cpp` prints layers: **1** VCR, **2** passive, **3** canonical
`ObligationModule`, **4** Z3 text. Layer 3 includes the schema version, module
and per-obligation semantic hashes, function identity, required features,
direct and negated goals, typed terms, obligation IDs/kinds, resolved source
metadata, ordered queries, and owned finite-fuel logic declarations.
Frames print as `heap_frame` with their regions, trigger patterns as
`trigger` children of their quantifier, and collection operations by name
(`seq.push : seq`). Layer 4 encodes that same in-memory module, preceded by
the range facts, bit definitions, the definitions of `cppverify.cell_*` and
`cppverify.seq_at` that the query uses, and the sequence index, split, and
membership facts. The layer mask is parsed by
`parseDumpIRLayers` (`1`, `2`,
`layer-3,4`, `all`, etc.).

`cpp-verify --lower-only` runs the entire selected Z3/cvc5/portfolio/BMC
lowering pipeline through spec-axiom and goal encoding, but does not call a
solver. An
encoding error remains a hard failure; success is reported as `Lowered`, never
`Verified`. This is intentionally distinct from Clang's `-fno-verify`, which
stops before VCR conversion.

## Regression and Coverage

- Tests: `clang/test/Verify/` (frontend) and `clang/test/Verify/suite/`
  (end-to-end Z3/cvc5/portfolio/BMC/Lean/dump).
- Unit oracles: `clang/unittests/Verify` (`VerifyTests`) checks every machine-integer
  operator against `llvm::APInt` under each encoding; with
  `CPPVERIFY_PARITY_ARCHIVES` it also compares encodings per archived obligation.
- Runner: `scripts/run-verify-tests.sh`; every solver-positive example receives
  a solver-free lowering preflight before its semantic verification run.
- Backend fidelity gate: `clang/test/Verify/suite/backend_fidelity_gate.test`
  requires cvc5 and pinned Lean 4.32.2 and runs the permanent differential
  matrix under every machine-integer encoding.
- Instrumented coverage: `scripts/coverage-verify.sh` (region target on `clang/lib/Verify`).

Every new semantic feature needs layered oracles rather than a solver result
alone:

1. realistic positive and false C++ programs;
2. Layer 1 checks for typed VCR lowering;
3. Layer 2 checks for SSA, heap versions, and path merges;
4. Layer 3 checks for sorts, features, IDs, origins, and the decisive canonical
   query, plus Layer 4 checks for its Z3 translation;
5. solver-backed proof and counterexample tests.

The structural checks use `--lower-only`, so a slow or undecidable query cannot
mask a lowering regression. Conversely, `Lowered` is never accepted as a proof:
SAT/UNSAT/UNKNOWN handling remains a separate backend gate.

The release matrix in
`clang/test/Verify/suite/backend_fidelity_gate.test` is executable rather than
an unchecked support table:

| Canonical surface | Required evidence |
|---|---|
| Boolean control and mathematical integers | Layer 3 nodes plus matching decisive Z3/cvc5/portfolio/BMC outcomes |
| Bit-vectors, resizing, signedness, and overflow | Positive conversions and bit operations; false add/sub/mul/neg/div and bounds obligations |
| Pointers and total heaps | Loads, stores, default non-aliasing, `valid(p,n)` bounds, and source-identical failures |
| Quantifiers and finite-fuel specs | Both quantifier kinds, recursive spec calls, and conservative `unknown` rather than false proof |
| Frontend-derived semantics | Type invariants and complete-loop Z3/BMC parity |
| Portable artifacts | Source-stable obligation IDs, canonical/BMC archive replay, and deterministic parallel results |
| Lean | Source/archive theorem identity, stable proof-module hashes, generated-file kernel build, and bounds instrumentation |
| Advisory checks | `recommends` warnings stay source-only and never enter BMC or Lean replay artifacts |

An approved valid quantified or inductive query may remain
`solver.unknown` on cvc5; every false matrix case must still be found, and
disagreement is always a gate failure. A new canonical sort, feature, or
operator must extend this matrix before its backend capability can be treated as
release-ready.

## Research and Production Extension Boundary

CppVerify has one owner for each semantic layer:

1. Clang AST/Sema owns C++ typing, evaluation, layout, and supported-language
   decisions.
2. VCR owns control flow, typed values, object/place/effect operations, and
   source locations shared by every analysis.
3. Passive SSA owns path ordering, heap versions, modular call abstraction, and
   loop proof rules.
4. `ObligationModule` owns backend-neutral logical meaning.
5. Adapters own only target encoding, solving, proof export, and
   backend-specific diagnostics.

A research backend should consume `ObligationModule`; it must not reinterpret
the Clang AST. A research VCR pass must preserve types, source locations,
function identity, integer mode, allocation/provenance metadata, and its
documented input/output invariant. New logic features require an explicit
`LogicSort`/`LogicExpr` representation and `LogicFeature` capability bit before
any adapter may accept them. Unsupported composition returns `unknown`.

Graduation into the production path requires deterministic Layer 1-4 dumps,
positive and false-program regressions, Z3/BMC differential checks where
applicable, solver-independent `--lower-only` coverage, performance benchmarks,
and fail-closed review.

Remaining platform work is explicit rather than hidden:

- VCR still lacks a first-class object/place/effect type system, arrays, and
  structured aggregate values;
- pass registration and a stable plugin ABI are not implemented yet;
- archives carry portable inclusive presumed source ranges rather than raw
  Clang locations or macro-expansion stacks;
- Z3 proof-object certification and independent replay are not implemented;
  Lean certification is an interactive proof path, not Z3 proof replay.

| Future feature | Correct extension point |
|---|---|
| Alternate SMT solver / portfolio | New `ObligationModule` adapter with capability and model semantics |
| Symbolic execution | VCR analysis/backend preserving C++ and source metadata |
| Separation/ownership reasoning | VCR object/effect extension plus a declared logic feature and adapter |
| Abstract interpretation / invariant inference | VCR pass that proposes facts rechecked as ordinary obligations |
| `std::vector` model | Frontend/library model lowered to VCR object/place operations |
| Concurrency | VCR atomic/effect model, then explicit happens-before logic terms |
| Manual quantifier triggers | Extend neutral quantifier terms and backend capabilities |
