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
  | SpecCall(identity, args: [VExpr], type)
  | OverflowCheck(op, lhs, rhs?)
  | Forall(binder: VarDecl, lo: VExpr, hi: VExpr, body: VExpr)
  | Exists(binder: VarDecl, lo: VExpr, hi: VExpr, body: VExpr)
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

### Statements (VStmt)

```
VStmt =
  | VarDecl(name, type, init: VExpr?)
  | Assign(target, value: VExpr)                          // local variable
  | Store(ptr: VExpr, value: VExpr)                       // *p = value
  | Allocate(target, allocatedType, init?, sizeBytes, alignBytes)
  | Free(ptr: VExpr)
  | If(cond: VExpr, then: [VStmt], else: [VStmt])
  | While(cond: VExpr, invariants: [VExpr], decreases: VExpr?, body: [VStmt])
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
  modifies: [VLvalue]                  // explicit frame, or inferred conservative default
  aliases: [(VarName, VarName)]        // opted-in aliasing pairs
  recommends: [VExpr]                  // spec functions only
  body: [VStmt]
  isSpec: bool
  isProof: bool
  usesDynamicStorage: bool
  freshOwnedReturn: (allocatedType, size, alignment, nullable)? // inferred
  decreases: [VExpr]                   // tuple → lex-ordered
  intMode: VIntMode                    // Math for explicit spec; Machine otherwise
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
assume(I);                         // 3. inductive hypothesis
if (cond) {                        // 4. if loop continues:
    [body in SSA]                  //    execute one iteration
    assert(I);                     //    invariant preserved
    assert(D_new < D_old);         //    termination measure decreases
    assume(false);                 //    cut path
} else {
    // continue with I ∧ ¬cond
}
```

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

**Function calls → assert precondition, havoc modifies, assume postcondition:**
```
// y = foo(x)  where foo has pre(P) modifies(M) post(Q)

assert(P[params := args] ∧ /* implicit non-aliasing pre, if applicable */);
havoc(M);                              // forget the locations declared in modifies
havoc(y);
assume(Q[Result := y, Old(params) := args]);
```

- The heap version increments only across the modifies set: `mem_{k+1}(loc) = mem_k(loc)` for `loc ∉ modifies`.
- If `modifies` is the conservative default (all reachable through mut params), the entire heap is havocked.
- A `freshOwnedReturn` call is not a whole-heap havoc. It preserves every old
  cell, materializes one disjoint initialized scalar object, then assumes the
  ordinary postconditions against that new heap.

## Layer 3: Canonical Obligation IR

`buildObligationModule` is the only passive-to-logic lowering path. It folds the
ordered `PassiveProgram` once and publishes:

- a typed `LogicExpr` tree with explicit `Bool`, mathematical integer,
  width-indexed bit-vector, pointer, and heap-array sorts; integer sorts retain
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
preserves semantic identity.

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

| VExpr | Z3 Expr |
|---|---|
| BinOp(+, a, b) | `a + b` (Int) or `bvadd a b` (BitVec) |
| BinOp(&&, a, b) | `(and a b)` |
| Cast(inner, Int32, Int64) | math mode: identity — BitVec mode: `(sign_ext 32 inner)` |
| Cast(inner, UInt32, UInt64) | math mode: identity — BitVec mode: `(zero_ext 32 inner)` |
| Load(p, T) | `(select mem_k p)` for the current heap version k |
| Forall(x, lo, hi, P) | `(forall ((x Int)) (=> (and (<= lo x) (< x hi)) P))` — bound is the implicit trigger |
| Old(x) | `x_entry` (SSA version at function entry) |
| Old(*p) | `(select mem_0 p_entry)` |
| Result | `result_var` (SSA version of return value) |

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
  reduce modulo `2^N` (`mod(x + 2^(N-1), 2^N) - 2^(N-1)` when signed);
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

Range facts make Z3 assign every machine variable. Counterexample extraction
therefore reports a variable as undetermined (`<unknown>`) when the goal and
spec equations still evaluate to true with it, and every variable freed before
it, replaced by an unassigned symbol. Layer 4 dumps print the range facts and
bit-vector definitions before the goal.

**Spec functions → owned logical functions:** while VCR is still available,
`SpecAxioms` materializes every reachable typed declaration and finite
definition level into `ObligationModule`. Z3 emits equations only at concrete
logical call sites. Recursive leaves remain applications of the opaque logical
function, and `reveal_with_fuel` controls the exact finite depth. Adapters never
borrow `VFunction` metadata.

**Heap-reading specs:** a spec that reads memory, directly or through another
spec, becomes a logical function with a leading `__spec_heap` parameter of sort
`Heap`; its definitions read through that parameter. Each call site passes the
heap version passivization resolves for it, exactly as for a load, and
modules containing such functions require the `heap-functions` logic feature.

**`recommends`:** parsed and stored; not emitted into the main VC. On
verification failure, a second pass adds `recommends` checks and reports
violations as warnings. These diagnostic-only second-pass modules are not
serialized into canonical archives.

**Verification:** each module already contains a counterexample query. Z3
asserts that query directly. UNSAT means every encoded obligation holds; SAT
produces a counterexample; UNKNOWN is reported honestly. If the complete query
is unresolved, Z3 may solve the module-owned ordered queries. It does not
reconstruct alternate passive programs.

## Counterexample Extraction

When Z3 returns SAT, CppVerify evaluates source-attributed SSA variables without
model completion. Diagnostic metadata supplies the original display name,
exact logic sort, internal SSA identity, and declaration range. Signed and
unsigned bit-vectors are rendered as source-level decimal values. A value that
the model does not determine is reported as `<unknown>` in text and JSON
`null`; the verifier never invents a convenient value.

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
   e. Submit the complete query, or dependency-scoped ordered queries when
      parallel execution/caching is selected, to the backend.
   f. Report verified / counterexample / unresolved / bounded-safe / exported,
      or kernel-certified.
3. For each failure, run a second pass with `recommends` checks → warnings.

## Verification Backends (`VerifyBackend`)

The driver selects a backend via `VerifyOptions` (`Verifier.h` / `cpp-verify --backend`):

| Backend | Implementation | Notes |
|---------|----------------|-------|
| **Z3** | `Z3VerifyBackend` | Default. Consumes `ObligationModule`; counterexamples come from models. |
| **cvc5** | `CVC5VerifyBackend` + standalone SMT-LIB2 | Encodes the same canonical sorts, C++ truncating math division/remainder, bit-vectors, signed overflow, total heap, bounded quantifiers, and finite ground spec equations. Solver process failures and malformed output are unresolved. |
| **Strict portfolio** | `PortfolioVerifyBackend` | Runs ordered Z3 and cvc5 queries. Matching UNSAT proves; matching SAT fails and retains the Z3 model; disagreement or an unresolved side is unresolved. |
| **BMC** | `LoopUnroll` on VCR, then shared obligation/Z3 path | Source verification grows bounds from zero through `--unroll=N`, stopping on a counterexample, complete unwinding, unresolved query, or the maximum frontier. Safety with failed unwinding is `BoundedSafe(N)`; only proved unwinding is `Verified`. |
| **Lean** | `exportLeanScratchPad` / project certification | Standalone mode emits unchecked theorem stubs. Project mode emits direct source goals, total functional heaps, typed bit-vector/integer operations, and compact finite-fuel spec bodies into generated files while preserving user proofs. Export is `Exported`; only the pinned admission-free kernel/axiom check is `Certified`. |

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
canonical query-node, job-count, and proof-cache budgets. Ordered queries run
in isolated worker-owned `Z3Encoder` instances and are gathered in source
order; lowering, archives, dumps, Lean streams, and diagnostics remain serial.
The compile-time verifier already runs beside CodeGen and keeps the default
single solver job, avoiding an implicit nested concurrency layer.

cvc5 execution resolves an explicit `--cvc5-path` or searches `PATH`, writes one
bounded temporary SMT-LIB2 query, invokes the executable without a shell under
the same timeout/resource policy, accepts only one exact `sat`, `unsat`, or
`unknown` token, bounds captured output, and removes query/output files. cvc5
processes may run concurrently; each exact child is polled, bounded, terminated,
and reaped independently, while results remain source ordered. It does not
manufacture models. Portfolio mode uses a separate Z3 cache namespace for its Z3
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
3. Havocs value-heap SSA according to `modifies`.
4. Maps syntactically reassigned by-value formals to fresh final values while
   retaining entry actuals for `old(formal)`.
5. `assume`s callee postconditions (including `result` linkage).

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

Executable pointer difference consumes the same identity model. `ASTConverter`
admits matching complete pointee types with recursively compositional pointer
arithmetic. VCR first subtracts mathematical target-byte addresses and divides
by the Clang target `sizeof(T)`. Passivization asserts non-null/live bases,
one origin, in-range element positions, and target-`ptrdiff_t`
representability before normalizing recoverable same-base indices to machine
subtraction. A `VValidExtent` supplies the closed `[0, n]` position range for
an abstract array; absent that extent, direct abstract and represented
scalar-dynamic bases retain only positions `0` and `1`. Without concrete
provenance, origin equality requires the exact same SSA base; numeric pointer
equality is deliberately insufficient because equal addresses need not share
C++ object provenance. Explicit specs and lifted `constexpr` functions still
reject pointer difference.

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
Layer 4 encodes that same in-memory module. The layer mask is parsed by
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
