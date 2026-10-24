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
│ - cvc5: SMT-LIB2 process │
│ - portfolio, race: both  │
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
- All `RevealWithFuelStmt`, `HideSpecStmt`, and `RevealSpecStmt` nodes
- All `cppverify::spec` / `cppverify::proof` function declarations (gated in CodeGenModule)
- All contract clauses (pre/post/modifies/aliases/invariant/decreases/recommends/type_invariant)

Result: standard binary with zero overhead from contracts.

## Layer 1: VCR IR (Verified C Representation)

Purpose: clean, typed, control-flow-preserving representation of the verified program. 1:1 with a subset of the Clang AST but stripped of C++-specific noise (declaration contexts, template sugar). **Implicit type conversions are preserved as explicit Cast nodes** — not stripped — so the Z3 encoder can decide whether to emit `sign_extend`/`zero_extend` (BitVec mode) or silently ignore them (mathematical integer mode).

### Type Propagation from Clang

Every `VExpr` carries a `VType` populated automatically from canonical Clang
`QualType` data during `ASTConverter`; users never re-annotate contract terms.
`VType::fromQualType` recognizes booleans, void, pointers/references, integral
and enum widths/signedness, and two aggregate markers: `Struct` for a record
and `Array` for a constant array (with its element count and stride). Record
fields are flattened by the converter where supported, and fixed local arrays
are supported as automatic objects; other arrays fail closed.

### Types (VType)

```
VIntMode = Math | Machine

VType =
  | Bool
  | Int32(IntMode, bitWidth, isSigned)
  | Int64(IntMode, bitWidth, isSigned)
  | Struct
  | Array(count, strideBytes)                // constant-array marker
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
  - In `cppverify::spec` function bodies → `Math` (Z3 `Int`)
  - In `cppverify::proof`/`exec`/lifted-`constexpr` function bodies → `Machine` (Z3 `BitVec(N)` or range-checked `Int`, per `--int-encoding`)
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
  | Load(ptr: VExpr, type, accessCondition?)     // *p in an expression context
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

**Places inside objects:** a field or fixed-array element inside an object is
a `VPlace`: the object's address plus Clang's layout offset for each field and
`index * stride` for each element, at any depth, with an access condition,
the conjunction of `0 <= index < count` over the fixed-array indices of the
path. A `Load` or `Store` of the place carries the condition, and
passivization asserts it, kind `bounds`, where the access is evaluated. The
object is a promoted local (`ASTConverter::objectPlace` on its allocation) or
the object a pointer addresses: `pointeeRootPointer` walks the place down to
`p->`, `(*p).`, or `p[k].`, and `pointeePlace` takes that pointer as the base,
whose own access UB instrumentation checks against the pointer's extent or
object as before. `p->buf[i]` therefore has both checks, and the array's is
what rejects `p->buf[8]`, the address of the next field.

**Pointers into objects:** `ASTConverter::subobjectPointer` lowers a decayed
member array of a pointee and the address of a pointee's element, field, or
nested record. In a statement (`SubobjectSink`) it asserts the place's access
condition and its accessibility (`appendReferenceBindingCheck`) and binds the
address to a fresh pointer `__subobject_N` with two companions,
`__subobject_N.__lo` and `.__hi`, the bytes of the array it comes from or
else of the field or record; elsewhere, as in a condition or a contract, it
is the address alone. `VFunction::BoundedPointers` names the pointers with
companions. `propagateSubobjectBounds` (`Transform/SubobjectBounds.cpp`) runs
on the converted body: every pointer variable assigned a value rooted at a
bounded pointer (through steps, casts, and conditionals, `pointerBound`) is
bounded too; before each such assignment its companions take the value's
bounds (a root without bounds may address any byte, `[0, 2^64)`), a step
keeps them, every bounded variable starts with any byte at entry, and a loop
that moves one gets the generated invariant `q == 0 || q.__lo == 0 ||
q % S == q.__lo % S`. Storing a bounded value in memory or returning it is a
conversion error. UB instrumentation (`subobjectObligation`, `sameSubobject`)
adds `lo <= addr < hi` at each access, `lo <= p <= hi` at each step, and each
operand in the other's closed bounds at a pointer difference; a call asserts
that the bytes a callee's extent or object takes from a bounded argument lie
in its bounds. Origins treat the companions as no pointers, and a constant of
pointer type in a sum of two pointers is the field offset
(`steppedPointer`). Pointer-difference positions measure an origin's object
in its own elements (`PassivizerImpl::OriginObjects`), since a pointer into a
member has a smaller type than its origin.

**Quantifiers, triggers, choices, collections:** a quantifier without bounds
ranges over all mathematical integers. A `cppverify::trigger(term)` mark is an identity
`Cast` flagged `IsTrigger` around the term. Each `cppverify::choose` is lifted to a
synthesized uninterpreted spec function (`IsChoice`) of the values its body
mentions, whose postcondition is the Hilbert axiom `!cppverify::exists(k, P) || P(cppverify::result)`
(with the range for a bounded choose). Chooses with the same condition, compared
by a structural key of its range and body that names bound variables by
position, are lifted once (as Verus's `choose_map` shares closure functions), so
they are one function. The calls in its body are calls of the
function it is written in, for recursion and termination. A collection
operation is a `SpecCall` whose identity is `__cppverify.<op>`, such as
`__cppverify.seq.push`.
`cppverify::valid(p, n)` becomes a call of the synthesized builtin spec
`__cppverify_valid(p, n)` (body `true`, marked `IsBuiltin` and never
reported), so the extent marker scan treats it exactly like a user-declared
`valid`. A function that applies either anywhere but as a top-level condition
of a precondition, where it would mean `true`, is rejected under `--check-ub`
(`misplacedValidMarker`, `Transform/UBChecks.cpp`).

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
  | Store(ptr: VExpr, value: VExpr, accessCondition?)     // *p = value
  | Allocate(target, allocatedType, init?, sizeBytes, alignBytes)
  | Free(ptr: VExpr)
  | If(cond: VExpr, then: [VStmt], else: [VStmt])
  | While(cond: VExpr, invariants: [VExpr], decreases: VExpr?, modifies: [VFootprint], body: [VStmt])
  | Assert(expr: VExpr)
  | Assume(expr: VExpr)
  | Return(value: VExpr?)
  | GhostBlock(body: [VStmt])
  | RevealWithFuel(fn: spec name, fuel: unsigned)
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
- `cppverify::aliases` empty means the implicit non-aliasing precondition applies to every pair of distinct pointer/reference parameters of which at least one is mutable.
- A `VFootprint` is a target lvalue with an optional element count and
  element size: a cell (`p[i]`, `p->f`, a reference), a range `p[lo : n]`
  (target `p[lo]`, count `n`), or a region `*p` (the object `p` addresses).
- Behaviors are desugared in the frontend: each scoped `cppverify::pre` becomes
  `!assumes || pre`, each scoped `cppverify::post` `!old(assumes) || post`, and
  `cppverify::complete_behaviors`/`cppverify::disjoint_behaviors` become assertions at body entry.
- `cppverify::check(c) by { proof }` is desugared to
  `Assign(k, false); Havoc(k); if (k) { proof; assert c; assume false }
  assume c`; `cppverify::calc` to nested assert-by steps. When `c` is
  `cppverify::forall(x, lo, hi, P)`, the parser puts `x` in scope for the block, and the
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
write set: its explicit `cppverify::modifies` footprints, read in each iteration's state
(ACSL `loop assigns`), else the objects its stores and calls reach: the entry
objects of their pointers' origins (below). With a function `cppverify::modifies` too,
both frames are assumed, so only cells inside both may change; when an
origin is unknown the function's frame alone bounds the loop, since every
store is checked against it. When every written region is a single cell the
frame is a chain of stores of fresh values; otherwise it is a
`HeapFrame(mem_entry, mem_head, regions)` relation.
An explicit loop `cppverify::modifies` is also asserted at the end of each iteration and
at each `continue` (obligation kind `frame`, located at the footprint).

**Termination.** An executable loop without `cppverify::decreases` contributes no
measure obligation, and the driver reports the function `Unresolved` with
`decreases.missing` unless BMC proved the unwinding or the loop's condition is
the constant false, so that it never repeats: the converter gives such a loop
(`while (false)`, the `do { ... } while (0)` of a macro) the condition
`false`, and its havoc keeps every value. `cppverify::decreases(*)` marks the
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

**Enumeration ranges.** A machine value of an enumeration type without a
fixed underlying type (`VType::EnumMin`, `EnumMax`) lies in its range, since
a conversion into it is asserted. Each expression's definedness checks are
followed by an assumption of facts about the values it reads
(`machineMathBridgeForExpr`), under the expression's guards and quantifiers;
it includes the range of every enumeration variable and memory read, which
covers parameters, call results, loop heads, and the heap after a havoc.
Mathematical values (specs, and the proofs generated from them) convert
without a check and get no range.

**Assertions → assert, then assume:** `cppverify::check(P)` is proved where it
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
  the callee must lie inside the caller's own frame, by its cells
  (`footprintWithin`): a region of one scalar object is one cell, and a
  footprint through a pointer of another base than a caller region's lies in
  it where its cells lie in the region parameter's entry object, the rule a
  store already follows.
- If `cppverify::modifies` is the conservative default (all reachable through mut params), the entire heap is havocked.
- A `freshOwnedReturn` call is not a whole-heap havoc. It preserves every old
  cell, materializes one disjoint initialized scalar object, then assumes the
  ordinary postconditions against that new heap.

**Contract well-formedness.** Every contract clause must be defined where it is
evaluated, as Dafny's per-method `CheckWellFormed$$f` procedure requires. Its
definedness checks are the core ones (`collectSafety`) and, under
`--check-ub`, the memory checks of the clause as written: `instrumentUBChecks`
records them before spec inlining, as it checks the body's accesses, beside
each written precondition and postcondition (`VFunction::PreconditionChecks`,
`PostconditionChecks`), each loop invariant (`VWhileStmt::InvariantChecks`),
and each `cppverify::check` (`VContractAssertStmt::MemoryChecks`). A read under
`old` is checked in the entry state, a quantifier's body at every value of
its range, and in a pre- or postcondition every parameter is its entry value.
Checking the inlined clause instead would check a spec's own reads, though a
spec is total, and repeat a lifted helper's argument reads for every use in
its body. Cloning and loop unrolling copy the records; passivization joins
each clause's memory checks to its core checks, one obligation per kind.

`Passivizer::contract` builds a separate passive program, `f.contract`
(identity `f::contract`), on the interface version of `f` (UB-instrumented,
not spec-inlined: the one call sites use), so a lifted helper's checks are
reported at its call. `enter` assumes only the generated preconditions
(validity, separation, type invariants) and the entry facts; each written
precondition then gets its definedness asserts and is assumed, in order, so
each clause is checked where the ones before it hold. For an external
contract (trusted, or without a definition, `IsExternalContract`)
`returnAnywhere` makes the state callers assume: `havocFootprints`, the frame
code `emitCallStmt` uses, over its own footprints, and a fresh result. The
generated result validity is assumed, and each written postcondition is
checked and assumed in turn. The postconditions of a verified body are
checked in `run()` instead, in its final state, each clause's checks guarded
by the clauses before it. Loop invariants and `cppverify::check` get their
memory checks where they are checked.

## Layer 3: Canonical Obligation IR

`buildObligationModule` is the only passive-to-logic lowering path. It folds the
ordered `PassiveProgram` once and publishes:

- typed `LogicExpr` terms, whose subterms are shared (below), with explicit
  `Bool`, mathematical integer,
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
  conditional, quantifier, and `cppverify::old` guards, so the conjunction is unchanged;
- owned logical-function declarations, typed signatures, compact one-step
  definitions, and exact finite definition levels for the caller's fuel;
- the logical features required by the module for capability validation.

Construction returns `llvm::Expected`. A null, unhandled, malformed, or
untyped term prevents publication of the module and is reported as `unknown`;
it is never replaced by `true`.

**Shared subterms.** A term owns its root and shares its subterms: the
children and patterns of a `LogicExpr` are `LogicExprRef`s
(`llvm::IntrusiveRefCntPtr<const LogicExpr>`, the count in the node), and no
code changes a node once it is a subterm, which the type enforces. A copy
(`cloneLogicExpr`) copies the root's fields and shares its children. So each
obligation's goal states every assumption before it, its query negates the
goal, and the complete goal conjoins the goals, all without copying them, as
Verus's AIR shares `Arc<ExprX>`, Frama-C's Qed hash-conses its terms, and
Lean shares `Expr`. A change below a root rebuilds only the path to it. The
simplifier is copy-on-write and memoizes each subterm per module, so a
subterm that many goals share is simplified once and stays shared; a reuse
adds the rewrites its first simplification counted, so the reported
statistics are those of the tree. The certifier's substitution, renaming,
and witness analysis rewrite children the same way (`rewriteSlots`), copying
a node only when a child changes. The one field written after a term is
shared is a node's `Source`, a function of its `Loc` alone: annotation visits
each node once and writes only a value that differs, so it never writes a
node that an earlier, annotated module shares, which other threads may be
reading. The caches keyed by a node's address hold what depends on the node
alone, so sharing cannot make them answer for another place: the Z3
encoding (a variable is encoded by its name, and the traversal keeps no
scope), the certifier's cost estimate, and the Lean printer's `let`s, which
name a shared subterm of a statement once. Every hash, archive, and Layer 3
and 4 dump is what it was with copies (checked on every Verify source), and
the Lean exports state definitionally equal goals.

Before 0.2 every copy copied the whole term. Each obligation's goal repeated
its assumptions, and its query, the complete goal, and the complete query
repeated those, so memory grew with the number of obligations times what
came before them: lowering the ULEB128 case study took 12.8 GB of address
space and 53 s, verifying it 14.9 GB with eight jobs (`--jobs=8`, more than
a 16 GB CI runner holds beside the tests running with it), and lowering
`safe_fib.cpp` 4.7 GB and 16 s. They now take 0.43 GB and 10 s, 0.9 GB, and
0.35 GB and 7 s. The goals still repeat their assumptions as trees, so a
traversal that does not memoize (validation, hashing, serialization) still
takes time quadratic in a function's length; hash-consing the terms and
memoizing those traversals would make it linear.

Every source-built or replayed module then passes through one fail-closed
canonicalization step before hashing or backend dispatch. The pass folds only
sort-preserving Boolean constants, double negation, constant conditionals, and
reflexive equality/inequality. It simplifies owned finite-fuel definitions and
removes logical declarations unreachable transitively from every ordered
obligation, a declaration reaching what its definition and its termination
measures apply. It then rebuilds each exact counterexample negation, the complete
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
- A logical function marked `Choice` is a lifted `cppverify::choose`: uninterpreted,
  with the Hilbert axiom as its postcondition. `SpecAxioms` lowers the
  postconditions of a function without a definition, its axioms, into every
  module that applies it, and fails the module when one does not lower.
  Passivization assumes the axiom at every application of a choice in a
  fact as well, an unfolding, a postcondition, or an induction hypothesis
  (`addChoiceAxioms`), quantified like the application and read in its
  memory. The certifier reads a choice's value from the model and, after
  the evaluation, checks the axiom at every value read, including those the
  checks read (`Evaluator::checkChoices`): a value the axiom excludes is no
  evidence, but a dispute whose refinement gives the solver the axiom
  there, and a value it cannot decide leaves the counterexample unchecked.
  Before, the certifier took the model's choices on trust, and a model that
  broke the axiom of a choice applied only inside an unfolding certified
  false counterexamples. A claim true only for some choices still fails
  certified, with choices the axioms allow.
  A choice is a function of the values its condition reads, so the same
  choice in two memories is one value where those values agree: for each
  application of a choice that reads memory and each step back from its
  memory, `addFrameInstances` assumes `agree -> c(after) == c(before)`, where
  `agree` (`choiceReadsAgree`) says that every load of the condition, at
  every binder value where it is evaluated and with its address read in
  each memory, and every application in it that reads memory, has the same
  value on both sides. The certifier holds a model to the same rule: two
  values of one choice with the same other arguments are evidence only when
  some value the condition reads differs between the memories
  (`readsApart`, a formula that follows the condition's evaluation order),
  and otherwise the counterexample is unchecked.
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
`cppverify.obligation/3` records after source attribution. The binary format has
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
treats a choice as an ordinary uninterpreted function. A logical function's
`Decreases` follow its definition levels, and with source metadata the
`Premise` of each `Or` follows its source point; neither is hashed. A
measure is validated like a definition (an integer over the parameters,
every call resolved): it changes no meaning, since Lean proves a
definition's termination itself and an induction descends by a
well-founded relation whatever the measure, and canonicalization keeps the
functions a measure applies, so a module never names one it does not
declare. Before, a spec only a measure applied was removed, and the
measure could not be printed.

Schema v2 adds the precise obligation kinds, and schema v3 the measures and
premises; readers still read schema v2 and schema v1, whose records name
only assertions, postconditions, and unwinding checks. Records
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
or public source-anchored obligation IDs, measures, premises, and every
obligation kind except `unwinding` (the only kind that changes result
semantics), so moving identical
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
cpp-verify --obligation-in=goals.cpv --lean-project=proof --lean-certify
```

Replay treats decoded records as untrusted input: validation happens before
canonicalization, and the canonicalized module is revalidated before it can
reach any adapter. Semantically equivalent records that differ only by
supported constant structure or unreachable logical declarations therefore
converge to the same backend module and semantic identity.

Replay settles each module alone. What a source verdict also rests on (callee
and trusted contracts, spec facts, partiality) and the vacuity checks are not
archived, so a module whose obligations all hold reports `Proved obligations:
f (dependencies not checked in replay)` (JSON status `proved-obligations`),
never `Verified`. A counterexample is still a failure: postconditions are not
archived either, so replay certifies it by the definitions alone.

With `--lean-project`, `replayLeanProject` (`Verifier.h`) exports every
module through the project adapter and drives the same `LeanProject` a
source run does: the modules and the spec trial, regeneration with moves
and quarantine, automation, and with `--lean-certify` certification. The
goals have the names, files, and proofs the same obligations have from
source (both name a goal by its statement), and `Specs.lean` the same
definitions, since the measures are archived; a readable goal names the
same hypotheses, since the premises are. A module whose goals all certify
is `Verified` there, printed `Proved obligations ... [backend=lean]`, never
`Certified`, which claims the dependency fixpoint.

BMC-produced modules retain the unroll bound as semantic transform provenance.
Replay aggregates those modules with BMC unwinding semantics even when Z3 is
the selected solver, so an exhausted frontier remains `BoundedSafe(N)` rather
than becoming an ordinary program failure or an unbounded proof. Applying BMC
to an untransformed archive is rejected because loop unrolling must precede
obligation construction. Lean exports a bounded module, to the scratch-pad
or a project, with its bound stated over its goals (`/- bound: N loop
iterations, by unrolling: ... -/`), and `LeanProjectGoal::Unwinding` marks
its unwinding goals: every goal certified is `Verified` (`Proved
obligations`, `bound=N`), every goal but some unwinding goal certified is
`BoundedSafe` (`bmc.incomplete-bound`), else `Unresolved`. Lean proves and
never refutes, so its `BoundedSafe` says that the unwinding goals are not
certified, where BMC's says that they fail; both claim what the safety
goals state, no failure in an execution within the bound, and reporting
the unproved unwinding unresolved would leave Lean no bounded verdict for
a module whose unwinding fails, the case BMC is for.
Failure-triggered `cppverify::recommends` diagnostics are excluded from archives, keeping
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
| Forall(x, lo, hi, P) | `(forall ((x Int)) (=> (and (<= lo x) (< x hi)) P))`; marked triggers become `:pattern`, and otherwise Z3 chooses the patterns |
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
Without them, `cppverify::forall(k, 0, n, p[k] >= 0)` did not prove `p[2] >= 0` on Z3
or even `p[0] >= 0` on cvc5.

**Extensionality.** A sequence equality the query refutes (an `a == b` it
asserts the negation of, or an asserted `a != b`, with no bound variable)
is joined with its extensionality instance before Z3 encoding
(`instantiateExtensionality`): `a == b` becomes `a == b || (len(a) ==
len(b) && forall k in [0, len(a)). a[k] == b[k])`. The two are equivalent,
and the quantifier occurs negatively, so the solver introduces one witness
index rather than instantiating it. Z3 then proves an equality from equal
elements, as Verus's `=~=` and Dafny's sequence equality do, and a stated
`cppverify::check(a == b)` works as a hint. Equalities the query assumes, such
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
applications of the opaque logical function, and `cppverify::reveal_with_fuel` controls
the exact finite depth. An application's arguments take the integer mode of
the callee's parameters (mathematical for an explicit spec), not that of its
result: with the result's mode, a `bool` spec's argument `a + 1` was reduced
to 32 bits, which proved `!above(a + 1)` for `a == 2147483647` and refuted
`above(a + 1)` with a false counterexample. Adapters never borrow `VFunction`
metadata.

**Heap-reading specs:** a spec that reads memory, directly or through another
spec, becomes a logical function with a leading `__spec_heap` parameter of sort
`Heap`; its definitions read through that parameter, and a value read is the
exact value of the machine cell, as the spec's integers are mathematical
(a `bitvector32` sum of two reads wrapped before). Each call site passes the
heap version passivization resolves for it, exactly as for a load, and
modules containing such functions require the `heap-functions` logic feature.
A spec with `cppverify::reads(p, n)` clauses is checked in its own module (`spec reads:`,
the spec and its recursion cycle opaque): every load address under its path
guard, and every range a heap-reading callee reads, lies in the declared
ranges. Since the spec then depends only on those cells (by induction on its
terminating definition), passivization adds, for each application `f(H', a)`
and each store `H' = store(H, q, v)` reached backwards through the heap
versions, the assumption `q outside R(a) -> f(H', a) == f(H, a)` under the
store's guard. The driver demotes a proof that relies on a spec whose reads
check did not pass to `Unresolved` with reason `spec.reads`.

**Spec postconditions and domains:** a spec's `cppverify::post` is checked in its
termination module (its own module `spec post:` when it is not recursive):
each call within the recursion cycle contributes the assumption
`dec(a) < dec(x) -> post(a, f(a))` under the cycle's well-founded relation,
each call of another spec its post (a choose its axiom only where the calls
of the cycle in its body lower the measure), and every return value must
satisfy the post. Since the facts at lower measures are the induction hypothesis, a
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
receives. `cppverify::when(c)` is desugared in the frontend: the body
becomes `if (c) body else return f.unspecified(params)`, where
`f.unspecified` is a logical function without a definition (Z3 and cvc5
declare it; the certifier cannot evaluate it, so a counterexample that needs
its value is `counterexample.unchecked`), and each post becomes `!c || post`.

**Inductive predicates:** `cppverify::inductive` on a spec returning `bool` sets
`VFunction::InductiveLoc`. After conversion, `expandInductivePredicates`
(`Transform/Inductive.cpp`) turns each body into one condition `F` (returns
under `if`/`else`), groups predicates that apply each other (strongly
connected components), checks that the members occur in each body only
positively and continuously (conjuncts, disjuncts, `?:` branches, `cppverify::exists`,
bounded `cppverify::forall`; never under negation, in a comparison, conversion,
condition, argument, quantifier bound, or unbounded `cppverify::forall`), and generates
for each member the recursive spec `P.step(h, x)` (`InductiveStepOf`,
`cppverify::decreases(h)`, mathematical `h`) with body `h > 0 && F[Q(a) := Q.step(h -
1, a)]` for every member `Q`. `P`'s body becomes `cppverify::exists(h, P.step(h, x))`,
its true definition, and `F` is kept as `VFunction::Unfolding`. `P` is
hidden in every function that does not `cppverify::reveal` it, and
`specApplicationFacts` assumes `P(t) == F[t]` beside its postconditions at
each application, in function bodies (`addSpecPostInstances`) and in spec
checks (`addSpecPostChecks`). The unfolding reads memory at the
application's heap version, and the facts of an application are keyed by
callee, arguments, and heap version, so the same application before and
after a store has facts of its own. The applications inside an unfolding
get none at depth one, so each named application unfolds once; at depth
`d` the applications of inductive predicates inside the unfoldings of
level `l < d` get theirs too (`Passivizer::setUnfoldingDepth`, and per
predicate `cppverify::reveal_with_fuel(P, d)`, which keeps `P` hidden). A predicate
reached again through a spec outside its group is rejected, since its
occurrences there escape the positivity check.

The driver deepens automatically, as Stainless unrolls: a function verdict
`Unresolved` with `spec.fuel`, `spec.hidden`, or
`counterexample.unchecked` whose module assumed unfoldings is passivized
again at depth 2, 3, and 4 (`MaxUnfoldingDepth`), skipping depths that
`cppverify::reveal_with_fuel` already reached; the first `Verified` or `Failed`
verdict replaces it, and its module replaces the archived one. Every level
adds only proved unfoldings, so a proof stays sound and a counterexample is
still certified against the true definitions. It does not deepen a verdict
marked `VerifyResult::InductionOnly`: the goal needs a predicate false where
its derivations go round forever, and every fixpoint, the greatest
included, keeps every unfolding; or checking it needs a value too deep to
evaluate (no derivation among the heights tried, and no finite fixpoint),
which four more levels cannot change. A deeper attempt that finds the
first of these replaces the reason and ends the search. Unfoldings under an unbounded binder (the
`cppverify::exists` of `reach`) are quantified facts, which help proofs but can keep
the solver from finding a model, so after `cppverify::reveal_with_fuel` an unresolved
verdict is also tried at depth one without the fuel.

Unfolding nests a body inside itself, so every substitution under a binder
renames the binder apart when a substituted value mentions its name
(`substParamsInExpr`, the spec inliner, and the certifier's own unfolding):
the second level of `reach` once read `edge(c, c)` for `edge(c, c')`, which
stated `reach(c, b) == (c == b || reach(0, b))` and proved a false claim.

The equation is a theorem only of this construction, so it is proved per
predicate by three generated proof functions (`InductiveRuleOf`), in
mathematical integers, with every member revealed:

- `P (monotonicity)`, `P::monotone(h, j, x)`: `cppverify::pre(P.step(h, x) && h <= j)`,
  `cppverify::post(P.step(j, x))`, `cppverify::decreases(h)`. For `h > 0` it states the induction
  hypothesis for each member `Q` that `F` applies, `forall y. Q.step(h - 1,
  y) -> Q.step(j - 1, y)`, by generalization: a fresh `y` is havocked in a
  branch that calls `Q::monotone(h - 1, j - 1, y)`, asserts the instance, and
  ends in `assume false`; the universal is assumed after it. Bounded
  universals in `F` are carried from `h - 1` to `j - 1` the same way, and an
  existential above one is fixed at a chosen witness (`P::transportN`).
- `P (case analysis)`, `P::inversion(x)`: `cppverify::pre(P(x))`, `cppverify::post(F)`. It names
  the height `P.height(x)`, a Hilbert choice (`IsChoice`) with axiom
  `!cppverify::exists(h, P.step(h, x)) || P.step(cppverify::result, x)`, asserts `P.step` there,
  proves `forall y. Q.step(H - 1, y) -> Q(y)` by generalization, and
  transports `F`.
- `P (introduction)`, `P::introduction(x)`: `cppverify::pre(F)`, `cppverify::post(P(x))`. The
  bound `B` is the height of `F`, clamped at zero: `Q.height(a)` for an
  application, the larger of two parts, the height at the chosen witness
  (`P::witnessN`) for an existential, and for a bounded universal the
  generated spec `P::boundN(lo, hi, v)` = `lo >= hi ? 0 : max(height[w :=
  lo], bound(lo + 1, hi, v))`, `cppverify::decreases(hi - lo)`, whose postcondition
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

A postcondition `!cppverify::result || Q` is copied to `P.step` and proved by
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

**Proof blocks of spec clauses:** `cppverify::post(...) by { ... }`, and the same
after `cppverify::decreases` and `cppverify::reads`, on a spec definition. The parser caches the
block's tokens (`PendingClauseProofs`) and parses each, once
`ActOnStartOfFunctionDef` has put the parameters in scope, as a compound
statement before the body (`cppverify::post` blocks with `cppverify::result` enabled), into
`FunctionContractInfo::ClauseProofs`; a block on another clause, on a
non-spec, or on a declaration is an error. The converter lowers it as ghost
code in the spec's mathematical mode into `VFunction::ClauseProofs`, so the
ghost rules apply (no return, store, or assignment but to its own locals).
An inductive predicate's `cppverify::post` and `cppverify::reads` blocks move to its step.
`withClauseProofs` (`Transform/SpecInline.cpp`) turns a check with blocks
into one generated proof function, `TotalExpressions`, with the spec's
parameters and visibility: the check's assumptions as `assume` statements,
the blocks, then the check's obligations as `assert` statements of their
kinds (an `unsupported` obligation is kept as it is), passivized normally,
with the spec, its cycle, and its group's predicates in `FactsWithheld`.
In a `cppverify::post` block, `cppverify::result` is replaced by the body's value (its returns as
nested conditionals); each application of the spec's recursion cycle in
the passivized program assumes the callee's postcondition under the
measure's decrease (the induction hypothesis at the block's arguments).
The driver applies it to the post module (`cppverify::post` blocks), the termination
module (`cppverify::decreases` and, unless a step's bare check, `cppverify::post` blocks), a
step's induction module (`cppverify::post`), and the reads module (`cppverify::reads`), and
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
and `P(v)` is evaluated by its definition, `cppverify::exists(h, P.step(h, v))`, which
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

**`cppverify::recommends`:** parsed and stored; not emitted into the main VC. On
verification failure, a second pass adds `cppverify::recommends` checks and reports
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
fuel and `cppverify::hide` only decide which unfoldings a solver receives.

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
postcondition `!cppverify::result || Q`, since only induction shows it. An unfolding
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
that holds under the definitions pins the search to that counterexample. The
probe has half the slice left, and its time moves the slice's end, so
refinement keeps the rest. Its searches, one for each end of each argument,
take turns, each check with an equal share of the time left, and each doubles
its distance while the solver finds a value beyond and then halves the gap
below the first distance it cannot reach (`ExtremeSearch`), so a 32-bit end
takes at most 65 checks. Before, the ends ran one after the other and each
restarted at distance 1 after every overshoot, hundreds of checks for a 32-bit
end: on the efficiency cores of an M1 the first end spent the budget, and
`fibo_strict` (`spec_post_unfolded.cpp`), whose counterexample lies at the
other end, ended `spec.fuel` in 20 of 20 runs. A probe bounded only by its
checks and the query's deadline instead spent 72 s on `count_reverse`
(`sequence_induction.cpp`), one check taking 39 s, and its direct proof gave
way to an induction ten times slower; Z3's resource limit does not bound
those checks.

A race interrupts the losing encoder's context, possibly while its
certifier reads a model; Z3 then evaluates a term to nothing. Every model
evaluation goes through `Z3Encoder::evaluated`, which reads an empty result
as an opaque constant (undetermined), and a certification made by an
encoder that was stopped is discarded (`Z3Encoder::certify`). Before this,
about one run in six over sequences crashed on the empty term.

The verifier is built without exceptions, so a failed Z3 call returns a
null term and records an error code that the next call clears. Each encoder
therefore installs an error handler on its context that keeps the first
error and marks the encoding failed, and `verifyModule` and `lowerModule`
end a query in which a call failed as `Unresolved [encoding.failed]` with
Z3's message, whatever the result was. Errors inside a check do not count
(Z3 reports them as the check's `unknown`), nor do those of a stopped
encoder.

Z3 gives refinement a short slice of the query budget (5%, at least half a
second) and at most eight rounds that only search among hidden values. A model
whose applications are too deep to evaluate is followed by a search for one
whose arguments to them lie within 4096 of zero. Checking a model has a budget
of its own (`--certify-timeout`), so the time a check takes moves the slice's
end, and that search keeps its time. Before, one check of an application such
as `fibo` at a billion could spend the slice, leaving a false claim
`spec.fuel` on a loaded machine. It
then solves the query again with whole definitions in the remaining time and
certifies any model it returns: a non-recursive function is replaced by its
definition and a recursive one becomes a native recursive definition
(`z3::context::recdef`) when its recursion is guarded: `&&` and `||` over a
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
lifted `cppverify::choose` is read from the model and checked against its axiom
(see `Choice` above).

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
over some variables: the `cppverify::decreases` of a recursive spec applied in the claim
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
query whose `Failed` result shows it can hold), instantiates the theorems of
the established proof functions where their conclusions' spec applications
match the query's (a machine parameter seen as `bv_to_int(p)` matches an
integer term `t` with `p := int_to_bv(t)`), and asks the same
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

A proof function's theorem is what its verification proves, built by the
same lowering as its module. Passivization records its postconditions as
asserted (`PassiveProgram::ContractConclusions`) and the variables of its
entry state (`EntryVariables`); Layer 3 lowers them with every entry
assumption (`ObligationModule::Contract`: `Premises`, which hold the
preconditions with the generated ones, such as pointer validity in the
memory model's own terms, extents, separation, and type invariants injected
where the body reads a field, and the facts about null at entry;
`Conclusions`). It is published only when every variable it mentions belongs
to the entry state, so it is a theorem on its own, and the driver keeps it
for a verified proof function (`FunctionRun::Contract`). Before, the
confirmation lowered a lemma's declared clauses from source: `valid(p, n)`
became `true` and `initialized_ptr` `false`, so pointer lemmas were left out.
An instance renames the theorem's variables apart, binds those a match
fixes, and quantifies the other integer, machine, pointer, and Boolean ones
over the integers (`int_to_bv(k)`, `0 + k`, `k != 0`), adding the instance
at zero as a witness the solver need not find (cvc5 did not find the
two-pointer one). A premise that constrains only unbound memory, which
nothing else mentions, is dropped once the certifier evaluates it true with
memory of zeros: the theorem then holds without it. Other unbound memory is
the module's variable of the same name, its entry state. Every value gives
an instance of a theorem, so none of these choices can make a confirmation
unsound; they decide only where the module's facts can meet the premises.
The tests `depth_below_zero` and `total_of_negatives` are true claims that a
lemma used without such a premise would refute: they stay unresolved.

## Lean Encoding

The Lean adapter (`Backend/LeanBackend.cpp`) prints the canonical module as
Lean 4 propositions that mean what the module means, so a kernel-checked
proof of a printed goal is a proof of its obligation.

| Logic sort | Lean type |
|---|---|
| `Bool` | `Prop` |
| `MathematicalInteger`, `Pointer` | `Int` |
| `BitVector(N)` | `BitVec N` |
| `Heap` | `CppHeap` (`Int -> Int`) |
| `Seq` | `List Int` |
| `Set` | `Int → Bool`, its membership test |
| `Multiset` | `Int → Nat`, its counts |
| `Map` | `Int → Option Int`, the value at each key it holds |

- **Precedence.** Each operator is printed at its Lean notation level
  (`Init/Notation.lean`, `Init/Core.lean`), and an operand that binds looser
  than its position is parenthesized: `↔` 20, `→` 25, `∨` 30 and `∧` 35
  (right-associative), `¬` 40, comparisons 50, `|||` 55, `^^^` 58, `&&&`
  60, `+` and `-` 65, `*` 70, `<<<` and `>>>` 75 (left-associative), and a
  function argument an atom. A quantifier or `if` extends as far right as it
  can, so it is parenthesized everywhere but at the top of its context.
  Before 0.2 the adapter used a table of its own: `(a ^ b) + 1` printed as
  `a_0 ^^^ b_0 + 1`, which Lean reads as `a ^^^ (b + 1)`, and a Lean proof
  certified a false check; a quantifier took the rest of the goal into its
  body.
- **Numerals** have their types: `(3 : Int)` for a mathematical integer or
  a pointer, `(BitVec.ofInt 32 (3))` for a machine value. Lean elaborates a
  term of untyped numerals in `Nat`, where `2 - 3` is 0: before 0.2 a Lean
  proof certified `cppverify::check(2 - 3 == 0)`.
- **Booleans** are propositions: equality is `↔` and inequality `¬(a ↔ b)`,
  the form `simp` normalizes an equality of propositions to (`eq_iff_iff`),
  which a proof can use without `propext`.
- **Division.** Machine division is SMT-LIB's, as in the solvers and the
  certifier: `BitVec.smtUDiv` (all ones at a zero divisor) and
  `BitVec.smtSDiv` (`-1` or `1` by the dividend's sign); Lean's `udiv` and
  `sdiv` give 0 there. The remainders `BitVec.umod` and `BitVec.srem` agree
  with SMT-LIB. Mathematical division and remainder are the prelude's
  `cppIntDiv` and `cppIntRem`: truncating, with quotient 0 and remainder the
  dividend at a zero divisor.
- **Shifts.** A left shift is `x <<< min (s).toNat N`, which has the value of
  `x <<< (s).toNat`: Lean's evaluator computes `2^amount` and panics on a
  64-bit amount. A signed right shift is the application
  `(BitVec.sshiftRight x (s).toNat)`.
- **Definition instances.** A goal's hypotheses state the definition levels
  of each spec application it makes, as the solvers receive them. One under
  quantifiers is stated for every value of the binders it mentions,
  `∀ (k : Int), f k = body k`, a theorem since the definition holds at every
  argument; before 0.2 it named the binder outside its quantifier, and the
  export did not build.
- **Evaluation.** The prelude's comparison wrappers (`cppBvUlt`, `cppBvUle`,
  `cppBvSlt`, `cppBvSle`) and `heapSelectBool` are `abbrev`s, so instance
  search sees the Boolean comparison beneath them and `decide` evaluates them
  at constants; as `def`s they had no `Decidable` instance outside the
  generated file. Its `local instance` of `Classical.propDecidable` serves
  only the `if`s of generated definitions whose condition has no decision
  procedure; Lean's instance search already tries a specific instance before
  it.
- **Collections.** Each operation is a prelude function
  (`LeanCollectionPrelude`), `cppSeqAt`, `cppSetInsert`, `cppMapGet`, ..., with
  the total meaning of `<cppverify.h>`: a read outside a sequence or a map's
  domain is 0, a subrange clamps `lo` into `[0, len]` and `hi` into
  `[lo', len]`, a multiset removal of a count of 0 leaves 0 (`Nat`
  subtraction). A set is its membership test rather than a finite set, since
  a set may be infinite (Vermilion's mirror of vstd uses Mathlib's `Finset`,
  for finite sets only). The three membership predicates are `def`s with
  `Decidable` instances, not `abbrev`s: as `abbrev`s, the Boolean lemmas of
  `cppverify_norm` rewrote `cppSetContains s x` to `s x = true`, and the
  lemmas stated on `cppSetContains` no longer matched. As Vermilion states
  its vstd operations, the prelude states each operation's meaning in
  `@[simp, grind =]` lemmas (`cppSeqAt_push`, `cppSetContains_remove`,
  `cppMultisetCount_remove`, ...), with `grind_pattern`s for the facts that
  lengths and counts are not negative (grind's own pattern for `0 ≤ count m
  x` is the inequality, which no goal contains), and extensionality lemmas
  (`cppSeq_ext`, `cppSet_ext`, `cppMultiset_ext`, `cppMap_ext`); all of them
  are theorems of the definitions, so no goal rests on them.

`CertifyTest.AgreesWithLeanEvaluation` checks the agreement in the pinned
Lean. The value the certifier computes for each ground term is a theorem Lean
proves by `decide`, and a corrupted value one whose negation it proves, for:
240 random terms (machine, mathematical, Boolean, and Boolean equalities);
every machine operator and `if` inside every other, on either side, at 8
bits signed and unsigned, every mathematical operator inside every other, and
every connective inside every other at all eight assignments of its operands,
so that a lost parenthesis changes a value; and every operator at the extreme
operands of widths 1, 8, and 64 (a zero divisor, `INT_MIN / -1`, a shift past
the width, each overflow predicate); and for collections, 80 random chains of
operations read by length, index, membership, count, and key, 20 equalities
of sequences, and each operation where it matters (every clamp of a
subrange of `[1, 2, 3]`, membership of an element inserted and removed, each
combination of two sets, a multiset removal of a count of 0, 1, and 2, a key
written over and removed). Printing set removal as insertion fails it.
`lean_collections.test` exports a function over each kind, certifies their
automatic proofs and a proof by hand of `total(s.push(x)) == total(s) + x`,
and keeps a false claim unproved. `lean_semantics.cpp` checks the printed
forms, builds an export, certifies a goal whose proof needs the quantifier
closed and `decide` on a comparison, refuses proofs that read `(a ^ b) + 1`
as `a ^ (b + 1)` or `2 - 3` in `Nat`, and its probe file
(`Inputs/lean_semantics_probe.lean`) states the prelude's values where C++,
SMT-LIB, and Lean's own operators differ.

### Project goals and their proofs

A project names nothing by position, so that a proof keeps every name it
uses when the source around it changes. `LeanProject` (`Verifier.cpp`) owns
a project: its modules, its proof files, automation, and certification,
reporting what it warns of to its caller; a source run and an archive's
replay both drive it.

- **Names.** A module's goals form a group, `cppverify_<function>_<h6>`
  (`leanProjectGroup`), `h6` from the MD5 of the function identity, which
  tells overloads apart. A goal is `<group>_<kind>_<h8>`, `h8` the first
  eight digits of `obligationStatementHash`: SHA-256 over the obligation's
  semantics and the logical declarations it reaches, in the domain
  `cppverify-obligation-statement` version 1, without the function identity
  that the semantic hash includes, so a renamed function's goals keep their
  hashes. Goals of one group with one hash get `_2`, `_3` in source order,
  numbered over every obligation of the module whichever are exported. Spec
  bodies are `cppSpecBody_<h8 of the identity>_...`. Before 0.2 a goal was
  `..._obligation_<N>`, its position among the function's obligations, a
  body `cppSpecBody_m<module index>_...`, and its proof
  `Proofs/Goal_<md5 of the name>.lean`: reordering two postconditions gave
  each proof the other's goal, and inserting a function renamed the bodies
  every later proof used.
- **Modules.** The adapter writes a project's goals by group
  (`LeanProjectModules`): the goals, readable forms, bridges, and spec
  bodies of each function go to `CppVerify/Goals/<group>.lean`, which
  imports `CppVerify/Specs.lean`, where `emitLeanFunctionDeclarations`
  declares each spec the run's modules apply once (`opaque
  cppSpec_<identity>`). Two goal modules that declared one spec would clash
  when imported together, and Lean 4.35's import keeps one of two differing
  declarations without a word. The prelude is `CppVerify/Prelude.lean`, and
  `CppVerify/Generated.lean` imports every goal module, so a `User.lean` of
  0.1, which imports it, still sees every goal. A proof imports its goal
  module, `User` (which a new project starts with `import CppVerify.Specs`),
  and `Auto` (which imports `Prelude`); `CppVerify.lean`, the library's
  root, imports `Check`, so `lake build` builds every proof (before, the
  library had no root and `lake build` failed). Every file is written only
  when its text changes (`writeTextFileIfChanged`), and
  `writeLeanProjectModules` removes every goal module the run did not
  write: a fallback run rewrites `Specs` with the specs of the modules it
  exports, and a module it kept from an earlier run failed (`Unknown
  identifier cppSpec_...`).
- **Spec definitions** (`leanSpecDefinition`, `leanSpecsText`,
  `tryLeanSpecs`). The adapter gives each logical function of a project its
  opaque declaration and, unless it is a choice, has no step definition, or
  recurses without `Decreases` (an archive's), a candidate definition: the
  step definition printed with the recursion's applications by name and no
  temporaries (a hoisted application would lose its guard), in definition
  mode (`LeanDefinitionMode`), where each `ite` is `if _h : c`, a
  conjunction or disjunction whose later operand applies a spec is a
  dependent `if` (`a ∧ b` -> `if _h : a then b else False`, `a ∨ b` -> `if
  _h : a then True else b`, `¬a ∨ b` -> `if _h : a then b else True`), and
  a bounded existential over one guards its body by its range, each a
  classical equivalence; then `termination_by ((m1 + 1).toNat, ...)` and
  `decreasing_by all_goals cppverify_decreasing` (a prelude macro: `simp_wf;
  omega`, then with the collection and comparison wrappers unfolded, then
  with `cppIntDiv` and `cppIntRem` unfolded and their conditions split, so
  that a measure falling by a constant divisor is linear (`log2(n / 2)`),
  then `simp_all; omega`, then `decreasing_tactic`). `(m + 1).toNat` decreases
  exactly where the termination check's relation does (`upper >= 0 &&
  lower < upper`, lower possibly -1); Vermilion instead guards the whole
  body by `0 ≤ measure`, which changes the value where the measure is
  negative and the body does not recurse. The driver groups the functions
  by the strongly connected components of their applications (Tarjan,
  callees first), each group one `mutual` block, and decides each from
  `.cppverify/specs/<key>`, the key the SHA-256 of the toolchain,
  `LeanSpecRevision`, the group's text, and what each callee group is. The
  rest it tries in one Lean file importing `Auto`, the others as decided,
  undecided callees as definitions, `#cppverify_axioms` after each member:
  a definition Lean rejects is added with `sorryAx`, or not at all. A
  group's verdict is kept only when each callee tried in the same round was
  accepted; else it is tried again with the rejected callee opaque, until
  nothing changes. No Lean: undecided groups are opaque and nothing is kept.
  `Specs.lean` has the groups in that order, and its definitions use the
  classical decidability instance locally. Statements do not change: a goal
  states the same definition instances, which a definition makes theorems.
- **Records.** The exporter returns a `LeanProjectGoal` for every
  obligation of each module it exports, those a fallback selection leaves to
  the solver marked `Exported = false`, with the 0.1 names of the goal and
  its bodies. A proof file starts with a header the driver reads back
  (`readLeanProof`): the goal, the stable obligation id, the full hash, the
  body prefix, and the source, escaped as a Lean comment must be.
- **Regeneration** (`finalizeLeanProject`) reads the records of
  `CppVerify/Proofs/` and `Stale/` and gives each exported goal, in name
  order: the file at its path; else a record with its name, wherever it is
  kept; else a record of the same hash whose goal is gone, from the group
  with records of the most of this group's hashes (a renamed function's goals
  move together), in path order; else the 0.1 file of its 0.1 name; else a
  stub. A move strips the header, the notes, and the 0.1 comment, renames
  the goal and the bodies throughout the text, and writes a new header. A
  headerless file at a goal's path, a proof written over its stub, gets the
  header. A stub never edited (`Pristine`) is never moved and is removed
  when its goal is gone, as are unedited 0.1 stubs; any other record no goal
  took is renamed into `Stale/` with a note: its statement changed (a goal
  has its stable id), its function has no obligation with its statement, or
  its function is gone. `--lean-prune-stale` then removes `Stale/`. Emptied
  directories are removed, and `Check.lean` imports the exported goals.
- **Fallback runs** examine only the modules their solver leaves
  unresolved. The driver records the group of every function and
  termination module it gives the solver (`LeanRunGroups`); a record whose
  group is among them but has no goal this run, or whose goal the run knows
  but does not export, is left where it is and never moved.
- **Refutations.** Where the adapter attributes a certified counterexample
  to an obligation, it keeps the model's value of every free variable of
  that obligation's goal (`counterexampleAssignment`, read through the
  certifier's `CandidateModel::constant`, so the values are the ones it
  evaluated; `VerifyResult::Assignment`). A fallback run turns each such
  failure into `exportLeanRefutation`'s module, which states the goal and
  the bodies it unfolds as the project would (its specs added to `Specs`,
  so the trial may define them), then `theorem <goal>_refuted : ¬ <goal>`:
  the goal applied to the values in the order it binds its variables
  (machine integers as `BitVec.ofInt`, a heap or collection by its runs of
  equal cells as nested `if`s), and closed by `cppverify_refute`, an
  `Auto.lean` tactic that tries `decide`, then evaluation by the bodies,
  the spec equations (which prove the definition instances the goal states),
  memory reads, and machine comparisons, closed by `decide` or, for a store
  relation, which quantifies over every address, `grind`. When both fail it
  tries to show the instance true, in a context without the goal (which
  would prove any instance of itself): Lean deciding it true fails with
  `Lean decides the goal true at the counterexample`, else with `Lean cannot
  decide the goal`. Each attempt, and that probe, has `cppverify.autoBudget`
  heartbeats of its own (`withinBudget`, as a step of `cppverify_auto`), and
  the module lifts the heartbeat limit for the goal's definitions only, so
  the theorem keeps Lean's limit, which bounds the kernel's check of it too:
  with no limit, the refutation of an inductive predicate applied at -5000
  ran for over an hour. The prelude decides a quantifier over a
  range of integers by trying each one (`cppIntBallDecidable`,
  `cppIntBexDecidable`, through core's `Nat` ones). `writeLeanRefutations`
  writes `Refutations/<group>/<goal>.lean` and removes every other, and
  certification builds them beside the proofs and gives the checker each as
  a `refutation` entry, whose theorem must state exactly `Not <goal>` of the
  goal its module defines, with Lean's foundations alone. Once the verdicts
  settle (a failure checked with a spec postcondition that is not
  established is `spec.post`), the driver marks each failure that stands and
  was confirmed (`LeanRefuted`, JSON `lean_refuted`), warns of one Lean
  cannot decide, and makes one Lean decides true `Unresolved`
  (`InconsistentBackendResults`): two evaluators of one goal disagree, so
  the failure is not a fact. On the gate's matrix every certified failure is
  refuted; a goal applying an opaque function (a choice, `validPtr`) is not.

- **Readable goals.** `makeGoal` (`Obligation.cpp`) marks each `Or` it
  builds, `!A || rest`, with where `A` comes from (`LogicExpr::Premise`,
  like `Patterns` outside the term's meaning and its hash, kept by the
  clones, the in-place simplifier, and archives of schema 3, so a replayed
  goal names the same hypotheses). The passivizer records
  the origin of every assumption it emits (`PassiveStmt::Origin`, from a
  current origin each statement kind sets and its parts refine:
  `def`, `call:f`, `inv`, `cond`, `exit`, `keep`, `exact`, `check`,
  `spec:f`, ...) and of each entry assumption (`PassiveProgram::EntryOrigins`:
  `pre` for a written precondition, `entry` for a generated one, `null`,
  `object`); a contract's check that it is defined (`Passivizer::contract`)
  labels each clause it assumes once shown defined `pre` or `post`, and the
  state a function without a verified body returns in `ret`; spec checks
  built elsewhere default to `fact`. The Lean adapter
  peels the marked chain into `G.readable`: `∀ vars axioms, let …; (h_pre_1
  : A1) → … → C`, a hypothesis being the operand its `Or` negates (or `¬B`
  where simplification folded `¬¬B` to `B`), named `h_<origin>_<n>`, a
  definition `h_<variable>`, never a binder's name; its `let`s are the large
  subterms of the hypotheses and the conclusion. The bridge
  `G.of_readable : G.readable → G` is a term, one prelude lemma per
  hypothesis (`cppverify_imp_or : (a → b) → ¬a ∨ b`, or
  `cppverify_not_imp_or : (¬a → b) → a ∨ b`), so the kernel checks with
  the goal module that the readable form implies the goal: a printer bug in
  it fails the build, never certifies. `LeanProjectGoal::Intros` gives the
  stub its `intro` list. On the 375 suite exports, the 351 that built
  before still build, with every bridge.

- **Automation** (`automateLeanProject`, after `finalizeLeanProject`). Every
  export writes `CppVerify/Auto.lean` (`LeanAutomation.h`): the tactic
  `cppverify_auto`, a ladder of steps (`cppverify_auto_grind`, `_heap`,
  `_bv`, `_decide`, `_simp`) as Vermilion's discharger is, each run with a
  fresh heartbeat budget (`cppverify.autoBudget`, 50000), counting only when
  it closes the goal with a proof whose axioms are Lean's foundations
  (`collectAxioms` of every constant it uses), and rolled back otherwise,
  runtime exceptions included. Each step first unfolds a goal left as its
  readable form (one without binders); `_heap` turns every `heapStore*`
  equation into the function it defines and substitutes it; `_bv` and
  `_heap` rewrite the machine comparisons, constants, and overflow
  predicates into integer facts before `grind`. The steps and their order
  come from a probe of every goal the suite exports (9830): of the 5740 that
  Z3 proves, they prove 90.2%. Stating the range of every `BitVec.toInt`
  term first proved nothing more (`grind` knows the ranges), and removing
  `Int.bmod` with an `omega` discharger proved 32 fewer and took longer, so
  neither is a step. Revision 2 (`LeanAutomationRevision`) appends three
  steps after the others, so that every goal an earlier step proves keeps
  its proof: `_bveq` states equalities of machine values and sign extensions
  as integer facts too (`← BitVec.toInt_inj`, `toInt_signExtend_of_le` with
  `omega` for its side condition); `_ext` applies a collection's
  extensionality lemma; `_unfold` delta-expands the generated spec bodies
  (`cppverify_unfold_bodies`, every constant named `cppSpecBody_…`, to a
  fixed point, since a body names only lower levels of its definition) in
  the goal and its hypotheses, so each definition instance says what the
  body does, then as `_bveq`. Tagging the bodies for `grind` instead would
  have changed what every earlier step does. `_bveq` is not subsumed by
  `_unfold`: on the 37 goals of `roundtrip_uleb128` (`llvm_uleb128.cpp`)
  unfolding the lifted helpers' bodies exhausts the heartbeats, and `_bveq`
  proves them. Over the same exports (375 sources, 9259 goals), of the 5582
  that Z3 proves revision 1 proves 5044 (90.4%) and revision 2 5210
  (93.3%), none fewer; of the 112 over collections, 86 and 104. A goal
  neither proves now takes 2.8 s on average instead of 1.4 s. Revision 3
  appends `_eval`, which rewrites with the equations of every spec that
  `CppVerify.Specs` defines (`cppverify_eval_specs`, from that module's
  constant names), and with `cppIntDiv` and `cppIntRem`, and closes goals
  at known arguments; on unknown ones it unfolds until its budget is spent.
  It then appends `_div`, `grind` given the definitions of `cppIntDiv` and
  `cppIntRem`, which decides a mathematical division or remainder by a
  constant once their conditions are split; `_eval` fails without a spec
  definition, and a contract such as `a / 2 >= 2` needs no spec.
  Over the same exports, of the 5582 goals Z3 proves revision 2 proves
  5210 (93.3%) and revision 3 5301 (95.0%), none fewer, and of all 9259
  goals 8078 and 8194; in the five sources with the most new proofs, 48 of
  their 61 are `_div`'s (pointer differences divide by the element size,
  and binary search halves an interval) and 13 `_eval`'s (the factorial
  constants of `mvp_factorial.cpp`). A goal neither proves takes 4.4 s on
  average instead of 3.1 s. The trial makes 213 of the suite's 293 spec
  functions definitions; of the 80 opaque, 69 have no definition to try
  (20 choices, 47 heights and witnesses of inductive predicates, 2
  `unspecified` functions), and 11 do not terminate, or terminate only by
  their own postcondition or a choice's axiom. Its first ladder missed
  three that terminate by C++ division (`log2(n / 2)`), since `omega` does
  not see through `cppIntDiv`.
  Heartbeats alone did not bound the time, since a kernel check is not
  counted. The trial takes every exported goal whose proof file
  is pristine and whose header (`automation:`) names no attempt by the
  current `LeanAutomationRevision`, builds `Generated`, `User`, and `Auto`
  with the pinned toolchain, and runs `lean` itself (with the `LEAN_PATH` of `lake env`, so a
  stopped process leaves no child) on a file of one theorem per goal, in
  `--jobs` chunks. Lean reports to a file, line by line: the step that
  proved each goal, then the axioms of its theorem or that the kernel
  rejected it (its messages, written by a thread of its own, are buffered and
  lost when it is stopped). A goal that takes longer than
  `--lean-auto-timeout`, or stops Lean, is not proved, and the goals after it
  start again in a new process. Each goal then gets the step that proved it
  (an automatic proof, pristine like a stub) or a stub whose header records
  the attempt. An export's `LeanAutomatic` counts its goals with automatic
  proofs. Without the toolchain nothing is tried.
- **Certification** (`certifyLeanProject`) builds `Generated`, `User`, and
  `Auto` with Lake, then each proof file with `lean -EhasSorry`, `--jobs` at
  once, unless its key is unchanged (`leanProofKey`: SHA-256 of the
  toolchain, the proof's text, and the bytes of the `.olean` of every project
  module in its import closure, read from the `import` lines of their
  sources; written to `.cppverify/built/<goal>` after a build, and removed
  with the `.olean` before one). Lake cannot tell this itself: when a
  dependency fails it names only the dependency, and a dependent's `.olean`
  of an earlier build stays, so a proof the user broke would certify from
  its old `.olean`. It records the goals whose proofs do not build and runs
  the checker of
  `LeanCertifier.h`, written into the project as `.cppverify/Certify.lean`,
  with `lake env lean --run` over the goals that built. The checker
  elaborates none of the user's source, so their macros and commands cannot
  change what it checks. It reads, from their compiled files, the goal
  modules the goal list names, every proof module, and every module of the
  project they import (its `.olean` lies outside the toolchain), imports the
  toolchain modules among their imports once, and replays the project's
  modules through the kernel into that one environment, each after the
  modules it imports and the goal modules first, as `leanchecker` does. A
  module the kernel rejects, a module that imports one, and a module that
  declares a constant an earlier module or the toolchain declares otherwise
  are left out, each with why; a constant two modules declare alike (an
  equation lemma Lean derives in each, a theorem stated the same, which the
  kernel's replay takes twice) is the same. So a proof file that declares a
  goal's name is the one left out (`... declares G, which
  CppVerify.Goals.<function> declares`), and a bad module fails only the
  goals whose proofs import it. Every check reads the kernel's constants and
  the module that declared each, so proofs cannot change each other's
  checks: a goal passes when its proof module and its goal module were
  replayed, `G_proof` is a theorem of type exactly `.const G []` with `G` a
  definition of its goal module, and the axioms its kernel constants reach
  are allowed; every goal fails when a declaration of `CppVerify.User`
  depends on `sorryAx` (`userSorry`; before, `User` was compiled with `sorry`
  an error); it prints `ok` or `fail` with the reason per goal. One import
  matters because an automatic proof imports `Lean`: a check per goal took
  161 s for 33 goals (now 8 s), and the first 0.2 checker, which fell back to
  it when one module failed, imported each proof module and the imports of
  each module it replayed again, never freeing imported data, which took
  13 GB for one proof through a rejected module (now 3.6 GB,
  `lean_certifier_memory.test`) and stopped CI runners. Each Lean result
  records its goals (`VerifyResult::LeanGoals`), and a function is
  `Certified` only when all of them pass; a failure names the obligation.
  Before 0.2 certification parsed what `Check.lean` printed, which imports
  the user's modules: macros there certified proofs of `True`, and so did a
  theorem added with `debug.skipKernelTC`.

`lean_certifier.test` checks each of those attacks, a proof file that defines
a goal of the same name of its own (the type check alone would take it), a
proof that does not build, and an axiom behind a lemma, with a function whose
proofs are sound certified beside each; `lean_certifier_memory.test` bounds
the checker's memory where a proof imports `Lean` through a module the kernel
rejects. `lean_readable.cpp` checks the readable form of each kind of assumption,
the bridge, the stubs (every one builds), a proof by hypothesis names that
certifies, and a readable form that says less than its goal, which fails at
its bridge. `lean_automation.test` checks what an export writes (an automatic
proof, a stub that records the attempt, a goal stopped at the time limit with
the goals after it still tried), certification of both, that nothing is
tried again, that an edited proof is kept, that a stub of no attempt or an
earlier revision's is tried, that a step proving a goal with the user's
unfinished lemma does not count, and `--no-lean-auto`. `lean_identity.test` walks one project through each case (insertion and
reordering, renames of two functions at once, a changed statement, a removed
function and its return, fallback runs, pruning, and a 0.1 project with
proofs, stubs, and a proof of a goal that is gone) and certifies it after
the renames and the migration. `lean_modules.test` checks the layout (a
spec declared once for two goal modules certified together, a proof's
imports, a new `User`), that a rerun writes no file, that a change to one
function compiles only its goal module, `Generated`, and its proofs again,
`lake build`, that a deleted function takes its module, a 0.1 `User.lean`,
and a fallback run that keeps no goal module.

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
pure JSON stream. A construct the converter cannot represent is a
`ConversionError` at a source range: the innermost declaration, statement, or
expression being converted (`ASTConverter::CurrentRange`), unless the site
names a place of its own, such as a function for the checks made after every
function is converted. It is printed with Clang's `TextDiagnostic`, line and
caret included, as a compiler error is, and its JSON record carries the range.

## Modular Verification Protocol

1. Build VFunction for each function in source order. An error of the
   converter belongs to the function it is raised in (`ConversionError::
   Function`), and to its signature or contract (`InContract`) or its body;
   the errors that passes after conversion find about a function (a recursion
   without a measure, a malformed inductive predicate) belong to it too
   (`errorOf`). Such a function keeps what others may rely on
   (`markUnsupported`, `VFunction::UnsupportedConstruct`): an executable or
   proof function whose contract converted becomes an external contract, its
   body not verified, and one whose contract did not is left out, so a call
   of it is an `unsupported` obligation; a spec becomes a declaration without
   definition, postconditions, reads, or domain. The driver prints every
   error, gives the first of each function its verdict (`Unresolved`,
   `construct.unsupported`), reports a function whose `SpecDependencies`
   reach an unsupported spec the same way without verifying it, and verifies
   the rest; the fixpoint demotes callers of the external contracts
   (`callee.contract`). Only an error of no function stops the run.
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
   g. Check that its contract is defined (`Passivizer::contract`) when that
      program asserts anything, on the spec backend (Z3 under BMC); only a
      failure is reported, as `contract of f`.
3. For each failure, run a second pass with `cppverify::recommends` checks → warnings.
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
     demoted function its contract, until nothing changes; a contract whose
     well-formedness check is not settled is not established either;
   - a least fixpoint then rejects circles: starting from no established
     fact, a verdict is sound once every fact it needs is, and a fact once
     every verdict producing it is sound (a contract is produced by its
     function's verdict and by its well-formedness check). It needs its callees' contracts
     and its proof blocks' callees, the definitions and frames of the specs
     it mentions, and the postconditions and unfoldings its module assumes
     (`PassiveProgram`/`ObligationModule::AssumedPosts` and
     `AssumedUnfoldings`, recorded where the facts are added, never
     archived), except within a recursion cycle and for the spec it checks.
     A verdict left unsound is `Unresolved` with reason `proof.cycle`.
     Clusters (`VFunction::Cluster`, computed in the frontend) relax this
     as Dafny does: the specs and proof functions that reach each other
     through bodies, contracts (pre, post, decreases), and proof blocks,
     when all share `cppverify::decreases` clauses of one length. A call to a member
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
     naming the bound. Each finding records its verdict
     (`VerifyDiagnostic::FindingOf`) and whether its query was of the entry
     state alone (`FoundAtEntry`); when a fixpoint demotes the verdict, a
     finding is withdrawn unless its query cannot contain the missing fact:
     a callee contract enters only after the entry state, a spec fact may
     enter any query;

## Verification Backends (`VerifyBackend`)

The driver selects a backend via `VerifyOptions` (`Verifier.h` / `cpp-verify --backend`):

| Backend | Implementation | Notes |
|---------|----------------|-------|
| **Z3** | `Z3VerifyBackend` | Default. Consumes `ObligationModule`; counterexamples come from models. |
| **cvc5** | `CVC5VerifyBackend` + standalone SMT-LIB2 | Encodes the same canonical sorts, C++ truncating math division/remainder, bit-vectors, signed overflow, total heap, bounded and unbounded quantifiers (marked triggers as `:pattern`), heap frames, sequences (`full-saturate-quant` when sequences meet quantifiers), and finite ground spec equations. Sets, multisets, and maps are arrays over all integers, as for Z3 (cvc5's own set theory is finite, which would prove facts false of an infinite set): `(Array Int Bool)`, `(Array Int Int)` with a count of `max(0, cell)` and equality count by count, and `(Array Int cppverify.option)` over a declared `none | some(value)` datatype; union, intersection, and difference are declared functions each defined pointwise by one quantified axiom, exact by array extensionality, and subset is a quantified formula. A model cvc5 prints with `unknown` is certified like one after `sat`. Solver process failures and malformed output are unresolved. |
| **Strict portfolio** | `PortfolioVerifyBackend` | Runs ordered Z3 and cvc5 queries. Matching UNSAT proves; matching certified counterexamples fail and retain the Z3 model; disagreement or an unresolved side is unresolved. |
| **Race** | `RaceVerifyBackend` | Runs the Z3 and cvc5 backends at once; the first proof or certified counterexample stands and cancels the other (`cancel`/`resume`: a backend-wide `Race` of Z3 encoders, each forwarding an interrupt to the pass it runs, and a flag the cvc5 process loop polls). Otherwise the obligations either proved are joined, `Verified` (`z3+cvc5`) when they cover the module. |
| **BMC** | `LoopUnroll` on VCR, then shared obligation/Z3 path | Source verification grows bounds from zero through `--unroll=N`, stopping on a counterexample, complete unwinding, unresolved query, or the maximum frontier. Safety with failed unwinding is `BoundedSafe(N)`; only proved unwinding is `Verified`. A spec's checks have no loops: the driver solves them with a Z3 backend (`SpecBackend`), as on the default path, and keeps the bound on their archived modules for replay. |
| **Lean** | `exportLeanScratchPad` / project certification | Standalone mode emits unchecked theorem stubs. Project mode emits direct source goals, total functional heaps, typed bit-vector/integer operations, and compact finite-fuel spec bodies into generated files while preserving user proofs. Export is `Exported`; only the pinned admission-free kernel/axiom check is `Certified`. Collections are core Lean values (`List Int`, `Int → Bool`, `Int → Nat`, `Int → Option Int`) with prelude operations and lemmas. |

A Lean project pins `LeanToolchain` (`Driver/CppVerifyVersion.h`) in its
`lean-toolchain` file. A pin in `EarlierLeanToolchains`, which an earlier
release wrote, is rewritten to the current one with a warning; any other pin is
an error, since the generated semantics are written for one Lean. elan picks a
toolchain by the working directory, not by `--dir`, so through elan's proxy
every certification step names the pin (`lake +leanprover/lean4:v4.35.0
--dir=DIR ...`). Certification first asks `lake --version`, alone, since lake
takes it alone, and refuses a `lake` that reports another Lean. Before 0.2,
certification ran elan's default toolchain.

Each backend declares supported `LogicFeature`s. Central dispatch rejects a
module requiring an unavailable feature before backend execution. Spec
inlining runs before passivization: `SpecInliner::prepareFunctionAxiomatic`
on Z3, cvc5, portfolio, race, and Lean, and `SpecInliner::prepareFunction` on
BMC. `--lean-fallback=DIR` keeps Z3 or strict portfolio as the primary
backend and sends only `Unresolved` modules through the same canonical Lean
adapter. An unresolved Z3 or portfolio result lists the obligations it did not
prove individually, and by default only those are exported, under their
complete-export goal names (`--lean-fallback-scope=all` exports every
obligation). Once they kernel-check, the result is `MixedProof`
(`Proved (z3+lean)`, JSON `mixed-proof`) with `ProofEvidence` recording the
split; `Certified` still means Lean checked every obligation. A certified
counterexample is never a fallback success; its refutation shows it in
Lean.

A verdict left to Lean (a Lean-backend export, or a fallback export under
`--lean-certify`) rests on what its module uses, as a solver's does. At export
it records its dependencies as a verified verdict does (`recordDependencies`,
`CallDependencies`, and for a spec check the facts it `Establishes`), and a
spec check pending in Lean leaves its spec in `UndefinedSpecs` and
`UnprovenPosts`. Certification (`certifyLeanProject`) runs after every
function and before the fixpoint, whenever `--lean-certify` is given and
whatever else failed. It turns each pending verdict into `Certified`,
`MixedProof`, or `Unresolved`. The facts of the certified checks are then
established, and the fixpoint and the qualifiers (`[trusts=...]`,
`[partial]`, unverified callers, `decreases.missing`) treat `Certified` and
`MixedProof` as proofs (`VerifyDiagnostic::isProof`). A generated check that
is quiet when proved is reported when certification does not make it one. The vacuity checks of a
pending verdict run with the Z3 smoke backend at export. Certification marks
a proof `[vacuous]` from them, and hides the findings of a verdict it does
not certify. Before 0.2, a fallback spec check established its facts at
export and certification ran after the fixpoint and only when nothing else
had failed: callers relying on a spec whose Lean termination proof failed, or
was never checked, stayed `Verified`, and a Lean verdict was `Certified`
whatever its callees' contracts.

Z3-backed execution accepts explicit timeout, deterministic solver-resource,
canonical query-node, job-count, and proof-cache budgets. A module that
requires the `sequences` or `collections` feature gets the collection
timeout (`--collection-timeout`, by default twice `--timeout`) on every
solver backend. The driver verifies each function as a task (its own backend,
smoke backend, passivizer, and buffers for diagnostics, dumps, and archive
records) on one `llvm::StdThreadPool` of exactly `--jobs` workers, which the
Z3 and cvc5 backends also receive (`BackendExecutionOptions::Pool`) for their
obligations: a task waiting on its obligation group runs those tasks itself,
so nesting never exceeds the pool. Every group is a `TaskGroup`
(`Backend/TaskGroup.h`): a worker that waits for it runs only its tasks not
yet started, then waits for those running, and a thread outside the pool
only waits, so exactly `--jobs` run at once. Waits follow the creation of
groups, so none can wait for itself. `llvm::ThreadPoolTaskGroup`'s wait runs
whatever task the pool has next instead: a function whose own queries were
done ran another function's query in its wait, and its next check found its
`--function-timeout` spent. With more than one job and obligation, Z3
solves the obligations beside the whole query (`Z3VerifyBackend::Race`): a
proved whole query interrupts the obligation encoders, and a complete set of
proved obligations interrupts the whole query. Otherwise
the obligations decide, exactly as after a whole query alone, so the verdict
does not depend on the jobs. When the whole query yields a certified
counterexample, the obligations only choose which failure is reported, the
first in source order: the ones solved beside it are stopped, and they are
solved in order within the whole query's own budget, its timeout and, for a
probe (below), its work, with any number of jobs, so the choice does not
depend on them either (`Z3VerifyBackend::UnitsCap`). If the failing
obligation's query does not finish within it, the whole query's
counterexample stands. Before, that query could run to the timeout although
the whole query had refuted the function in milliseconds: model search over
quantified heap queries depends on the solver's search order, and 16 of 40
random seeds took the full 30 s.

The whole query of a module without logic functions is a probe of a fixed
amount of work, `WholeProbeUnits` (6 million) Z3 resource units, with the
module's timeout as its bound in time, so where it stops depends neither on
the load nor on the build. It had 500 ms before. In an assertions build, or
on a loaded core, the whole query of `certified_failure_attribution.cpp`
(about 700 thousand units) did not finish in that time; with one job its
obligations then ran, the postcondition among them, whose own search does
not end, and the function ended `Unresolved` with `solver.timeout` after
121 s on one core shared with two busy loops. The assertions build now
reports the test's counterexample there in 7 s, with one job or three. Every
probe of the test suite that an idle release build decided within 500 ms
took at most 5.2 million units (99% of the 2622 took less than 200
thousand); the three that took 5.2 million are those of the UTF-8 case
study. A probe that does not decide costs more than before: the suite has 18,
which do 1,900 to 13,000 units a millisecond, so 0.5 to 3 s each instead of
0.5 s. With one job the suite takes 1331 s instead of 1321 s on an assertions
build, most of it in `loop_frames.cpp` (3.6 s, now 8.8 s), whose five failing
functions each spend 1.4 s on a probe that never decides; with more jobs the
obligations solved beside the probe stop it once they settle the module. A
probe that its work bound stops is retried with the full budget; one that
its timeout stops already had it. A whole
query given only a slice of the budget (a sixth of it over collections)
checks a model it finds with a check's own time (half the module's timeout,
or `--certify-timeout`), not with what is left of the slice
(`Z3Encoder::setSearchSlice`): on one loaded core the search of a 500 ms
probe took 460 ms, the check had 41 ms, and the model was left unchecked.
Racing, a whole query its probe or slice leaves unresolved is retried with
the full budget as one more task of the race, queued after the obligations:
a free worker runs it beside them, and without one the function's own thread
runs it after them, as with one job. Before, the retry always waited for the
obligations, so an obligation whose search does not end held it back until
that obligation's timeout: with the 500 ms probe, that test took 61 s with
`--jobs=3` on two loaded cores. The obligations stop the whole query, or its
retry, whenever they settle the module: when one fails, as when they prove
all of it. A proof cache stores proofs of single obligations, so with one
only the obligations are solved.

Every query runs in an encoder of its own (`Z3VerifyBackend::solveQuery`):
a Z3 context keeps the state of the queries solved in it, as far as an
interrupted one got, and that state steers the search of the next. With one
long-lived encoder per backend, which with one job (as under lit) solved
every function of a file, the retry of a complete query interrupted under
load timed out in 2 of 40 runs of `loop_exits.cpp`, a file's counterexamples
changed from run to run (14 outputs in 16 runs), and after one induction
attempt every later query of the file only sought a proof. A query is still
not entirely independent of the process: Z3 hashes some objects by address,
so a model's values can depend on what ran before it.

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
until it returns. Ctrl-C stops the whole process the same way:
`cpp-verify` installs `requestInterrupt` as LLVM's interrupt function, which
only sets a flag, and every check's watchdog, the cvc5 process loop, and the
certifier's clock poll it, so running queries stop and none starts. The
driver reports each function whose verification had not ended as
`Interrupted` (reason `interrupted`), keeping its verdicts, hidden, for what
they establish, and the tool exits with 130; a second Ctrl-C ends the
process, since LLVM restores the default handler before it calls the
interrupt function. Every solver is created with Z3's `ctrl_c` parameter
off: otherwise each check swaps Z3's own SIGINT handler in, Z3 keeps the
handlers of concurrent checks in one unsynchronized stack, and Ctrl-C ran the
handler of a finished check (a crash report, then a run that went on).
Source-location annotation takes a lock, since
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
`Unresolved`, never cache misses or proofs. A store failure after a fresh
solver proof remains explicit telemetry rather than invalidating that proof.
Size and entry-count pruning runs once, after the run's last lookup: pruning
after each function removed entries that the functions verified beside it had
not yet looked up, so their verdicts depended on scheduling. A failure to
prune is a warning. Pruning proceeds independently of cache errors, touches
only CppVerify-prefixed records, and removes abandoned atomic-write files
after 24 hours; a capacity-limited write is retried after evicting an entry. Failed, unknown,
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

`ASTConverter` lowers contracted **exec** calls to `VCallStmt` nodes. Nested calls in expressions (e.g. `return f(g(x))`) are flattened into a sequence of calls with temporaries (`__nested_N`) so `Passivize::emitCallStmt` can apply callee `cppverify::pre`/`cppverify::post` at each site.

At each call the passivizer:

1. Maps actual arguments into the callee parameter namespace.
2. `assert`s callee preconditions (including implicit non-aliasing from the callee's contract).
3. Changes the value heap only inside the callee's `cppverify::modifies` footprints.
4. `assume`s callee postconditions (including `cppverify::result` linkage), where a
   formal, inside or outside `cppverify::old`, denotes its entry actual.

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

The callee may update the value heap under its ordinary `cppverify::modifies` contract;
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
declarations inside loops remain fail-closed; so does the decay of an array
member through a pointer (`ASTConverter::arrayDecayError` names which). Automatic metadata transitions
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
by the Clang target `sizeof(T)`. Unless both operands are null (a difference
of 0, as C++ defines), passivization asserts non-null/live bases, one origin,
and in-range positions; it always asserts target-`ptrdiff_t` representability
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
lowered only after proving containment, including nonnegative offset/length
and the one-past empty case: structurally when it is written as a caller
parameter plus an offset (`sliceContainment`), and otherwise, in the object
model, by `[actual, actual + n * S]` lying in an entry object its origins name,
or in any of the caller's objects when they are unknown
(`Passivizer::objectContainment`). The callee's validity precondition for such
an argument is then discharged by the same membership (`abstractValidity`)
instead of a parameter's validity at entry. A conservative transitive
body scan distinguishes acyclic read-only callees from unknown, recursive, or
writing effects. Exact-cell writes reuse ordinary frame substitution; writes to
a symbolic range or a whole sub-slice are supported, framed by a `HeapFrame`
relation over the written regions.

Ghost blocks and proof functions share the VCR statement vocabulary but are
erased by CodeGen. Frontend isolation therefore permits assignments only to
ghost/proof-local values, rejects executable calls and runtime-memory/global
writes, and requires `cppverify::decreases` on proof-only loops. This prevents erased
mutation, returns, or nontermination from changing executable verification
semantics.

## Compile-Time Integration

`CppVerifyIntegration` (`clang/lib/Verify/Driver/CppVerifyIntegration.cpp`) hooks **CodeGen**: when `-fverify-contracts` is on and `-fno-verify` is off, verification runs asynchronously while LLVM IR is generated. Failures surface as `diag::err_fe_cppverify_failed`. Zero ghost/spec code in the object file.

## Tooling Integration

Contracts are visible to every Clang-based tool, so editors treat them as
code:

- `RecursiveASTVisitor` (and `DynamicRecursiveASTVisitor`) visits function
  contracts and the construct references written in a function from
  `TraverseFunctionHelper`, loop contracts from the `while`/`for`/`do`
  traversals (found through the `ASTContext` the function's traversal sets),
  and type invariants from the `CXXRecordDecl` traversal. clangd's hover,
  go-to-definition, rename, document highlights, semantic highlighting, and
  inlay hints, clang-tidy's matchers, and the parent map all build on it.
  A visitor that analyzes executable code opts out with
  `shouldVisitCppVerifyContracts()` returning false (`ShouldVisitCppVerifyContracts`
  for the dynamic visitor): PGO counter mapping (`CodeGenPGO`), the dllimport
  inlining check (`CodeGenModule`), and function-effect analysis
  (`SemaFunctionEffects`), so contracts never change generated code. A walk
  that starts at a function body, as the verifier's own and Sema's do, sees
  no contract.
- libIndex indexes the contract expressions and construct references of each
  function and record, and loop contracts inside bodies, which gives clangd's
  find references, cross-file rename, and call hierarchy.
- libclang exposes them as child cursors of the function and the loop:
  each construct is an unexposed expression or statement
  (`CXCursor_UnexposedExpr`, `CXCursor_UnexposedStmt`) with its operands as
  children.
- `DeclPrinter` prints a function's clauses, one per line, after its
  declarator, and `cppverify::spec`/`cppverify::proof` as its specifier;
  `StmtPrinter` prints loop clauses and the constructs qualified. clangd's
  hover on a function therefore shows its contract, and `-ast-print` output
  parses again.
- Each construct written in a function is recorded as a `DeclRefExpr` to its
  declaration in `<cppverify.h>` (`ASTContext::getCppVerifyReferences`), with
  the qualifier as written, so hover shows the construct's documentation and
  renaming a namespace alias updates every construct.
- clang-format (`lib/Format/CppVerifyClauses.cpp`) lays out each clause after
  a function declarator or a loop head like a trailing `requires` clause: on
  its own line, the body's brace below. In a clause, the colon of a range
  footprint `p[lo : n]` is a range separator (`TT_ArraySectionColon`), never
  an Objective-C message's.
- Clang's own analyses meet the constructs by their meaning. The CFG leaves
  out ghost code and contract statements, which emit no code, so the static
  analyzer and the CFG-based warnings continue past them. A contract
  expression cannot throw (`noexcept`), is not an integral constant
  expression, has its operands' side effects, and is reported as not yet
  mangled where a mangled name would contain it. CI fails when a `switch` over
  statement classes misses one of the contract classes.

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
- Runner: `scripts/run-verify-tests.sh`.
- Backend fidelity gate: `clang/test/Verify/suite/backend_fidelity_gate.test`
  requires cvc5 and pinned Lean 4.35.0 and runs the permanent differential
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
| Lean | Source/archive obligation identity, one proof file per project goal recording its statement hash, generated-file kernel build, bounds instrumentation, and decisive verdicts: every valid case certified (one with a proof by hand, `Inputs/backend_fidelity_proofs`), every counterexample refuted |
| Advisory checks | `cppverify::recommends` warnings stay source-only and never enter BMC or Lean replay artifacts |

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

- VCR still lacks a first-class object/place/effect type system, general
  arrays, and structured aggregate values;
- pass registration and a stable plugin ABI are not implemented yet;
- archives carry portable inclusive presumed source ranges rather than raw
  Clang locations or macro-expansion stacks;
- Z3 proof-object certification and independent replay are not implemented;
  Lean certification is an interactive proof path, not Z3 proof replay.

| Future feature | Correct extension point |
|---|---|
| Symbolic execution | VCR analysis/backend preserving C++ and source metadata |
| Separation/ownership reasoning | VCR object/effect extension plus a declared logic feature and adapter |
| Abstract interpretation / invariant inference | VCR pass that proposes facts rechecked as ordinary obligations |
| `std::vector` model | Frontend/library model lowered to VCR object/place operations |
| Concurrency | VCR atomic/effect model, then explicit happens-before logic terms |
