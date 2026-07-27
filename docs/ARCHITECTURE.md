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
│  Stage 4: WP Calculus    │
│  - Walks Layer 2 backward│
│  - Generates verification│
│    conditions (VCs)      │
└──────────┬───────────────┘
           │ VCs (logical formulas)
           ▼
┌──────────────────────────┐
│  Stage 5: Z3 Encoding    │
│  - VType → Z3 Sort       │
│  - VExpr → Z3 Expr       │
│  - Heap → Z3 Array sort  │
│  - Check validity:       │
│    add(¬VC), check UNSAT │
└──────────┬───────────────┘
           │ sat / unsat / unknown
           ▼
┌──────────────────────────┐
│  Stage 6: Diagnostics    │
│  - Map Z3 result back to │
│    SourceLocation        │
│  - Extract counterexample│
│    from Z3 model         │
│  - Emit Clang-style      │
│    warnings/errors       │
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

Every `VExpr` carries a `VType` populated automatically from Clang's canonical
`QualType` during AST conversion; users never re-annotate contract types.
Integer width and signedness come from `ASTContext`, pointers use the abstract
address sort, and supported records are flattened separately into typed scalar
fields. Unsupported type structure is diagnosed before lowering.

### Types (VType)

```
VIntMode = Math | Machine

VType =
  | Bool
  | Int32(IntMode, bitWidth, signedness)
  | Int64(IntMode, bitWidth, signedness)
  | Struct                                   // fields flattened by VFunction
  | Ptr                                      // untyped mathematical address
  | Void
  | Unsupported
```

- Every `VExpr` carries a `VType`. Populated from Clang's `QualType` during ASTConverter.
- The `IntMode` tag on integer types is set by ASTConverter:
  - In `spec` function bodies → `Math` (Z3 `Int`)
  - In `proof`/`exec`/lifted-`constexpr` function bodies → `Machine` (Z3 `BitVec`)
- Raw pointers to supported scalar or flat-record pointees are admitted.
  References, pointer-to-pointer values, smart pointers, and pointer-bearing
  records are rejected at the current verifier boundary.
- `Int32`/`Int64` are storage categories; `bitWidth` carries the exact target
  width, including narrow integers and `__int128`.

### Expressions (VExpr)

```
VExpr =
  | Literal(value, type)
  | Var(name, type)
  | BinOp(op, lhs: VExpr, rhs: VExpr, type)
  | UnaryOp(op, operand: VExpr, type)
  | Cast(inner: VExpr, fromType: VType, toType: VType)
  | FieldAccess(base: VExpr, field: string, type)
  | ArrayIndex(base: VExpr, index: VExpr, type)
  | Load(ptr: VExpr, type)                       // *p in an expression context
  | AddrOf(lvalue: VExpr, type)                  // &x
  | FnCall(name, args: [VExpr], type)
  | Forall(binder: VarDecl, lo: VExpr, hi: VExpr, body: VExpr)
  | Exists(binder: VarDecl, lo: VExpr, hi: VExpr, body: VExpr)
  | Old(inner: VExpr)
  | Result(type)
  | Conditional(cond: VExpr, then: VExpr, else: VExpr, type)
```

All carry `SourceLocation` for diagnostics.

**Cast node rationale:** Clang inserts `ImplicitCastExpr` aggressively for integral promotions, sign conversions, and widening. Stripping these is safe only in mathematical integer mode (`z3::Int`). In BitVec mode, `(int64_t)x + y` and `x + y` differ when `x` is `int32_t`. By preserving casts as explicit `Cast(inner, fromType, toType)` nodes, the Z3 encoder makes the mode decision once — emit `sign_extend`/`zero_extend` or no-op — without requiring a second pass over the IR.

**Load node:** Reads through a pointer in expression contexts. `*p` → `Load(p, T)` where `T` is the pointee type. The Z3 encoder maps this to `(select mem p)`.

### Statements (VStmt)

```
VStmt =
  | VarDecl(name, type, init: VExpr?)
  | Assign(target, value: VExpr)                          // local variable
  | Store(ptr: VExpr, value: VExpr)                       // *p = value
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
- `RevealWithFuel`: locally raises Z3 unfolding depth for the named recursive spec function within the enclosing function's VC.

### Functions (VFunction)

```
VFunction =
  name: string
  identity: string                         // signature-stable internal key
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
  decreases: [VExpr]                   // tuple → lex-ordered
  intMode: VIntMode                    // Math for explicit spec; Machine otherwise

```

- `identity` includes the canonical signature, so overloads with the same
  source spelling remain distinct through modular calls and SMT symbols.
- `aliases` empty means the implicit non-aliasing/range-exclusivity precondition
  applies to distinct mutable raw-pointer parameter pairs.

## Layer 2: Passive IR

Purpose: eliminate control flow so wp calculus can operate mechanically. All variables assigned exactly once (SSA). Loops replaced by havoc/assume/assert. The heap is also SSA-versioned (`mem_0`, `mem_1`, ...).

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

**Function calls → assert precondition, havoc modifies, assume postcondition:**
```
// y = foo(x)  where foo has pre(P) modifies(M) post(Q)

assert(P[params := args] ∧ /* implicit non-aliasing pre, if applicable */);
havoc(M);                              // forget the locations declared in modifies
havoc(y);
assume(Q[Result := y, Old(params) := args]);
```

- Exact footprints such as `p->field` and `p[i]` replace only that address with a
  fresh value. Other addresses retain the preceding heap version.
- A bare `modifies(*p)` is a **region** footprint: it authorizes any indexed
  store rooted at `p` in the callee body. The flat heap does not yet carry an
  allocation/provenance identity with which to bound that region at a modular
  call, so the caller conservatively receives a fresh whole heap. This loses
  facts but cannot create a false proof.
- A callee with pointer parameters and no explicit footprint also receives the
  conservative whole-heap treatment. Pure scalar calls do not havoc the heap.
- Footprint containment is checked in the caller's entry state, so reassigning a
  pointer variable cannot expand the caller's declared frame.

## WP Calculus Rules

```
wp(skip, Q)                = Q
wp(x = E, Q)               = Q[x := E]
wp(*p = E, Q)              = Q[mem := store(mem, p, E)]
wp(S1; S2, Q)              = wp(S1, wp(S2, Q))
wp(assert(P), Q)           = P ∧ Q
wp(assume(P), Q)           = P → Q
wp(havoc(x), Q)            = ∀x. Q
wp(if(c) S1 else S2, Q)    = (c → wp(S1,Q)) ∧ (¬c → wp(S2,Q))
```

After Layer 2 transformation, there are no loops or function calls left — only assignments, stores, asserts, assumes, havocs, and if/else.

## Z3 Encoding

| VType | Z3 Sort |
|---|---|
| Bool | `Bool` |
| Int32(Math), Int64(Math), ... | `Int` |
| Int32(Machine), Int64(Machine), ... | `BitVec(N)` |
| UInt32(Math), UInt64(Math), ... | `Int` with `≥ 0` invariant |
| UInt32(Machine), UInt64(Machine), ... | `BitVec(N)` |
| Struct | Flattened: each supported field becomes a separate typed Z3 constant |
| Ptr | `Int` (mathematical abstract address) |
| Heap | `Array(Int, Int)` with typed load/store conversions at the boundary |

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

**Spec functions → finite call-site equations:** each referenced `spec` call
becomes an SMT function application plus a defining equation specialized to
that call's actual arguments. Nonrecursive specs are normally inlined before
this stage. Recursive definitions default to one unfolding step and retain
residual applications; `reveal_with_fuel` raises the finite depth. CppVerify
does not install a universal self-triggering recursive axiom.

**`recommends`:** parsed and stored; not emitted into the main VC. On verification failure, a second pass adds `recommends` checks and reports violations as warnings.

**Verification:** the primary query submits the complete ordered weakest
precondition: `solver.add(!vc)`. UNSAT means the VC holds; SAT yields a
counterexample. If Z3 returns UNKNOWN, the backend retries individual
assertions in program order, with entry assumptions and only the assumptions
that precede each assertion. This can recover tractable quantified heap proofs
without allowing a later fact to justify an earlier obligation. If every
soundly smaller query cannot be discharged, UNKNOWN is reported and the
function is not considered verified.

## Counterexample Extraction

When Z3 returns SAT, extract the model:
```
z3::model m = solver.get_model();
for each variable in VC:
    value = m.eval(variable);
    map variable back to SourceLocation via IR metadata;
    emit diagnostic with concrete values;
```

Output format:
```
example.cpp:12:5: error: precondition may not hold
  pre(x > 0)
  ^~~~~~~~~~~
  counterexample: x = -1
```

For pointer-related failures, the counterexample includes the heap state:
```
example.cpp:20:9: error: postcondition may not hold
  post(*a == old(*b))
  counterexample: a == b (aliased; missing aliases(a, b) clause?)
```

## Modular Verification Protocol

1. Build VFunction for each function in source order.
2. For each VFunction:
   a. Build Layer 1 IR.
   b. Passivize to Layer 2 (SSA + havoc/assume/assert + heap versioning).
   c. Compute wp of postcondition through Layer 2.
   d. Conjunct preconditions + implicit non-aliasing + type_invariants of parameters.
   e. Submit to Z3.
   f. Report verified / counterexample / unknown.
3. For each failure, run a second pass with `recommends` checks → warnings.

## Extensibility Points

| Future Feature | What Changes |
|---|---|
| BMC backend | New backend consuming Layer 1 directly, unrolling loops K times |
| Symbolic execution | New backend forking at branches, collecting path constraints |
| Separation-logic mode | New heap representation with explicit ownership predicates; alternative to the current array model |
| std::vector | Abstract model: Array + length in Layer 1, Z3 array theory |
| Overflow checking | Switch Z3 encoder to BitVec mode globally via `--bv`; Cast nodes already carry from/to types |
| Concurrency | Extend IR with atomic statements, add happens-before encoding |
| Unbounded quantifiers + manual triggers | Extend Forall/Exists with optional trigger sets; encoder honours them |
