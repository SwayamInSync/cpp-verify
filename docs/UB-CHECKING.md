# Undefined-Behavior Checking

## Why this exists

A verifier for **runtime** C++ code has two obligations, not one. For a function
with `pre`/`post`:

1. **Safety** — every operation the function executes is *well-defined* (no UB).
2. **Functional** — `pre ∧ code ⇒ post`.

Both are mandatory. The functional obligation is **meaningless without the
safety one**: if the code can execute UB, the real program has no defined
behavior at all, so proving `post` against our (necessarily total) model proves
nothing about the binary. UB-freedom is therefore *prior to* functional
correctness, and — crucially — it is the **tool's** job to generate the safety
obligations, not the user's. The user writes `pre`/`post`; if `pre` is too weak
to rule out an overflow, the tool reports the overflow and tells the user the
precondition their algorithm actually needs.

This is the Verus/SPARK posture: signed `a + b` carries an implicit "does not
overflow" proof obligation that you discharge via preconditions/invariants, or
verification fails.

### Spec world vs. exec world

UB checking applies only to the **exec world** (real `exec`/`proof` functions,
machine integers, `VIntMode::Machine`). The **spec world** (`spec` functions,
unbounded `VIntMode::Math`) has no notion of overflow by construction and is
never instrumented.

## How the two obligations combine

They are not two separate solver runs. They interleave in one weakest-precondition
pass. Conceptually, for `x = a + b`:

```
wp(x = a + b, Q)  =  no_overflow_signed(a, b)   ∧   Q[x := a + b]
                     └──── safety obligation ────┘   └──── functional ────┘
```

The safety obligation sits **inline at each operation**; the functional
obligation (the postcondition) sits at the end. They compose soundly because of
order: once `no_overflow(a,b)` holds, the bit-vector result `bvadd(a,b)` equals
the true mathematical `a + b`, so functional reasoning about `post` is faithful.

Mechanically, each safety obligation is emitted as a **guarded `assert`** in the
Layer-1 IR, *before* the statement that consumes the value. From there the
existing pipeline does the rest:

- **Passivization** SSA-renames the obligation's operands and path-guards it
  (`guardCond` / `DeadConds`), so an obligation inside a branch or after an early
  return is only required on the path that reaches it.
- The **nested-WP VC machine** checks each obligation against exactly the
  assumes that precede it.

So the UB layer is *purely additive*: it inserts asserts; the Tier-0 soundness
machinery discharges them.

## The extensible checker framework

UB is open-ended — there will always be more cases. The design is built so that
**adding a new check is a localized, additive change**, never a rewrite.

```
   Layer-1 VFunction body
          │
          ▼
   instrumentUBChecks(VFunction&)        ← walks statements, in evaluation order
          │   for each evaluated VExpr:
          ▼
   collectObligations(VExpr*, out)       ← the REGISTRY: one case per UB kind
          │   returns a list of boolean "this op is safe" VExprs
          ▼
   insert  contract_assert(obligation)   ← before the consuming statement
                                            (and at loop-body end for conditions)
```

`collectObligations` is the single extension point. Each checker:

1. pattern-matches a `VExpr` shape (e.g. a signed `VBinOpExpr` with `Op == Mul`),
2. builds a boolean obligation expression (`true` ⇒ the operation is safe), and
3. appends it to the output list.

A check fires only when it is **applicable**: machine integers
(`IntMode == Machine`) and, for overflow, **signed** operands (unsigned overflow
is defined wraparound in C++ and is deliberately *not* flagged).

### Obligation representation

Most obligations are ordinary `VExpr` (`b != 0` for division-by-zero, a range
comparison, …). Arithmetic *overflow* obligations use a dedicated node,
`VOverflowCheckExpr`, because the precise predicate is a primitive of the solver
(`Z3_mk_bvadd_no_overflow` and friends) rather than something safely expressible
in surface arithmetic (the surface form would itself overflow). The node carries
the operation and operands and is threaded `VExpr → VCExpr → Z3`:

| `VOverflowCheckExpr` op | Z3 encoding (signed) |
|---|---|
| `Add` | `bvadd_no_overflow(a,b,signed) ∧ bvadd_no_underflow(a,b)` |
| `Sub` | `bvsub_no_overflow(a,b) ∧ bvsub_no_underflow(a,b,signed)` |
| `Mul` | `bvmul_no_overflow(a,b,signed) ∧ bvmul_no_underflow(a,b)` |
| `Neg` | `bvneg_no_overflow(a)` |
| `SDiv` | `bvsdiv_no_overflow(a,b)` (the `INT_MIN / -1` case) |

## Soundness model

The model is **sound by conservative over-approximation**, not by precisely
mirroring the C++ abstract machine (which, for C++, no tool fully does). A
check must flag an operation as possibly-UB whenever *some* real execution makes
it UB; being conservative (occasional false positives) is sound, missing a real
UB is not. Precision is a UX dial we can sharpen later without ever becoming
unsound.

Specifics for Layer A:

- **Only signed integer arithmetic is checked.** Unsigned overflow is defined in
  C++ (modular wraparound); the existing `bvadd`/… wrapping encoding is already
  correct for unsigned, so no obligation is emitted. (This requires signedness in
  `VType`, added for this feature.)
- **Width.** Machine integers are currently encoded as 32-bit bit-vectors
  regardless of declared width, so overflow is checked at 32-bit. For `int` this
  is exact. Sub-`int` types (`int8/16`) are modeled as `int`, and `long`/`int64`
  is currently also modeled at 32-bit — so 64-bit overflow is **not yet** caught
  precisely. Per-width bit-vector sorts are a planned refinement; the obligation
  node already takes whatever width the encoder assigns, so it tightens for free
  once widths land.

## Layering

UB classes are introduced in layers, each sound on its own, each sized to the IR
fidelity it needs. We grow IR/heap fidelity in lockstep with the classes we
check, rather than trying to encode the whole abstract machine up front.

| Layer | UB caught | IR / model need | Status |
|---|---|---|---|
| **A** | signed `+ - * /` overflow, unary `-` overflow, division/modulo by zero | scalar compute model + **signedness in `VType`** | **implemented** (this doc) |
| **B** | out-of-bounds access, use-after-end-of-lifetime, uninitialized read | **block-structured heap** (pointer = base+offset, allocation = size+liveness) | planned |
| **C** | pointer provenance, strict-aliasing (TBAA), alignment | precise object model | assumed-away (documented) |

### Assumed-away (Layer C and beyond)

These are explicitly **not** checked and are assumed not to occur. Programs that
rely on them are outside the verified subset:

- pointer provenance / out-of-object pointer arithmetic,
- strict-aliasing violations (accessing an object through the wrong type),
- alignment violations,
- data races / concurrency,
- shifts and bitwise operators (not yet represented in Layer-1 at all — when they
  are added, shift-amount-range is a one-checker addition to the registry).

## Scope and the flag

- Enabled with **`--check-ub`** on `cpp-verify` (and intended to become
  `-fcheck-ub` on the `clang++` driver). It is **flag-gated for migration**: the
  end state is UB checking *on by default* for exec functions, because that is
  what makes the runtime contract mean something. The flag is the rollout path,
  not the design — the two-path structure is intrinsic, not optional.
- Backend: **Z3** (the overflow predicates are bit-vector primitives). The BMC
  and Lean backends ignore the obligations for now.
- Applies to exec and `proof` functions; `spec` functions are never instrumented.

## How to add a new check (the recipe)

1. If the predicate is expressible in surface arithmetic, build it as ordinary
   `VExpr` in a new case of `collectObligations`. Done.
2. If it needs a solver primitive (like overflow), add a variant to
   `VOverflowCheckExpr` (or a sibling node), one case in `VCMachine::fromVExpr`,
   and one case in `Z3Encoder` mapping to the primitive.
3. Add the applicability guard (type/signedness/mode) in the checker.
4. Add edge-case and general tests under `clang/test/Verify/suite/` and a runnable
   example under `examples/`.

No other layer changes. That is the whole point of routing every obligation
through the single `collectObligations` registry and the guarded-assert
injection.
