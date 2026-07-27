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

Core expression definedness is mandatory; it is not disabled by omitting a
flag. The current `--check-ub` option is narrower than its historical name: it
enables `valid(p, n)`-based **buffer extent** checking on the Z3 path. This
rollout split lets existing pointer code opt into explicit bounds while signed
arithmetic, division, shifts, dereference validity, and lifted-`constexpr`
definedness remain checked on every normal proof.

## How the two obligations combine

They interleave in one weakest-precondition pass rather than being generated as
independent safety and functional programs. Conceptually, for `x = a + b`:

```
wp(x = a + b, Q)  =  no_overflow_signed(a, b)   ∧   Q[x := a + b]
                     └──── safety obligation ────┘   └──── functional ────┘
```

The safety obligation sits **inline at each operation**; the functional
obligation (the postcondition) sits at the end. They compose soundly because of
order: once `no_overflow(a,b)` holds, the bit-vector result `bvadd(a,b)` equals
the true mathematical `a + b`, so functional reasoning about `post` is faithful.
The backend's sound UNKNOWN-recovery path may submit individual ordered
assertions separately, but it never changes this program order or lets a later
assumption justify an earlier safety check.

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

UB is open-ended — there will always be more cases. The implementation has two
additive insertion points:

```
   Layer-1 VFunction
          │
          ├─ --check-ub + Z3
          │    instrumentUBChecks()
          │    - discover valid(p, n) before spec inlining
          │    - add extent semantics and indexed-access bounds asserts
          │
          ▼
   passivization, in C++ evaluation order
          safetyForExpr()
          - arithmetic/division/shift definedness
          - non-null abstract-valid loads and stores
          - path-sensitive lifted-constexpr definedness
          │
          ▼
   guarded passive assert → ordered weakest precondition
```

Both paths produce ordinary guarded proof obligations. A check fires only when
applicable: machine integers (`IntMode == Machine`) and, for overflow,
**signed** operands. Unsigned overflow is defined wraparound in C++ and is
deliberately not flagged.

`valid` is a conventional pure spec declaration, not a new keyword:

```cpp
spec bool valid(int *p, int n) { return true; }
```

When `valid(p, n)` appears in a precondition under `--check-ub`, the verifier
adds these semantics before the intentionally trivial body can inline to
`true`:

- `n >= 0`;
- `n == 0` permits a null pointer;
- `n > 0` requires `p != nullptr` and the abstract pointer-validity predicate;
- every `p[i]` or `*(p + i)` access must prove `0 <= i && i < n`.

An access through a base with no declared extent still receives the mandatory
non-null/abstract-valid dereference check, but no size claim is invented.

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

Specifics for machine arithmetic:

- **Only signed integer arithmetic is checked.** Unsigned overflow is defined in
  C++ (modular wraparound); the existing `bvadd`/… wrapping encoding is already
  correct for unsigned, so no obligation is emitted. (This requires signedness in
  `VType`, added for this feature.)
- **Width is taken from the target's data model and Clang's computation type.**
  `VType` records the relevant width and signedness, integral promotions happen
  before arithmetic, and assignment converts back to the destination width.
  The Z3 encoder therefore checks `int` at 32 bits and `long`/`long long` at 64
  bits on LP64, while narrow increments and compound assignments use promoted
  arithmetic followed by faithful narrowing.

## Layering

UB classes are introduced in layers, each sound on its own, each sized to the IR
fidelity it needs. We grow IR/heap fidelity in lockstep with the classes we
check, rather than trying to encode the whole abstract machine up front.

| Layer | UB caught | IR / model need | Status |
|---|---|---|---|
| **A** | signed arithmetic/negation overflow, division/modulo by zero, invalid shifts, null/abstract-invalid dereference | typed expressions + signedness/width in `VType` | **implemented, always on** |
| **B1** | out-of-bounds indexed access for a declared buffer extent | `valid(p, n)` marker + base/offset recovery | **implemented with `--check-ub` on Z3** |
| **B2** | use-after-end-of-lifetime and reads of uninitialized heap storage | block-structured heap (allocation = size+liveness+initialization) | planned |
| **C** | pointer provenance, strict-aliasing (TBAA), alignment | precise object model | assumed-away (documented) |

### Assumed-away (Layer C and beyond)

These are explicitly **not** checked and are assumed not to occur. Programs that
rely on them are outside the verified subset:

- pointer provenance / out-of-object pointer arithmetic,
- strict-aliasing violations (accessing an object through the wrong type),
- alignment violations,
- data races / concurrency,
- allocation/deallocation and heap-object lifetime changes.

## Scope and the flag

- Core expression safety applies to exec and `proof` functions; mathematical
  `spec` functions are total and are never instrumented for machine UB.
- **`cpp-verify --check-ub`** additionally enables buffer extent discovery and
  bounds obligations. That extent feature currently runs only on the Z3
  backend and has no `clang++` driver spelling yet.
- Omitting `--check-ub` does **not** disable overflow, division, shift, or
  dereference checks. It only means the verifier has no declared buffer length
  from which to prove indexed bounds.

## How to add a new check (the recipe)

1. If the check is local to one evaluated expression, add it to
   `safetyForExpr` so it follows short-circuit, branch, loop, and early-return
   guards automatically.
2. If the check needs function-wide metadata such as a declared extent, collect
   that metadata before spec preparation and inject guarded `VExpr` assertions
   in `instrumentUBChecks`.
3. If it needs a solver primitive (like overflow), add a variant to
   `VOverflowCheckExpr` (or a sibling node), one case in `VCMachine::fromVExpr`,
   and one case in `Z3Encoder` mapping to the primitive.
4. Add the applicability guard (type/signedness/mode) in the checker.
5. Add edge-case and general tests under `clang/test/Verify/suite/` and a runnable
   example under `examples/`.
