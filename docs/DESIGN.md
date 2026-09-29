# Contract Syntax & Language Design

## Enabling Contracts

All contract syntax is enabled with `-fverify-contracts`. Without this flag, the new keywords are not reserved and existing C++ code compiles normally.

## Contract Syntax Overview

| Syntax | Where | Meaning |
|---|---|---|
| `pre(expr)` | After function `)` | Precondition — caller must satisfy |
| `post(expr)` | After function `)` | Postcondition — callee must establish; may use `result` and `old(x)` |
| `modifies(lvalue, ...)` | After function `)` | Frame condition — declares the lvalues this function may write to |
| `aliases(p, q)` | After function `)` | Opts out of implicit non-aliasing for a supported same-pointee pointer/reference address pair |
| `recommends(expr)` | After function `)` (spec only) | Soft precondition for spec functions; reported on verification failure |
| `invariant(expr)` | After a `while`/`for` condition or a `do` loop's trailing condition | Loop invariant |
| `decreases(expr [, expr...])` | After loop `)` or function `)` | Termination measure. Tuple form is lex-ordered. |
| `type_invariant(expr)` | Inside class/struct body | Per-instance invariant injected at function boundaries |
| `ghost { ... }` | Statement | Ghost block — proof steps, stripped by CodeGen |
| `contract_assert(expr)` | Statement | Verification condition (not a runtime check) |
| `reveal_with_fuel(fn, n)` | Inside ghost blocks | Locally raise Z3 unfolding depth for spec function `fn` |
| `spec T f(...)` | Declaration | Pure spec function — interpreted by verifier only |
| `proof void f(...)` | Declaration | Ghost proof function — establishes lemmas |
| `forall(i, lo, hi, expr)` | Expression | Bounded universal quantifier |
| `exists(i, lo, hi, expr)` | Expression | Bounded existential quantifier |
| `old(expr)` | Inside `post` or `invariant` | Value of `expr` at function entry |
| `result` | Inside `post` | Return value of the enclosing function |

## Function Contracts: pre / post / modifies / aliases / recommends

```cpp
void swap(int* a, int* b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
    int t = *a; *a = *b; *b = t;
}
```

- `pre(expr)`: precondition. `expr` must be contextually convertible to bool.
- `post(expr)`: postcondition. `expr` may reference `result` (return value) and `old(x)` (pre-state).
- `modifies(lvalue, ...)`: frame condition — see §Pointers and Memory below.
- `aliases(p, q)`: see §Pointers and Memory below.
- Multiple `pre` / `post` / `modifies` clauses are conjuncted.
- Parsed after the function declarator's `)` and before `{`.

## Loop Contracts: invariant / decreases

```cpp
while (i < n)
  invariant(2 <= i && i <= n)
  invariant(fib.size() == i)
  decreases(n - i)
{ ... }
```

- `invariant(expr)`: must hold on entry and be preserved by each iteration.
- `decreases(expr [, expr...])`: termination measure. Single expression must be non-negative and strictly decreasing. Tuple form is lex-ordered: `decreases(a, b)` means `(a, b)` strictly decreases lexicographically.

`do` loops place the clauses between the trailing condition and its semicolon:

```cpp
do {
    i = i + 1;
} while (i < n)
  invariant(i >= 1 && i <= n)
  decreases(n - i);
```

The body executes once before invariant establishment. CppVerify verifies that
mandatory execution from the concrete incoming state, establishes the invariant
after it, and then applies the ordinary modular `while` rule to every subsequent
iteration. `old(expr)` in any loop invariant denotes the enclosing function's
entry state, not the previous iteration. A function local has no value at
function entry and is rejected inside `old(...)`; snapshot such a value in an
ordinary local and refer to that snapshot without `old`.

`return`, `break`, and `continue` may leave a `while` or `for` loop from an
arbitrary inductive iteration. A return checks the postcondition in its own
state, a break continues after the loop in its own state, and a continue ends
the iteration: it re-establishes the invariant and decreases the measure, after
running a `for` increment. `break` and `continue` in a `do` loop, whose first
iteration is lowered outside the loop, and ghost code leaving an executable
loop fail closed.

## Assertions: contract_assert

```cpp
contract_assert(x > 0);
```

- Generates a verification condition (not a runtime check).
- In ghost blocks, used for proof steps.

## Ghost Blocks

```cpp
ghost {
    lemma_fibo_monotonic(i, n);
    contract_assert(fibo(i) <= fibo(n));
    reveal_with_fuel(fibo, 3);
}
```

- Code inside `ghost { }` exists only for verification.
- May contain `contract_assert`, `reveal_with_fuel`, spec/proof function calls, ghost variable declarations.
- May assign only ghost-local variables and their direct dot-fields; executable
  locals, globals, pointees, executable calls, and enclosing-function returns
  are rejected.
- Ghost loops require `decreases`, because the loop is absent at runtime.
- Stripped entirely by CodeGen — zero runtime cost.

## Spec Functions

```cpp
spec int fibo(int n)
  decreases(n)
{
    if (n == 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}
```

- Pure mathematical functions used in contracts.
- Usable only in contracts, ghost code, and other `spec` or `proof`
  functions. A spec is never compiled, so Sema rejects a reference from
  executable code (a body, initializer, or default argument).
- Must be total (all paths return, termination proven via `decreases`).
- No side effects, no mutation, no I/O. A spec may read memory through its
  pointer parameters but never write it; each call is evaluated in the heap
  state a load at that point would read (the current state, the entry state
  inside `old(...)`, or the call-site state of a callee contract).
- Can be recursive (with `decreases`).
- **Integer semantics: mathematical (unbounded `Int` in Z3) by default.** See §Integer Semantics.
- Body is interpreted by the verifier as an axiom; not compiled.
- Can call other spec functions.
- Type-checked by Clang Sema like normal functions.

**Why termination must be verified:** A non-terminating spec function introduces a logical contradiction — Z3 can derive `bad(0) == bad(0) + 1`, therefore `0 == 1`, and from that prove anything. The `decreases` clause is the only thing about a spec function that needs verification. Its body is the mathematical definition and is axiomatically true by construction. Non-recursive spec functions need no verification at all.

### `recommends` — soft preconditions for spec functions

```cpp
spec int safe_div(int a, int b)
  recommends(b != 0)
{
    return a / b;
}
```

- `recommends` clauses do **not** generate VCs at call sites. Spec functions remain total.
- They are checked only on verification failure of any function calling the spec, and reported as warnings.
- Cheap UX recovery — gives users feedback that they probably misused a spec function without imposing real preconditions.

## `constexpr` Functions as Automatic Spec Functions

```cpp
constexpr bool is_power_of_two(int n) {
    return n > 0 && (n & (n - 1)) == 0;
}

void allocate(int n)
  pre(is_power_of_two(n))
{ ... }
```

Any uncontracted `constexpr` definition is automatically available as a spec
function — no `spec` keyword or re-declaration. A `constexpr` function with
`pre`/`post` clauses remains a modular executable function so its contract
cannot be bypassed through implicit lifting.

**Soundness:** Clang enforces the restrictions on a `constexpr` definition.
CppVerify additionally unfolds symbolic calls for path-sensitive C++ definedness
and uses finite call-site equations, so recursive calls do not introduce an
unbounded self-triggering axiom.

**Integer semantics — machine integers:** A lifted `constexpr` function
retains C++ integer semantics — `int` has its target width, unsigned arithmetic
wraps, and signed overflow is undefined. The verifier uses machine-integer
values but unfolds the function into the path-sensitive definedness checker at every call;
an overflowing call is rejected rather than interpreted as signed wraparound.
For C++17 signed left shift, a nonnegative value may set the sign bit when the
shifted mathematical value fits the corresponding unsigned type.

**Contrast with explicit `spec`:** `spec int fibo(int n)` uses mathematical integers (Z3 `Int`, unbounded). Users pick:
- Want fast verification with abstract math semantics → write `spec`.
- Want code reuse with runtime-honest semantics → write `constexpr` (and accept the machine-integer encoding cost).

Calls in contract expressions retain the callee's integer semantics: a
mathematical spec result stays unbounded, operations involving it are exact,
and the implicit usual arithmetic conversions do not bound it. A mathematical
value never wraps into a machine type. Storing it in a ghost or proof variable,
passing it to a lifted `constexpr` parameter, casting it explicitly, or using
it as a bitwise operand converts it, and that conversion carries an `overflow`
obligation that the value fits.

This is genuinely a CppVerify advantage over Verus — Verus forces users to maintain two separate bodies; we let one body do double duty *or* let users opt into a clean math-integer spec.

**Compile-time partial evaluation:** When a contract contains a `constexpr` call with all-concrete arguments, Clang evaluates it at compile time before the verifier sees it:

```cpp
write_data(buf, 512);
// At this call site, Clang evaluates is_power_of_two(512) → true.
// Z3 receives pre(true) for this site — no SMT reasoning needed.
```

This is unique to being inside the compiler.

## Proof Functions

```cpp
proof void lemma_fibo_monotonic(int i, int j)
  pre(i <= j)
  post(fibo(i) <= fibo(j))
  decreases(j - i)
{
    if (i < 2 && j < 2) {
    } else if (i == j) {
    } else if (i == j - 1) {
        lemma_fibo_monotonic(i, j - 1);
    } else {
        lemma_fibo_monotonic(i, j - 1);
        lemma_fibo_monotonic(i, j - 2);
    }
}
```

- Ghost functions that serve as proofs.
- Must terminate (proven via `decreases`).
- Body establishes that precondition implies postcondition.
- Can call other proof functions and spec functions.
- May mutate local proof values, but cannot write executable memory/global
  state or call executable functions.
- Every proof-function loop requires `decreases`.
- Not compiled — exist only for verification.
- **Integer semantics:** machine integers (matches `exec`).

## Quantifiers: forall / exists (bounded)

```cpp
post(forall(i, 2, n, ret[i] == ret[i-1] + ret[i-2]))
//   forall(binder, lo, hi, body)
//   means: ∀i. lo ≤ i < hi → body

pre(exists(j, 0, n, arr[j] == target))
//   means: ∃j. 0 ≤ j < n ∧ body
```

- **MVP supports bounded quantifiers only.** The `[lo, hi)` range acts as the implicit Z3 trigger — no manual trigger annotation needed.
- `binder` is a fresh variable of type `int` (mathematical, unbounded), scoped to `body`.
- `lo` and `hi` must be integer; `body` must be bool.
- Post-MVP: unbounded `forall(i: T, body)` with optional explicit trigger syntax.

## Pointers and Memory

CppVerify supports verification of pointer-manipulating code in the MVP via three coupled mechanisms.

### 1. Heap model

The verifier represents memory as a Z3 array (the "heap"). Pointer dereferences become array operations:

- `*p = v` → conceptually `mem' = store(mem, p, v)`
- `*p` (read) → `select(mem, p)`

This is internal to the verifier — users never write the heap directly. Aliasing correctness comes for free from Z3's array theory: if `p == q`, then `select(mem, p) == select(mem, q)`.

Pointer addition/subtraction and array subscripting use mathematical target-byte
addresses, so address arithmetic itself cannot wrap. A typed `T*` step is
multiplied by Clang's target `sizeof(T)` and record fields add their target
byte-layout offset. The supported buffer fragment includes `p + i`, `p - i`,
`*(p + i)`, and `p[i]`. Executable pointer-pointer subtraction is additionally
supported for same-array positions. A `valid(p, n)` extent admits compositional
positions in `[0, n]`, including one-past; without an extent, direct abstract
and represented scalar-dynamic pointers retain only base and one-past
complete-object positions. Operands must share either one syntactic abstract
base or one concrete local lifetime identity. The target-byte difference is
divided by `sizeof(T)`, proved representable by target `ptrdiff_t`, and then
materialized as a machine value. Stored/indirect positions, equal-address
distinct abstract bases, subtraction inside explicit specs or lifted
`constexpr` functions, pointer compound assignment, and forged pointer/integer
casts remain rejected.

At modular calls, a callee `valid(q, length)` extent can be instantiated from
`q = p + offset` only after proving a same-root nonnegative subrange with
`offset + length <= n`. Empty one-past slices, acyclic read-only forwarding,
and exact-cell slice writes are supported. Symbolic finite write ranges and
unbounded region effects through a proper sub-slice remain fail-closed.

For direct local scalar `new`/`delete`, the value heap is accompanied by
SSA-versioned metadata maps:

- address → allocation lifetime identity;
- allocation identity → numeric base, live/dead, target size, and target
  alignment;
- allocation identity → issued/not-issued, so a dead lifetime token is never
  reused;
- address → initialized/uninitialized.

Ordinary throwing scalar `new` chooses a non-null aligned base whose target-byte
range has no live owner, records the metadata, and initializes the value only
when C++ initialization does. A read requires current liveness and
initialization. Each supported local pointer has an SSA provenance companion
that retains its producing lifetime identity. Matching-pointee copies,
reassignment, conditional selection, and `nullptr` update address and
provenance together. A store requires the byte owner to match the current
companion and marks owned storage initialized. `delete` requires null or the
matching direct live allocation base and ends the identity in a fresh liveness
version. This permits numeric-address reuse without contradictory timeless
validity assumptions or revival of a dangling pointer, and proves simultaneous
allocations disjoint.

The direct allocation boundary covers complete non-volatile integer/enum
objects up to 256 target bytes, direct local pointer initialization,
same-pointee local copies/reassignment/conditionals/null, direct
dereference/store/delete, and equality/null observation. Aliases retain the
same identity, so deletion through any alias invalidates all of them.
Type-erasing or indirect copies, arithmetic-derived ownership, arrays,
placement/nothrow allocation, non-trivial objects, pointer reassignment in
loops, and allocation/deallocation inside loops fail closed.

A checked modular interface admits a direct dynamic pointer argument to a
verified, non-allocating executable callee with a matching scalar pointer
parameter. Identity is substituted into call-site validity checks, and
ordinary pre/`modifies`/post abstraction controls the value heap. A recursive
VCR scan admits direct scalar access, acyclic direct-pointer forwarding, and
executable/spec helpers over loaded scalar values. It rejects offset/subscript
access, pointer copies/rebinding, deallocation, recursive scan cycles, nested
pointer-result calls, ghost use, proof/external contracts, and other ways the
scalar identity or extent could be lost.

Direct/conditional/null returns of dynamic formals are supported. The modular
call freshens address and provenance result targets together; generated
validity binds the provenance to the byte owner, while an explicit result
equality relates the returned address to a caller argument. Frame containment
and subsequent modular writes additionally require that provenance to equal an
identity in the caller's owned-allocation set. A foreign or weakly specified
result therefore cannot manufacture ownership merely by being assigned to a
previously dynamic local.

VCR also carries an inferred `FreshOwnedReturn` effect for a narrow factory
boundary. The effect is never accepted from contract text. A body-present,
non-external, non-proof executable function receives it only when a
conservative acyclic VCR analysis proves that every path returns null or the
exact live base of its sole fresh scalar allocation, fully initialized, with
no pointer parameter, secondary escape, explicit frame, arithmetic-derived
result, extra allocation, or intervening unsupported call. A direct store may
complete initialization. Calls to an already inferred factory can be returned
directly or through matching local aliases, so factory forwarding composes
only along an acyclic call graph.

At such a call, passivization creates a never-issued lifetime identity and a
fresh pointer result, proves target alignment and disjointness from all live
represented storage and declared extents, installs base/size/alignment,
byte-owner, liveness, and initialization metadata, and changes only the new
scalar cell in the value heap. A nullable summary guards those updates. The
callee's ordinary postconditions still specify null correlation and the
pointee value; ownership inference supplies lifetime authority, not an
unstated functional result. The caller may mutate and delete the result, while
double delete and every stale alias remain rejected.

On the Z3, cvc5, portfolio, BMC, and Lean paths, `--check-ub` recognizes a conventional
`valid(p, n)` spec call in a precondition as a buffer extent. It entails
`n >= 0`; a positive extent entails non-null abstractly valid storage, while
extent zero permits null. Every access rooted at `p` must then prove its index
lies in `[0, n)`. Modular sub-slices prove nonnegative containment, and pointer
difference positions prove the inclusive one-past range `[0, n]`. Core
arithmetic, division, shift, and dereference definedness remain mandatory
without the option.

The marker must be a positive top-level conjunction clause on a bare pointer to
a complete object type. At most one marker may describe each pointer. Shifted,
disjunctive, conditional, or duplicate markers fail closed rather than creating
unconditional extent assumptions.

### 2. Implicit non-aliasing default

When a function has multiple mutable address parameters, the verifier
*implicitly* assumes their complete object ranges do not overlap at function
entry. Address parameters currently include raw pointers and supported scalar
lvalue references.

```
pre(p != q && p != r && q != r && ...)   // for all distinct mut ptr/ref pairs
```

- The caller's verification must establish these inequalities. Calling `swap(&x, &x)` produces a precondition failure.
- With `--check-ub`, a pointer carrying a `valid(p, n)` extent contributes the
  whole extent (`n * sizeof(T)` bytes) as its complete object, so the pair is
  disjoint unless either pointer is null or either extent is empty. Callers
  prove disjointness of the extents they pass. An `aliases` pair keeps the
  single-object rule and may share storage, as `memmove` does.
- **This is NOT the C++ `__restrict__` keyword.** `__restrict__` is a compiler optimization hint affecting codegen; the implicit assumption above is a verification-level precondition affecting correctness. The keyword `__restrict__`, if present, is a no-op for verification.

### 3. `aliases(p, q)` opt-out

If a function legitimately accepts aliased parameters, declare it:

```cpp
void copy_or_self(int* dst, int* src)
  aliases(dst, src)
  pre(dst != nullptr && src != nullptr)
  modifies(*dst)
  post(*dst == old(*src))
{
    *dst = *src;
}
```

The `aliases(dst, src)` clause disables the implicit `dst != src` precondition
for this function. The body must verify under both `dst == src` and `dst != src`.
The same rule applies to supported scalar lvalue-reference parameters.

### 3a. Scalar lvalue references and automatic scalar objects

Contracted executable free functions support `T&` and `const T&` parameters
when `T` is `bool`, integral, or enum. The reference binding lowers to an
immutable VCR address. A value use is a heap load, assignment is a heap store,
and `old(ref)` reads through the same address in the entry heap.

Every reference receives a generated non-null, live, and initialized entry
precondition. Distinct address parameters are object-range disjoint by default
when at least one is mutable; `aliases` permits the same complete object.
`modifies(ref)` is an open region rooted at the referent, matching
`modifies(*p)`.

A reference formal may bind to another supported reference, an initialized
ordinary scalar local, or a direct pointer dereference. Local `T&`/`const T&`
declarations may bind the same direct forms, may chain through other local
references, and snapshot a raw pointer's address at the declaration. Reassigning
that pointer therefore does not rebind the reference.

Only locals whose addresses are needed are spilled out of scalar SSA. Each such
local becomes an automatic `VAllocateStmt` with a fresh lifetime identity,
target size/alignment, byte ownership, liveness, and initialization metadata.
It is disjoint from incoming address parameters and every simultaneously live
allocation. All reads and writes then use heap loads/stores; a defensive VCR
check rejects accidental scalar use of the same local. Lifetime is
conservatively extended to function return, which is unobservable under the
non-escaping boundary.

A provenance-backed scalar actual permits an open-region `modifies(ref)` or
`modifies(*p)` footprint to be framed as its exact scalar cell only after the
callee passes the structural non-escape scan. Immutable local reference aliases
are tracked transitively by that scan and retain the same owned lifetime
identity.

Addressable local declarations inside loops, `old(local)`, `old(local_ref)`,
subscript/field/conditional bindings, temporaries, reference returns,
address-taking, rvalue references, and non-scalar referents remain fail-closed.
An outer automatic local and a local reference declaration may be used inside a
loop. Recursive executable bodies that allocate an automatic object or store
through references fail closed until the termination collector models heap
state updates.

### 4. `modifies(...)` frame condition

```cpp
void incr_first(int* a, int* b)
  modifies(*a)              // promises: only writes to *a; *b unchanged
  post(*a == old(*a) + 1)
{
    *a = *a + 1;
}
```

- `modifies(X, Y, Z)` lists every lvalue the function may write to. Anything not listed is preserved.
- Default if absent:
  - Pure-typed functions (no pointers) modify nothing.
  - Functions with mutable pointer/reference address parameters are treated as
    potentially modifying reachable heap state at modular calls (conservative).
- Users write `modifies(...)` to narrow the default.
- Heap lvalue forms supported: scalar `ref`, `*p`, `p->field`, and `p[i]`.
- `modifies(*p)` is a region permission inside the callee. At a modular call,
  the restricted direct-scalar dynamic boundary recognizes caller-owned
  storage. Other parameter-pointer calls conservatively havoc the whole value
  heap and recover only the callee's postconditions.
- A no-`modifies` address-parameter callee has the same conservative heap
  effect. It cannot fit inside an explicit caller frame; an unframed caller can
  use its own address parameters or checked caller-owned scalar allocations.
- `modifies(p->field)` and `modifies(p[i])` are exact-address footprints and
  preserve every other address. Entry-state frame containment prevents pointer
  reassignment from expanding the declared frame.
- Preconditions and `old(parameter)` use entry actual arguments. A plain
  by-value parameter in a postcondition uses a fresh final value when the
  callee syntactically reassigns that local parameter or flattened field.
- General reference binding and member-function effects are not yet in the
  verified subset.

### Worked example

```cpp
void swap(int* a, int* b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}

int compute() {
    int x = 5;
    int y = 10;
    int z = 100;
    swap(&x, &y);
    // Verifier knows:
    //  - x and y are non-aliased (implicit default) OK
    //  - swap modified only *(&x) and *(&y)
    //  - therefore z is unchanged
    contract_assert(z == 100);          // verifies
    contract_assert(x == 10 && y == 5); // verifies from post
    return x + y + z;
}
```

## Type Invariants

```cpp
class Coordinate {
    int x;
    int y;
    type_invariant(x >= 0 && y >= 0);   // must appear after the fields it names
};

int dist_sq(Coordinate p, Coordinate q) {
    // Verifier auto-injects (lazy — only because the body accesses .x and .y):
    //   assume(p.x >= 0 && p.y >= 0);
    //   assume(q.x >= 0 && q.y >= 0);
    int dx = p.x - q.x;
    int dy = p.y - q.y;
    return dx*dx + dy*dy;
}
```

- `type_invariant(expr)`: holds for every instance of the type at all times.
- `expr` may reference any field of the enclosing type by name.
- Must be contextually convertible to bool.

### Lazy injection

The verifier injects assume/assert only where they matter:

- `assume(invariant)` at the *first use* of an invariant-named field within a function body — not blindly at the function entry. A function that takes a `Coordinate` parameter but never reads `c.x` or `c.y` gets no injection.
- `assert(invariant_holds_after_assignment)` after assignments to fields named in the invariant — not after every assignment.
- Return values of invariant-bearing types: `assert(invariant)` at every return point that constructs a value of that type.

This is purely an optimization — correctness is identical to eager injection. The win is that VCs stay tight on large structs and rarely-touched fields.

### Status

- Parser: implemented in Weeks 4.5 (after Weeks 3-4 core IR).
- New keyword `type_invariant` in `TokenKinds.def` under KEYCONTRACT.
- `TypeContractInfo` side table on `RecordDecl` in `ASTContext`.
- The clause must appear **after** the fields it names (it is parsed eagerly;
  late parsing is future work).
- Implemented: `assume(invariant)` at the first use of an invariant-named field
  for by-value flat-record parameters. Because the
  invariant is injected as a precondition, callers must *establish* it at call
  sites (the modular precondition check), which is sound.
- Implemented: `assert(invariant)` at every `return s;` where `s` is a struct
  variable of an invariant-bearing type. The invariant is checked over `s`'s
  fields just before the return, so a function that constructs and returns a
  struct violating its invariant is rejected. Struct construction/mutation/return
  is modelled by the backend (field stores become `var.field` SSA assignments).
- By design, the invariant is **not** asserted after each individual field write.
  Asserting the whole invariant mid-construction would spuriously fail while a
  multi-field struct is being initialised one field at a time (the other fields
  are still unconstrained). The return (the encapsulation boundary) is the
  checkpoint — matching how Dafny/Verus check constructors.
- Pointer-to-record parameters are not injected (their field access lowers to a
  heap Load).

## View Functions (idiomatic spec abstraction)

When verifying code over a concrete data structure, define `spec` functions that produce a mathematical view of the data. Specs are then written against the view, not the internals.

```cpp
class SortedArray {
    int data[100];
    int len;
};

// abstract view: what the structure means mathematically
spec int elem(SortedArray a, int i) { return a.data[i]; }
spec int size(SortedArray a) { return a.len; }

bool contains(SortedArray a, int target)
  pre(size(a) > 0 && size(a) <= 100)
  post(result == exists(i, 0, size(a), elem(a, i) == target))
{ ... }
```

- No new syntax. `spec` functions named `view()`, `elem()`, `size()`, etc. are a documented convention.
- The verifier treats these spec function bodies as axioms (definitions), not as code to execute.
- This is Verus's main abstraction idiom and the recommended style for non-trivial data structures.

## Integer Semantics — summary

| Function kind | Integer semantics | Solver encoding |
|---|---|---|
| `spec` function (explicit) | Mathematical (unbounded) | `Int` |
| `constexpr` lifted as spec | Machine (overflow happens) | `BitVec(N)` or range-checked `Int` |
| `proof` function | Machine | `BitVec(N)` or range-checked `Int` |
| `exec` (regular) function | Machine | `BitVec(N)` or range-checked `Int` |

- Conversion at boundaries is explicit. Machine to mathematical is exact.
  Mathematical to machine (materialization in ghost or proof code, a machine
  parameter, an explicit cast, or a bitwise operand) is an `overflow`
  obligation that the value fits; it never wraps. Implicit C++ conversions in
  contracts keep a mathematical value unbounded.
- Mathematical `spec` division and remainder are unbounded but use C++'s
  truncate-toward-zero sign convention. At a zero divisor their total logical
  extension is quotient zero and remainder equal to the dividend; evaluated
  executable and contract expressions must still prove a nonzero divisor.
- `--int-encoding` selects how machine integers reach the solver: `auto`
  (default; integers unless a query needs the bits of a non-constant
  operand), `integer`, or `bitvector`. Every choice is exact, so it changes
  solver performance, never semantics.

## old() Expression

```cpp
post(result == old(x) + 1)
post(result == old(*p))
```

- Refers to the value of an expression at function entry.
- Valid in postconditions and loop invariants. In either location it denotes
  the enclosing function's entry state, not the previous iteration.
- The inner expression is evaluated in the pre-state. For pointer-typed expressions, `old(*p)` is the value at the pre-state heap.

## result Expression

```cpp
post(result > 0)
post(result.size() == n)
```

- Refers to the return value of the enclosing function.
- Only valid in postconditions.
- Type is computed via `Sema::GetTypeForDeclarator` from the full Declarator.
- Supports postfix operators: `result.x`, `result[i]`.

## reveal_with_fuel (control recursive spec unfolding)

```cpp
spec int fibo(int n) decreases(n) { ... }

int safe_fib(int n) pre(...) post(result == fibo(n)) {
    ghost {
        reveal_with_fuel(fibo, 5);  // unfold fibo up to 5 levels in this VC
    }
    ...
}
```

- Default fuel for any recursive spec: **1**.
- `reveal_with_fuel(fn, n)` locally raises the unfolding depth Z3 uses for `fn` within the enclosing function's VC.
- Without this, recursive `spec` axioms cause Z3 matching loops.
- Inside ghost blocks only.

## hide / reveal

- `hide(fn_name)` and `reveal(fn_name)` in ghost blocks selectively control whether the body of a spec function is visible to Z3.
- Default for non-recursive specs: visible (body inlined into queries).
- Default for recursive specs: one finite unfolding step. Deeper unfolding
  requires `reveal_with_fuel`.
- `hide` suppresses defining equations while leaving the function application
  available to contracts and imported lemma postconditions. This is useful
  after a finite lemma has established all facts needed by a large arithmetic
  proof: irrelevant recursive equations can otherwise dominate solver time.
- Both constructs are implemented and are verification-only no-ops in CodeGen.

## choose (Hilbert ε — post-MVP)

- Documented as future work. Useful for spec functions that need "some witness" semantics.

## Clang Modification Details

### New Keywords (TokenKinds.def — KEYCONTRACT)

```
KEYWORD(pre,              KEYCONTRACT)
KEYWORD(post,             KEYCONTRACT)
KEYWORD(modifies,         KEYCONTRACT)
KEYWORD(aliases,          KEYCONTRACT)
KEYWORD(recommends,       KEYCONTRACT)
KEYWORD(invariant,        KEYCONTRACT)
KEYWORD(decreases,        KEYCONTRACT)
KEYWORD(type_invariant,   KEYCONTRACT)
KEYWORD(ghost,            KEYCONTRACT)
KEYWORD(spec,             KEYCONTRACT)
KEYWORD(proof,            KEYCONTRACT)
KEYWORD(contract_assert,  KEYCONTRACT)
KEYWORD(reveal_with_fuel, KEYCONTRACT)
KEYWORD(forall,           KEYCONTRACT)
KEYWORD(exists,           KEYCONTRACT)
KEYWORD(old,              KEYCONTRACT)
KEYWORD(result,           KEYCONTRACT)
```

KEYCONTRACT flag: only active when `-fverify-contracts` is passed. Otherwise these are valid identifiers.

### AST Nodes

**Expressions (inherit from Expr):**

| Node | Fields | Type |
|---|---|---|
| ForallExpr | BoundVar, Lo, Hi, Body | BoolTy |
| ExistsExpr | BoundVar, Lo, Hi, Body | BoolTy |
| OldExpr | Inner | Inner->getType() |
| ResultExpr | — | enclosing function's return type |

**Statements (inherit from Stmt):**

| Node | Fields |
|---|---|
| ContractAssertStmt | Expr (the condition) |
| GhostBlockStmt | CompoundStmt (the body) |
| RevealWithFuelStmt | FunctionDecl* fn, int fuel |

**Side-table info on existing nodes:**

| Existing Node | New Data |
|---|---|
| FunctionDecl (via ASTContext side table) | preconditions, postconditions, modifies, aliases, recommends, isSpec, isProof, decreases |
| WhileStmt / ForStmt | invariants, decreases |
| RecordDecl | type_invariants |

### Parser Entry Points

| Syntax Position | Parser Method | File |
|---|---|---|
| After function declarator `)` | ParseContractClauses() | ParseDecl.cpp |
| After a while/for condition or a do-loop trailing condition | ParseLoopContracts() | ParseStmt.cpp |
| `ghost { ... }` | ParseGhostBlock() | ParseStmt.cpp |
| `contract_assert(...)` | ParseContractAssert() | ParseStmt.cpp |
| `reveal_with_fuel(...)` | ParseRevealWithFuel() | ParseStmt.cpp |
| `spec type name(...)` | ParseSpecFunction() | ParseDecl.cpp |
| `proof void name(...)` | ParseProofFunction() | ParseDecl.cpp |
| `forall(...)` / `exists(...)` | ParseQuantifierExpr() | ParseExpr.cpp |
| `old(...)` | ParseOldExpr() | ParseExpr.cpp |
| `result` | ParseResultExpr() | ParseExpr.cpp |
| `type_invariant(...)` inside record | ParseTypeInvariant() | ParseDecl.cpp |

### Sema Rules

1. All contract expressions must be contextually convertible to bool (except `decreases` which must be integer; and `modifies` lvalues which need ordinary lvalue typing).
2. `old(expr)` is only valid in postconditions and loop invariants; both use
   the enclosing function's entry state.
3. `result` is only valid in postconditions. Its type matches the enclosing function's return type.
4. Quantifier binders are pushed into scope during body type-checking, popped after.
5. Spec functions must have no side effects (no assignments to non-local state, no I/O calls).
6. Proof functions must return void.
7. Ghost blocks may only contain ghost-safe statements. They can update
   ghost-local variables/direct dot-fields and call proof functions, but cannot
   mutate executable state, call executable functions, return from the
   enclosing function, or contain a loop without `decreases`.
8. `modifies` lvalues must be ordinary lvalues; the parser computes their alias keys for the encoder.
9. `aliases(p, q)` arguments must be pointer/reference-typed parameters of the enclosing function.
10. `recommends` is only valid on `spec` functions.
11. A `spec` function may be referenced only from contracts, ghost code, and
    `spec` or `proof` functions; executable code, including initializers and
    default arguments, may not reference one. Unevaluated operands
    (`sizeof`, `decltype`) are exempt.

### CodeGen Rules

- `GhostBlockStmt` → emit nothing
- `ContractAssertStmt` → emit nothing (or optionally emit runtime assert in debug mode)
- `RevealWithFuelStmt` → emit nothing
- Functions with `isSpec` or `isProof` → skip entirely (already gated in CodeGenModule)
- All contract clauses on FunctionDecl → ignored by codegen
- Loop invariants/decreases → ignored by codegen
- `type_invariant` on RecordDecl → ignored by codegen

## Backend-Neutral Obligation Contract

CppVerify lowers C++ semantics exactly once:

```
Clang AST -> typed VCR -> passive SSA -> ObligationModule -> backend adapter
```

`ObligationModule` is the production/research boundary. It contains matching
direct correctness and counterexample terms, deterministic internal IDs,
source-anchored public IDs named by a precise obligation kind (such as
`precondition`, `invariant-preserved`, `overflow`, `bounds`, `aliasing`, or
`unwinding`), inclusive source
ranges, original-name typed model metadata, guarded diagnostic trace events,
required logic features, equivalent ordered queries, and owned typed
logical-function declarations with compact step definitions and exact finite
fuel levels. Layer 3 dumps this exact module; Layer 4 and ordinary verification
encode the same in-memory object. There is no separate dump-only
weakest-precondition implementation and no backend may borrow VCR declarations.

Diagnostic metadata is non-semantic: names, source ranges, internal positional
and public source-anchored IDs, and trace events survive archive replay but do
not change semantic hashes. Model and trace
evaluation never requests Z3 model completion. Undetermined values remain
unknown, false-guarded events are omitted, and undetermined guards remain
explicitly unknown rather than selecting a path.

The consumer header contains no VCR/passive types. Canonical integer sorts own
signedness and the originating C++ width needed by explicit
machine/mathematical conversions; backend adapters derive all representation
choices from those sorts.

Module construction is fail-closed. Null, unsupported, malformed, or untyped
terms return an error before backend dispatch. Every free symbol, including
diagnostic model and trace expressions, has one module-wide logic sort.
Conflicting reuse is rejected before a solver can observe it. Every backend
declares supported logical features; a missing capability yields `unknown`,
never an approximation.

Before publication or dispatch, a shared fail-closed canonicalizer applies a
deliberately narrow set of semantics-preserving rewrites: Boolean constants,
double negation, constant conditionals, and reflexive equality/inequality. It
simplifies logical definitions, removes declarations unreachable transitively
from the ordered goals, rebuilds exact per-obligation and complete
goal/counterexample pairs, recomputes features, and revalidates. The same step
runs after archive decoding, so adapters never depend on producer-specific
dead declarations or trivial Boolean structure. It does not rewrite
arithmetic, quantifiers, pointer/heap expressions, or assumptions.

`--obligation-out=FILE` publishes deterministic, concatenable
`cppverify.obligation/2` binary records with stable wire tags and portable
source attribution; schema v1 records remain readable. Publication includes an
exact serialize/deserialize/validate/reserialize check. SHA-256 module and
per-obligation semantic hashes exclude source paths, display-only names, both
positional and source-anchored obligation IDs, and every obligation kind except
`unwinding`; individual hashes include the transitive logical declarations
reachable from that goal. Their format version is independent of the archive
wire version. Canonicalization introduced semantic-hash format v2, excluding
diagnostic identities advanced it to v3, and excluding diagnostic kinds
advances it to v4.
`--obligation-in=FILE` validates and replays the records through Z3, cvc5,
strict Z3+cvc5 portfolio, lower-only/Layer 3-4 dumps, or Lean scratch export
without reparsing C++.
BMC-produced records carry their unroll bound in semantics and replay through
the BMC result aggregator; untransformed records cannot acquire BMC semantics
after this boundary. Lean scratch replay of bounded records is rejected.
Failure-only `recommends` diagnostics do not alter archive contents.
Imported records are untrusted input: bounded parsing precedes structural,
scope, sort, signature, feature, canonical-payload, exact-negation, and
complete-versus-ordered-goal validation. Module-local finite fuel may differ
across concatenated records, but a reused logical identity must keep the same
parameter and result signature.

Backend results carry stable machine-readable reason codes independently of
their human message: `counterexample`, `solver.timeout`, `solver.unknown`,
`solver.resource-limit`, `solver.unavailable`, `solver.invocation-failed`,
`solver.malformed-output`, `query.size-limit`, `encoding.failed`,
`obligation.invalid`, `logic.unsupported`, `query.missing`,
`backend.invalid-result`, `backend.inconsistent-results`,
`bmc.incomplete-bound`, `lean.export-failed`, `cache.corrupt`,
`cache.io-failed`, and `spec.fuel`.
`--diagnostics-format=json` serializes verification results as versioned JSON
Lines (`cppverify.diagnostic/1`) for both source verification and archive
replay.

Z3-backed ordered obligations may run concurrently under `--jobs=N`. Each task
constructs a distinct Z3 context/solver and results are consumed in canonical
source order, so concurrency cannot choose which failure is public. AST/VCR
lowering, canonicalization, dumps, archive writes, Lean emission, and diagnostic
publication remain serial. `--solver-rlimit` adds a deterministic per-query Z3
budget, while `--max-query-nodes` rejects an oversized canonical module before
verification, lower-only encoding, or a requested Z3 dump; neither limit can
become success.

`--proof-cache=DIR` stores only successful individual proofs. The key binds an
obligation's dependency-scoped semantic hash to hash format v4, the backend
namespace and adapter revision, and the exact Z3 version. Relevant C++ target,
UB, fuel, transform, and bound choices are already represented in the canonical
goal and reachable declarations; BMC additionally has a distinct namespace.
Entries are immutable and atomically installed. Corruption and I/O errors are
reported fail-closed when reading a requested proof, while store/prune errors
after a fresh proof are explicit telemetry and do not replace that verdict.
Pruning still runs after errors, retries capacity-limited writes after eviction,
and removes abandoned atomic-write files after 24 hours. Failed, unresolved,
resource-limited, and `BoundedSafe` results are never stored. Source verification
and archive replay therefore share proofs only when they consume the same
canonical semantics.
The opt-in directory is trusted local memoization, not a proof-object
certificate or an untrusted shared-service boundary; Lean remains the
independently kernel-checked path.

The optional cvc5 adapter independently serializes canonical obligations to
standalone SMT-LIB2. It explicitly reproduces C++ truncate-toward-zero
mathematical division/remainder (including the total zero-divisor extension),
signed/unsigned bit-vector operations and conversions, overflow predicates,
`Array Int Int` heap cells, bounded quantifiers, and only the finite ground spec
equations owned by the module. It runs an installed executable with deterministic
seed/resource options and bounded output; missing tools, invocation failures,
timeouts, `unknown`, extra diagnostics, and malformed tokens are unresolved.

`--backend=portfolio` runs ordered Z3 and cvc5 queries over that same module.
Only `unsat`/`unsat` is `Verified`; only `sat`/`sat` is `Failed`, where cvc5's
`spec.fuel` counts as `sat` beside a Z3 counterexample checked against the spec
definitions; a decisive split is `backend.inconsistent-results`; and an
unresolved side keeps the portfolio unresolved. Agreed failures retain Z3's
typed source model and trace.
The persistent cache, when requested, memoizes only the portfolio's
namespace-separated Z3 component and never skips cvc5. BMC remains Z3-backed,
and bounded archives must replay through the BMC aggregator.

BMC remains a VCR loop transformation followed by the shared passive,
obligation, and Z3 path. Source verification treats `--unroll=N` as a maximum
and explores bounds `0..N` in order. A failed safety query terminates as
`Failed`; complete unwinding terminates as `Verified`; an unresolved query
terminates fail-closed; and a failed unwinding query at `N` is
`BoundedSafe(N)`. Only previously `Verified` dependency-scoped prefix queries
are reused across bounds. Their in-process identity omits the enclosing bound
but includes the exact transformed query and reachable declarations; persistent
cache records retain explicit bound provenance. Terminal source diagnostics
publish explored bounds, reuse counts, and numbered loop-iteration traces.
Archives contain only each function's terminal bounded module and replay that
exact bound without pretending to rerun source-level incremental exploration.

Lean consumes the same module. Standalone output is an unchecked scratch-pad.
Editable project mode pins Lean 4.32.2, overwrites only generated semantics and
the active check module, and preserves reusable user lemmas and one proof file
per stable obligation goal. Initial generation is `Exported`. Certification
compiles the user module and every active proof with `sorry` as an error, then
checks aggregate theorem types and axiom dependencies. Only foundational Lean
axioms are permitted; user `axiom`/`opaque` proof shortcuts, stale proof types,
missing proofs, malformed output, and toolchain failures remain `Unresolved`.
Only complete success is `Certified`.

`--check-ub` extent instrumentation is applied before all Z3, cvc5, portfolio,
BMC, and Lean obligation construction. Direct Lean export and canonical archive
replay therefore name and state the same bounds obligations. The automated
backend fidelity gate also kernel-builds the generated Lean semantics, checks
stable theorem/proof-module identities, compares source and replay exports, and
requires source-identical failed obligations across every automated backend.

The default remains Z3 alone. `--lean-fallback=DIR` is an explicit opt-in that
exports only Z3 `Unresolved` modules; SAT counterexamples remain failures. It
exports only the obligations the solver did not prove individually, reporting
the split (`[z3: 18 of 20 proved; lean: 2 exported]`);
`--lean-fallback-scope=all` exports every obligation. A rerun with
`--lean-certify` can replace those unresolved results only after the preserved
Lean proofs pass the kernel gate: a split result becomes `Proved (z3+lean)`
(JSON `mixed-proof`, with per-obligation evidence), never `Verified`, and only
a complete Lean export becomes `Certified`.

## MVP Acceptance Programs

The MVP gate is implemented as permanent end-to-end regressions rather than a
documentation-only example:

| Program | Proved range | Rejected boundary | Features exercised |
|---|---:|---:|---|
| Factorial | `0..12` | `13!` | mathematical spec, executable recursion, loop invariant, termination, signed multiplication overflow |
| Fibonacci | `0..46` | `F(47)` | mathematical recurrence, proof lemmas, executable recursion, loop invariant, termination, signed addition overflow |
| Framed output | factorial range | null or out-of-frame writes | non-null pointers, `modifies(*out)`, `old(*preserved)`, heap framing |

Both arithmetic programs have recursive and iterative executable
implementations with exact 32-bit signed-`int` contracts. They are proved equal
to unbounded mathematical specifications while every executable operation
retains C++ machine semantics. The first out-of-range operation is deliberately
kept as a negative regression and must be rejected.

The source-of-truth tests are:

- `clang/test/Verify/suite/mvp_factorial.cpp`
- `clang/test/Verify/suite/safe_fib.cpp`

Feature acceptance is layered. Real C++ positive/negative programs establish
user-visible behavior, while `cpp-verify --lower-only --dump-ir=1,2,3,4`
provides solver-independent VCR, passive, VC, and Z3 encoding oracles.
`Lowered` means only that encoding succeeded; only an ordinary backend
`Verified` result certifies the obligations. The executable sweep performs
this lowering preflight for every solver-positive example before invoking its
backend.

This gate established the integer/control-flow/pointer core of the MVP.
Subsequent bounded lifetime checkpoints added scalar `new`/`delete`,
initialized-storage checks, aligned disjoint allocation,
use-after-delete/double-delete rejection, first-class local provenance, and
inferred fresh-owned scalar factory returns. Bounded promoted local objects,
fixed arrays, scalar subobject references, modular slices, and general
same-array pointer difference under `valid(p, n)` are also supported.
Provenance across ownership-taking or recursive interfaces, pointer
reinterpretation/cross-object arithmetic, aggregate/rvalue references,
by-value pointer-bearing records, and general arrays remains unsupported.
