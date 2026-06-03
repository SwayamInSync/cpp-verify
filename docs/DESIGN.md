# Contract Syntax & Language Design

## Enabling Contracts

All contract syntax is enabled with `-fverify-contracts`. Without this flag, the new keywords are not reserved and existing C++ code compiles normally.

## Contract Syntax Overview

| Syntax | Where | Meaning |
|---|---|---|
| `pre(expr)` | After function `)` | Precondition — caller must satisfy |
| `post(expr)` | After function `)` | Postcondition — callee must establish; may use `result` and `old(x)` |
| `modifies(lvalue, ...)` | After function `)` | Frame condition — declares the lvalues this function may write to |
| `aliases(p, q)` | After function `)` | Opts out of implicit non-aliasing assumption for the named pointer/reference pair |
| `recommends(expr)` | After function `)` (spec only) | Soft precondition for spec functions; reported on verification failure |
| `invariant(expr)` | After `while`/`for` condition `)` | Loop invariant |
| `decreases(expr [, expr...])` | After loop `)` or function `)` | Termination measure. Tuple form is lex-ordered. |
| `type_invariant(expr)` | Inside class/struct body | Per-instance invariant injected at function boundaries |
| `ghost { ... }` | Statement | Ghost block — proof steps, stripped by CodeGen |
| `contract_assert(expr)` | Statement | Verification condition (not a runtime check) |
| `reveal_with_fuel(fn, n)` | Inside ghost blocks | Locally raise Z3 unfolding depth for spec function `fn` |
| `spec T f(...)` | Declaration | Pure spec function — interpreted by verifier only |
| `proof void f(...)` | Declaration | Ghost proof function — establishes lemmas |
| `forall(i, lo, hi, expr)` | Expression | Bounded universal quantifier |
| `exists(i, lo, hi, expr)` | Expression | Bounded existential quantifier |
| `old(expr)` | Inside `post` | Value of `expr` at function entry |
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
- Must be total (all paths return, termination proven via `decreases`).
- No side effects, no mutation, no I/O.
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

Any `constexpr` function is automatically available as a spec function — no `spec` keyword, no re-declaration.

**Soundness:** Clang's `constexpr` evaluator already enforces purity (no side effects in constant context) and termination (step limit; non-terminating `constexpr` is a compile error). We inherit both guarantees.

**Integer semantics — machine integers:** A lifted `constexpr` function retains C++ integer semantics — `int` is 32-bit, overflow happens, two's-complement wraparound applies (C++20+). The verifier reasons about it in BitVec mode. This is the *honest* choice: `constexpr int fib(int n)` really does overflow at n=47 and the verifier sees that.

**Contrast with explicit `spec`:** `spec int fibo(int n)` uses mathematical integers (Z3 `Int`, unbounded). Users pick:
- Want fast verification with abstract math semantics → write `spec`.
- Want code reuse with runtime-honest semantics → write `constexpr` (and accept the BitVec encoding cost).

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

### 2. Implicit non-aliasing default

When a function has multiple mutable pointer or reference parameters, the verifier *implicitly* assumes they don't alias at function entry. Effectively, the verifier inserts:

```
pre(p != q && p != r && q != r && ...)   // for all distinct mut ptr/ref pairs
```

- The caller's verification must establish these inequalities. Calling `swap(&x, &x)` produces a precondition failure.
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

The `aliases(dst, src)` clause disables the implicit `dst != src` precondition for this function. The body must verify under both `dst == src` and `dst != src`.

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
  - Pure-typed functions (no pointers/references) modify nothing.
  - Functions with mutable pointer/reference parameters implicitly modify everything reachable through those parameters (conservative).
- Users write `modifies(...)` to narrow the default.
- Lvalue forms supported: `*p`, `p->field`, `a[i]`, `obj.field`, `obj.method(...)` (where the method has its own modifies clause).

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
  for by-value and reference (`C`, `C&`, `const C&`) parameters. Because the
  invariant is injected as a precondition, callers must *establish* it at call
  sites (the modular precondition check), which is sound.
- Not yet implemented: the `assert(invariant)` after field assignments and at
  returns that construct an invariant-bearing value. These require verifying
  struct construction/mutation/return, which the backend does not model yet
  (such functions currently report "no verifiable functions"). Pointer-to-record
  parameters are also not injected (their field access lowers to a heap Load).

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

| Function kind | Integer semantics | Z3 encoding |
|---|---|---|
| `spec` function (explicit) | Mathematical (unbounded) | `Int` |
| `constexpr` lifted as spec | Machine (overflow happens) | `BitVec(N)` |
| `proof` function | Machine | `BitVec(N)` |
| `exec` (regular) function | Machine | `BitVec(N)` |

- Conversion at boundaries is explicit (`int` ↔ unbounded `Int` requires a cast that may incur a precondition for fits-in-range).
- Bitvector mode globally forced with `--bv` flag (post-MVP; cast nodes already designed for it).

## old() Expression

```cpp
post(result == old(x) + 1)
post(result == old(*p))
```

- Refers to the value of an expression at function entry.
- Only valid in postconditions and proof blocks.
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

## hide / reveal (post-MVP, designed in)

- `hide(fn_name)` and `reveal(fn_name)` in ghost blocks selectively control whether the body of a spec function is visible to Z3.
- Default for non-recursive specs: visible (body inlined into queries).
- Default for recursive specs: hidden (only revealed via `reveal_with_fuel`).
- Used as a performance lever for large proofs.

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
| After while/for condition `)` | ParseLoopContracts() | ParseStmt.cpp |
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
2. `old(expr)` is only valid in postconditions and proof function bodies.
3. `result` is only valid in postconditions. Its type matches the enclosing function's return type.
4. Quantifier binders are pushed into scope during body type-checking, popped after.
5. Spec functions must have no side effects (no assignments to non-local state, no I/O calls).
6. Proof functions must return void.
7. Ghost blocks may only contain ghost-safe statements (contract_assert, reveal_with_fuel, spec/proof calls, local ghost variable declarations).
8. `modifies` lvalues must be ordinary lvalues; the parser computes their alias keys for the encoder.
9. `aliases(p, q)` arguments must be pointer/reference-typed parameters of the enclosing function.
10. `recommends` is only valid on `spec` functions.

### CodeGen Rules

- `GhostBlockStmt` → emit nothing
- `ContractAssertStmt` → emit nothing (or optionally emit runtime assert in debug mode)
- `RevealWithFuelStmt` → emit nothing
- Functions with `isSpec` or `isProof` → skip entirely (already gated in CodeGenModule)
- All contract clauses on FunctionDecl → ignored by codegen
- Loop invariants/decreases → ignored by codegen
- `type_invariant` on RecordDecl → ignored by codegen

## Example: Full Verified Program (target by end of MVP)

```cpp
spec int fibo(int n)
  decreases(n)
{
    if (n == 0) return 0;
    if (n == 1) return 1;
    return fibo(n - 2) + fibo(n - 1);
}

spec bool fibo_fits_i32(int n) {
    return fibo(n) < 0x7FFFFFFF;
}

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

int safe_fib(int n)
  pre(n >= 0)
  pre(fibo_fits_i32(n))
  post(result == fibo(n))
{
    if (n <= 1) return n;

    int prev = 0;
    int cur = 1;
    int i = 1;

    while (i < n)
      invariant(1 <= i && i < n + 1)
      invariant(cur == fibo(i))
      invariant(prev == fibo(i - 1))
      decreases(n - i)
    {
        ghost {
            reveal_with_fuel(fibo, 2);
            lemma_fibo_monotonic(i, n);
            contract_assert(fibo(i + 1) <= fibo(n));
            contract_assert(fibo(i + 1) < 0x7FFFFFFF);
        }

        int next = cur + prev;
        prev = cur;
        cur = next;
        i = i + 1;
    }
    return cur;
}
```

Compiled normally: `clang++ -std=c++20 fib.cpp -o fib` — contracts ignored, ghost code gone.
Verified: `cpp-verify fib.cpp` — full deductive verification via Z3.
