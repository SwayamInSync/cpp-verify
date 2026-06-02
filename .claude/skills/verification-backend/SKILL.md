---
name: verification-backend
description: Patterns for the VCGen IR, weakest precondition calculus, Z3 encoding, and counterexample extraction. Use when implementing or modifying the verification pipeline (Layer 1 IR, Layer 2 passivization, wp rules, Z3 integration).
---

# Verification Backend Patterns

## WP Calculus Rules

```
wp(skip, Q)              = Q
wp(x = E, Q)             = Q[x := E]           // substitute E for x in Q
wp(S1; S2, Q)            = wp(S1, wp(S2, Q))   // right to left
wp(assert(P), Q)         = P ∧ Q
wp(assume(P), Q)         = P → Q
wp(havoc(x), Q)          = Q[x := fresh]        // fresh unconstrained var
wp(if(c) S1 else S2, Q)  = (c → wp(S1,Q)) ∧ (¬c → wp(S2,Q))
```

## Loop Desugaring (Layer 1 → Layer 2)

```
while (cond) invariant(I) decreases(D) { body }
```
becomes:
```
assert(I);                    // invariant holds on entry
havoc(modified_vars);         // forget loop-modified variables
assume(I);                    // inductive hypothesis
if (cond) {
    body;                     // one iteration (in SSA)
    assert(I);                // invariant preserved
    assert(D_new < D_old);   // termination
    assert(D_new >= 0);       // measure non-negative
    assume(false);            // cut — inductive step done
} else {
    // continue with I ∧ ¬cond
}
```

## Function Call Desugaring

```
y = f(a, b);   // where f has pre(P) post(Q)
```
becomes:
```
assert(P[params := (a, b)]);                    // prove precondition
havoc(y);                                        // forget result
assume(Q[result := y, old(params) := (a, b)]);  // assume postcondition
```

## SSA Renaming

- Maintain a counter per variable name: `x_0, x_1, x_2, ...`
- At each assignment, increment and create new version
- At if/else merge: `x_merged = cond ? x_true_branch : x_false_branch`
- After havoc: increment to fresh version, add no constraints

## Z3 C++ API Patterns

```cpp
#include <z3++.h>

z3::context ctx;
z3::solver solver(ctx);

// Create sorts
z3::sort int_sort = ctx.int_sort();
z3::sort bool_sort = ctx.bool_sort();
z3::sort bv32_sort = ctx.bv_sort(32);

// Create constants (SSA variables)
z3::expr x_0 = ctx.int_const("x_0");
z3::expr x_1 = ctx.int_const("x_1");

// Build formulas
z3::expr vc = z3::implies(x_0 > 0, x_1 > 1);

// Check validity: VC valid iff ¬VC unsat
solver.add(!vc);
z3::check_result result = solver.check();

if (result == z3::unsat) {
    // Verified!
} else if (result == z3::sat) {
    z3::model m = solver.get_model();
    // Extract counterexample
    z3::expr x0_val = m.eval(x_0);
    // Report: "counterexample: x = " + x0_val.to_string()
} else {
    // Unknown — report honestly
}

// Quantifiers
z3::expr i = ctx.int_const("i");
z3::expr forall_vc = z3::forall(i, 
    z3::implies(i >= 0 && i < n, arr_select(i) >= 0));

// Arrays (for future vector modeling)
z3::sort arr_sort = ctx.array_sort(int_sort, int_sort);
z3::expr arr = ctx.constant("arr", arr_sort);
z3::expr val = z3::select(arr, idx);
z3::expr new_arr = z3::store(arr, idx, new_val);
```

## Spec Function Encoding

Two approaches:
1. **Uninterpreted function + axioms** (default, scales better):
   ```cpp
   z3::func_decl fibo = ctx.function("fibo", int_sort, int_sort);
   // Add defining axioms:
   solver.add(fibo(0) == 0);
   solver.add(fibo(1) == 1);
   solver.add(z3::forall(n, z3::implies(n >= 2, 
       fibo(n) == fibo(n-1) + fibo(n-2))));
   ```
2. **Inline expansion** (simpler for non-recursive specs):
   Just substitute the spec function body at call sites.

## Diagnostics

Map every VExpr/VStmt to a SourceLocation. When a VC fails:
1. Identify which assert generated the failed VC
2. Walk back through the IR to find the originating contract/invariant
3. Extract counterexample values from Z3 model
4. Emit clang-style diagnostic:
   ```
   file.cpp:12:3: error: postcondition may not hold
     post(result > 0)
     ^~~~~~~~~~~~~~~~
     counterexample: x = -5, result = -4
   ```
