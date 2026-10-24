// REQUIRES: lean
//
// The Lean export means what the obligation module means: each operator is
// printed at its Lean 4 precedence, a quantifier is closed before what follows
// it, a numeral has its type, Booleans are compared as propositions, machine
// division by zero is SMT-LIB's, as in the solvers and the certifier, and a
// definition instance under a quantifier is stated for every value of its
// binders.
//
// RUN: rm -rf %t.export %t.mix %t.numerals %t.call
// RUN: %cpp-verify --backend=lean --lean-project=%t.export %s -- 2>&1 | FileCheck %s --check-prefix=EXPORT
// RUN: %python %S/Inputs/lean_project_text.py %t.export | FileCheck %s --check-prefix=LEAN
// RUN: %python %S/Inputs/lean_project_text.py %t.export | not grep -E 'BitVec\.(udiv|sdiv) '
// RUN: lake --dir=%t.export build CppVerify.Generated
//
// The prelude's values where C++, SMT-LIB, and Lean's own operators differ.
// RUN: cp %S/Inputs/lean_semantics_probe.lean %t.export/CppVerify/Probe.lean
// RUN: lake --dir=%t.export build CppVerify.Probe
//
// A proof that reads `(a ^ b) + 1` as `a ^ (b + 1)` must not certify the
// false check of mix.
// RUN: %cpp-verify --backend=lean --lean-project=%t.mix %S/Inputs/lean_semantics_mix.cpp --
// RUN: cp %S/Inputs/lean_semantics_mix.lean %t.mix/CppVerify/Proofs/cppverify_mix_b839ab/cppverify_mix_b839ab_assertion_255467f3.lean
// RUN: sed -i.orig 's/  sorry/  trivial/' %t.mix/CppVerify/Proofs/cppverify_mix_b839ab/cppverify_mix_b839ab_postcondition_54ae7c80.lean %t.mix/CppVerify/Proofs/cppverify_mix_b839ab/cppverify_mix_b839ab_missing_return_54ae7c80.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.mix --lean-certify %S/Inputs/lean_semantics_mix.cpp -- 2>&1 | FileCheck %s --check-prefix=MIX
//
// A proof that reads `2 - 3` in Nat, where it is 0, must not certify the false
// check of difference.
// RUN: %cpp-verify --backend=lean --lean-project=%t.numerals %S/Inputs/lean_semantics_numerals.cpp --
// RUN: cp %S/Inputs/lean_semantics_numerals.lean %t.numerals/CppVerify/Proofs/cppverify_difference_465d5b/cppverify_difference_465d5b_assertion_d7e0e821.lean
// RUN: sed -i.orig 's/  sorry/  trivial/' %t.numerals/CppVerify/Proofs/cppverify_difference_465d5b/cppverify_difference_465d5b_missing_return_ba8abb90.lean %t.numerals/CppVerify/Proofs/cppverify_difference_465d5b/cppverify_difference_465d5b_postcondition_ba8abb90.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.numerals --lean-certify %S/Inputs/lean_semantics_numerals.cpp -- 2>&1 | FileCheck %s --check-prefix=NUMERALS
//
// A precondition with a quantifier, checked at a call, is certified with
// `decide` on the machine comparison.
// RUN: %cpp-verify --backend=lean --lean-project=%t.call %S/Inputs/lean_semantics_call.cpp --
// RUN: cp %S/Inputs/lean_semantics_call.lean %t.call/CppVerify/Proofs/cppverify_small_74ff94/cppverify_small_74ff94_precondition_4e324fa2.lean
// RUN: sed -i.orig 's/  sorry/  trivial/' %t.call/CppVerify/Proofs/cppverify_nonnegative_5bd01c/cppverify_nonnegative_5bd01c_missing_return_ba8abb90.lean %t.call/CppVerify/Proofs/cppverify_small_74ff94/cppverify_small_74ff94_missing_return_ba8abb90.lean %t.call/CppVerify/Proofs/cppverify_small_74ff94/cppverify_small_74ff94_postcondition_ba8abb90.lean
// RUN: %cpp-verify --backend=lean --lean-project=%t.call --lean-certify %S/Inputs/lean_semantics_call.cpp -- 2>&1 | FileCheck %s --check-prefix=CALL

unsigned mix(unsigned a, unsigned b)
  cppverify::post(true)
{
  unsigned r = (a ^ b) + 1u;
  unsigned s = a ^ (b + 1u);
  cppverify::check(r == s);
  return r;
}

unsigned quotient(unsigned a, unsigned d)
  cppverify::pre(d != 0)
  cppverify::post(cppverify::result == a / d)
{
  return a / d;
}

int signed_quotient(int x, int y)
  cppverify::pre(y != 0 && !(x == -2147483647 - 1 && y == -1))
  cppverify::post(cppverify::result == x / y)
{
  return x / y;
}

int nested(int a, int b, int c)
  cppverify::pre(a > -1000 && a < 1000 && b > -1000 && b < 1000 && c > -1000 && c < 1000)
  cppverify::post(cppverify::result == a - (b - c))
{
  return a - (b - c);
}

int shifted(int x, unsigned s, unsigned t)
  cppverify::pre(s < 8 && t < 8 && x >= 0 && x < 1000)
  cppverify::post(true)
{
  int y = (x >> s) >> t;
  unsigned z = 1u << s;
  return y + (int)z;
}

bool below(int x)
  cppverify::post(cppverify::result == (x < 5))
{
  return x < 5;
}

void flip(bool *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == !cppverify::old(*p))
{
  *p = !*p;
}

bool has_one(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 0)
  cppverify::pre(cppverify::exists(k, 0, n, p[k] == 1 || k == 2))
  cppverify::post(cppverify::result)
{
  return true;
}

int zeros(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 0)
  cppverify::pre(cppverify::forall(k, 0, n, p[k] == 0) && n < 100)
  cppverify::post(cppverify::result == n)
{
  return n;
}

void difference()
  cppverify::post(true)
{
  cppverify::check(2 - 3 < 0);
}

cppverify::spec int total(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : total(n - 1) + n;
}

int totals(int n)
  cppverify::pre(n >= 0 && n < 10)
  cppverify::pre(cppverify::forall(k, 0, n, total(k) >= 0))
  cppverify::post(cppverify::result == n)
{
  return n;
}

// EXPORT: Exported: lean obligation: mix
// EXPORT: Exported: lean obligation: zeros
// EXPORT: Exported: lean obligation: difference
// EXPORT: Exported: lean obligation: totals

// LEAN: abbrev heapSelectBool (h : CppHeap) (p : Int) : Prop := h p ≠ 0
// LEAN: abbrev cppBvUlt {w : Nat} (x y : BitVec w) : Prop := x.ult y = true
// LEAN: abbrev cppBvUle {w : Nat} (x y : BitVec w) : Prop := x.ule y = true
// LEAN: abbrev cppBvSlt {w : Nat} (x y : BitVec w) : Prop := x.slt y = true
// LEAN: abbrev cppBvSle {w : Nat} (x y : BitVec w) : Prop := x.sle y = true
// LEAN: ¬(r_1 = (a_0 ^^^ b_0) + (BitVec.ofInt 32 (1))) ∨ ¬(s_1 = a_0 ^^^ b_0 + (BitVec.ofInt 32 (1))) ∨ r_1 = s_1
// LEAN: ¬(__result_1 = (BitVec.smtUDiv a_0 d_0))
// LEAN: ¬(__result_1 = (BitVec.smtSDiv x_0 y_0))
// LEAN: ¬(__result_1 = a_0 - (b_0 - c_0))
// LEAN: ¬(y_1 = (BitVec.sshiftRight (BitVec.sshiftRight x_0 (s_0).toNat) (t_0).toNat))
// LEAN: ¬(z_1 = (BitVec.ofInt 32 (1)) <<< min (s_0).toNat 32)
// LEAN: ¬(__result_1 ↔ (cppBvSlt x_0 (BitVec.ofInt 32 (5))))
// LEAN: heapStoreBool __heap_0 p_0 (¬(heapSelectBool __heap_0 p_0)) __heap_1
// LEAN: ∃ ([[K:__quant_[a-z0-9_]+]] : Int), {{.*}} ∧ ((heapSelectBv 32 __heap_0 (p_0 + [[K]] * (4 : Int))) = (BitVec.ofInt 32 (1)) ∨ [[K]] = (2 : Int))
// LEAN: ¬((∀ ({{__quant_[a-z0-9_]+}} : Int), {{.*}} = (BitVec.ofInt 32 (0))) ∧ (cppBvSlt n_0 (BitVec.ofInt 32 (100))))
// LEAN: ∨ (2 : Int) - (3 : Int) < (0 : Int)
// LEAN: (cppverify_spec_axiom_1_1 : ∀ ([[T:__quant_[a-z0-9_]+]] : Int), (cppSpec_fn_{{[0-9a-f]+}} [[T]]) = (cppSpecBody_{{[0-9a-f]+}}_fn_{{[0-9a-f]+}}_1 [[T]]))

// MIX: Unresolved: lean obligation: mix (Lean certification failed:
// MIX-NOT: Certified

// NUMERALS: Unresolved: lean obligation: difference (Lean certification failed:
// NUMERALS-NOT: Certified

// CALL: Certified: nonnegative [backend=Lean]
// CALL: Certified: small [backend=Lean]
