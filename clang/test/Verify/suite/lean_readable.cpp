// REQUIRES: lean
//
// Each project goal also has a readable form, its assumptions as hypotheses
// named by where they come from, and a bridge from that form to the goal that
// the kernel checks with the generated file. A stub proves the goal through
// it.
//
// RUN: rm -rf %t && mkdir -p %t
// RUN: %cpp-verify --backend=lean --lean-project=%t/p %s -- 2>&1 | FileCheck %s --check-prefix=EXPORT
// RUN: FileCheck %s --input-file=%t/p/CppVerify/Generated.lean
// RUN: FileCheck %s --input-file=%t/p/CppVerify/Proofs/cppverify_twice_edf933/cppverify_twice_edf933_postcondition_28de726e.lean --check-prefix=STUB
// RUN: FileCheck %s --input-file=%t/p/CppVerify/Proofs/cppverify_poly_c94108/cppverify_poly_c94108_postcondition_fde367c1.lean --check-prefix=LETS
// Every stub's names match its readable form: the project builds, with
// nothing admitted but the stubs.
// RUN: cd %t/p && lake build CppVerify.Check 2>&1 | FileCheck %s --check-prefix=STUBS --implicit-check-not=error
//
// Proofs that use the hypotheses by name certify.
// RUN: %cpp-verify --backend=lean --lean-project=%t/c %S/Inputs/lean_readable_certify.cpp -- 2>&1 | FileCheck %s --check-prefix=TRUSTED
// RUN: cp %S/Inputs/lean_readable_proofs/*.lean %t/c/CppVerify/Proofs/cppverify_twice_edf933/
// RUN: %cpp-verify --backend=lean --lean-project=%t/c --lean-certify %S/Inputs/lean_readable_certify.cpp -- 2>&1 | FileCheck %s --check-prefix=CERTIFIED
//
// A readable form that says less than its goal does not build: here the
// definition of b is replaced by the conclusion it should lead to.
// RUN: sed -i 's/(h_b_1 : b_1 = __local_call_2_1)/(h_b_1 : b_1 = x_0 + (BitVec.ofInt 32 (2)))/' %t/p/CppVerify/Generated.lean
// RUN: cd %t/p && not lake build CppVerify.Generated 2>&1 | FileCheck %s --check-prefix=BRIDGE

int next(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int twice(int x)
  cppverify::pre(x >= 0 && x < 50)
  cppverify::post(cppverify::result == x + 2)
{
  int a = next(x);
  int b = next(a);
  return b;
}

int count_up(int n)
  cppverify::pre(n >= 0 && n < 100)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}

void checked(int x)
  cppverify::pre(x > 0)
{
  cppverify::check(x != 0);
  cppverify::check(x >= 1);
}

cppverify::spec int count(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  return n <= 0 ? 0 : count(n - 1) + 1;
}

cppverify::proof void counted(int n)
  cppverify::post(count(n) + 1 > 0)
{
}

int positive(int x)
  cppverify::post(!(x > 0) || cppverify::result > 0)
{
  return x;
}

int read(const int *p)
  cppverify::pre(cppverify::valid(p, 1))
  cppverify::post(cppverify::result == *p)
{
  return *p;
}

int named(int x)
  cppverify::pre(x >= 0 && x < 10)
  cppverify::post(cppverify::result == 2 * x + 1)
{
  int h_x = x + 1;
  x = x + h_x;
  return x;
}

int poly(int x)
  cppverify::pre(x >= 0 && x < 10)
  cppverify::post(cppverify::result == ((x + 1) * (x + 2) + (x + 3) * (x + 4)) * ((x + 5) * (x + 6) + (x + 7) * (x + 8)))
{
  return ((x + 1) * (x + 2) + (x + 3) * (x + 4)) * ((x + 5) * (x + 6) + (x + 7) * (x + 8));
}

[[cppverify::trusted]] int *pick(int *p)
  cppverify::pre(cppverify::valid(p, 1) && *p > 0)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result == p)
  cppverify::post(100 / *p > 0);

// EXPORT: Exported: lean obligation: next
// EXPORT: Exported: lean obligation: twice
// EXPORT: Exported: lean obligation: count_up
// EXPORT: Exported: lean obligation: checked
// EXPORT: Exported: decreases: count
// EXPORT: Exported: lean obligation: counted
// EXPORT: Exported: lean obligation: positive
// EXPORT: Exported: lean obligation: read
// EXPORT: Exported: lean obligation: named
// EXPORT: Exported: lean obligation: poly
// EXPORT: Exported: lean obligation: contract of pick

// CHECK: theorem cppverify_imp_or {a b : Prop} (h : a → b) : ¬a ∨ b :=
// CHECK-NEXT:   (Classical.em a).elim (fun ha => Or.inr (h ha)) Or.inl
// CHECK-NEXT: theorem cppverify_not_imp_or {a b : Prop} (h : ¬a → b) : a ∨ b :=
// CHECK-NEXT:   (Classical.em a).elim Or.inl (fun ha => Or.inr (h ha))

// Calls of one callee are told apart; a definition is named by what it defines.
// CHECK: def cppverify_twice_edf933_postcondition_28de726e.readable : Prop :=
// CHECK: (x_0 : BitVec 32),
// CHECK-NEXT: (h_pre_1 : (cppBvSle (BitVec.ofInt 32 (0)) x_0) ∧ (cppBvSlt x_0 (BitVec.ofInt 32 (50)))) →
// CHECK-NEXT: (h_null_1 : (heapSelectInt __heap_alloc_0 (0 : Int)) = (0 : Int)) →
// CHECK-NEXT: (h_null_2 : ¬(heapSelectBool __heap_live_0 (0 : Int))) →
// CHECK-NEXT: (h_call_next_1 : {{.*}} ∧ __local_call_1_1 = x_0 + (BitVec.ofInt 32 (1))) →
// CHECK-NEXT: (h_a_1 : a_1 = __local_call_1_1) →
// CHECK-NEXT: (h_call_next_2 : {{.*}} ∧ __local_call_2_1 = a_1 + (BitVec.ofInt 32 (1))) →
// CHECK-NEXT: (h_b_1 : b_1 = __local_call_2_1) →
// CHECK-NEXT: (h_result_1 : __result_1 = b_1) →
// CHECK-NEXT: ((x_0).toInt + (2 : Int) ≥ (-2147483648 : Int) ∧ (x_0).toInt + (2 : Int) ≤ (2147483647 : Int)) ∧ __result_1 = x_0 + (BitVec.ofInt 32 (2))
// CHECK-EMPTY:
// CHECK-NEXT: theorem cppverify_twice_edf933_postcondition_28de726e.of_readable (h : cppverify_twice_edf933_postcondition_28de726e.readable) : cppverify_twice_edf933_postcondition_28de726e :=
// CHECK-NEXT:   fun __heap_alloc_0 __heap_live_0 __local_call_1_1 __local_call_2_1 __result_1 a_1 b_1 x_0 =>
// CHECK-NEXT:   cppverify_imp_or fun h_pre_1 =>
// CHECK-NEXT:   cppverify_imp_or fun h_null_1 =>
// CHECK-NEXT:   cppverify_not_imp_or fun h_null_2 =>
// CHECK-NEXT:   cppverify_imp_or fun h_call_next_1 =>
// CHECK-NEXT:   cppverify_imp_or fun h_a_1 =>
// CHECK-NEXT:   cppverify_imp_or fun h_call_next_2 =>
// CHECK-NEXT:   cppverify_imp_or fun h_b_1 =>
// CHECK-NEXT:   cppverify_imp_or fun h_result_1 =>
// CHECK-NEXT:   h __heap_alloc_0 __heap_live_0 __local_call_1_1 __local_call_2_1 __result_1 a_1 b_1 x_0 h_pre_1 h_null_1 h_null_2 h_call_next_1 h_a_1 h_call_next_2 h_b_1 h_result_1

// A loop: its invariant, the condition of an iteration, the exact value of
// a machine operation, the value a path that skips the body keeps, and the
// exit.
// CHECK: def cppverify_count_up_{{[0-9a-f]+}}_postcondition_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_i_1 : i_1 = (BitVec.ofInt 32 (0))) →
// CHECK-NEXT: (h_inv_1 : (cppBvSle (BitVec.ofInt 32 (0)) i_2) ∧ (cppBvSle i_2 n_0)) →
// CHECK-NEXT: (h_cond_1 : ¬__loop_choice_1 ∨ (cppBvSlt i_2 n_0)) →
// CHECK-NEXT: (h_exact_1 : ¬__loop_choice_1 ∨ {{.*}}) →
// CHECK-NEXT: (h_i_3 : ¬__loop_choice_1 ∨ i_3 = i_2 + (BitVec.ofInt 32 (1))) →
// CHECK-NEXT: (h_keep_1 : __loop_choice_1 ∨ i_3 = i_2) →
// CHECK-NEXT: (h_exit_1 : ¬__loop_choice_1) →
// CHECK-NEXT: (h_exit_2 : ¬(cppBvSlt i_2 n_0)) →
// CHECK-NEXT: (h_result_1 : __result_1 = i_2) →
// CHECK-NEXT: __result_1 = n_0

// A check proved before is a hypothesis of the next.
// CHECK: def cppverify_checked_{{[0-9a-f]+}}_assertion_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_null_2 : ¬(heapSelectBool __heap_live_0 (0 : Int))) →
// CHECK-NEXT: x_0 ≠ (BitVec.ofInt 32 (0))
// CHECK: def cppverify_checked_{{[0-9a-f]+}}_assertion_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_check_1 : x_0 ≠ (BitVec.ofInt 32 (0))) →
// CHECK-NEXT: (cppBvSle (BitVec.ofInt 32 (1)) x_0)

// A spec's proved postcondition at each application.
// CHECK: def cppverify_counted_{{[0-9a-f]+}}_postcondition_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_spec_count_1 : (cppSpec_fn_5f5a35636f756e7469 (n_0).toInt) ≥ (0 : Int)) →
// CHECK-NEXT: (h_spec_count_2 : (cppSpec_fn_5f5a35636f756e7469 ((n_0).toInt - (1 : Int))) ≥ (0 : Int)) →

// The postcondition's own disjunction is what remains to be shown.
// CHECK: def cppverify_positive_{{[0-9a-f]+}}_postcondition_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_result_1 : __result_1 = x_0) →
// CHECK-NEXT: ¬(cppBvSlt (BitVec.ofInt 32 (0)) x_0) ∨ (cppBvSlt (BitVec.ofInt 32 (0)) __result_1)

// Facts the verifier states at entry: an extent's, and where an object lies.
// CHECK: def cppverify_read_{{[0-9a-f]+}}_postcondition_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_entry_1 : {{.*}}) →
// CHECK: (h_object_1 : p_0 = (0 : Int) ∨ {{.*}}) →

// A hypothesis never takes a variable's name.
// CHECK: def cppverify_named_{{[0-9a-f]+}}_postcondition_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_x_1 : BitVec 32)
// CHECK: (h_h_x_1 : h_x_1 = x_0 + (BitVec.ofInt 32 (1))) →
// CHECK: (h_x_1_1 : x_1 = x_0 + h_x_1) →

// A contract's check that it is defined: each clause shown defined is
// assumed for the next, in the state a function without a verified body may
// return in, its frame and its result.
// CHECK: def cppverify_pick_contract_{{[0-9a-f]+}}_division_by_zero_{{[0-9a-f]+}}.readable : Prop :=
// CHECK: (h_entry_1 : {{.*}}) →
// CHECK-NEXT: (h_null_1 : {{.*}}) →
// CHECK-NEXT: (h_null_2 : {{.*}}) →
// CHECK-NEXT: (h_object_1 : {{.*}}) →
// CHECK-NEXT: (h_pre_1 : {{.*}}) →
// CHECK-NEXT: (h_ret_1 : (∀ (__frame_address : Int), {{.*}})) →
// CHECK-NEXT: (h_ret_2 : __result_1 = (0 : Int) ∨ {{.*}}) →
// CHECK-NEXT: (h_post_1 : __result_1 = p_0) →
// CHECK-NEXT: ((heapSelectBv 32 __heap_1 p_0)).toInt ≠ (0 : Int)

// STUB: theorem cppverify_twice_edf933_postcondition_28de726e_proof : cppverify_twice_edf933_postcondition_28de726e := by
// STUB-NEXT:   apply cppverify_twice_edf933_postcondition_28de726e.of_readable
// STUB-NEXT:   intro __heap_alloc_0 __heap_live_0 __local_call_1_1 __local_call_2_1 __result_1 a_1 b_1 x_0 h_pre_1 h_null_1 h_null_2 h_call_next_1 h_a_1 h_call_next_2 h_b_1 h_result_1
// STUB-NEXT:   sorry

// A large goal names its parts, which a proof introduces too.
// LETS: intro __heap_alloc_0 __heap_live_0 __result_1 x_0 __cppverify_term_1 {{.*}} h_pre_1 h_null_1 h_null_2

// STUBS: Build completed successfully

// TRUSTED: Trusted: next (contract assumed, not verified)
// TRUSTED: Exported: lean obligation: twice
// CERTIFIED: Certified: twice [backend=Lean] [trusts=next]

// BRIDGE: Generated.lean:{{[0-9]+}}:{{[0-9]+}}: Application type mismatch: The argument
