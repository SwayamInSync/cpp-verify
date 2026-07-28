// REQUIRES: lean
//
// RUN: rm -rf %t.admitted %t.certified %t.axiom %t.stale
// RUN: not %cpp-verify --backend=lean --lean-project=%t.admitted --lean-certify %s 2>&1 | FileCheck %s --check-prefix=ADMITTED
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.certified %s
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_1_goal]/' %t.certified/CppVerify/Proofs/Goal_583ed320b83a75f8.lean
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_2_goal]/' %t.certified/CppVerify/Proofs/Goal_279b1b0b28d9b239.lean
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_3_goal]/' %t.certified/CppVerify/Proofs/Goal_61463634fb4df80b.lean
// RUN: %cpp-verify --backend=lean --lean-project=%t.certified --lean-certify %s 2>&1 | FileCheck %s --check-prefix=CERTIFIED
// RUN: echo 'theorem unfinished : True := by sorry' >> %t.certified/CppVerify/User.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.certified --lean-certify %s 2>&1 | FileCheck %s --check-prefix=USER-ADMITTED
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.axiom %s
// RUN: echo 'axiom escape {p : Prop} : p' >> %t.axiom/CppVerify/User.lean
// RUN: sed -i 's/  sorry/  exact escape/' %t.axiom/CppVerify/Proofs/*.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.axiom --lean-certify %s 2>&1 | FileCheck %s --check-prefix=AXIOM
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.stale %s
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_1_goal]/' %t.stale/CppVerify/Proofs/Goal_583ed320b83a75f8.lean
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_2_goal]/' %t.stale/CppVerify/Proofs/Goal_279b1b0b28d9b239.lean
// RUN: sed -i 's/  sorry/  simp [cppverify_trivial_fn_5f5a377472697669616c76_obligation_3_goal]/' %t.stale/CppVerify/Proofs/Goal_61463634fb4df80b.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.stale --lean-certify %S/Inputs/lean_certify_stale.cpp 2>&1 | FileCheck %s --check-prefix=STALE

void trivial()
  post(true)
{}

// ADMITTED: Unresolved: lean obligation: trivial (Lean certification failed:
// ADMITTED-SAME: declaration uses `sorry`
// CERTIFIED: Certified: trivial [backend=Lean]
// USER-ADMITTED: Unresolved: lean obligation: trivial (Lean certification failed:
// USER-ADMITTED-SAME: User.lean
// USER-ADMITTED-SAME: declaration uses `sorry`
// AXIOM: Unresolved: lean obligation: trivial (Lean certification failed: proof depends on undocumented axiom escape)
// STALE: Unresolved: lean obligation: trivial (Lean certification failed:
