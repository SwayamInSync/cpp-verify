// REQUIRES: lean
//
// RUN: rm -rf %t.admitted %t.certified %t.axiom %t.stale
// RUN: not %cpp-verify --backend=lean --lean-project=%t.admitted --lean-certify %s -- 2>&1 | FileCheck %s --check-prefix=ADMITTED
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.certified %s --
// RUN: sed -i.orig 's/  sorry/  simp [cppverify_trivial_3e4f5a_missing_return_ba8abb90]/' %t.certified/CppVerify/Proofs/cppverify_trivial_3e4f5a/cppverify_trivial_3e4f5a_missing_return_ba8abb90.lean
// RUN: sed -i.orig 's/  sorry/  simp [cppverify_trivial_3e4f5a_postcondition_ba8abb90]/' %t.certified/CppVerify/Proofs/cppverify_trivial_3e4f5a/cppverify_trivial_3e4f5a_postcondition_ba8abb90.lean
// RUN: %cpp-verify --backend=lean --lean-project=%t.certified --lean-certify %s -- 2>&1 | FileCheck %s --check-prefix=CERTIFIED
// RUN: echo 'theorem unfinished : True := by sorry' >> %t.certified/CppVerify/User.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.certified --lean-certify %s -- 2>&1 | FileCheck %s --check-prefix=USER-ADMITTED
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.axiom %s --
// RUN: echo 'axiom escape {p : Prop} : p' >> %t.axiom/CppVerify/User.lean
// RUN: sed -i.orig 's/  sorry/  exact escape/' %t.axiom/CppVerify/Proofs/*/*.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.axiom --lean-certify %s -- 2>&1 | FileCheck %s --check-prefix=AXIOM
//
// RUN: %cpp-verify --backend=lean --lean-project=%t.stale %s --
// RUN: sed -i.orig 's/  sorry/  simp [cppverify_trivial_3e4f5a_missing_return_ba8abb90]/' %t.stale/CppVerify/Proofs/cppverify_trivial_3e4f5a/cppverify_trivial_3e4f5a_missing_return_ba8abb90.lean
// RUN: sed -i.orig 's/  sorry/  simp [cppverify_trivial_3e4f5a_postcondition_ba8abb90]/' %t.stale/CppVerify/Proofs/cppverify_trivial_3e4f5a/cppverify_trivial_3e4f5a_postcondition_ba8abb90.lean
// RUN: not %cpp-verify --backend=lean --lean-project=%t.stale --lean-certify %S/Inputs/lean_certify_stale.cpp -- 2>&1 | FileCheck %s --check-prefix=STALE

void trivial()
  cppverify::post(true)
{}

// ADMITTED: Unresolved: lean obligation: trivial (Lean certification failed:
// ADMITTED-SAME: declaration uses `sorry`
// CERTIFIED: Certified: trivial [backend=Lean]
// USER-ADMITTED: Unresolved: lean obligation: trivial (Lean certification failed:
// USER-ADMITTED-SAME: User.lean
// USER-ADMITTED-SAME: declaration uses `sorry`
// AXIOM: Unresolved: lean obligation: trivial (Lean certification failed: proof depends on undocumented axiom escape)
// STALE: Unresolved: lean obligation: trivial (Lean certification failed:
