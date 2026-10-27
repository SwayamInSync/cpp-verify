import CppVerify.Goals.cppverify_twice_edf933
import CppVerify.User

theorem cppverify_twice_edf933_precondition_f0a3d715_proof : cppverify_twice_edf933_precondition_f0a3d715 := by
  apply cppverify_twice_edf933_precondition_f0a3d715.of_readable
  intro __heap_alloc_0 __heap_live_0 x_0 h_pre_1 h_null_1 h_null_2
  simp only [cppBvSle, cppBvSlt, BitVec.sle, BitVec.slt, decide_eq_true_eq] at h_pre_1 ⊢
  have : (BitVec.ofInt 32 0).toInt = 0 := rfl
  have : (BitVec.ofInt 32 50).toInt = 50 := rfl
  have : (BitVec.ofInt 32 100).toInt = 100 := rfl
  omega
