import CppVerify.Goals.cppverify_twice_edf933
import CppVerify.User

theorem cppverify_twice_edf933_postcondition_28de726e_proof : cppverify_twice_edf933_postcondition_28de726e := by
  apply cppverify_twice_edf933_postcondition_28de726e.of_readable
  intro __heap_alloc_0 __heap_live_0 __local_call_1_1 __local_call_2_1 __result_1 a_1 b_1 x_0 h_pre_1 h_null_1 h_null_2 h_call_next_1 h_a_1 h_call_next_2 h_b_1 h_result_1
  obtain ⟨_, first⟩ := h_call_next_1
  obtain ⟨_, second⟩ := h_call_next_2
  subst h_result_1 h_b_1 second h_a_1 first
  simp only [cppBvSle, cppBvSlt, BitVec.sle, BitVec.slt, decide_eq_true_eq] at h_pre_1
  have : (BitVec.ofInt 32 0).toInt = 0 := rfl
  have : (BitVec.ofInt 32 50).toInt = 50 := rfl
  refine ⟨by omega, ?_⟩
  rw [BitVec.add_assoc]
  rfl
