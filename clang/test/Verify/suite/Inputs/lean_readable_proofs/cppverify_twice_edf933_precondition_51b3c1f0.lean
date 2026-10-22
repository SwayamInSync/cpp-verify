import CppVerify.User

theorem cppverify_twice_edf933_precondition_51b3c1f0_proof : cppverify_twice_edf933_precondition_51b3c1f0 := by
  apply cppverify_twice_edf933_precondition_51b3c1f0.of_readable
  intro __heap_alloc_0 __heap_live_0 __local_call_1_1 a_1 x_0 h_pre_1 h_null_1 h_null_2 h_call_next_1 h_a_1
  obtain ⟨range, called⟩ := h_call_next_1
  subst h_a_1 called
  simp only [cppBvSle, cppBvSlt, BitVec.sle, BitVec.slt, decide_eq_true_eq] at h_pre_1 ⊢
  have : (BitVec.ofInt 32 0).toInt = 0 := rfl
  have : (BitVec.ofInt 32 1).toInt = 1 := rfl
  have : (BitVec.ofInt 32 50).toInt = 50 := rfl
  have : (BitVec.ofInt 32 100).toInt = 100 := rfl
  rw [BitVec.toInt_add_of_not_saddOverflow (by simp [BitVec.saddOverflow]; omega)]
  omega
