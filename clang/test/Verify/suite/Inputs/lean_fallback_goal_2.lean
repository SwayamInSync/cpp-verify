import CppVerify.User

theorem cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal_proof :
    cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal := by
  unfold cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal
  intro __heap_alloc_0 __heap_live_0 i_0 spec1 spec2 spec3 spec4
  by_cases h :
      cppBvSle (BitVec.ofInt 32 1) i_0 ∧
        cppBvSle i_0 (BitVec.ofInt 32 10)
  · right
    right
    right
    right
    have bounds := h
    simp [cppBvSle, BitVec.sle] at bounds
    have add64 :
        ((BitVec.signExtend 64 i_0) +
            (BitVec.signExtend 64 (BitVec.ofInt 32 1))).toInt =
          i_0.toInt + 1 := by
      simp only [BitVec.toInt_add]
      repeat rw [BitVec.toInt_signExtend_of_le (by omega)]
      apply Int.bmod_eq_of_le <;> simp <;> omega
    have sub64 :
        ((BitVec.signExtend 64 i_0) -
            (BitVec.signExtend 64 (BitVec.ofInt 32 1))).toInt =
          i_0.toInt - 1 := by
      simp only [BitVec.toInt_sub]
      repeat rw [BitVec.toInt_signExtend_of_le (by omega)]
      apply Int.bmod_eq_of_le <;> simp <;> omega
    unfold cppBvSle
    simp only [BitVec.sle, decide_eq_true_eq]
    rw [add64, sub64]
    simp
    omega
  · exact Or.inl h
