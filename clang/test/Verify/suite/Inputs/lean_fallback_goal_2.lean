import CppVerify.User

theorem cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal_proof :
    cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal := by
  unfold cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_2_goal
  intro __heap_alloc_0 __heap_live_0 i_0
  by_cases h :
      cppBvSle (BitVec.ofInt 32 1) i_0 ∧
        cppBvSle i_0 (BitVec.ofInt 32 10)
  · right
    right
    right
    right
    obtain ⟨low, high⟩ := h
    simp only [cppBvSle, BitVec.sle, decide_eq_true_eq] at low high
    have one : (BitVec.ofInt 32 1).toInt = 1 := rfl
    have ten : (BitVec.ofInt 32 10).toInt = 10 := rfl
    simp only [BitVec.signExtend_eq, BitVec.saddOverflow, BitVec.ssubOverflow,
      one]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  · exact Or.inl h
