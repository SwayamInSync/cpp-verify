import CppVerify.User

theorem cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_3_goal_proof :
    cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_3_goal := by
  unfold cppverify_fibo_step_fn_5f5a396669626f5f7374657069_obligation_3_goal
  intro __heap_alloc_0 __heap_live_0 i_0 spec1 spec2 spec3 spec4 spec5 spec6 spec7
  by_cases h :
      cppBvSle (BitVec.ofInt 32 1) i_0 ∧
        cppBvSle i_0 (BitVec.ofInt 32 10)
  · right
    right
    right
    right
    have bounds := h
    simp [cppBvSle, BitVec.sle] at bounds
    have addInt :
        (i_0 + BitVec.ofInt 32 1).toInt = i_0.toInt + 1 := by
      simp only [BitVec.toInt_add]
      apply Int.bmod_eq_of_le <;> simp <;> omega
    have subInt :
        (i_0 - BitVec.ofInt 32 1).toInt = i_0.toInt - 1 := by
      simp only [BitVec.toInt_sub]
      apply Int.bmod_eq_of_le <;> simp <;> omega
    have positive : ¬i_0.toInt + 1 ≤ 0 := by omega
    have notOne : i_0.toInt + 1 ≠ 1 := by omega
    have minusTwo : i_0.toInt + 1 - 2 = i_0.toInt - 1 := by omega
    have minusOne : i_0.toInt + 1 - 1 = i_0.toInt := by omega
    rw [spec5, addInt, subInt]
    unfold cppSpecBody_m1_fn_5f5a346669626f69_1
    rw [if_neg positive, if_neg notOne, minusTwo, minusOne]
    exact Int.add_comm _ _
  · exact Or.inl h
