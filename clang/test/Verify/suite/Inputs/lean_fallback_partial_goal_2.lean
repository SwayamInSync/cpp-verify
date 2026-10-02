import CppVerify.User

theorem cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal_proof :
    cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal := by
  unfold cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal
  intro _ _ x_0 y_1
  by_cases pre : cppBvSle (BitVec.ofInt 32 0) x_0 ∧ cppBvSle x_0 (BitVec.ofInt 32 100)
  · right; right; right; right
    by_cases next : y_1 = x_0 + BitVec.ofInt 32 1
    · right
      subst next
      obtain ⟨low, high⟩ := pre
      simp only [cppBvSle, cppBvSlt, BitVec.sle, BitVec.slt, decide_eq_true_eq] at low high ⊢
      have zero : (BitVec.ofInt 32 0).toInt = 0 := rfl
      have hundred : (BitVec.ofInt 32 100).toInt = 100 := rfl
      have one : (BitVec.ofInt 32 1).toInt = 1 := rfl
      have sum : (x_0 + BitVec.ofInt 32 1).toInt = x_0.toInt + 1 := by
        rw [BitVec.toInt_add, one]
        apply Int.bmod_eq_of_le <;> omega
      omega
    · left; exact next
  · exact Or.inl pre
