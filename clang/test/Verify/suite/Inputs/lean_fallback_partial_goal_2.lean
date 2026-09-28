import CppVerify.User

theorem cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal_proof :
    cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal := by
  unfold cppverify_bump_fn_5f5a3462756d7069_obligation_2_goal
  intro _ _ x_0
  by_cases pre : cppBvSle (BitVec.ofInt 32 0) x_0 ∧ cppBvSle x_0 (BitVec.ofInt 32 100)
  · right; right; right
    obtain ⟨low, high⟩ := pre
    simp only [cppBvSle, BitVec.sle, decide_eq_true_eq] at low high
    have zero : (BitVec.ofInt 32 0).toInt = 0 := rfl
    have hundred : (BitVec.ofInt 32 100).toInt = 100 := rfl
    have one : (BitVec.ofInt 32 1).toInt = 1 := rfl
    simp only [BitVec.signExtend_eq, BitVec.saddOverflow, one]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  · exact Or.inl pre
