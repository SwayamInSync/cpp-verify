import CppVerify.User

/- Complete this proof; this file is never regenerated. -/
theorem cppverify_six_fn_5f5a3373697876_obligation_2_goal_proof :
    cppverify_six_fn_5f5a3373697876_obligation_2_goal := by
  unfold cppverify_six_fn_5f5a3373697876_obligation_2_goal
  intro _ _ r _ _ _ unfolded
  intros
  have three : (BitVec.ofInt 32 3).toInt = 3 := rfl
  rw [unfolded, three]
  by_cases h : r = BitVec.ofInt 32 6
  · right; right; right
    simp [cppSpecBody_m2_fn_5f5a3374726969_4, cppSpecBody_m2_fn_5f5a3374726969_3,
      cppSpecBody_m2_fn_5f5a3374726969_2, cppSpecBody_m2_fn_5f5a3374726969_1, h]
  · right; right; left; exact h
