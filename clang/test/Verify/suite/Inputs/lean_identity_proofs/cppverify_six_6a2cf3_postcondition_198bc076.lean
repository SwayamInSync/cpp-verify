import CppVerify.User

theorem cppverify_six_6a2cf3_postcondition_198bc076_proof :
    cppverify_six_6a2cf3_postcondition_198bc076 := by
  unfold cppverify_six_6a2cf3_postcondition_198bc076
  intro _ _ r _ _ _ unfolded
  intros
  have three : (BitVec.ofInt 32 3).toInt = 3 := rfl
  rw [unfolded, three]
  by_cases h : r = BitVec.ofInt 32 6
  · right; right; right
    simp [cppSpecBody_6a2cf351_fn_5f5a3374726969_4, cppSpecBody_6a2cf351_fn_5f5a3374726969_3,
      cppSpecBody_6a2cf351_fn_5f5a3374726969_2, cppSpecBody_6a2cf351_fn_5f5a3374726969_1, h]
  · right; right; left; exact h
