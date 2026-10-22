import CppVerify.User

theorem cppverify_one_99bcee_postcondition_cd6bdfcd_2_proof :
    cppverify_one_99bcee_postcondition_cd6bdfcd_2 := by
  unfold cppverify_one_99bcee_postcondition_cd6bdfcd_2
  intro _ _ r
  by_cases h : r = BitVec.ofInt 32 1
  · right; right; right; exact h
  · right; right; left; exact h
