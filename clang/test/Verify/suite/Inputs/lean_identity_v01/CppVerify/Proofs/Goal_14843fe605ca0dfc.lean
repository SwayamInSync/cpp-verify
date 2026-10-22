import CppVerify.User

/- Complete this proof; this file is never regenerated. -/
theorem cppverify_one_fn_5f5a336f6e6576_obligation_2_goal_proof :
    cppverify_one_fn_5f5a336f6e6576_obligation_2_goal := by
  unfold cppverify_one_fn_5f5a336f6e6576_obligation_2_goal
  intro _ _ r
  by_cases h : r = BitVec.ofInt 32 1
  · right; right; right; exact h
  · right; right; left; exact h
