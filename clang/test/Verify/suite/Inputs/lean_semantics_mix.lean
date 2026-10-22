import CppVerify.User

theorem cppverify_mix_fn_5f5a336d69786a6a_obligation_1_goal_proof :
    cppverify_mix_fn_5f5a336d69786a6a_obligation_1_goal := by
  unfold cppverify_mix_fn_5f5a336d69786a6a_obligation_1_goal
  intro _ _ a b r s
  by_cases hr : r = a ^^^ b + (BitVec.ofInt 32 (1))
  · by_cases hs : s = a ^^^ b + (BitVec.ofInt 32 (1))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hr.trans hs.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inl hr))
