import CppVerify.User

theorem cppverify_trusting_fn_5f5a387472757374696e6769_obligation_2_goal_proof : cppverify_trusting_fn_5f5a387472757374696e6769_obligation_2_goal := by
  unfold cppverify_trusting_fn_5f5a387472757374696e6769_obligation_2_goal
  intro _ _ r c
  by_cases hc : c = BitVec.ofInt 32 7
  · by_cases hr : r = c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hr.trans hc))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
  · exact Or.inr (Or.inr (Or.inl hc))
