import CppVerify.User

theorem cppverify_same_fn_5f5a3473616d6569_obligation_2_goal_proof : cppverify_same_fn_5f5a3473616d6569_obligation_2_goal := by
  unfold cppverify_same_fn_5f5a3473616d6569_obligation_2_goal
  intro _ _ r x
  by_cases h : r = x
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))
