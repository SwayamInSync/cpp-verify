import CppVerify.User

theorem cppverify_same_9601c2_postcondition_ce92acf8_proof : cppverify_same_9601c2_postcondition_ce92acf8 := by
  unfold cppverify_same_9601c2_postcondition_ce92acf8
  intro _ _ r x
  by_cases h : r = x
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))
