import CppVerify.User

theorem cppverify_seven_634ea3_postcondition_f0d135e6_proof : cppverify_seven_634ea3_postcondition_f0d135e6 := by
  unfold cppverify_seven_634ea3_postcondition_f0d135e6
  intro _ _ r c
  by_cases hc : c = BitVec.ofInt 32 7
  · by_cases hr : r = c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hr.trans hc))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
  · exact Or.inr (Or.inr (Or.inl hc))
