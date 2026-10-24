import CppVerify.Goals.cppverify_trusting_b6301a
import CppVerify.User

theorem cppverify_trusting_b6301a_postcondition_bafafdfb_proof : cppverify_trusting_b6301a_postcondition_bafafdfb := by
  unfold cppverify_trusting_b6301a_postcondition_bafafdfb
  intro _ _ r c
  by_cases hc : c = BitVec.ofInt 32 7
  · by_cases hr : r = c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hr.trans hc))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
  · exact Or.inr (Or.inr (Or.inl hc))
