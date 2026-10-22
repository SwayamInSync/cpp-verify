import CppVerify.User

theorem cppverify_mix_b839ab_assertion_255467f3_proof :
    cppverify_mix_b839ab_assertion_255467f3 := by
  unfold cppverify_mix_b839ab_assertion_255467f3
  intro _ _ a b r s
  by_cases hr : r = a ^^^ b + (BitVec.ofInt 32 (1))
  · by_cases hs : s = a ^^^ b + (BitVec.ofInt 32 (1))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hr.trans hs.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inl hr))
