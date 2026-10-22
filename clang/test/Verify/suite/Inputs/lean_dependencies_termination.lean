import CppVerify.User

theorem cppverify_scaled_decreases_52d363_termination_3164b050_proof : cppverify_scaled_decreases_52d363_termination_3164b050 := by
  unfold cppverify_scaled_decreases_52d363_termination_3164b050
  intro a b
  have measure : a ≤ 0 ∨ b ≤ 0 ∨ (a * b ≥ 0 ∧ a * (b - 1) < a * b) := by
    by_cases ha : a ≤ 0
    · exact Or.inl ha
    · by_cases hb : b ≤ 0
      · exact Or.inr (Or.inl hb)
      · refine Or.inr (Or.inr ⟨Int.mul_nonneg (by omega) (by omega), ?_⟩)
        rw [Int.mul_sub, Int.mul_one]
        omega
  simpa only [or_assoc] using measure
