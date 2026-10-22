import CppVerify.User

theorem cppverify_product_fn_5f5a3770726f647563746a6a_obligation_2_goal_proof :
    cppverify_product_fn_5f5a3770726f647563746a6a_obligation_2_goal := by
  unfold cppverify_product_fn_5f5a3770726f647563746a6a_obligation_2_goal
  intro _ _ r c a b
  have thousand : (BitVec.ofInt 32 1000).toNat = 1000 := by decide
  rcases Classical.em (cppBvUlt a (BitVec.ofInt 32 1000) ∧
      cppBvUlt b (BitVec.ofInt 32 1000)) with ⟨ha, hb⟩ | outside
  · rcases Classical.em (c = a * b) with hc | hc
    · rcases Classical.em (r = c) with hr | hr
      · simp only [cppBvUlt, BitVec.ult, decide_eq_true_eq, thousand] at ha hb
        have small : a.toNat * b.toNat ≤ 999 * 999 :=
          Nat.mul_le_mul (by omega) (by omega)
        have low : Int.ofNat a.toNat * Int.ofNat b.toNat ≥ 0 := by
          rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, ← Int.natCast_mul]
          omega
        have high : Int.ofNat a.toNat * Int.ofNat b.toNat ≤ 4294967295 := by
          rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, ← Int.natCast_mul]
          omega
        -- Conjunctions as written, or grouped as the module groups them.
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        first
          | exact ⟨low, high, hr.trans hc⟩
          | exact ⟨⟨low, high⟩, hr.trans hc⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · refine Or.inl fun ⟨first, second⟩ => outside ⟨?_, ?_⟩
    · rcases first with h | h
      · exact absurd h (by decide)
      · first | exact h.2.2 | exact h.2
    · rcases second with h | h
      · exact absurd h (by decide)
      · first | exact h.2.2 | exact h.2
