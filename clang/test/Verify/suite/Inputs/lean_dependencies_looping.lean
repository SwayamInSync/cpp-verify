import CppVerify.User

theorem cppverify_looping_3f4bd4_postcondition_d06fccd0_proof : cppverify_looping_3f4bd4_postcondition_d06fccd0 := by
  unfold cppverify_looping_3f4bd4_postcondition_d06fccd0
  intro _ _ _ r a b _ _ _
  have thousand : (BitVec.ofInt 32 1000).toNat = 1000 := by decide
  rcases Classical.em (cppBvUlt a (BitVec.ofInt 32 1000) ∧
      cppBvUlt b (BitVec.ofInt 32 1000)) with ⟨ha, hb⟩ | outside
  · rcases Classical.em (r = a * b) with hr | hr
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
      iterate 10 right
      first
        | exact ⟨low, high, hr⟩
        | exact ⟨⟨low, high⟩, hr⟩
    · iterate 9 right
      exact Or.inl hr
  · refine Or.inl fun ⟨first, second⟩ => outside ⟨?_, ?_⟩
    · rcases first with h | h
      · exact absurd h (by decide)
      · first | exact h.2.2 | exact h.2
    · rcases second with h | h
      · exact absurd h (by decide)
      · first | exact h.2.2 | exact h.2
