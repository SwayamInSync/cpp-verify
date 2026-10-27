import CppVerify.Goals.cppverify_tri_nonneg_42a030
import CppVerify.User
import CppVerify.Auto

/-- tri is never negative, by induction over its own recursion. -/
theorem tri_nonneg (m : Int) : 0 ≤ cppSpec_fn_5f5a3374726969 m := by
  induction m using cppSpec_fn_5f5a3374726969.induct with
  | case1 x h => rw [cppSpec_fn_5f5a3374726969]; simp [h]
  | case2 x h ih => rw [cppSpec_fn_5f5a3374726969]; simp [h]; omega

theorem cppverify_tri_nonneg_42a030_postcondition_053b1980_proof :
    cppverify_tri_nonneg_42a030_postcondition_053b1980 := by
  apply cppverify_tri_nonneg_42a030_postcondition_053b1980.of_readable
  intro _ _ n _ _ _
  exact tri_nonneg _
