import CppVerify.Goals.cppverify_positive_fb6abf
import CppVerify.User

theorem cppverify_positive_fb6abf_postcondition_78bdd643_proof : cppverify_positive_fb6abf_postcondition_78bdd643 := by
  unfold cppverify_positive_fb6abf_postcondition_78bdd643
  intro _ _ r x
  by_cases h : r = x
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
