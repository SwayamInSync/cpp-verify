import CppVerify.Goals.cppverify_one_99bcee
import CppVerify.User

theorem cppverify_one_99bcee_postcondition_ebbe6a6a_proof :
    cppverify_one_99bcee_postcondition_ebbe6a6a := by
  unfold cppverify_one_99bcee_postcondition_ebbe6a6a
  intro _ _ r
  by_cases h : r = BitVec.ofInt 32 1
  · right; right; right; subst h; decide
  · right; right; left; exact h
