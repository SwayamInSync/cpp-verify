import CppVerify.Goals.cppverify_one_99bcee
import CppVerify.User

theorem cppverify_one_99bcee_postcondition_cd6bdfcd_proof :
    cppverify_one_99bcee_postcondition_cd6bdfcd := by
  unfold cppverify_one_99bcee_postcondition_cd6bdfcd
  intro _ _ r
  by_cases h : r = BitVec.ofInt 32 1
  · right; right; right; exact h
  · right; right; left; exact h
