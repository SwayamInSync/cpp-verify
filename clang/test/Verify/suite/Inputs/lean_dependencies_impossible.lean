import CppVerify.Goals.cppverify_impossible_9d6c7c
import CppVerify.User

theorem cppverify_impossible_9d6c7c_postcondition_1cd35301_proof : cppverify_impossible_9d6c7c_postcondition_1cd35301 := by
  unfold cppverify_impossible_9d6c7c_postcondition_1cd35301
  intro _ _ _ x
  left
  intro ⟨above, below⟩
  simp only [cppBvSlt, BitVec.slt, decide_eq_true_eq] at above below
  omega
