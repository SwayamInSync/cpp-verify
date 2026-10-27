import CppVerify.Goals.cppverify_small_74ff94
import CppVerify.User

theorem cppverify_small_74ff94_precondition_4e324fa2_proof :
    cppverify_small_74ff94_precondition_4e324fa2 := by
  unfold cppverify_small_74ff94_precondition_4e324fa2
  intro _ _
  have zero : (BitVec.ofInt 32 0).toInt = 0 := by decide
  exact Or.inr (Or.inr (Or.inr ⟨fun _ range => by rw [zero] at range; omega, by decide⟩))
