import CppVerify.User

theorem cppverify_small_fn_5f5a35736d616c6c76_obligation_1_goal_proof :
    cppverify_small_fn_5f5a35736d616c6c76_obligation_1_goal := by
  unfold cppverify_small_fn_5f5a35736d616c6c76_obligation_1_goal
  intro _ _
  have zero : (BitVec.ofInt 32 0).toInt = 0 := by decide
  exact Or.inr (Or.inr (Or.inr ⟨fun _ range => by rw [zero] at range; omega, by decide⟩))
