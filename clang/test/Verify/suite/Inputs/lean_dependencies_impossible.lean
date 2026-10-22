import CppVerify.User

theorem cppverify_impossible_fn_5f5a3130696d706f737369626c6569_obligation_2_goal_proof : cppverify_impossible_fn_5f5a3130696d706f737369626c6569_obligation_2_goal := by
  unfold cppverify_impossible_fn_5f5a3130696d706f737369626c6569_obligation_2_goal
  intro _ _ _ x
  left
  intro ⟨above, below⟩
  simp only [cppBvSlt, BitVec.slt, decide_eq_true_eq] at above below
  omega
