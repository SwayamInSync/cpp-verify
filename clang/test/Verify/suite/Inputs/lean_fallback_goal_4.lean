import CppVerify.User

theorem cppverify_fibo_six_fn_5f5a386669626f5f73697876_obligation_2_goal_proof :
    cppverify_fibo_six_fn_5f5a386669626f5f73697876_obligation_2_goal := by
  unfold cppverify_fibo_six_fn_5f5a386669626f5f73697876_obligation_2_goal
  intro __heap_alloc_0 __heap_live_0 _ _ _ _ _ _ _ unfolded
  intros
  right
  right
  have six : (BitVec.ofInt 32 6).toInt = 6 := rfl
  rw [unfolded, six]
  simp [cppSpecBody_m2_fn_5f5a346669626f69_8, cppSpecBody_m2_fn_5f5a346669626f69_7,
    cppSpecBody_m2_fn_5f5a346669626f69_6, cppSpecBody_m2_fn_5f5a346669626f69_5,
    cppSpecBody_m2_fn_5f5a346669626f69_4, cppSpecBody_m2_fn_5f5a346669626f69_3]
