import CppVerify.User

theorem cppverify_fibo_six_ec829a_postcondition_30cd1b97_proof :
    cppverify_fibo_six_ec829a_postcondition_30cd1b97 := by
  unfold cppverify_fibo_six_ec829a_postcondition_30cd1b97
  intro __heap_alloc_0 __heap_live_0 _ _ _ _ _ _ _ unfolded
  intros
  right
  right
  have six : (BitVec.ofInt 32 6).toInt = 6 := rfl
  rw [unfolded, six]
  simp [cppSpecBody_ec829a45_fn_5f5a346669626f69_8, cppSpecBody_ec829a45_fn_5f5a346669626f69_7,
    cppSpecBody_ec829a45_fn_5f5a346669626f69_6, cppSpecBody_ec829a45_fn_5f5a346669626f69_5,
    cppSpecBody_ec829a45_fn_5f5a346669626f69_4, cppSpecBody_ec829a45_fn_5f5a346669626f69_3]
