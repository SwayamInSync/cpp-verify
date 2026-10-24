import CppVerify.Goals.cppverify_plus_tri_zero_10bb8a
import CppVerify.User
import CppVerify.Auto

theorem cppverify_plus_tri_zero_10bb8a_postcondition_8b45419c_proof :
    cppverify_plus_tri_zero_10bb8a_postcondition_8b45419c := by
  apply cppverify_plus_tri_zero_10bb8a_postcondition_8b45419c.of_readable
  intro __heap_alloc_0 __heap_live_0 __result_1 x_0 tri_0 _ _ h_pre_1 h_null_1 h_null_2 h_result_1
  rw [tri_0] at *
  simp only [cppSpecBody_10bb8a86_fn_5f5a3374726969_1] at *
  cppverify_auto
