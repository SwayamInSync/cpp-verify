import CppVerify.Goals.cppverify_tri_zero_e086e9
import CppVerify.User
import CppVerify.Auto

theorem cppverify_tri_zero_e086e9_postcondition_44e49d34_proof :
    cppverify_tri_zero_e086e9_postcondition_44e49d34 := by
  apply cppverify_tri_zero_e086e9_postcondition_44e49d34.of_readable
  intro __heap_alloc_0 __heap_live_0 __result_1 tri_0 _ _ h_null_1 h_null_2 h_result_1
  rw [tri_0] at *
  simp only [cppSpecBody_e086e9ab_fn_5f5a3374726969_1] at *
  cppverify_auto
