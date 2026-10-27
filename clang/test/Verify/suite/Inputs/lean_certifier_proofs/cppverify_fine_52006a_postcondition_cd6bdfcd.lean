import CppVerify.Goals.cppverify_fine_52006a
import CppVerify.User

theorem cppverify_fine_52006a_postcondition_cd6bdfcd_proof : cppverify_fine_52006a_postcondition_cd6bdfcd := by
  apply cppverify_fine_52006a_postcondition_cd6bdfcd.of_readable
  intro __heap_alloc_0 __heap_live_0 __result_1 h_null_1 h_null_2 h_result_1
  exact h_result_1
