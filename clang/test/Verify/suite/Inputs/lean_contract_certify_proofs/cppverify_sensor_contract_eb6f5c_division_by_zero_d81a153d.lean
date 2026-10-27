import CppVerify.Goals.cppverify_sensor_contract_eb6f5c
import CppVerify.User

theorem cppverify_sensor_contract_eb6f5c_division_by_zero_d81a153d_proof : cppverify_sensor_contract_eb6f5c_division_by_zero_d81a153d := by
  apply cppverify_sensor_contract_eb6f5c_division_by_zero_d81a153d.of_readable
  intro __heap_alloc_0 __heap_live_0 channel_0 h_null_1 h_null_2 h_pre_1
  simp only [cppBvSle, BitVec.sle_iff_toInt_le, BitVec.toInt_ofInt] at h_pre_1
  have := h_pre_1.1
  simp at this
  omega
