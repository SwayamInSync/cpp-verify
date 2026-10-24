import CppVerify.Goals.cppverify_total_push_cdfd2d
import CppVerify.User
import CppVerify.Auto

theorem cppverify_total_push_cdfd2d_postcondition_3a9fac6f_proof :
    cppverify_total_push_cdfd2d_postcondition_3a9fac6f := by
  apply cppverify_total_push_cdfd2d_postcondition_3a9fac6f.of_readable
  intro _ _ s x pushed _ _ _
  rw [pushed]
  unfold cppSpecBody_cdfd2da1_fn_5f5a35746f74616c4e396370707665726966793373657145_1
  have := cppSeqLength_nonneg s
  simp [BitVec.toInt_signExtend_of_le]
  omega
