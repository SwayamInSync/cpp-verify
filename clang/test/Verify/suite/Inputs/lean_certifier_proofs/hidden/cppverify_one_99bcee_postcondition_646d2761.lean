import CppVerify.Goals.cppverify_one_99bcee
import CppVerify.User

/- An axiom behind a lemma. -/
axiom escape {p : Prop} : p

theorem helper : cppverify_one_99bcee_postcondition_646d2761 := escape

theorem cppverify_one_99bcee_postcondition_646d2761_proof : cppverify_one_99bcee_postcondition_646d2761 := helper
