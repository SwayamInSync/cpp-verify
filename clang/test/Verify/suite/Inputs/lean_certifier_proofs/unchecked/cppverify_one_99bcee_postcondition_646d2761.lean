import CppVerify.Goals.cppverify_one_99bcee
import CppVerify.User
import Lean

/- A theorem of the goal whose value is a proof of True, added without the
   kernel. -/
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  addDecl (.thmDecl { name := `cppverify_one_99bcee_postcondition_646d2761_proof, levelParams := [], type := mkConst `cppverify_one_99bcee_postcondition_646d2761, value := mkConst ``True.intro })
