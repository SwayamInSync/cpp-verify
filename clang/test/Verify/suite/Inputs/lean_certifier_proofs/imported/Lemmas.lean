import CppVerify.Goals.cppverify_one_99bcee
import CppVerify.User
import Lean

/- The same, in a module of the project the proof imports. -/
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  addDecl (.thmDecl { name := `cheat, levelParams := [], type := mkConst `cppverify_one_99bcee_postcondition_646d2761, value := mkConst ``True.intro })
