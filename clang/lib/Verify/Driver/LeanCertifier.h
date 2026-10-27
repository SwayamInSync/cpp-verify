//===--- LeanCertifier.h - The checker of Lean project proofs ----------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_LEANCERTIFIER_H
#define LLVM_CLANG_VERIFY_DRIVER_LEANCERTIFIER_H

#include "llvm/ADT/StringRef.h"

namespace clang {
namespace verify {

/// A Lean program certification runs on a project's compiled modules. It
/// elaborates none of the user's source, so nothing the user writes changes
/// what it checks.
inline constexpr llvm::StringLiteral LeanCertifierSource = R"lean(import Lean
import Lean.Replay
open Lean

/-- The axioms a constant depends on, through the statements and values of the
constants it uses, read from the kernel's constants. -/
def axiomsOf (env : Kernel.Environment) (root : Name) : Except String NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut work := #[root]
  while h : 0 < work.size do
    let c := work.back
    work := work.pop
    if seen.contains c then continue
    seen := seen.insert c
    let used (e : Expr) := e.getUsedConstants
    match env.find? c with
    | some (.axiomInfo v) => axioms := axioms.insert c; work := work ++ used v.type
    | some (.defnInfo v) => work := work ++ used v.type ++ used v.value
    | some (.thmInfo v) => work := work ++ used v.type ++ used v.value
    | some (.opaqueInfo v) => work := work ++ used v.type ++ used v.value
    | some (.quotInfo _) => pure ()
    | some (.ctorInfo v) => work := work ++ used v.type
    | some (.recInfo v) => work := work ++ used v.type
    | some (.inductInfo v) => work := work ++ used v.type ++ v.ctors.toArray
    | none => return .error s!"{c} is not in the environment"
  return .ok axioms

/-- A module's imports and its own constants, in the order it declares them,
read from its compiled files. -/
unsafe def moduleConstants (module : Name) :
    IO (Array Import × Array Name × Std.HashMap Name ConstantInfo) := do
  let file ← findOLean module
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  if ← server.pathExists then
    files := files.push server
    let priv := OLeanLevel.private.adjustFileName file
    if ← priv.pathExists then
      files := files.push priv
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError "cannot read the module" else
  let mut constants := {}
  for name in parts[parts.size - 1].1.constNames, info in parts[parts.size - 1].1.constants do
    constants := constants.insert name info
  return (parts[0].1.imports, parts[parts.size - 1].1.constNames, constants)

/-- A module of the project, read from its compiled files. -/
structure ProjectModule where
  name : Name
  imports : Array Import
  declared : Array Name
  constants : Std.HashMap Name ConstantInfo

/-- The modules of the project some modules import, each after the modules it
imports, and the toolchain's modules they import. -/
structure Closure where
  modules : Array ProjectModule := #[]
  toolchain : Array Import := #[]
  seen : NameSet := {}

unsafe def Closure.visit (toolchain : String) (module : Name) : StateT Closure IO Unit := do
  if (← get).seen.contains module then return
  modify fun c => { c with seen := c.seen.insert module }
  if (← findOLean module).toString.startsWith toolchain then
    modify fun c => { c with toolchain := c.toolchain.push { module } }
    return
  let (imports, declared, constants) ← moduleConstants module
  for i in imports do
    Closure.visit toolchain i.module
  modify fun c => { c with modules := c.modules.push { name := module, imports, declared, constants } }

/-- The kernel's environment of the project: the toolchain's modules the
project imports, imported once, then every module of the project replayed
with the kernel, each after the modules it imports, as leanchecker does. A
module the kernel rejects, one that imports it, and one that declares a
constant an earlier module or the toolchain declares otherwise are left out,
each with why; the constant each other module declares is recorded with it. -/
structure Replayed where
  env : Kernel.Environment
  rejected : Std.HashMap Name String
  owner : Std.HashMap Name Name

unsafe def replayProject (closure : Closure) : IO Replayed := do
  let (_, s) ← importModulesCore closure.toolchain |>.run
  let imported ← finalizeImport s closure.toolchain {} 0 false false (isModule := true)
  let mut env := imported.toKernelEnv
  let mut rejected : Std.HashMap Name String := {}
  let mut owner : Std.HashMap Name Name := {}
  for m in closure.modules do
    if let some i := m.imports.find? (rejected.contains ·.module) then
      rejected := rejected.insert m.name rejected[i.module]!
      continue
    let mut fresh : Std.HashMap Name ConstantInfo := {}
    let mut clash : Option String := none
    for (name, info) in m.constants do
      match env.find? name with
      | none => fresh := fresh.insert name info
      | some known =>
        -- Lean derives an equation lemma in each module that unfolds a
        -- definition, the same constant every time, and the kernel takes a
        -- theorem twice when it states the same.
        let same := known.type == info.type && known.levelParams == info.levelParams &&
          (known.isTheorem || known.value? == info.value?)
        unless same do
          let other := (owner[name]?).map toString |>.getD "the toolchain"
          clash := some s!"{m.name} declares {name}, which {other} declares"
          break
    if let some why := clash then
      rejected := rejected.insert m.name why
      continue
    try env ← env.replay fresh
    catch e =>
      rejected := rejected.insert m.name s!"the kernel rejects {m.name}: {e}"
      continue
    for (name, _) in fresh do
      owner := owner.insert name m.name
  return { env, rejected, owner }

/-- Whether the proof of a goal states exactly the goal its generated module
defines, or a refutation exactly its negation, and depends on no axiom
outside the allowed ones. -/
def checkStatement (project : Replayed) (goal module generated : Name)
    (refutes : Bool) (allowed : NameSet) : Option String := Id.run do
  let env := project.env
  let proof := goal.appendAfter (if refutes then "_refuted" else "_proof")
  let stated := if refutes then mkApp (mkConst ``Not) (mkConst goal) else mkConst goal
  match env.find? goal with
  | some (.defnInfo _) =>
    if project.owner[goal]? != some generated then
      return some s!"{goal} is not the goal {generated} defines"
  | _ => return some s!"{generated} defines no goal {goal}"
  match env.find? proof with
  | some (.thmInfo v) =>
    if project.owner[proof]? != some module then
      return some s!"{proof} is not declared in {module}"
    if v.type != stated then
      return some s!"{proof} proves {v.type}, not {stated}"
    match axiomsOf env proof with
    | .error e => return some e
    | .ok axioms =>
      match axioms.toList.filter (!allowed.contains ·) with
      | [] => return none
      | [one] =>
        return some s!"{proof} depends on the axiom {one}, which is not one of Lean's foundations"
      | many =>
        return some s!"{proof} depends on the axioms {", ".intercalate (many.map toString)}, which are not among Lean's foundations"
  | some _ => return some s!"{proof} is not a theorem"
  | none => return some s!"{module} declares no {proof}"

/-- The declaration of the user's lemmas that uses `sorry`, if one does: an
admitted lemma fails every goal, as when the module was compiled with `sorry`
an error. -/
def userSorry (closure : Closure) (project : Replayed) : Option String := Id.run do
  let some user := closure.modules.find? (·.name == `CppVerify.User) | return none
  for name in user.declared do
    if let .ok axioms := axiomsOf project.env name then
      if axioms.contains ``sorryAx then
        return some s!"{name} of CppVerify.User uses sorry"
  return none

/-- What a check reports: the goal, or the theorem that refutes it. -/
def shown (goal : Name) (refutes : Bool) : Name :=
  if refutes then goal.appendAfter "_refuted" else goal

/-- Usage: Certify GOALS ALLOWED, where each line of GOALS is a goal, its
proof module, and the module that defines it, separated by tabs, then
`refutation` for a module that refutes the goal it defines, and ALLOWED lists
the axioms a proof may use, separated by commas. Prints one line per goal:
`ok` or `fail`, the goal (a refutation's theorem for a refutation), and why it
failed. A goal is proved when its proof module and its generated module pass
the kernel, with every module of the project they import, and its proof
states exactly the goal (a refutation, its negation) and uses only the
allowed axioms. The generated modules are replayed first, so that a proof
file that declares a name one declares is the one left out. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [goals, allowed] := args | throw <| IO.userError "usage: Certify GOALS ALLOWED"
  let sysroot ← findSysroot
  initSearchPath sysroot
  let toolchain := (sysroot / "lib" / "lean").toString
  let allowed := (allowed.splitOn ",").foldl (fun s a => s.insert a.toName) ({} : NameSet)
  let mut entries : Array (Name × Name × Name × Bool) := #[]
  for line in ← IO.FS.lines goals do
    match line.splitOn "\t" with
    | [goal, module, generated] =>
      entries := entries.push (goal.toName, module.toName, generated.toName, false)
    | [goal, module, generated, "refutation"] =>
      entries := entries.push (goal.toName, module.toName, generated.toName, true)
    | _ => continue
  let roots := entries.map (·.2.2.1) ++ entries.map (·.2.1)
  let (_, closure) ← (roots.forM (Closure.visit toolchain)).run {}
  let project ← replayProject closure
  let user := userSorry closure project
  for (goal, module, generated, refutes) in entries do
    let why := (project.rejected[module]?).orElse fun _ =>
      (project.rejected[generated]?).orElse fun _ => user.orElse fun _ =>
        checkStatement project goal module generated refutes allowed
    match why with
    | none => IO.println s!"ok\t{shown goal refutes}"
    | some why => IO.println s!"fail\t{shown goal refutes}\t{why.replace "\n" " "}"
  return 0
)lean";

} // namespace verify
} // namespace clang

#endif
