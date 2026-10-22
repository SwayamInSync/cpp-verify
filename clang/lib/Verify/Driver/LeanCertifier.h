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
def axiomsOf (env : Environment) (root : Name) : Except String NameSet := Id.run do
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

/-- Replays a module's own constants into the environment of its imports with
the kernel, as leanchecker does: nothing in it escaped the kernel. -/
unsafe def replayModule (module : Name) : IO Unit := do
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
  let (data, _) := parts[0]
  let (_, s) ← importModulesCore data.imports |>.run
  let env ← finalizeImport s data.imports {} 0 false false (isModule := true)
  let mut constants := {}
  for name in parts[parts.size - 1].1.constNames, info in parts[parts.size - 1].1.constants do
    constants := constants.insert name info
  discard <| env.toKernelEnv.replay constants

/-- Whether the proof of a goal states exactly the goal the generated module
defines and depends on no axiom outside the allowed ones. -/
def checkStatement (env : Environment) (goal module : Name) (allowed : NameSet) :
    Option String := Id.run do
  let generated := `CppVerify.Generated
  let moduleOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).bind fun i => env.header.moduleNames[i.toNat]?
  let proof := goal.appendAfter "_proof"
  match env.find? goal with
  | some (.defnInfo _) =>
    if moduleOf goal != some generated then
      return some s!"{goal} is not the goal {generated} defines"
  | _ => return some s!"{generated} defines no goal {goal}"
  match env.find? proof with
  | some (.thmInfo v) =>
    if moduleOf proof != some module then
      return some s!"{proof} is not declared in {module}"
    if v.type != .const goal [] then
      return some s!"{proof} proves {v.type}, not {goal}"
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

/-- A goal is proved when every module of the project its proof imports passes
the kernel (each replayed once in a run), and its proof states exactly the
goal and uses only the allowed axioms. Imported data is never freed: a later
import in the process reads it. -/
unsafe def checkGoal (goal module : Name) (allowed : NameSet) (toolchain : String)
    (replayed : IO.Ref NameSet) : IO (Option String) := do
  let env ← importModules #[{ module }] {}
  let project ← env.header.moduleNames.filterM fun m =>
    return !(← findOLean m).toString.startsWith toolchain
  let why := checkStatement env goal module allowed
  for m in project do
    if (← replayed.get).contains m then continue
    try replayModule m
    catch e => return some s!"the kernel rejects {m}: {e}"
    replayed.modify (·.insert m)
  return why

/-- Usage: Certify GOALS ALLOWED, where each line of GOALS is a goal and its
proof module, separated by a tab, and ALLOWED lists the axioms a proof may
use, separated by commas. Prints one line per goal: `ok` or `fail`, the goal,
and why it failed. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [goals, allowed] := args | throw <| IO.userError "usage: Certify GOALS ALLOWED"
  let sysroot ← findSysroot
  initSearchPath sysroot
  let toolchain := (sysroot / "lib" / "lean").toString
  let allowed := (allowed.splitOn ",").foldl (fun s a => s.insert a.toName) ({} : NameSet)
  let replayed ← IO.mkRef ({} : NameSet)
  for line in ← IO.FS.lines goals do
    let [goal, module] := line.splitOn "\t" | continue
    match ← checkGoal goal.toName module.toName allowed toolchain replayed with
    | none => IO.println s!"ok\t{goal}"
    | some why => IO.println s!"fail\t{goal}\t{why.replace "\n" " "}"
  return 0
)lean";

} // namespace verify
} // namespace clang

#endif
