module

import Lean

open Lean

/-- Check the declaration names collected by the blueprint HTML build. -/
public unsafe def main (args : List String) : IO UInt32 := do
  let path := args.headD "blueprint/lean_decls"
  let refs := ((← IO.FS.readFile path).splitOn "\n").map (·.trimAscii.toString)
  let names := (refs.filter (!·.isEmpty)).eraseDups
  if names.isEmpty then
    IO.eprintln s!"{path}: no Lean declaration names found"
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `EulerDipoleEigenvalues }] {}
  let missing := names.filter fun ref => !env.contains ref.toName
  for ref in missing do
    IO.eprintln s!"Missing blueprint declaration: {ref}"
  IO.println s!"{names.length} distinct blueprint declarations checked; {missing.length} missing"
  return if missing.isEmpty then 0 else 1
