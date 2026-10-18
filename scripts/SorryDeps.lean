/-
List the declarations with `sorry` that a declaration depends on.

Usage (after `lake build`; `just sorries` does both):

    lake env lean --run scripts/SorryDeps.lean [--count] NAME...
    lake env lean --run scripts/SorryDeps.lean --all

Each NAME may omit the `NoEmbeddedEigenvalues.` prefix. For each NAME the script
follows constants used in types and values through the project modules and reports
every declaration whose own elaborated term contains `sorryAx`, with its source
location. Auxiliary declarations (`foo._proof_1`, `foo.match_1`, ...) are reported
under the declaration they belong to. Project `axiom`s in the closure are reported
too. With `--count`, print one line `NAME<TAB>COUNT` per name instead. With `--all`,
list every admission in the project, used or not.

This reads the built `.olean` files, so the result is only as current as the last
build. Mathlib is not traversed: it cannot depend on project declarations.
-/
import Lean

open Lean

namespace SorryDeps

def project : Name := `NoEmbeddedEigenvalues

def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => project.isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

def ranges? (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n

/-- The source-level declaration an auxiliary declaration belongs to: the nearest prefix
with a source range. -/
partial def sourceDecl (env : Environment) (n : Name) : Name :=
  if (ranges? env n).isSome then n
  else match n with
    | .str p _ | .num p _ => if p.isAnonymous then n else sourceDecl env p
    | .anonymous => n

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _) => "theorem"
  | some (.defnInfo _) => "def"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "constructor"
  | some (.recInfo _) => "recursor"
  | some (.quotInfo _) => "quot"
  | none => "?"

def location (env : Environment) (n : Name) : String :=
  let file := match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!.toString.replace "." "/") ++ ".lean"
    | none => "?"
  match ranges? env n with
  | some r => s!"{file}:{r.selectionRange.pos.line}"
  | none => file

def isAdmission (c : ConstantInfo) : Bool :=
  c.getUsedConstantsAsSet.contains ``sorryAx || c matches .axiomInfo _

/-- Admissions (as source declarations) among all project constants. -/
def allAdmissions (env : Environment) : NameSet :=
  env.constants.fold (init := {}) fun acc n c =>
    if inProject env n && isAdmission c then acc.insert (sourceDecl env n) else acc

/-- Admissions (as source declarations) in the closure of `root`, restricted to the
project. -/
def admissions (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut found : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !inProject env n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    if isAdmission c then
      found := found.insert (sourceDecl env n)
    for m in c.getUsedConstantsAsSet do
      unless seen.contains m do todo := todo.push m
  return found

/-- Resolve a command-line name: exact, with the project prefix, or a private name. -/
def resolve (env : Environment) (s : String) : Option Name :=
  let n := s.toName
  let candidates := [n, project ++ n]
  match candidates.find? env.contains with
  | some m => some m
  | none =>
    -- Private declarations are stored as `_private.<module>.0.<name>`.
    env.constants.map₁.fold (init := none) fun acc m _ =>
      acc <|> if candidates.contains (privateToUserName m) && inProject env m then some m
        else none

end SorryDeps

open SorryDeps in
unsafe def main (args : List String) : IO UInt32 := do
  let countOnly := args.contains "--count"
  let all := args.contains "--all"
  let names := args.filter (!["--count", "--all"].contains ·)
  if names.isEmpty == !all then
    IO.eprintln "usage: lake env lean --run scripts/SorryDeps.lean [--count] NAME... | --all"
    return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := project }] {} (loadExts := true)
  if all then
    let found := (allAdmissions env).toArray.qsort (·.toString < ·.toString)
    IO.println s!"{found.size} admissions in the project"
    for m in found do
      IO.println s!"  {privateToUserName m}  [{kindOf env m}]  {location env m}"
    return 0
  let mut status : UInt32 := 0
  for s in names do
    let some n := resolve env s
      | IO.eprintln s!"unknown declaration: {s}"; status := 1; continue
    let found := (admissions env n).toArray.qsort (·.toString < ·.toString)
    let display := privateToUserName n
    if countOnly then
      IO.println s!"{display}\t{found.size}"
      continue
    let noun := if found.size == 1 then "admission" else "admissions"
    IO.println s!"{display}: {found.size} {noun}"
    for m in found do
      let own := if m == n then "  (itself)" else ""
      IO.println s!"  {privateToUserName m}  [{kindOf env m}]  {location env m}{own}"
  return status
