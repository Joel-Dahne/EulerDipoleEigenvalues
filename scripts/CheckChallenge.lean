/-
Compare `Solution` against `Challenge`, an unsandboxed stand-in for the comparator.

Usage (after `lake build Challenge Solution`; `just challenge` does both):

    lake env lean --run scripts/CheckChallenge.lean [comparator.json]

Reads `challenge_module`, `solution_module`, `theorem_names` and `permitted_axioms` from the
comparator configuration and checks:

1. every constant that a challenge theorem's statement depends on, through the types and
   values of the definitions in the challenge module, exists in the solution environment with
   the same kind, universe parameters, type and (for definitions) value;
2. each theorem has the same statement in both;
3. each solution theorem depends on no axiom outside `permitted_axioms`; `sorryAx` is reported
   as an admission.

Constants outside the challenge module (Lean core and Mathlib) are compared by type only and
not traversed: both environments load the same build of them. Unlike the comparator, this does
not sandbox the build or replay proofs in the kernel; it checks that the two files agree, not
that a solution is not adversarial. Lean v4.35 provides the real check as `lake comparator`.
-/
import Lean

open Lean

namespace CheckChallenge

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

def inModule (env : Environment) (mod n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]! == mod
  | none => false

/-- Compare one constant; return an error message on mismatch. -/
def compareConst (mod : Name) (cenv senv : Environment) (n : Name) : Option String := Id.run do
  let some c := cenv.find? n | return some s!"{n}: missing in the challenge"
  let some s := senv.find? n | return some s!"{n}: missing in the solution"
  if kind c != kind s then return some s!"{n}: {kind c} in the challenge, {kind s} in the solution"
  if c.levelParams != s.levelParams then return some s!"{n}: universe parameters differ"
  if c.type != s.type then return some s!"{n}: types differ"
  if inModule cenv mod n then
    match c, s with
    | .defnInfo c, .defnInfo s =>
      if c.value != s.value then return some s!"{n}: values differ"
      if c.safety != s.safety then return some s!"{n}: safety differs"
    | .opaqueInfo c, .opaqueInfo s =>
      if c.value != s.value then return some s!"{n}: values differ"
    | _, _ => pure ()
  return none

/-- The constants a statement depends on, following types and definition values inside the
challenge module. -/
def statementClosure (mod : Name) (env : Environment) (root : Expr) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut order := #[]
  let mut todo := root.getUsedConstants
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    order := order.push n
    unless inModule env mod n do continue
    let some c := env.find? n | continue
    let used := match c with
      | .thmInfo c => c.type.getUsedConstants
      | _ => c.getUsedConstantsAsSet.toArray
    for m in used do
      unless seen.contains m do todo := todo.push m
  return order

/-- Axioms a constant depends on, through types and values. -/
def axioms (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut found := #[]
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    if c matches .axiomInfo _ then found := found.push n
    for m in c.getUsedConstantsAsSet do
      unless seen.contains m do todo := todo.push m
  return found.qsort (·.toString < ·.toString)

def getStr (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

def getStrs (j : Json) (key : String) : Except String (Array String) := do
  (← (← j.getObjVal? key).getArr?).mapM (·.getStr?)

end CheckChallenge

open CheckChallenge in
unsafe def main (args : List String) : IO UInt32 := do
  let path := args.headD "comparator.json"
  let cfg ← match Json.parse (← IO.FS.readFile path) with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"{path}: {e}"
  let read {α} (x : Except String α) : IO α := match x with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"{path}: {e}"
  let cmod := (← read (getStr cfg "challenge_module")).toName
  let smod := (← read (getStr cfg "solution_module")).toName
  let thms := (← read (getStrs cfg "theorem_names")).map String.toName
  let permitted := (← read (getStrs cfg "permitted_axioms")).map String.toName
  initSearchPath (← findSysroot)
  let cenv ← importModules #[{ module := cmod }] {}
  let senv ← importModules #[{ module := smod }] {}
  let mut errors := #[]
  let mut admitted := #[]
  let mut checked : NameSet := {}
  for t in thms do
    let some c := cenv.find? t
      | errors := errors.push s!"{t}: not in the challenge"; continue
    unless c matches .thmInfo _ do
      errors := errors.push s!"{t}: not a theorem in the challenge"
    for n in statementClosure cmod cenv c.type do
      if checked.contains n then continue
      checked := checked.insert n
      if let some e := compareConst cmod cenv senv n then errors := errors.push e
    match senv.find? t with
    | some (.thmInfo s) =>
      if s.type != c.type then errors := errors.push s!"{t}: statements differ"
      if s.levelParams != c.levelParams then
        errors := errors.push s!"{t}: universe parameters differ"
      for a in axioms senv t do
        if a == ``sorryAx then admitted := admitted.push t
        else unless permitted.contains a do
          errors := errors.push s!"{t}: uses the axiom {a}"
    | some _ => errors := errors.push s!"{t}: not a theorem in the solution"
    | none => errors := errors.push s!"{t}: not in the solution"
  IO.println s!"{thms.size} theorems, {checked.size} statement constants compared"
  for e in errors do IO.println s!"error: {e}"
  for t in admitted do IO.println s!"admitted: {t} depends on sorryAx"
  if !errors.isEmpty then return 1
  if !admitted.isEmpty then
    IO.println "statements agree; some solution theorems still depend on admissions"
    return 2
  IO.println "statements agree and all solution theorems are proved"
  return 0
