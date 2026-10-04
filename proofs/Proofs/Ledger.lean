import Proofs.Q
import Proofs.Semantics
import Proofs.SimpReal
import Proofs.Deriv
import Proofs.Integrate
import Proofs.Expand
import Proofs.Radical
import Proofs.Cx
import Proofs.CxRules
import Proofs.Fourier
import Proofs.Stats
import Proofs.Matrix
import Proofs.SimpAll
import Lean
/-!
# The ledger cites what exists

`engine.capabilities` reports every rule's status with a note, and a note names the theorems behind
it: `(sol_rref)`, `(Real.rpow_def_of_pos)`, `(SemEqR.canon)`. The notes are prose, written by hand,
so nothing tied them to the theorems: a renamed or deleted theorem left a `verified` claim standing.
`#check_ledger` reads the ledger from the engine itself (`MathEngine.ruleStatus`) and fails the
build unless every name a note cites is a declaration here, among the engine's theorems, these
proofs and Mathlib. `proofs.yml` builds this file, so the check runs in CI.
-/
open Lean Elab Command

namespace MathProofs.Ledger

/-- The theorem names a ledger note cites: identifiers with an underscore (`sol_rref`,
`Real.rpow_def_of_pos`) or a namespace and a lower-case name (`SemEqR.canon`). -/
def citations (note : String) : List String :=
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\''
  let words := (note.splitOn " ").flatMap fun w => (String.ofList w.toList).split (fun c => !isId c) |>.toList.map (·.copy)
  words.filterMap fun w =>
    let w := (w.dropWhile (· == '.')).copy
    let w := (w.dropEndWhile (fun c => c == '.' || c == '\'')).copy
    let parts := w.splitOn "."
    let ok := w.length > 1 && (w.front.isAlpha) && !w.endsWith ".lean" &&
      (w.contains '_' && !w.endsWith "_" ||
       (parts.length ≥ 2 && (parts.head!.front.isUpper) && (parts.getLast!.front.isLower)))
    if ok then some w else none

/-- Every `(rule, status, note)` of the ledger, the ℂ notes included. -/
def notes : List (String × String × String) :=
  match MathEngine.ruleStatus with
  | .arr xs => xs.toList.flatMap fun j =>
    let get (k : String) := match j.get? k with | some (.str s) => s | _ => ""
    let base := (get "rule", get "status", get "note")
    match j.get? "complex" with
    | some c => [base, (get "rule", (match c.get? "status" with | some (.str s) => s | _ => ""), match c.get? "note" with | some (.str s) => s | _ => "")]
    | none => [base]
  | _ => []

end MathProofs.Ledger

open MathProofs.Ledger in
/-- Fails unless every theorem the ledger cites is a declaration (matched by its last components, so
`sol_rref` finds `MathEngine.LinQ.sol_rref`). -/
elab "#check_ledger" : command => do
  let env ← getEnv
  let cited := notes.flatMap fun (rule, _, note) => (citations note).map (rule, ·)
  let lasts : Std.HashSet String := cited.foldl (fun s (_, c) => s.insert ((c.splitOn ".").getLast!)) {}
  let mut found : Std.HashSet Name := {}
  for (n, _) in env.constants.toList do
    if let .str _ last := n then
      if lasts.contains last then found := found.insert n
  let mut missing : Array String := #[]
  for (rule, c) in cited do
    let target := c.toName
    unless found.toList.any (fun n => target.isSuffixOf n) do
      missing := missing.push s!"{rule}: {c}"
  if missing.isEmpty then
    logInfo m!"ledger: {cited.length} citations, every one a declaration"
  else
    throwError m!"the ledger cites declarations that do not exist:\n{"\n".intercalate missing.toList}"


#check_ledger
