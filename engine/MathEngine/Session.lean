import MathEngine.SimpRules
import MathEngine.DiffRules
import MathEngine.LinAlg
import MathEngine.ExpandRules
import MathEngine.Numeric
import MathEngine.Print
import MathEngine.Parser
/-!
# Sessions, commands and the evaluation pipeline

A session is one notebook: `let` bindings plus each cell's output and derivation (for
`engine.explain`). Notebook commands are rules too: they fire on `fn` nodes with reserved names.
The combined pipeline runs under `normalizeFuel` (see the step-2 note in `book/TRACKING.md`).
-/
namespace MathEngine
open Expr

structure Cell where
  output : Expr
  derivation : Derivation

structure Session where
  env : List (String × Expr) := []
  cells : List (String × Cell) := []

/-- All sessions the engine knows about, keyed by `sessionId`. Threaded through `handle` by the host. -/
abbrev Store := List (String × Session)

def Store.get (st : Store) (id : String) : Session := (st.lookup id).getD {}
def Store.set (st : Store) (id : String) (s : Session) : Store := (id, s) :: st.filter (·.1 != id)
def Store.reset (st : Store) (id : String) : Store := st.filter (·.1 != id)

def maxSteps : Nat := 10000

def simpPlain : List PlainRule := simpRules.map Rule.toPlain
def expandSet : List PlainRule := expandRules ++ simpPlain

/-- Notebook commands: `simplify`, `expand`, `rref`, `N`, `subst`. -/
def commandRules : List PlainRule := [
  { name := "cmd.simplify", apply := fun e =>
      match e with
      | .fn "simplify" [a] => some ⟨a, "Arguments are already in simplified normal form.", none, none⟩
      | _ => none },
  { name := "cmd.expand", apply := fun e =>
      match e with
      | .fn "expand" [a] =>
        match nested expandSet maxSteps a with
        | .ok (out, sub) => some ⟨out, "Expand products and powers of sums by repeated distribution.", sub, none⟩
        | .error msg => some ⟨a, "", none, some msg⟩
      | _ => none },
  { name := "cmd.rref", apply := fun e =>
      match e with
      | .fn "rref" [.matrix rows] =>
        let (out, steps) := rref rows
        some ⟨out, "Gauss–Jordan elimination to reduced row echelon form.",
          if steps.isEmpty then none else some ⟨.matrix rows, steps, out⟩, none⟩
      | _ => none },
  { name := "cmd.N", apply := fun e =>
      match e with
      | .fn "N" [a] =>
        if a.isNum then none else
        match evalNumeric [] a >>= floatToExpr with
        | .ok v => some ⟨v, "Numerical approximation in IEEE-754 double precision.", none, none⟩
        | .error msg => some ⟨a, "", none, some msg⟩
      | _ => none },
  { name := "cmd.subst", apply := fun e =>
      match e with
      | .fn "subst" [body, .var x, v] => some ⟨substitute [(x, v)] body, s!"Substitute ${x} := {v.toText}$.", none, none⟩
      | _ => none }
]

def pipelineRules : List PlainRule := commandRules ++ diffRules ++ matrixRules ++ simpPlain

/-- Evaluate one cell: parse, substitute the session's bindings, normalize with a trace, record the
cell. Returns the updated session and either an error or the output with its derivation. -/
def evaluateCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Stmt × Expr × Derivation) :=
  match parseStmt source with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    let input := substitute s.env stmt.value
    match (normalizeFuel pipelineRules maxSteps input).run #[] with
    | (.error msg, _) => (s, .error ("eval", msg, none))
    | (.ok output, steps) =>
      let d : Derivation := ⟨input, steps, output⟩
      let s := { s with cells := (cellId, ⟨output, d⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match stmt with
        | .«let» name _ => { s with env := (name, output) :: s.env.filter (·.1 != name) }
        | _ => s
      (s, .ok (stmt, output, d))

def isPrefix : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

/-- Which steps produced the subterm at `path` in the cell's output? Prototype heuristic: every step
that fired at, above, or below that path. Rewriting *moves* subterms, so this over-approximates;
proper origin tracking is M6. -/
def explainCell (s : Session) (cellId : String) (path : Path) : Except String (Expr × Array Step) :=
  match s.cells.lookup cellId with
  | none => .error s!"unknown cell {cellId}"
  | some cell =>
    match cell.output.at? path with
    | none => .error s!"bad path {path}"
    | some sub => .ok (sub, cell.derivation.steps.filter fun st => isPrefix st.path path || isPrefix path st.path)

end MathEngine
