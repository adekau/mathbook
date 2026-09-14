import MathEngine.PipelineOrder
import MathEngine.Parser
/-!
# Sessions, commands and the evaluation pipeline

A session is one notebook: `let` bindings plus each cell's output and derivation (for
`engine.explain`). Notebook commands are rules too: they fire on `fn` nodes with reserved names.
The combined pipeline and its rule set live in `Pipeline.lean`; cells are normalized by `normalizeT`
(Terminate.lean), whose termination is the theorem `pipelineOrdered` (PipelineOrder.lean) — no step budget.
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

/-- Evaluate one cell: parse, substitute the session's bindings, normalize with a trace, record the
cell. Returns the updated session and either an error or the output with its derivation. -/
def evaluateCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Stmt × Expr × Derivation) :=
  match parseStmt source with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    let input := substitute s.env stmt.value
    match (normalizeT pipelineRules pipelineOrdered input).run #[] with
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
