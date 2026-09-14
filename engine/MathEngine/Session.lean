import MathEngine.Integrate
import MathEngine.Origin
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
  /-- `let f(x, y) = …` definitions, by name. -/
  fns : List (String × FnDef) := []
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
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    -- a function's parameters are bound by the definition, not by the session
    let params := match stmt with | .«let» _ ps _ => ps | _ => []
    let env := s.env.filter fun (x, _) => !params.contains x
    let input := substitute env (substituteFns s.fns stmt.value)
    match (normalizeT pipelineRules pipelineOrdered input).run #[] with
    | (.error msg, _) => (s, .error ("eval", msg, none))
    | (.ok output, steps) =>
      let d : Derivation := ⟨input, steps, output⟩
      let s := { s with cells := (cellId, ⟨output, d⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match stmt with
        | .«let» name [] _ => { s with env := (name, output) :: s.env.filter (·.1 != name) }
        | .«let» name ps _ => { s with fns := (name, (ps, output)) :: s.fns.filter (·.1 != name) }
        | _ => s
      (s, .ok (stmt, output, d))

/-- A sampled plot: the variable, the range, and `(t, y)` pairs (`none` where `f` has no finite value). -/
structure Plot where
  var : String
  from_ : Float
  to : Float
  points : Array (Float × Option Float)

/-- `plot(f, x, from, to[, n])`: simplify `f` under the session (so derivatives and session functions
plot as what they are), record the cell like any other, and sample `f` on a uniform grid with the
numeric evaluator. Sampling is presentation: the derivation shown is `f`'s. -/
def plotCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Expr × Derivation × Plot) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    let bad := (s, .error ("eval", "plot takes a function, a variable, and the range: plot(f, x, from, to)", none))
    match stmt.value with
    | .fn "plot" (f :: .var x :: a :: b :: rest) =>
      let num (e : Expr) : Option Float := (evalNumeric [] (substitute s.env (substituteFns s.fns e))).toOption
      match num a, num b with
      | some lo, some hi =>
        let n : Nat := match rest with
          | [.num k] => min 4000 (max 2 k.val.num.toNat)
          | _ => 300
        let input := substitute (s.env.filter (·.1 != x)) (substituteFns s.fns f)
        match (normalizeT pipelineRules pipelineOrdered input).run #[] with
        | (.error msg, _) => (s, .error ("eval", msg, none))
        | (.ok output, steps) =>
          let d : Derivation := ⟨input, steps, output⟩
          let s := { s with cells := (cellId, ⟨output, d⟩) :: s.cells.filter (·.1 != cellId) }
          let points := (Array.range n).map fun i =>
            let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
            let y := (evalNumeric [(x, t)] output).toOption.filter fun v => v.isFinite
            (t, y)
          (s, .ok (f, output, d, ⟨x, lo, hi, points⟩))
      | _, _ => (s, .error ("eval", "plot: the range must evaluate to numbers", none))
    | _ => bad

def isPrefix : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

/-- Which of a cell's terms a path refers to. -/
inductive TermRef where
  | input
  | output
  | step (n : Nat)

/-- The subterm at `path` in the chosen term, and the steps that produced it with how (M6 origin
tracking, `Origin.lean`). Steps come back in derivation order, each once; the relations carry the
finer story (a step can both create a node and copy one of its parts). -/
def explainCell (s : Session) (cellId : String) (path : Path) (ref : TermRef := .output) :
    Except String (Expr × Array Step × List (Nat × Relation)) :=
  match s.cells.lookup cellId with
  | none => .error s!"unknown cell {cellId}"
  | some cell =>
    let d := cell.derivation
    let (term, k) : Expr × Nat := match ref with
      | .input => (d.input, 0)
      | .output => (cell.output, d.steps.size)
      | .step n => ((d.steps[n]?.map (·.after)).getD cell.output, n)
    match term.at? path with
    | none => .error s!"bad path {path}"
    | some sub =>
      let infos := d.steps.map fun st => ({ before := st.before, after := st.after, path := st.path } : StepInfo)
      let rels := match ref with
        | .input => []
        | _ => trace infos cell.output k path
      -- one relation per step: created beats copied beats contains
      let rank : Relation → Nat | .created => 0 | .copied => 1 | .contains => 2
      let indices := (rels.map (·.1)).eraseDups.mergeSort (· ≤ ·)
      let best := indices.map fun i =>
        let rs := (rels.filter (·.1 == i)).map (·.2)
        (i, rs.foldl (fun b r => if rank r < rank b then r else b) .contains)
      let steps := best.filterMap fun (i, _) => d.steps[i]?
      .ok (sub, steps.toArray, best)

end MathEngine
