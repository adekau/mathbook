import MathEngine.Integrate
import MathEngine.Origin
import MathEngine.Parser
import MathEngine.Stlc
import MathEngine.Poset
import MathEngine.Relation
import MathEngine.Algebra
import MathEngine.Fourier
import MathEngine.Logic
import MathEngine.Systems
import MathEngine.Replicas
import MathEngine.Rewriting
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
  /-- A λ-cell: its steps carry the de Bruijn view too (`lambdaDbSteps`). -/
  lambda : Bool := false

structure Session where
  env : List (String × Expr) := []
  /-- `let f(x, y) = …` definitions, by name. -/
  fns : List (String × FnDef) := []
  /-- λ-cell definitions (`name := term`), by name; the Church library sits behind them. -/
  lambdas : List (String × Lam.Term) := []
  /-- Order-world values: posets and maps on them, by name. -/
  posets : List (String × Ord.Poset) := []
  pmaps : List (String × Ord.PMap) := []
  /-- Relations (order world) bound by `let`, by name. -/
  rels : List (String × Ord.Rel) := []
  /-- Operation tables and formal contexts (order world, `Algebra.lean`) bound by `let`, by name. -/
  ops : List (String × Ord.Op) := []
  ctxs : List (String × Ord.Ctx) := []
  /-- Transition systems (`Systems.lean`) bound by `let`, by name. -/
  systems : List (String × Sys.System) := []
  /-- Rewriting systems (`let R = rules(…)`), by name. -/
  trss : List (String × TRS.System) := []
  /-- Logic-world formulas bound by `let`, by name. -/
  formulas : List (String × Logic.Fm) := []
  cells : List (String × Cell) := []
  /-- Outputs by evaluation number, for `%`, `%%` and `%n`; `nextOut` is the number the next
  evaluation gets (every evaluation takes one, error or not, like Mathematica's `In[n]`). -/
  outs : List (Nat × Expr) := []
  nextOut : Nat := 1

/-- Number an evaluation and remember its output, if it had one. Returns the label. -/
def Session.tick (s : Session) (out : Option Expr) : Session × Nat :=
  let n := s.nextOut
  ({ s with nextOut := n + 1, outs := match out with | some e => (n, e) :: s.outs | none => s.outs }, n)

/-- Replace `%`, `%%`, `%n` (parsed as `%prev k` / `%out n`) by the outputs they name. -/
partial def Session.resolveOuts (s : Session) : Expr → Except String Expr
  | .fn "%prev" [.num k] =>
    let k := k.val.num.toNat
    if k ≥ s.nextOut then .error (if k == 1 then "% refers to the previous output, and there is none yet" else s!"{String.mk (List.replicate k '%')} refers to output {s.nextOut - k}, which does not exist")
    else match s.outs.lookup (s.nextOut - k) with
      | some e => .ok e
      | none => .error s!"Out[{s.nextOut - k}] has no value (that evaluation failed)"
  | .fn "%out" [.num n] =>
    match s.outs.lookup n.val.num.toNat with
    | some e => .ok e
    | none => .error s!"Out[{n.toText}] is not defined"
  | e => do pure (withChildren e (← (children e).mapM s.resolveOuts))

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
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok value =>
    let input := substitute env (substituteFns s.fns value)
    match (normalizeT pipelineRules pipelineOrdered input).run #[] with
    | (.error msg, _) => (s, .error ("eval", msg, none))
    | (.ok output, steps) =>
      let d : Derivation := ⟨input, steps, output⟩
      let s := { s with cells := (cellId, { output, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match stmt with
        | .«let» name [] _ => { s with env := (name, output) :: s.env.filter (·.1 != name) }
        | .«let» name ps _ => { s with fns := (name, (ps, output)) :: s.fns.filter (·.1 != name) }
        | _ => s
      (s, .ok (stmt, output, d))

/-- The de Bruijn view of each step's result in a λ-cell's derivation, in step order. The steps
store the encoded term; decode it. A step whose result is not a term (a type, a set) shows as it is. -/
def lambdaDbSteps (d : Derivation) : Array Expr :=
  d.steps.map fun st => match Lam.ofExpr st.after with
    | some t => Lam.dbToExpr (Lam.toDB [] t)
    | none => st.after

/-- What a λ-cell produced. -/
structure LamResult where
  name : Option String
  /-- What the cell shows: a term, or, for a command, a type, a set of variables or a verdict. -/
  value : Expr
  /-- The value as a term, when it is one: it has a de Bruijn view and may be read as a numeral. -/
  term : Option Lam.Term
  derivation : Derivation
  /-- The de Bruijn view of each step's result, in step order. -/
  dbSteps : Array Expr
  reading : Option String
  /-- A typing derivation to draw (`type:` and `infer:`). -/
  tree : Option Lam.Deriv := none
  /-- The command the cell ran (`cbv`, `type`, …), if any. -/
  command : Option Lam.Cmd := none
  /-- The type found by `type:` or `infer:`. -/
  ty : Option Lam.Ty := none

/-- The names a λ-cell may use: the session's definitions, then the Church library. -/
def lambdaDefs (s : Session) : List (String × Lam.Term) := s.lambdas ++ Lam.churchDefs

/-- Is the source a λ-cell for this session? -/
def isLambdaCell (s : Session) (source : String) : Bool :=
  Lam.isLambdaSource source ((lambdaDefs s).map (·.1))

/-- What a normal form encodes, when it is a Church numeral or boolean. -/
def churchReading (t : Lam.Term) : Option String :=
  match Lam.readChurch t with
  | some n => some s!"the Church numeral {n}"
  | none => match Lam.readBool t with
    | some true => some "the Church boolean true"
    | some false => some "the Church boolean false"
    | none => none

private def lamTex (e : Expr) : String := "$" ++ e.toLatex false ++ "$"

/-- Which redex a strategy contracts, for a step's explanation. -/
private def redexText : Lam.Strategy → String
  | .normal => "the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracts to $b[x := a]$."
  | .cbn => "call by name: the leftmost-outermost redex outside every λ contracts to $b[x := a]$, its argument passed unevaluated."
  | .cbv => "call by value: the leftmost redex whose argument is already a value (a variable or a λ) contracts to $b[x := a]$; arguments are evaluated before the call, and nothing under a λ is."
  | .applicative => "applicative order: the leftmost-innermost redex contracts to $b[x := a]$; the function and its argument are reduced to normal form first, under λ too."

private def lamStep (st : Lam.Strategy) (prev t' : Lam.Term) : Lam.StepKind → Step
  | .beta => ⟨"lambda.beta", "β: " ++ redexText st, [], Lam.toExpr prev, Lam.toExpr t', none⟩
  | .alphaBeta =>
    if st == .normal then
      ⟨"lambda.alpha-beta", "α then β: a binder of the body was renamed so the argument's free variables are not captured, then the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracted to $b[x := a]$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩
    else ⟨"lambda.alpha-beta", "α then β: a binder of the body was renamed so the argument's free variables are not captured; then, " ++ redexText st, [], Lam.toExpr prev, Lam.toExpr t', none⟩
  | .eta => ⟨"lambda.eta", "η: $\\lambda x.\\, f\\ x$ contracts to $f$, since $x$ is not free in $f$: both give $f\\ a$ applied to any $a$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩

private abbrev LamErr := String × String × Option (Nat × Nat)

/-- Unfold the definitions (one δ-step), then take the strategy's steps (β, or β and η) until none
applies, `limit` steps are taken (`Lam.maxSteps` without one), or the term grows past `Lam.maxSize`.
Returns the term reached, the steps shown (a long run's middle is one step saying how many it
leaves out), why it stopped, and how many steps it took. -/
private def lamRun (s : Session) (t : Lam.Term) (st : Lam.Strategy) (eta : Bool) (limit : Option Nat) :
    Lam.Term × Lam.Term × Array Step × Lam.Halt × Nat :=
  let expanded := Lam.expandDefs (lambdaDefs s) t
  let δ : Array Step := if expanded != t then
      #[⟨"lambda.delta", "δ: unfold the definitions used (the session's, then the Church library's).", [], Lam.toExpr t, Lam.toExpr expanded, none⟩]
    else #[]
  let r : Lam.Run Lam.StepKind :=
    if eta then Lam.runSteps Lam.betaEtaStep expanded (limit.getD Lam.maxSteps)
    else Lam.runSteps (fun u => (st.step u).map fun (u', r) => (u', if r then Lam.StepKind.alphaBeta else .beta)) expanded (limit.getD Lam.maxSteps)
  let chain (acc : Array Step) (base : Lam.Term) (ts : List (Lam.Term × Lam.StepKind)) :=
    (ts.foldl (fun (acc, prev) (t', k) => (acc.push (lamStep st prev t' k), t')) (acc, base)).1
  let steps := chain δ expanded r.first
  let steps := if r.dropped == 0 then steps else
    let upTo := (r.first.getLast?.map (·.1)).getD expanded
    steps.push ⟨"lambda.elided", s!"{r.dropped} more steps, the same rule each time, not shown: the work shows the first {r.first.length} and the last {r.last.length} of {r.count}.", [], Lam.toExpr upTo, Lam.toExpr r.lastFrom, none⟩
  let steps := chain steps r.lastFrom r.last
  (expanded, r.out, steps, r.halt, r.count)

/-- Why a run that did not reach its goal is refused: the step budget, or the term's growth. -/
private def haltError (halt : Lam.Halt) (goal how : String) (steps : Nat) (out : Lam.Term) : LamErr :=
  if halt == .size then
    ("eval", s!"λ: no {goal} yet after {steps} steps{how}, and the term has grown past {Lam.maxSize} symbols, so the reduction stops here", none)
  else
    -- a long term is cut short: the message is to read, and the head says what is happening
    let txt := (Lam.toExpr out).toText
    let txt := if txt.length > 240 then (txt.take 240).copy ++ " …" else txt
    ("eval", s!"λ: no {goal} after {Lam.maxSteps} {if how.isEmpty then "β-steps" else "steps" ++ how}; the term had become {txt}", none)

/-- A typing derivation's steps, premises first: one per rule used. -/
partial def typingSteps : Lam.Deriv → Array Step
  | .node rule _ t T ps =>
    let before := (ps.foldl (fun acc p => acc ++ typingSteps p) #[])
    let tyOf : Lam.Deriv → Lam.Ty := fun | .node _ _ _ U _ => U
    let expl := match rule, t, T, ps with
      | "var", .var x, _, _ => s!"Var: {lamTex (.var x)} has type {lamTex T.toExpr} in the context."
      | "abs", .lam x _ _, .arrow A B, _ =>
        s!"→I (abstraction): with ${(Expr.var x).toLatex false} : {A.toExpr.toLatex false}$ added to the context the body has type {lamTex B.toExpr}, so the function has type {lamTex T.toExpr}."
      | "app", _, _, [f, a] =>
        s!"→E (application): the function has type {lamTex (tyOf f).toExpr} and the argument type {lamTex (tyOf a).toExpr}, which is the function's argument type, so the application has type {lamTex T.toExpr}."
      | _, _, _, _ => rule
    before.push ⟨"stlc." ++ rule, expl, [], t.toExpr, T.toExpr, none⟩

/-- The type-variable equations, in LaTeX. -/
private def eqsTex (eqs : List (Lam.Ty × Lam.Ty)) : String :=
  "; ".intercalate (eqs.map fun (a, b) => lamTex (.fn "=" [a.toExpr, b.toExpr]))

/-- Run a λ-command. -/
def lambdaCommand (s : Session) (cmd : Lam.Cmd) : Except LamErr LamResult := do
  let mk (value : Expr) (term : Option Lam.Term) (input : Expr) (steps : Array Step) (reading : Option String)
      (tree : Option Lam.Deriv := none) : LamResult :=
    let d : Derivation := ⟨input, steps, value⟩
    ⟨none, value, term, d, lambdaDbSteps d, reading, tree, some cmd, none⟩
  match cmd with
  | .reduce st limit t =>
    let t := t.erase
    let goal := match st with
      | .normal | .applicative => "normal form" | .cbn => "weak head normal form" | .cbv => "value"
    let (_, out, steps, halt, count) := lamRun s t st false limit
    if halt == .size || (halt == .fuel && limit.isNone) then
      throw (haltError halt goal s!" ({st.name})" count out)
    let reading :=
      if halt != .done then some s!"stopped after {limit.getD 0} steps: not yet a {goal}"
      else match churchReading out with
        | some r => some r
        | none =>
          if (Lam.betaStep out).isSome then
            some (if st == .cbv then "a value: the redexes left are under a λ, where call by value does not look"
              else "a weak head normal form: the redexes left are where call by name does not look")
          else none
    pure (mk (Lam.toExpr out) (some out) (Lam.toExpr t) steps reading)
  | .eta limit t =>
    let t := t.erase
    let (_, out, steps, halt, count) := lamRun s t .normal true limit
    if halt == .size || (halt == .fuel && limit.isNone) then
      throw (haltError halt "βη-normal form" " (β and η)" count out)
    let reading := if halt != .done then some s!"stopped after {limit.getD 0} steps: not yet in βη-normal form" else churchReading out
    pure (mk (Lam.toExpr out) (some out) (Lam.toExpr t) steps reading)
  | .fv t =>
    let t := t.erase
    let fv := Lam.freeVars t
    let value := Expr.fn "set" (fv.map Expr.var)
    let bound := Lam.boundVars t
    let reading := (if fv.isEmpty then "closed: no free variables" else s!"{fv.length} free") ++
      (if bound.isEmpty then "" else "; bound: " ++ ", ".intercalate bound)
    pure (mk value none (Lam.toExpr t)
      #[⟨"lambda.fv", "The free variables: $FV(x) = \\{x\\}$, $FV(\\lambda x.\\, M) = FV(M) \\setminus \\{x\\}$, $FV(M\\ N) = FV(M) \\cup FV(N)$. A variable is bound where a λ above it has its name.", [], Lam.toExpr t, value, none⟩]
      (some reading))
  | .db t =>
    let t := t.erase
    let value := Lam.dbToExpr (Lam.toDB [] t)
    pure (mk value none (Lam.toExpr t)
      #[⟨"lambda.db", "De Bruijn indices: each bound variable becomes the number of λs between it and its own binder (0 for the nearest); a free variable keeps its name.", [], Lam.toExpr t, value, none⟩]
      none)
  | .alpha a b =>
    let a := a.erase
    let b := b.erase
    let da := Lam.dbToExpr (Lam.toDB [] a)
    let db := Lam.dbToExpr (Lam.toDB [] b)
    let same := Lam.toDB [] a == Lam.toDB [] b
    let value := if same then Expr.fn "⊤" [] else Expr.fn "⊥" []
    let steps : Array Step := #[
      ⟨"lambda.db", "The first term in de Bruijn indices: the bound names are gone.", [], Lam.toExpr a, da, none⟩,
      ⟨"lambda.db", "The second term in de Bruijn indices.", [], Lam.toExpr b, db, none⟩,
      ⟨"lambda.alpha-eq", if same then "The de Bruijn forms are the same, so the terms differ at most in the names of bound variables: they are α-equivalent."
          else "The de Bruijn forms differ, so no renaming of bound variables turns one term into the other: they are not α-equivalent.",
        [], .fn (if same then "=" else "≠") [da, db], value, none⟩]
    pure (mk value none (.fn "pair" [Lam.toExpr a, Lam.toExpr b]) steps
      (some (if same then "α-equivalent: the same term up to the names of bound variables" else "not α-equivalent")))
  | .subst e x arg =>
    let e := e.erase
    let arg := arg.erase
    let clash := (Lam.freeVars arg).filter (· != x)
    let e' := Lam.renameFor x arg e
    let out := Lam.substRaw x arg e'
    let α : Array Step := if e' != e then
        #[⟨"lambda.alpha", s!"α: rename the binders that would capture a free variable of the term put in ({", ".intercalate clash}): those over a free {lamTex (.var x)}.", [], Lam.toExpr e, Lam.toExpr e', none⟩]
      else #[]
    let steps := α.push ⟨"lambda.subst", s!"Substitute: every free {lamTex (.var x)} becomes {lamTex (Lam.toExpr arg)}; under a binder named {lamTex (.var x)} the occurrences are bound, and stay.", [], Lam.toExpr e', Lam.toExpr out, none⟩
    pure (mk (Lam.toExpr out) (some out) (Lam.toExpr e) steps none)
  | .type Γ t =>
    match Lam.check Γ t with
    | .error m => throw ("eval", m, none)
    | .ok (d, T) => pure { mk T.toExpr none t.toExpr (typingSteps d) none (some d) with ty := some T }
  | .infer Γ t =>
    let defs := (lambdaDefs s).filter fun (n, _) => !Γ.any (·.1 == n)
    let t' := t.expandDefs defs
    let δ : Array Step := if t' != t then
        #[⟨"lambda.delta", "δ: unfold the definitions used (the session's, then the Church library's).", [], t.toExpr, t'.toExpr, none⟩]
      else #[]
    match Lam.infer Γ t' with
    | .error m => throw ("eval", m, none)
    | .ok r =>
      let eqText := if r.eqs.isEmpty then "there are no applications, so no equations to solve."
        else s!"each application $f\\ a$ needs $f$'s type to be an arrow from $a$'s type to the result's: {eqsTex r.eqs}."
      let gen : Step := ⟨"stlc.constraints", s!"Give each binder without a type, each application's result and each free variable a type variable. The term has type {lamTex r.initial.toExpr} when the equations hold: {eqText}", [], r.generated.toExpr, r.initial.toExpr, none⟩
      let (moves, σ) := r.moves.foldl (fun (acc, σ) (m, σ') =>
          let before := (r.initial.apply σ).toExpr
          let after := (r.initial.apply σ').toExpr
          let step : Step := match m with
            | .split a b => ⟨"stlc.split", s!"Both sides of {lamTex (.fn "=" [a.toExpr, b.toExpr])} are arrows: their arguments must be equal, and so must their results.", [], before, after, none⟩
            | .bind n u => ⟨"stlc.unify", s!"Solve {lamTex (.fn "=" [(Lam.Ty.tvar n).toExpr, u.toExpr])}: put {lamTex u.toExpr} for {lamTex (Lam.Ty.tvar n).toExpr} everywhere.", [], before, after, none⟩
          (acc.push step, σ')) (#[], ([] : Lam.TSubst))
      let fin : Step := ⟨"stlc.principal", "Every equation is solved. The variables left are named α, β, … : any type for them gives a type of the term. Checked: the term, annotated with this type, passes the type checker (the tree).", [], (r.initial.apply σ).toExpr, r.type.toExpr, none⟩
      let reading := if r.frees.isEmpty then none
        else some ("with " ++ ", ".intercalate (r.frees.map fun (x, A) => s!"{x} : {A.text}"))
      pure { mk r.type.toExpr none t.toExpr ((δ.push gen) ++ moves |>.push fin) reading (some r.deriv) with ty := some r.type }

/-- Evaluate a λ-cell: a command, or a term — unfold definitions (one δ-step), then reduce in
normal order, one β-step at a time, every step recorded with its de Bruijn view. A term without a
normal form after `Lam.maxSteps` steps, or grown past `Lam.maxSize` symbols, is refused — the one
budget in the engine, since the question is undecidable — but a definition is bound unreduced. -/
def lambdaCell (s : Session) (cellId source : String) : Session × Except LamErr LamResult :=
  let record (s : Session) (res : LamResult) :=
    { s with cells := (cellId, ⟨res.value, res.derivation, true⟩) :: s.cells.filter (·.1 != cellId) }
  match Lam.parseCmd source with
  | some (.error msg) => (s, .error ("syntax", msg, none))
  | some (.ok cmd) =>
    match lambdaCommand s cmd with
    | .error e => (s, .error e)
    | .ok res => (record s res, .ok res)
  | none =>
  match Lam.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (name, t) =>
    let (expanded, out, steps, halt, βs) := lamRun s t .normal false none
    if halt != .done && name.isNone then (s, .error (haltError halt "normal form" "" βs out)) else
      -- a definition with no normal form (`fact := Y F`) is bound as written, its names unfolded
      let (out, steps, reading) := if halt == .done then (out, steps, churchReading out)
        else (expanded, steps.filter (·.rule == "lambda.delta"),
          some s!"no normal form within {βs} β-steps{if halt == .size then s!" (the term grew past {Lam.maxSize} symbols)" else ""}, so it is bound unreduced")
      let d : Derivation := ⟨Lam.toExpr t, steps, Lam.toExpr out⟩
      let res : LamResult := ⟨name, Lam.toExpr out, some out, d, lambdaDbSteps d, reading, none, none, none⟩
      let s := record s res
      let s := match name with
        | some n => { s with lambdas := (n, out) :: s.lambdas.filter (·.1 != n) }
        | none => s
      (s, .ok res)

/-- What an order-world cell produced: a value (encoded), the derivation, and the poset to draw. -/
structure OrdResult where
  name : Option String
  value : Expr
  derivation : Derivation
  poset : Option Ord.Poset
  summary : String
  /-- A relation to draw as a directed graph: its elements and pairs, the pairs that show a property
  failing, and the pairs a closure added. -/
  graph : Option (Ord.Rel × List (String × String) × List (String × String)) := none
  /-- An operation to draw as its table, and the cells that show a law failing. -/
  table : Option (Ord.Op × List (String × String)) := none
  /-- A formal context to draw as its cross table. -/
  context : Option Ord.Ctx := none

/-- An element's name in LaTeX: a word upright, a set's braces escaped. -/
def nm (x : String) : String :=
  let esc := (x.replace "{" "\\{").replace "}" "\\}"
  if x.length > 1 && (x.toList.all fun c => c.isAlpha || c == '_') then "\\mathrm{" ++ esc ++ "}" else esc

/-- An explanation's LaTeX as plain text, for an error message: `$`, `\\mathrm{…}` and the escapes dropped. -/
def deTeX (t : String) : String :=
  let t := t.replace "$" "" |>.replace "\\cdot" "·" |>.replace "\\{" "{" |>.replace "\\}" "}"
  -- `\\mathrm{word}` → `word`
  let parts := t.splitOn "\\mathrm{"
  parts.headD "" ++ String.join (parts.tail.map fun p => match p.splitOn "}" with | w :: rest => w ++ "}".intercalate rest | [] => "")

/-- The first failure of a law of an operation: its explanation, and the cells of the table to mark. -/
def opLawFailure (o : Ord.Op) : String → Option (String × List (String × String))
  | "associative" => (Ord.assocFailure o).map fun (x, y, z) =>
      let xy := o.ap x y
      let yz := o.ap y z
      (s!"$({nm x} \\cdot {nm y}) \\cdot {nm z} = {nm xy} \\cdot {nm z} = {nm (o.ap xy z)}$, but ${nm x} \\cdot ({nm y} \\cdot {nm z}) = {nm x} \\cdot {nm yz} = {nm (o.ap x yz)}$",
        [(x, y), (xy, z), (y, z), (x, yz)])
  | "commutative" => (Ord.commFailure o).map fun (x, y) =>
      (s!"${nm x} \\cdot {nm y} = {nm (o.ap x y)}$, but ${nm y} \\cdot {nm x} = {nm (o.ap y x)}$", [(x, y), (y, x)])
  | _ => (Ord.idemFailure o).map fun x => (s!"${nm x} \\cdot {nm x} = {nm (o.ap x x)}$, not ${nm x}$", [(x, x)])

/-- Evaluate an order-world cell. -/
def orderCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
  match Ord.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (name, head, args) =>
    let least := head != "gfp"
    let head := if head == "sup" then "join" else if head == "inf" then "meet" else if head == "gfp" then "lfp" else head
    let braces (xs : List String) : String := "{" ++ ", ".intercalate xs ++ "}"
    let err (msg : String) : Session × Except (String × String × Option (Nat × Nat)) OrdResult := (s, .error ("eval", msg, none))
    let getP (a : Ord.Arg) : Except String Ord.Poset := match a with
      | .elem n => match s.posets.lookup n with | some P => .ok P | none => .error s!"'{n}' is not a poset"
      | _ => .error "expected the name of a poset"
    let getR (a : Ord.Arg) : Except String Ord.Rel := match a with
      | .elem n => match s.rels.lookup n, s.posets.lookup n with
        | some R, _ => .ok R
        | none, some P => .ok (Ord.Rel.of P.elems P.le)
        | none, none => .error s!"'{n}' is not a relation"
      | _ => .error "expected the name of a relation"
    let relExpr' := Ord.relExpr
    let getF (a : Ord.Arg) : Except String Ord.PMap := match a with
      | .elem n => match s.pmaps.lookup n with | some f => .ok f | none => .error s!"'{n}' is not a map"
      | _ => .error "expected the name of a map"
    -- an element of `P`, written as a name or, for a subsets poset, as a set literal
    -- an element as typed: a name, a pair `(x, y)`, or a set `{a,b}` (a powerset's), matched whatever
    -- the spacing and the order of a set's members
    let getE (P : Ord.Poset) (a : Ord.Arg) : Except String String := match a with
      | .elem x => match Ord.findElem P.elems x with | some e => .ok e | none => .error s!"'{x}' is not an element of the poset"
      | .set xs =>
        let typed := "{" ++ ",".intercalate xs ++ "}"
        match Ord.findElem P.elems typed with
        | some e => .ok e
        | none => .error (typed ++ " is not an element of the poset")
      | _ => .error "expected an element"
    let getO (a : Ord.Arg) : Except String Ord.Op := match a with
      | .elem n => match s.ops.lookup n with | some o => .ok o | none => .error s!"'{n}' is not an operation (make one with op or joinop)"
      | _ => .error "expected the name of an operation"
    let getC (a : Ord.Arg) : Except String Ord.Ctx := match a with
      | .elem n => match s.ctxs.lookup n with | some c => .ok c | none => .error s!"'{n}' is not a context"
      | _ => .error "expected the name of a context"
    let getS (P : Ord.Poset) (a : Ord.Arg) : Except String (List String) := match a with
      | .set xs => xs.mapM fun x => getE P (.elem x)
      | .elem x => (getE P (.elem x)).map ([·])
      | _ => .error "expected a set of elements"
    let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
    let done (value : Expr) (steps : Array Step) (P : Option Ord.Poset) (summary : String) (bindP : Option Ord.Poset := none) (bindF : Option Ord.PMap := none)
        (bindR : Option Ord.Rel := none) (graph : Option (Ord.Rel × List (String × String) × List (String × String)) := none)
        (bindO : Option Ord.Op := none) (bindC : Option Ord.Ctx := none) (table : Option (Ord.Op × List (String × String)) := none)
        (context : Option Ord.Ctx := none) :
        Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
      -- the derivation starts where the first step does, so the echo shows the question, not the answer
      let input := match steps[0]? with | some st => st.before | none => value
      let d : Derivation := ⟨input, steps, value⟩
      let s := { s with cells := (cellId, { output := value, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match name, bindP with
        | some n, some P => { s with posets := (n, P) :: s.posets.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindF with
        | some n, some f => { s with pmaps := (n, f) :: s.pmaps.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindR with
        | some n, some R => { s with rels := (n, R) :: s.rels.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindO with
        | some n, some o => { s with ops := (n, o) :: s.ops.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindC with
        | some n, some c => { s with ctxs := (n, c) :: s.ctxs.filter (·.1 != n) }
        | _, _ => s
      (s, .ok ⟨name, value, d, P, summary, graph, table, context⟩)
    let withPoset (P : Ord.Poset) (steps : Array Step) (what : String) :=
      done (Ord.posetExpr P) steps (some P) what (bindP := some P)
    let bool (b : Bool) : Expr := .var (if b then "true" else "false")
    match head, args with
    | "poset", [.set xs, .rels ps] | "poset", [.set xs, .rels ps, _] =>
      match Ord.mk xs ps with
      | .error msg => err msg
      | .ok P => withPoset P #[step "order.closure" "The order is the reflexive-transitive closure of the relation given; reflexivity, antisymmetry and transitivity were checked." (Ord.setExpr xs) (Ord.posetExpr P)] s!"a poset with {P.elems.length} elements"
    | "poset", [.set xs] =>
      match Ord.mk xs [] with
      | .error msg => err msg
      | .ok P => withPoset P #[] "an antichain"
    | "divisors", [.elem n] =>
      match n.toNat? with
      | none => err "divisors takes a number"
      | some n => match Ord.divisors n with
        | .error msg => err msg
        | .ok P => withPoset P #[step "order.divisors" s!"The divisors of {n} ordered by divisibility: $a \\le b$ iff $a \\mid b$." (.num (Q.ofInt n)) (Ord.posetExpr P)] s!"the divisors of {n} under divisibility"
    | "subsets", [.set xs] =>
      let P := Ord.subsets xs
      withPoset P #[step "order.subsets" "All subsets ordered by inclusion." (Ord.setExpr xs) (Ord.posetExpr P)] s!"the {P.elems.length} subsets of a {xs.eraseDups.length}-element set under inclusion"
    | "chain", [.elem n] =>
      match n.toNat? with
      | none => err "chain takes a number"
      | some n => withPoset (Ord.chain n) #[] s!"the chain of {n} elements"
    | "map", [.elem pn, .maps ps] =>
      match getP (.elem pn) with
      | .error msg => err msg
      | .ok P =>
        match ps.find? fun (a, b) => (Ord.findElem P.elems a).isNone || (Ord.findElem P.elems b).isNone with
        | some (a, b) => err s!"{a} -> {b} mentions an element outside the poset"
        | none =>
          let ps := ps.map fun (a, b) => ((Ord.findElem P.elems a).getD a, (Ord.findElem P.elems b).getD b)
          let f : Ord.PMap := ⟨ps⟩
          let value := Ord.setExpr (ps.map fun (a, b) => s!"{a}↦{b}")
          done value #[] none s!"a map on {pn} ({ps.length} explicit value{if ps.length == 1 then "" else "s"}; other elements are fixed)" (bindF := some f)
    | "hasse", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P =>
        let cov := Ord.hasse P
        withPoset P #[step "order.covers" "The Hasse diagram draws exactly the covers: $x \\lessdot y$ iff $x < y$ with nothing strictly between (order.covers_spec)." (Ord.setExpr P.elems) (.fn "hasse" (cov.map fun (a, b) => .fn "covers" [Ord.elemExpr a, Ord.elemExpr b]))] s!"{cov.length} covers"
    | "join", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          let ubs := Ord.upperBounds P [x, y]
          let s1 := step "order.upper-bounds" s!"The upper bounds of ${x}$ and ${y}$: every element above both." (Ord.setExpr [x, y]) (Ord.setExpr ubs)
          match Ord.sup P [x, y] with
          | some j => done (Ord.elemExpr j) #[s1, step "order.least" "The least of them is below every other upper bound (order.sup_spec): the join." (Ord.setExpr ubs) (Ord.elemExpr j)] none s!"{x} ∨ {y} = {j}"
          | none => err (s!"{x} and {y} have no join: the upper bounds " ++ braces ubs ++ " have no least element")
        | .error m, _ | _, .error m => err m
    | "meet", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          let lbs := Ord.lowerBounds P [x, y]
          let s1 := step "order.lower-bounds" s!"The lower bounds of ${x}$ and ${y}$: every element below both." (Ord.setExpr [x, y]) (Ord.setExpr lbs)
          match Ord.inf P [x, y] with
          | some m => done (Ord.elemExpr m) #[s1, step "order.greatest" "The greatest of them is above every other lower bound: the meet." (Ord.setExpr lbs) (Ord.elemExpr m)] none s!"{x} ∧ {y} = {m}"
          | none => err (s!"{x} and {y} have no meet: the lower bounds " ++ braces lbs ++ " have no greatest element")
        | .error m, _ | _, .error m => err m
    | "upper", [p, xs] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getS P xs with
        | .ok ys => done (Ord.setExpr (Ord.upperBounds P ys)) #[] none "upper bounds"
        | .error m => err m
    | "lower", [p, xs] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getS P xs with
        | .ok ys => done (Ord.setExpr (Ord.lowerBounds P ys)) #[] none "lower bounds"
        | .error m => err m
    | "lattice", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.latticeFailure P with
        | none => done (bool true) #[step "order.lattice" "Every pair has a join and a meet: a lattice." (Ord.setExpr P.elems) (bool true)] none "a lattice"
        | some (x, y, what) => done (bool false) #[step "order.lattice" s!"${x}$ and ${y}$ have no {what}: not a lattice." (Ord.setExpr [x, y]) (bool false)] none s!"not a lattice: {x}, {y} have no {what}"
    | "top", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.top P with
        | some t => done (Ord.elemExpr t) #[] none s!"⊤ = {t}"
        | none => err ("no top: the maximal elements are " ++ braces (Ord.maximal P))
    | "bottom", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.bottom P with
        | some b => done (Ord.elemExpr b) #[] none s!"⊥ = {b}"
        | none => err ("no bottom: the minimal elements are " ++ braces (Ord.minimal P))
    | "maximal", [p] => match getP p with | .error m => err m | .ok P => done (Ord.setExpr (Ord.maximal P)) #[] none "maximal elements"
    | "minimal", [p] => match getP p with | .error m => err m | .ok P => done (Ord.setExpr (Ord.minimal P)) #[] none "minimal elements"
    | "le", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          if P.rel x y then
            -- a chain of covers from x to y, found greedily (any path in the Hasse diagram is one)
            let rec path (fuel : Nat) (cur : String) (acc : List String) : List String :=
              match fuel with
              | 0 => acc.reverse
              | f + 1 => if cur == y then acc.reverse else
                match P.elems.find? fun z => Ord.covers P cur z && P.rel z y with
                | some z => path f z (z :: acc)
                | none => acc.reverse
            let chain := path P.elems.length x [x]
            let steps := (chain.zip chain.tail).toArray.map fun (u, v) =>
              step "order.cover" s!"${u} \\lessdot {v}$: a cover in the Hasse diagram; by transitivity ${x} \\le {v}$." (Ord.elemExpr u) (Ord.elemExpr v)
            done (bool true) steps none s!"{x} ≤ {y}"
          else done (bool false) #[step "order.incomparable" s!"${x} \\le {y}$ is not in the order (and there is no chain of covers from ${x}$ to ${y}$)." (Ord.elemExpr x) (bool false)] none s!"{x} ≰ {y}"
        | .error m, _ | _, .error m => err m
    | "monotone", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F => match Ord.monotoneFailure P F with
        | none => done (bool true) #[step "order.monotone" "For every $x \\le y$, $f(x) \\le f(y)$: monotone." (Ord.setExpr P.elems) (bool true)] none "monotone"
        | some (x, y) => done (bool false) #[step "order.monotone" s!"${x} \\le {y}$ but $f({x}) = {F.apply x} \\not\\le f({y}) = {F.apply y}$: not monotone." (Ord.setExpr [x, y]) (bool false)] none s!"not monotone at {x} ≤ {y}"
      | .error m, _ | _, .error m => err m
    | "lfp", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F =>
        match (if least then Ord.bottom P else Ord.top P), Ord.monotoneFailure P F with
        | none, _ => err s!"the poset has no {if least then "bottom" else "top"} to start from"
        | _, some (x, y) => err s!"f is not monotone ({x} ≤ {y} but f({x}) ≰ f({y})), so the iteration need not reach a fixed point"
        | some start, none =>
          let chain := Ord.iterate P F start
          let last := chain.getLastD start
          if F.apply last != last then err "the iteration did not stabilize (it should on a finite poset with a monotone map)" else
          let steps := (chain.zip chain.tail).toArray.map fun (u, v) =>
            step "order.iterate" s!"$f({u}) = {v}$; the chain from ${start}$ climbs, since $f$ is monotone." (Ord.elemExpr u) (Ord.elemExpr v)
          let steps := steps.push (step "order.fixed" (if least then s!"$f({last}) = {last}$: a fixed point, and below every fixed point (order.iter_le_fixed): the least." else s!"$f({last}) = {last}$: a fixed point, and above every fixed point: the greatest.") (Ord.elemExpr last) (Ord.elemExpr last))
          done (Ord.elemExpr last) steps none s!"{if least then "lfp" else "gfp"} = {last}"
      | .error m, _ | _, .error m => err m
    | "fixpoints", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F => done (Ord.setExpr (Ord.fixedPoints P F)) #[] none "fixed points"
      | .error m, _ | _, .error m => err m
    -- relations: a relation's own name, or a poset's (its order, as a relation)
    | "rel", (.set xs) :: rest =>
      let ps := match rest with | [.maps ps] => ps | _ => []
      match ps.find? fun (a, b) => !xs.contains a || !xs.contains b with
      | some (a, b) => err s!"{a} -> {b} mentions an element outside the set"
      | none =>
        let R := Ord.Rel.of xs ps
        done (Ord.relExpr R) #[] none s!"a relation on {R.elems.length} element{if R.elems.length == 1 then "" else "s"} with {R.pairs.length} pair{if R.pairs.length == 1 then "" else "s"}" (bindR := some R) (graph := some (R, [], []))
    | "kernel", [.set xs, .maps ps] =>
      let R := Ord.kernel xs ps
      done (Ord.relExpr R) #[step "rel.kernel" "Related when they have the same label: an equivalence relation (reflexive, symmetric and transitive, since equality of labels is)." (Ord.setExpr xs) (Ord.relExpr R)] none
        s!"same label: {R.classes.length} class{if R.classes.length == 1 then "" else "es"}" (bindR := some R) (graph := some (R, [], []))
    | "reflexive", [r] | "symmetric", [r] | "antisymmetric", [r] | "transitive", [r] | "equivalence", [r] | "preorder", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let props := match head with
          | "equivalence" => ["reflexive", "symmetric", "transitive"]
          | "preorder" => ["reflexive", "transitive"]
          | p => [p]
        -- the first property that fails, its witness as text and as the pairs to mark
        let fail (p : String) : Option (String × List (String × String)) := match p with
          | "reflexive" => (Ord.reflexiveFailure R).map fun x => (s!"${x} \\mathrel\{R} {x}$ fails", [(x, x)])
          | "symmetric" => (Ord.symmetricFailure R).map fun (x, y) => (s!"${x} \\mathrel\{R} {y}$ but not ${y} \\mathrel\{R} {x}$", [(x, y)])
          | "antisymmetric" => (Ord.antisymmetricFailure R).map fun (x, y) => (s!"${x} \\mathrel\{R} {y}$ and ${y} \\mathrel\{R} {x}$ with ${x} \\ne {y}$", [(x, y), (y, x)])
          | _ => (Ord.transitiveFailure R).map fun (x, y, z) => (s!"${x} \\mathrel\{R} {y}$ and ${y} \\mathrel\{R} {z}$ but not ${x} \\mathrel\{R} {z}$", [(x, y), (y, z)])
        match props.findSome? fun p => (fail p).map (p, ·) with
        | some (p, why, bad) =>
          done (bool false) #[step s!"rel.{p}" s!"Not {p}: {why}." (relExpr' R) (bool false)] none s!"not {p}" (graph := some (R, bad, []))
        | none =>
          done (bool true) #[step s!"rel.{props.getLast!}" s!"{", ".intercalate props |>.capitalize}: every {if props.length > 1 then "condition" else "case"} checked." (relExpr' R) (bool true)] none head (graph := some (R, [], []))
    | "closure", [r, .elem kind] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let reflAdd := Ord.reflClosureAdds R
        let symmAdd (R : Ord.Rel) := Ord.symmClosureAdds R
        let addPairs (R : Ord.Rel) (ps : List (String × String)) : Ord.Rel := ⟨R.elems, R.pairs ++ ps⟩
        let pairsText (ps : List (String × String)) := ", ".intercalate (ps.map fun (a, b) => s!"({a}, {b})")
        let trans (R : Ord.Rel) : Except String (Ord.Rel × Array Step) :=
          let (T, rounds, stable) := Ord.transClosure R
          if !stable then .error "the transitive closure did not settle (please report this)" else
          let (_, steps) := rounds.foldl (fun (cur, acc) add =>
            let nxt := addPairs cur add
            (nxt, acc.push (step "rel.transitive-closure" s!"Each pair forced by two that chain ($a \\mathrel\{R} b$ and $b \\mathrel\{R} c$ give $a \\mathrel\{R} c$): {pairsText add}." (relExpr' cur) (relExpr' nxt)))) (R, #[])
          .ok (T, steps)
        let finish (T : Ord.Rel) (steps : Array Step) := done (relExpr' T) steps none s!"{kind} closure: {T.pairs.length - R.pairs.length} pair{if T.pairs.length - R.pairs.length == 1 then "" else "s"} added" (bindR := some T)
          (graph := some (T, [], T.pairs.filter fun (a, b) => !R.has a b))
        match kind with
        | "reflexive" =>
          let T := addPairs R reflAdd
          finish T (if reflAdd.isEmpty then #[] else #[step "rel.reflexive-closure" s!"Each element related to itself: {pairsText reflAdd}." (relExpr' R) (relExpr' T)])
        | "symmetric" =>
          let add := symmAdd R
          let T := addPairs R add
          finish T (if add.isEmpty then #[] else #[step "rel.symmetric-closure" s!"Each pair turned round: {pairsText add}." (relExpr' R) (relExpr' T)])
        | "transitive" => match trans R with | .ok (T, st) => finish T st | .error m => err m
        | "equivalence" =>
          let R1 := addPairs R reflAdd
          let a2 := symmAdd R1
          let R2 := addPairs R1 a2
          match trans R2 with
          | .error m => err m
          | .ok (T, st) =>
            let s0 := if reflAdd.isEmpty then #[] else #[step "rel.reflexive-closure" s!"Each element related to itself: {pairsText reflAdd}." (relExpr' R) (relExpr' R1)]
            let s1 := if a2.isEmpty then #[] else #[step "rel.symmetric-closure" s!"Each pair turned round: {pairsText a2}." (relExpr' R1) (relExpr' R2)]
            finish T (s0 ++ s1 ++ st)
        | k => err s!"closure: {k} is not reflexive, symmetric, transitive or equivalence"
    | "classes", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        match (Ord.reflexiveFailure R).map (fun _ => "reflexive") <|> (Ord.symmetricFailure R).map (fun _ => "symmetric") <|> (Ord.transitiveFailure R).map (fun _ => "transitive") with
        | some p => err s!"classes are for equivalence relations, and this one is not {p} (closure(R, equivalence) makes it one)"
        | none =>
          let cs := R.classes
          done (Ord.partitionExpr cs) #[step "rel.classes" "Each element's class is everything related to it; for an equivalence relation the classes partition the set." (relExpr' R) (Ord.partitionExpr cs)] none s!"{cs.length} class{if cs.length == 1 then "" else "es"}" (graph := some (R, [], []))
    | "finer", [r, t] =>
      match getR r, getR t with
      | .ok R, .ok T =>
        match Ord.finerFailure R T with
        | none => done (bool true) #[step "rel.finer" "Every pair of the first is a pair of the second: finer (for equivalences, each class of the first lies inside a class of the second)." (relExpr' R) (bool true)] none "finer"
        | some (x, y) => done (bool false) #[step "rel.finer" s!"${x}$ and ${y}$ are related by the first but not by the second: not finer." (relExpr' R) (bool false)] none s!"not finer: ({x}, {y})" (graph := some (R, [(x, y)], []))
      | .error m, _ | _, .error m => err m
    | "wellfounded", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        match Ord.wellfounded R with
        | .error m => err m
        | .ok none => done (bool true) #[step "rel.wellfounded" "No cycle: on a finite set every chain of steps stops, so the relation is well-founded." (relExpr' R) (bool true)] none "well-founded" (graph := some (R, [], []))
        | .ok (some c) =>
          let edges := c.zip c.tail
          done (bool false) #[step "rel.wellfounded" s!"A cycle: {" → ".intercalate c}; following it never stops." (relExpr' R) (bool false)] none s!"not well-founded: {" → ".intercalate c}" (graph := some (R, edges, []))
    | "measure", [r, .maps ps] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let m (x : String) : Option Int := (ps.lookup x).bind fun v => (if v.startsWith "-" then (v.drop 1).toNat?.map (- ·) else v.toNat?.map Int.ofNat)
        match R.elems.find? fun x => (m x).isNone with
        | some x => err s!"measure: no number for {x}"
        | none =>
          match Ord.measureFailure R m with
          | none => done (bool true) #[step "rel.measure" "The measure goes down along every step, and a natural number cannot go down forever: well-founded." (relExpr' R) (bool true)] none "the measure decreases along every step"
          | some (x, y) => done (bool false) #[step "rel.measure" s!"The step ${x} \\to {y}$ does not decrease the measure ({(m x).getD 0} to {(m y).getD 0})." (relExpr' R) (bool false)] none s!"not decreasing at {x} → {y}" (graph := some (R, [(x, y)], []))
    -- happens-before: each process's events in order, and messages from send to receipt
    | "events", args | "clocks", args =>
      let procs := args.filterMap fun a => match a with | .set xs => some xs | _ => none
      let msgs := args.foldl (fun acc a => match a with | .maps ps => acc ++ ps | _ => acc) []
      let all := procs.flatten
      if procs.isEmpty then err s!"{head} takes each process's events in order, as sets, then the messages: {head}({"{"}a1, a2{"}"}, {"{"}b1{"}"}; a1->b1)" else
      if all.eraseDups.length != all.length then err "an event appears twice" else
      match msgs.find? fun (a, b) => !all.contains a || !all.contains b with
      | some (a, b) => err s!"{a} -> {b}: a message joins two events"
      | none =>
        match Ord.mk all (procs.flatMap (fun p => p.zip p.tail) ++ msgs) with
        | .error m => err s!"the messages make a cycle, so some event would happen before itself ({m})"
        | .ok P =>
          if head == "events" then
            withPoset P #[step "order.happens-before" "Happens-before: each process's events in order, each message's sending before its receipt, and everything that follows by transitivity." (Ord.setExpr all) (Ord.posetExpr P)]
              s!"{all.length} events on {procs.length} processes, {msgs.length} message{if msgs.length == 1 then "" else "s"}"
          else
            let tuple (ns : List Nat) := "(" ++ ", ".intercalate (ns.map toString) ++ ")"
            let entries := all.map fun e => s!"{e}↦{tuple (procs.map fun p => (p.filter fun x => P.rel x e).length)}"
            done (Ord.setExpr entries) #[step "order.clocks" "An event's vector clock counts, for each process, that process's events that happen before it or are it. One event happens before another exactly when its clock is below the other's in every entry." (Ord.setExpr all) (Ord.setExpr entries)] none
              s!"vector clocks of {all.length} events"
    | "concurrent", [p, a, b] =>
      match getP p with
      | .error m => err m
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          let c := !P.rel x y && !P.rel y x
          done (bool c) #[step "order.concurrent" (if c then s!"Neither ${nm x} \\le {nm y}$ nor ${nm y} \\le {nm x}$: concurrent." else s!"${nm (if P.rel x y then x else y)} \\le {nm (if P.rel x y then y else x)}$: one happens before the other.") (Ord.setExpr [x, y]) (bool c)] none (if c then "concurrent" else "ordered")
        | .error m, _ | _, .error m => err m
    -- finite algebra (Algebra.lean): operation tables and their laws
    | "op", [.set xs, .table rows] =>
      match Ord.Op.ofRows xs rows with
      | .error m => err m
      | .ok o => done (Ord.opExpr o) #[] none s!"an operation on {xs.length} elements" (bindO := some o) (table := some (o, []))
    | "joinop", [p] | "meetop", [p] =>
      match getP p with
      | .error m => err m
      | .ok P =>
        let which := if head == "joinop" then "join" else "meet"
        match (if head == "joinop" then Ord.joinOp P else Ord.meetOp P) with
        | some o => done (Ord.opExpr o) #[step "alg.from-order" s!"The {which} of each pair, read off the order, as a table." (Ord.setExpr P.elems) (Ord.opExpr o)] none s!"the {which} as an operation" (bindO := some o) (table := some (o, []))
        | none =>
          let pr := (Ord.allPairs P.elems).find? fun (x, y) => (if head == "joinop" then Ord.sup P [x, y] else Ord.inf P [x, y]).isNone
          err (match pr with | some (x, y) => s!"{x} and {y} have no {which}, so there is no table" | none => s!"some pair has no {which}")
    | "table", [j] =>
      match getO j with
      | .error m => err m
      | .ok o => done (Ord.opExpr o) #[] none s!"an operation on {o.elems.length} elements" (table := some (o, []))
    | "associative", [j] | "commutative", [j] | "idempotent", [j] | "semilattice", [j] =>
      match getO j with
      | .error m => err m
      | .ok o =>
        let laws := if head == "semilattice" then ["associative", "commutative", "idempotent"] else [head]
        match laws.findSome? fun l => (opLawFailure o l).map (l, ·) with
        | some (l, why, cells) =>
          done (bool false) #[step s!"alg.{l}" s!"Not {l}: {why}." (Ord.opExpr o) (bool false)] none s!"not {l}" (table := some (o, cells))
        | none =>
          let what := if head == "semilattice" then "Associative, commutative and idempotent: a semilattice" else s!"{head.capitalize}: every {if head == "associative" then "triple" else if head == "commutative" then "pair" else "element"} checked"
          done (bool true) #[step s!"alg.{laws.getLast!}" s!"{what}." (Ord.opExpr o) (bool true)] none (if head == "semilattice" then "a semilattice" else head) (table := some (o, []))
    | "identity", [j] =>
      match getO j with
      | .error m => err m
      | .ok o => match o.identity with
        | some e => done (Ord.elemExpr e) #[step "alg.identity" s!"${nm e} \\cdot x = x = x \\cdot {nm e}$ for every $x$: the identity." (Ord.opExpr o) (Ord.elemExpr e)] none s!"the identity is {e}" (table := some (o, o.elems.map (e, ·)))
        | none => err "no element is an identity: for each e, some x has e · x ≠ x or x · e ≠ x"
    | "fold", j :: rest =>
      match getO j with
      | .error m => err m
      | .ok o =>
        let elems : Except String (List String) := rest.mapM fun a => match a with
          | .elem x => match Ord.findElem o.elems x with | some e => Except.ok e | none => Except.error s!"'{x}' is not in the operation's set"
          | _ => Except.error "fold takes elements"
        match elems with
        | .error m => err m
        | .ok [] => match o.identity with
          | some e => done (Ord.elemExpr e) #[step "alg.fold" s!"Nothing to combine: the identity, ${nm e}$." (Ord.setExpr []) (Ord.elemExpr e)] none s!"= {e}"
          | none => err "fold of nothing needs an identity element, and this operation has none"
        | .ok (x :: xs) =>
          let (r, steps) := xs.foldl (fun (acc, st) y =>
            let v := o.ap acc y
            (v, st.push (step "alg.fold" s!"${nm acc} \\cdot {nm y} = {nm v}$." (Ord.elemExpr acc) (Ord.elemExpr v)))) (x, #[])
          done (Ord.elemExpr r) steps none s!"= {r}" (table := some (o, (xs.foldl (fun (acc, cs) y => (o.ap acc y, cs ++ [(acc, y)])) (x, [])).2))
    | "order", [j] =>
      match getO j with
      | .error m => err m
      | .ok o =>
        match ["associative", "commutative", "idempotent"].findSome? fun l => (opLawFailure o l).map (l, ·) with
        | some (l, why, _) => err s!"the order needs a semilattice, and this operation is not {l}: {deTeX why}"
        | none =>
          let P := o.order
          withPoset P #[step "alg.order" "$x \\le y$ when $x \\cdot y = y$: a partial order in which $x \\cdot y$ is the join (semilattice_order)." (Ord.opExpr o) (Ord.posetExpr P)] "the order of the semilattice"
    -- lattice properties
    | "distributive", [p] | "complemented", [p] | "boolean", [p] =>
      match getP p with
      | .error m => err m
      | .ok P =>
        match Ord.joinOp P, Ord.meetOp P with
        | some J, some M =>
          let distrib : Option (String × Array Step) := (Ord.distribFailure J M).map fun (x, y, z) =>
            let l := M.ap x (J.ap y z)
            let r := J.ap (M.ap x y) (M.ap x z)
            (s!"not distributive at {x}, {y}, {z}", #[step "order.distributive" s!"Not distributive: ${nm x} \\land ({nm y} \\lor {nm z}) = {nm x} \\land {nm (J.ap y z)} = {nm l}$, but $({nm x} \\land {nm y}) \\lor ({nm x} \\land {nm z}) = {nm (M.ap x y)} \\lor {nm (M.ap x z)} = {nm r}$." (Ord.setExpr [x, y, z]) (bool false)])
          let compl : Option (String × Array Step) := match Ord.top P, Ord.bottom P with
            | some t, some b => (P.elems.find? fun x => (Ord.complementsOf J M t b x).isEmpty).map fun x =>
                (s!"{x} has no complement", #[step "order.complement" s!"No complement: no $y$ has ${nm x} \\lor y = {nm t}$ and ${nm x} \\land y = {nm b}$." (Ord.elemExpr x) (bool false)])
            | _, _ => some ("no top or no bottom", #[step "order.complement" "Complements need a top and a bottom, and this lattice lacks one." (Ord.setExpr P.elems) (bool false)])
          let checks := match head with | "distributive" => [distrib] | "complemented" => [compl] | _ => [distrib, compl]
          match checks.findSome? id with
          | some (why, steps) => done (bool false) steps none why
          | none =>
            let what := match head with
              | "distributive" => "$x \\land (y \\lor z) = (x \\land y) \\lor (x \\land z)$ for every triple: distributive."
              | "complemented" => "Every element has a complement."
              | _ => "Distributive and complemented: a Boolean lattice (each complement is unique)."
            done (bool true) #[step s!"order.{if head == "boolean" then "boolean" else if head == "distributive" then "distributive" else "complement"}" what (Ord.setExpr P.elems) (bool true)] none (if head == "boolean" then "a Boolean lattice" else head)
        | _, _ => match Ord.latticeFailure P with
          | some (x, y, w) => err s!"not a lattice: {x} and {y} have no {w}"
          | none => err "not a lattice"
    | "complement", [p, a] =>
      match getP p with
      | .error m => err m
      | .ok P => match getE P a, Ord.joinOp P, Ord.meetOp P, Ord.top P, Ord.bottom P with
        | .error m, _, _, _, _ => err m
        | .ok x, some J, some M, some t, some b =>
          let cs := Ord.complementsOf J M t b x
          done (Ord.setExpr cs) #[step "order.complement" s!"The $y$ with ${nm x} \\lor y = {nm t}$ and ${nm x} \\land y = {nm b}$." (Ord.elemExpr x) (Ord.setExpr cs)] none
            (if cs.isEmpty then s!"{x} has no complement" else if cs.length == 1 then s!"one complement" else s!"{cs.length} complements")
        | _, _, _, _, _ => err "complements need a lattice with a top and a bottom"
    -- building and comparing orders
    | "product", [p, q] =>
      match getP p, getP q with
      | .ok P, .ok Q =>
        let R := Ord.product P Q
        withPoset R #[step "order.product" "Pairs, ordered componentwise: $(a, c) \\le (b, d)$ when $a \\le b$ and $c \\le d$." (.fn "pair" [Ord.setExpr P.elems, Ord.setExpr Q.elems]) (Ord.posetExpr R)]
          s!"a product of {P.elems.length} × {Q.elems.length} = {R.elems.length} elements"
      | .error m, _ | _, .error m => err m
    | "map", [.elem pn, .elem qn, .maps ps] =>
      match getP (.elem pn), getP (.elem qn) with
      | .ok P, .ok Q =>
        let resolved : Except String (List (String × String)) := ps.mapM fun (a, b) => match Ord.findElem P.elems a, Ord.findElem Q.elems b with
          | some a', some b' => Except.ok (a', b')
          | none, _ => Except.error s!"{a} is not in {pn}"
          | _, none => Except.error s!"{b} is not in {qn}"
        match resolved with
        | .error m => err m
        | .ok tbl =>
          match P.elems.find? fun x => (tbl.lookup x).isNone with
          | some x => err s!"{x} has no value: a map from {pn} to {qn} lists every element of {pn}"
          | none => done (Ord.setExpr (tbl.map fun (a, b) => s!"{a}↦{b}")) #[] none s!"a map from {pn} to {qn}" (bindF := some ⟨tbl⟩)
      | .error m, _ | _, .error m => err m
    | "monotone", [p, q, f] =>
      match getP p, getP q, getF f with
      | .ok P, .ok Q, .ok F => match Ord.monotoneFailure2 P Q F with
        | none => done (bool true) #[step "order.monotone" "For every $x \\le y$, $f(x) \\le f(y)$: monotone." (Ord.setExpr P.elems) (bool true)] none "monotone"
        | some (x, y) => done (bool false) #[step "order.monotone" s!"${nm x} \\le {nm y}$ but $f({nm x}) = {nm (F.apply x)} \\not\\le f({nm y}) = {nm (F.apply y)}$: not monotone." (Ord.setExpr [x, y]) (bool false)] none s!"not monotone at {x} ≤ {y}"
      | .error m, _, _ | _, .error m, _ | _, _, .error m => err m
    | "galois", [p, q, f, g] =>
      match getP p, getP q, getF f, getF g with
      | .ok P, .ok Q, .ok F, .ok G => match Ord.galoisFailure P Q F G with
        | none => done (bool true) #[step "order.galois" "$f(x) \\le y \\iff x \\le g(y)$ for every $x$ and $y$: a Galois connection." (Ord.setExpr P.elems) (bool true)] none "a Galois connection"
        | some (x, y) =>
          let fx := F.apply x
          let gy := G.apply y
          let l := if Q.rel fx y then "\\le" else "\\not\\le"
          let r := if P.rel x gy then "\\le" else "\\not\\le"
          done (bool false) #[step "order.galois" s!"Not a Galois connection: $f({nm x}) = {nm fx} {l} {nm y}$ but ${nm x} {r} g({nm y}) = {nm gy}$." (Ord.setExpr [x, y]) (bool false)] none s!"not a Galois connection at {x}, {y}"
      | .error m, _, _, _ | _, .error m, _, _ | _, _, .error m, _ | _, _, _, .error m => err m
    | "closureop", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F => match Ord.closureOpFailure P F with
        | none => done (bool true) #[step "order.closure-operator" "Extensive ($x \\le f(x)$), monotone and idempotent ($f(f(x)) = f(x)$): a closure operator." (Ord.setExpr P.elems) (bool true)] none "a closure operator"
        | some (kind, x, y) =>
          let why := match kind with
            | "extensive" => s!"${nm x} \\not\\le f({nm x}) = {nm (F.apply x)}$"
            | "monotone" => s!"${nm x} \\le {nm y}$ but $f({nm x}) = {nm (F.apply x)} \\not\\le f({nm y}) = {nm (F.apply y)}$"
            | _ => s!"$f({nm x}) = {nm (F.apply x)}$ but $f(f({nm x})) = {nm (F.apply (F.apply x))}$"
          done (bool false) #[step "order.closure-operator" s!"Not {kind}: {why}." (Ord.setExpr [x]) (bool false)] none s!"not a closure operator: not {kind}"
      | .error m, _ | _, .error m => err m
    -- formal concept analysis
    | "context", [.set objs, .set attrs, .maps inc] =>
      match inc.find? fun (o, a) => !objs.contains o || !attrs.contains a with
      | some (o, a) => err s!"{o} -> {a}: {if objs.contains o then s!"{a} is not an attribute" else s!"{o} is not an object"}"
      | none =>
        let C : Ord.Ctx := ⟨objs.eraseDups, attrs.eraseDups, inc.eraseDups⟩
        done (.fn "set" (C.inc.map Ord.pairExpr)) #[] none s!"a context: {C.objs.length} objects, {C.attrs.length} attributes" (bindC := some C) (context := some C)
    | "concepts", [c] =>
      match getC c with
      | .error m => err m
      | .ok C =>
        let P := C.lattice
        withPoset P #[step "order.concepts" s!"Each concept pairs a set of objects with a set of attributes: all the objects that have every one of the attributes, and all the attributes they share. Ordered by their objects: {P.elems.length} concepts, a complete lattice." (.fn "set" (C.inc.map Ord.pairExpr)) (Ord.posetExpr P)] s!"{P.elems.length} concepts"
    -- information flow
    | "secure", [p, r, .maps labels] =>
      match getP p, getR r with
      | .ok P, .ok R =>
        let resolved : Except String (List (String × String)) := labels.mapM fun (x, c) => match Ord.findElem P.elems c with
          | some c' => Except.ok (x, c')
          | none => Except.error s!"{c} is not a class of the lattice"
        match resolved with
        | .error m => err m
        | .ok lab =>
          match R.elems.find? fun x => (lab.lookup x).isNone with
          | some x => err s!"{x} has no class: label every variable"
          | none =>
            let L (x : String) : String := (lab.lookup x).getD x
            match Ord.flowFailure P L R with
            | none => done (bool true) #[step "order.flow" "Every flow goes from a class to one at least as high: no information flows down." (Ord.relExpr R) (bool true)] none "secure: every flow goes up" (graph := some (R, [], []))
            | some (x, y) => done (bool false) #[step "order.flow" s!"Not secure: {x} flows to {y}, but the class of {x}, ${nm (L x)}$, is not below the class of {y}, ${nm (L y)}$." (Ord.relExpr R) (bool false)] none s!"insecure: {x} → {y} flows down" (graph := some (R, [(x, y)], []))
      | .error m, _ | _, .error m => err m
    | h, _ => err s!"{h}: wrong arguments (see the reference)"

/-- What a logic cell produced: its value (a formula, a truth value, or an assignment written as a
conjunction of literals), its derivation, a one-line summary, and for `truthtable` the table. -/
structure LogicResult where
  name : Option String
  value : Expr
  derivation : Derivation
  summary : String
  /-- The variables, then one row per assignment: the variables' values and the formula's. -/
  table : Option (List String × List (List Bool)) := none

/-- A number from an expression of a logic cell: its bound variables (`env`) and the session's names
put in, then the pipeline. -/
def logicNum (s : Session) (env : List (String × Q)) (e : Expr) : Option Q :=
  let e := substitute s.env (substituteFns s.fns (substitute (env.map fun (x, q) => (x, .num q)) e))
  match (normalizeT pipelineRules pipelineOrdered e).run #[] with
  | (.ok (.num q), _) => some q
  | _ => none

/-- Evaluate a logic cell. -/
def logicCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) LogicResult :=
  match Logic.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok stmt =>
    let err (msg : String) : Session × Except (String × String × Option (Nat × Nat)) LogicResult := (s, .error ("eval", msg, none))
    let prep (f : Logic.Fm) : Logic.Fm := Logic.expand s.formulas f
    let tv (b : Bool) : Logic.Fm := if b then .tt else .ff
    let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
    let done (name : Option String) (input : Expr) (value : Logic.Fm) (steps : Array Step) (summary : String)
        (table : Option (List String × List (List Bool)) := none) :
        Session × Except (String × String × Option (Nat × Nat)) LogicResult :=
      let out := value.toExpr
      let d : Derivation := ⟨input, steps, out⟩
      let s := { s with cells := (cellId, { output := out, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match name with
        | some n => { s with formulas := (n, value) :: s.formulas.filter (·.1 != n) }
        | none => s
      (s, .ok ⟨name, out, d, summary, table⟩)
    -- a propositional formula with at most `limit` variables, for the truth-table commands
    let propOnly (f : Logic.Fm) (what : String) (limit := Logic.maxVars) : Except String (List String) :=
      if !f.isProp then .error s!"{what} is for propositional formulas; {f.toText} has arithmetic or quantifiers in it (write it on its own to evaluate it)"
      else if f.vars.length > limit then .error s!"{what}: {f.vars.length} variables, more than {limit}"
      else .ok f.vars
    let num := logicNum s
    match stmt with
    | .fm name f =>
      let f := prep f
      if f.isProp && !f.vars.isEmpty then
        done name f.toExpr f #[] s!"a formula in {", ".intercalate f.vars}"
      else if f.isProp then
        let b := f.eval (fun _ => false)
        done name f.toExpr (tv b) #[step "logic.evaluate" "A formula with no variables has one value, read off its connectives' truth tables." f.toExpr (tv b).toExpr] (if b then "true" else "false")
      else
        match Logic.decide num [] f, Logic.decidingElement num f with
        | .error m, _ | _, .error m => err m
        | .ok b, .ok el =>
          let why := match el, f with
            | some (x, v), .all _ _ body => s!"Not for every ${x}$: at ${x} = {v.toText}$, ${(Logic.instantiate x (.num v) body).toExpr.toLatex}$ is false."
            | some (x, v), .ex _ _ body => s!"A witness: at ${x} = {v.toText}$, ${(Logic.instantiate x (.num v) body).toExpr.toLatex}$ holds."
            | none, .all x _ _ => s!"Every ${x}$ of the domain was checked: the body holds for each."
            | none, .ex x _ _ => s!"Every ${x}$ of the domain was checked: the body holds for none."
            | _, _ => "Each atom evaluated, then the connectives."
          let summary := match el with
            | some (x, v) => s!"{if b then "true" else "false"} ({x} = {v.toText})"
            | none => if b then "true" else "false"
          done name f.toExpr (tv b) #[step "logic.bounded" why f.toExpr (tv b).toExpr] summary
    | .cmd name head args =>
      let args := args.map prep
      match head, args with
      | "truthtable", [f] =>
        match propOnly f "truthtable" 8 with
        | .error m => err m
        | .ok vs =>
          let rows := (Logic.rows vs).map fun r => r ++ [f.eval (Logic.assignment vs r)]
          let k := (rows.filter fun r => r.getLastD false).length
          done name (.fn "truthtable" [f.toExpr]) f #[] s!"true in {k} of {rows.length} rows" (some (vs, rows))
      | "taut", [f] =>
        match propOnly f "taut" with
        | .error m => err m
        | .ok vs =>
          match Logic.findRow vs (fun σ => !f.eval σ) with
          | none => done name (.fn "taut" [f.toExpr]) .tt #[step "logic.truthtable" s!"True in every one of the {(Logic.rows vs).length} rows of its truth table: a tautology." f.toExpr Logic.Fm.tt.toExpr] "a tautology"
          | some r => done name (.fn "taut" [f.toExpr]) .ff #[step "logic.truthtable" s!"False when {Logic.rowText vs r}: not a tautology." f.toExpr Logic.Fm.ff.toExpr] s!"false when {Logic.rowText vs r}"
      | "sat", [f] | "falsify", [f] =>
        match propOnly f head with
        | .error m => err m
        | .ok vs =>
          let want := head == "sat"
          match Logic.findRow vs (fun σ => f.eval σ == want) with
          | some r =>
            let lit := Logic.literals vs r
            done name (.fn head [f.toExpr]) lit #[step "logic.truthtable" s!"The first row of its truth table where it is {if want then "true" else "false"}: {Logic.rowText vs r}." f.toExpr lit.toExpr] s!"{if want then "satisfied" else "falsified"} by {Logic.rowText vs r}"
          | none => done name (.fn head [f.toExpr]) .ff #[step "logic.truthtable" s!"{if want then "False" else "True"} in every row: {if want then "unsatisfiable" else "a tautology"}, so no assignment does it (⊥: none)." f.toExpr Logic.Fm.ff.toExpr] (if want then "unsatisfiable" else "a tautology: nothing falsifies it")
      | "equiv", [f, g] =>
        match propOnly (.and f g) "equiv" with
        | .error m => err m
        | .ok vs =>
          match Logic.findRow vs (fun σ => f.eval σ != g.eval σ) with
          | none => done name (.fn "equiv" [f.toExpr, g.toExpr]) .tt #[step "logic.truthtable" s!"The same value in each of the {(Logic.rows vs).length} rows: equivalent." (.fn "equiv" [f.toExpr, g.toExpr]) Logic.Fm.tt.toExpr] "equivalent"
          | some r => done name (.fn "equiv" [f.toExpr, g.toExpr]) .ff #[step "logic.truthtable" s!"They differ when {Logic.rowText vs r}: the first is {f.eval (Logic.assignment vs r)}, the second {g.eval (Logic.assignment vs r)}." (.fn "equiv" [f.toExpr, g.toExpr]) Logic.Fm.ff.toExpr] s!"not equivalent: they differ when {Logic.rowText vs r}"
      | "nnf", [f] | "cnf", [f] | "dnf", [f] =>
        if !f.isProp then err s!"{head} is for propositional formulas; {f.toText} has arithmetic or quantifiers in it" else
        let (r, steps) := Logic.toNormal head f
        if !Logic.hasShape head r then err s!"{head}: the result {r.toText} is not in {head.toUpper} (please report this)" else
        done name f.toExpr r steps s!"{head.toUpper}: {steps.size} step{if steps.size == 1 then "" else "s"}"
      | h, _ => err s!"{h}: wrong arguments (see the reference)"

/-- What a systems cell produced: its value, derivation (a trace is a step per action), summary, and the
state graph to draw, with a counterexample's transitions marked or a witness's added. -/
structure SysResult where
  name : Option String
  value : Expr
  derivation : Derivation
  summary : String
  graph : Option (Ord.Rel × List (String × String) × List (String × String)) := none
  /-- Each drawn state's distance from an initial state, for a layered drawing. -/
  layers : List Nat := []
  /-- A replica simulation's space-time diagram, and the diagram's events each step made. -/
  spacetime : Option (Rep.Diagram × Array (List Nat)) := none

namespace Sys

def commands : List String := ["system", "states", "invariant", "inductive", "reach", "deadlock", "trace", "ctl", "eventually", "refines", "replicas",
  "rules", "rewrite", "terminates", "critical"]

/-- `[let NAME =] command(…)` for a systems command. -/
def splitLet (src : String) : Option String × String :=
  let t := src.trimAscii.copy
  if t.startsWith "let " then
    match (t.drop 4).copy.splitOn "=" with
    | n :: rest@(_ :: _) =>
      let name := n.trimAscii.copy
      if !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') then (some name, ("=".intercalate rest).trimAscii.copy) else (none, t)
    | _ => (none, t)
  else (none, t)

def headOf (t : String) : String := String.ofList (t.toList.takeWhile fun c => c.isAlphanum || c == '_')

def isSystemSource (src : String) : Bool :=
  let (_, t) := splitLet src
  let h := headOf t
  commands.contains h && ((t.drop h.length).trimAscii.copy.startsWith "(")

/-- The text between a command's outer brackets. -/
def argsOf (t : String) (h : String) : Except String String :=
  let rest := (t.drop h.length).trimAscii.copy
  if rest.startsWith "(" && rest.endsWith ")" then .ok ((rest.drop 1).dropEnd 1).copy
  else .error s!"{h}: write {h}(…)"

/-- Split at the first top-level `,` or `;`. -/
def splitFirst (s : String) : String × String :=
  let rec go : List Char → Nat → List Char → String × String
    | [], _, cur => (String.ofList cur.reverse, "")
    | c :: cs, d, cur =>
      if (c == ',' || c == ';') && d == 0 then (String.ofList cur.reverse, String.ofList cs)
      else if c == '(' || c == '{' || c == '[' then go cs (d + 1) (c :: cur)
      else if c == ')' || c == '}' || c == ']' then go cs (d - 1) (c :: cur)
      else go cs d (c :: cur)
  let (a, b) := go s.toList 0 []
  (a.trimAscii.copy, b.trimAscii.copy)

end Sys

/-- Evaluate a systems cell. -/
def systemCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) SysResult :=
  let (name, t) := Sys.splitLet source
  let head := Sys.headOf t
  let err (msg : String) : Session × Except (String × String × Option (Nat × Nat)) SysResult := (s, .error ("eval", msg, none))
  let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
  let bool (b : Bool) : Expr := .var (if b then "true" else "false")
  -- the question as the engine read it: the command with its system and formula
  let question : Expr :=
    if head == "system" || head == "rules" then .var head else
    if head == "replicas" then
      (match Sys.argsOf t head |>.toOption |>.bind (Rep.parse · |>.toOption) with
       | some (_, rs, _) => .fn "replicas" [.var ((Sys.splitFirst ((Sys.argsOf t head).toOption.getD "")).1), Ord.setExpr rs]
       | none => .var "replicas") else
    match Sys.argsOf t head with
    | .error _ => .var head
    | .ok body =>
      let (a, rest) := Sys.splitFirst body
      .fn head ([.var a] ++ (if rest.isEmpty then [] else [match Logic.parseFormula rest with | .ok f => f.toExpr | .error _ => .var rest]))
  let done (value : Expr) (steps : Array Step) (summary : String) (bindS : Option Sys.System := none)
      (graph : Option (Ord.Rel × List (String × String) × List (String × String) × List Nat) := none)
      (spacetime : Option (Rep.Diagram × Array (List Nat)) := none) (bindT : Option TRS.System := none) :
      Session × Except (String × String × Option (Nat × Nat)) SysResult :=
    let input := if head == "system" then value else question
    let d : Derivation := ⟨input, steps, value⟩
    let s := { s with cells := (cellId, { output := value, derivation := d }) :: s.cells.filter (·.1 != cellId) }
    let s := match name, bindS with
      | some n, some S => { s with systems := (n, S) :: s.systems.filter (·.1 != n) }
      | _, _ => s
    let s := match name, bindT with
      | some n, some T => { s with trss := (n, T) :: s.trss.filter (·.1 != n) }
      | _, _ => s
    (s, .ok ⟨name, value, d, summary, graph.map (fun (R, b, a, _) => (R, b, a)), (graph.map (·.2.2.2)).getD [], spacetime⟩)
  let getT (n : String) : Except String TRS.System :=
    match s.trss.lookup n.trimAscii.copy with
    | some T => .ok T
    | none => .error s!"'{n.trimAscii}' is not a rewriting system (make one with let R = rules(…))"
  let getS (n : String) : Except String Sys.System :=
    match s.systems.lookup n.trimAscii.copy with
    | some S => .ok S
    | none => .error s!"'{n.trimAscii}' is not a system (make one with let S = system(…))"
  let result : Except String (Session × Except (String × String × Option (Nat × Nat)) SysResult) := do
    let body ← Sys.argsOf t head
    -- the graph to draw: small enough to read, with transitions marked
    let draw (G : Sys.Graph) (bad added : List (Nat × Nat)) : Option (Ord.Rel × List (String × String) × List (String × String) × List Nat) :=
      if G.states.size > 40 then none else
      let lbl (i : Nat) := Sys.stateLabel G.states[i]!
      some (G.rel, bad.map (fun (i, j) => (lbl i, lbl j)), added.map (fun (i, j) => (lbl i, lbl j)), (List.range G.states.size).map fun i => (G.pathTo i).2.length)
    -- a trace from an initial state to state `j` as steps, each re-checked against the system
    let traceSteps (S : Sys.System) (G : Sys.Graph) (j : Nat) : Except String (Array Step × List (Nat × Nat)) := do
      let (start, path) := G.pathTo j
      let mut steps := #[step "sys.init" s!"Start: an initial state ({(S.init.toExpr).toText} holds)." (.var "init") (S.stateExpr G.states[start]!)]
      let mut cur := start
      let mut edges := []
      for (a, k) in path do
        let act := (S.actions.find? (·.name == a)).get!
        -- re-run the action: the step must be one the system takes
        let succ ← S.successors G.states[cur]!
        if !(succ.any fun (b, u) => b == a && u == G.states[k]!) then throw s!"internal: the trace's step {a} does not check"
        steps := steps.push (step "sys.step" s!"{act.describe}." (S.stateExpr G.states[cur]!) (S.stateExpr G.states[k]!))
        edges := edges ++ [(cur, k)]
        cur := k
      return (steps, edges)
    match head with
    | "system" =>
      let S ← Sys.parseSystem body
      let G ← S.explore
      let value := Expr.fn "system" [.fn "set" (S.vars.map (Expr.var ·.name)), .fn "set" (S.actions.map (Expr.var ·.name))]
      return done value #[] s!"{S.vars.length} variable{if S.vars.length == 1 then "" else "s"}, {S.actions.length} action{if S.actions.length == 1 then "" else "s"}, {G.states.size} reachable state{if G.states.size == 1 then "" else "s"}" (bindS := some S) (graph := draw G [] [])
    | "states" =>
      let S ← getS body
      let G ← S.explore
      return done (.num (Q.ofInt G.states.size)) #[step "sys.reach" s!"Breadth-first from the initial states: {G.states.size} reachable states, {G.edges.length} transitions." (.var "init") (.num (Q.ofInt G.states.size))]
        s!"{G.states.size} reachable states, {G.edges.length} transitions" (graph := draw G [] [])
    | "invariant" | "reach" =>
      let (sn, ftext) := Sys.splitFirst body
      let S ← getS sn
      let φ ← Logic.parseFormula ftext
      let G ← S.explore
      let target ← (List.range G.states.size).findM? fun i => do
        let h ← S.holds φ G.states[i]!
        return if head == "invariant" then !h else h
      match target with
      | some j =>
        let (steps, edges) ← traceSteps S G j
        if head == "invariant" then
          let steps := steps.push (step "sys.violated" s!"Here {(φ.toExpr).toText} fails: a shortest trace to a state that breaks it." (S.stateExpr G.states[j]!) (bool false))
          return done (bool false) steps s!"not invariant: fails after {edges.length} step{if edges.length == 1 then "" else "s"}" (graph := draw G edges [])
        else
          let steps := steps.push (step "sys.found" s!"Here {(φ.toExpr).toText} holds: a shortest trace to it." (S.stateExpr G.states[j]!) (bool true))
          return done (bool true) steps s!"reachable in {edges.length} step{if edges.length == 1 then "" else "s"}" (graph := draw G [] edges)
      | none =>
        if head == "invariant" then
          return done (bool true) #[step "sys.invariant" s!"{(φ.toExpr).toText} holds in every one of the {G.states.size} reachable states." (φ.toExpr) (bool true)] "invariant" (graph := draw G [] [])
        else
          return done (bool false) #[step "sys.unreachable" s!"None of the {G.states.size} reachable states satisfies {(φ.toExpr).toText}." (φ.toExpr) (bool false)] "unreachable" (graph := draw G [] [])
    | "inductive" =>
      let (sn, ftext) := Sys.splitFirst body
      let S ← getS sn
      let φ ← Logic.parseFormula ftext
      let inits ← S.initStates
      match ← inits.findM? fun x => do return !(← S.holds φ x) with
      | some x => return done (bool false) #[step "sys.cti" s!"Not even initially: an initial state where {(φ.toExpr).toText} fails." (.var "init") (S.stateExpr x)] "fails in an initial state"
      | none =>
        let all ← S.allStates
        let G ← S.explore
        let reachable := G.states.toList
        let mut cti : Option (Sys.State × String × Sys.State) := none
        let mut outside : Option (Sys.State × String) := none
        for x in all do
          if cti.isSome || outside.isSome then break
          if ← S.holds φ x then
            for (a, y) in ← S.successorsE x do
              match y with
              | .ok y => if cti.isNone && !(← S.holds φ y) then cti := some (x, a, y)
              | .error m => if outside.isNone then outside := some (x, m)
        if let some (x, m) := outside then
          return done (bool false) #[step "sys.cti" s!"A counterexample to induction: {(φ.toExpr).toText} holds here, and {m}. Add the variable's bounds to the formula." (φ.toExpr) (S.stateExpr x)]
            s!"not inductive: a step from a state where it holds leaves a domain"
        match cti with
        | none =>
          return done (bool true) #[step "sys.inductive" s!"{(φ.toExpr).toText} holds initially, and every action from a state where it holds (reachable or not: all {all.length} states checked) leads to one where it holds. So it is an invariant." (φ.toExpr) (bool true)] "inductive"
        | some (x, a, y) =>
          let note := if reachable.contains x then "This state is reachable, so the formula is not even an invariant." else "This state is not reachable: the formula may still be an invariant, but it is too weak to prove itself. Strengthen it."
          return done (bool false) #[step "sys.cti" s!"A counterexample to induction: {(φ.toExpr).toText} holds here…" (φ.toExpr) (S.stateExpr x),
            step "sys.cti" s!"{a}: …and fails after it. {note}" (S.stateExpr x) (S.stateExpr y)] s!"not inductive: {a} breaks it{if reachable.contains x then "" else " from an unreachable state"}"
    | "deadlock" =>
      let S ← getS body
      let G ← S.explore
      match (List.range G.states.size).find? fun i => !(G.edges.any fun (a, _, _) => a == i) with
      | some j =>
        let (steps, edges) ← traceSteps S G j
        return done (bool true) (steps.push (step "sys.deadlock" "No action is enabled here: a deadlock." (S.stateExpr G.states[j]!) (bool true))) s!"a deadlock after {edges.length} step{if edges.length == 1 then "" else "s"}" (graph := draw G edges [])
      | none => return done (bool false) #[step "sys.deadlock" s!"Every one of the {G.states.size} reachable states has an enabled action." (.var "init") (bool false)] "no deadlock" (graph := draw G [] [])
    | "rules" =>
      let R ← TRS.parseSystem body
      let value := Expr.fn "set" (R.rules.map TRS.Rule.toExpr)
      return done value #[] s!"{R.rules.length} rule{if R.rules.length == 1 then "" else "s"}: {", ".intercalate (R.rules.map (·.name))}" (bindT := some R)
    | "rewrite" =>
      let (rn, tt) := Sys.splitFirst body
      let R ← getT rn
      let t ← TRS.parseTerm tt
      let (trace, out, normal) := TRS.normalize R t
      if !normal then
        throw (if out.size > TRS.maxSize then s!"the term grew past {TRS.maxSize} symbols after {trace.length} rewrites (the system may not terminate on this term)"
          else s!"no normal form after {trace.length} rewrites (the system may not terminate on this term)")
      let (steps, _) := trace.foldl (fun (acc, prev) (ρ, p, t') =>
          (acc.push ⟨"trs.step", s!"{ρ.name}: ${ρ.lhs.toExpr.toLatex false} \\to {ρ.rhs.toExpr.toLatex false}$, {if p.isEmpty then "at the root" else "at the marked subterm"}.", p, prev.toExpr, t'.toExpr, none⟩, t'))
        (#[], t)
      return done out.toExpr steps s!"a normal form after {trace.length} step{if trace.length == 1 then "" else "s"}"
    | "terminates" =>
      let (rn, rest) := Sys.splitFirst body
      let R ← getT rn
      let interps ← (TRS.topCommas rest).mapM TRS.parseInterp
      let I := TRS.interpOf interps
      let what := if interps.isEmpty then "size" else "interpretation"
      let checks := R.rules.map fun ρ => (ρ, TRS.lin I ρ.lhs, TRS.lin I ρ.rhs)
      let steps := (checks.map fun (ρ, l, r) =>
        let ok := TRS.decreases l r
        step "trs.decrease" (s!"{ρ.name}: the left side's {what} is {l.text}, the right side's {r.text}: " ++
          (if ok then "larger, whatever the variables are." else "not larger for every value of the variables."))
          ρ.toExpr (bool ok)).toArray
      match checks.find? (fun (_, l, r) => !TRS.decreases l r) with
      | some (ρ, _, _) => return done (bool false) steps s!"not shown to terminate: {ρ.name} does not decrease the {what}"
      | none => return done (bool true) steps s!"terminates: every rule decreases the {what}, a natural number, so no term rewrites for ever"
    | "critical" =>
      let R ← getT body.trimAscii.copy
      let cps := TRS.critical R
      let results := cps.map fun c =>
        let (_, nl, okl) := TRS.normalize R c.left
        let (_, nr, okr) := TRS.normalize R c.right
        (c, nl, nr, okl && okr && nl == nr)
      let steps := (results.map fun (c, nl, nr, joined) =>
        step "trs.critical" (s!"{c.outer.name} at the root and {c.inner.name} at position {c.pos} overlap on this term. It rewrites to {c.left} and to {c.right}, which reduce to {nl} and {nr}: " ++
          (if joined then "joinable." else "not joinable."))
          c.peak.toExpr (.fn (if joined then "=" else "≠") [nl.toExpr, nr.toExpr])).toArray
      let value := Expr.fn "set" (cps.map fun c => .fn "pair" [c.left.toExpr, c.right.toExpr])
      let bad := (results.filter fun (_, _, _, j) => !j).length
      let say := if cps.isEmpty then "no critical pairs: locally confluent"
        else if bad == 0 then s!"{cps.length} critical pair{if cps.length == 1 then "" else "s"}, all joinable: locally confluent, and confluent if it terminates (Newman's lemma)"
        else s!"{cps.length} critical pair{if cps.length == 1 then "" else "s"}, {bad} not joinable: not confluent"
      return done value steps say
    | "replicas" =>
      let (kind, replicas, evs) ← Rep.parse body
      let r ← Rep.run kind replicas evs
      let (value, say, same) := Rep.summary r
      let steps := r.steps.map fun (rule, text, before, after, _) => step rule text before after
      let steps := steps.push (step (if same then "crdt.converged" else "crdt.diverged")
        (if same then "Every replica is in the same state, so every replica reads the same."
         else "The replicas are not all in the same state: some have not received every update yet.") value (bool same))
      let evOf := (r.steps.map (·.2.2.2.2)).push []
      return done value steps say (spacetime := some (r.diagram, evOf))
    | "trace" =>
      let (sn, rest) := Sys.splitFirst body
      let S ← getS sn
      let inits ← S.initStates
      let start ← match inits with | [x] => pure x | [] => throw "no initial state" | _ => throw "trace needs a single initial state"
      let names := (rest.splitOn ",").map (·.trimAscii.copy) |>.filter (· != "")
      let mut cur := start
      let mut steps := #[step "sys.init" s!"Start: the initial state ({(S.init.toExpr).toText})." (.var "init") (S.stateExpr start)]
      let mut visited : List Sys.State := [start]
      for a in names do
        let act ← match S.actions.find? (·.name == a) with | some x => pure x | none => throw s!"{a} is not an action of {sn}"
        match (← S.successors cur).find? (·.1 == a) with
        | none => throw s!"{a} is not enabled in {Sys.stateLabel cur} ({(act.guard.toExpr).toText} fails)"
        | some (_, nxt) =>
          steps := steps.push (step "sys.step" s!"{act.describe}." (S.stateExpr cur) (S.stateExpr nxt))
          visited := visited ++ [nxt]
          cur := nxt
      -- the trace on the graph of reachable states, its transitions marked
      let graph := match S.explore with
        | .ok G =>
          let idx (x : Sys.State) := (List.range G.states.size).find? fun i => G.states[i]! == x
          let edges := (visited.zip visited.tail).filterMap fun (a, b) => do pure (← idx a, ← idx b)
          draw G edges []
        | .error _ => none
      return done (S.stateExpr cur) steps s!"{names.length} step{if names.length == 1 then "" else "s"}" (graph := graph)
    | "ctl" =>
      let (sn, ftext) := Sys.splitFirst body
      let S ← getS sn
      let ftext := ftext.trimAscii.copy
      let op := String.ofList (ftext.toList.take 2)
      if !["EF", "AF", "EG", "AG", "EX", "AX"].contains op then throw "ctl takes EF, AF, EG, AG, EX or AX, then a formula: ctl(S, AG x ≤ 3)"
      let φ ← Logic.parseFormula (ftext.drop 2).copy
      let G ← S.explore
      let n := G.states.size
      let sat ← (List.range n).filterM fun i => S.holds φ G.states[i]!
      let live := (List.range n).filter fun i => G.edges.any fun (a, _, _) => a == i
      let preA (Z : List Nat) := (G.preA Z).filter live.contains
      let (chain, least) : List (List Nat) × Bool := match op with
        | "EX" => ([G.preE sat], true)
        | "AX" => ([preA sat], true)
        | "EF" => (Sys.iterateSets n (fun Z => sat ++ (G.preE Z).filter (!sat.contains ·)) [], true)
        | "AF" => (Sys.iterateSets n (fun Z => sat ++ (preA Z).filter (!sat.contains ·)) [], true)
        | "EG" => (Sys.iterateSets n (fun Z => sat.filter (G.preE Z).contains) (List.range n), false)
        | _ => (Sys.iterateSets n (fun Z => sat.filter (G.preA Z).contains) (List.range n), false)
      let final := chain.getLastD []
      -- the answer carries its certificate: the set and its ranks, checked (`CtlProofs.lean`)
      let es := G.edges.map fun (a, _, b) => (a, b)
      if !Sys.Ctl.check op n es sat chain final then throw s!"internal: the {op} set does not check"
      let what := match op with
        | "EF" => "states with a path to one where φ holds: the least Z with Z = φ ∪ EX Z"
        | "AF" => "states all of whose paths reach φ: the least Z with Z = φ ∪ AX Z (a state with no successor has no path onward)"
        | "EG" => "states with an infinite path along which φ always holds: the greatest Z with Z = φ ∩ EX Z"
        | "AG" => "states from which φ holds along every path: the greatest Z with Z = φ ∩ AX Z"
        | "EX" => "states with a successor where φ holds"
        | _ => "states that have successors, all of them where φ holds"
      let mut steps : Array Step := #[step "sys.ctl" s!"{op} {(φ.toExpr).toText}: the {what}. φ holds in {sat.length} of the {n} reachable states." (φ.toExpr) (Sys.stateSet G sat)]
      let mut k := 0
      for (a, b) in chain.zip chain.tail do
        k := k + 1
        steps := steps.push (step "sys.iterate" s!"Round {k}: {b.length} state{if b.length == 1 then "" else "s"}." (Sys.stateSet G a) (Sys.stateSet G b))
      if op != "EX" && op != "AX" then
        steps := steps.push (step "sys.fixed" s!"No change: the {if least then "least" else "greatest"} fixed point, reached from {if least then "∅" else "all states"} (Kleene)." (Sys.stateSet G final) (Sys.stateSet G final))
      let holds := G.inits.all final.contains
      steps := steps.push (step "sys.ctl" s!"{if holds then "Every initial state is in it" else "An initial state is not in it"}: {op} {(φ.toExpr).toText} {if holds then "holds" else "fails"}." (Sys.stateSet G final) (bool holds))
      return done (bool holds) steps s!"{op} holds in {final.length} of {n} states; {if holds then "true" else "false"} initially"
    | "eventually" =>
      let (sn, ftext) := Sys.splitFirst body
      let S ← getS sn
      let φ ← Logic.parseFormula ftext
      let G ← S.explore
      let n := G.states.size
      let bad ← (List.range n).filterM fun i => do return !(← S.holds φ G.states[i]!)
      -- the ¬φ part of the graph, and what can be reached inside it from an initial ¬φ state
      let inside := G.edges.filter fun (a, _, b) => bad.contains a && bad.contains b
      let reach (from_ : List Nat) (allowed : List Nat) : Std.HashMap Nat (Option (Nat × String)) := Id.run do
        let mut seen : Std.HashMap Nat (Option (Nat × String)) := {}
        let mut queue := from_.filter allowed.contains
        for x in queue do seen := seen.insert x none
        for _ in [0:n + 1] do
          match queue with
          | [] => break
          | x :: rest =>
            queue := rest
            for (a, l, b) in inside do
              if a == x && allowed.contains b && !seen.contains b then
                seen := seen.insert b (some (x, l))
                queue := queue ++ [b]
        return seen
      let fromInit := reach G.inits bad
      let pathIn (seen : Std.HashMap Nat (Option (Nat × String))) (j : Nat) : List (Nat × String × Nat) := Id.run do
        let mut cur := j
        let mut acc := []
        for _ in [0:n + 1] do
          match seen.getD cur none with
          | none => break
          | some (p, l) => acc := (p, l, cur) :: acc; cur := p
        return acc
      -- a deadlock reached without φ: the run stops short of φ
      let deadEnd := (List.range n).find? fun i => fromInit.contains i && !(G.edges.any fun (a, _, _) => a == i)
      -- otherwise a fair cycle: a strongly connected set of ¬φ states, each fair action taken in it or disabled somewhere in it
      let reachableBad := bad.filter fromInit.contains
      let scc (x : Nat) : List Nat := reachableBad.filter fun y => (reach [x] bad).contains y && (reach [y] bad).contains x
      let fairActs := S.actions.filter (·.fair)
      let mut found : Option (Nat × List Nat) := none
      for x in reachableBad do
        if found.isNone then
          let C := scc x
          let internal := inside.filter fun (a, _, b) => C.contains a && C.contains b
          if !internal.isEmpty then
            let ok ← fairActs.allM fun act => do
              if internal.any (fun (_, l, _) => l == act.name) then return true
              -- weakly fair: disabled somewhere on the cycle; strongly fair: disabled everywhere on it
              if act.strong then C.allM fun i => do return !(← S.holds act.guard G.states[i]!)
              else C.anyM fun i => do return !(← S.holds act.guard G.states[i]!)
            if ok then found := some (x, C)
      let fmt := fun (i : Nat) => S.stateExpr G.states[i]!
      let desc := fun (l : String) => ((S.actions.find? (·.name == l)).map (·.describe)).getD l
      match deadEnd, found with
      | some j, _ =>
        let path := pathIn fromInit j
        let start := (path.head?.map (·.1)).getD j
        let steps := #[step "sys.init" "Start: an initial state." (.var "init") (fmt start)] ++ (path.map fun (a, l, b) => step "sys.step" s!"{desc l}." (fmt a) (fmt b)).toArray
        return done (bool false) (steps.push (step "sys.deadlock" s!"No action is enabled, and {(φ.toExpr).toText} never held: the run stops without it." (fmt j) (bool false))) "never: a deadlock first" (graph := draw G (path.map fun (a, _, b) => (a, b)) [])
      | none, some (x, C) =>
        -- the lasso: a path to x, then a cycle through C covering every fair action's obligation
        let path := pathIn fromInit x
        let start := (path.head?.map (·.1)).getD x
        let mut targets : List Nat := []
        for act in fairActs do
          match (inside.filter fun (a, l, b) => C.contains a && C.contains b && l == act.name).head? with
          | some (a, _, _) => targets := targets ++ [a]
          | none =>
            if !act.strong then
              match ← C.findM? fun i => do return !(← S.holds act.guard G.states[i]!) with
              | some i => targets := targets ++ [i]
              | none => pure ()
        let mut cycle : List (Nat × String × Nat) := []
        let mut cur := x
        for tgt in targets ++ [x] do
          let seen := reach [cur] C
          cycle := cycle ++ pathIn seen tgt
          cur := tgt
        if cycle.isEmpty then
          -- a self-loop or a cycle through x
          match inside.find? fun (a, _, b) => a == x && C.contains b with
          | some (a, l, b) => cycle := [(a, l, b)] ++ pathIn (reach [b] C) x
          | none => pure ()
        -- after a fair action's edge, the path to x continues
        let steps := #[step "sys.init" "Start: an initial state." (.var "init") (fmt start)] ++
          (path.map fun (a, l, b) => step "sys.step" s!"{desc l}." (fmt a) (fmt b)).toArray ++
          (cycle.map fun (a, l, b) => step "sys.cycle" s!"{desc l} (on the cycle)." (fmt a) (fmt b)).toArray
        let steps := steps.push (step "sys.lasso" s!"The cycle repeats forever and {(φ.toExpr).toText} never holds; every weakly fair action is taken on it or disabled somewhere on it, and every strongly fair one taken or never enabled, so the run is fair." (fmt x) (bool false))
        return done (bool false) steps "never, on a fair run that loops" (graph := draw G ((path ++ cycle).map fun (a, _, b) => (a, b)) [])
      | none, none =>
        return done (bool true) #[step "sys.eventually" s!"Every fair run reaches {(φ.toExpr).toText}: no deadlock and no fair cycle avoids it." (φ.toExpr) (bool true)] "eventually, on every fair run" (graph := draw G [] [])
    | "refines" =>
      let (cn, rest) := Sys.splitFirst body
      let (an, maptext) := Sys.splitFirst rest
      let C ← getS cn
      let A ← getS an
      let mapping ← Sys.parseUpdates maptext
      for v in A.vars do
        if (mapping.lookup v.name).isNone then throw s!"the mapping gives no value for {an}'s variable {v.name}"
      let abs (x : Sys.State) : Except String Sys.State := A.vars.mapM fun v => do
        let val ← Sys.evalExpr (C.syms ++ A.syms) (C.env x) (mapping.lookup v.name).get!
        if !v.dom.contains val then throw s!"the mapping sends {Sys.stateLabel x} to {v.name} = {val}, outside its domain"
        return val
      let G ← C.explore
      for i in G.inits do
        let a ← abs G.states[i]!
        if !(← A.holds A.init a) then
          return done (bool false) #[step "sys.refines" s!"The initial state {Sys.stateLabel G.states[i]!} maps to {Sys.stateLabel a}, which is not initial in {an}." (C.stateExpr G.states[i]!) (A.stateExpr a)] "an initial state maps outside the abstract initial states"
      let mut bad : Option (Nat × String × Nat) := none
      for (i, l, j) in G.edges do
        if bad.isNone then
          let a ← abs G.states[i]!
          let b ← abs G.states[j]!
          if a != b && !((← A.successors a).any fun (_, u) => u == b) then bad := some (i, l, j)
      match bad with
      | none => return done (bool true) #[step "sys.refines" s!"Every step of {cn} ({G.edges.length} transitions) maps to a step of {an} or leaves the abstract state unchanged (a stutter)." (.var cn) (bool true)] "refines"
      | some (i, l, j) =>
        let (steps, edges) ← traceSteps C G i
        let a ← abs G.states[i]!
        let b ← abs G.states[j]!
        let steps := steps.push (step "sys.refines" s!"{l}: this step maps {Sys.stateLabel a} to {Sys.stateLabel b}, which is neither a step of {an} nor a stutter." (A.stateExpr a) (A.stateExpr b))
        return done (bool false) steps s!"does not refine: {l} has no abstract counterpart" (graph := draw G (edges ++ [(i, j)]) [])
    | h => throw s!"{h}: not a systems command"
  match result with
  | .ok r => r
  | .error m => err m

/-- A sampled plot: the variable, the range, and one series per function — its normalized term and
`(t, y)` pairs (`none` where it has no finite value). A `parametric` series is a complex-valued
curve: its pairs are `(re, im)`, drawn in the plane. -/
structure PlotSeries where
  term : Expr
  points : Array (Float × Option Float)
  parametric : Bool := false

structure Plot where
  var : String
  from_ : Float
  to : Float
  series : Array PlotSeries
  /-- `epicycles`/`dft` only: the rotating terms `(k, c_k)` as numbers, each with its exact term when
  there is one. -/
  terms : Array (Int × CF × Option Expr) := #[]

/-- The curves a plot argument names: a list `[f, g, …]` (which the parser reads as a one-row
matrix; a column is accepted too) is one curve per entry, a scalar is one curve, and a genuine
matrix is none. -/
def plotFns : Expr → Option (List Expr)
  | .matrix [row] => some row
  | .matrix rows => if rows.all (·.length == 1) then some (rows.filterMap List.head?) else none
  | e => some [e]

/-- A list of points for `dft`: complex numbers, or `[x, y]` pairs, in a row or a column. -/
def samplePoints (e : Expr) : Except String (Array CF) := do
  let entries ← match e with
    | .matrix [row] => pure row
    | .matrix rows =>
      if rows.all (·.length == 1) then pure (rows.filterMap List.head?)
      else if rows.all (·.length == 2) then pure (rows.map fun r => .add [r[0]!, .mul [r[1]!, iE]])
      else throw "dft: give the points as complex numbers [z₁, z₂, …] or as pairs [x₁, y₁; x₂, y₂; …]"
    | _ => throw "dft takes a list of points"
  let pts ← entries.mapM fun z => match evalNumericC [] z with
    | .ok v => pure v
    | .error m => throw s!"dft: {m}"
  pure pts.toArray

private def sampleReal (x : String) (lo hi : Float) (n : Nat) (g : Expr) : Array (Float × Option Float) :=
  (Array.range n).map fun i =>
    let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
    (t, (evalNumeric [(x, t)] g).toOption.filter fun v => v.isFinite)

private def sampleComplex (x : String) (lo hi : Float) (n : Nat) (g : Expr) : Array (Float × Option Float) :=
  (Array.range n).map fun i =>
    let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
    match (evalNumericC [(x, t)] g).toOption.filter CF.isFinite with
    | some z => (z.re, some z.im)
    | none => (0, none)

/-- `plot(f, x, from, to[, n])`, `plot([f, g, …], x, from, to[, n])`, `epicycles(f, t[, n])` and
`dft(points[, modes])`: simplify the function (or the list, entrywise) under the session — so
derivatives and session functions plot as what they are — record the cell like any other, and
sample. A curve that mentions `i` is complex-valued and is drawn in the plane (`parametric`).
`epicycles` reads the `(k, c_k)` off a finite Fourier sum and samples the curve over `[0, 2π]`;
`dft` computes the coefficients of sample points numerically, keeps the `modes` largest, and does
the same. Sampling and the DFT are presentation: the derivation shown is the term's. -/
def plotValue (s : Session) (cellId : String) (value : Expr) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Expr × Derivation × Plot) :=
    let bad := (s, .error ("eval", "plot takes a function, a variable, and the range: plot(f, x, from, to); epicycles(f, t); dft(points)", none))
    let num (e : Expr) : Option Float := (evalNumeric [] (substitute s.env (substituteFns s.fns e))).toOption
    -- normalize a term under the session, record the cell, and hand back the derivation
    let record (x : String) (f : Expr) : Session × Except String (Expr × Derivation) :=
      let input := substitute (s.env.filter (·.1 != x)) (substituteFns s.fns f)
      match (normalizeT pipelineRules pipelineOrdered input).run #[] with
      | (.error msg, _) => (s, .error msg)
      | (.ok output, steps) =>
        let d : Derivation := ⟨input, steps, output⟩
        ({ s with cells := (cellId, { output, derivation := d }) :: s.cells.filter (·.1 != cellId) }, .ok (output, d))
    let samples (rest : List Expr) (dflt : Nat) : Nat := match rest with
      | [.num k] => min 4000 (max 2 k.val.num.toNat)
      | _ => dflt
    match value with
    | .fn "plot" (f :: .var x :: a :: b :: rest) =>
      match num a, num b with
      | some lo, some hi =>
        let n := samples rest 300
        match record x f with
        | (s, .error msg) => (s, .error ("eval", msg, none))
        | (s, .ok (output, d)) =>
          match plotFns output with
          | none => (s, .error ("eval", "plot: give one function or a list [f, g, …], not a matrix", none))
          | some fns =>
            let series := fns.toArray.map fun g =>
              if mentionsI g then ⟨g, sampleComplex x lo hi n g, true⟩ else ⟨g, sampleReal x lo hi n g, false⟩
            (s, .ok (f, output, d, ⟨x, lo, hi, series, #[]⟩))
      | _, _ => (s, .error ("eval", "plot: the range must evaluate to numbers", none))
    | .fn "epicycles" (f :: .var t :: rest) =>
      match record t f with
      | (s, .error msg) => (s, .error ("eval", msg, none))
      | (s, .ok (output, d)) =>
        -- distribute first (the pipeline never does): 2i/π·(e^{−it} − e^{it}) is two terms, not one
        match fourierTerms output t <|> fourierTerms (Expand.dist output) t with
        | none => (s, .error ("eval", s!"epicycles: {output.toText} is not a finite sum of terms c·exp(i·k·{t}) with integer k", none))
        | some fts =>
          match fts.mapM fun ft => (evalNumericC [] ft.coeff).toOption.map fun c => (ft.k, c, some ft.coeff) with
          | none => (s, .error ("eval", "epicycles: a coefficient could not be evaluated numerically (unbound variable?)", none))
          | some terms =>
            -- slow, big circles first: by |k|, then k
            let terms := terms.toArray.qsort fun (k₁, _, _) (k₂, _, _) => k₁.natAbs < k₂.natAbs || (k₁.natAbs == k₂.natAbs && k₁ < k₂)
            let n := samples rest 400
            let trace := (epicycleTrace (terms.map fun (k, c, _) => (k, c)) n).map fun (x, y) => (x, some y)
            (s, .ok (f, output, d, ⟨t, 0, 2 * 3.141592653589793, #[⟨output, trace, true⟩], terms⟩))
    -- `epicycles(points[, modes])` — a list of points instead of a Fourier sum — is `dft`
    | .fn "dft" (p :: rest) | .fn "epicycles" (p :: rest) =>
      match samplePoints (substitute s.env (substituteFns s.fns p)) with
      | .error msg => (s, .error ("eval", msg, none))
      | .ok pts =>
        let all := dft pts
        let modes := match rest with | [.num k] => k.val.num.toNat | _ => all.size
        -- keep the `modes` largest coefficients (an approximation; all of them reproduce the samples exactly)
        let sorted := all.qsort fun (_, a) (_, b) => a.abs > b.abs
        let kept := (sorted.extract 0 (min modes sorted.size)).qsort fun (k₁, _) (k₂, _) => k₁.natAbs < k₂.natAbs || (k₁.natAbs == k₂.natAbs && k₁ < k₂)
        let n := max 400 pts.size
        let trace := (epicycleTrace kept n).map fun (x, y) => (x, some y)
        let terms := kept.map fun (k, c) => (k, c, (none : Option Expr))
        let d : Derivation := ⟨value, #[], value⟩
        let s := { s with cells := (cellId, { output := value, derivation := d }) :: s.cells.filter (·.1 != cellId) }
        (s, .ok (p, value, d, ⟨"t", 0, 2 * 3.141592653589793, #[⟨value, trace, true⟩], terms⟩))
    | _ => bad

/-- `plotValue` of a cell's source: parse it and resolve `%`, `%%` and `%n` first. -/
def plotCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Expr × Derivation × Plot) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok value => plotValue s cellId value

/-- The number the session reads `e` as, exactly: its normal form, when that is a numeral. -/
def Session.exactNum (s : Session) (e : Expr) : Option Q :=
  match (normalizeT pipelineRules pipelineOrdered (substitute s.env (substituteFns s.fns e))).run #[] with
  | (.ok (.num q), _) => some q
  | _ => none

/-- A calculation as it reads: the term it starts from, then each step's whole term, skipping a
step that prints the same as the one before (a silent rule). -/
def workChain (input : Expr) (steps : Array Step) : Array Expr :=
  (steps.map (·.after)).foldl (fun acc e => if (acc.back?.map (·.toText)) == some e.toText then acc else acc.push e) #[input]

/-- One part of a `manipulate` frame, evaluated as its own cell would be: its normal form, its
samples when it is a plot, and otherwise its calculation (`workChain`). A part that is a name the
session binds is labelled with it. -/
structure FramePart where
  label : Option String := none
  output : Expr
  plot : Option Plot := none
  work : Array Expr := #[]

/-- One frame of `manipulate`: the parameter's value and the body evaluated with it. A body of one
part is the frame itself (`plot`, `work`); a `column(…)` body has its `parts`. -/
structure Frame where
  value : Q
  output : Expr
  plot : Option Plot := none
  work : Array Expr := #[]
  parts : Array FramePart := #[]

/-- `manipulate(e, p, from, to[, frames])`, Mathematica's `Manipulate`: `e` evaluated as a cell
would be, once for each of `frames` values of `p` (40 unless given, at most 200) evenly spaced from
`from` to `to`, either way round (the first is where the slider starts). `from` and `to` must
normalize to numbers, so the values are exact (approximate when an end is a decimal). `e` may be
`column(e₁, e₂, …)`, Mathematica's `Column`: each part is evaluated as its own cell, so a plot and
the calculations beside it move together. A plot is sampled at every frame; any other part keeps its
calculation with `p` put in. The session's names are put in before `p`, so a name bound to a term in
`p` (`let m = … h …`) moves with it. The cell records the first frame; `p` is bound only inside the
frames. The frames are presentation, like a plot's samples: only the first frame's work is kept as
the cell's. -/
def manipulateCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Derivation × String × Array Frame) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok (.fn "manipulate" (body :: .var p :: a :: b :: more)) =>
      match s.exactNum a, s.exactNum b with
      | some q0, some q1 =>
        let k := match more with
          | [.num m] => min 200 (max 2 m.val.num.toNat)
          | _ => 40
        let isColumn := match body with | .fn "column" _ => true | _ => false
        let partsSrc : List Expr := match body with | .fn "column" ps => ps | e => [e]
        let varOf (e : Expr) : Option String := match e with | .fn "plot" (_ :: .var x :: _) => some x | _ => none
        if partsSrc.any (fun e => varOf e == some p) then (s, .error ("eval", s!"manipulate: {p} is the plot's own variable; manipulate another name", none)) else
        let values := (List.range k).map fun (j : Nat) => q0 + (q1 - q0) * Q.ofInt (j : Int) / Q.ofInt ((k - 1 : Nat) : Int)
        -- the session's names first, then `p`: a name bound to a term in `p` (`let m = … h …`) moves
        -- with it. A plot's own variable is its binder and stays.
        let sp : Session := { s with env := s.env.filter (·.1 != p) }
        let prepared : List (Option String × Expr) := partsSrc.map fun e =>
          let label := match e with | .var n => if (sp.env.lookup n).isSome then some n else none | _ => none
          (label, substitute (sp.env.filter (·.1 != (varOf e).getD p)) (substituteFns s.fns e))
        -- one part at one value: a plot sampled, any other term normalized with its calculation
        let part (label : Option String) (e : Expr) : Except String (FramePart × Derivation) :=
          match e with
          | .fn "plot" _ =>
            match plotValue sp cellId e with
            | (_, .error (_, msg, _)) => .error msg
            | (_, .ok (_, out, d, pl)) => .ok ({ label := label, output := out, plot := some pl }, d)
          | _ =>
            match (normalizeT pipelineRules pipelineOrdered e).run #[] with
            | (.error msg, _) => .error msg
            | (.ok out, steps) => .ok ({ label := label, output := out, work := workChain e steps }, ⟨e, steps, out⟩)
        let record (out : Expr) (d : Derivation) : Session :=
          { s with cells := (cellId, { output := out, derivation := d }) :: s.cells.filter (·.1 != cellId) }
        -- one frame: every part with `p` set to `v`; the session keeps the cell, not the binding
        let frame (v : Q) : Except String (Session × Frame × Derivation) := do
          let put (e : Expr) : Expr := substitute [(p, .num v)] e
          let ps ← prepared.mapM fun (label, e) => part label (put e)
          match isColumn, ps with
          | false, [(pt, d)] =>
            pure (record pt.output d, { value := v, output := pt.output, plot := pt.plot, work := pt.work }, d)
          | _, _ =>
            let out := Expr.fn "column" (ps.map (·.1.output))
            let d : Derivation := ⟨Expr.fn "column" (prepared.map fun (_, e) => put e), #[], out⟩
            pure (record out d, { value := v, output := out, parts := (ps.map (·.1)).toArray }, d)
        match values.mapM frame with
        | .error msg => (s, .error ("eval", s!"manipulate: {msg}", none))
        | .ok [] => (s, .error ("eval", "manipulate: no frames", none))
        | .ok ((s0, f0, d0) :: rest) => (s0, .ok (f0.output, d0, p, (f0 :: rest.map (·.2.1)).toArray))
      | _, _ => (s, .error ("eval", "manipulate: the range must evaluate to numbers", none))
    | .ok _ => (s, .error ("eval", "manipulate takes an expression, a parameter and its range: manipulate(e, p, from, to[, frames])", none))

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
