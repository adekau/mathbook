import MathEngine.Integrate
import MathEngine.Origin
import MathEngine.Parser
import MathEngine.Lambda
import MathEngine.Poset
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
  /-- λ-cell definitions (`name := term`), by name; the Church library sits behind them. -/
  lambdas : List (String × Lam.Term) := []
  /-- Order-world values: posets and maps on them, by name. -/
  posets : List (String × Ord.Poset) := []
  pmaps : List (String × Ord.PMap) := []
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
      let s := { s with cells := (cellId, ⟨output, d⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match stmt with
        | .«let» name [] _ => { s with env := (name, output) :: s.env.filter (·.1 != name) }
        | .«let» name ps _ => { s with fns := (name, (ps, output)) :: s.fns.filter (·.1 != name) }
        | _ => s
      (s, .ok (stmt, output, d))

/-- What a λ-cell produced. -/
structure LamResult where
  name : Option String
  input : Lam.Term
  output : Lam.Term
  derivation : Derivation
  /-- The de Bruijn view of each step's result, in step order. -/
  dbSteps : Array Expr
  reading : Option String

/-- The names a λ-cell may use: the session's definitions, then the Church library. -/
def lambdaDefs (s : Session) : List (String × Lam.Term) := s.lambdas ++ Lam.churchDefs

/-- Is the source a λ-cell for this session? -/
def isLambdaCell (s : Session) (source : String) : Bool :=
  Lam.isLambdaSource source ((lambdaDefs s).map (·.1))

/-- Evaluate a λ-cell: unfold definitions (one δ-step), then reduce in normal order, one β-step at
a time, every step recorded with its de Bruijn view. A term without a normal form after
`Lam.maxSteps` steps is refused — the one budget in the engine, since the question is undecidable. -/
def lambdaCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) LamResult :=
  match Lam.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (name, t) =>
    let expanded := Lam.expandDefs (lambdaDefs s) t
    let (out, trace, normal) := Lam.reduce expanded
    if !normal then
      (s, .error ("eval", s!"λ: no normal form after {Lam.maxSteps} β-steps; the term had become {(Lam.toExpr out).toText}", none))
    else
      let δ : Array Step := if expanded != t then
          #[⟨"lambda.delta", "δ: unfold the definitions used (the session's, then the Church library's).", [], Lam.toExpr t, Lam.toExpr expanded, none⟩]
        else #[]
      let (steps, _) := trace.foldl (fun (acc, prev) (t', renamed) =>
          let step : Step := if renamed then
              ⟨"lambda.alpha-beta", "α then β: a binder of the body was renamed so the argument's free variables are not captured, then the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracted to $b[x := a]$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩
            else ⟨"lambda.beta", "β: the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracts to $b[x := a]$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩
          (acc.push step, t')) (δ, expanded)
      let d : Derivation := ⟨Lam.toExpr t, steps, Lam.toExpr out⟩
      let dbSteps := steps.map fun st => Lam.dbToExpr (Lam.toDB [] (dbOf st.after))
      let reading := match Lam.readChurch out with
        | some n => some s!"the Church numeral {n}"
        | none => match Lam.readBool out with
          | some true => some "the Church boolean true"
          | some false => some "the Church boolean false"
          | none => none
      let s := { s with cells := (cellId, ⟨Lam.toExpr out, d⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match name with
        | some n => { s with lambdas := (n, out) :: s.lambdas.filter (·.1 != n) }
        | none => s
      (s, .ok ⟨name, t, out, d, dbSteps, reading⟩)
where
  /-- The steps store the encoded term; decode it for the de Bruijn view. -/
  dbOf (e : Expr) : Lam.Term := (Lam.ofExpr e).getD (.var "?")

/-- What an order-world cell produced: a value (encoded), the derivation, and the poset to draw. -/
structure OrdResult where
  name : Option String
  value : Expr
  derivation : Derivation
  poset : Option Ord.Poset
  summary : String

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
    let getF (a : Ord.Arg) : Except String Ord.PMap := match a with
      | .elem n => match s.pmaps.lookup n with | some f => .ok f | none => .error s!"'{n}' is not a map"
      | _ => .error "expected the name of a map"
    -- an element of `P`, written as a name or, for a subsets poset, as a set literal
    let getE (P : Ord.Poset) (a : Ord.Arg) : Except String String := match a with
      | .elem x => if P.elems.contains x then .ok x else .error s!"'{x}' is not an element of the poset"
      | .set xs =>
        -- a subsets-poset element is written `{a,b}`; match the literal as a set, whatever the order
        let key := xs.eraseDups
        let members (e : String) : List String := (((e.replace "{" "").replace "}" "").splitOn ",").filter (· != "")
        match P.elems.find? fun e => e.startsWith "{" && (members e).length == key.length && key.all ((members e).contains ·) with
        | some e => .ok e
        | none => .error ("{" ++ ",".intercalate xs ++ "} is not an element of the poset")
      | _ => .error "expected an element"
    let getS (P : Ord.Poset) (a : Ord.Arg) : Except String (List String) := match a with
      | .set xs => xs.mapM fun x => getE P (.elem x)
      | .elem x => (getE P (.elem x)).map ([·])
      | _ => .error "expected a set of elements"
    let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
    let done (value : Expr) (steps : Array Step) (P : Option Ord.Poset) (summary : String) (bindP : Option Ord.Poset := none) (bindF : Option Ord.PMap := none) :
        Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
      -- the derivation starts where the first step does, so the echo shows the question, not the answer
      let input := match steps[0]? with | some st => st.before | none => value
      let d : Derivation := ⟨input, steps, value⟩
      let s := { s with cells := (cellId, ⟨value, d⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match name, bindP with
        | some n, some P => { s with posets := (n, P) :: s.posets.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindF with
        | some n, some f => { s with pmaps := (n, f) :: s.pmaps.filter (·.1 != n) }
        | _, _ => s
      (s, .ok ⟨name, value, d, P, summary⟩)
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
        match ps.find? fun (a, b) => !P.elems.contains a || !P.elems.contains b with
        | some (a, b) => err s!"{a} -> {b} mentions an element outside the poset"
        | none =>
          let f : Ord.PMap := ⟨ps⟩
          let value := Ord.setExpr (ps.map fun (a, b) => s!"{a}↦{b}")
          done value #[] none s!"a map on {pn} ({ps.length} explicit values; other elements are fixed)" (bindF := some f)
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
    | h, _ => err s!"{h}: wrong arguments (see the reference)"

/-- A sampled plot: the variable, the range, and one series per function — its normalized term and
`(t, y)` pairs (`none` where it has no finite value). -/
structure Plot where
  var : String
  from_ : Float
  to : Float
  series : Array (Expr × Array (Float × Option Float))

/-- The curves a plot argument names: a list `[f, g, …]` (which the parser reads as a one-row
matrix; a column is accepted too) is one curve per entry, a scalar is one curve, and a genuine
matrix is none. -/
def plotFns : Expr → Option (List Expr)
  | .matrix [row] => some row
  | .matrix rows => if rows.all (·.length == 1) then some (rows.filterMap List.head?) else none
  | e => some [e]

/-- `plot(f, x, from, to[, n])` or `plot([f, g, …], x, from, to[, n])`: simplify the function (or
the list, entrywise) under the session — so derivatives and session functions plot as what they
are — record the cell like any other, and sample each curve on a uniform grid with the numeric
evaluator. Sampling is presentation: the derivation shown is the list's. -/
def plotCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Expr × Derivation × Plot) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    let bad := (s, .error ("eval", "plot takes a function, a variable, and the range: plot(f, x, from, to)", none))
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok value =>
    match value with
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
          match plotFns output with
          | none => (s, .error ("eval", "plot: give one function or a list [f, g, …], not a matrix", none))
          | some fns =>
          let d : Derivation := ⟨input, steps, output⟩
          let s := { s with cells := (cellId, ⟨output, d⟩) :: s.cells.filter (·.1 != cellId) }
          let sample (g : Expr) := (Array.range n).map fun i =>
            let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
            let y := (evalNumeric [(x, t)] g).toOption.filter fun v => v.isFinite
            (t, y)
          let series := fns.toArray.map fun g => (g, sample g)
          (s, .ok (f, output, d, ⟨x, lo, hi, series⟩))
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
