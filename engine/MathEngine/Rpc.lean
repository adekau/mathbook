import MathEngine.Json
import MathEngine.Wire
import MathEngine.Parser
import MathEngine.Print
import MathEngine.Session
/-!
# JSON-RPC surface

One pure function `handleS : Store → String → Store × String`. Every host — the Emscripten worker,
the native stdio server, a future HTTP server — is a shim around this function that keeps the
`Store` between calls (the C shim holds it in a static; `Main.lean` threads it through its loop).
The engine itself has no mutable state.
-/
namespace MathEngine
open Json

/-- Proof status of each rewrite rule, so a frontend can say which steps of a derivation are
machine-checked instead of guessing. Kept next to the rules it describes: `verified` means an
unconditional soundness theorem over ℝ (`proofs/Proofs/SimpReal.lean`), `conditional` means the
theorem needs a side condition *and* the necessity of that condition is itself proved, `unverified`
means no theorem yet, `checked` means the step is a guess whose result a later step verifies
(the `int.*` finder, checked by `int.check`). The `la.row-*` rules are proved over ℚ (`LinAlgQ.lean`), not ℝ: their claim is
that the row operation preserves the solution set. Rules absent from this list are unverified. -/
def ruleStatus : Json :=
  let entry (name status note : String) : Json :=
    .obj #[("rule", .str name), ("status", .str status), ("note", .str note)]
  -- a rule with a theorem over ℂ as well (`proofs/Proofs/Cx.lean`): the status a cell containing `i` shows
  let entryC (name status note cstatus cnote : String) : Json :=
    .obj #[("rule", .str name), ("status", .str status), ("note", .str note),
           ("complex", .obj #[("status", .str cstatus), ("note", .str cnote)])]
  .arr #[
    entryC "simp.flatten" "verified" "Associativity of + and ·." "verified" "Associativity, in any field (flatten_soundC).",
    entryC "simp.identity" "verified" "The additive and multiplicative identities and the annihilator." "verified" "The identities and the annihilator, in any field (identity_soundC).",
    entryC "simp.fold-constants" "verified" "Exact rational arithmetic; ℚ embeds in ℝ." "verified" "ℚ embeds in ℂ (foldConstants_soundC).",
    entryC "simp.collect-like-terms" "verified" "Distributivity: a·t + b·t = (a+b)·t." "verified" "Distributivity (collectTerms_soundC).",
    entryC "simp.power" "verified" "Includes exact roots; the root search returns only checked roots." "verified" "The principal branch agrees with the real power on the positive rational bases the exact roots use (powerRules_soundC).",
    entry "simp.collect-powers" "conditional" "b^m·b^n = b^(m+n) needs a positive base: at b = 0 it turns 0 into 1.",
    entryC "simp.function" "conditional" "exp(ln x) = x needs 0 < x: at x = -1 it turns -1 into 1. The other cases, sin/cos = tan among them, are unconditional." "unverified" "ln(exp x) = x is false on the principal branch: at x = 2πi it turns 2πi into 0 (not_functionRules_soundC).",
    entry "diff.constant" "verified" "A term the variable does not occur in has derivative 0.",
    entry "diff.variable" "verified" "The identity function has slope 1 everywhere.",
    entry "diff.constant-multiple" "verified" "Constant factors pull out; no differentiability needed.",
    entry "diff.sum" "conditional" "Needs every summand differentiable: for |x| + x at 0 the rule gives 1 where the derivative does not exist.",
    entry "diff.product" "conditional" "Needs both factors differentiable at the point.",
    entry "diff.power" "conditional" "Proved for a natural exponent with a differentiable base; real exponents still open.",
    entry "diff.chain" "conditional" "Needs the inner function differentiable; proved for sin, cos and exp, while ln and tan also need a domain condition.",
    entry "diff.matrix" "unverified" "Proved, but matrices carry no value in the ℝ semantics, so the theorem has no content yet.",
    entry "diff.higher-order" "unverified" "An abbreviation: it eliminates the three-argument form, so there is nothing to prove.",
    entry "cmd.rref" "verified" "Over ℚ the reduced matrix has the input's solution set (LinQ.sol_rref) and is in reduced row echelon form (LinQ.rref_isRref). With symbolic entries the nested row operations are the unverified .symbolic ones, and the step inherits their status.",
    entry "la.row-swap" "verified" "Exchanging two rows preserves the solution set (LinQ.sol_swap); elimination as a whole: LinQ.sol_rref.",
    entry "la.row-scale" "verified" "Scaling a row by a nonzero rational preserves the solution set (LinQ.sol_scale).",
    entry "la.row-add" "verified" "Adding a multiple of another row preserves the solution set (LinQ.sol_addMul).",
    entry "la.row-swap.symbolic" "unverified" "Symbolic entries: the pivot is assumed nonzero because simplify could not show it is zero.",
    entry "la.row-scale.symbolic" "unverified" "Symbolic entries: division by a pivot that is only assumed nonzero.",
    entry "la.row-add.symbolic" "unverified" "Symbolic entries: the arithmetic is the simplifier's, outside the ℚ theorem.",
    entry "simp.radical" "verified" "A perfect-power base is reduced (8^(1/2) = 2^(3/2)) and same-index radicals multiply under one root; unconditional, the bases are positive integers (radicalBase_soundR, mulRadicals_soundR).",
    entry "simp.collect-radicals" "verified" "Radicals with the same square-free part collect, √50 − √18 = 2√2; unconditional (collectRadicals_soundR).",
    entry "cmd.expand" "verified" "Distribution is a total function proved sound over ℝ (dist_sound, proofs/Proofs/Expand.lean); the collection afterwards is the pipeline's own steps with their statuses.",
    entry "expand.distribute" "verified" "Multiplying out a product of sums and collecting like monomials: dist_sound.",
    entry "expand.power" "verified" "A power of a sum is the sum multiplied by itself: dist_sound.",
    entry "cmd.integrate" "verified" "Accepted only when the candidate's derivative normalizes to the integrand, exactly (cmdIntegrate_spec); integrate_deriv reads that as deriv F = f wherever the differentiation steps shown are sound. The finder's own steps are guesses.",
    entry "int.bounds" "verified" "The fundamental theorem of calculus: the checked antiderivative evaluated at the bounds, F(b) − F(a) (cmdIntegrate_definite_spec; integrate_definite reads it as the interval integral over ℝ, for an integrand continuous on [a, b]).",
    entry "cmd.sum" "verified" "A definition: one substituted term per integer value of the index (cmdSum_spec); sum_soundR reads the result as the finite sum over ℝ.",
    entryC "cmd.exptotrig" "unverified" "Euler's formula has no content over ℝ, where i is the junk value 0." "verified" "exp(iθ) = cos θ + i sin θ for every complex θ (expToTrig_soundC).",
    entry "la.dot" "verified" "Σ uᵢvᵢ by definition; a matrix has no value in the ℝ semantics, so the claim is the definition (bilinear, as Mathematica's Dot — the Hermitian product is dot(u, conj(v))).",
    entry "la.norm" "verified" "(Σ vᵢ²)^(1/2) by definition, the Pythagorean length.",
    entry "la.conj" "verified" "Entrywise by definition.",
    entry "int.check" "verified" "The differentiation of the candidate: this step carries the claim, with the statuses of its own steps.",
    entry "int.compare" "verified" "Derivative and integrand are rewritten with cos²u = 1 − sin²u and (eᵘ)ᵏ = eᵏᵘ (identNorm), expanded (dist) and simplified before comparison — both rewrites proved sound, and needed because the pipeline applies neither identity nor distributes a numeral over a sum; the statuses of the simplification steps apply.",
    entry "int.constant" "checked" "A guess from the finder; nothing is proved about it. Accepted only because int.check verifies the result by differentiation.",
    entry "int.variable" "checked" "A guess from the finder, verified by int.check.",
    entry "int.sum" "checked" "A guess from the finder, verified by int.check.",
    entry "int.constant-multiple" "checked" "A guess from the finder, verified by int.check.",
    entry "int.power" "checked" "A guess from the finder, verified by int.check (the symbolic-exponent case relies on simp.collect-powers there).",
    entry "int.exponential" "checked" "A guess from the finder, verified by int.check.",
    entry "int.table" "checked" "A guess from the finder, verified by int.check.",
    entry "int.linear-substitution" "checked" "A guess from the finder, verified by int.check.",
    entry "int.substitution" "checked" "A guess from the finder (u-substitution), verified by int.check.",
    entry "int.by-parts" "checked" "A guess from the finder (integration by parts), verified by int.check.",
    entry "int.trig-power" "checked" "A guess from the finder (the reduction formula for sinᵐu cosⁿu), verified by int.check.",
    entry "int.exp-power" "checked" "A guess from the finder ((eᵘ)ᵏ = eᵏᵘ, then the table), verified by int.check.",
    entry "order.closure" "verified" "The order is the reflexive-transitive closure, and reflexivity, antisymmetry and transitivity are decided (checkPartialOrder_none).",
    entry "order.covers" "verified" "Hasse edges are exactly the covers: x < y with nothing strictly between (covers_spec).",
    entry "order.upper-bounds" "verified" "Every element above both, by the decision on the finite order.",
    entry "order.least" "verified" "The element found is an upper bound below every upper bound (sup_spec); none exists when the search fails (sup_none).",
    entry "order.lower-bounds" "verified" "Every element below both, by the decision on the finite order.",
    entry "order.greatest" "verified" "Dual of the join: the greatest lower bound.",
    entry "order.lattice" "verified" "Every pair searched for a join and a meet; the witness is reported when one is missing.",
    entry "order.cover" "verified" "A cover in the Hasse diagram; the chain composes by transitivity.",
    entry "order.monotone" "verified" "Every pair x ≤ y of the order checked; the witness is reported when it fails.",
    entry "order.iterate" "verified" "One step of the Kleene chain; each element of the chain is below every fixed point (iter_le_fixed).",
    entry "order.fixed" "verified" "The chain stopped at a fixed point (checked), which iter_le_fixed makes the least (dually, the greatest).",
    entryC "cx.i-power" "unverified" "i has no real meaning; read in ℂ." "verified" "i² = −1 (Complex.I_sq); the powers cycle.",
    entryC "cx.arithmetic" "unverified" "i has no real meaning; read in ℂ." "verified" "Products of Gaussian rationals, by the field laws and i² = −1.",
    entryC "cx.power" "unverified" "i has no real meaning; read in ℂ." "verified" "Integer powers and inverses of Gaussian rationals; 1/(a+bi) = (a−bi)/(a²+b²).",
    entryC "cx.conjugate" "unverified" "i has no real meaning; read in ℂ." "verified" "Conjugation of a Gaussian rational, and conj ∘ conj = id.",
    entryC "cx.re-im" "unverified" "i has no real meaning; read in ℂ." "verified" "Real and imaginary parts of a Gaussian rational.",
    entryC "cx.abs" "unverified" "i has no real meaning; read in ℂ." "verified" "|a + bi| = √(a² + b²) (Complex.abs_apply, normSq).",
    entryC "cx.exact-trig" "verified" "sin, cos, tan at rational multiples of π: period, reflections and the reference angles (Real.sin_pi_div_four and friends)." "verified" "The real values, cast (Complex.ofReal_sin, ofReal_cos)." ,
    entryC "cx.euler" "unverified" "i has no real meaning; read in ℂ." "verified" "Euler's formula exp(iθ) = cos θ + i sin θ (Complex.exp_mul_I) with the exact values.",
    entryC "cx.euler-power" "verified" "(e¹)^b = e^b (Real.rpow_def_of_pos)." "verified" "(e¹)^b = e^b (Complex.cpow_def, log_exp with Im 1 = 0).",
    entry "lambda.delta" "verified" "Unfolding a definition replaces a free name by its term; nothing to prove beyond that.",
    entry "lambda.beta" "unverified" "β-reduction with capture-avoiding substitution; the substitution lemma is not yet proved.",
    entry "lambda.alpha-beta" "unverified" "A binder renamed to avoid capture, then β; the renaming is not yet proved to preserve α-equivalence."]

def capabilities : Json :=
  .obj #[("engine", .str "engine-lean"), ("version", .str "0.1.0-m8"), ("verified", .bool true),
         ("features", .arr #[.str "simplify", .str "expand", .str "diff", .str "linalg", .str "numeric", .str "integrate", .str "plot", .str "lambda", .str "order", .str "sum", .str "exptotrig"]),
         ("ruleStatus", ruleStatus),
         ("termination", .obj #[("status", .str "proven"), ("theorem", .str "MathEngine.pipelineOrdered"),
           ("summary", .str "Cell evaluation has no step budget: every pipeline rule decreases a five-tier ordering (commands, higher-order diff, matrix literals, the weight M, size) on nodes whose children are normal.")])]

def Rendered.toJson (e : Expr) (paths : Bool) : Json :=
  .obj #[("text", .str e.toText), ("latex", .str (e.toLatex paths))]

private def errorJson (code msg : String) (span : Option (Nat × Nat) := none) : Json :=
  let err := #[("code", .str code), ("message", .str msg)]
  let err := match span with
    | some (s, e) => err.push ("span", .obj #[("start", .num (toString s)), ("end", .num (toString e))])
    | none => err
  .obj #[("ok", .bool false), ("error", .obj err)]

private def pathOfJson : Json → Option Path
  | .arr xs => xs.toList.mapM fun j => match j with | .num s => s.toNat? | _ => none
  | _ => none

/-- A λ-cell's reply: like an ordinary one, plus the de Bruijn renderings and the reading. -/
def evaluateLambda (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := lambdaCell (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let d := res.derivation
    let steps := (d.steps.zip res.dbSteps).map fun (stp, db) =>
      match stp.toJson paths with
      | .obj fields => Json.obj (fields.push ("afterDeBruijn", Rendered.toJson db false))
      | j => j
    let dj : Json := .obj #[("input", d.input.toJson), ("steps", .arr steps), ("output", d.output.toJson)]
    let out := Lam.toExpr res.output
    let r := #[("ok", .bool true), ("kind", .str "lambda"), ("value", out.toJson), ("rendered", Rendered.toJson out paths),
      ("renderedDeBruijn", Rendered.toJson (Lam.dbToExpr (Lam.toDB [] res.output)) false)]
    let r := match res.reading with | some t => r.push ("reading", .str t) | none => r
    let r := if params.getBool "showWork" then
        (r.push ("derivation", dj)).push ("inputRendered", Rendered.toJson d.input paths)
      else r
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- An order-world cell's reply: the value, the derivation, and the poset to draw. -/
def evaluateOrder (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := orderCell (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let r := #[("ok", .bool true), ("kind", .str "poset"), ("value", res.value.toJson), ("rendered", Rendered.toJson res.value paths),
      ("summary", .str res.summary)]
    let r := match res.poset with
      | some P => r.push ("hasse", .obj #[
          ("nodes", .arr (P.elems.map fun x => Json.obj #[("name", .str x), ("height", .num (toString (Ord.height P x)))]).toArray),
          ("covers", .arr ((Ord.hasse P).map fun (a, b) => Json.arr #[.str a, .str b]).toArray)])
      | none => r
    let r := if params.getBool "showWork" then
        (r.push ("derivation", res.derivation.toJson paths)).push ("inputRendered", Rendered.toJson res.derivation.input paths)
      else r
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- Number the evaluation (`In[n]`), remember its output for `%`, and put the label in the reply. -/
def withLabel (st : Store) (sessionId cellId : String) (j : Json) : Store × Json :=
  let s := st.get sessionId
  let ok := match j.get? "ok" with | some (.bool true) => true | _ => false
  let out := if ok then (s.cells.lookup cellId).map (·.output) else none
  let (s, n) := s.tick out
  let j := match j with
    | .obj fs => Json.obj (fs.push ("label", .num (toString n)))
    | j => j
  (st.set sessionId s, j)

def evaluate (st : Store) (params : Json) : Store × Json :=
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (st, j) := evaluateCore st params sessionId cellId src
    withLabel st sessionId cellId j
where
  evaluateCore (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
    if Ord.isOrderSource src then evaluateOrder st params sessionId cellId src else
      if isLambdaCell (st.get sessionId) src then evaluateLambda st params sessionId cellId src else
      let (s, r) := evaluateCell (st.get sessionId) cellId src
      let st := st.set sessionId s
      match r with
      | .error (code, msg, span) => (st, errorJson code msg span)
      | .ok (stmt, out, d) =>
        let paths := params.getBool "paths"
        let sem := if mentionsI d.input || mentionsI out then "complex" else "real"
        let res := #[("ok", .bool true), ("value", out.toJson), ("rendered", Rendered.toJson out paths), ("semantics", .str sem)]
        let res := if params.getBool "showWork" then
            (res.push ("derivation", d.toJson paths)).push ("inputRendered", Rendered.toJson d.input paths)
          else res
        let res := match stmt with
          | .«let» name [] _ => res.push ("bound", .arr #[.str name])
          | .«let» name ps _ => (res.push ("bound", .arr #[.str name])).push ("params", .arr (ps.map .str).toArray)
          | _ => res
        (st, .obj res)

private def floatJson (x : Float) : Json := .num (toString x)

def plot (st : Store) (params : Json) : Store × Json :=
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (s, r) := plotCell (st.get sessionId) cellId src
    let st := st.set sessionId s
    let (st, j) := match r with
    | .error (code, msg, span) => (st, errorJson code msg span)
    | .ok (_, out, d, pl) =>
      let paths := params.getBool "paths"
      let ptsJson (pts : Array (Float × Option Float)) : Json :=
        .arr (pts.map fun (t, y) => Json.arr #[floatJson t, match y with | some v => floatJson v | none => .null])
      let series := pl.series.map fun (g, pts) => Json.obj #[("rendered", Rendered.toJson g false), ("points", ptsJson pts)]
      let res := #[("ok", .bool true), ("kind", .str "plot"), ("value", out.toJson), ("rendered", Rendered.toJson out paths),
        ("var", .str pl.var), ("from", floatJson pl.from_), ("to", floatJson pl.to), ("series", .arr series)]
      let res := if params.getBool "showWork" then
          (res.push ("derivation", d.toJson paths)).push ("inputRendered", Rendered.toJson d.input paths)
        else res
      (st, .obj res)
    withLabel st sessionId cellId j

def explain (st : Store) (params : Json) : Except String Json := do
  let sessionId := (params.getStr? "sessionId").getD ""
  let cellId := (params.getStr? "cellId").getD ""
  let path ← match params.get? "path" >>= pathOfJson with | some p => pure p | none => throw "missing or malformed path"
  -- which term the path is into: the output (default), the input, or the term after step n
  let ref : TermRef := match params.get? "term" with
    | some t => match t.getStr? "kind" with
      | some "input" => .input
      | some "step" => match t.get? "index" with
        | some (.num n) => .step (n.toNat?.getD 0)
        | _ => .output
      | _ => .output
    | none => .output
  let (sub, steps, rels) ← explainCell (st.get sessionId) cellId path ref
  let traceJson := rels.map fun (i, r) => Json.obj #[("index", .num (toString i)), ("relation", .str r.toString)]
  pure (.obj #[("subterm", sub.toJson), ("rendered", Rendered.toJson sub false), ("steps", .arr (steps.map Step.toJson)),
    ("trace", .arr traceJson.toArray)])

def dispatch (st : Store) (req : Json) : Store × Json :=
  let id := (req.get? "id").getD .null
  let params := (req.get? "params").getD (.obj #[])
  let reply (r : Json) : Json := .obj #[("jsonrpc", .str "2.0"), ("id", id), ("result", r)]
  let fail (code : Int) (msg : String) : Json :=
    .obj #[("jsonrpc", .str "2.0"), ("id", id), ("error", .obj #[("code", .num (toString code)), ("message", .str msg)])]
  match req.getStr? "method" with
  | some "engine.capabilities" => (st, reply capabilities)
  | some "engine.evaluate" => let (st, r) := evaluate st params; (st, reply r)
  | some "engine.plot" => let (st, r) := plot st params; (st, reply r)
  | some "engine.explain" =>
    match explain st params with
    | .ok r => (st, reply r)
    | .error msg => (st, fail (-32000) msg)
  | some "engine.resetSession" => (st.reset ((params.getStr? "sessionId").getD ""), reply (.obj #[("ok", .bool true)]))
  | some m => (st, fail (-32601) s!"unknown method {m}")
  | none => (st, fail (-32600) "missing method")

/-- The single entry point. C symbol `mathengine_handle_state`: `lean_object* (lean_object* store, lean_object* request)`,
returning the pair (new store, response). Both arguments are consumed. -/
@[export mathengine_handle_state]
def handleS (st : Store) (raw : String) : Store × String :=
  match Json.parse raw with
  | .error msg => (st, (Json.obj #[("jsonrpc", .str "2.0"), ("id", .null), ("error", .obj #[("code", .num "-32700"), ("message", .str msg)])]).render)
  | .ok req => let (st, r) := dispatch st req; (st, r.render)

/-- Stateless convenience (fresh store) for tests. -/
def handle (raw : String) : String := (handleS [] raw).2

end MathEngine
