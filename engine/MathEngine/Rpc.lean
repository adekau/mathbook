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
means no theorem yet (M4 covers `diff.*`, M7 `la.*`). Rules absent from this list are unverified. -/
def ruleStatus : Json :=
  let entry (name status note : String) : Json :=
    .obj #[("rule", .str name), ("status", .str status), ("note", .str note)]
  .arr #[
    entry "simp.flatten" "verified" "Associativity of + and ·.",
    entry "simp.identity" "verified" "The additive and multiplicative identities and the annihilator.",
    entry "simp.fold-constants" "verified" "Exact rational arithmetic; ℚ embeds in ℝ.",
    entry "simp.collect-like-terms" "verified" "Distributivity: a·t + b·t = (a+b)·t.",
    entry "simp.power" "verified" "Includes exact roots; the root search returns only checked roots.",
    entry "simp.collect-powers" "conditional" "b^m·b^n = b^(m+n) needs a positive base: at b = 0 it turns 0 into 1.",
    entry "simp.function" "conditional" "exp(ln x) = x needs 0 < x: at x = -1 it turns -1 into 1.",
    entry "diff.constant" "verified" "A term the variable does not occur in has derivative 0.",
    entry "diff.variable" "verified" "The identity function has slope 1 everywhere.",
    entry "diff.constant-multiple" "verified" "Constant factors pull out; no differentiability needed.",
    entry "diff.sum" "conditional" "Needs every summand differentiable: for |x| + x at 0 the rule gives 1 where the derivative does not exist.",
    entry "diff.product" "conditional" "Needs both factors differentiable at the point.",
    entry "diff.power" "conditional" "Proved for a natural exponent with a differentiable base; real exponents still open.",
    entry "diff.chain" "conditional" "Needs the inner function differentiable; proved for sin, cos and exp, while ln and tan also need a domain condition.",
    entry "diff.matrix" "unverified" "Proved, but matrices carry no value in the ℝ semantics yet, so the theorem has no content until M7.",
    entry "diff.higher-order" "unverified" "An abbreviation: it eliminates the three-argument form, so there is nothing to prove."]

def capabilities : Json :=
  .obj #[("engine", .str "engine-lean"), ("version", .str "0.1.0-m5"), ("verified", .bool true),
         ("features", .arr #[.str "simplify", .str "expand", .str "diff", .str "linalg", .str "numeric"]),
         ("ruleStatus", ruleStatus),
         ("termination", .obj #[("status", .str "proven"), ("theorem", .str "MathEngine.pipelineOrdered"),
           ("summary", .str "Cell evaluation has no step budget: every pipeline rule decreases a five-tier ordering (commands, higher-order diff, matrix literals, the weight M, size) on nodes whose children are normal. Only the nested `expand` set still runs on fuel.")])]

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

def evaluate (st : Store) (params : Json) : Store × Json :=
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (s, r) := evaluateCell (st.get sessionId) cellId src
    let st := st.set sessionId s
    match r with
    | .error (code, msg, span) => (st, errorJson code msg span)
    | .ok (stmt, out, d) =>
      let paths := params.getBool "paths"
      let res := #[("ok", .bool true), ("value", out.toJson), ("rendered", Rendered.toJson out paths)]
      let res := if params.getBool "showWork" then
          (res.push ("derivation", d.toJson)).push ("inputRendered", Rendered.toJson d.input false)
        else res
      let res := match stmt with
        | .«let» name _ => res.push ("bound", .arr #[.str name])
        | _ => res
      (st, .obj res)

def explain (st : Store) (params : Json) : Except String Json := do
  let sessionId := (params.getStr? "sessionId").getD ""
  let cellId := (params.getStr? "cellId").getD ""
  let path ← match params.get? "path" >>= pathOfJson with | some p => pure p | none => throw "missing or malformed path"
  let (sub, steps) ← explainCell (st.get sessionId) cellId path
  pure (.obj #[("subterm", sub.toJson), ("rendered", Rendered.toJson sub false), ("steps", .arr (steps.map Step.toJson))])

def dispatch (st : Store) (req : Json) : Store × Json :=
  let id := (req.get? "id").getD .null
  let params := (req.get? "params").getD (.obj #[])
  let reply (r : Json) : Json := .obj #[("jsonrpc", .str "2.0"), ("id", id), ("result", r)]
  let fail (code : Int) (msg : String) : Json :=
    .obj #[("jsonrpc", .str "2.0"), ("id", id), ("error", .obj #[("code", .num (toString code)), ("message", .str msg)])]
  match req.getStr? "method" with
  | some "engine.capabilities" => (st, reply capabilities)
  | some "engine.evaluate" => let (st, r) := evaluate st params; (st, reply r)
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
