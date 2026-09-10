import MathEngine.Rewrite
import MathEngine.Print
/-!
# `diff.*` — differentiation as rewriting

`diff(e, x)` is an ordinary node and the calculus rules push it inward, so the trace reads like a
textbook derivation with pending d/dx's visible at each step. Ported from `diff.ts`. These rules
duplicate subterms (product, chain), so they run under `normalizeFuel` until M5 supplies an
ordering (book/TRACKING.md); M4 proves each against `HasDerivAt`.
-/
namespace MathEngine
open Expr

private def D (e : Expr) (x : String) : Expr := .fn "diff" [e, .var x]

/-- `diff(body, x)` with a variable target, if `e` is one. -/
private def target : Expr → Option (Expr × String)
  | .fn "diff" [body, .var x] => some (body, x)
  | _ => none

private def rule (name : String) (f : Expr × String → Option RuleResult) : PlainRule :=
  { name, apply := fun e => target e >>= f }

private def rules : List PlainRule := [
  { name := "diff.higher-order", apply := fun e =>
      match e with
      | .fn "diff" [body, .var x, .num n] =>
        if n.isInt && n.val.num ≥ 1 then
          let k := n.val.num.toNat
          some ⟨(List.range k).foldl (fun r _ => D r x) body, s!"The {k}th derivative is {k} successive derivatives.", none, none⟩
        else none
      | _ => none },
  rule "diff.constant" fun (body, x) =>
    if !body.dependsOn x then
      some ⟨Expr.zero, s!"${body.toText}$ does not depend on ${x}$, so its derivative is 0: constants have zero rate of change.", none, none⟩
    else none,
  rule "diff.variable" fun (body, x) =>
    match body with
    | .var y => if y == x then some ⟨Expr.one, s!"$\\frac\{d}\{d{x}} {x} = 1$: the identity function has slope 1 everywhere.", none, none⟩ else none
    | _ => none,
  rule "diff.sum" fun (body, x) =>
    match body with
    | .add es => some ⟨.add (es.map (D · x)), "Sum rule: the derivative of a sum is the sum of the derivatives (differentiation is linear).", none, none⟩
    | _ => none,
  rule "diff.constant-multiple" fun (body, x) =>
    match body with
    | .mul es =>
      let consts := es.filter (fun a => !a.dependsOn x)
      let rest := es.filter (fun a => a.dependsOn x)
      if consts.isEmpty || rest.isEmpty then none
      else some ⟨.mul (consts ++ [D (mulN rest) x]),
        s!"Constant multiple rule: factors independent of ${x}$ (here ${(mulN consts).toText}$) pull out of the derivative.", none, none⟩
    | _ => none,
  rule "diff.product" fun (body, x) =>
    match body with
    | .mul fs =>
      let terms := (List.range fs.length).map fun i =>
        .mul (D (fs.getD i Expr.zero) x :: (fs.zipIdx.filter (·.2 != i)).map (·.1))
      let expl := match fs with
        | [f, g] => s!"Product rule: $(fg)' = f'g + fg'$ with $f = {f.toText}$ and $g = {g.toText}$."
        | _ => s!"Product rule for {fs.length} factors: differentiate each factor in turn, holding the others fixed, and add."
      some ⟨.add terms, expl, none, none⟩
    | _ => none,
  rule "diff.power" fun (body, x) =>
    match body with
    | .pow base exp =>
      let baseDep := base.dependsOn x
      let expDep := exp.dependsOn x
      if baseDep && !expDep then
        let nMinus1 := Expr.add [exp, Expr.minusOne]
        match base with
        | .var y => if y == x
            then some ⟨.mul [exp, .pow base nMinus1], s!"Power rule: $\\frac\{d}\{d{x}} {x}^n = n\\,{x}^\{n-1}$ with $n = {exp.toText}$.", none, none⟩
            else some ⟨.mul [exp, .pow base nMinus1, D base x], s!"Power rule with the chain rule: $(u^n)' = n u^\{n-1} u'$ where $u = {base.toText}$.", none, none⟩
        | _ => some ⟨.mul [exp, .pow base nMinus1, D base x], s!"Power rule with the chain rule: $(u^n)' = n u^\{n-1} u'$ where $u = {base.toText}$.", none, none⟩
      else if !baseDep && expDep then
        some ⟨.mul [body, .fn "ln" [base], D exp x], s!"Exponential rule with the chain rule: $(b^u)' = b^u \\ln b \\cdot u'$ where $u = {exp.toText}$.", none, none⟩
      else if baseDep && expDep then
        some ⟨.mul [body, .add [.mul [D exp x, .fn "ln" [base]], .mul [exp, Expr.div (D base x) base]]],
          s!"Both base and exponent depend on ${x}$: write $f^g = e^\{g \\ln f}$ and differentiate, giving $f^g\\left(g' \\ln f + g \\frac\{f'}\{f}\\right)$.", none, none⟩
      else none
    | _ => none,
  rule "diff.chain" fun (body, x) =>
    match body with
    | .fn f [u] =>
      let outer : Option (Expr × String) := match f with
        | "sin" => some (.fn "cos" [u], "\\sin' = \\cos")
        | "cos" => some (Expr.neg (.fn "sin" [u]), "\\cos' = -\\sin")
        | "tan" => some (.pow (.fn "cos" [u]) (Expr.ofInt (-2)), "\\tan' = \\sec^2 = 1/\\cos^2")
        | "exp" => some (.fn "exp" [u], "\\exp' = \\exp")
        | "ln" => some (.pow u Expr.minusOne, "\\ln' u = 1/u")
        | _ => none
      match outer with
      | some (fprime, law) =>
        let inner := match u with | .var y => if y == x then [] else [D u x] | _ => [D u x]
        some ⟨.mul (fprime :: inner),
          if inner.isEmpty then s!"${law}$." else s!"Chain rule: $(f(u))' = f'(u)\\,u'$ with ${law}$ and $u = {u.toText}$.", none, none⟩
      | none => none
    | _ => none,
  rule "diff.matrix" fun (body, x) =>
    match body with
    | .matrix rows => some ⟨.matrix (rows.map (·.map (D · x))), "Differentiate a matrix entrywise.", none, none⟩
    | _ => none
]

def diffRules : List PlainRule := rules

end MathEngine
