import MathEngine.SimpRules
import MathEngine.DiffRules
import MathEngine.LinAlg
import MathEngine.ExpandRules
import MathEngine.Numeric
import MathEngine.Fourier
import MathEngine.Antiderivative
import MathEngine.RadicalRules
import MathEngine.ComplexRules
import MathEngine.Terminate
/-!
# The notebook pipeline: commands as rules, and the combined rule set

Notebook commands are rules too: they fire on `fn` nodes with reserved names (`cmdNames`). Every
such node either evaluates or refuses, so a normal form never contains one — the fact the
termination proof (`PipelineOrder.lean`) needs about the command tier.

`pipelineRulesWith norm` is what a cell is normalized with, under `normalizeT` (Terminate.lean):
innermost, with the tiered ordering of `Order.lean`, no step budget anywhere (`expand` distributes
by a total function and lets the pipeline collect the result).

The parameter `norm` is the normalizer the `integrate` command checks its candidates with. It cannot
be the pipeline itself (the pipeline is being defined), so `Integrate.lean` closes the knot after the
termination proof: the checker is the pipeline with nested `integrate` refused, and `pipelineRules`
is the pipeline with that checker.
-/
namespace MathEngine
open Expr


/-- Commands delegate to unverified subsystems (the fuel-based expand set, elimination, floating
point, substitution). The termination proof (`PipelineOrder.lean`) needs only that a command's output
contains no command node, so that is checked at run time rather than proved about each subsystem. -/
def checked (r : RuleResult) : RuleResult :=
  if r.error.isSome then r
  else if cmdCount r.result = 0 then r
  else refuse "a command produced a term that still contains a command"

/-- In the pipeline, a scalar rule leaves nodes with a matrix literal among their children to the
matrix rules (which evaluate or refuse every such node), so its termination proof only has to
consider literal-free nodes. -/
def scalarOnly (r : PlainRule) : PlainRule :=
  { r with apply := fun e => if (children e).any isMatrix then none else r.apply e }

def simpPlain : List PlainRule := simpRules.map fun r => scalarOnly r.toPlain
def parityPlain : List PlainRule := parityRules.map scalarOnly
def radicalPlain : List PlainRule := radicalRules.map scalarOnly
def complexPlain : List PlainRule := complexRules.map scalarOnly

/-- Notebook commands: `simplify`, `expand`, `rref`, `N`, `subst`, `integrate`, `sum`, `exptotrig`. -/
def cmdSimplify : PlainRule :=
  { name := "cmd.simplify", apply := fun e => Option.map checked <|
      match e with
      | .fn "simplify" [a] => some ⟨a, "Arguments are already in simplified normal form.", none, none⟩
      | .fn "simplify" _ => some (refuse "simplify takes one argument")
      | _ => none }

def cmdExpand : PlainRule :=
  { name := "cmd.expand", apply := fun e => Option.map checked <|
      match e with
      | .fn "expand" [a] =>
        let out := Expand.dist a
        let steps := Expand.steps a
        some ⟨out, "Expand products and powers of sums by distribution; the pipeline collects the result.",
          if steps.isEmpty then none else some ⟨a, steps, out⟩, none⟩
      | .fn "expand" _ => some (refuse "expand takes one argument")
      | _ => none }

def cmdRref : PlainRule :=
  { name := "cmd.rref", apply := fun e => Option.map checked <|
      match e with
      | .fn "rref" [.matrix rows] =>
        match rref rows with
        | .ok (out, steps) =>
          some ⟨out, "Gauss–Jordan elimination to reduced row echelon form.",
            if steps.isEmpty then none else some ⟨.matrix rows, steps, out⟩, none⟩
        | .error msg => some (refuse msg)
      | .fn "rref" _ => some (refuse "rref takes one matrix")
      | _ => none }

def cmdN : PlainRule :=
  { name := "cmd.N", apply := fun e => Option.map checked <|
      match e with
      | .fn "N" [a] =>
        -- over ℝ unless the term mentions `i` or has no finite real value (sqrt(−1), ln(−1)): then over ℂ
        let real := evalNumeric [] a >>= floatToExpr
        match (if mentionsI a || real.toOption.isNone then evalNumericC [] a >>= cfToExpr else real) with
        | .ok v => some ⟨v, "Numerical approximation in IEEE-754 double precision.", none, none⟩
        | .error msg => some ⟨a, "", none, some msg⟩
      | .fn "N" _ => some (refuse "N takes one argument")
      | _ => none }

def cmdSubst : PlainRule :=
  { name := "cmd.subst", apply := fun e => Option.map checked <|
      match e with
      | .fn "subst" [body, .var x, v] => some ⟨substitute [(x, v)] body, s!"Substitute ${x} := {v.toText}$.", none, none⟩
      | .fn "subst" _ => some (refuse "subst takes (expression, variable, value)")
      | _ => none }

/-- `sum(f, k, a, b)` for integer numerals `a ≤ b`: the terms `f[k := a] + … + f[k := b]`, which the
pipeline then collects. A definition, not a theorem: `cmdSum_spec` says the result is exactly that
list of substitutions, and `sum_soundR` reads it as a finite sum over ℝ. -/
def sumTerms (f : Expr) (k : String) (a b : Int) : List Expr :=
  (List.range (b - a + 1).toNat).map fun (j : Nat) => substVar k (.num (Q.ofInt (a + j))) f

def cmdSum : PlainRule :=
  { name := "cmd.sum", apply := fun e => Option.map checked <|
      match e with
      | .fn "sum" [f, .var k, .num a, .num b] =>
        if !a.isInt || !b.isInt then some (refuse "sum: the bounds must be integers")
        else if b.val.num < a.val.num then some (refuse "sum: the upper bound is below the lower bound (an empty sum is 0; write 0)")
        else if b.val.num - a.val.num > 1000 then some (refuse "sum: at most 1001 terms")
        else some ⟨addN (sumTerms f k a.val.num b.val.num),
          s!"$\\sum_\{{k}={a.toText}}^\{{b.toText}}$: one term per integer value of ${k}$, substituted.", none, none⟩
      | .fn "sum" [_, .var _, _, _] => some (refuse "sum: the bounds must be integer numerals")
      | .fn "sum" _ => some (refuse "sum takes (term, variable, from, to)")
      | _ => none }

/-- `exptotrig(e)`: Euler's formula applied to every `exp(θ·i)` at once (`expToTrig`), then the
pipeline collects. The general formula duplicates θ, so it cannot be a simplification rule; as a
command it runs once. Proved sound over ℂ (`expToTrig_soundC`). -/
def cmdExpToTrig : PlainRule :=
  { name := "cmd.exptotrig", apply := fun e => Option.map checked <|
      match e with
      | .fn "exptotrig" [a] => some ⟨expToTrig a, "Euler's formula $e^{i\\theta} = \\cos\\theta + i\\sin\\theta$, applied to every exponential with a pure-imaginary argument.", none, none⟩
      | .fn "exptotrig" _ => some (refuse "exptotrig takes one argument")
      | _ => none }

/-- A normalizer with its derivation, as the `integrate` command needs one. -/
abbrev Norm := Expr → Except String (Expr × Option Derivation)

/-! `integrate(f, x)`: a candidate from the unverified finder (`Antiderivative.lean`), normalized,
then accepted only if its derivative and the integrand have the same normal form *after
distribution*: `norm (dist (identNorm (norm (diff F x)))) = norm (dist (identNorm f))`. Distribution is there because the
pipeline never distributes a numeral over a sum (the ordering forbids it), so `-(a + b) + b` is a
normal form; `Expand.dist` is proved sound, so expanding both sides first weakens nothing. The
claim is `cmdIntegrate_spec` (Integrate.lean); the finder's steps are the sub-derivation, ending
with the `int.check` step that carries the differentiation and the `int.compare` step.

The four-argument form `integrate(f, x, a, b)` is the definite integral: the same checked
antiderivative, evaluated at the bounds (`definite`, the fundamental theorem of calculus; its
reading over ℝ is `integrate_definite` in the proofs). -/
/-- The antiderivative search and check shared by the two forms of `integrate`: the accepted
candidate `F` with the finder's steps, `int.check` and `int.compare`, or the refusal. -/
def findAnti (norm : Norm) (f : Expr) (x : String) : Except RuleResult (Expr × Array Step) :=
  match Anti.anti (fun e => (norm e).toOption.map (·.1)) x 3 f with
  | none => .error (refuse s!"integrate: no antiderivative of {f.toText} found by the available rules (sums, constant factors, powers, the elementary table, linear substitution, u-substitution, integration by parts)")
  | some (F₀, steps) =>
    match norm F₀ with
    | .error msg => .error (refuse s!"integrate: the candidate {F₀.toText} could not be simplified: {msg}")
    | .ok (F, _) =>
      match norm (D F x) with
      | .error msg => .error (refuse s!"integrate: the candidate {F.toText} could not be differentiated: {msg}")
      | .ok (g, sub) =>
        match norm (Expand.dist (Expand.identNorm g)), norm (Expand.dist (Expand.identNorm f)) with
        | .ok (g', subg), .ok (f', _) =>
          if equal g' f' then
            let check : Step := ⟨"int.check", s!"Check: $\\frac\{d}\{d{x}}$ of the candidate, simplified. This step carries the claim; the finder's steps above are unverified guesses.", [], D F x, g, sub⟩
            let compare : Step := ⟨"int.compare", s!"Both the derivative and the integrand are rewritten with $\\cos^2 u = 1 - \\sin^2 u$ and $(e^u)^k = e^\{ku}$ (`Expand.identNorm`), expanded (`Expand.dist`) and simplified — the two rewrites are proved sound — and they agree: ${f'.toText}$. The candidate is accepted.", [], g, g', subg⟩
            .ok (F, (steps.push check).push compare)
          else .error (refuse s!"integrate: the candidate {F.toText} was rejected: its derivative simplifies to {g.toText}, not to {f.toText}")
        | _, _ => .error (refuse s!"integrate: the candidate {F.toText} could not be compared with the integrand")

/-- The definite integral's value from an accepted antiderivative: `F[x := b] − F[x := a]`. -/
def definite (F : Expr) (x : String) (a b : Expr) : Expr := Expr.sub (substVar x b F) (substVar x a F)

def cmdIntegrate (norm : Norm) : PlainRule :=
  { name := "cmd.integrate", apply := fun e => Option.map checked <|
      match e with
      | .fn "integrate" [f, .var x] =>
        match findAnti norm f x with
        | .error r => some r
        | .ok (F, steps) =>
          some ⟨F, "Antiderivative found by the integration rules and accepted because its derivative simplifies back to the integrand (no constant of integration).", some ⟨Anti.integral f x, steps, F⟩, none⟩
      | .fn "integrate" [f, .var x, a, b] =>
        if (freeVars a).contains x || (freeVars b).contains x then some (refuse s!"integrate: the bounds may not mention the variable {x}")
        else match findAnti norm f x with
        | .error r => some r
        | .ok (F, steps) =>
          let out := definite F x a b
          let bounds : Step := ⟨"int.bounds", s!"The fundamental theorem of calculus: $\\int_a^b f = F(b) - F(a)$ for the antiderivative $F$ just checked, so the value is $F$ at ${b.toText}$ minus $F$ at ${a.toText}$; the pipeline simplifies it.", [], F, out, none⟩
          some ⟨out, "Definite integral: the checked antiderivative evaluated at the bounds.", some ⟨.fn "integrate" [f, .var x, a, b], steps.push bounds, out⟩, none⟩
      | .fn "integrate" [_, _] | .fn "integrate" [_, _, _, _] => some (refuse "integrate: the second argument must be a variable")
      | .fn "integrate" _ => some (refuse "integrate takes an integrand and a variable, optionally with the bounds: integrate(f, x, a, b)")
      | _ => none }

def commandRulesWith (norm : Norm) : List PlainRule := [cmdSimplify, cmdExpand, cmdRref, cmdN, cmdSubst, cmdIntegrate norm, cmdSum, cmdExpToTrig]

/-- The matrix rules precede `simp` as in the reference (so `A·A` is a product, not `A^2`); the
catch-all `la.context` must come after every rule that handles a literal, so it is last. -/
def pipelineRulesWith (norm : Norm) : List PlainRule := commandRulesWith norm ++ diffRules ++ matrixRules ++ complexPlain ++ simpPlain ++ parityPlain ++ radicalPlain ++ contextRules


end MathEngine
