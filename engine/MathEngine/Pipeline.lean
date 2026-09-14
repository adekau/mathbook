import MathEngine.SimpRules
import MathEngine.DiffRules
import MathEngine.LinAlg
import MathEngine.ExpandRules
import MathEngine.Numeric
import MathEngine.Antiderivative
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

/-- Notebook commands: `simplify`, `expand`, `rref`, `N`, `subst`, `integrate`. -/
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
        match evalNumeric [] a >>= floatToExpr with
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

/-- A normalizer with its derivation, as the `integrate` command needs one. -/
abbrev Norm := Expr → Except String (Expr × Option Derivation)

/-- `integrate(f, x)`: a candidate from the unverified finder (`Antiderivative.lean`), normalized,
then accepted only if its derivative and the integrand have the same normal form *after
distribution*: `norm (dist (norm (diff F x))) = norm (dist f)`. Distribution is there because the
pipeline never distributes a numeral over a sum (the ordering forbids it), so `-(a + b) + b` is a
normal form; `Expand.dist` is proved sound, so expanding both sides first weakens nothing. The
claim is `cmdIntegrate_spec` (Integrate.lean); the finder's steps are the sub-derivation, ending
with the `int.check` step that carries the differentiation and the `int.compare` step. -/
def cmdIntegrate (norm : Norm) : PlainRule :=
  { name := "cmd.integrate", apply := fun e => Option.map checked <|
      match e with
      | .fn "integrate" [f, .var x] =>
        match Anti.anti (fun e => (norm e).toOption.map (·.1)) x 3 f with
        | none => some (refuse s!"integrate: no antiderivative of {f.toText} found by the available rules (sums, constant factors, powers, the elementary table, linear substitution, u-substitution, integration by parts)")
        | some (F₀, steps) =>
          match norm F₀ with
          | .error msg => some (refuse s!"integrate: the candidate {F₀.toText} could not be simplified: {msg}")
          | .ok (F, _) =>
            match norm (D F x) with
            | .error msg => some (refuse s!"integrate: the candidate {F.toText} could not be differentiated: {msg}")
            | .ok (g, sub) =>
              match norm (Expand.dist g), norm (Expand.dist f) with
              | .ok (g', subg), .ok (f', _) =>
                if equal g' f' then
                  let check : Step := ⟨"int.check", s!"Check: $\\frac\{d}\{d{x}}$ of the candidate, simplified. This step carries the claim; the finder's steps above are unverified guesses.", [], D F x, g, sub⟩
                  let compare : Step := ⟨"int.compare", s!"Both the derivative and the integrand are expanded (`Expand.dist`, proved sound) and simplified; they agree: ${f'.toText}$. The candidate is accepted.", [], g, g', subg⟩
                  some ⟨F, "Antiderivative found by the integration rules and accepted because its derivative simplifies back to the integrand (no constant of integration).", some ⟨Anti.integral f x, (steps.push check).push compare, F⟩, none⟩
                else some (refuse s!"integrate: the candidate {F.toText} was rejected: its derivative simplifies to {g.toText}, not to {f.toText}")
              | _, _ => some (refuse s!"integrate: the candidate {F.toText} could not be compared with the integrand")
      | .fn "integrate" [_, _] => some (refuse "integrate: the second argument must be a variable")
      | .fn "integrate" _ => some (refuse "integrate takes an integrand and a variable")
      | _ => none }

def commandRulesWith (norm : Norm) : List PlainRule := [cmdSimplify, cmdExpand, cmdRref, cmdN, cmdSubst, cmdIntegrate norm]

/-- The matrix rules precede `simp` as in the reference (so `A·A` is a product, not `A^2`); the
catch-all `la.context` must come after every rule that handles a literal, so it is last. -/
def pipelineRulesWith (norm : Norm) : List PlainRule := commandRulesWith norm ++ diffRules ++ matrixRules ++ simpPlain ++ parityPlain ++ contextRules


end MathEngine
