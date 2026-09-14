import MathEngine.SimpRules
import MathEngine.DiffRules
import MathEngine.LinAlg
import MathEngine.ExpandRules
import MathEngine.Numeric
import MathEngine.Terminate
/-!
# The notebook pipeline: commands as rules, and the combined rule set

Notebook commands are rules too: they fire on `fn` nodes with reserved names (`cmdNames`). Every
such node either evaluates or refuses, so a normal form never contains one — the fact the
termination proof (`PipelineOrder.lean`) needs about the command tier.

`pipelineRules` is what a cell is normalized with, under `normalizeT` (Terminate.lean): innermost,
with the tiered ordering of `Order.lean`, no step budget. Only the `expand` command's nested set
still runs on `normalizeFuel` (book/TRACKING.md, M5 decision).
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

def maxSteps : Nat := 10000

/-- In the pipeline, a scalar rule leaves nodes with a matrix literal among their children to the
matrix rules (which evaluate or refuse every such node), so its termination proof only has to
consider literal-free nodes. -/
def scalarOnly (r : PlainRule) : PlainRule :=
  { r with apply := fun e => if (children e).any isMatrix then none else r.apply e }

def simpPlain : List PlainRule := simpRules.map fun r => scalarOnly r.toPlain
def parityPlain : List PlainRule := parityRules.map scalarOnly
def expandSet : List PlainRule := expandRules ++ simpPlain ++ parityRules

/-- Notebook commands: `simplify`, `expand`, `rref`, `N`, `subst`. -/
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
        match nested expandSet maxSteps a with
        | .ok (out, sub) => some ⟨out, "Expand products and powers of sums by repeated distribution.", sub, none⟩
        | .error msg => some ⟨a, "", none, some msg⟩
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

def commandRules : List PlainRule := [cmdSimplify, cmdExpand, cmdRref, cmdN, cmdSubst]

/-- The matrix rules precede `simp` as in the reference (so `A·A` is a product, not `A^2`); the
catch-all `la.context` must come after every rule that handles a literal, so it is last. -/
def pipelineRules : List PlainRule := commandRules ++ diffRules ++ matrixRules ++ simpPlain ++ parityPlain ++ contextRules


end MathEngine
