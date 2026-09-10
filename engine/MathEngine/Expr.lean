/-!
# Expression syntax

Mirrors `packages/reference-ts/src/ast.ts` node for node; `Wire.lean` serializes to the
same JSON. No subtraction/division/negation constructors — fewer cases in every proof.
-/
namespace MathEngine

/-- Exact rationals as numerator/denominator. Normalization and arithmetic come in M1. -/
structure Q where
  num : Int
  den : Nat := 1
  deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | num    : Q → Expr
  | var    : String → Expr
  | add    : List Expr → Expr
  | mul    : List Expr → Expr
  | pow    : Expr → Expr → Expr
  | fn     : String → List Expr → Expr
  | matrix : List (List Expr) → Expr
  deriving Repr, Inhabited

end MathEngine
