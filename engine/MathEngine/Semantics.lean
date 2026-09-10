import MathEngine.Expr
/-!
# Denotational semantics (integer fragment, total)

`evalZ ρ e` gives the value of `e` in environment `ρ`. Nodes outside the fragment (non-integer
numerals, functions, matrices, non-natural exponents) evaluate to a junk value `0`, the same
convention Lean itself uses for `x / 0`. Junk-value semantics keeps every proof a plain
structural induction; M3 replaces `Int` with `ℝ` and the fragment with the full language.
-/
namespace MathEngine
open Expr

abbrev Env := String → Int

def Expr.asNat : Expr → Nat
  | .num ⟨n, 1⟩ => n.toNat
  | _ => 0

mutual
  def evalZ (ρ : Env) : Expr → Int
    | .num ⟨n, 1⟩ => n
    | .num _      => 0
    | .var x      => ρ x
    | .add es     => evalSum ρ es
    | .mul es     => evalProd ρ es
    | .pow b e    => (evalZ ρ b) ^ e.asNat
    | .fn _ _     => 0
    | .matrix _   => 0
  def evalSum (ρ : Env) : List Expr → Int
    | []      => 0
    | e :: es => evalZ ρ e + evalSum ρ es
  def evalProd (ρ : Env) : List Expr → Int
    | []      => 1
    | e :: es => evalZ ρ e * evalProd ρ es
end

/-- Semantic equality on the fragment: agreement in every environment. -/
def SemEq (a b : Expr) : Prop := ∀ ρ, evalZ ρ a = evalZ ρ b

end MathEngine
