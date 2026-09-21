import MathEngine.SimpRules
import MathEngine.ExpandRules
/-!
# `factor`: a sum as one fraction with its common factor pulled out

`factor(e)` expands and collects `e` (the pipeline's own steps), puts the resulting sum over a
common denominator (Mathematica's `Together`) and pulls the numerator's common factor out — the
shape a hand derivation ends in: `i(e^{-ikπ} + e^{ikπ} - 2)/(2kπ)` rather than the normal form's
`½·(−(i/k − i e^{ikπ}/k) − i/k + i e^{−ikπ}/k)/π`. It is a command, not a rule: the normal form is
what the rules produce, and this is one presentation of it. Unverified (see the ledger).

The bookkeeping is on *factors*: every term is a rational coefficient times bases with rational
exponents, positive ones in the numerator and negative ones (negated) in the denominator.
-/
namespace MathEngine
namespace Factor
open Expr

private def ratLt (a b : Rat) : Bool := (a - b).num < 0
private def ratMin (a b : Rat) : Rat := if ratLt a b then a else b
private def ratMax (a b : Rat) : Rat := if ratLt a b then b else a

/-- Bases with rational exponents, in first-seen order. -/
abbrev Factors := List (Expr × Rat)

def exponentOf (fs : Factors) (b : Expr) : Rat := ((fs.find? (·.1 == b)).map (·.2)).getD 0

/-- Add `q` to the exponent of `b`. -/
def addFactor (fs : Factors) (b : Expr) (q : Rat) : Factors :=
  if (fs.find? (·.1 == b)).isSome then fs.map fun (b', q') => if b' == b then (b', q' + q) else (b', q')
  else fs ++ [(b, q)]

/-- Raise the exponent of `b` to at least `q`. -/
def maxFactor (fs : Factors) (b : Expr) (q : Rat) : Factors :=
  if (fs.find? (·.1 == b)).isSome then fs.map fun (b', q') => if b' == b then (b', ratMax q' q) else (b', q')
  else fs ++ [(b, q)]

structure Term where
  coeff : Rat := 1
  num : Factors := []
  den : Factors := []

/-- A product's parts. -/
def termOf (t : Expr) : Term :=
  (unMul t).foldl (init := {}) fun acc f =>
    match f with
    | .num q => { acc with coeff := acc.coeff * q.val }
    | .pow b (.num q) =>
      if q.val.num < 0 then { acc with den := addFactor acc.den b (-q.val) }
      else { acc with num := addFactor acc.num b q.val }
    | _ => { acc with num := addFactor acc.num f 1 }

/-- `c · Π num · Π den⁻¹` as a product (the bare factor when there is one). -/
def ofParts (c : Rat) (num den : Factors) : Expr :=
  let pw (b : Expr) (q : Rat) : Expr := if q == 1 then b else .pow b (.num (Q.ofRat q))
  let fs := (if c == 1 then [] else [Expr.num (Q.ofRat c)]) ++ num.map (fun (b, q) => pw b q)
    ++ den.map (fun (b, q) => Expr.pow b (.num (Q.ofRat (-q))))
  match fs with
  | [] => Expr.one
  | fs => mulN fs

/-- The terms of a sum over a common denominator, with the numerator's common factor pulled out:
`g · Π common · (Σ rest) / D`. -/
def combine (terms : List Term) : Expr :=
  match terms with
  | [] => Expr.zero
  | _ =>
    -- the common denominator: the coefficients' denominators' lcm, and each base at its largest exponent
    let dnum : Nat := terms.foldl (fun acc t => Nat.lcm acc t.coeff.den) 1
    let dbases : Factors := terms.foldl (fun acc t => t.den.foldl (fun acc (b, q) => maxFactor acc b q) acc) []
    -- every term over D: an integer coefficient, and the denominator factors it lacks move up
    let lifted : List (Rat × Factors) := terms.map fun t =>
      let c := t.coeff * Rat.ofInt (Int.ofNat dnum)
      let up := dbases.filterMap fun (b, q) => let e := q - exponentOf t.den b; if ratLt 0 e then some (b, e) else none
      (c, up.foldl (fun acc (b, e) => addFactor acc b e) t.num)
    -- the common factor of the numerator's terms: the coefficients' gcd (negative when all are), each base at its least exponent
    let gnat := lifted.foldl (fun acc (c, _) => Nat.gcd acc c.num.natAbs) 0
    let g : Rat := Rat.ofInt (if lifted.all (fun (c, _) => c.num < 0) then -(Int.ofNat gnat) else Int.ofNat gnat)
    let gbases : Factors := match lifted with
      | [] => []
      | (_, fs) :: rest => fs.filterMap fun (b, q) =>
          let m := rest.foldl (fun acc (_, fs') => ratMin acc (exponentOf fs' b)) q
          if ratLt 0 m then some (b, m) else none
    let inner := addN (lifted.map fun (c, fs) =>
      ofParts (if g == 0 then c else c / g)
        (fs.filterMap fun (b, q) => let e := q - exponentOf gbases b; if ratLt 0 e then some (b, e) else none) [])
    let outer := ofParts (g / Rat.ofInt (Int.ofNat dnum)) gbases dbases
    if outer == Expr.one then inner else mulN (unMul outer ++ [inner])

/-- Expand and collect with the pipeline's normalizer, then combine. -/
def run (norm : Expr → Except String Expr) (a : Expr) : Except String Expr := do
  let e ← norm (Expand.dist a)
  pure (combine ((unAdd e).map termOf))

end Factor
end MathEngine
