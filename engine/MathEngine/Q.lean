/-!
# Exact rationals with an "approximate" flag

`Q` wraps core's `Rat` (always normalized: `den > 0`, `gcd num den = 1`) and adds the
Mathematica-style flag from `rational.ts`: decimal literals and `N(...)` produce approximate
numbers, which print as decimals; exact ones print as fractions. The flag is contagious
through arithmetic. Semantics (`Semantics.lean`) ignores the flag — it is a printing hint.
-/
namespace MathEngine

structure Q where
  val : Rat
  approx : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Q

def ofInt (n : Int) : Q := ⟨Rat.ofInt n, false⟩
def ofRat (r : Rat) (approx := false) : Q := ⟨r, approx⟩
instance : OfNat Q n := ⟨ofInt n⟩
def zero : Q := ofInt 0
def one : Q := ofInt 1
def minusOne : Q := ofInt (-1)

def isZero (q : Q) : Bool := q.val == 0
def isOne (q : Q) : Bool := q.val == 1
def isInt (q : Q) : Bool := q.val.den == 1
def isNeg (q : Q) : Bool := q.val.num < 0
/-- Structural equality ignoring the approximate flag, like `Rational.eq` in the reference. -/
def eq (a b : Q) : Bool := a.val == b.val
def cmp (a b : Q) : Ordering := compare (a.val.num * b.val.den) (b.val.num * a.val.den)

def add (a b : Q) : Q := ⟨a.val + b.val, a.approx || b.approx⟩
def mul (a b : Q) : Q := ⟨a.val * b.val, a.approx || b.approx⟩
def neg (a : Q) : Q := ⟨-a.val, a.approx⟩
def sub (a b : Q) : Q := a.add b.neg
def inv (a : Q) : Q := ⟨a.val.inv, a.approx⟩
def div (a b : Q) : Q := ⟨a.val / b.val, a.approx || b.approx⟩
def abs (a : Q) : Q := ⟨a.val.abs, a.approx⟩
/-- `q ^ n` for an integer exponent (negative exponents invert). -/
def zpow (a : Q) (n : Int) : Q := ⟨a.val ^ n, a.approx⟩
def withApprox (a : Q) (approx : Bool) : Q := { a with approx }

instance : Add Q := ⟨add⟩
instance : Mul Q := ⟨mul⟩
instance : Neg Q := ⟨neg⟩
instance : Sub Q := ⟨sub⟩
instance : Div Q := ⟨div⟩
instance : BEq Q := ⟨fun a b => a.val == b.val && a.approx == b.approx⟩

/-- Parse a numeric literal: `"3"`, `"2.5"`, `".5"`, `"1/3"`. Decimal literals are stored exactly
(`2.5 = 5/2`) but flagged approximate. Returns `none` on malformed input. -/
def parse (s : String) : Option Q := do
  let digits (t : String) : Option Nat := if t.isEmpty || !t.all Char.isDigit then none else t.toNat?
  match s.splitOn "/" with
  | [n, d] => do let n ← digits n; let d ← digits d; if d = 0 then none else some (ofRat (mkRat n d))
  | [_] =>
    match s.splitOn "." with
    | [i] => do let n ← digits i; some (ofInt n)
    | [i, f] => do
      let ip ← if i.isEmpty then some 0 else digits i
      let fp ← digits f
      let scale : Nat := 10 ^ f.length
      some (ofRat (mkRat (Int.ofNat (ip * scale + fp)) scale) true)
    | _ => none
  | _ => none

/-- `|q|` as `n × 10^(-k)` with exactly `p` significant digits in `n` (0 ↦ (0, 0)). -/
private def sigDigits (a : Rat) (p : Nat) : Nat × Int := Id.run do
  if a == 0 then return (0, 0)
  let tenPow (k : Int) : Rat := (10 : Rat) ^ k
  -- decimal exponent E of the leading digit: 10^E ≤ a < 10^(E+1)
  let mut e : Int := 0
  let ip := a.floor.toNat
  if ip > 0 then
    e := (toString ip).length - 1
  else
    -- a < 1: count leading zeros after the point (bounded search)
    let mut j : Nat := 1
    while j < 400 && a * tenPow j < 1 do j := j + 1
    e := -j
  let k : Int := (p : Int) - 1 - e
  let scaled := a * tenPow k + mkRat 1 2
  let mut n := scaled.floor.toNat
  let mut k' := k
  if n ≥ 10 ^ p then
    n := n / 10
    k' := k - 1
  return (n, k')

/-- Decimal expansion to 15 significant digits, formatted like JavaScript's
`Number.prototype.toPrecision(15)` with trailing zeros trimmed in positional notation
(the reference engine's `Rational.decimal`). -/
def toDecimal (q : Q) (p : Nat := 15) : String :=
  let a := q.val.abs
  let sign := if q.isNeg then "-" else ""
  if a == 0 then "0" else
  let (n, k) := sigDigits a p
  let digits := (toString n).toList  -- exactly p digits
  let str (l : List Char) : String := String.ofList l
  let e : Int := (p : Int) - 1 - k   -- exponent of the leading digit
  let trimFrac (s : String) : String :=
    let s := (s.toList.reverse.dropWhile (· == '0')).reverse
    String.ofList s
  let body :=
    if e < -6 || e ≥ (p : Int) then
      let mant := str (digits.take 1) ++ "." ++ str (digits.drop 1)
      mant ++ "e" ++ (if e < 0 then "-" else "+") ++ toString e.natAbs
    else if e ≥ 0 then
      let ipLen := e.toNat + 1
      let ip := str (digits.take ipLen)
      let fp := trimFrac (str (digits.drop ipLen))
      if fp.isEmpty then ip else ip ++ "." ++ fp
    else
      let zeros := String.ofList (List.replicate (e.natAbs - 1) '0')
      "0." ++ zeros ++ trimFrac (str digits)
  sign ++ body

def toText (q : Q) : String :=
  if q.approx then q.toDecimal
  else if q.isInt then toString q.val.num
  else s!"{q.val.num}/{q.val.den}"

def toLatex (q : Q) : String :=
  if q.isInt then toString q.val.num
  else if q.approx then q.toDecimal
  else
    let sign := if q.isNeg then "-" else ""
    s!"{sign}\\frac\{{q.val.num.natAbs}}\{{q.val.den}}"

instance : ToString Q := ⟨toText⟩

end Q
end MathEngine
