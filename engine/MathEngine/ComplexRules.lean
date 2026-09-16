import MathEngine.RadicalRules
/-!
# `cx.*` — complex numbers

`i` and `π` are constants (0-ary function nodes `fn "i" []`, `fn "π" []`), so they have no binding
and both semantics read them: `π` is `Real.pi` over ℝ, and over ℂ (`proofs/Proofs/Cx.lean`) `i` is
`Complex.I`. The rules here are the arithmetic of Gaussian rationals `a + b·i` — products, integer
powers and inverses (`1/(a + bi) = (a − bi)/(a² + b²)`), conjugate, real and imaginary parts, the
modulus — the powers of `i`, the exact values of sine, cosine and tangent at rational multiples of
π (which are what make Euler's identity compute), and Euler's formula `exp(iθ) = cos θ + i sin θ`
where the two trigonometric values are exact, so `ℯ^(πi)` becomes `−1` and `ℯ^(iπ/4)` becomes
`√2/2 + (√2/2) i`. Each rule guards itself with the decrease of `M` its termination proof needs
(never false in practice), like the radical rules.

What is proved: over ℝ, the exact trigonometric values (`exactTrig_soundR`) and `ℯ^b = exp b`;
over ℂ, every rule of this file (`proofs/Proofs/Cx.lean`). A term containing `i` has no real
meaning, so the notebook reads such a cell in the complex semantics and reports each rule's
status over ℂ.
-/
namespace MathEngine
open Expr

def iE : Expr := .fn "i" []
def piE : Expr := .fn "π" []
def isI : Expr → Bool | .fn f [] => f == "i" | _ => false
def isPi : Expr → Bool | .fn f [] => f == "π" | _ => false

mutual
  /-- Does `i` occur anywhere? Decides which semantics a cell is read in. -/
  def mentionsI : Expr → Bool
    | .fn "i" [] => true
    | .num _ | .var _ => false
    | .add es | .mul es | .fn _ es => mentionsIList es
    | .pow b e => mentionsI b || mentionsI e
    | .matrix rows => mentionsIRows rows
  def mentionsIList : List Expr → Bool
    | [] => false
    | e :: es => mentionsI e || mentionsIList es
  def mentionsIRows : List (List Expr) → Bool
    | [] => false
    | r :: rs => mentionsIList r || mentionsIRows rs
end

/-! ## Gaussian rationals -/

/-- `re + im·i` with rational parts. -/
structure Gauss where
  re : Q
  im : Q
  deriving Repr

namespace Gauss
def zero : Gauss := ⟨Q.zero, Q.zero⟩
def one : Gauss := ⟨Q.one, Q.zero⟩
def I : Gauss := ⟨Q.zero, Q.one⟩
def isReal (g : Gauss) : Bool := g.im.isZero
def add (a b : Gauss) : Gauss := ⟨a.re + b.re, a.im + b.im⟩
def mul (a b : Gauss) : Gauss := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def conj (a : Gauss) : Gauss := ⟨a.re, a.im.neg⟩
/-- `|a|²`, a rational. -/
def normSq (a : Gauss) : Q := a.re * a.re + a.im * a.im
/-- `1/a = ā/|a|²` (`a ≠ 0`; the inverse of 0 is 0, as in Mathlib). -/
def inv (a : Gauss) : Gauss :=
  let n := a.normSq
  if n.isZero then zero else ⟨a.re / n, a.im.neg / n⟩
def pow (a : Gauss) : Nat → Gauss
  | 0 => one
  | n + 1 => mul (pow a n) a
def zpow (a : Gauss) (n : Int) : Gauss := if n ≥ 0 then pow a n.toNat else pow (inv a) (-n).toNat
end Gauss

/-- A numeral, `i`, or `q·i`. -/
def gaussAtom : Expr → Option Gauss
  | .num q => some ⟨q, Q.zero⟩
  | .fn "i" [] => some Gauss.I
  | .mul [.num q, .fn "i" []] => some ⟨Q.zero, q⟩
  | .mul [.fn "i" [], .num q] => some ⟨Q.zero, q⟩
  | _ => none

/-- A Gaussian rational as the engine writes it: an atom or a sum of atoms. -/
def gauss? : Expr → Option Gauss
  | .add es => es.foldlM (fun acc e => (gaussAtom e).map (Gauss.add acc)) Gauss.zero
  | e => gaussAtom e

/-- `q·i` in the engine's normal form: `i`, `−i`, or `q·i`. -/
def imE (q : Q) : Expr :=
  if q.isOne then iE
  else if q.eq Q.minusOne then .mul [Expr.minusOne, iE]
  else .mul [.num q, iE]

/-- The engine's normal form of `re + im·i`: a numeral, `i`, `−i`, `q·i`, or a two-term sum. -/
def gaussE (g : Gauss) : Expr :=
  if g.im.isZero then .num g.re else if g.re.isZero then imE g.im else .add [.num g.re, imE g.im]

/-! ## Exact trigonometric values at rational multiples of π -/

/-- `q` such that the argument is `q·π`: `π`, `q·π`, or `π·q`. -/
def trigArg : Expr → Option Q
  | .fn "π" [] => some Q.one
  | .mul [.num q, .fn "π" []] => some q
  | .mul [.fn "π" [], .num q] => some q
  | _ => none

/-- `c·√r` as a term, for `r ∈ {1, 2, 3}`. -/
def radE (c : Q) (r : Nat) : Expr :=
  if c.isZero then Expr.zero
  else if r = 1 then .num c
  else if c.isOne then .pow (.num (Q.ofInt r)) (.num (Q.ofRat (mkRat 1 2)))
  else .mul [.num c, .pow (.num (Q.ofInt r)) (.num (Q.ofRat (mkRat 1 2)))]

/-- `(sin, cos)` of `r·π` for `r ∈ {0, 1/6, 1/4, 1/3, 1/2}`, each as `(coefficient, radicand)`. -/
def refTable (r : Rat) : Option ((Rat × Nat) × (Rat × Nat)) :=
  if r = 0 then some ((0, 1), (1, 1))
  else if r = mkRat 1 6 then some ((mkRat 1 2, 1), (mkRat 1 2, 3))
  else if r = mkRat 1 4 then some ((mkRat 1 2, 2), (mkRat 1 2, 2))
  else if r = mkRat 1 3 then some ((mkRat 1 2, 3), (mkRat 1 2, 1))
  else if r = mkRat 1 2 then some ((1, 1), (0, 1))
  else none

/-- Reflection into `[0, 1/2]`: `sin(π − x) = sin x`, `cos(π − x) = −cos x`. -/
def reflect (r : Rat) : Option ((Rat × Nat) × (Rat × Nat)) :=
  if r > mkRat 1 2 then (refTable (1 - r)).map fun p => ((p.1.1, p.1.2), (-p.2.1, p.2.2)) else refTable r

/-- Half turn into `[0, 1)`: `sin(x + π) = −sin x`, `cos(x + π) = −cos x`. -/
def halfTurn (r : Rat) : Option ((Rat × Nat) × (Rat × Nat)) :=
  if r ≥ 1 then (reflect (r - 1)).map fun p => ((-p.1.1, p.1.2), (-p.2.1, p.2.2)) else reflect r

/-- `(sin, cos)` of `q·π` as `(coefficient, radicand)` pairs, when the value is exact: reduce by
the period into `[0, 2)`, then by the half turn, then by the reflection, down to a reference angle. -/
def sinCos (q : Rat) : Option ((Rat × Nat) × (Rat × Nat)) := halfTurn (q - 2 * (q / 2).floor)

/-- The exact value of `sin`, `cos` or `tan` at `q·π` as `(coefficient, radicand)`, if there is one. -/
def trigCoeff (f : String) (q : Q) : Option (Q × Nat) :=
  match sinCos q.val with
  | none => none
  | some ((sc, sr), (cc, cr)) =>
    if f == "sin" then some (Q.ofRat sc, sr)
    else if f == "cos" then some (Q.ofRat cc, cr)
    else if f == "tan" then
      if cc = 0 then none
      else if sr = cr then some (Q.ofRat (sc / cc), 1)
      else if sr = 3 then some (Q.ofRat (sc / cc), 3)
      else if cr = 3 then some (Q.ofRat (sc / cc / 3), 3)
      else none
    else none

/-- The exact value as a term. -/
def trigValue (f : String) (q : Q) : Option Expr := (trigCoeff f q).map fun p => radE p.1 p.2

/-! ## The rules -/

/-- Fire only if `M` decreases: the termination lemma is then a split on this guard. -/
def guarded (res : Expr) (e : Expr) (why : String) : Option RuleResult :=
  if M res < M e then some ⟨res, why, none, none⟩ else none

/-- `i^n` for an integer `n`: the powers of `i` cycle through `1, i, −1, −i`. -/
def iPower : PlainRule :=
  { name := "cx.i-power", apply := fun e =>
      match e with
      | .pow (.fn "i" []) (.num n) =>
        if n.isInt && (n.val.num ≥ 2 || n.val.num < 0) then
          let r := n.val.num % 4
          let g : Gauss := if r = 0 then Gauss.one else if r = 1 then Gauss.I else if r = 2 then ⟨Q.minusOne, Q.zero⟩ else ⟨Q.zero, Q.minusOne⟩
          guarded (gaussE g) e s!"$i^2 = -1$, so the powers of $i$ cycle: $i^\{{n.toText}} = {(gaussE g).toText}$."
        else none
      | _ => none }

/-- A factor of a product that is a Gaussian numeral or an integer power of one — an inverse,
`(a + bi)^(-1)`, in particular, which is how `1/(a + bi)` arrives. -/
def gaussFactor : Expr → Option Gauss
  | .pow b (.num n) => if n.isInt then (gauss? b).map fun g => g.zpow n.val.num else none
  | e => gauss? e

/-- Two Gaussian factors of a product, at least one not real, multiplied. -/
def gaussMul (a b : Expr) : Option Expr :=
  match gaussFactor a, gaussFactor b with
  | some x, some y => if x.isReal && y.isReal then none else some (gaussE (x.mul y))
  | _, _ => none

def cxArith : PlainRule :=
  { name := "cx.arithmetic", apply := fun e =>
      match e with
      | .mul es =>
        match findPair gaussMul es with
        | some (m, others) => guarded (mulN (m :: others)) e "$(a + bi)(c + di) = (ac - bd) + (ad + bc)\\,i$: complex numbers multiply by the distributive law and $i^2 = -1$."
        | none => none
      | _ => none }

/-- An integer power of a Gaussian numeral that is not real: repeated multiplication, and for a
negative exponent the inverse `1/(a + bi) = (a - bi)/(a^2 + b^2)` first. -/
def cxPow : PlainRule :=
  { name := "cx.power", apply := fun e =>
      match e with
      | .pow b (.num n) =>
        if n.isInt && n.val.num != 0 && n.val.num != 1 then
          match gauss? b with
          | some g => if g.isReal || isI b then none else
              guarded (gaussE (g.zpow n.val.num)) e (if n.val.num < 0
                then "$\\frac{1}{a + bi} = \\frac{a - bi}{a^2 + b^2}$: multiply numerator and denominator by the conjugate, then raise to the power."
                else "A power of a complex number: multiply out with $i^2 = -1$.")
          | none => none
        else none
      | _ => none }

def cxConj : PlainRule :=
  { name := "cx.conjugate", apply := fun e =>
      match e with
      | .fn "conj" [.fn "conj" [z]] => guarded z e "$\\overline{\\overline{z}} = z$."
      | .fn "conj" [z] =>
        match gauss? z with
        | some g => guarded (gaussE g.conj) e "$\\overline{a + bi} = a - bi$."
        | none => none
      | _ => none }

def cxReIm : PlainRule :=
  { name := "cx.re-im", apply := fun e =>
      match e with
      | .fn "re" [z] => match gauss? z with | some g => guarded (.num g.re) e "$\\operatorname{Re}(a + bi) = a$." | none => none
      | .fn "im" [z] => match gauss? z with | some g => guarded (.num g.im) e "$\\operatorname{Im}(a + bi) = b$." | none => none
      | _ => none }

def cxAbs : PlainRule :=
  { name := "cx.abs", apply := fun e =>
      match e with
      | .fn "abs" [z] =>
        match gauss? z with
        | some g => if g.isReal then none else
            guarded (.pow (.num g.normSq) (.num (Q.ofRat (mkRat 1 2)))) e "$|a + bi| = \\sqrt{a^2 + b^2}$."
        | none => none
      | _ => none }

/-- `sin`, `cos`, `tan` at a rational multiple of π with an exact value. -/
def exactTrig : PlainRule :=
  { name := "cx.exact-trig", apply := fun e =>
      match e with
      | .fn f [a] =>
        if f == "sin" || f == "cos" || f == "tan" then
          match trigArg a with
          | some q =>
            match trigValue f q with
            | some v => guarded v e s!"Exact value on the unit circle: $\\{f}({a.toText}) = {v.toText}$, by the period $2\\pi$, the reflections $\\sin(\\pi - x) = \\sin x$, $\\cos(\\pi - x) = -\\cos x$, $\\sin(x + \\pi) = -\\sin x$, and the reference angles $0, \\pi/6, \\pi/4, \\pi/3, \\pi/2$."
            | none => none
          | none => none
        else none
      | _ => none }

/-- The factors of `θ·i` other than `i`, as `θ`, when exactly one factor is `i`. -/
def imagArg : Expr → Option Expr
  | .fn "i" [] => some Expr.one
  | .mul fs => if (fs.filter isI).length == 1 then some (mulN (fs.filter (fun f => !isI f))) else none
  | _ => none

/-- `−θ` written as `θ` negated: a negative numeral, or a product led by one, gives the
positive counterpart; anything else is `none`. -/
def negOf : Expr → Option Expr
  | .num q => if q.isNeg then some (.num (Q.zero - q)) else none
  | .mul (.num q :: rest) => if q.isNeg then some (mulN (if (Q.zero - q).isOne then rest else .num (Q.zero - q) :: rest)) else none
  | _ => none

mutual
  /-- Euler's formula applied everywhere at once, as the `exptotrig` command does it: every
  `exp(u)` with a pure-imaginary argument `u = θ·i` becomes `cos θ + sin θ · i`. The general
  rewrite duplicates `θ`, which the ordering cannot pay for as a simplification rule; as a command
  it runs once, and the pipeline collects what it leaves. -/
  def expToTrig : Expr → Expr
    | .num q => .num q
    | .var x => .var x
    | .add es => .add (expToTrigList es)
    | .mul es => .mul (expToTrigList es)
    | .pow b e => .pow (expToTrig b) (expToTrig e)
    | .fn f es =>
      match f, expToTrigList es with
      | "exp", [u] =>
        match imagArg u with
        | some θ =>
          -- a negated angle: cos(−θ) = cos θ and sin(−θ) = −sin θ, applied here because the
          -- pipeline cannot afford `sin(−θ) → −sin θ` (a tie in every tier of the ordering)
          match negOf θ with
          | some θ' => .add [.fn "cos" [θ'], .mul [Expr.minusOne, .fn "sin" [θ'], iE]]
          | none => .add [.fn "cos" [θ], .mul [.fn "sin" [θ], iE]]
        | none => .fn "exp" [u]
      | f', es' => .fn f' es'
    | .matrix rows => .matrix (expToTrigRows rows)
  def expToTrigList : List Expr → List Expr
    | [] => []
    | e :: es => expToTrig e :: expToTrigList es
  def expToTrigRows : List (List Expr) → List (List Expr)
    | [] => []
    | r :: rs => expToTrigList r :: expToTrigRows rs
end

/-- `s·i` in normal form: nothing, `i`, or the factors of `s` with `i` appended. -/
def imagOf (s : Expr) : Expr := if s.isZero then Expr.zero else if s.isOne then iE else mulN (unMul s ++ [iE])

/-- `c + s·i` from the exact values, in the engine's normal form. -/
def eulerValue (c s : Expr) : Expr :=
  if ([c, imagOf s].filter (fun t => !t.isZero)).isEmpty then Expr.zero
  else addN ([c, imagOf s].filter (fun t => !t.isZero))

/-- Euler's formula `exp(iθ) = cos θ + i sin θ`, applied where both values are exact. -/
def euler : PlainRule :=
  { name := "cx.euler", apply := fun e =>
      match e with
      | .fn "exp" [a] =>
        match imagArg a with
        | none => none
        | some θ =>
          match trigArg θ with
          | none => none
          | some q =>
            match trigValue "cos" q, trigValue "sin" q with
            | some c, some s => guarded (eulerValue c s) e s!"Euler's formula: $e^\{i\\theta} = \\cos\\theta + i\\sin\\theta$ with $\\theta = {θ.toText}$, and both values are exact."
            | _, _ => none
      | _ => none }

/-- `ℯ^b = exp(b)`: the constant `ℯ` is `exp(1)`, and `(e^1)^b = e^b`. -/
def eulerPower : PlainRule :=
  { name := "cx.euler-power", apply := fun e =>
      match e with
      | .pow (.fn "exp" [.num q]) b =>
        if q.isOne && !b.isNum then guarded (.fn "exp" [b]) e "$e^{b}$ is $\\exp(b)$: the constant $e$ is $\\exp(1)$ and $(e^1)^b = e^b$." else none
      | _ => none }

def complexRules : List PlainRule := [iPower, cxArith, cxPow, cxConj, cxReIm, cxAbs, exactTrig, euler, eulerPower]

end MathEngine
