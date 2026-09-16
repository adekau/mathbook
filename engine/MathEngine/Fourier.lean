import MathEngine.Numeric
import MathEngine.ComplexRules
import MathEngine.SimpRules
/-!
# Fourier presentation: complex numerics, epicycles, the DFT

Everything here is *presentation*, like `plot`'s sampling: floating point, unverified, and the
notebook says so. The exact mathematics lives in the rules (`integrate`, `sum`, `exptotrig`) and
their proofs.

* `CF` — a complex number as two `Float`s, with the arithmetic `evalNumericC` needs.
* `evalNumericC` — the numeric evaluator over ℂ: what `N` uses when the term mentions `i`, and
  what samples a complex-valued curve for `plot`.
* `fourierTerms` — reads a finite Fourier sum `Σ c_k · exp(i k t)` off a normalized term: the
  `(k, c_k)` pairs the epicycle animation rotates.
* `dft` — the discrete Fourier transform of sample points, `c_k = (1/N) Σ_j p_j e^{−2πi kj/N}`,
  the O(N²) form the article used.
-/
namespace MathEngine
open Expr

/-- A complex number in floating point. -/
structure CF where
  re : Float
  im : Float
  deriving Repr, Inhabited

namespace CF
def ofReal (x : Float) : CF := ⟨x, 0⟩
def zero : CF := ⟨0, 0⟩
def one : CF := ⟨1, 0⟩
def I : CF := ⟨0, 1⟩
def add (a b : CF) : CF := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : CF) : CF := ⟨a.re - b.re, a.im - b.im⟩
def mul (a b : CF) : CF := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def neg (a : CF) : CF := ⟨-a.re, -a.im⟩
def conj (a : CF) : CF := ⟨a.re, -a.im⟩
def normSq (a : CF) : Float := a.re * a.re + a.im * a.im
def abs (a : CF) : Float := Float.sqrt a.normSq
def arg (a : CF) : Float := Float.atan2 a.im a.re
def inv (a : CF) : CF := let n := a.normSq; ⟨a.re / n, -a.im / n⟩
def div (a b : CF) : CF := a.mul b.inv
/-- `e^{x+iy} = e^x (cos y + i sin y)`. -/
def exp (a : CF) : CF := let r := Float.exp a.re; ⟨r * Float.cos a.im, r * Float.sin a.im⟩
/-- `e^{iθ}` for a real θ. -/
def cis (θ : Float) : CF := ⟨Float.cos θ, Float.sin θ⟩
/-- The principal logarithm. -/
def log (a : CF) : CF := ⟨Float.log a.abs, a.arg⟩
/-- `sin z = (e^{iz} − e^{−iz}) / 2i`, `cos z = (e^{iz} + e^{−iz}) / 2`. -/
def sin (a : CF) : CF := ⟨Float.sin a.re * Float.cosh a.im, Float.cos a.re * Float.sinh a.im⟩
def cos (a : CF) : CF := ⟨Float.cos a.re * Float.cosh a.im, -(Float.sin a.re * Float.sinh a.im)⟩
def tan (a : CF) : CF := a.sin.div a.cos
/-- The principal square root, `√((|z|+re)/2) + i·sgn(im)·√((|z|−re)/2)`, so `√(−1)` is exactly `i`. -/
def sqrt (a : CF) : CF :=
  let r := a.abs
  let re := Float.sqrt ((r + a.re) / 2)
  let im := Float.sqrt ((r - a.re) / 2)
  ⟨re, if a.im < 0 then -im else im⟩
/-- `z^n` for a natural `n`, by squaring: exact where the arithmetic is. -/
def npow (a : CF) : Nat → CF
  | 0 => one
  | n + 1 => if (n + 1) % 2 == 0 then let h := npow a ((n + 1) / 2); h.mul h else a.mul (npow a n)
/-- The principal power `z^w = exp(w log z)`, except that an integer exponent multiplies out (so
`(1+2i)^2` is exactly `−3+4i`) and `0^w` is `0` for `w ≠ 0`. -/
def pow (a b : CF) : CF :=
  if a.re == 0 && a.im == 0 then (if b.re == 0 && b.im == 0 then one else zero)
  else if b.im == 0 && b.re == b.re.round && b.re.abs ≤ 1024 then
    let n := b.re.abs.toUInt64.toNat
    if b.re < 0 then (npow a n).inv else npow a n
  else if b.im == 0 && b.re == 0.5 then sqrt a
  else exp (b.mul a.log)
def isFinite (a : CF) : Bool := a.re.isFinite && a.im.isFinite
instance : Add CF := ⟨add⟩
instance : Mul CF := ⟨mul⟩
instance : Sub CF := ⟨sub⟩
instance : Neg CF := ⟨neg⟩
end CF

private def fnsC : List (String × (CF → CF)) :=
  [("sin", CF.sin), ("cos", CF.cos), ("tan", CF.tan), ("exp", CF.exp), ("ln", CF.log),
   ("sqrt", CF.sqrt), ("abs", fun z => CF.ofReal z.abs), ("conj", CF.conj),
   ("re", fun z => CF.ofReal z.re), ("im", fun z => CF.ofReal z.im),
   ("sign", fun z => CF.ofReal (if z.im == 0 then (if z.re > 0 then 1 else if z.re < 0 then -1 else 0) else 0))]

/-- The numeric evaluator over ℂ. Real variables come from `env`; `i` and `π` are constants. -/
partial def evalNumericC (env : List (String × Float)) : Expr → Except String CF
  | .num q => .ok (CF.ofReal q.toFloat)
  | .var x =>
    match env.lookup x <|> constants.lookup x with
    | some v => .ok (CF.ofReal v)
    | none => .error s!"cannot evaluate numerically: '{x}' is unbound"
  | .add es => es.foldlM (fun s a => do pure (s + (← evalNumericC env a))) CF.zero
  | .mul es => es.foldlM (fun s a => do pure (s * (← evalNumericC env a))) CF.one
  | .pow b e => do pure (CF.pow (← evalNumericC env b) (← evalNumericC env e))
  | .fn f [a] =>
    match fnsC.lookup f with
    | some g => do pure (g (← evalNumericC env a))
    | none => .error s!"cannot evaluate '{f}' numerically"
  | .fn "π" [] => .ok (CF.ofReal 3.141592653589793)
  | .fn "i" [] => .ok CF.I
  | .fn f _ => .error s!"cannot evaluate '{f}' numerically"
  | .matrix _ => .error "N() of a matrix: apply N to entries instead"

/-- A complex float as the engine's exact-looking term `re + im·i` (each part a rational
approximation, flagged as such). -/
def cfToExpr (z : CF) : Except String Expr := do
  let re ← floatToExpr z.re
  let im ← floatToExpr z.im
  if z.im == 0 then pure re
  else if z.re == 0 then pure (.mul [im, iE])
  else pure (.add [re, .mul [im, iE]])

/-- One term of a finite Fourier sum: the frequency `k` and the coefficient `c_k`. -/
structure FTerm where
  k : Int
  coeff : Expr
  deriving Repr, Inhabited

/-- `k` from an angle `θ` in `exp(i θ)` that is `k·t`, `t`, `−t` or `q·t` with an integer `q`. -/
private def freqOf (θ : Expr) (t : String) : Option Int :=
  match θ with
  | .var y => if y == t then some 1 else none
  | .mul [.num q, .var y] => if y == t && q.isInt then some q.val.num else none
  | _ => none

/-- One summand as `(k, c_k)`: a product with exactly one factor `exp(i k t)` and the rest
independent of `t`, a bare `exp(i k t)`, or a term free of `t` (the constant term, `k = 0`). -/
private def termOf (s : Expr) (t : String) : Option FTerm :=
  let fs := unMul s
  let isExpT (f : Expr) : Bool := match f with
    | .fn "exp" [u] => match imagArg u with | some θ => (freqOf θ t).isSome | none => false
    | _ => false
  match fs.filter isExpT, fs.filter (fun f => !isExpT f) with
  | [.fn "exp" [u]], rest =>
    if rest.any (·.dependsOn t) then none else
    match imagArg u >>= (freqOf · t) with
    | some k => some ⟨k, mulN (if rest.isEmpty then [Expr.one] else rest)⟩
    | none => none
  | [], _ => if s.dependsOn t then none else some ⟨0, s⟩
  | _, _ => none

/-- The `(k, c_k)` of a finite Fourier sum in `t`, or `none` when some summand is not of the form
`c · exp(i k t)`. Terms with the same `k` are kept separate; the animation sums them. -/
def fourierTerms (e : Expr) (t : String) : Option (List FTerm) :=
  (unAdd e).mapM (termOf · t)

/-- The discrete Fourier transform, `c_k = (1/N) Σ_j p_j e^{−2πi kj/N}`, for `k` from `−⌊N/2⌋`
to `⌈N/2⌉ − 1`: the frequencies an `N`-point sample can carry, centred on 0 so the epicycles come
in ± pairs. -/
def dft (pts : Array CF) : Array (Int × CF) :=
  let n := pts.size
  if n == 0 then #[] else
  let nf := n.toFloat
  let lo : Int := -(n / 2 : Nat)
  (Array.range n).map fun (j : Nat) =>
    let k : Int := lo + (j : Int)
    let sum := (Array.range n).foldl (fun acc m =>
      acc + pts[m]! * CF.cis (-2 * 3.141592653589793 * Float.ofInt k * m.toFloat / nf)) CF.zero
    (k, ⟨sum.re / nf, sum.im / nf⟩)

/-- The curve `Σ c_k e^{i k t}` sampled at `n` points of `[0, 2π]`, from numeric terms. -/
def epicycleTrace (terms : Array (Int × CF)) (n : Nat) : Array (Float × Float) :=
  (Array.range n).map fun j =>
    let t := 2 * 3.141592653589793 * j.toFloat / n.toFloat
    let z := terms.foldl (fun acc (k, c) => acc + c * CF.cis (Float.ofInt k * t)) CF.zero
    (z.re, z.im)

end MathEngine
