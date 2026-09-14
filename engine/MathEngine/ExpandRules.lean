import MathEngine.Rewrite
import MathEngine.Print
import MathEngine.SimpRules
/-!
# `expand` — distribution as a total function, and the two parity rules
-/
namespace MathEngine
open Expr

/-- `(ab)^n = a^n b^n` and `(b^m)^n = b^(mn)` for symbolic `m`: the two reference `simp.power` cases
that no additive measure can decrease (see `SimpRules.lean`); `Order.lean`'s `M` does. They are parity
rules for the notebook pipeline and the expand set, not part of the additively-proven `simplify`.
Exponents 0 and 1 are left to `simp.power`, which is what makes them measure-decreasing. -/
def parityPowMul : PlainRule :=
  { name := "simp.power", apply := fun e =>
      match e with
      | .pow (.mul fs) (.num n) =>
        if n.isInt && !n.isZero && !n.isOne then some ⟨.mul (fs.map fun a => .pow a (.num n)), "$(ab)^n = a^n b^n$: a power of a product is the product of the powers.", none, none⟩ else none
      | _ => none }

def parityPowPow : PlainRule :=
  { name := "simp.power", apply := fun e =>
      match e with
      | .pow (.pow b m) (.num n) =>
        if n.isInt && !n.isZero && !n.isOne && !m.isNum then some ⟨.pow b (.mul [m, .num n]), "$(b^m)^n = b^{mn}$ for integer $n$.", none, none⟩ else none
      | _ => none }

def parityRules : List PlainRule := [parityPowMul, parityPowPow]

/-!
## Distribution as a total function

`expand` used to be a nested rewrite system (distribute, then the simp rules, under fuel). A joint
termination ordering for distribution together with `simp` runs into the wall M5 hit — an
interpretation under which `a(b + c) → ab + ac` decreases makes `x·x → x²` increase — so instead
distribution is one total, structurally recursive function, `Expand.dist`, and the pipeline (whose
termination is proved) collects the result afterwards. There is no step budget anywhere any more.
`dist` is what the `expand` command returns and what `proofs/Proofs/Expand.lean` proves sound;
`Expand.steps` retraces the same traversal to record the derivation shown, and proves nothing.
-/
namespace Expand

def summands : Expr → List Expr | .add ts => ts | e => [e]
def factors : Expr → List Expr | .mul fs => fs | e => [e]

/-- A monomial: a rational coefficient and its other factors, kept sorted so that equal monomials
have equal keys and can be collected as they arise. -/
structure Mono where
  coeff : Q
  key : List Expr
  deriving Repr

def Mono.eval (m : Mono) : Expr :=
  if m.key.isEmpty then .num m.coeff
  else if m.coeff.isOne then mulN m.key
  else .mul (.num m.coeff :: m.key)

/-- The product of the numerals in a list, times `c`. -/
def numProduct : List Expr → Q → Q
  | [], c => c
  | .num q :: fs, c => numProduct fs (c * q)
  | _ :: fs, c => numProduct fs c

/-- The monomial of a factor list: numerals multiply into the coefficient. -/
def Mono.ofFactors (fs : List Expr) : Mono :=
  ⟨numProduct (fs.filter isNum) Q.one, (fs.filter (fun f => !isNum f)).mergeSort leMul⟩

def Mono.mul (a b : Mono) : Mono := ⟨a.coeff * b.coeff, (a.key ++ b.key).mergeSort leMul⟩

/-- A polynomial is a list of monomials with distinct keys. -/
abbrev Poly := List Mono

def insertMono (m : Mono) : Poly → Poly
  | [] => [m]
  | n :: ns => if Expr.beqList n.key m.key then ⟨n.coeff + m.coeff, n.key⟩ :: ns else n :: insertMono m ns

def collect (ms : List Mono) : Poly := ms.foldl (fun acc m => insertMono m acc) []

def polyMul (p q : Poly) : Poly := collect (p.flatMap fun a => q.map (Mono.mul a))

/-- A distributed term as a polynomial: one monomial per summand. -/
def toPoly (e : Expr) : Poly := (summands e).map fun t => Mono.ofFactors (factors t)

/-- Back to a term; zero coefficients are dropped. -/
def ofPoly (p : Poly) : Expr := .add ((p.filter fun m => !m.coeff.isZero).map Mono.eval)

/-- A product whose factors are already distributed: multiply out if any factor is a sum,
collecting like monomials as the product is built up factor by factor. -/
def distMul (fs : List Expr) : Expr :=
  if fs.any isAdd then ofPoly ((fs.map toPoly).foldl polyMul [⟨Q.one, []⟩]) else .mul fs

/-- `(sum)^n` for `2 ≤ n ≤ 12` is the sum multiplied by itself `n` times. -/
def powCopies (b e : Expr) : Expr :=
  match b, e with
  | .add ts, .num n =>
    if n.isInt && n.val.num ≥ 2 && n.val.num ≤ 12 then distMul (List.replicate n.val.num.toNat (.add ts))
    else .pow b e
  | _, _ => .pow b e

/-- Splice sums into a sum, so that a summand is never itself a sum — otherwise a product with such
a sum among its factors would treat the inner sum as one monomial and stop distributing early. -/
def flatAdd : List Expr → List Expr
  | [] => []
  | .add ts :: es => ts ++ flatAdd es
  | e :: es => e :: flatAdd es

mutual
  /-- Fully distributed form: children first, then this node. -/
  def dist : Expr → Expr
    | .num q => .num q
    | .var x => .var x
    | .add es => .add (flatAdd (distList es))
    | .mul es => distMul (distList es)
    | .pow b e => powCopies (dist b) (dist e)
    | .fn f es => .fn f (distList es)
    | .matrix rows => .matrix (distRows rows)
  def distList : List Expr → List Expr
    | [] => []
    | e :: es => dist e :: distList es
  def distRows : List (List Expr) → List (List Expr)
    | [] => []
    | r :: rs => distList r :: distRows rs
end

/-- The derivation `dist` would show: one step per product multiplied out and per power copied,
each with the local before and after. Display only; `dist` is the result. -/
partial def steps (e : Expr) : Array Step := Id.run do
  let below := (children e).foldl (fun acc c => acc ++ steps c) #[]
  let e' := withChildren e ((children e).map dist)
  match e' with
  | .mul fs =>
    if fs.any isAdd then
      let sums := (fs.filter isAdd).map (·.toText)
      return below.push ⟨"expand.distribute", s!"Distributive law: multiply out ${", ".intercalate sums}$ against the other factors, one monomial per choice of summands, like monomials collected.", [], e', distMul fs, none⟩
    else return below
  | .pow b x =>
    let r := powCopies b x
    if r == .pow b x then return below
    else
      let n := match x with | .num n => n.val.num.toNat | _ => 0
      let copies := .mul (List.replicate n b)
      return (below.push ⟨"expand.power", s!"$s^\{{n}}$ is $s$ multiplied by itself {n} times.", [], e', copies, none⟩).push
        ⟨"expand.distribute", "Distributive law: one monomial per choice of summands.", [], copies, r, none⟩
  | _ => return below

end Expand

end MathEngine
