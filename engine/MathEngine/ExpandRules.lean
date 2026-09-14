import MathEngine.Rewrite
import MathEngine.Print
import MathEngine.SimpRules
/-!
# `expand.*` — distribution. Used by the `expand` command, not by `simplify`.
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

def expandRules : List PlainRule := [
  { name := "expand.power", apply := fun e =>
      match e with
      | .pow (.add ts) (.num n) =>
        if n.isInt && n.val.num ≥ 2 && n.val.num ≤ 12 then
          let k := n.val.num.toNat
          some ⟨.mul (List.replicate k (.add ts)), s!"$s^\{{k}}$ is $s$ multiplied by itself {k} times; expand by repeated distribution.", none, none⟩
        else none
      | _ => none },
  { name := "expand.distribute", apply := fun e =>
      match e with
      | .mul es =>
        match es.zipIdx.find? (fun (a, _) => isAdd a) with
        | some (.add ts, i) =>
          let others := (es.zipIdx.filter (·.2 != i)).map (·.1)
          some ⟨.add (ts.map fun t => .mul (others ++ [t])), s!"Distributive law: $a(b + c) = ab + ac$, applied to ${(Expr.add ts).toText}$.", none, none⟩
        | _ => none
      | _ => none },
]

end MathEngine
