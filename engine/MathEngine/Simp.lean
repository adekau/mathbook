import MathEngine.Semantics
/-!
# A verified simplifier (first slice)

`simpTop` is the `simp.identity` rule from `simplify.ts` — drop `+ 0` and `* 1` — and
`simpTop_sound` proves it preserves meaning. This is the pattern every rule follows:
rule as a function on syntax, soundness as `SemEq`, proof by induction using ring laws.
-/
namespace MathEngine
open Expr

def isZeroLit : Expr → Bool | .num q => q.num == 0 && q.den == 1 | _ => false
def isOneLit  : Expr → Bool | .num q => q.num == 1 && q.den == 1 | _ => false

def dropZeros (es : List Expr) : List Expr := es.filter (fun e => !isZeroLit e)
def dropOnes  (es : List Expr) : List Expr := es.filter (fun e => !isOneLit e)

def simpTop : Expr → Expr
  | .add es => match dropZeros es with | [] => .num ⟨0, 1⟩ | [e] => e | es' => .add es'
  | .mul es => match dropOnes es  with | [] => .num ⟨1, 1⟩ | [e] => e | es' => .mul es'
  | e => e

theorem isZeroLit_iff {e : Expr} : isZeroLit e = true ↔ e = .num ⟨0, 1⟩ := by
  cases e with
  | num q => obtain ⟨n, d⟩ := q; simp [isZeroLit]
  | _ => simp [isZeroLit]

theorem isOneLit_iff {e : Expr} : isOneLit e = true ↔ e = .num ⟨1, 1⟩ := by
  cases e with
  | num q => obtain ⟨n, d⟩ := q; simp [isOneLit]
  | _ => simp [isOneLit]

theorem evalZ_zeroLit {e : Expr} (h : isZeroLit e = true) (ρ : Env) : evalZ ρ e = 0 := by
  rw [isZeroLit_iff.mp h]; rfl

theorem evalZ_oneLit {e : Expr} (h : isOneLit e = true) (ρ : Env) : evalZ ρ e = 1 := by
  rw [isOneLit_iff.mp h]; rfl

theorem evalSum_dropZeros (ρ : Env) (es : List Expr) : evalSum ρ (dropZeros es) = evalSum ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : isZeroLit e = true
    · simp [dropZeros, List.filter, h, evalSum, evalZ_zeroLit h, ← ih]
    · simp only [Bool.not_eq_true] at h
      simp [dropZeros, List.filter, h, evalSum, ← ih]

theorem evalProd_dropOnes (ρ : Env) (es : List Expr) : evalProd ρ (dropOnes es) = evalProd ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : isOneLit e = true
    · simp [dropOnes, List.filter, h, evalProd, evalZ_oneLit h, ← ih]
    · simp only [Bool.not_eq_true] at h
      simp [dropOnes, List.filter, h, evalProd, ← ih]

theorem simpTop_sound (e : Expr) : SemEq (simpTop e) e := by
  intro ρ
  cases e with
  | add es =>
    have h := evalSum_dropZeros ρ es
    simp only [simpTop]
    split <;> rename_i hd <;> simp_all [evalZ, evalSum]
  | mul es =>
    have h := evalProd_dropOnes ρ es
    simp only [simpTop]
    split <;> rename_i hd <;> simp_all [evalZ, evalProd]
  | _ => rfl

end MathEngine
