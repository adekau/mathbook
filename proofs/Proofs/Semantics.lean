import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sign
import MathEngine
/-!
# ℝ-valued semantics

`engine/MathEngine/Semantics.lean` interprets the integer fragment: numerals with denominator 1,
no functions, natural-number exponents. That was enough to prove the `simp.*` rules sound *as far
as the fragment sees them*, but it is not what the notebook means by `sin`, `1/2` or `x^(1/2)`.

Here the whole language gets its real meaning, in `proofs/` because ℝ is noncomputable and Mathlib
may not enter the engine (`scripts/check-engine-deps.sh`). `evalR` is total, using Mathlib's own
junk conventions at the edges (`Real.log 0 = 0`, `Real.sqrt (-1) = 0`, `(0:ℝ) ^ (-1 : ℝ) = 0`), so
that every statement below is an unconditional equation between total functions and the *side
conditions a rule really needs* have to be written down rather than hidden in a partial function.

`evalR_of_eval?` is the bridge: wherever the integer semantics is defined, it agrees with this one.
So M1's `simplify_sound` was a restriction of the truth, not a different claim.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- Real-valued environment. -/
abbrev EnvR := String → ℝ

/-- The unary functions the notebook knows. `log` is base 10, as in the reference engine; unknown
names get the junk value 0 (the engine never evaluates them either). -/
def applyFn (f : String) (x : ℝ) : ℝ :=
  match f with
  | "sin" => Real.sin x
  | "cos" => Real.cos x
  | "tan" => Real.tan x
  | "exp" => Real.exp x
  | "ln" => Real.log x
  | "log" => Real.logb 10 x
  | "sqrt" => Real.sqrt x
  | "abs" => |x|
  | "sign" => Real.sign x
  | _ => 0

@[simp] theorem applyFn_sin (x : ℝ) : applyFn "sin" x = Real.sin x := by simp [applyFn]
@[simp] theorem applyFn_cos (x : ℝ) : applyFn "cos" x = Real.cos x := by simp [applyFn]
@[simp] theorem applyFn_exp (x : ℝ) : applyFn "exp" x = Real.exp x := by simp [applyFn]
@[simp] theorem applyFn_ln (x : ℝ) : applyFn "ln" x = Real.log x := by simp [applyFn]
@[simp] theorem applyFn_sqrt (x : ℝ) : applyFn "sqrt" x = Real.sqrt x := by simp [applyFn]
@[simp] theorem applyFn_abs (x : ℝ) : applyFn "abs" x = |x| := by simp [applyFn]
@[simp] theorem applyFn_sign (x : ℝ) : applyFn "sign" x = Real.sign x := by simp [applyFn]

/-- The constants: `π` is `Real.pi`; any other 0-ary function node (`i`, which has no real
meaning) is the junk value 0. Shared by `evalR` and `evalD`, so the two agree definitionally. -/
def constR (f : String) : ℝ := if f = "π" then Real.pi else 0

@[simp] theorem constR_pi : constR "π" = Real.pi := by simp [constR]

mutual
  /-- Meaning of an expression in ℝ. Exponentiation is `Real.rpow`, which agrees with integer and
  natural powers (`Real.rpow_intCast`) and gives `Real.sqrt` its `x ^ (1/2)` reading. -/
  def evalR (ρ : EnvR) : Expr → ℝ
    | .num q => (q.val : ℝ)
    | .var x => ρ x
    | .add es => sumR ρ es
    | .mul es => prodR ρ es
    | .pow b e => (evalR ρ b) ^ (evalR ρ e)
    | .fn f [] => constR f
    | .fn f [a] => applyFn f (evalR ρ a)
    | .fn _ _ => 0
    | .matrix _ => 0
  def sumR (ρ : EnvR) : List Expr → ℝ
    | [] => 0
    | e :: es => evalR ρ e + sumR ρ es
  def prodR (ρ : EnvR) : List Expr → ℝ
    | [] => 1
    | e :: es => evalR ρ e * prodR ρ es
end

@[simp] theorem evalR_num (ρ : EnvR) (q : Q) : evalR ρ (.num q) = (q.val : ℝ) := rfl
@[simp] theorem evalR_var (ρ : EnvR) (x : String) : evalR ρ (.var x) = ρ x := rfl
@[simp] theorem evalR_add (ρ : EnvR) (es : List Expr) : evalR ρ (.add es) = sumR ρ es := rfl
@[simp] theorem evalR_mul (ρ : EnvR) (es : List Expr) : evalR ρ (.mul es) = prodR ρ es := rfl
@[simp] theorem evalR_pow (ρ : EnvR) (b e : Expr) :
    evalR ρ (.pow b e) = (evalR ρ b) ^ (evalR ρ e) := rfl
@[simp] theorem evalR_fn₁ (ρ : EnvR) (f : String) (a : Expr) :
    evalR ρ (.fn f [a]) = applyFn f (evalR ρ a) := rfl
@[simp] theorem evalR_fn₀ (ρ : EnvR) (f : String) : evalR ρ (.fn f []) = constR f := rfl
@[simp] theorem evalR_matrix (ρ : EnvR) (rows : List (List Expr)) : evalR ρ (.matrix rows) = 0 := rfl
@[simp] theorem sumR_nil (ρ : EnvR) : sumR ρ [] = 0 := rfl
@[simp] theorem sumR_cons (ρ : EnvR) (e : Expr) (es : List Expr) :
    sumR ρ (e :: es) = evalR ρ e + sumR ρ es := rfl
@[simp] theorem prodR_nil (ρ : EnvR) : prodR ρ [] = 1 := rfl
@[simp] theorem prodR_cons (ρ : EnvR) (e : Expr) (es : List Expr) :
    prodR ρ (e :: es) = evalR ρ e * prodR ρ es := rfl

@[simp] theorem evalR_zero (ρ : EnvR) : evalR ρ Expr.zero = 0 := by
  simp [Expr.zero, Q.zero, Q.ofInt]
@[simp] theorem evalR_one (ρ : EnvR) : evalR ρ Expr.one = 1 := by
  simp [Expr.one, Q.one, Q.ofInt]

theorem sumR_append (ρ : EnvR) (l₁ l₂ : List Expr) :
    sumR ρ (l₁ ++ l₂) = sumR ρ l₁ + sumR ρ l₂ := by
  induction l₁ with
  | nil => simp
  | cons e es ih => simp [ih, add_assoc]

theorem prodR_append (ρ : EnvR) (l₁ l₂ : List Expr) :
    prodR ρ (l₁ ++ l₂) = prodR ρ l₁ * prodR ρ l₂ := by
  induction l₁ with
  | nil => simp
  | cons e es ih => simp [ih, mul_assoc]

theorem sumR_perm (ρ : EnvR) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : sumR ρ l₁ = sumR ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l => simp; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem prodR_perm (ρ : EnvR) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : prodR ρ l₁ = prodR ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l => simp; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `addN`/`mulN` collapse a singleton, so they agree with the list forms. -/
@[simp] theorem evalR_addN (ρ : EnvR) (l : List Expr) : evalR ρ (Expr.addN l) = sumR ρ l := by
  match l with
  | [x] => simp [Expr.addN]
  | [] | _ :: _ :: _ => rfl

@[simp] theorem evalR_mulN (ρ : EnvR) (l : List Expr) : evalR ρ (Expr.mulN l) = prodR ρ l := by
  match l with
  | [x] => simp [Expr.mulN]
  | [] | _ :: _ :: _ => rfl

/-- Semantic equality over ℝ: agreement in every environment. -/
def SemEqR (a b : Expr) : Prop := ∀ ρ, evalR ρ a = evalR ρ b

theorem SemEqR.refl (e : Expr) : SemEqR e e := fun _ => rfl
theorem SemEqR.trans {a b c : Expr} (h₁ : SemEqR a b) (h₂ : SemEqR b c) : SemEqR a c :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)
theorem SemEqR.symm {a b : Expr} (h : SemEqR a b) : SemEqR b a := fun ρ => (h ρ).symm

/-- Semantic equality *where `P` holds*: what a rule with a side condition really proves. -/
def SemEqROn (P : EnvR → Prop) (a b : Expr) : Prop := ∀ ρ, P ρ → evalR ρ a = evalR ρ b

theorem SemEqR.on {a b : Expr} (h : SemEqR a b) (P : EnvR → Prop) : SemEqROn P a b :=
  fun ρ _ => h ρ

-- ---------------------------------------------------------------------------
-- The bridge: the integer fragment is a restriction of this semantics
-- ---------------------------------------------------------------------------

/-- An integer environment, read as a real one. -/
def ofEnvZ (ρ : MathEngine.Env) : EnvR := fun x => (ρ x : ℝ)

theorem evalR_of_asInt? {q : Q} {n : ℤ} (h : q.asInt? = some n) (ρ : EnvR) :
    evalR ρ (.num q) = (n : ℝ) := by
  simp only [Q.asInt?] at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    rw [evalR_num, Rat.cast_def, hd]
    norm_num
  · simp at h

mutual
  /-- **Wherever the integer semantics is defined, the real semantics agrees.** -/
  theorem evalR_of_eval? {ρ : MathEngine.Env} : ∀ {e : Expr} {v : ℤ},
      eval? ρ e = some v → evalR (ofEnvZ ρ) e = (v : ℝ)
    | .num q, v, h => evalR_of_asInt? h _
    | .var x, v, h => by simp only [eval?, Option.some.injEq] at h; simp [ofEnvZ, h]
    | .add es, v, h => by simp only [eval?] at h; exact sumR_of_evalSum? h
    | .mul es, v, h => by simp only [eval?] at h; exact prodR_of_evalProd? h
    | .fn _ _, v, h => by simp [eval?] at h
    | .matrix _, v, h => by simp [eval?] at h
    | .pow b x, v, h => by
      obtain ⟨vb, n, hb, hx, hn, rfl⟩ := eval?_pow_some h
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [evalR_pow, evalR_of_eval? hb, evalR_of_eval? hx]
      simp only [Int.toNat_natCast, Int.cast_natCast, Int.cast_pow]
      exact Real.rpow_natCast _ k
  theorem sumR_of_evalSum? {ρ : MathEngine.Env} : ∀ {es : List Expr} {v : ℤ},
      evalSum? ρ es = some v → sumR (ofEnvZ ρ) es = (v : ℝ)
    | [], v, h => by simp only [evalSum?, Option.some.injEq] at h; simp [← h]
    | e :: es, v, h => by
      simp only [evalSum?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, s, hs, rfl⟩ := h
      rw [sumR_cons, evalR_of_eval? ha, sumR_of_evalSum? hs]
      push_cast
      ring
  theorem prodR_of_evalProd? {ρ : MathEngine.Env} : ∀ {es : List Expr} {v : ℤ},
      evalProd? ρ es = some v → prodR (ofEnvZ ρ) es = (v : ℝ)
    | [], v, h => by simp only [evalProd?, Option.some.injEq] at h; simp [← h]
    | e :: es, v, h => by
      simp only [evalProd?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, p, hp, rfl⟩ := h
      rw [prodR_cons, evalR_of_eval? ha, prodR_of_evalProd? hp]
      push_cast
      ring
end

/-- The M1 notion of soundness implies the ℝ one *on the fragment*: if `a` refines to `b` and `a`
has an integer value, `b` has the same real value. (The converse is what `SemEqR` strengthens.) -/
theorem evalR_eq_of_Refines {a b : Expr} (h : Refines a b) (ρ : MathEngine.Env) (v : ℤ)
    (ha : eval? ρ a = some v) : evalR (ofEnvZ ρ) a = evalR (ofEnvZ ρ) b :=
  (evalR_of_eval? ha).trans (evalR_of_eval? (h ρ v ha)).symm

end MathProofs
end
