import Proofs.Semantics
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
/-!
# `diff.*` against Mathlib's `deriv`

`evalR` gives every node its real value, but it sends `diff(f, x)` to junk, and deliberately: the
second child of a `diff` node is a **binder**, not a value. `Expr` does not mark binder positions,
so `.var x` and `.add [.var x]` denote the same real number while only one of them can be read as
"the variable we are differentiating along". A semantics that interprets `diff` therefore cannot
satisfy `SemEqR.congr`, which is the law M3's fold (`normalize_sound_for`) is built on.

So this file *extends* rather than edits: `evalD` agrees with `evalR` everywhere except that it
reads `diff`, and `evalD_eq_evalR` proves the two agree on every diff-free term. That is the same
shape as M1 → M3, where `evalR_of_eval?` showed the integer fragment was a restriction of ℝ. The
`diff.*` rules run under the tiered rewriter `normalizeT`, never under the additive `normalize`, so they never need
the congruence in the first place.

As in M3, the interesting result is which rules need a hypothesis. `deriv` is junk-valued off the
differentiable set, so the sum, product and chain rules genuinely fail without one: the notebook is
doing what every computer-algebra system does, and here the assumption is written down.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- `ρ` with `x` rebound to `t`. -/
def upd (ρ : EnvR) (x : String) (t : ℝ) : EnvR := fun y => if y = x then t else ρ y

@[simp] theorem upd_same (ρ : EnvR) (x : String) (t : ℝ) : upd ρ x t x = t := by simp [upd]
theorem upd_other (ρ : EnvR) {x y : String} (h : y ≠ x) (t : ℝ) : upd ρ x t y = ρ y := by simp [upd, h]

/-- Rebinding a variable to the value it already has changes nothing. This is what turns a
`HasDerivAt` at the point `ρ x` back into a statement about `ρ` itself. -/
@[simp] theorem upd_self (ρ : EnvR) (x : String) : upd ρ x (ρ x) = ρ := by
  funext y; by_cases h : y = x <;> simp [upd, h]

theorem upd_comm (ρ : EnvR) {x y : String} (h : y ≠ x) (s t : ℝ) :
    upd (upd ρ y t) x s = upd (upd ρ x s) y t := by
  funext z; by_cases hx : z = x <;> by_cases hy : z = y <;> simp_all [upd]

mutual
  /-- `evalR` extended to the differentiation fragment. The only new case is `diff`, factored into
  `fnD` so that the patterns are non-overlapping (by argument count) and every equation is `rfl`. -/
  def evalD : EnvR → Expr → ℝ
    | ρ, .num q => (q.val : ℝ)
    | ρ, .var y => ρ y
    | ρ, .add es => sumD ρ es
    | ρ, .mul es => prodD ρ es
    | ρ, .pow b e => (evalD ρ b) ^ (evalD ρ e)
    | ρ, .fn f es => fnD ρ f es
    | _, .matrix _ => 0
  def fnD : EnvR → String → List Expr → ℝ
    | _, f, [] => constR f
    | ρ, f, [a] => applyFn f (evalD ρ a)
    | ρ, f, [g, v] =>
      if f = "diff" then
        match v with
        | .var x => deriv (fun t => evalD (upd ρ x t) g) (ρ x)
        | _ => 0
      else 0
    | _, _, _ => 0
  def sumD : EnvR → List Expr → ℝ
    | _, [] => 0
    | ρ, e :: es => evalD ρ e + sumD ρ es
  def prodD : EnvR → List Expr → ℝ
    | _, [] => 1
    | ρ, e :: es => evalD ρ e * prodD ρ es
end

@[simp] theorem evalD_num (ρ : EnvR) (q : Q) : evalD ρ (.num q) = (q.val : ℝ) := rfl
@[simp] theorem evalD_var (ρ : EnvR) (y : String) : evalD ρ (.var y) = ρ y := rfl
@[simp] theorem evalD_add (ρ : EnvR) (es : List Expr) : evalD ρ (.add es) = sumD ρ es := rfl
@[simp] theorem evalD_mul (ρ : EnvR) (es : List Expr) : evalD ρ (.mul es) = prodD ρ es := rfl
@[simp] theorem evalD_pow (ρ : EnvR) (b e : Expr) : evalD ρ (.pow b e) = (evalD ρ b) ^ (evalD ρ e) := rfl
@[simp] theorem evalD_matrix (ρ : EnvR) (rows : List (List Expr)) : evalD ρ (.matrix rows) = 0 := rfl
@[simp] theorem evalD_fn (ρ : EnvR) (f : String) (es : List Expr) : evalD ρ (.fn f es) = fnD ρ f es := rfl
@[simp] theorem fnD_one (ρ : EnvR) (f : String) (a : Expr) : fnD ρ f [a] = applyFn f (evalD ρ a) := rfl
theorem fnD_two (ρ : EnvR) (f : String) (g v : Expr) :
    fnD ρ f [g, v] = if f = "diff" then (match v with | .var x => deriv (fun t => evalD (upd ρ x t) g) (ρ x) | _ => 0) else 0 := rfl
@[simp] theorem fnD_nil (ρ : EnvR) (f : String) : fnD ρ f [] = constR f := rfl
@[simp] theorem fnD_long (ρ : EnvR) (f : String) (a b c : Expr) (r : List Expr) :
    fnD ρ f (a :: b :: c :: r) = 0 := rfl
@[simp] theorem fnD_two_ne (ρ : EnvR) {f : String} (g v : Expr) (h : f ≠ "diff") : fnD ρ f [g, v] = 0 := by
  rw [fnD_two, if_neg h]
@[simp] theorem sumD_nil (ρ : EnvR) : sumD ρ [] = 0 := rfl
@[simp] theorem sumD_cons (ρ : EnvR) (e : Expr) (es : List Expr) :
    sumD ρ (e :: es) = evalD ρ e + sumD ρ es := rfl
@[simp] theorem prodD_nil (ρ : EnvR) : prodD ρ [] = 1 := rfl
@[simp] theorem prodD_cons (ρ : EnvR) (e : Expr) (es : List Expr) :
    prodD ρ (e :: es) = evalD ρ e * prodD ρ es := rfl

/-- **The meaning of `diff(f, x)`**: the derivative of `f`, read as a function of `x`, at the point
`ρ` names. Written `D ρ x f` throughout. -/
def D (ρ : EnvR) (x : String) (f : Expr) : ℝ := deriv (fun t => evalD (upd ρ x t) f) (ρ x)

@[simp] theorem evalD_diff (ρ : EnvR) (f : Expr) (x : String) :
    evalD ρ (.fn "diff" [f, .var x]) = D ρ x f := by rw [evalD_fn, fnD_two, if_pos rfl]; rfl

/-- The function `diff(f, x)` differentiates. -/
abbrev fx (ρ : EnvR) (x : String) (f : Expr) : ℝ → ℝ := fun t => evalD (upd ρ x t) f

/-- "`f` is differentiable in `x` at the point `ρ` names" — the hypothesis the sum, product and
chain rules need, and the thing `deriv`'s junk value hides. -/
abbrev DiffAt (ρ : EnvR) (x : String) (f : Expr) : Prop := DifferentiableAt ℝ (fx ρ x f) (ρ x)

theorem D_eq (ρ : EnvR) (x : String) (f : Expr) : D ρ x f = deriv (fx ρ x f) (ρ x) := rfl

/-- `fnD` is what the `evalD_fn` simp lemma leaves behind, so `diff` needs its own form here too. -/
@[simp] theorem fnD_diff (ρ : EnvR) (f : Expr) (x : String) :
    fnD ρ "diff" [f, .var x] = D ρ x f := by rw [fnD_two, if_pos rfl]; rfl

theorem evalD_intLit (ρ : EnvR) (m : ℤ) : evalD ρ (.num (Q.ofInt m)) = (m : ℝ) := by
  show ((Q.ofInt m).val : ℝ) = _
  norm_num [Q.ofInt]

@[simp] theorem evalD_minusOne (ρ : EnvR) : evalD ρ Expr.minusOne = -1 := by
  have h := evalD_intLit ρ (-1)
  simpa [Expr.minusOne, Q.minusOne] using h

@[simp] theorem evalD_zero (ρ : EnvR) : evalD ρ Expr.zero = 0 := by simp [Expr.zero, Q.zero, Q.ofInt]
@[simp] theorem evalD_one (ρ : EnvR) : evalD ρ Expr.one = 1 := by simp [Expr.one, Q.one, Q.ofInt]

-- ---------------------------------------------------------------------------
-- `evalD` extends `evalR`
-- ---------------------------------------------------------------------------

/-- A term with no `diff` node anywhere. -/
def DiffFree : Expr → Prop
  | .num _ | .var _ => True
  | .add es | .mul es => DiffFreeList es
  | .pow b e => DiffFree b ∧ DiffFree e
  | .fn f es => f ≠ "diff" ∧ DiffFreeList es
  | .matrix _ => True
where
  DiffFreeList : List Expr → Prop
    | [] => True
    | e :: es => DiffFree e ∧ DiffFreeList es

mutual
  /-- **`evalD` is a conservative extension of `evalR`.** -/
  theorem evalD_eq_evalR (ρ : EnvR) : ∀ {e : Expr}, DiffFree e → evalD ρ e = evalR ρ e
    | .num _, _ => rfl
    | .var _, _ => rfl
    | .matrix _, _ => rfl
    | .add es, h => by simp only [evalD_add, evalR_add]; exact sumD_eq_sumR ρ h
    | .mul es, h => by simp only [evalD_mul, evalR_mul]; exact prodD_eq_prodR ρ h
    | .pow b e, h => by
      obtain ⟨hb, he⟩ := h
      simp only [evalD_pow, evalR_pow, evalD_eq_evalR ρ hb, evalD_eq_evalR ρ he]
    | .fn f es, h => by
      obtain ⟨hne, hl⟩ := h
      match es, hl with
      | [], _ => rfl
      | [a], ⟨ha, _⟩ => simp only [evalD_fn, fnD_one, evalR_fn₁, evalD_eq_evalR ρ ha]
      | [g, v], _ => simp [fnD_two_ne _ _ _ hne, evalR]
      | _ :: _ :: _ :: _, _ => simp [evalR]
  theorem sumD_eq_sumR (ρ : EnvR) : ∀ {es : List Expr}, DiffFree.DiffFreeList es → sumD ρ es = sumR ρ es
    | [], _ => rfl
    | e :: es, h => by
      obtain ⟨he, hes⟩ := h
      rw [sumD_cons, sumR_cons, evalD_eq_evalR ρ he, sumD_eq_sumR ρ hes]
  theorem prodD_eq_prodR (ρ : EnvR) : ∀ {es : List Expr}, DiffFree.DiffFreeList es → prodD ρ es = prodR ρ es
    | [], _ => rfl
    | e :: es, h => by
      obtain ⟨he, hes⟩ := h
      rw [prodD_cons, prodR_cons, evalD_eq_evalR ρ he, prodD_eq_prodR ρ hes]
end

-- ---------------------------------------------------------------------------
-- Substitution: rebinding a variable a term does not mention changes nothing
-- ---------------------------------------------------------------------------

mutual
  theorem evalD_upd_not_free (ρ : EnvR) (y : String) (t : ℝ) :
      ∀ {e : Expr}, y ∉ Expr.freeVars e → evalD (upd ρ y t) e = evalD ρ e
    | .num _, _ => rfl
    | .matrix _, _ => rfl
    | .var z, h => by
      have hz : z ≠ y := by intro hz; exact h (by simp [Expr.freeVars, hz])
      simp [upd_other ρ hz]
    | .add es, h => by
      simp only [evalD_add]
      exact sumD_upd_not_free ρ y t (by simpa [Expr.freeVars] using h)
    | .mul es, h => by
      simp only [evalD_mul]
      exact prodD_upd_not_free ρ y t (by simpa [Expr.freeVars] using h)
    | .pow b e, h => by
      simp only [Expr.freeVars, List.mem_append, not_or] at h
      simp only [evalD_pow, evalD_upd_not_free ρ y t h.1, evalD_upd_not_free ρ y t h.2]
    | .fn f es, h => by
      match es with
      | [] => rfl
      | [a] =>
        have ha : y ∉ Expr.freeVars a := by simpa [Expr.freeVars, Expr.freeVars.freeVarsList] using h
        simp only [evalD_fn, fnD_one, evalD_upd_not_free ρ y t ha]
      | [g, v] =>
        by_cases hf : f = "diff"
        · subst hf
          cases v with
          | var x =>
            have hx : x ≠ y := by
              intro hx; exact h (by simp [Expr.freeVars, Expr.freeVars.freeVarsList, hx])
            have hg : y ∉ Expr.freeVars g :=
              (by simpa [Expr.freeVars, Expr.freeVars.freeVarsList] using h :
                y ∉ Expr.freeVars g ∧ ¬ y = x).1
            simp only [evalD_diff, D, upd_other ρ hx]
            congr 1
            funext s
            rw [upd_comm ρ (Ne.symm hx) s t, evalD_upd_not_free (upd ρ x s) y t hg]
          | _ => simp [fnD_two]
        · simp [fnD_two_ne _ _ _ hf]
      | _ :: _ :: _ :: _ => rfl
  theorem sumD_upd_not_free (ρ : EnvR) (y : String) (t : ℝ) :
      ∀ {es : List Expr}, y ∉ Expr.freeVars.freeVarsList es → sumD (upd ρ y t) es = sumD ρ es
    | [], _ => rfl
    | e :: es, h => by
      simp only [Expr.freeVars.freeVarsList, List.mem_append, not_or] at h
      rw [sumD_cons, sumD_cons, evalD_upd_not_free ρ y t h.1, sumD_upd_not_free ρ y t h.2]
  theorem prodD_upd_not_free (ρ : EnvR) (y : String) (t : ℝ) :
      ∀ {es : List Expr}, y ∉ Expr.freeVars.freeVarsList es → prodD (upd ρ y t) es = prodD ρ es
    | [], _ => rfl
    | e :: es, h => by
      simp only [Expr.freeVars.freeVarsList, List.mem_append, not_or] at h
      rw [prodD_cons, prodD_cons, evalD_upd_not_free ρ y t h.1, prodD_upd_not_free ρ y t h.2]
end

/-- A term the differentiation variable does not occur in is a constant function of it. -/
theorem fx_const {ρ : EnvR} {x : String} {e : Expr} (h : ¬ e.dependsOn x) :
    fx ρ x e = fun _ => evalD ρ e := by
  funext t
  exact evalD_upd_not_free ρ x t (by simpa [Expr.dependsOn] using h)


-- ---------------------------------------------------------------------------
-- List plumbing
-- ---------------------------------------------------------------------------

theorem sumD_append (ρ : EnvR) : ∀ (l₁ l₂ : List Expr), sumD ρ (l₁ ++ l₂) = sumD ρ l₁ + sumD ρ l₂
  | [], _ => by simp
  | e :: es, l₂ => by rw [List.cons_append, sumD_cons, sumD_cons, sumD_append ρ es l₂]; ring

theorem prodD_append (ρ : EnvR) : ∀ (l₁ l₂ : List Expr), prodD ρ (l₁ ++ l₂) = prodD ρ l₁ * prodD ρ l₂
  | [], _ => by simp
  | e :: es, l₂ => by rw [List.cons_append, prodD_cons, prodD_cons, prodD_append ρ es l₂]; ring

theorem not_mem_freeVarsList {x : String} : ∀ {es : List Expr},
    (∀ e ∈ es, ¬ e.dependsOn x) → x ∉ Expr.freeVars.freeVarsList es
  | [], _ => by simp [Expr.freeVars.freeVarsList]
  | e :: es, h => by
    simp only [Expr.freeVars.freeVarsList, List.mem_append, not_or]
    exact ⟨by simpa [Expr.dependsOn] using h e (by simp),
      not_mem_freeVarsList (fun a ha => h a (by simp [ha]))⟩

-- ---------------------------------------------------------------------------
-- The rules that need no hypothesis
-- ---------------------------------------------------------------------------

/-- **`diff.constant`.** A term the variable does not occur in is a constant function of it. -/
theorem diff_constant_sound (ρ : EnvR) (x : String) {e : Expr} (h : ¬ e.dependsOn x) :
    D ρ x e = evalD ρ Expr.zero := by
  rw [D_eq, fx_const h, evalD_zero]; exact deriv_const _ _

/-- **`diff.variable`.** -/
theorem diff_variable_sound (ρ : EnvR) (x : String) :
    D ρ x (.var x) = evalD ρ Expr.one := by
  have : fx ρ x (.var x) = id := by funext t; simp
  rw [D_eq, this, evalD_one]; exact deriv_id (ρ x)

/-- **`diff.matrix`.** Matrices carry no real value in this semantics, so the rule is vacuously
sound: both sides denote the junk value. Real content waits for M7's linear algebra. -/
theorem diff_matrix_sound (ρ : EnvR) (x : String) (rows : List (List Expr)) :
    D ρ x (.matrix rows) = evalD ρ (.matrix (rows.map (·.map (fun e => .fn "diff" [e, .var x])))) := by
  have : fx ρ x (.matrix rows) = fun _ => (0 : ℝ) := by funext t; simp
  rw [D_eq, this, evalD_matrix]; exact deriv_const _ _

/-- **`diff.constant-multiple`.** Unconditional: `deriv_const_mul_field` needs no differentiability,
because if the remaining factor is not differentiable then neither is the whole product. -/
theorem diff_const_mul_sound (ρ : EnvR) (x : String) (consts rest : List Expr)
    (hc : ∀ e ∈ consts, ¬ e.dependsOn x) :
    D ρ x (.mul (consts ++ rest)) = evalD ρ (.mul (consts ++ [.fn "diff" [.mul rest, .var x]])) := by
  have hfun : (fun t => evalD (upd ρ x t) (.mul (consts ++ rest)))
      = fun t => prodD ρ consts * prodD (upd ρ x t) rest := by
    funext t
    rw [evalD_mul, prodD_append, prodD_upd_not_free ρ x t (not_mem_freeVarsList hc)]
  rw [D_eq]
  show deriv (fun t => evalD (upd ρ x t) (.mul (consts ++ rest))) (ρ x) = _
  rw [hfun, deriv_const_mul_field]
  rw [evalD_mul, prodD_append, prodD_cons, prodD_nil, evalD_diff, D_eq]
  show _ = prodD ρ consts * (deriv (fun t => evalD (upd ρ x t) (.mul rest)) (ρ x) * 1)
  simp only [evalD_mul, mul_one]

-- ---------------------------------------------------------------------------
-- The rules that need differentiability
-- ---------------------------------------------------------------------------

/-- **`diff.sum`**, as a `HasDerivAt` so the induction composes. -/
theorem hasDerivAt_sumD (ρ : EnvR) (x : String) : ∀ {es : List Expr}, (∀ e ∈ es, DiffAt ρ x e) →
    HasDerivAt (fun t => sumD (upd ρ x t) es) (sumD ρ (es.map (fun e => .fn "diff" [e, .var x]))) (ρ x)
  | [], _ => by simpa using hasDerivAt_const (ρ x) (0 : ℝ)
  | e :: es, h => by
    have h1 : HasDerivAt (fx ρ x e) (D ρ x e) (ρ x) := (h e (List.mem_cons_self ..)).hasDerivAt
    have h2 := hasDerivAt_sumD ρ x (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, sumD_cons, evalD_diff]
    exact h1.add h2

/-- **`diff.sum` is sound where every summand is differentiable.** -/
theorem diff_sum_sound (ρ : EnvR) (x : String) {es : List Expr} (h : ∀ e ∈ es, DiffAt ρ x e) :
    D ρ x (.add es) = evalD ρ (.add (es.map (fun e => .fn "diff" [e, .var x]))) := by
  rw [D_eq, evalD_add]
  exact (hasDerivAt_sumD ρ x h).deriv

/-- **`diff.product` for two factors, where both are differentiable.** -/
theorem diff_product_sound (ρ : EnvR) (x : String) {f g : Expr}
    (hf : DiffAt ρ x f) (hg : DiffAt ρ x g) :
    D ρ x (.mul [f, g])
      = evalD ρ (.add [.mul [.fn "diff" [f, .var x], g], .mul [.fn "diff" [g, .var x], f]]) := by
  have h1 : HasDerivAt (fx ρ x f) (D ρ x f) (ρ x) := hf.hasDerivAt
  have h2 : HasDerivAt (fx ρ x g) (D ρ x g) (ρ x) := hg.hasDerivAt
  have hfun : (fun t => evalD (upd ρ x t) (.mul [f, g])) = (fx ρ x f) * (fx ρ x g) := by
    funext t; show _ = fx ρ x f t * fx ρ x g t; simp
  rw [D_eq]
  show deriv (fun t => evalD (upd ρ x t) (.mul [f, g])) (ρ x) = _
  rw [hfun, (h1.mul h2).deriv]
  simp only [evalD_add, sumD_cons, sumD_nil, evalD_mul, prodD_cons, prodD_nil, evalD_diff, fx,
    upd_self]
  ring

/-- **`diff.power` for a natural exponent**, the case the notebook shows students. Sound wherever
the base is differentiable — no positivity needed, because `Real.rpow_natCast` reduces the engine's
real exponentiation to the monoid power for a natural literal. -/
theorem diff_power_nat_sound (ρ : EnvR) (x : String) {u : Expr} {n : ℕ} (hn : 1 ≤ n)
    (hu : DiffAt ρ x u) :
    D ρ x (.pow u (.num (Q.ofInt (n : ℤ))))
      = evalD ρ (.mul [.num (Q.ofInt (n : ℤ)), .pow u (.num (Q.ofInt ((n : ℤ) - 1))),
                       .fn "diff" [u, .var x]]) := by
  have hcast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; norm_num
  have hpow : (fun t => evalD (upd ρ x t) (.pow u (.num (Q.ofInt (n : ℤ))))) = (fx ρ x u) ^ n := by
    funext t
    show (evalD (upd ρ x t) u) ^ (evalD (upd ρ x t) (.num (Q.ofInt (n : ℤ)))) = (fx ρ x u t) ^ n
    rw [evalD_intLit]
    exact_mod_cast Real.rpow_natCast (evalD (upd ρ x t) u) n
  have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hu.hasDerivAt
  have hexp : evalD ρ (.pow u (.num (Q.ofInt ((n : ℤ) - 1)))) = (evalD ρ u) ^ (n - 1) := by
    show (evalD ρ u) ^ (evalD ρ (.num (Q.ofInt ((n : ℤ) - 1)))) = _
    rw [evalD_intLit]
    have : (((n : ℤ) - 1 : ℤ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [← hcast]; push_cast; ring
    rw [this]
    exact_mod_cast Real.rpow_natCast (evalD ρ u) (n - 1)
  rw [D_eq]
  show deriv (fun t => evalD (upd ρ x t) (.pow u (.num (Q.ofInt (n : ℤ))))) (ρ x) = _
  rw [hpow, (hd.pow n).deriv]
  simp only [evalD_mul, prodD_cons, prodD_nil, evalD_diff, evalD_intLit, hexp, fx, upd_self]
  push_cast
  ring

-- ---------------------------------------------------------------------------
-- `diff.chain`
-- ---------------------------------------------------------------------------

theorem fx_fn (ρ : EnvR) (x : String) (f : String) (u : Expr) :
    fx ρ x (.fn f [u]) = fun t => applyFn f (fx ρ x u t) := rfl

/-- **`diff.chain` for `sin`**, sound wherever the inner function is differentiable. -/
theorem diff_chain_sin_sound (ρ : EnvR) (x : String) {u : Expr} (hu : DiffAt ρ x u) :
    D ρ x (.fn "sin" [u]) = evalD ρ (.mul [.fn "cos" [u], .fn "diff" [u, .var x]]) := by
  have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hu.hasDerivAt
  rw [D_eq, fx_fn]
  simp only [applyFn_sin]
  rw [hd.sin.deriv]
  simp only [evalD_mul, prodD_cons, prodD_nil, evalD_fn, fnD_one, fnD_diff, applyFn_cos, fx, upd_self]
  ring

/-- **`diff.chain` for `cos`.** The rule produces `(-1)·sin(u) · u'`. -/
theorem diff_chain_cos_sound (ρ : EnvR) (x : String) {u : Expr} (hu : DiffAt ρ x u) :
    D ρ x (.fn "cos" [u]) = evalD ρ (.mul [Expr.neg (.fn "sin" [u]), .fn "diff" [u, .var x]]) := by
  have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hu.hasDerivAt
  rw [D_eq, fx_fn]
  simp only [applyFn_cos]
  rw [hd.cos.deriv]
  simp only [Expr.neg, evalD_mul, prodD_cons, prodD_nil, evalD_fn, fnD_one, fnD_diff,
    applyFn_sin, evalD_minusOne, fx, upd_self]
  ring

/-- **`diff.chain` for `exp`.** -/
theorem diff_chain_exp_sound (ρ : EnvR) (x : String) {u : Expr} (hu : DiffAt ρ x u) :
    D ρ x (.fn "exp" [u]) = evalD ρ (.mul [.fn "exp" [u], .fn "diff" [u, .var x]]) := by
  have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hu.hasDerivAt
  rw [D_eq, fx_fn]
  simp only [applyFn_exp]
  rw [hd.exp.deriv]
  simp only [evalD_mul, prodD_cons, prodD_nil, evalD_fn, fnD_one, fnD_diff, applyFn_exp, fx, upd_self]
  ring

-- ---------------------------------------------------------------------------
-- The hypotheses are necessary
-- ---------------------------------------------------------------------------

/-- `|·|` is expressible in the engine's own language, and it is the standard witness that `deriv`
is junk-valued off the differentiable set. -/
theorem fx_abs (ρ : EnvR) (x : String) : fx ρ x (.fn "abs" [.var x]) = fun t => |t| := by
  funext t; simp [fx_fn]

/-- **The sum rule is not unconditionally sound.** At `x = 0`, `|x| + x` is not differentiable, so
the left side is `deriv`'s junk value `0`, while the right side adds the junk derivative of `|x|`
to the genuine derivative of `x` and gets `1`. This is the `diff.*` analogue of M3's
`not_collectPowers_soundR`: the engine keeps the usual rule, and the hypothesis is now written
down in `diff_sum_sound`. -/
theorem not_diff_sum_sound :
    ¬ ∀ (ρ : EnvR) (x : String) (es : List Expr),
        D ρ x (.add es) = evalD ρ (.add (es.map (fun e => .fn "diff" [e, .var x]))) := by
  intro hs
  have key := hs (fun _ => 0) "x" [.fn "abs" [.var "x"], .var "x"]
  -- the left side: `|t| + t` is not differentiable at 0, so `deriv` is junk
  have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => |t| + t) 0 := by
    intro hdd
    have : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
      have := hdd.sub (differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ)))
      simpa using this
    exact not_differentiableAt_abs_zero this
  have hlhs : D (fun _ => 0) "x" (.add [.fn "abs" [.var "x"], .var "x"]) = 0 := by
    rw [D_eq]
    have : fx (fun _ : String => (0 : ℝ)) "x" (.add [.fn "abs" [.var "x"], .var "x"])
        = fun t => |t| + t := by
      funext t; simp [fx, upd]
    rw [this]
    exact deriv_zero_of_not_differentiableAt hnd
  have habs : D (fun _ : String => (0 : ℝ)) "x" (.fn "abs" [.var "x"]) = 0 := by
    rw [D_eq, fx_abs]
    exact deriv_zero_of_not_differentiableAt (by simpa using not_differentiableAt_abs_zero)
  have hvar : D (fun _ : String => (0 : ℝ)) "x" (.var "x") = 1 := by
    have := diff_variable_sound (fun _ : String => (0 : ℝ)) "x"
    simpa using this
  rw [hlhs] at key
  simp only [List.map_cons, List.map_nil, evalD_add, sumD_cons, sumD_nil, evalD_diff,
    habs, hvar] at key
  norm_num at key

end MathProofs
end
