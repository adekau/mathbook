import Proofs.Integrate
import Proofs.CxRules
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# The Fourier milestone: substitution, finite sums, Euler as a command, definite integrals

Four small readings the notebook's new commands need.

* `substVar` — the structural substitution `e[x := v]` — evaluates as an environment update, over
  ℝ and over ℂ. There are no binders in the scalar language, so this is plain induction.
* `sum(f, k, a, b)` is a definition (`cmdSum_spec`); `sum_soundR` reads it as the finite sum over
  ℝ, `∑ j < n, f[k := a + j]`.
* `exptotrig` applies Euler's formula everywhere at once (`expToTrig`); over ℂ it never changes a
  value (`expToTrig_soundC`: `Complex.exp_mul_I`, with `cos_neg`/`sin_neg` for a negated angle).
* `integrate(f, x, a, b)` returns `F[x := b] − F[x := a]` for a checked antiderivative `F`
  (`cmdIntegrate_definite_spec`). `integrate_definite` is the fundamental theorem of calculus
  read through the engine: if `F` is differentiable on `[a, b]` as a function of `x` and the
  integrand is interval-integrable, the interval integral of the integrand equals the value the
  command returned. The differentiability hypothesis is not decoration: `deriv` of a function that
  is not differentiable is the junk value 0, and `integrate_deriv` (M8) speaks about `deriv`.
-/
noncomputable section
namespace MathProofs
open MathEngine
open Complex (I)

/-! ## Substitution -/

mutual
  theorem substVar_soundR (ρ : EnvR) (x : String) (v : Expr) :
      ∀ e : Expr, evalR ρ (substVar x v e) = evalR (upd ρ x (evalR ρ v)) e
    | .num _ => rfl
    | .var y => by
      simp only [substVar]
      by_cases h : y = x
      · subst h; simp
      · simp [h, upd, upd_other]
    | .add es => by simp only [substVar, evalR_add]; exact substVarList_soundR ρ x v es
    | .mul es => by simp only [substVar, evalR_mul]; exact substVarList_soundR' ρ x v es
    | .pow b e => by simp only [substVar, evalR_pow, substVar_soundR ρ x v b, substVar_soundR ρ x v e]
    | .fn f es => by
      simp only [substVar]
      match es with
      | [] => rfl
      | [a] =>
        have := substVar_soundR ρ x v a
        simp only [substVarList, evalR_fn₁, this]
      | _ :: _ :: _ => simp [substVarList, evalR]
    | .matrix _ => rfl
  theorem substVarList_soundR (ρ : EnvR) (x : String) (v : Expr) :
      ∀ es : List Expr, sumR ρ (substVarList x v es) = sumR (upd ρ x (evalR ρ v)) es
    | [] => rfl
    | e :: es => by simp only [substVarList, sumR_cons, substVar_soundR ρ x v e, substVarList_soundR ρ x v es]
  theorem substVarList_soundR' (ρ : EnvR) (x : String) (v : Expr) :
      ∀ es : List Expr, prodR ρ (substVarList x v es) = prodR (upd ρ x (evalR ρ v)) es
    | [] => rfl
    | e :: es => by simp only [substVarList, prodR_cons, substVar_soundR ρ x v e, substVarList_soundR' ρ x v es]
end

def updC (ρ : EnvC) (x : String) (t : ℂ) : EnvC := fun y => if y = x then t else ρ y

mutual
  theorem substVar_soundC (ρ : EnvC) (x : String) (v : Expr) :
      ∀ e : Expr, evalC ρ (substVar x v e) = evalC (updC ρ x (evalC ρ v)) e
    | .num _ => rfl
    | .var y => by
      simp only [substVar]
      by_cases h : y = x
      · subst h; simp [updC]
      · simp [h, updC]
    | .add es => by simp only [substVar, evalC_add]; exact substVarList_soundC ρ x v es
    | .mul es => by simp only [substVar, evalC_mul]; exact substVarList_soundC' ρ x v es
    | .pow b e => by simp only [substVar, evalC_pow, substVar_soundC ρ x v b, substVar_soundC ρ x v e]
    | .fn f es => by
      simp only [substVar]
      match es with
      | [] => rfl
      | [a] =>
        have := substVar_soundC ρ x v a
        simp only [substVarList, evalC_fn₁, this]
      | _ :: _ :: _ => simp [substVarList, evalC]
    | .matrix _ => rfl
  theorem substVarList_soundC (ρ : EnvC) (x : String) (v : Expr) :
      ∀ es : List Expr, sumC ρ (substVarList x v es) = sumC (updC ρ x (evalC ρ v)) es
    | [] => rfl
    | e :: es => by simp only [substVarList, sumC_cons, substVar_soundC ρ x v e, substVarList_soundC ρ x v es]
  theorem substVarList_soundC' (ρ : EnvC) (x : String) (v : Expr) :
      ∀ es : List Expr, prodC ρ (substVarList x v es) = prodC (updC ρ x (evalC ρ v)) es
    | [] => rfl
    | e :: es => by simp only [substVarList, prodC_cons, substVar_soundC ρ x v e, substVarList_soundC' ρ x v es]
end

/-! ## `sign` of a numeral -/

/-- The `simp.function` arm for `sign(q)` agrees with `Real.sign`. -/
theorem sign_fold_soundR (ρ : EnvR) (q : Q) :
    evalR ρ (.num (if q.isNeg then Q.minusOne else if q.isZero then Q.zero else Q.one)) =
      evalR ρ (.fn "sign" [.num q]) := by
  simp only [evalR_fn₁, evalR_num, applyFn_sign]
  by_cases hneg : q.isNeg = true
  · have : q.val < 0 := by simpa [Q.isNeg, Rat.num_neg] using hneg
    rw [if_pos hneg, Real.sign_of_neg (by exact_mod_cast this)]; simp [Q.minusOne, Q.ofInt]
  · rw [if_neg hneg]
    have hnn : 0 ≤ q.val := by simpa [Q.isNeg, Rat.num_neg, not_lt] using hneg
    by_cases hz : q.isZero = true
    · rw [if_pos hz, Q_val_of_isZero hz]; simp
    · rw [if_neg hz]
      have hne : q.val ≠ 0 := fun h0 => hz (by simp [Q.isZero, h0])
      have : 0 < q.val := lt_of_le_of_ne hnn (Ne.symm hne)
      rw [Real.sign_of_pos (by exact_mod_cast this)]; simp

/-! ## Finite sums -/

theorem sumR_map (ρ : EnvR) (g : ℕ → Expr) : ∀ (l : List ℕ),
    sumR ρ (l.map g) = (l.map fun j => evalR ρ (g j)).sum
  | [] => rfl
  | j :: l => by simp only [List.map_cons, sumR_cons, List.sum_cons, sumR_map ρ g l]

/-- **`sum` over ℝ**: the value of `sum(f, k, a, b)` is `∑_{j < b − a + 1} f[k := a + j]`. -/
theorem sum_soundR (ρ : EnvR) (f : Expr) (k : String) (a b : ℤ) :
    evalR ρ (Expr.addN (sumTerms f k a b)) =
      ∑ j ∈ Finset.range (b - a + 1).toNat, evalR (upd ρ k ((a + j : ℤ) : ℝ)) f := by
  rw [evalR_addN, sumTerms, sumR_map]
  have hfun : (fun j : ℕ => evalR ρ (substVar k (.num (Q.ofInt (a + j))) f)) =
      fun j : ℕ => evalR (upd ρ k ((a + j : ℤ) : ℝ)) f := by
    funext j; rw [substVar_soundR]; simp only [evalR_num, Q_val_ofInt]; push_cast; rfl
  rw [hfun]; rfl

/-! ## Euler as a command, over ℂ -/

theorem negOf_spec (ρ : EnvC) {θ θ' : Expr} (h : negOf θ = some θ') : evalC ρ θ = -evalC ρ θ' := by
  unfold negOf at h
  split at h
  · rename_i q
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · simp at h
  · rename_i q rest
    split at h
    · simp only [Option.some.injEq] at h; subst h
      simp only [evalC_mul, prodC_cons, evalC_mulN]
      split
      · rename_i hone
        have h1 : (Q.zero - q).val = 1 := Q_val_of_isOne hone
        rw [Q_val_sub, Q_val_zero, zero_sub] at h1
        have hq : q.val = -1 := by linarith
        simp [hq]
      · simp only [prodC_cons, evalC_num, Q_val_sub, Q_val_zero]; push_cast; ring
    · simp at h
  · simp at h

theorem expToTrigList_map : ∀ es : List Expr, expToTrigList es = es.map expToTrig
  | [] => rfl
  | e :: es => by simp only [expToTrigList, List.map_cons, expToTrigList_map es]

/-- The value of Euler's right-hand side, as `expToTrig` writes it. -/
theorem euler_rhs (ρ : EnvC) (θ : Expr) :
    evalC ρ (.add [.fn "cos" [θ], .mul [.fn "sin" [θ], iE]]) = Complex.exp (evalC ρ θ * I) := by
  rw [Complex.exp_mul_I]; simp

theorem euler_rhs_neg (ρ : EnvC) (θ' : Expr) :
    evalC ρ (.add [.fn "cos" [θ'], .mul [Expr.minusOne, .fn "sin" [θ'], iE]]) = Complex.exp (-evalC ρ θ' * I) := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; simp [Expr.minusOne, Q.minusOne]

mutual
  /-- **`exptotrig` is sound over ℂ.** -/
  theorem expToTrig_soundC (ρ : EnvC) : ∀ e : Expr, evalC ρ (expToTrig e) = evalC ρ e
    | .num _ => rfl
    | .var _ => rfl
    | .add es => by simp only [expToTrig, evalC_add]; exact expToTrigList_soundC ρ es
    | .mul es => by simp only [expToTrig, evalC_mul]; exact expToTrigList_soundC' ρ es
    | .pow b e => by simp only [expToTrig, evalC_pow, expToTrig_soundC ρ b, expToTrig_soundC ρ e]
    | .fn f es => by
      simp only [expToTrig]
      match es with
      | [] => simp [expToTrigList]
      | [a] =>
        have ha := expToTrig_soundC ρ a
        simp only [expToTrigList]
        by_cases hf : f = "exp"
        · subst hf
          simp only
          split
          · rename_i θ hθ
            have hu := imagArg_spec ρ hθ
            split
            · rename_i θ' hθ'
              rw [euler_rhs_neg, evalC_fn₁, applyFnC_exp, ← ha, hu, negOf_spec ρ hθ']; ring_nf
            · rw [euler_rhs, evalC_fn₁, applyFnC_exp, ← ha, hu]; ring_nf
          · simp [ha]
        · simp [hf, ha]
      | _ :: _ :: _ => simp [expToTrigList, evalC]
    | .matrix _ => rfl
  theorem expToTrigList_soundC (ρ : EnvC) : ∀ es : List Expr, sumC ρ (expToTrigList es) = sumC ρ es
    | [] => rfl
    | e :: es => by simp only [expToTrigList, sumC_cons, expToTrig_soundC ρ e, expToTrigList_soundC ρ es]
  theorem expToTrigList_soundC' (ρ : EnvC) : ∀ es : List Expr, prodC ρ (expToTrigList es) = prodC ρ es
    | [] => rfl
    | e :: es => by simp only [expToTrigList, prodC_cons, expToTrig_soundC ρ e, expToTrigList_soundC' ρ es]
end

/-! ## The definite integral: the fundamental theorem of calculus, read through the engine -/

theorem upd_upd (ρ : EnvR) (x : String) (s t : ℝ) : upd (upd ρ x s) x t = upd ρ x t := by
  funext y; simp only [upd]; split <;> rfl

theorem fx_upd (ρ : EnvR) (x : String) (s : ℝ) (F : Expr) : fx (upd ρ x s) x F = fx ρ x F := by
  funext t; simp only [fx, upd_upd]

/-- The value of `definite F x a b` over ℝ, for a `diff`-free `F`: `F(b) − F(a)` as a function of `x`. -/
theorem definite_evalR (ρ : EnvR) {F : Expr} (hF : DiffFree F) (x : String) (a b : Expr) :
    evalR ρ (definite F x a b) = fx ρ x F (evalR ρ b) - fx ρ x F (evalR ρ a) := by
  simp only [definite, Expr.sub, Expr.neg, evalR_add, sumR_cons, sumR_nil, evalR_mul, prodR_cons, prodR_nil,
    substVar_soundR, fx, evalD_eq_evalR _ hF, Expr.minusOne, Q.minusOne, evalR_num, Q_val_ofInt]
  push_cast; ring

/-- **The fundamental theorem of calculus, through the engine.** `integrate(f, x, a, b)` returns a
term whose value is `∫_a^b f`, at every environment where (i) the accepted antiderivative `F` is
differentiable in `x` on `[a, b]`, (ii) the integrand is interval-integrable, and (iii) the three
normalizations the checker ran are sound at each point of `[a, b]` — the hypotheses of
`integrate_deriv` (M8), which the rule statuses of the derivation account for. -/
theorem integrate_definite (norm : Norm) {f a b : Expr} {x : String} {res : RuleResult}
    (h : (cmdIntegrate norm).apply (.fn "integrate" [f, .var x, a, b]) = some res) (hok : res.error = none) :
    ∃ F, res.result = definite F x a b ∧ ∀ ρ : EnvR, DiffFree F →
      (∀ t ∈ Set.uIcc (evalR ρ a) (evalR ρ b), DifferentiableAt ℝ (fx ρ x F) t) →
      IntervalIntegrable (fun t => evalD (upd ρ x t) f) MeasureTheory.volume (evalR ρ a) (evalR ρ b) →
      (∀ t ∈ Set.uIcc (evalR ρ a) (evalR ρ b),
        (∀ g sub, norm (MathEngine.D F x) = .ok (g, sub) → evalD (upd ρ x t) (MathEngine.D F x) = evalD (upd ρ x t) g) ∧
        (∀ g sub g' s, norm (MathEngine.D F x) = .ok (g, sub) →
          norm (Expand.dist (Expand.identNorm g)) = .ok (g', s) →
          evalD (upd ρ x t) (Expand.dist (Expand.identNorm g)) = evalD (upd ρ x t) g') ∧
        (∀ f' s, norm (Expand.dist (Expand.identNorm f)) = .ok (f', s) →
          evalD (upd ρ x t) (Expand.dist (Expand.identNorm f)) = evalD (upd ρ x t) f')) →
      ∫ t in (evalR ρ a)..(evalR ρ b), evalD (upd ρ x t) f = evalR ρ res.result := by
  obtain ⟨F, hres, g, sub, g', s₁, s₂, h₁, h₂, h₃⟩ := cmdIntegrate_definite_spec norm h hok
  refine ⟨F, hres, fun ρ hF hdiff hint hsound => ?_⟩
  rw [hres, definite_evalR ρ hF]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  obtain ⟨hd, hl, hr⟩ := hsound t ht
  have hderiv : deriv (fx ρ x F) t = evalD (upd ρ x t) f := by
    have key : deriv (fx (upd ρ x t) x F) ((upd ρ x t) x) = evalD (upd ρ x t) f := by
      rw [← D_eq, ← evalD_diff]
      show evalD (upd ρ x t) (MathEngine.D F x) = _
      rw [hd g sub h₁, ← identNorm_soundD g _, ← dist_soundD (Expand.identNorm g) _, hl g sub g' s₁ h₁ h₂,
        ← hr g' s₂ h₃, dist_soundD, identNorm_soundD]
    rwa [fx_upd, upd_same] at key
  rw [← hderiv]
  exact (hdiff t ht).hasDerivAt

end MathProofs
end
