import Proofs.Deriv
import Proofs.Expand
/-!
# `integrate` as a verified checker: the semantic reading (M8)

The engine proves `cmdIntegrate_spec`: an accepted antiderivative `F` of `f` has
`norm (dist (norm (diff F x))) = norm (dist f)`, exactly. Here that becomes the statement the
milestone names, `deriv F = f`, under the hypothesis that the three normalizations the checker ran
are sound at the point — `evalD ρ e = evalD ρ g` for each input `e` and normal form `g`. That
hypothesis is not assumed away; it is what the rule statuses of those derivations say (M3 for
`simp.*`, M4 for `diff.*`), rule by rule, and the notebook shows them under the `int.check` and
`int.compare` steps. The distribution in between needs no hypothesis: `dist_soundD` below.

So the checker is verified in the sense that matters: nothing about the *finder* is trusted, and
what remains to trust is exactly the rewriting shown, which the notebook already accounts for.
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expand

/-! ## `dist` is sound for the derivative semantics too -/

theorem sumD_eq_sum (ρ : EnvR) (es : List Expr) : sumD ρ es = (es.map (evalD ρ)).sum := by
  induction es with
  | nil => simp
  | cons f fs ih => simp [ih]

theorem prodD_eq_prod (ρ : EnvR) (fs : List Expr) : prodD ρ fs = (fs.map (evalD ρ)).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [ih]

/-- The derivative semantics as a `Sem`. -/
def semD : Sem where
  ev := evalD
  ev_add := fun ρ es => by rw [evalD_add, sumD_eq_sum]
  ev_mul := fun ρ es => by rw [evalD_mul, prodD_eq_prod]
  ev_num := fun _ _ => rfl
  ev_pow := fun _ _ _ => rfl

theorem evalD_distMul (ρ : EnvR) (fs : List Expr) : evalD ρ (distMul fs) = prodD ρ fs := by
  have := ev_distMul semD ρ fs; simp only [semD] at this; rw [this, prodD_eq_prod]

theorem evalD_powCopies (ρ : EnvR) (b e : Expr) : evalD ρ (powCopies b e) = evalD ρ (.pow b e) :=
  ev_powCopies semD ρ b e

/-- `dist` never turns a non-variable into a variable, so the binder position of `diff` is kept. -/
theorem dist_var_iff (v : Expr) (y : String) : Expand.dist v = .var y ↔ v = .var y := by
  cases v <;> simp only [Expand.dist, distMul, powCopies, ofPoly] <;> (repeat' split) <;> simp

theorem sumD_flatAdd (ρ : EnvR) (es : List Expr) : sumD ρ (Expand.flatAdd es) = sumD ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [Expand.flatAdd, sumD_cons, sumD_append, evalD_add, ih]

mutual
  /-- **`dist` is sound for `evalD`**, hence under a `diff`. -/
  theorem dist_soundD : ∀ (e : Expr) (ρ : EnvR), evalD ρ (Expand.dist e) = evalD ρ e
    | .num _, _ => rfl
    | .var _, _ => rfl
    | .add es, ρ => by simp only [Expand.dist, evalD_add]; rw [sumD_flatAdd]; exact (distList_soundD es ρ).1
    | .mul es, ρ => by simp only [Expand.dist]; rw [evalD_distMul, evalD_mul]; exact (distList_soundD es ρ).2
    | .pow b e, ρ => by simp only [Expand.dist]; rw [evalD_powCopies, evalD_pow, evalD_pow, dist_soundD b ρ, dist_soundD e ρ]
    | .fn f es, ρ => by
      simp only [Expand.dist]
      match es with
      | [] => rfl
      | [a] =>
        have h := (distList_soundD [a] ρ).1
        simp only [distList, sumD_cons, sumD_nil, add_zero] at h
        simp only [distList, evalD_fn, fnD_one, h]
      | [g, v] =>
        simp only [distList, evalD_fn, fnD_two]
        split
        · split
          · rename_i x hx
            have hv := (dist_var_iff v x).1 hx
            subst hv
            show deriv (fun t => evalD (upd ρ x t) (Expand.dist g)) (ρ x) = deriv (fun t => evalD (upd ρ x t) g) (ρ x)
            congr 1; funext t
            have := (distList_soundD [g] (upd ρ x t)).1
            simpa [distList] using this
          · rename_i hne
            split
            · rename_i y; exact (hne y (by simp [Expand.dist])).elim
            · rfl
        · rfl
      | _ :: _ :: _ :: _ => rfl
    | .matrix _, _ => rfl
  theorem distList_soundD : ∀ (es : List Expr) (ρ : EnvR),
      sumD ρ (distList es) = sumD ρ es ∧ prodD ρ (distList es) = prodD ρ es
    | [], _ => ⟨rfl, rfl⟩
    | e :: es, ρ => by
      obtain ⟨hs, hp⟩ := distList_soundD es ρ
      simp only [distList, sumD_cons, prodD_cons, dist_soundD e ρ, hs, hp]; exact ⟨trivial, trivial⟩
end

/-! ## The checker -/

/-- `deriv (integrate f) = f`: the derivative of an accepted antiderivative, read as a function of
`x`, is the integrand at every point where the checker's three normalizations were sound. -/
theorem integrate_deriv (norm : Norm) {f : Expr} {x : String} {res : RuleResult}
    (h : (cmdIntegrate norm).apply (.fn "integrate" [f, .var x]) = some res) (hok : res.error = none)
    (ρ : EnvR)
    (hdiff : ∀ g sub, norm (MathEngine.D res.result x) = .ok (g, sub) →
      evalD ρ (MathEngine.D res.result x) = evalD ρ g)
    (hleft : ∀ g sub g' s, norm (MathEngine.D res.result x) = .ok (g, sub) → norm (Expand.dist g) = .ok (g', s) →
      evalD ρ (Expand.dist g) = evalD ρ g')
    (hright : ∀ f' s, norm (Expand.dist f) = .ok (f', s) → evalD ρ (Expand.dist f) = evalD ρ f') :
    deriv (fx ρ x res.result) (ρ x) = evalD ρ f := by
  obtain ⟨g, sub, g', s₁, s₂, h₁, h₂, h₃⟩ := cmdIntegrate_spec norm h hok
  rw [← D_eq, ← evalD_diff]
  show evalD ρ (MathEngine.D res.result x) = _
  rw [hdiff g sub h₁, ← dist_soundD g ρ, hleft g sub g' s₁ h₁ h₂, ← hright g' s₂ h₃, dist_soundD]

end MathProofs
end
