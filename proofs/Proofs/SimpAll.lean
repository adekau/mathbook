import Proofs.Radical
import Proofs.Fourier
/-!
# Every unconditional `simp.*` rule over ℝ

`simp.function` holds for every real number once its two assuming cases are a rule of their own
(`simp.function.assuming`): `sin u/cos u = tan u`, `√a = a^(1/2)`, `ln 1 = 0`, `ln(exp x) = x`,
`ln(b^p) = p ln b` for an integer `p` (Mathlib's `Real.log` is `log |x|`, so a negative `b` is
fine), `exp 0 = 1`, `sin 0 = 0`, `cos 0 = 1`, and `abs` and `sign` of a numeral (`functionRules_soundR`).

With it, simplification by every rule but the two that assume preserves the real value
(`normalizeSafe_sound`): the fold of `RewriteSound`, at ℝ.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Expr

/-- **`simp.function` is sound over ℝ, unconditionally.** -/
theorem functionRules_soundR : RuleSoundR functionRules := by
  intro e res h ρ
  have hna : (functionAssumed e).isNone = true := by
    cases hca : (functionAssumed e).isNone with
    | true => rfl
    | false =>
      simp only [functionRules, Option.isNone_iff_eq_none] at h hca
      simp_all
  have hs := gate_some h
  unfold functionApply at hs
  split at hs
  · -- sin u / cos u = tan u
    rename_i es
    split at hs
    · rename_i u others hft
      cases hs
      exact (functionRules_tan_soundR ρ hft).symm
    · cases hs
  · -- √a = a^(1/2)
    cases hs
    exact (evalR_sqrt_eq_pow ρ _).symm
  · -- ln
    rename_i a
    split at hs
    · rename_i h1
      cases hs
      simp [evalR_of_isOne h1 ρ]
    · split at hs
      · cases hs
        simp [Real.log_exp]
      · rename_i b p
        cases hs
        simp only [functionAssumed, Option.isNone_iff_eq_none, ite_eq_left_iff, reduceCtorEq, imp_false,
          not_not] at hna
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hna
        simp only [evalR_fn₁, applyFn_ln, evalR_pow, evalR_mul, prodR_cons, prodR_nil, mul_one,
          evalR_of_intExp hm, Real.rpow_intCast, Real.log_zpow]
      · cases hs
  · -- exp
    rename_i a
    split at hs
    · rename_i h0
      cases hs
      simp [evalR_of_isZero h0 ρ]
    · split at hs
      · simp [functionAssumed] at hna
      · cases hs
  · -- sin 0
    rename_i a
    split at hs
    · rename_i h0; cases hs; simp [evalR_of_isZero h0 ρ]
    · cases hs
  · -- cos 0
    rename_i a
    split at hs
    · rename_i h0; cases hs; simp [evalR_of_isZero h0 ρ]
    · cases hs
  · -- |q|
    rename_i q
    cases hs
    simp only [evalR_fn₁, evalR_num, applyFn_abs, Q.abs, Rat.abs]
    split_ifs with hq
    · exact abs_of_nonneg (by exact_mod_cast hq)
    · rw [Rat.cast_neg]; exact abs_of_neg (by exact_mod_cast lt_of_not_ge hq)
  · -- sign q
    rename_i q
    cases hs
    exact (sign_fold_soundR ρ q).symm
  · cases hs

/-- `simpRules` without the two rules that assume. -/
def simpRulesSafe : List (Rule simpW) :=
  [flatten, identity, foldConstants, functionRules, powerRules, collectPowers, collectTerms]

theorem simpRulesSafe_soundR : ∀ r ∈ simpRulesSafe, RuleSoundR r := by
  intro r hr
  simp only [simpRulesSafe, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact flatten_soundR
  · exact identity_soundR
  · exact foldConstants_soundR
  · exact functionRules_soundR
  · exact powerRules_soundR
  · exact collectPowers_soundR
  · exact collectTerms_soundR

/-- **Simplifying with every rule but the two that assume preserves the real value.** -/
theorem normalizeSafe_sound (e : Expr) (s : Array Step) :
    SemEqR e ((normalize simpRulesSafe e).run' s) :=
  normalize_sound_for semEqRCongruence simpRulesSafe simpRulesSafe_soundR e s

end MathProofs
end
