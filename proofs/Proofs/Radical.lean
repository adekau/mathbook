import Proofs.SimpReal
/-!
# The radical rules are sound over ℝ

`simp.radical` and `simp.collect-radicals` (engine, `RadicalRules.lean`) are unconditional: their
bases are integers ≥ 2, so every real power involved is a power of a positive number, where
`Real.rpow_add`, `Real.rpow_mul` and `Real.mul_rpow` hold without side conditions.
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expr

theorem perfectPower_spec {a r k : ℕ} (h : perfectPower a = some (r, k)) : r ^ k = a := by
  unfold perfectPower at h
  obtain ⟨k', _, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · rename_i hk2
    obtain ⟨r', hr', hrk⟩ := Option.map_eq_some_iff.mp hk
    simp only [Prod.mk.injEq] at hrk; obtain ⟨rfl, rfl⟩ := hrk
    exact natRoot_pow (by omega) hr'
  · simp at hk

/-- `qthPowerPart b q = (m, s)` has `m ^ q * s = b` and `1 ≤ m`. -/
theorem qthPowerPart_spec (b q : ℕ) :
    (qthPowerPart b q).1 ^ q * (qthPowerPart b q).2 = b ∧ 1 ≤ (qthPowerPart b q).1 := by
  unfold qthPowerPart
  simp only
  cases hf : (List.range (2 ^ (Nat.log2 b / q + 1) + 1)).reverse.find? (fun m => m ≥ 1 && b % (m ^ q) == 0) with
  | none => simp
  | some m =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨hm, hdvd⟩ := hp
    simp only [Option.getD_some]
    exact ⟨Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdvd), hm⟩

theorem Q_val_zpow (a : Q) (n : ℤ) : (a.zpow n).val = a.val ^ n := rfl

/-- An integer numeral ≥ 2 is a positive real. -/
theorem Q_pos_of_ge_two {b : Q} (hint : b.isInt = true) (h2 : b.val.num ≥ 2) : (0 : ℝ) < (b.val : ℝ) := by
  rw [Q_cast_isInt hint]; exact_mod_cast (by omega : (0 : ℤ) < b.val.num)

theorem rat_cast_num_den (x : ℚ) : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
  exact_mod_cast (Rat.num_div_den x).symm

/-- `x = i + f/q` for `q = x.den`, `i = x.num / q`, `f = x.num % q`, as reals. -/
theorem rat_split (x : ℚ) : (x : ℝ) = ((x.num / x.den : ℤ) : ℝ) + ((x.num % x.den : ℤ) : ℝ) / (x.den : ℝ) := by
  have hd : (x.den : ℝ) ≠ 0 := by exact_mod_cast x.den_pos.ne'
  have h := Int.emod_def x.num x.den
  have hc : ((x.num % x.den : ℤ) : ℝ) = (x.num : ℝ) - (x.den : ℝ) * ((x.num / x.den : ℤ) : ℝ) := by
    exact_mod_cast h
  rw [rat_cast_num_den]
  field_simp
  linear_combination -hc

theorem radicalTerm_spec (ρ : EnvR) {s : Expr} {k b x : Q} (h : radicalTerm s = some (k, b, x)) :
    evalR ρ s = (k.val : ℝ) * (b.val : ℝ) ^ (x.val : ℝ) ∧ b.isInt = true ∧ b.val.num ≥ 2 ∧ x.isInt = false := by
  unfold radicalTerm at h
  split at h
  · split at h
    · rename_i hg
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      refine ⟨?_, hg.1.1, hg.1.2, hg.2⟩
      simp [Q_val_one]
    · simp at h
  · split at h
    · rename_i hg
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      refine ⟨?_, hg.1.1, hg.1.2, hg.2⟩
      simp
    · simp at h
  · simp at h

/-- `b^x = b^i · b^(f/q)` for a positive base. -/
theorem rpow_split {b : ℝ} (hb : 0 < b) (x : ℚ) :
    b ^ (x : ℝ) = b ^ ((x.num / x.den : ℤ)) * b ^ ((((x.num % x.den : ℤ) : ℝ)) / (x.den : ℝ)) := by
  rw [rat_split x, Real.rpow_add hb, Real.rpow_intCast]

/-- `b^x = m^p · s^i · s^(f/q)` for `b = m^q s`, `x = p/q`, `p = i q + f`. -/
theorem rpow_decompose {b : ℝ} (hb : 0 < b) {m s q : ℕ} (hq : q ≠ 0) (hm : 1 ≤ m)
    (hbms : (m : ℝ) ^ q * (s : ℝ) = b) (x : ℚ) (hden : x.den = q) :
    b ^ (x : ℝ) = (m : ℝ) ^ (x.num) * ((s : ℝ) ^ ((x.num / (q : ℤ))) * (s : ℝ) ^ ((((x.num % (q : ℤ)) : ℤ) : ℝ) / (q : ℝ))) := by
  subst hden
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (0 : ℝ) < s := by
    have : (0 : ℝ) < (m : ℝ) ^ x.den * (s : ℝ) := hbms ▸ hb
    exact pos_of_mul_pos_right this (by positivity)
  rw [← hbms, Real.mul_rpow (by positivity) hs.le, ← rpow_split hs x]
  congr 1
  rw [← Real.rpow_natCast (m : ℝ) x.den, ← Real.rpow_mul hmpos.le, ← Real.rpow_intCast]
  congr 1
  rw [rat_cast_num_den]
  have hq' : (x.den : ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp

theorem mergeRadicals_soundR (ρ : EnvR) {s t m : Expr} (h : mergeRadicals s t = some m) :
    evalR ρ m = evalR ρ s + evalR ρ t := by
  unfold mergeRadicals at h
  dsimp only at h
  split at h
  · rename_i k₁ b₁ x₁ k₂ b₂ x₂ hs ht
    obtain ⟨es, hb1, hb2, _⟩ := radicalTerm_spec ρ hs
    obtain ⟨et, hb1', hb2', _⟩ := radicalTerm_spec ρ ht
    have hq : x₁.val.den ≠ 0 := x₁.val.den_pos.ne'
    obtain ⟨hp1, hm1⟩ := qthPowerPart_spec b₁.val.num.toNat x₁.val.den
    obtain ⟨hp2, hm2⟩ := qthPowerPart_spec b₂.val.num.toNat x₁.val.den
    generalize hP1 : qthPowerPart b₁.val.num.toNat x₁.val.den = P₁ at hp1 hm1 h
    generalize hP2 : qthPowerPart b₂.val.num.toNat x₁.val.den = P₂ at hp2 hm2 h
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨⟨hden, hsq⟩, hmod⟩ := hg
      have hpos1 := Q_pos_of_ge_two hb1 hb2
      have hpos2 := Q_pos_of_ge_two hb1' hb2'
      have hcast1 : (P₁.1 : ℝ) ^ x₁.val.den * (P₁.2 : ℝ) = (b₁.val : ℝ) := by
        rw [Q_cast_isInt hb1]
        have : ((P₁.1 ^ x₁.val.den * P₁.2 : ℕ) : ℤ) = b₁.val.num := by rw [hp1]; exact Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have hcast2 : (P₂.1 : ℝ) ^ x₁.val.den * (P₂.2 : ℝ) = (b₂.val : ℝ) := by
        rw [Q_cast_isInt hb1']
        have : ((P₂.1 ^ x₁.val.den * P₂.2 : ℕ) : ℤ) = b₂.val.num := by rw [hp2]; exact Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [es, et, rpow_decompose hpos1 hq hm1 hcast1 x₁.val rfl, rpow_decompose hpos2 hq hm2 hcast2 x₂.val hden,
        ← hsq, ← hmod]
      have hrad : ((Q.ofRat (mkRat (x₁.val.num % ↑x₁.val.den) x₁.val.den)).val : ℝ)
          = ((x₁.val.num % x₁.val.den : ℤ) : ℝ) / (x₁.val.den : ℝ) := by
        simp [Q.ofRat, Rat.mkRat_eq_div]
      set c : Q := k₁ * (Q.ofInt ↑P₁.1).zpow x₁.val.num * (Q.ofInt ↑P₁.2).zpow (x₁.val.num / ↑x₁.val.den)
            + k₂ * (Q.ofInt ↑P₂.1).zpow x₂.val.num * (Q.ofInt ↑P₁.2).zpow (x₂.val.num / ↑x₁.val.den) with hcdef
      have hc : (c.val : ℝ) = (k₁.val : ℝ) * (P₁.1 : ℝ) ^ x₁.val.num * (P₁.2 : ℝ) ^ ((x₁.val.num / x₁.val.den : ℤ))
            + (k₂.val : ℝ) * (P₂.1 : ℝ) ^ x₂.val.num * (P₁.2 : ℝ) ^ ((x₂.val.num / x₁.val.den : ℤ)) := by
        simp only [hcdef, Q_val_add, Q_val_mul, Q_val_zpow, Q_val_ofInt]; push_cast; ring
      set F : ℝ := (P₁.2 : ℝ) ^ ((((x₁.val.num % x₁.val.den : ℤ) : ℝ)) / (x₁.val.den : ℝ)) with hF
      split
      · rename_i h1
        have hS1 : P₁.2 = 1 := by simpa using h1
        simp only [evalR_num, hc, hS1, hF]; push_cast; simp
      · split
        · rename_i hz
          have hcz : c.val = 0 := by simpa [Q.isZero] using hz
          rw [hcz] at hc; push_cast at hc
          simp only [evalR_zero]
          linear_combination hc * F
        · split
          · rename_i ho
            have hco : c.val = 1 := by simpa [Q.isOne] using ho
            rw [hco] at hc; push_cast at hc
            simp only [evalR_pow, evalR_num, hrad, Q_val_ofInt]; push_cast
            rw [← hF]
            linear_combination hc * F
          · simp only [evalR_mul, prodR_cons, prodR_nil, evalR_num, evalR_pow, hrad, Q_val_ofInt, mul_one]
            rw [hc]; push_cast; rw [← hF]; ring
    · simp at h
  · simp at h

theorem mulRadicalPair_soundR (ρ : EnvR) {s t m : Expr} (h : mulRadicalPair s t = some m) :
    evalR ρ m = evalR ρ s * evalR ρ t := by
  unfold mulRadicalPair at h
  split at h
  · rename_i a x b y
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hg
      obtain ⟨⟨⟨⟨⟨⟨ha, ha2⟩, hb⟩, hb2⟩, _⟩, _⟩, hden⟩ := hg
      have hpa := Q_pos_of_ge_two ha ha2
      have hpb := Q_pos_of_ge_two hb hb2
      simp only [evalR_pow, evalR_num, Q_val_mul, Q_val_zpow]
      have hq : ((Q.ofRat (mkRat 1 x.val.den)).val : ℝ) = 1 / (x.val.den : ℝ) := by
        simp [Q.ofRat, Rat.mkRat_eq_div]
      rw [hq]; push_cast
      rw [Real.mul_rpow (zpow_nonneg hpa.le _) (zpow_nonneg hpb.le _)]
      rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hpa.le, ← Real.rpow_mul hpb.le]
      congr 2
      · rw [rat_cast_num_den]; ring
      · rw [rat_cast_num_den, hden]; ring
    · simp at h
  · simp at h

theorem radicalBase_soundR (ρ : EnvR) {e : Expr} {res : RuleResult} (h : radicalBase.apply e = some res) :
    evalR ρ res.result = evalR ρ e := by
  simp only [radicalBase] at h
  split at h
  · rename_i a q
    split at h
    · rename_i hg
      split at h
      · rename_i r k hpp
        split at h
        · simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
          obtain ⟨⟨ha, ha2⟩, _⟩ := hg
          have hrk := perfectPower_spec hpp
          simp only [evalR_pow, evalR_num, Q_val_mul, Q_val_ofInt]
          push_cast
          rw [mul_comm, Real.rpow_natCast_mul (by positivity), Q_cast_isInt ha]
          congr 2
          have hz : ((r ^ k : ℕ) : ℤ) = a.val.num := by rw [hrk]; exact Int.toNat_of_nonneg (by omega)
          exact_mod_cast hz
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem collectRadicals_soundR (ρ : EnvR) {e : Expr} {res : RuleResult} (h : collectRadicals.apply e = some res) :
    evalR ρ res.result = evalR ρ e := by
  simp only [collectRadicals] at h
  split at h
  · rename_i es
    split at h
    · rename_i m others hfp
      split at h
      · simp only [Option.some.injEq] at h; subst h
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        rw [evalR_addN, evalR_add, sumR_perm ρ hperm, sumR_cons, sumR_cons, sumR_cons, mergeRadicals_soundR ρ hst]
        ring
      · simp at h
    · simp at h
  · simp at h

theorem mulRadicals_soundR (ρ : EnvR) {e : Expr} {res : RuleResult} (h : mulRadicals.apply e = some res) :
    evalR ρ res.result = evalR ρ e := by
  simp only [mulRadicals] at h
  split at h
  · rename_i es
    split at h
    · rename_i m others hfp
      split at h
      · simp only [Option.some.injEq] at h; subst h
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        rw [evalR_mulN, evalR_mul, prodR_perm ρ hperm, prodR_cons, prodR_cons, prodR_cons, mulRadicalPair_soundR ρ hst]
        ring
      · simp at h
    · simp at h
  · simp at h

end MathProofs
end
