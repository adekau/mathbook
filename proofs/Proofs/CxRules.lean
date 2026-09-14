import Proofs.Cx
/-!
# The complex rules are sound over ℂ; the exact trigonometric values over ℝ and ℂ
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expr

theorem Q_val_of_isZero {q : Q} (h : q.isZero = true) : q.val = 0 := by simpa [Q.isZero] using h
theorem Q_val_of_isOne {q : Q} (h : q.isOne = true) : q.val = 1 := by simpa [Q.isOne] using h
theorem Q_val_of_eq_minusOne {q : Q} (h : q.eq Q.minusOne = true) : q.val = -1 := by
  simpa [Q.eq, Q.minusOne, Q.ofInt] using h
@[simp] theorem Q_val_neg (a : Q) : (a.neg).val = -a.val := rfl
@[simp] theorem Q_val_sub (a b : Q) : (a - b : Q).val = a.val - b.val := by
  show (a.add b.neg).val = _; simp [Q.add, Q.neg, sub_eq_add_neg]
@[simp] theorem Q_val_div (a b : Q) : (a / b : Q).val = a.val / b.val := rfl
@[simp] theorem Q_val_ofRat (r : ℚ) : (Q.ofRat r).val = r := rfl

/-- A guarded rule returned its candidate. -/
theorem guarded_result {res e : Expr} {why : String} {r : RuleResult} (h : guarded res e why = some r) :
    r.result = res := by
  unfold guarded at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

end MathProofs

namespace MathEngine.Gauss
open MathProofs
open Complex (I)

/-- `re + im·i` as a complex number. -/
def toC (g : Gauss) : ℂ := (g.re.val : ℂ) + (g.im.val : ℂ) * Complex.I

@[simp] theorem toC_re (g : Gauss) : g.toC.re = (g.re.val : ℝ) := by simp [toC]
@[simp] theorem toC_im (g : Gauss) : g.toC.im = (g.im.val : ℝ) := by simp [toC]

theorem add_toC (a b : Gauss) : (a.add b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [add]
theorem mul_toC (a b : Gauss) : (a.mul b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [mul] <;> ring
theorem conj_toC (a : Gauss) : (a.conj).toC = (starRingEnd ℂ) a.toC := by
  apply Complex.ext <;> simp [conj]
theorem normSq_toC (a : Gauss) : Complex.normSq a.toC = (a.normSq.val : ℝ) := by
  simp [Complex.normSq_apply, normSq]
theorem zero_toC : zero.toC = 0 := by apply Complex.ext <;> simp [zero, Q.zero, Q.ofInt]
theorem one_toC : one.toC = 1 := by apply Complex.ext <;> simp [one, Q.zero, Q.one, Q.ofInt]
theorem I_toC : I.toC = Complex.I := by apply Complex.ext <;> simp [I, Q.zero, Q.one, Q.ofInt]

theorem inv_toC (a : Gauss) : (a.inv).toC = (a.toC)⁻¹ := by
  unfold inv
  dsimp only
  split
  · rename_i h0
    have hn : a.normSq.val = 0 := Q_val_of_isZero h0
    have h2 : a.re.val * a.re.val + a.im.val * a.im.val = 0 := by simpa [normSq] using hn
    obtain ⟨h3, h4⟩ := mul_self_add_mul_self_eq_zero.mp h2
    have : a.toC = 0 := by apply Complex.ext <;> simp [h3, h4]
    simp [this, zero_toC]
  · rename_i h0
    have hn : a.normSq.val ≠ 0 := by
      intro h; apply h0; simp only [Q.isZero, beq_iff_eq]; exact h
    have hnR : (a.re.val : ℝ) * a.re.val + (a.im.val : ℝ) * a.im.val ≠ 0 := by
      have := hn; simp only [normSq, Q_val_add, Q_val_mul] at this
      exact_mod_cast this
    have hD : (a.re.val : ℝ) ^ 2 + (a.im.val : ℝ) ^ 2 ≠ 0 := by rw [sq, sq]; exact hnR
    apply eq_inv_of_mul_eq_one_right
    apply Complex.ext
    · simp [normSq]
      field_simp
      try ring
    · simp [normSq]
      try ring

theorem pow_toC (a : Gauss) : ∀ n : ℕ, (a.pow n).toC = a.toC ^ n
  | 0 => by show one.toC = _; rw [one_toC, pow_zero]
  | n + 1 => by show (mul (pow a n) a).toC = _; rw [mul_toC, pow_toC a n, pow_succ]

theorem zpow_toC (a : Gauss) (n : ℤ) : (a.zpow n).toC = a.toC ^ n := by
  unfold zpow
  split
  · rename_i h
    rw [pow_toC]
    conv_rhs => rw [← Int.toNat_of_nonneg h]
    exact (zpow_natCast _ _).symm
  · rename_i h
    rw [pow_toC, inv_toC, inv_pow]
    have : n = -((-n).toNat : ℕ) := by omega
    conv_rhs => rw [this, zpow_neg, zpow_natCast]

end MathEngine.Gauss

namespace MathProofs
open MathEngine
open MathEngine.Expr
open Complex (I)

theorem gaussAtom_spec (ρ : EnvC) {e : Expr} {g : Gauss} (h : gaussAtom e = some g) : evalC ρ e = g.toC := by
  unfold gaussAtom at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    apply Complex.ext <;> simp [Gauss.I, Q.zero, Q.one, Q.ofInt]

theorem gauss?_spec (ρ : EnvC) {e : Expr} {g : Gauss} (h : gauss? e = some g) : evalC ρ e = g.toC := by
  unfold gauss? at h
  split at h
  · rename_i es
    have key : ∀ (l : List Expr) (acc g : Gauss),
        l.foldlM (fun acc e => (gaussAtom e).map (Gauss.add acc)) acc = some g → sumC ρ l = g.toC - acc.toC := by
      intro l
      induction l with
      | nil => intro acc g h; simp at h; subst h; simp
      | cons e l ih =>
        intro acc g h
        simp only [List.foldlM_cons] at h
        cases ha : gaussAtom e with
        | none => simp [ha] at h
        | some x =>
          simp [ha] at h
          have := ih _ _ h
          rw [sumC_cons, gaussAtom_spec ρ ha, this, Gauss.add_toC]; ring
    have := key es Gauss.zero g h
    rw [evalC_add, this, Gauss.zero_toC, sub_zero]
  · exact gaussAtom_spec ρ h

theorem imE_spec (ρ : EnvC) (q : Q) : evalC ρ (imE q) = (q.val : ℂ) * I := by
  unfold imE
  split
  · rename_i h; simp [Q_val_of_isOne h]
  · split
    · rename_i h; simp [Q_val_of_eq_minusOne h, Expr.minusOne, Q.minusOne, Q.ofInt]
    · simp

theorem gaussE_spec (ρ : EnvC) (g : Gauss) : evalC ρ (gaussE g) = g.toC := by
  unfold gaussE
  split
  · rename_i h; simp [Gauss.toC, Q_val_of_isZero h]
  · split
    · rename_i h; rw [imE_spec]; simp [Gauss.toC, Q_val_of_isZero h]
    · simp [Gauss.toC, imE_spec]

theorem gaussFactor_spec (ρ : EnvC) {e : Expr} {g : Gauss} (h : gaussFactor e = some g) : evalC ρ e = g.toC := by
  unfold gaussFactor at h
  split at h
  · rename_i b n
    split at h
    · rename_i hint
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨g', hg, rfl⟩ := h
      rw [evalC_pow, gauss?_spec ρ hg, evalC_num, Q_cast_isIntC hint, Complex.cpow_intCast, Gauss.zpow_toC]
    · simp at h
  · exact gauss?_spec ρ h

theorem gaussMul_spec (ρ : EnvC) {a b m : Expr} (h : gaussMul a b = some m) : evalC ρ m = evalC ρ a * evalC ρ b := by
  unfold gaussMul at h
  split at h
  · rename_i x y hx hy
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h
      rw [gaussE_spec, Gauss.mul_toC, gaussFactor_spec ρ hx, gaussFactor_spec ρ hy]
  · simp at h

-- ---------------------------------------------------------------------------
-- The powers of i
-- ---------------------------------------------------------------------------

theorem I_zpow_emod (n : ℤ) : I ^ n = I ^ (n % 4) := by
  have hn : n = n % 4 + 4 * (n / 4) := by omega
  conv_lhs => rw [hn]
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num [Complex.I_pow_four]

/-- The four values of `i^(n mod 4)`, as the rule builds them. -/
theorem iPower_value (n : ℤ) :
    (if n % 4 = 0 then Gauss.one else if n % 4 = 1 then Gauss.I
      else if n % 4 = 2 then (⟨Q.minusOne, Q.zero⟩ : Gauss) else ⟨Q.zero, Q.minusOne⟩).toC = I ^ (n % 4) := by
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> simp only [hr] <;> norm_num [Gauss.one_toC, Gauss.I_toC]
  · apply Complex.ext <;> simp [Gauss.toC, Q.minusOne, Q.zero, Q.ofInt]
  · apply Complex.ext <;> simp [Gauss.toC, Q.minusOne, Q.zero, Q.ofInt, pow_succ]

theorem iPower_soundC : PlainSoundC iPower := by
  intro e res h ρ
  simp only [iPower] at h
  split at h
  · rename_i n
    split at h
    · rename_i hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
      rw [guarded_result h, gaussE_spec, evalC_pow, evalC_fn₀, constC_i, evalC_num, Q_cast_isIntC hn.1,
        Complex.cpow_intCast, I_zpow_emod]
      exact (iPower_value _).symm
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- Gaussian arithmetic
-- ---------------------------------------------------------------------------

theorem cxArith_soundC : PlainSoundC cxArith := by
  intro e res h ρ
  simp only [cxArith] at h
  split at h
  · rename_i es
    split at h
    · rename_i m others hfp
      rw [guarded_result h]
      obtain ⟨a, b, hab, hperm⟩ := findPair_perm _ es hfp
      rw [evalC_mulN, evalC_mul, prodC_perm ρ hperm, prodC_cons, prodC_cons, prodC_cons, gaussMul_spec ρ hab]; ring
    · simp at h
  · simp at h

theorem cxPow_soundC : PlainSoundC cxPow := by
  intro e res h ρ
  simp only [cxPow] at h
  split at h
  · rename_i b n
    split at h
    · rename_i hn
      split at h
      · rename_i g hg
        split at h
        · simp at h
        · rw [guarded_result h, gaussE_spec, Gauss.zpow_toC, evalC_pow, gauss?_spec ρ hg, evalC_num]
          simp only [Bool.and_eq_true] at hn
          rw [Q_cast_isIntC hn.1.1, Complex.cpow_intCast]
      · simp at h
    · simp at h
  · simp at h

theorem cxConj_soundC : PlainSoundC cxConj := by
  intro e res h ρ
  simp only [cxConj] at h
  split at h
  · rw [guarded_result h]; simp
  · rename_i z
    split at h
    · rename_i g hg
      rw [guarded_result h, gaussE_spec, Gauss.conj_toC, evalC_fn₁, applyFnC_conj, gauss?_spec ρ hg]
    · simp at h
  · simp at h

theorem cxReIm_soundC : PlainSoundC cxReIm := by
  intro e res h ρ
  simp only [cxReIm] at h
  split at h
  · rename_i z
    split at h
    · rename_i g hg
      rw [guarded_result h, evalC_fn₁, applyFnC_re, gauss?_spec ρ hg, evalC_num]; simp
    · simp at h
  · rename_i z
    split at h
    · rename_i g hg
      rw [guarded_result h, evalC_fn₁, applyFnC_im, gauss?_spec ρ hg, evalC_num]; simp
    · simp at h
  · simp at h

/-- `‖z‖ = (normSq z) ^ (1/2)`, cast to ℂ. -/
theorem norm_eq_cpow_half (z : ℂ) : (‖z‖ : ℂ) = ((Complex.normSq z : ℝ) : ℂ) ^ ((mkRat 1 2 : ℚ) : ℂ) := by
  have h2 : ((mkRat 1 2 : ℚ) : ℂ) = (((2 : ℕ)⁻¹ : ℝ) : ℂ) := by
    rw [Rat.mkRat_eq_div]; push_cast; norm_num
  rw [h2, ← Complex.ofReal_cpow (Complex.normSq_nonneg z), ← Complex.sq_norm,
    Real.pow_rpow_inv_natCast (norm_nonneg z) two_ne_zero]

theorem cxAbs_soundC : PlainSoundC cxAbs := by
  intro e res h ρ
  simp only [cxAbs] at h
  split at h
  · rename_i z
    split at h
    · rename_i g hg
      split at h
      · simp at h
      · rw [guarded_result h, evalC_fn₁, applyFnC_abs, gauss?_spec ρ hg, norm_eq_cpow_half, Gauss.normSq_toC,
          evalC_pow, evalC_num, evalC_num, Complex.ofReal_ratCast]
        rfl
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- Exact values on the unit circle, over ℝ
-- ---------------------------------------------------------------------------

/-- What `refTable` says about a reference angle. -/
theorem refTable_spec {r sc cc : ℚ} {sr cr : ℕ} (h : refTable r = some ((sc, sr), (cc, cr))) :
    Real.sin ((r : ℝ) * Real.pi) = (sc : ℝ) * Real.sqrt (sr : ℝ) ∧
    Real.cos ((r : ℝ) * Real.pi) = (cc : ℝ) * Real.sqrt (cr : ℝ) := by
  unfold refTable at h
  split_ifs at h with h0 h1 h2 h3 h4 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := h
  · subst h0; simp
  · subst h1
    have e : ((mkRat 1 6 : ℚ) : ℝ) * Real.pi = Real.pi / 6 := by rw [Rat.mkRat_eq_div]; push_cast; ring
    rw [e, Real.sin_pi_div_six, Real.cos_pi_div_six, Rat.mkRat_eq_div]; push_cast
    constructor <;> simp <;> ring
  · subst h2
    have e : ((mkRat 1 4 : ℚ) : ℝ) * Real.pi = Real.pi / 4 := by rw [Rat.mkRat_eq_div]; push_cast; ring
    rw [e, Real.sin_pi_div_four, Real.cos_pi_div_four, Rat.mkRat_eq_div]; push_cast
    constructor <;> ring
  · subst h3
    have e : ((mkRat 1 3 : ℚ) : ℝ) * Real.pi = Real.pi / 3 := by rw [Rat.mkRat_eq_div]; push_cast; ring
    rw [e, Real.sin_pi_div_three, Real.cos_pi_div_three, Rat.mkRat_eq_div]; push_cast
    constructor <;> simp <;> ring
  · subst h4
    have e : ((mkRat 1 2 : ℚ) : ℝ) * Real.pi = Real.pi / 2 := by rw [Rat.mkRat_eq_div]; push_cast; ring
    rw [e, Real.sin_pi_div_two, Real.cos_pi_div_two]; simp

/-- The radicands `refTable` produces, as pairs: `(1,1)`, `(1,3)`, `(2,2)`, `(3,1)`. -/
theorem refTable_rad {r sc cc : ℚ} {sr cr : ℕ} (h : refTable r = some ((sc, sr), (cc, cr))) :
    (sr = 1 ∧ cr = 1) ∨ (sr = 1 ∧ cr = 3) ∨ (sr = 2 ∧ cr = 2) ∨ (sr = 3 ∧ cr = 1) := by
  unfold refTable at h
  split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩ := h <;> simp

theorem reflect_spec {r sc cc : ℚ} {sr cr : ℕ} (h : reflect r = some ((sc, sr), (cc, cr))) :
    (Real.sin ((r : ℝ) * Real.pi) = (sc : ℝ) * Real.sqrt (sr : ℝ) ∧
     Real.cos ((r : ℝ) * Real.pi) = (cc : ℝ) * Real.sqrt (cr : ℝ)) ∧
    ((sr = 1 ∧ cr = 1) ∨ (sr = 1 ∧ cr = 3) ∨ (sr = 2 ∧ cr = 2) ∨ (sr = 3 ∧ cr = 1)) := by
  unfold reflect at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨⟨sc', sr'⟩, ⟨cc', cr'⟩⟩, ht, hx⟩ := h
    simp only [Prod.mk.injEq] at hx
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := hx
    obtain ⟨hs, hc⟩ := refTable_spec ht
    have e : ((1 - r : ℚ) : ℝ) * Real.pi = Real.pi - (r : ℝ) * Real.pi := by push_cast; ring
    rw [e, Real.sin_pi_sub] at hs
    rw [e, Real.cos_pi_sub] at hc
    refine ⟨⟨hs, ?_⟩, refTable_rad ht⟩
    push_cast; linear_combination -hc
  · exact ⟨refTable_spec h, refTable_rad h⟩

theorem halfTurn_spec {r sc cc : ℚ} {sr cr : ℕ} (h : halfTurn r = some ((sc, sr), (cc, cr))) :
    (Real.sin ((r : ℝ) * Real.pi) = (sc : ℝ) * Real.sqrt (sr : ℝ) ∧
     Real.cos ((r : ℝ) * Real.pi) = (cc : ℝ) * Real.sqrt (cr : ℝ)) ∧
    ((sr = 1 ∧ cr = 1) ∨ (sr = 1 ∧ cr = 3) ∨ (sr = 2 ∧ cr = 2) ∨ (sr = 3 ∧ cr = 1)) := by
  unfold halfTurn at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨⟨sc', sr'⟩, ⟨cc', cr'⟩⟩, ht, hx⟩ := h
    simp only [Prod.mk.injEq] at hx
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := hx
    obtain ⟨⟨hs, hc⟩, hrad⟩ := reflect_spec ht
    have e : (r : ℝ) * Real.pi = ((r - 1 : ℚ) : ℝ) * Real.pi + Real.pi := by push_cast; ring
    refine ⟨⟨?_, ?_⟩, hrad⟩
    · rw [e, Real.sin_add_pi, hs]; push_cast; ring
    · rw [e, Real.cos_add_pi, hc]; push_cast; ring
  · exact reflect_spec h

theorem sinCos_spec {q sc cc : ℚ} {sr cr : ℕ} (h : sinCos q = some ((sc, sr), (cc, cr))) :
    (Real.sin ((q : ℝ) * Real.pi) = (sc : ℝ) * Real.sqrt (sr : ℝ) ∧
     Real.cos ((q : ℝ) * Real.pi) = (cc : ℝ) * Real.sqrt (cr : ℝ)) ∧
    ((sr = 1 ∧ cr = 1) ∨ (sr = 1 ∧ cr = 3) ∨ (sr = 2 ∧ cr = 2) ∨ (sr = 3 ∧ cr = 1)) := by
  unfold sinCos at h
  obtain ⟨⟨hs, hc⟩, hrad⟩ := halfTurn_spec h
  have e : (q : ℝ) * Real.pi = ((q - 2 * (q / 2).floor : ℚ) : ℝ) * Real.pi + ((q / 2).floor : ℤ) * (2 * Real.pi) := by
    push_cast; ring
  refine ⟨⟨?_, ?_⟩, hrad⟩
  · rw [e, Real.sin_add_int_mul_two_pi, hs]
  · rw [e, Real.cos_add_int_mul_two_pi, hc]

theorem evalR_radE (ρ : EnvR) (c : Q) (r : ℕ) : evalR ρ (radE c r) = (c.val : ℝ) * Real.sqrt (r : ℝ) := by
  unfold radE
  split
  · rename_i h; rw [Q_val_of_isZero h]; simp
  · split
    · rename_i h; subst h; simp
    · have hr : evalR ρ (.pow (.num (Q.ofInt r)) (.num (Q.ofRat (mkRat 1 2)))) = Real.sqrt (r : ℝ) := by
        rw [evalR_pow, evalR_num, evalR_num, Q_val_ofInt, Q_val_ofRat, Rat.mkRat_eq_div, Real.sqrt_eq_rpow]
        push_cast; norm_num
      split
      · rename_i h; rw [Q_val_of_isOne h, hr]; simp
      · simp only [evalR_mul, prodR_cons, prodR_nil, evalR_num, hr, mul_one]

/-- `trigValue f q` is the value of `f` at `q·π`, over ℝ. -/
theorem trigValue_soundR (ρ : EnvR) {f : String} (hf : f = "sin" ∨ f = "cos" ∨ f = "tan") {q : Q} {v : Expr}
    (hv : trigValue f q = some v) : evalR ρ v = applyFn f ((q.val : ℝ) * Real.pi) := by
  unfold trigValue at hv
  simp only [Option.map_eq_some_iff] at hv
  obtain ⟨⟨c, r⟩, hc, rfl⟩ := hv
  rw [evalR_radE]
  unfold trigCoeff at hc
  split at hc
  · simp at hc
  · rename_i sc sr cc cr hs
    obtain ⟨⟨hsin, hcos⟩, hrad⟩ := sinCos_spec hs
    rcases hf with rfl | rfl | rfl
    · rw [if_pos (by decide)] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp [hsin]
    · rw [if_neg (by decide), if_pos (by decide)] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp [hcos]
    · rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)] at hc
      simp only [applyFn]
      rw [Real.tan_eq_sin_div_cos, hsin, hcos]
      split_ifs at hc with h0 h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
      all_goals obtain ⟨rfl, rfl⟩ := hc
      · subst h1
        have hs0 : Real.sqrt (sr : ℝ) ≠ 0 := by
          rcases hrad with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact (Real.sqrt_pos.mpr (by norm_num)).ne'
        have hc0 : (cc : ℝ) ≠ 0 := by exact_mod_cast h0
        simp only [Q_val_ofRat, Rat.cast_div, Nat.cast_one, Real.sqrt_one]; push_cast; field_simp
      · subst h2
        have hcr : cr = 1 := by rcases hrad with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
        subst hcr
        have hc0 : (cc : ℝ) ≠ 0 := by exact_mod_cast h0
        simp only [Q_val_ofRat, Rat.cast_div, Nat.cast_one, Nat.cast_ofNat, Real.sqrt_one]; push_cast; field_simp
      · subst h3
        have hsr : sr = 1 := by rcases hrad with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
        subst hsr
        have hc0 : (cc : ℝ) ≠ 0 := by exact_mod_cast h0
        have h3 : Real.sqrt (3 : ℝ) * Real.sqrt (3 : ℝ) = 3 := Real.mul_self_sqrt (by norm_num)
        have h30 : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
        simp only [Q_val_ofRat, Rat.cast_div, Nat.cast_one, Nat.cast_ofNat, Real.sqrt_one]; push_cast
        field_simp
        linear_combination (sc : ℝ) * h3

/-- The value as a term: `trigValue` is `radE` of `trigCoeff`. -/
theorem trigValue_eq {f : String} {q : Q} {v : Expr} (hv : trigValue f q = some v) :
    ∃ c r, v = radE c r ∧ trigValue f q = some (radE c r) := by
  unfold trigValue at hv ⊢
  simp only [Option.map_eq_some_iff] at hv
  obtain ⟨⟨c, r⟩, hc, rfl⟩ := hv
  exact ⟨c, r, rfl, by simp [hc]⟩

/-- `trigArg a = some q` means `a` is `q·π`. -/
theorem trigArg_specR (ρ : EnvR) {a : Expr} {q : Q} (h : trigArg a = some q) : evalR ρ a = (q.val : ℝ) * Real.pi := by
  unfold trigArg at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp [Q.one, Q.ofInt] <;> ring

/-- A plain rule is ℝ-sound when every rewrite preserves the real value. -/
abbrev PlainSoundR (r : PlainRule) : Prop := ∀ e res, r.apply e = some res → ∀ ρ : EnvR, evalR ρ e = evalR ρ res.result

theorem exactTrig_soundR : PlainSoundR exactTrig := by
  intro e res h ρ
  simp only [exactTrig] at h
  split at h
  · rename_i f a
    split at h
    · rename_i hf
      split at h
      · rename_i q hq
        split at h
        · rename_i v hv
          rw [guarded_result h, evalR_fn₁, trigArg_specR ρ hq]
          simp only [Bool.or_eq_true, beq_iff_eq] at hf
          exact (trigValue_soundR ρ (by tauto) hv).symm
        · simp at h
      · simp at h
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- … and over ℂ, by casting
-- ---------------------------------------------------------------------------

theorem evalC_radE (ρ : EnvC) (c : Q) (r : ℕ) : evalC ρ (radE c r) = (((c.val : ℝ) * Real.sqrt (r : ℝ) : ℝ) : ℂ) := by
  unfold radE
  split
  · rename_i h; rw [Q_val_of_isZero h]; simp
  · split
    · rename_i h; subst h; simp
    · have hr : evalC ρ (.pow (.num (Q.ofInt r)) (.num (Q.ofRat (mkRat 1 2)))) = ((Real.sqrt (r : ℝ) : ℝ) : ℂ) := by
        rw [evalC_pow, evalC_num, evalC_num, Q_val_ofInt, Q_val_ofRat, Real.sqrt_eq_rpow, Rat.mkRat_eq_div,
          ← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast, ← Complex.ofReal_cpow (by positivity)]
        push_cast; norm_num
      split
      · rename_i h; rw [Q_val_of_isOne h, hr]; simp
      · simp only [evalC_mul, prodC_cons, prodC_nil, evalC_num, hr, mul_one]; push_cast; ring

theorem trigArg_specC (ρ : EnvC) {a : Expr} {q : Q} (h : trigArg a = some q) :
    evalC ρ a = (((q.val : ℝ) * Real.pi : ℝ) : ℂ) := by
  unfold trigArg at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp [Q.one, Q.ofInt] <;> ring

theorem exactTrig_soundC : PlainSoundC exactTrig := by
  intro e res h ρ
  simp only [exactTrig] at h
  split at h
  · rename_i f a
    split at h
    · rename_i hf
      split at h
      · rename_i q hq
        split at h
        · rename_i v hv
          obtain ⟨c, r, rfl, hv'⟩ := trigValue_eq hv
          rw [guarded_result h, evalC_fn₁, trigArg_specC ρ hq, evalC_radE]
          simp only [Bool.or_eq_true, beq_iff_eq] at hf
          have := trigValue_soundR (fun _ => 0) (by tauto) hv'
          rw [evalR_radE] at this
          rw [this]
          rcases hf with (rfl | rfl) | rfl
          · simp [Complex.ofReal_sin]
          · simp [Complex.ofReal_cos]
          · simp [applyFn, Complex.ofReal_tan]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- Euler's formula, and ℯ^b
-- ---------------------------------------------------------------------------

theorem isI_eq {e : Expr} (h : isI e = true) : e = iE := by
  cases e <;> simp only [isI, reduceCtorEq, Bool.false_eq_true] at h
  rename_i f es
  cases es
  · simp only [beq_iff_eq] at h; subst h; rfl
  · simp at h

theorem imagArg_spec (ρ : EnvC) {a θ : Expr} (h : imagArg a = some θ) : evalC ρ a = I * evalC ρ θ := by
  unfold imagArg at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp
  · rename_i fs
    split at h
    · rename_i hone
      simp only [Option.some.injEq] at h; subst h
      have hperm := List.filter_append_perm isI fs
      have hI : fs.filter isI = [iE] := by
        cases hfi : fs.filter isI with
        | nil => simp [hfi] at hone
        | cons x t =>
          cases t with
          | nil =>
            have hx : isI x = true := (List.mem_filter.mp (by rw [hfi]; simp)).2
            rw [isI_eq hx]
          | cons y t => simp [hfi] at hone
      rw [evalC_mul, ← prodC_perm ρ hperm, prodC_append, hI, evalC_mulN]
      simp
    · simp at h
  · simp at h

theorem evalC_unMul (ρ : EnvC) (s : Expr) : prodC ρ (unMul s) = evalC ρ s := by
  cases s <;> simp [unMul]

theorem imagOf_spec (ρ : EnvC) (s : Expr) : evalC ρ (imagOf s) = evalC ρ s * I := by
  unfold imagOf
  split
  · rename_i h; rw [evalC_of_isZero h]; simp
  · split
    · rename_i h; rw [evalC_of_isOne h]; simp
    · rw [evalC_mulN, prodC_append, evalC_unMul]; simp

theorem sumC_filter_nonzero' (ρ : EnvC) (l : List Expr) : sumC ρ (l.filter (fun t => !t.isZero)) = sumC ρ l :=
  sumC_filter_nonzero ρ l

theorem eulerValue_spec (ρ : EnvC) (c s : Expr) : evalC ρ (eulerValue c s) = evalC ρ c + evalC ρ s * I := by
  unfold eulerValue
  have key : sumC ρ ([c, imagOf s].filter (fun t => !t.isZero)) = evalC ρ c + evalC ρ s * I := by
    rw [sumC_filter_nonzero', sumC_cons, sumC_cons, sumC_nil, imagOf_spec, add_zero]
  split
  · rename_i h
    rw [List.isEmpty_iff] at h
    have := key; rw [h, sumC_nil] at this
    rw [evalC_zero, this]
  · rw [evalC_addN, key]

theorem euler_soundC : PlainSoundC euler := by
  intro e res h ρ
  simp only [euler] at h
  split at h
  · rename_i a
    split at h
    · simp at h
    · rename_i θ hθ
      split at h
      · simp at h
      · rename_i q hq
        split at h
        · rename_i c s hc hs
          obtain ⟨cc, cr, rfl, hc'⟩ := trigValue_eq hc
          obtain ⟨sc, sr, rfl, hs'⟩ := trigValue_eq hs
          rw [guarded_result h, eulerValue_spec, evalC_fn₁, applyFnC_exp, imagArg_spec ρ hθ, trigArg_specC ρ hq,
            evalC_radE, evalC_radE]
          have hcv := trigValue_soundR (fun _ => 0) (Or.inr (Or.inl rfl)) hc'
          have hsv := trigValue_soundR (fun _ => 0) (Or.inl rfl) hs'
          rw [evalR_radE] at hcv hsv
          simp only [applyFn_cos, applyFn_sin] at hcv hsv
          rw [hcv, hsv, mul_comm I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
        · simp at h
  · simp at h

theorem eulerPower_soundR : PlainSoundR eulerPower := by
  intro e res h ρ
  simp only [eulerPower] at h
  split at h
  · rename_i q b
    split at h
    · rename_i hq
      simp only [Bool.and_eq_true] at hq
      rw [guarded_result h, evalR_pow, evalR_fn₁, applyFn_exp, evalR_num, evalR_fn₁, applyFn_exp,
        Q_val_of_isOne hq.1, Rat.cast_one, Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
    · simp at h
  · simp at h

theorem eulerPower_soundC : PlainSoundC eulerPower := by
  intro e res h ρ
  simp only [eulerPower] at h
  split at h
  · rename_i q b
    split at h
    · rename_i hq
      simp only [Bool.and_eq_true] at hq
      rw [guarded_result h, evalC_pow, evalC_fn₁, applyFnC_exp, evalC_num, evalC_fn₁, applyFnC_exp,
        Q_val_of_isOne hq.1, Rat.cast_one, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp; positivity) (by simp; positivity), one_mul]
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- What the principal branch breaks: ln (exp x) = x fails at x = 2πi
-- ---------------------------------------------------------------------------

theorem not_functionRules_soundC : ¬ RuleSoundC functionRules := by
  intro hs
  have h := hs (.fn "ln" [.fn "exp" [.var "x"]]) _ rfl (fun _ => 2 * Real.pi * I)
  simp only [evalC_fn₁, applyFnC_exp, applyFnC_ln, evalC_var] at h
  rw [Complex.exp_two_pi_mul_I, Complex.log_one] at h
  have : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact this h.symm

end MathProofs
end
