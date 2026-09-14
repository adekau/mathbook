import Proofs.Semantics
/-!
# The `simp.*` rules over ℝ

M1 proved every rule sound on the integer fragment. That fragment cannot see `1/2`, `sin`, or
`x^(1/2)`, so it also could not see where a rule is *wrong*. Over ℝ each rule gets its real
soundness theorem, and two of them turn out to need side conditions:

| rule | over ℝ |
|---|---|
| `simp.flatten`, `simp.identity`, `simp.fold-constants`, `simp.collect-like-terms`, `simp.power`, canonical order | unconditionally sound |
| `simp.collect-powers` | needs a nonzero base — `x·x⁻¹ ⟶ x⁰` is `0 ≠ 1` at `x = 0` |
| `simp.function` | needs a positive argument for `exp(ln x) ⟶ x` — it is `1 ≠ -1` at `x = -1` |

The two gaps are not proof failures: `not_collectPowers_soundR` and `not_functionRules_soundR`
*prove* that no unconditional theorem exists. Both are the standard computer-algebra convention
(Mathematica simplifies `x/x` to `1` too), so the engine keeps them; what changes is that the
assumption is now written down instead of implied.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Expr

-- ---------------------------------------------------------------------------
-- ℝ as a `Congruence`
-- ---------------------------------------------------------------------------

private theorem list_eq_two {α : Type*} : ∀ {l : List α}, l.length = 2 → ∃ a b, l = [a, b]
  | [_, _], _ => ⟨_, _, rfl⟩

theorem sumR_congr (ρ : EnvR) : ∀ {as bs : List Expr}, RelList SemEqR as bs → sumR ρ as = sumR ρ bs
  | [], [], _ => rfl
  | a :: as, b :: bs, ⟨hab, hrest⟩ => by rw [sumR_cons, sumR_cons, hab ρ, sumR_congr ρ hrest]

theorem prodR_congr (ρ : EnvR) : ∀ {as bs : List Expr}, RelList SemEqR as bs → prodR ρ as = prodR ρ bs
  | [], [], _ => rfl
  | a :: as, b :: bs, ⟨hab, hrest⟩ => by rw [prodR_cons, prodR_cons, hab ρ, prodR_congr ρ hrest]

theorem SemEqR.congr (e : Expr) (cs : List Expr) (h : RelList SemEqR (children e) cs) :
    SemEqR e (withChildren e cs) := by
  intro ρ
  have hlen : (children e).length = cs.length := RelList_length h
  cases e with
  | num q => cases cs with | nil => rfl | cons _ _ => simp [children] at hlen
  | var x => cases cs with | nil => rfl | cons _ _ => simp [children] at hlen
  | add es => exact sumR_congr ρ h
  | mul es => exact prodR_congr ρ h
  | matrix rows => rfl
  | pow b x =>
    obtain ⟨b', x', rfl⟩ := list_eq_two (by simpa [children] using hlen.symm)
    obtain ⟨hb, hx, -⟩ := h
    simp only [withChildren, evalR_pow, hb ρ, hx ρ]
  | fn f es =>
    simp only [children] at hlen
    cases es with
    | nil => cases cs with
      | nil => rfl
      | cons _ _ => simp at hlen
    | cons a rest =>
      cases cs with
      | nil => simp at hlen
      | cons a' rest' =>
        cases rest with
        | nil =>
          cases rest' with
          | nil => obtain ⟨ha, -⟩ := h; simp only [withChildren, evalR_fn₁, ha ρ]
          | cons _ _ => simp at hlen
        | cons _ _ =>
          cases rest' with
          | nil => simp at hlen
          | cons _ _ => rfl

theorem SemEqR.canon (e : Expr) : SemEqR e (canon e) := by
  intro ρ
  cases e with
  | add es => exact sumR_perm ρ (List.mergeSort_perm es _).symm
  | mul es =>
    simp only [MathEngine.canon]
    split
    · rfl
    · exact prodR_perm ρ (List.mergeSort_perm es _).symm
  | _ => rfl

/-- ℝ packaged as a `Congruence`, so `normalize_sound_for` applies. -/
def semEqRCongruence : Congruence where
  rel := SemEqR
  refl := SemEqR.refl
  trans := SemEqR.trans
  congr := SemEqR.congr
  canon := SemEqR.canon

/-- A rule is ℝ-sound when every rewrite it performs preserves the real value. -/
abbrev RuleSoundR (r : Rule simpW) : Prop := RuleSoundFor semEqRCongruence r

-- ---------------------------------------------------------------------------
-- Numerals
-- ---------------------------------------------------------------------------

@[simp] theorem Q_val_add (a b : Q) : ((a + b : Q)).val = a.val + b.val := rfl
@[simp] theorem Q_val_mul (a b : Q) : ((a * b : Q)).val = a.val * b.val := rfl
@[simp] theorem Q_val_zero : (Q.zero).val = 0 := rfl
@[simp] theorem Q_val_one : (Q.one).val = 1 := rfl
@[simp] theorem Q_val_ofInt (n : ℤ) : (Q.ofInt n).val = (n : ℚ) := rfl

theorem evalR_of_isZero {e : Expr} (h : Expr.isZero e = true) (ρ : EnvR) : evalR ρ e = 0 := by
  cases e <;> simp [Expr.isZero] at h
  rename_i q
  have : q.val = 0 := by simpa [Q.isZero] using h
  simp [this]

theorem evalR_of_isOne {e : Expr} (h : Expr.isOne e = true) (ρ : EnvR) : evalR ρ e = 1 := by
  cases e <;> simp [Expr.isOne] at h
  rename_i q
  have : q.val = 1 := by simpa [Q.isOne] using h
  simp [this]

theorem evalR_of_isNum {e : Expr} (h : Expr.isNum e = true) (ρ : EnvR) : evalR ρ e = (numOf e).val := by
  cases e <;> simp [Expr.isNum] at h
  rfl

-- ---------------------------------------------------------------------------
-- simp.flatten
-- ---------------------------------------------------------------------------

theorem sumR_unAdd (ρ : EnvR) (e : Expr) : sumR ρ (unAdd e) = evalR ρ e := by
  cases e <;> simp [unAdd]

theorem prodR_unMul (ρ : EnvR) (e : Expr) : prodR ρ (unMul e) = evalR ρ e := by
  cases e <;> simp [unMul]

theorem sumR_flatMap_unAdd (ρ : EnvR) (es : List Expr) :
    sumR ρ (es.flatMap unAdd) = sumR ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, sumR_append, sumR_unAdd, ih, sumR_cons]

theorem prodR_flatMap_unMul (ρ : EnvR) (es : List Expr) :
    prodR ρ (es.flatMap unMul) = prodR ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, prodR_append, prodR_unMul, ih, prodR_cons]

theorem flatten_soundR : RuleSoundR flatten := by
  intro e r h ρ
  cases e <;> simp only [flatten, flattenApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; simp [sumR_flatMap_unAdd]
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; simp [prodR_flatMap_unMul]

-- ---------------------------------------------------------------------------
-- simp.identity
-- ---------------------------------------------------------------------------

theorem sumR_filter_nonzero (ρ : EnvR) (es : List Expr) :
    sumR ρ (es.filter (fun e => !Expr.isZero e)) = sumR ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hz : Expr.isZero e = true
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, sumR_cons,
        evalR_of_isZero hz, zero_add]
    · simp only [hz, Bool.not_false, ↓reduceIte, sumR_cons, ih]

theorem prodR_filter_nonone (ρ : EnvR) (es : List Expr) :
    prodR ρ (es.filter (fun e => !Expr.isOne e)) = prodR ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h1 : Expr.isOne e = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, prodR_cons,
        evalR_of_isOne h1, one_mul]
    · simp only [h1, Bool.not_false, ↓reduceIte, prodR_cons, ih]

theorem prodR_eq_zero_of_any (ρ : EnvR) (es : List Expr) (h : es.any Expr.isZero = true) :
    prodR ρ es = 0 := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · simp [evalR_of_isZero h]
    · simp [ih h]

theorem identity_soundR : RuleSoundR identity := by
  intro e r h ρ
  cases e with
  | add es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [e], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [evalR_addN, evalR_add, sumR_filter_nonzero]
  | mul es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [e], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rename_i hz
        simp only [evalR_mul, evalR_zero]
        exact prodR_eq_zero_of_any ρ _ hz
      · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; simp only [evalR_mulN, evalR_mul, prodR_filter_nonone]
  | _ => simp [identity, identityApply] at h

-- ---------------------------------------------------------------------------
-- simp.fold-constants  (over ℚ→ℝ this is exact: 1/2 + 1/3 = 5/6 is now provable)
-- ---------------------------------------------------------------------------

theorem sumQ_eval (ρ : EnvR) : ∀ (l : List Expr) (acc : Q), (∀ e ∈ l, Expr.isNum e = true) →
    ((l.foldl (fun s e => s + numOf e) acc).val : ℝ) = (acc.val : ℝ) + sumR ρ l
  | [], acc, _ => by simp
  | e :: es, acc, hall => by
    rw [List.foldl_cons, sumQ_eval ρ es _ (fun a ha => hall a (List.mem_cons_of_mem _ ha)),
      sumR_cons, evalR_of_isNum (hall e (by simp))]
    simp only [Q_val_add, Rat.cast_add]
    ring

theorem prodQ_eval (ρ : EnvR) : ∀ (l : List Expr) (acc : Q), (∀ e ∈ l, Expr.isNum e = true) →
    ((l.foldl (fun s e => s * numOf e) acc).val : ℝ) = (acc.val : ℝ) * prodR ρ l
  | [], acc, _ => by simp
  | e :: es, acc, hall => by
    rw [List.foldl_cons, prodQ_eval ρ es _ (fun a ha => hall a (List.mem_cons_of_mem _ ha)),
      prodR_cons, evalR_of_isNum (hall e (by simp))]
    simp only [Q_val_mul, Rat.cast_mul]
    ring

theorem sumQ_evalR (ρ : EnvR) (l : List Expr) (hall : ∀ e ∈ l, Expr.isNum e = true) :
    ((sumQ l).val : ℝ) = sumR ρ l := by
  have h := sumQ_eval ρ l Q.zero hall
  simp only [Q_val_zero, Rat.cast_zero, zero_add] at h
  exact h

theorem prodQ_evalR (ρ : EnvR) (l : List Expr) (hall : ∀ e ∈ l, Expr.isNum e = true) :
    ((prodQ l).val : ℝ) = prodR ρ l := by
  have h := prodQ_eval ρ l Q.one hall
  simp only [Q_val_one, Rat.cast_one, one_mul] at h
  exact h

theorem foldConstants_soundR : RuleSoundR foldConstants := by
  intro e r h ρ
  have hnums : ∀ (es : List Expr), ∀ a ∈ es.filter Expr.isNum, Expr.isNum a = true :=
    fun es a ha => (List.mem_filter.mp ha).2
  cases e <;> simp only [foldConstants, foldApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [evalR_add, evalR_add, sumR_cons, evalR_num, sumQ_evalR ρ _ (hnums es),
      ← sumR_perm ρ (List.filter_append_perm Expr.isNum es), sumR_append]
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [evalR_mul, evalR_mul, prodR_cons, evalR_num, prodQ_evalR ρ _ (hnums es),
      ← prodR_perm ρ (List.filter_append_perm Expr.isNum es), prodR_append]

-- ---------------------------------------------------------------------------
-- simp.collect-like-terms
-- ---------------------------------------------------------------------------

theorem evalR_coeffRest {e : Expr} {c : Q} {t : Expr} (h : coeffRest e = (c, t)) (ρ : EnvR) :
    evalR ρ e = (c.val : ℝ) * evalR ρ t := by
  rcases coeffRest_cases e c t h with ⟨he, ht⟩ | ⟨r, he, ht⟩ | ⟨he, hc⟩
  · subst he; subst ht; simp
  · subst he; subst ht; simp
  · subst he; subst hc; simp

theorem mergeTerms_soundR (ρ : EnvR) : ∀ (es l : List Expr) (t : Expr),
    mergeTerms es = some (l, t) → sumR ρ l = sumR ρ es
  | [], _, _, h => by simp [mergeTerms] at h
  | e :: rest, l, t, h => by
    simp only [mergeTerms] at h
    obtain ⟨c, u, hcu⟩ : ∃ c u, coeffRest e = (c, u) := ⟨_, _, rfl⟩
    rw [hcu] at h
    simp only at h
    split at h
    · split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : Expr.equal (coeffRest f).2 u = true := by simpa using List.find?_some hf
        have hfu : coeffRest f = ((coeffRest f).1, u) := by rw [← Expr.equal_eq hp]
        have h1 : sumR ρ rest
            = evalR ρ f + sumR ρ (removeFirst (fun x => (coeffRest x).2.equal u) rest) := by
          rw [sumR_perm ρ (perm_find?_removeFirst _ rest f hf), sumR_cons]
        rw [sumR_cons, sumR_cons, h1, evalR_coeffRest hcu, evalR_coeffRest hfu]
        simp only [evalR_mul, prodR_cons, prodR_nil, evalR_num, Q_val_add, Rat.cast_add]
        ring
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        rw [sumR_cons, sumR_cons, mergeTerms_soundR ρ rest l' t' hm]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [sumR_cons, sumR_cons, mergeTerms_soundR ρ rest l' t' hm]

theorem collectTerms_soundR : RuleSoundR collectTerms := by
  intro e r h ρ
  cases e <;> simp only [collectTerms, collectTermsApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    simp only [Option.some.injEq] at h; subst h
    rw [evalR_add, evalR_add]; exact (mergeTerms_soundR ρ es l t hm).symm
  · simp at h

-- ---------------------------------------------------------------------------
-- simp.power
-- ---------------------------------------------------------------------------

/-- The search only ever returns a `y` whose power it has checked, so correctness needs no
reasoning about the search itself — and completeness is never needed. -/
theorem natRootGo_pow (n x : ℕ) :
    ∀ (fuel lo hi a : ℕ), natRootGo n x lo hi fuel = some a → a ^ n = x
  | 0, _, _, _, h => by simp [natRootGo] at h
  | fuel + 1, lo, hi, a, h => by
    simp only [natRootGo] at h
    split at h
    · split at h
      · exact natRootGo_pow n x fuel _ _ _ h
      · exact natRootGo_pow n x fuel _ _ _ h
    · split at h
      · rename_i heq; simp only [Option.some.injEq] at h; subst h; exact heq
      · simp at h

theorem natRoot_pow {n x a : ℕ} (hn : n ≠ 0) (h : natRoot n x = some a) : a ^ n = x := by
  simp only [natRoot] at h
  split at h
  · rename_i hx
    simp only [Option.some.injEq] at h
    rw [h] at hx ⊢
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp [hn]
  · exact natRootGo_pow n x _ _ _ _ h

theorem exactRoot_spec {r : ℚ} {n : ℕ} {a : ℚ} (hn : n ≠ 0) (h : exactRoot r n = some a) :
    0 ≤ a ∧ a ^ n = r := by
  simp only [exactRoot] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hg
    have hr : 0 ≤ r := by
      by_contra hlt
      push_neg at hlt
      exact hg (by
        first
          | simp [hlt]
          | rw [decide_eq_true hlt, Bool.true_or]
          | simp [decide_eq_true hlt]
          | exact Bool.or_eq_true _ _ ▸ Or.inl (decide_eq_true hlt))
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, q, hq, ha⟩ := h
    have hpn := natRoot_pow hn hp
    have hqn := natRoot_pow hn hq
    simp only [Option.some.injEq] at ha
    subst ha
    have hnum : ((r.num.natAbs : ℕ) : ℚ) = (r.num : ℚ) := by
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Rat.num_nonneg.mpr hr)
      rw [hk]; simp
    rw [Rat.mkRat_eq_div]
    refine ⟨by positivity, ?_⟩
    rw [div_pow]
    have e1 : ((p : ℤ) : ℚ) ^ n = (r.num : ℚ) := by rw [← hnum, ← hpn]; push_cast; ring
    have e2 : ((q : ℕ) : ℚ) ^ n = (r.den : ℚ) := by rw [← hqn]; push_cast; ring
    rw [e1, e2, Rat.num_div_den]

theorem Q_cast_isInt {q : Q} (h : q.isInt = true) : (q.val : ℝ) = ((q.val.num : ℤ) : ℝ) := by
  have hd : q.val.den = 1 := by simpa [Q.isInt] using h
  rw [Rat.cast_def, hd]; norm_num

theorem isPosNum_ne_zero {x : Expr} (h : isPosNum x = true) (ρ : EnvR) : evalR ρ x ≠ 0 := by
  cases x <;> simp only [isPosNum, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    reduceCtorEq] at h
  rename_i q
  have : q.val ≠ 0 := by
    intro hz; rw [show q.isZero = true by simp [Q.isZero, hz]] at h; simp at h
  simpa using this

theorem powerRules_soundR : RuleSoundR powerRules := by
  intro e r h ρ
  cases e <;> simp only [powerRules, powerApply, reduceCtorEq] at h
  rename_i b x
  simp only [powerAt] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i hz
    rw [evalR_pow, evalR_of_isZero hz]
    show _ = evalR ρ Expr.one
    rw [evalR_one, Real.rpow_zero]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [evalR_pow, evalR_of_isOne h1, Real.rpow_one]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [evalR_pow, evalR_of_isOne h1]
    show _ = evalR ρ Expr.one
    rw [evalR_one, Real.one_rpow]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h0
    simp only [Bool.and_eq_true] at h0
    rw [evalR_pow, evalR_of_isZero h0.1]
    show _ = evalR ρ Expr.zero
    rw [evalR_zero, Real.zero_rpow (isPosNum_ne_zero h0.2 ρ)]
  · cases b with
    | num p =>
      cases x with
      | num q =>
        simp only [powerNum, powNumeric] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; rename_i hint
          rw [evalR_pow, evalR_num, evalR_num, Q_cast_isInt hint, Real.rpow_intCast]
          show _ = ((p.val ^ q.val.num : ℚ) : ℝ)
          rw [Rat.cast_zpow]
        · split at h
          · rename_i hone
            split at h
            · rename_i rr hroot
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨hnn, hpow⟩ := exactRoot_spec (Rat.den_nz q.val) hroot
              have hnum1 : q.val.num = 1 := by simpa using hone
              have hqv : (q.val : ℝ) = (((q.val.den : ℕ) : ℝ))⁻¹ := by
                rw [Rat.cast_def, hnum1]; norm_num
              rw [evalR_pow, evalR_num, evalR_num, hqv]
              show (((p.val : ℚ) : ℝ)) ^ _ = ((rr : ℚ) : ℝ)
              have hp : ((p.val : ℚ) : ℝ) = ((rr : ℚ) : ℝ) ^ (q.val.den) := by
                rw [← hpow]; push_cast; ring
              rw [hp]
              exact Real.pow_rpow_inv_natCast (by exact_mod_cast hnn) (Rat.den_nz q.val)
            · simp at h
          · simp at h
      | _ => simp [powerNum] at h
    | pow b' m =>
      cases x with
      | num n' =>
        cases m with
        | num mq =>
          simp only [powerNum] at h
          split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
          subst h; rename_i hint
          simp only [Bool.and_eq_true] at hint
          obtain ⟨hn', hm⟩ := hint
          have hmn : ((mq * n' : Q).val : ℝ) = ((mq.val.num * n'.val.num : ℤ) : ℝ) := by
            rw [Q_val_mul, Rat.cast_mul, Q_cast_isInt hm, Q_cast_isInt hn']; push_cast; ring
          show ((evalR ρ b') ^ (evalR ρ (Expr.num mq))) ^ (evalR ρ (Expr.num n'))
            = (evalR ρ b') ^ (evalR ρ (Expr.num (mq * n')))
          rw [evalR_num, evalR_num, evalR_num, hmn, Q_cast_isInt hm, Q_cast_isInt hn',
            Real.rpow_intCast, Real.rpow_intCast, Real.rpow_intCast, zpow_mul]
        | _ => simp [powerNum] at h
      | _ => simp [powerNum] at h
    | _ => cases x <;> simp [powerNum] at h

-- ---------------------------------------------------------------------------
-- simp.collect-powers: sound exactly where the merged base is positive
-- ---------------------------------------------------------------------------

theorem evalR_addExp (ρ : EnvR) (x y : Expr) : evalR ρ (addExp x y) = evalR ρ x + evalR ρ y := by
  cases x <;> cases y <;> simp [addExp]

theorem evalR_baseExp {e b x : Expr} (h : baseExp e = (b, x)) (ρ : EnvR) :
    evalR ρ e = (evalR ρ b) ^ (evalR ρ x) := by
  rcases baseExp_cases e b x h with he | ⟨he, hx⟩
  · rw [he, evalR_pow]
  · rw [he, hx, evalR_one, Real.rpow_one]

theorem mergePowers_soundR_on (ρ : EnvR) : ∀ (es l : List Expr) (t : Expr),
    mergePowers es = some (l, t) → 0 < evalR ρ t → prodR ρ l = prodR ρ es
  | [], _, _, h, _ => by simp [mergePowers] at h
  | e :: rest, l, t, h, ht => by
    simp only [mergePowers] at h
    obtain ⟨b, x, hbx⟩ : ∃ b x, baseExp e = (b, x) := ⟨_, _, rfl⟩
    rw [hbx] at h
    simp only at h
    split at h
    · split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : Expr.equal (baseExp f).1 b = true := by simpa using List.find?_some hf
        have hfb : baseExp f = (b, (baseExp f).2) := by rw [← Expr.equal_eq hp]
        have h1 : prodR ρ rest
            = evalR ρ f * prodR ρ (removeFirst (fun y => (baseExp y).1.equal b) rest) := by
          rw [prodR_perm ρ (perm_find?_removeFirst _ rest f hf), prodR_cons]
        rw [prodR_cons, prodR_cons, h1, evalR_baseExp hbx, evalR_baseExp hfb, evalR_pow,
          evalR_addExp, Real.rpow_add ht]
        ring
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        rw [prodR_cons, prodR_cons, mergePowers_soundR_on ρ rest l' t' hm ht]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [prodR_cons, prodR_cons, mergePowers_soundR_on ρ rest l' t' hm ht]

/-- **`simp.collect-powers` is sound wherever the base it merged is positive.** -/
theorem collectPowers_soundR_on {e : Expr} {res : RuleResult} (ρ : EnvR)
    (h : collectPowers.apply e = some res)
    (ht : ∀ es l t, e = .mul es → mergePowers es = some (l, t) → 0 < evalR ρ t) :
    evalR ρ e = evalR ρ res.result := by
  cases e <;> simp only [collectPowers, collectPowersApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    simp only [Option.some.injEq] at h; subst h
    rw [evalR_mul, evalR_mul]
    exact (mergePowers_soundR_on ρ es l t hm (ht es l t rfl hm)).symm
  · simp at h

/-- **…and it is not sound without that hypothesis.** At `x = 0` the rule turns `x·x⁻¹` into `x⁰`,
that is `0` into `1`. This is the usual computer-algebra convention (`x/x` simplifies to `1`), so
the engine keeps the rule; the point is that the assumption is now explicit. -/
theorem not_collectPowers_soundR : ¬ RuleSoundR collectPowers := by
  intro hs
  have h := hs (.mul [.var "x", .pow (.var "x") (.num (Q.ofInt (-1)))]) _ rfl (fun _ => 0)
  norm_num [evalR_mul, prodR_cons, prodR_nil, evalR_var, evalR_pow, evalR_num, Q_val_ofInt,
    baseExp, addExp, Expr.one, removeFirst, Expr.equal, Expr.beq, Q_val_add, Q_val_one,
    Real.rpow_zero] at h

-- ---------------------------------------------------------------------------
-- simp.function: sound except that `exp (ln x) ⟶ x` needs `0 < x`
-- ---------------------------------------------------------------------------

/-- The justification the rule actually needs for its `exp ∘ ln` case. -/
theorem exp_log_sound {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x) = x := Real.exp_log hx

/-- The `sin u / cos u ⟶ tan u` case is unconditional: Mathlib's `Real.tan` is `sin / cos`
everywhere, junk values included. -/
theorem functionRules_tan_soundR (ρ : EnvR) {es : List Expr} {u : Expr} {others : List Expr}
    (h : findTan es = some (u, others)) :
    evalR ρ (Expr.mulN (.fn "tan" [u] :: others)) = evalR ρ (.mul es) := by
  obtain ⟨c, hc, hperm⟩ := findTan_perm es h
  rw [isCosInv_eq hc] at hperm
  rw [evalR_mul, prodR_perm ρ hperm, evalR_mulN]
  simp only [prodR_cons, evalR_fn₁, evalR_pow, evalR_num, Expr.minusOne, Q.minusOne, Q_val_ofInt]
  push_cast
  rw [Real.rpow_neg_one, applyFn, applyFn, applyFn, Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc]

/-- **`simp.function` is not unconditionally sound over ℝ**: at `x = -1`, `exp (ln x)` is `1`,
not `-1`, because `Real.log` is even. Every other case of the rule is unconditional. -/
theorem not_functionRules_soundR : ¬ RuleSoundR functionRules := by
  intro hs
  have h := hs (.fn "exp" [.fn "ln" [.var "x"]]) _ rfl (fun _ => -1)
  simp only [evalR_fn₁, applyFn_exp, applyFn_ln, evalR_var] at h
  rw [show ((-1 : ℝ)) = -(1 : ℝ) by norm_num, Real.log_neg_eq_log, Real.log_one, Real.exp_zero] at h
  norm_num at h

-- ---------------------------------------------------------------------------
-- The fold over the unconditionally sound rules
-- ---------------------------------------------------------------------------

/-- The subset of `simpRules` that is unconditionally sound over ℝ: everything except
`simp.collect-powers` and `simp.function`, each of which needs a side condition (above). -/
def simpRulesR : List (Rule simpW) := [flatten, identity, foldConstants, collectTerms, powerRules]

theorem simpRulesR_soundR : ∀ r ∈ simpRulesR, RuleSoundR r := by
  intro r hr
  simp only [simpRulesR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact flatten_soundR
  · exact identity_soundR
  · exact foldConstants_soundR
  · exact collectTerms_soundR
  · exact powerRules_soundR

/-- **Normalization with the unconditionally sound rules preserves the real value.** The proof is
`normalize_sound_for` — the same fold M1 used for the integer fragment, reused at ℝ because
`RewriteSound` is stated for an arbitrary `Congruence`. -/
theorem normalizeR_sound (e : Expr) (s : Array Step) :
    SemEqR e ((normalize simpRulesR e).run' s) :=
  normalize_sound_for semEqRCongruence simpRulesR simpRulesR_soundR e s

end MathProofs
end
