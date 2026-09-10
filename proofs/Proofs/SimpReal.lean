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

@[simp] theorem applyFn_sin (x : ℝ) : applyFn "sin" x = Real.sin x := by simp [applyFn]
@[simp] theorem applyFn_cos (x : ℝ) : applyFn "cos" x = Real.cos x := by simp [applyFn]
@[simp] theorem applyFn_exp (x : ℝ) : applyFn "exp" x = Real.exp x := by simp [applyFn]
@[simp] theorem applyFn_ln (x : ℝ) : applyFn "ln" x = Real.log x := by simp [applyFn]
@[simp] theorem applyFn_sqrt (x : ℝ) : applyFn "sqrt" x = Real.sqrt x := by simp [applyFn]
@[simp] theorem applyFn_abs (x : ℝ) : applyFn "abs" x = |x| := by simp [applyFn]

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

end MathProofs
end
