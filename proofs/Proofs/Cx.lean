import Proofs.SimpReal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Norm
/-!
# The complex semantics, and what is proved over ℂ

`i` has no real meaning, so a term that mentions it is read here: `evalC` is `evalR` with
`Complex.I` for `i`, `Complex.cpow` (the principal branch) for powers, and the complex
functions. The complex rules of `ComplexRules.lean` are proved sound over ℂ, the four algebraic
simplification rules and the structural power rules are proved again over ℂ (their real proofs
port almost verbatim), and the exact trigonometric values are proved over ℝ first and cast.

The principal branch has consequences the real semantics never met: `ln (exp x) = x` fails at
`x = 2πi` (`not_functionRules_soundC`), while `b^m·b^n = b^(m+n)` needs only `b ≠ 0`
(`Complex.cpow_add`) rather than `0 < b`. The ledger (`Rpc.lean`) reports both columns.
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expr
open Complex (I)

/-- Complex-valued environment. -/
abbrev EnvC := String → ℂ

/-- The constants: `π` and the imaginary unit `i`; anything else is the junk value 0. -/
def constC (f : String) : ℂ := if f = "π" then (Real.pi : ℂ) else if f = "i" then I else 0

@[simp] theorem constC_pi : constC "π" = (Real.pi : ℂ) := by simp [constC]
@[simp] theorem constC_i : constC "i" = I := by simp [constC]

/-- The unary functions over ℂ. `abs` is the modulus, `conj`, `re`, `im` as expected. -/
def applyFnC (f : String) (z : ℂ) : ℂ :=
  match f with
  | "sin" => Complex.sin z
  | "cos" => Complex.cos z
  | "tan" => Complex.tan z
  | "exp" => Complex.exp z
  | "ln" => Complex.log z
  | "sqrt" => z ^ ((1 : ℂ) / 2)
  | "abs" => (‖z‖ : ℂ)
  | "conj" => (starRingEnd ℂ) z
  | "re" => (z.re : ℂ)
  | "im" => (z.im : ℂ)
  | _ => 0

@[simp] theorem applyFnC_sin (z : ℂ) : applyFnC "sin" z = Complex.sin z := by simp [applyFnC]
@[simp] theorem applyFnC_cos (z : ℂ) : applyFnC "cos" z = Complex.cos z := by simp [applyFnC]
@[simp] theorem applyFnC_tan (z : ℂ) : applyFnC "tan" z = Complex.tan z := by simp [applyFnC]
@[simp] theorem applyFnC_exp (z : ℂ) : applyFnC "exp" z = Complex.exp z := by simp [applyFnC]
@[simp] theorem applyFnC_ln (z : ℂ) : applyFnC "ln" z = Complex.log z := by simp [applyFnC]
@[simp] theorem applyFnC_abs (z : ℂ) : applyFnC "abs" z = (‖z‖ : ℂ) := by simp [applyFnC]
@[simp] theorem applyFnC_conj (z : ℂ) : applyFnC "conj" z = (starRingEnd ℂ) z := by simp [applyFnC]
@[simp] theorem applyFnC_re (z : ℂ) : applyFnC "re" z = (z.re : ℂ) := by simp [applyFnC]
@[simp] theorem applyFnC_im (z : ℂ) : applyFnC "im" z = (z.im : ℂ) := by simp [applyFnC]

mutual
  /-- Meaning of an expression in ℂ. -/
  def evalC (ρ : EnvC) : Expr → ℂ
    | .num q => (q.val : ℂ)
    | .var x => ρ x
    | .add es => sumC ρ es
    | .mul es => prodC ρ es
    | .pow b e => (evalC ρ b) ^ (evalC ρ e)
    | .fn f [] => constC f
    | .fn f [a] => applyFnC f (evalC ρ a)
    | .fn _ _ => 0
    | .matrix _ => 0
  def sumC (ρ : EnvC) : List Expr → ℂ
    | [] => 0
    | e :: es => evalC ρ e + sumC ρ es
  def prodC (ρ : EnvC) : List Expr → ℂ
    | [] => 1
    | e :: es => evalC ρ e * prodC ρ es
end

@[simp] theorem evalC_num (ρ : EnvC) (q : Q) : evalC ρ (.num q) = (q.val : ℂ) := rfl
@[simp] theorem evalC_var (ρ : EnvC) (x : String) : evalC ρ (.var x) = ρ x := rfl
@[simp] theorem evalC_add (ρ : EnvC) (es : List Expr) : evalC ρ (.add es) = sumC ρ es := rfl
@[simp] theorem evalC_mul (ρ : EnvC) (es : List Expr) : evalC ρ (.mul es) = prodC ρ es := rfl
@[simp] theorem evalC_pow (ρ : EnvC) (b e : Expr) :
    evalC ρ (.pow b e) = (evalC ρ b) ^ (evalC ρ e) := rfl
@[simp] theorem evalC_fn₁ (ρ : EnvC) (f : String) (a : Expr) :
    evalC ρ (.fn f [a]) = applyFnC f (evalC ρ a) := rfl
@[simp] theorem evalC_fn₀ (ρ : EnvC) (f : String) : evalC ρ (.fn f []) = constC f := rfl
@[simp] theorem evalC_matrix (ρ : EnvC) (rows : List (List Expr)) : evalC ρ (.matrix rows) = 0 := rfl
@[simp] theorem sumC_nil (ρ : EnvC) : sumC ρ [] = 0 := rfl
@[simp] theorem sumC_cons (ρ : EnvC) (e : Expr) (es : List Expr) :
    sumC ρ (e :: es) = evalC ρ e + sumC ρ es := rfl
@[simp] theorem prodC_nil (ρ : EnvC) : prodC ρ [] = 1 := rfl
@[simp] theorem prodC_cons (ρ : EnvC) (e : Expr) (es : List Expr) :
    prodC ρ (e :: es) = evalC ρ e * prodC ρ es := rfl

@[simp] theorem evalC_zero (ρ : EnvC) : evalC ρ Expr.zero = 0 := by
  simp [Expr.zero, Q.zero, Q.ofInt]
@[simp] theorem evalC_one (ρ : EnvC) : evalC ρ Expr.one = 1 := by
  simp [Expr.one, Q.one, Q.ofInt]
@[simp] theorem evalC_iE (ρ : EnvC) : evalC ρ iE = I := by simp [iE]
@[simp] theorem evalC_piE (ρ : EnvC) : evalC ρ piE = (Real.pi : ℂ) := by simp [piE]

theorem sumC_append (ρ : EnvC) (l₁ l₂ : List Expr) :
    sumC ρ (l₁ ++ l₂) = sumC ρ l₁ + sumC ρ l₂ := by
  induction l₁ with
  | nil => simp
  | cons e es ih => simp [ih, add_assoc]

theorem prodC_append (ρ : EnvC) (l₁ l₂ : List Expr) :
    prodC ρ (l₁ ++ l₂) = prodC ρ l₁ * prodC ρ l₂ := by
  induction l₁ with
  | nil => simp
  | cons e es ih => simp [ih, mul_assoc]

theorem sumC_perm (ρ : EnvC) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : sumC ρ l₁ = sumC ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l => simp; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem prodC_perm (ρ : EnvC) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : prodC ρ l₁ = prodC ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l => simp; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `addN`/`mulN` collapse a singleton, so they agree with the list forms. -/
@[simp] theorem evalC_addN (ρ : EnvC) (l : List Expr) : evalC ρ (Expr.addN l) = sumC ρ l := by
  match l with
  | [x] => simp [Expr.addN]
  | [] | _ :: _ :: _ => rfl

@[simp] theorem evalC_mulN (ρ : EnvC) (l : List Expr) : evalC ρ (Expr.mulN l) = prodC ρ l := by
  match l with
  | [x] => simp [Expr.mulN]
  | [] | _ :: _ :: _ => rfl

/-- A simplification rule is ℂ-sound when every rewrite it performs preserves the complex value. -/
abbrev RuleSoundC (r : Rule simpW) : Prop := ∀ e res, r.apply e = some res → ∀ ρ : EnvC, evalC ρ e = evalC ρ res.result
/-- The same for a plain (pipeline) rule. -/
abbrev PlainSoundC (r : PlainRule) : Prop := ∀ e res, r.apply e = some res → ∀ ρ : EnvC, evalC ρ e = evalC ρ res.result

-- ---------------------------------------------------------------------------
-- The algebraic simplification rules, ported from the real proofs
-- ---------------------------------------------------------------------------

theorem evalC_of_isZero {e : Expr} (h : Expr.isZero e = true) (ρ : EnvC) : evalC ρ e = 0 := by
  cases e <;> simp [Expr.isZero] at h
  rename_i q
  have : q.val = 0 := by simpa [Q.isZero] using h
  simp [this]

theorem evalC_of_isOne {e : Expr} (h : Expr.isOne e = true) (ρ : EnvC) : evalC ρ e = 1 := by
  cases e <;> simp [Expr.isOne] at h
  rename_i q
  have : q.val = 1 := by simpa [Q.isOne] using h
  simp [this]

theorem evalC_of_isNum {e : Expr} (h : Expr.isNum e = true) (ρ : EnvC) : evalC ρ e = (numOf e).val := by
  cases e <;> simp [Expr.isNum] at h
  rfl

-- ---------------------------------------------------------------------------
-- simp.flatten
-- ---------------------------------------------------------------------------

theorem sumC_unAdd (ρ : EnvC) (e : Expr) : sumC ρ (unAdd e) = evalC ρ e := by
  cases e <;> simp [unAdd]

theorem prodC_unMul (ρ : EnvC) (e : Expr) : prodC ρ (unMul e) = evalC ρ e := by
  cases e <;> simp [unMul]

theorem sumC_flatMap_unAdd (ρ : EnvC) (es : List Expr) :
    sumC ρ (es.flatMap unAdd) = sumC ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, sumC_append, sumC_unAdd, ih, sumC_cons]

theorem prodC_flatMap_unMul (ρ : EnvC) (es : List Expr) :
    prodC ρ (es.flatMap unMul) = prodC ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, prodC_append, prodC_unMul, ih, prodC_cons]

theorem flatten_soundC : RuleSoundC flatten := by
  intro e r h ρ
  cases e <;> simp only [flatten, flattenApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; simp [sumC_flatMap_unAdd]
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; simp [prodC_flatMap_unMul]

-- ---------------------------------------------------------------------------
-- simp.identity
-- ---------------------------------------------------------------------------

theorem sumC_filter_nonzero (ρ : EnvC) (es : List Expr) :
    sumC ρ (es.filter (fun e => !Expr.isZero e)) = sumC ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hz : Expr.isZero e = true
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, sumC_cons,
        evalC_of_isZero hz, zero_add]
    · simp only [hz, Bool.not_false, ↓reduceIte, sumC_cons, ih]

theorem prodC_filter_nonone (ρ : EnvC) (es : List Expr) :
    prodC ρ (es.filter (fun e => !Expr.isOne e)) = prodC ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h1 : Expr.isOne e = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, prodC_cons,
        evalC_of_isOne h1, one_mul]
    · simp only [h1, Bool.not_false, ↓reduceIte, prodC_cons, ih]

theorem prodC_eq_zero_of_any (ρ : EnvC) (es : List Expr) (h : es.any Expr.isZero = true) :
    prodC ρ es = 0 := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · simp [evalC_of_isZero h]
    · simp [ih h]

theorem identity_soundC : RuleSoundC identity := by
  intro e r h ρ
  cases e with
  | add es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [e], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [evalC_addN, evalC_add, sumC_filter_nonzero]
  | mul es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [e], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rename_i hz
        simp only [evalC_mul, evalC_zero]
        exact prodC_eq_zero_of_any ρ _ hz
      · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; simp only [evalC_mulN, evalC_mul, prodC_filter_nonone]
  | _ => simp [identity, identityApply] at h

-- ---------------------------------------------------------------------------
-- simp.fold-constants  (over ℚ→ℂ this is exact: 1/2 + 1/3 = 5/6 is now provable)
-- ---------------------------------------------------------------------------

theorem sumQ_evalC' (ρ : EnvC) : ∀ (l : List Expr) (acc : Q), (∀ e ∈ l, Expr.isNum e = true) →
    ((l.foldl (fun s e => s + numOf e) acc).val : ℂ) = (acc.val : ℂ) + sumC ρ l
  | [], acc, _ => by simp
  | e :: es, acc, hall => by
    rw [List.foldl_cons, sumQ_evalC' ρ es _ (fun a ha => hall a (List.mem_cons_of_mem _ ha)),
      sumC_cons, evalC_of_isNum (hall e (by simp))]
    simp only [Q_val_add, Rat.cast_add]
    ring

theorem prodQ_evalC' (ρ : EnvC) : ∀ (l : List Expr) (acc : Q), (∀ e ∈ l, Expr.isNum e = true) →
    ((l.foldl (fun s e => s * numOf e) acc).val : ℂ) = (acc.val : ℂ) * prodC ρ l
  | [], acc, _ => by simp
  | e :: es, acc, hall => by
    rw [List.foldl_cons, prodQ_evalC' ρ es _ (fun a ha => hall a (List.mem_cons_of_mem _ ha)),
      prodC_cons, evalC_of_isNum (hall e (by simp))]
    simp only [Q_val_mul, Rat.cast_mul]
    ring

theorem sumQ_evalC (ρ : EnvC) (l : List Expr) (hall : ∀ e ∈ l, Expr.isNum e = true) :
    ((sumQ l).val : ℂ) = sumC ρ l := by
  have h := sumQ_evalC' ρ l Q.zero hall
  simp only [Q_val_zero, Rat.cast_zero, zero_add] at h
  exact h

theorem prodQ_evalC (ρ : EnvC) (l : List Expr) (hall : ∀ e ∈ l, Expr.isNum e = true) :
    ((prodQ l).val : ℂ) = prodC ρ l := by
  have h := prodQ_evalC' ρ l Q.one hall
  simp only [Q_val_one, Rat.cast_one, one_mul] at h
  exact h

theorem foldConstants_soundC : RuleSoundC foldConstants := by
  intro e r h ρ
  have hnums : ∀ (es : List Expr), ∀ a ∈ es.filter Expr.isNum, Expr.isNum a = true :=
    fun es a ha => (List.mem_filter.mp ha).2
  cases e <;> simp only [foldConstants, foldApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [evalC_add, evalC_add, sumC_cons, evalC_num, sumQ_evalC ρ _ (hnums es),
      ← sumC_perm ρ (List.filter_append_perm Expr.isNum es), sumC_append]
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [evalC_mul, evalC_mul, prodC_cons, evalC_num, prodQ_evalC ρ _ (hnums es),
      ← prodC_perm ρ (List.filter_append_perm Expr.isNum es), prodC_append]

-- ---------------------------------------------------------------------------
-- simp.collect-like-terms
-- ---------------------------------------------------------------------------

theorem evalC_coeffRest {e : Expr} {c : Q} {t : Expr} (h : coeffRest e = (c, t)) (ρ : EnvC) :
    evalC ρ e = (c.val : ℂ) * evalC ρ t := by
  rcases coeffRest_cases e c t h with ⟨he, ht⟩ | ⟨r, he, ht⟩ | ⟨he, hc⟩
  · subst he; subst ht; simp
  · subst he; subst ht; simp
  · subst he; subst hc; simp

theorem mergeTerms_soundC (ρ : EnvC) : ∀ (es l : List Expr) (t : Expr),
    mergeTerms es = some (l, t) → sumC ρ l = sumC ρ es
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
        have h1 : sumC ρ rest
            = evalC ρ f + sumC ρ (removeFirst (fun x => (coeffRest x).2.equal u) rest) := by
          rw [sumC_perm ρ (perm_find?_removeFirst _ rest f hf), sumC_cons]
        rw [sumC_cons, sumC_cons, h1, evalC_coeffRest hcu, evalC_coeffRest hfu]
        simp only [evalC_mul, prodC_cons, prodC_nil, evalC_num, Q_val_add, Rat.cast_add]
        ring
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        rw [sumC_cons, sumC_cons, mergeTerms_soundC ρ rest l' t' hm]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [sumC_cons, sumC_cons, mergeTerms_soundC ρ rest l' t' hm]

theorem collectTerms_soundC : RuleSoundC collectTerms := by
  intro e r h ρ
  cases e <;> simp only [collectTerms, collectTermsApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    simp only [Option.some.injEq] at h; subst h
    rw [evalC_add, evalC_add]; exact (mergeTerms_soundC ρ es l t hm).symm
  · simp at h


-- ---------------------------------------------------------------------------
-- simp.power over ℂ: the principal branch agrees with the real power on positive rational bases
-- ---------------------------------------------------------------------------

/-- The real fact behind the exact-root case, extracted so both semantics use it. -/
theorem exactRoot_rpow {p q : Q} {rr : ℚ} (hroot : exactRoot p.val q.val.den = some rr) (hone : q.val.num = 1) :
    ((p.val : ℚ) : ℝ) ^ ((q.val : ℚ) : ℝ) = ((rr : ℚ) : ℝ) := by
  obtain ⟨hnn, hpow⟩ := exactRoot_spec (Rat.den_nz q.val) hroot
  have hqv : (q.val : ℝ) = (((q.val.den : ℕ) : ℝ))⁻¹ := by
    rw [Rat.cast_def, hone]; norm_num
  rw [hqv]
  have hp : ((p.val : ℚ) : ℝ) = ((rr : ℚ) : ℝ) ^ (q.val.den) := by
    rw [← hpow]; push_cast; ring
  rw [hp]
  exact Real.pow_rpow_inv_natCast (by exact_mod_cast hnn) (Rat.den_nz q.val)

theorem Q_cast_isIntC {q : Q} (h : q.isInt = true) : (q.val : ℂ) = ((q.val.num : ℤ) : ℂ) := by
  have hd : q.val.den = 1 := by simpa [Q.isInt] using h
  rw [Rat.cast_def, hd]; norm_num

theorem isPosNum_ne_zeroC {x : Expr} (h : isPosNum x = true) (ρ : EnvC) : evalC ρ x ≠ 0 := by
  cases x <;> simp only [isPosNum, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    reduceCtorEq] at h
  rename_i q
  have : q.val ≠ 0 := by
    intro hz; rw [show q.isZero = true by simp [Q.isZero, hz]] at h; simp at h
  simpa using this

theorem powerRules_soundC : RuleSoundC powerRules := by
  intro e r h ρ
  cases e <;> simp only [powerRules, powerApply, reduceCtorEq] at h
  rename_i b x
  simp only [powerAt] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i hz
    rw [evalC_pow, evalC_of_isZero hz]
    show _ = evalC ρ Expr.one
    rw [evalC_one, Complex.cpow_zero]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [evalC_pow, evalC_of_isOne h1, Complex.cpow_one]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [evalC_pow, evalC_of_isOne h1]
    show _ = evalC ρ Expr.one
    rw [evalC_one, Complex.one_cpow]
  split at h
  · simp only [Option.some.injEq] at h; subst h; rename_i h0
    simp only [Bool.and_eq_true] at h0
    rw [evalC_pow, evalC_of_isZero h0.1]
    show _ = evalC ρ Expr.zero
    rw [evalC_zero, Complex.zero_cpow (isPosNum_ne_zeroC h0.2 ρ)]
  · cases b with
    | num p =>
      cases x with
      | num q =>
        simp only [powerNum, powNumeric] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; rename_i hint
          rw [evalC_pow, evalC_num, evalC_num, Q_cast_isIntC hint, Complex.cpow_intCast]
          show _ = ((p.val ^ q.val.num : ℚ) : ℂ)
          rw [Rat.cast_zpow]
        · split at h
          · rename_i hone
            split at h
            · rename_i rr hroot
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨hnn, hpow⟩ := exactRoot_spec (Rat.den_nz q.val) hroot
              have hnum1 : q.val.num = 1 := by simpa using hone
              rw [evalC_pow, evalC_num, evalC_num]
              show (((p.val : ℚ) : ℂ)) ^ (((q.val : ℚ)) : ℂ) = ((rr : ℚ) : ℂ)
              have hp0 : (0 : ℝ) ≤ ((p.val : ℚ) : ℝ) := by
                rw [← hpow]; push_cast; positivity
              rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast,
                ← Complex.ofReal_cpow hp0, exactRoot_rpow hroot (by simpa using hone)]
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
          have hmn : ((mq * n' : Q).val : ℂ) = ((mq.val.num * n'.val.num : ℤ) : ℂ) := by
            rw [Q_val_mul, Rat.cast_mul, Q_cast_isIntC hm, Q_cast_isIntC hn']; push_cast; ring
          show ((evalC ρ b') ^ (evalC ρ (Expr.num mq))) ^ (evalC ρ (Expr.num n'))
            = (evalC ρ b') ^ (evalC ρ (Expr.num (mq * n')))
          rw [evalC_num, evalC_num, evalC_num, hmn, Q_cast_isIntC hm, Q_cast_isIntC hn',
            Complex.cpow_intCast, Complex.cpow_intCast, Complex.cpow_intCast, zpow_mul]
        | _ => simp [powerNum] at h
      | _ => simp [powerNum] at h
    | _ => cases x <;> simp [powerNum] at h


end MathProofs
end
