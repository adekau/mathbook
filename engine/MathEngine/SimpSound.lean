import MathEngine.SimpRules
import MathEngine.RewriteSound
/-!
# Soundness of the `simp.*` rules on the integer fragment

Each rule refines its input under `eval?` (definedness-preserving equality); `simplify_sound` is
the fold of these through `normalize_sound`. Rules on functions are vacuously sound here because
the fragment does not evaluate functions; M3 gives them real content over ℝ.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Numerals
-- ---------------------------------------------------------------------------

theorem Q.asInt?_ofInt (n : Int) : (Q.ofInt n).asInt? = some n := by
  simp [Q.asInt?, Q.ofInt, Rat.ofInt]

theorem Q.val_eq_intCast {q : Q} {n : Int} (h : q.asInt? = some n) : q.val = (n : Rat) := by
  simp only [Q.asInt?] at h
  split at h
  · rename_i hd; simp only [Option.some.injEq] at h; subst h; apply Rat.ext <;> simp [hd]
  · simp at h

theorem Q.asInt?_of_val {q : Q} {n : Int} (h : q.val = (n : Rat)) : q.asInt? = some n := by
  simp [Q.asInt?, h]

theorem Q.asInt?_add {a b : Q} {x y : Int} (ha : a.asInt? = some x) (hb : b.asInt? = some y) :
    (a + b).asInt? = some (x + y) :=
  Q.asInt?_of_val (by
    show a.val + b.val = _
    rw [Q.val_eq_intCast ha, Q.val_eq_intCast hb]; exact (Rat.intCast_add x y).symm)

theorem Q.asInt?_mul {a b : Q} {x y : Int} (ha : a.asInt? = some x) (hb : b.asInt? = some y) :
    (a * b).asInt? = some (x * y) :=
  Q.asInt?_of_val (by
    show a.val * b.val = _
    rw [Q.val_eq_intCast ha, Q.val_eq_intCast hb]; exact (Rat.intCast_mul x y).symm)

theorem Q.asInt?_zpow {a : Q} {x : Int} (ha : a.asInt? = some x) (n : Nat) :
    (a.zpow n).asInt? = some (x ^ n) :=
  Q.asInt?_of_val (by
    show a.val ^ (n : Int) = _
    rw [Q.val_eq_intCast ha, Rat.zpow_natCast]; exact (Rat.intCast_pow x n).symm)

theorem Q.asInt?_of_isZero {q : Q} (h : q.isZero = true) : q.asInt? = some 0 := by
  have hq : q.val = 0 := by simpa [Q.isZero] using h
  exact Q.asInt?_of_val (by rw [hq]; rfl)

theorem Q.asInt?_of_isOne {q : Q} (h : q.isOne = true) : q.asInt? = some 1 := by
  have hq : q.val = 1 := by simpa [Q.isOne] using h
  exact Q.asInt?_of_val (by rw [hq]; rfl)

theorem Q.asInt?_none_of_not_isInt {q : Q} (h : q.isInt = false) : q.asInt? = none := by
  simp only [Q.isInt, beq_eq_false_iff_ne, ne_eq] at h; simp [Q.asInt?, h]

theorem Q.asInt?_isInt {q : Q} {n : Int} (h : q.asInt? = some n) : n = q.val.num := by
  simp only [Q.asInt?] at h; split at h <;> simp_all

-- ---------------------------------------------------------------------------
-- `eval?` on the node shapes the rules produce
-- ---------------------------------------------------------------------------

theorem eval?_num (ρ : Env) (q : Q) : eval? ρ (.num q) = q.asInt? := rfl
theorem eval?_add (ρ : Env) (es : List Expr) : eval? ρ (.add es) = evalSum? ρ es := rfl
theorem eval?_mul (ρ : Env) (es : List Expr) : eval? ρ (.mul es) = evalProd? ρ es := rfl
theorem eval?_fn (ρ : Env) (f : String) (es : List Expr) : eval? ρ (.fn f es) = none := rfl
theorem eval?_pow (ρ : Env) (b x : Expr) :
    eval? ρ (.pow b x) = (do let v ← eval? ρ b; let n ← eval? ρ x; if 0 ≤ n then some (v ^ n.toNat) else none) := rfl
theorem evalSum?_nil (ρ : Env) : evalSum? ρ [] = some 0 := rfl
theorem evalSum?_cons (ρ : Env) (e : Expr) (es : List Expr) :
    evalSum? ρ (e :: es) = (do let v ← eval? ρ e; let s ← evalSum? ρ es; some (v + s)) := rfl
theorem evalProd?_nil (ρ : Env) : evalProd? ρ [] = some 1 := rfl
theorem evalProd?_cons (ρ : Env) (e : Expr) (es : List Expr) :
    evalProd? ρ (e :: es) = (do let v ← eval? ρ e; let p ← evalProd? ρ es; some (v * p)) := rfl
theorem eval?_zero (ρ : Env) : eval? ρ Expr.zero = some 0 := Q.asInt?_ofInt 0
theorem eval?_one (ρ : Env) : eval? ρ Expr.one = some 1 := Q.asInt?_ofInt 1

theorem eval?_of_isZero {e : Expr} (h : isZero e = true) (ρ : Env) : eval? ρ e = some 0 := by
  cases e <;> simp [isZero] at h; exact Q.asInt?_of_isZero h
theorem eval?_of_isOne {e : Expr} (h : isOne e = true) (ρ : Env) : eval? ρ e = some 1 := by
  cases e <;> simp [isOne] at h; exact Q.asInt?_of_isOne h

theorem eval?_addN (ρ : Env) (l : List Expr) : eval? ρ (addN l) = evalSum? ρ l := by
  match l with
  | [x] => simp only [addN, evalSum?_cons, evalSum?_nil]; cases eval? ρ x <;> simp
  | [] | _ :: _ :: _ => rfl

theorem eval?_mulN (ρ : Env) (l : List Expr) : eval? ρ (mulN l) = evalProd? ρ l := by
  match l with
  | [x] => simp only [mulN, evalProd?_cons, evalProd?_nil]; cases eval? ρ x <;> simp
  | [] | _ :: _ :: _ => rfl

/-- Unpack a defined power. -/
theorem eval?_pow_some {ρ : Env} {b x : Expr} {v : Int} (h : eval? ρ (.pow b x) = some v) :
    ∃ vb n, eval? ρ b = some vb ∧ eval? ρ x = some n ∧ 0 ≤ n ∧ v = vb ^ n.toNat := by
  rw [eval?_pow] at h
  cases hb : eval? ρ b with
  | none => simp [hb] at h
  | some vb =>
    cases hx : eval? ρ x with
    | none => simp [hb, hx] at h
    | some n =>
      rw [hb, hx] at h
      change (if 0 ≤ n then some (vb ^ n.toNat) else none) = some v at h
      split at h
      · simp only [Option.some.injEq] at h; exact ⟨vb, n, rfl, rfl, ‹_›, h.symm⟩
      · simp at h

-- ---------------------------------------------------------------------------
-- simp.flatten
-- ---------------------------------------------------------------------------

theorem evalSum?_unAdd (ρ : Env) (e : Expr) : evalSum? ρ (unAdd e) = eval? ρ e := by
  cases e <;> simp only [unAdd, evalSum?_cons, evalSum?_nil, eval?_add] <;> (try rfl) <;>
    (cases eval? ρ _ <;> simp)

theorem evalProd?_unMul (ρ : Env) (e : Expr) : evalProd? ρ (unMul e) = eval? ρ e := by
  cases e <;> simp only [unMul, evalProd?_cons, evalProd?_nil, eval?_mul] <;> (try rfl) <;>
    (cases eval? ρ _ <;> simp)

theorem evalSum?_flatMap_unAdd (ρ : Env) (es : List Expr) : evalSum? ρ (es.flatMap unAdd) = evalSum? ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, evalSum?_append, evalSum?_unAdd, ih, evalSum?_cons]

theorem evalProd?_flatMap_unMul (ρ : Env) (es : List Expr) : evalProd? ρ (es.flatMap unMul) = evalProd? ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.flatMap_cons, evalProd?_append, evalProd?_unMul, ih, evalProd?_cons]

theorem flatten_sound : RuleSound flatten := by
  intro e r h ρ v hv
  cases e <;> simp only [flatten, flattenApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h; subst h
    simpa [eval?_add, evalSum?_flatMap_unAdd] using hv
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h; subst h
    simpa [eval?_mul, evalProd?_flatMap_unMul] using hv

-- ---------------------------------------------------------------------------
-- simp.identity
-- ---------------------------------------------------------------------------

theorem evalSum?_filter_nonzero (ρ : Env) (es : List Expr) :
    evalSum? ρ (es.filter (fun e => !isZero e)) = evalSum? ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hz : isZero e = true
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, evalSum?_cons, eval?_of_isZero hz]
      cases evalSum? ρ es <;> simp
    · simp only [hz, Bool.not_false, ↓reduceIte, evalSum?_cons, ih]

theorem evalProd?_filter_nonone (ρ : Env) (es : List Expr) :
    evalProd? ρ (es.filter (fun e => !isOne e)) = evalProd? ρ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h1 : isOne e = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, evalProd?_cons, eval?_of_isOne h1]
      cases evalProd? ρ es <;> simp
    · simp only [h1, Bool.not_false, ↓reduceIte, evalProd?_cons, ih]

theorem evalProd?_zero_of_any (ρ : Env) (es : List Expr) (h : es.any isZero = true) (p : Int)
    (hp : evalProd? ρ es = some p) : p = 0 := by
  induction es generalizing p with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_true] at h
    simp only [evalProd?_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hp
    obtain ⟨v, hv, q, hq, rfl⟩ := hp
    rcases h with h | h
    · rw [eval?_of_isZero h] at hv; simp only [Option.some.injEq] at hv; subst hv; simp
    · rw [ih h q hq]; simp

theorem identity_sound : RuleSound identity := by
  intro e r h ρ v hv
  cases e with
  | add es =>
    match es, h with
    | [], h =>
      simp only [identity, identityApply, Option.some.injEq] at h; subst h
      simp only [eval?_add, evalSum?_nil, Option.some.injEq] at hv; subst hv; exact eval?_zero ρ
    | [e], h =>
      simp only [identity, identityApply, Option.some.injEq] at h; subst h
      rw [eval?_add, evalSum?_cons, evalSum?_nil] at hv
      cases he : eval? ρ e with
      | none => simp [he] at hv
      | some w => simp [he] at hv; rw [hv]
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [eval?_addN, evalSum?_filter_nonzero]; exact hv
  | mul es =>
    match es, h with
    | [], h =>
      simp only [identity, identityApply, Option.some.injEq] at h; subst h
      simp only [eval?_mul, evalProd?_nil, Option.some.injEq] at hv; subst hv; exact eval?_one ρ
    | [e], h =>
      simp only [identity, identityApply, Option.some.injEq] at h; subst h
      rw [eval?_mul, evalProd?_cons, evalProd?_nil] at hv
      cases he : eval? ρ e with
      | none => simp [he] at hv
      | some w => simp [he] at hv; rw [hv]
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rename_i hz
        rw [evalProd?_zero_of_any ρ _ hz v hv]; exact eval?_zero ρ
      · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; simp only [eval?_mulN, evalProd?_filter_nonone]; exact hv
  | _ => simp [identity, identityApply] at h

-- ---------------------------------------------------------------------------
-- simp.fold-constants
-- ---------------------------------------------------------------------------

theorem sumQ_sound (ρ : Env) : ∀ (es : List Expr) (acc : Q) (x s : Int), acc.asInt? = some x →
    evalSum? ρ (es.filter isNum) = some s →
    (List.foldl (fun s e => s + numOf e) acc (es.filter isNum)).asInt? = some (x + s)
  | [], acc, x, s, hacc, hs => by simp only [List.filter_nil, evalSum?_nil, Option.some.injEq] at hs; subst hs; simpa using hacc
  | e :: es, acc, x, s, hacc, hs => by
    by_cases hn : isNum e = true
    · cases e with
      | num q =>
        simp only [List.filter_cons, hn, ↓reduceIte, evalSum?_cons, eval?_num, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at hs ⊢
        obtain ⟨v, hv, s', hs', rfl⟩ := hs
        rw [List.foldl_cons]
        have := sumQ_sound ρ es (acc + numOf (.num q)) (x + v) s' (by simpa [numOf] using Q.asInt?_add hacc hv) hs'
        rw [this, Int.add_assoc]
      | _ => simp [isNum] at hn
    · simp only [List.filter_cons, hn, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact sumQ_sound ρ es acc x s hacc hs

theorem prodQ_sound (ρ : Env) : ∀ (es : List Expr) (acc : Q) (x p : Int), acc.asInt? = some x →
    evalProd? ρ (es.filter isNum) = some p →
    (List.foldl (fun s e => s * numOf e) acc (es.filter isNum)).asInt? = some (x * p)
  | [], acc, x, p, hacc, hp => by simp only [List.filter_nil, evalProd?_nil, Option.some.injEq] at hp; subst hp; simpa using hacc
  | e :: es, acc, x, p, hacc, hp => by
    by_cases hn : isNum e = true
    · cases e with
      | num q =>
        simp only [List.filter_cons, hn, ↓reduceIte, evalProd?_cons, eval?_num, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at hp ⊢
        obtain ⟨v, hv, p', hp', rfl⟩ := hp
        rw [List.foldl_cons]
        have := prodQ_sound ρ es (acc * numOf (.num q)) (x * v) p' (by simpa [numOf] using Q.asInt?_mul hacc hv) hp'
        rw [this, Int.mul_assoc]
      | _ => simp [isNum] at hn
    · simp only [List.filter_cons, hn, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact prodQ_sound ρ es acc x p hacc hp

theorem foldConstants_sound : RuleSound foldConstants := by
  intro e r h ρ v hv
  cases e <;> simp only [foldConstants, foldApply, reduceCtorEq] at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [eval?_add] at hv ⊢
    rw [← evalSum?_perm ρ (List.filter_append_perm isNum es), evalSum?_append] at hv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    rw [evalSum?_cons, eval?_num]
    have := sumQ_sound ρ es Q.zero 0 a (Q.asInt?_ofInt 0) ha
    simp only [sumQ, this, hb, Int.zero_add]; rfl
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i es _
    rw [eval?_mul] at hv ⊢
    rw [← evalProd?_perm ρ (List.filter_append_perm isNum es), evalProd?_append] at hv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    rw [evalProd?_cons, eval?_num]
    have := prodQ_sound ρ es Q.one 1 a (Q.asInt?_ofInt 1) ha
    simp only [prodQ, this, hb, Int.one_mul]; rfl

-- ---------------------------------------------------------------------------
-- simp.function (vacuous on the fragment)
-- ---------------------------------------------------------------------------

theorem functionRules_sound : RuleSound functionRules := by
  intro e r h ρ v hv
  cases e <;> simp [functionRules, functionApply] at h
  simp [eval?] at hv

-- ---------------------------------------------------------------------------
-- simp.power
-- ---------------------------------------------------------------------------

theorem isPosNum_pos {x : Expr} (h : isPosNum x = true) {ρ : Env} {n : Int} (hx : eval? ρ x = some n) : 0 < n := by
  cases x with
  | num q =>
    simp only [isPosNum, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨hneg, hz⟩ := h
    have hn := Q.asInt?_isInt hx
    have hd : q.val.den = 1 := by simp only [eval?_num, Q.asInt?] at hx; split at hx <;> simp_all
    simp only [Q.isNeg, decide_eq_false_iff_not, Int.not_lt] at hneg
    have : q.val.num ≠ 0 := by
      intro h0
      have hq0 : q.val = 0 := Rat.ext (by rw [h0]; rfl) (by rw [hd]; rfl)
      have : q.isZero = true := by simp [Q.isZero, hq0]
      simp_all
    omega
  | _ => simp [isPosNum] at h

theorem powerRules_sound : RuleSound powerRules := by
  intro e r h ρ v hv
  cases e <;> simp only [powerRules, powerApply, reduceCtorEq] at h
  rename_i b x
  obtain ⟨vb, n, hb, hx, hn, rfl⟩ := eval?_pow_some hv
  simp only [powerAt] at h
  split at h
  · -- b^0 = 1
    simp only [Option.some.injEq] at h; subst h; rename_i hz
    rw [eval?_of_isZero hz] at hx; simp only [Option.some.injEq] at hx; subst hx
    simp [eval?_one]
  split at h
  · -- b^1 = b
    simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [eval?_of_isOne h1] at hx; simp only [Option.some.injEq] at hx; subst hx
    simpa [Int.pow_one] using hb
  split at h
  · -- 1^n = 1
    simp only [Option.some.injEq] at h; subst h; rename_i h1
    rw [eval?_of_isOne h1] at hb; simp only [Option.some.injEq] at hb; subst hb
    simp [eval?_one, Int.one_pow]
  split at h
  · -- 0^n = 0, n > 0
    simp only [Option.some.injEq] at h; subst h; rename_i h0
    simp only [Bool.and_eq_true] at h0
    rw [eval?_of_isZero h0.1] at hb; simp only [Option.some.injEq] at hb; subst hb
    have hpos := isPosNum_pos h0.2 hx
    simp only [eval?_zero]; rw [Int.zero_pow (by omega)]
  · -- structural power rules
    cases b with
    | num p =>
      cases x with
      | num q =>
        simp only [powerNum, powNumeric] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          simp only [eval?_num] at hb hx ⊢
          have hq := Q.asInt?_isInt hx; subst hq
          obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
          rw [hk, Int.toNat_natCast]; exact Q.asInt?_zpow hb k
        · split at h
          · exfalso; rename_i hint _
            rw [eval?_num, Q.asInt?_none_of_not_isInt (by simpa using hint)] at hx; simp at hx
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
          obtain ⟨vb', mi, hb', hm, hmi, rfl⟩ := eval?_pow_some hb
          simp only [eval?_num] at hm hx
          rw [eval?_pow, hb', eval?_num, Q.asInt?_mul hm hx]
          obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hmi
          obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hn
          simp only [Int.toNat_natCast]
          simp
          exact ⟨Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg c),
            by rw [← Int.natCast_mul, Int.toNat_natCast, Int.pow_mul]⟩
        | _ => simp [powerNum] at h
      | _ => simp [powerNum] at h
    | _ => cases x <;> simp [powerNum] at h

-- ---------------------------------------------------------------------------
-- simp.collect-powers
-- ---------------------------------------------------------------------------

theorem baseExp_eval {ρ : Env} {e b x : Expr} {ve : Int} (he : baseExp e = (b, x)) (hv : eval? ρ e = some ve) :
    ∃ vb n, eval? ρ b = some vb ∧ eval? ρ x = some n ∧ 0 ≤ n ∧ ve = vb ^ n.toNat := by
  rcases baseExp_cases e b x he with rfl | ⟨rfl, rfl⟩
  · exact eval?_pow_some hv
  · exact ⟨ve, 1, hv, eval?_one ρ, by decide, by simp [Int.pow_one]⟩

theorem eval?_addExp {ρ : Env} {x y : Expr} {a b : Int} (hx : eval? ρ x = some a) (hy : eval? ρ y = some b) :
    eval? ρ (addExp x y) = some (a + b) := by
  cases x <;> cases y <;> simp only [addExp, eval?_add, evalSum?_cons, evalSum?_nil, hx, hy] <;>
    (try simp) <;> (try exact Q.asInt?_add hx hy)

theorem mergePowers_sound (ρ : Env) : ∀ (es l : List Expr) (t : Expr) (v : Int),
    mergePowers es = some (l, t) → evalProd? ρ es = some v → evalProd? ρ l = some v
  | [], _, _, _, h, _ => by simp [mergePowers] at h
  | e :: rest, l, t, v, h, hv => by
    simp only [mergePowers] at h
    obtain ⟨b, x, hbx⟩ : ∃ b x, baseExp e = (b, x) := ⟨_, _, rfl⟩
    rw [hbx] at h
    simp only at h
    simp only [evalProd?_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨ve, hve, vr, hvr, rfl⟩ := hv
    split at h
    · rename_i hbig
      split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : equal (baseExp f).1 b = true := by simpa using List.find?_some hf
        have hfb : baseExp f = (b, (baseExp f).2) := by rw [← equal_eq hp]
        rw [evalProd?_perm ρ (perm_find?_removeFirst _ rest f hf), evalProd?_cons] at hvr
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hvr
        obtain ⟨vf, hvf, vrf, hvrf, rfl⟩ := hvr
        obtain ⟨vb, nx, hb, hx, hnx, rfl⟩ := baseExp_eval hbx hve
        obtain ⟨vb', nf, hb', hxf, hnf, rfl⟩ := baseExp_eval hfb hvf
        rw [hb] at hb'; simp only [Option.some.injEq] at hb'; subst hb'
        rw [evalProd?_cons, eval?_pow, hb, eval?_addExp hx hxf, hvrf]
        obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hnx
        obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hnf
        simp [← Int.natCast_add, Int.pow_add, Int.mul_assoc]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        rw [evalProd?_cons, hve, mergePowers_sound ρ rest l' t' vr hm hvr]; rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [evalProd?_cons, hve, mergePowers_sound ρ rest l' t' vr hm hvr]; rfl

theorem collectPowers_sound : RuleSound collectPowers := by
  intro e r h ρ v hv
  cases e <;> simp only [collectPowers, collectPowersApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    simp only [Option.some.injEq] at h; subst h
    rw [eval?_mul] at hv ⊢; exact mergePowers_sound ρ es l t v hm hv
  · simp at h

-- ---------------------------------------------------------------------------
-- simp.collect-like-terms
-- ---------------------------------------------------------------------------

theorem coeffRest_eval {ρ : Env} {e : Expr} {c : Q} {t : Expr} {ve : Int} (he : coeffRest e = (c, t))
    (hv : eval? ρ e = some ve) : ∃ vc vt, c.asInt? = some vc ∧ eval? ρ t = some vt ∧ ve = vc * vt := by
  rcases coeffRest_cases e c t he with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ve, 1, hv, eval?_one ρ, by simp⟩
  · simp only [eval?_mul, evalProd?_cons, eval?_num, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨vc, hc, vr, hr, rfl⟩ := hv
    exact ⟨vc, vr, hc, by rw [eval?_mulN]; exact hr, rfl⟩
  · exact ⟨1, ve, Q.asInt?_ofInt 1, hv, by simp⟩

theorem mergeTerms_sound (ρ : Env) : ∀ (es l : List Expr) (t : Expr) (v : Int),
    mergeTerms es = some (l, t) → evalSum? ρ es = some v → evalSum? ρ l = some v
  | [], _, _, _, h, _ => by simp [mergeTerms] at h
  | e :: rest, l, t, v, h, hv => by
    simp only [mergeTerms] at h
    obtain ⟨c, u, hcu⟩ : ∃ c u, coeffRest e = (c, u) := ⟨_, _, rfl⟩
    rw [hcu] at h
    simp only at h
    simp only [evalSum?_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨ve, hve, vr, hvr, rfl⟩ := hv
    split at h
    · rename_i hbig
      split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : equal (coeffRest f).2 u = true := by simpa using List.find?_some hf
        have hfu : coeffRest f = ((coeffRest f).1, u) := by rw [← equal_eq hp]
        rw [evalSum?_perm ρ (perm_find?_removeFirst _ rest f hf), evalSum?_cons] at hvr
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hvr
        obtain ⟨vf, hvf, vrf, hvrf, rfl⟩ := hvr
        obtain ⟨vc, vt, hc, ht, rfl⟩ := coeffRest_eval hcu hve
        obtain ⟨vcf, vt', hcf, ht', rfl⟩ := coeffRest_eval hfu hvf
        rw [ht] at ht'; simp only [Option.some.injEq] at ht'; subst ht'
        rw [evalSum?_cons, eval?_mul, evalProd?_cons, eval?_num, Q.asInt?_add hc hcf, evalProd?_cons, ht, evalProd?_nil, hvrf]
        simp [Int.add_mul, Int.add_assoc]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        rw [evalSum?_cons, hve, mergeTerms_sound ρ rest l' t' vr hm hvr]; rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [evalSum?_cons, hve, mergeTerms_sound ρ rest l' t' vr hm hvr]; rfl

theorem collectTerms_sound : RuleSound collectTerms := by
  intro e r h ρ v hv
  cases e <;> simp only [collectTerms, collectTermsApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    simp only [Option.some.injEq] at h; subst h
    rw [eval?_add] at hv ⊢; exact mergeTerms_sound ρ es l t v hm hv
  · simp at h

-- ---------------------------------------------------------------------------
-- The fold
-- ---------------------------------------------------------------------------

theorem simpRules_sound : ∀ r ∈ simpRules, RuleSound r := by
  intro r hr
  simp only [simpRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact flatten_sound
  · exact identity_sound
  · exact foldConstants_sound
  · exact functionRules_sound
  · exact powerRules_sound
  · exact collectPowers_sound
  · exact collectTerms_sound

/-- **Simplification is sound on the integer fragment**: whatever value the input has, the
simplified term has the same value. -/
theorem simplify_sound (e : Expr) : Refines e (simplify0 e) :=
  normalize_sound simpRules simpRules_sound e #[]

end MathEngine
