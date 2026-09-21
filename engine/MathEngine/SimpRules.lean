import MathEngine.Rewrite
import MathEngine.Semantics
import MathEngine.Print
/-!
# `simp.*` — the simplification rules, each with its termination obligation

Ported from `simplify.ts`. Every rule is a `Rule simpW`: it comes with a proof that it strictly
decreases the weighted node count under the weights below. The weights were chosen by tabulating
the rules (see the book, "why simplification terminates"):

| node | weight | why |
|---|---|---|
| num | 2 | cheapest; rules replace whole nodes by a numeral |
| add, mul | 4 | `add [] ⟶ 0` needs add > num; `ln(b^p) ⟶ p·ln b` needs pow > mul |
| pow | 5 | `sqrt a ⟶ a^(1/2)` needs fn > pow + num |
| var, fn, matrix | 8 | `t·t ⟶ t^2` needs every non-numeral base to outweigh pow + num = 7 |

Three rules are guarded slightly more tightly than in the reference so that the obligation holds
for *all* inputs, not just normalized ones (`bigBase`), one case is dropped (`8^(2/3)`, an exact
root with a non-unit numerator: same shape before and after), and `(ab)^n ⟶ a^n b^n` moves to the
`expand` rule set because it duplicates the exponent and no additive measure can decrease.
-/
set_option linter.unusedSimpArgs false  -- the shared `rule_leaf` simp set is deliberately broad

namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Weights
-- ---------------------------------------------------------------------------

def simpWeight : Expr → Nat
  | .num _ => 2
  | .var _ => 8
  | .add _ => 4
  | .mul _ => 4
  | .pow _ _ => 5
  | .fn _ _ => 8
  | .matrix _ => 8

def simpW : Weights where
  w := simpWeight
  pos e := by cases e <;> simp [simpWeight]
  head e cs := by
    cases e <;> try rfl
    match cs with
    | [_, _] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => rfl

/-- Every node weighs at least 2 under `simpW`. -/
theorem measure_ge_two (e : Expr) : 2 ≤ measure simpW e := by
  rw [measure_eq]; cases e <;> simp [simpW, simpWeight] <;> omega

local notation "M" => measure simpW
local notation "ML" => measureList simpW

theorem ML_cons (e : Expr) (es : List Expr) : ML (e :: es) = M e + ML es := rfl

/-- A base that outweighs `pow + num = 7`: everything except numerals and sums/products with
fewer than two arguments. -/
def bigBase : Expr → Bool
  | .num _ => false
  | .add (_ :: _ :: _) | .mul (_ :: _ :: _) => true
  | .add _ | .mul _ => false
  | _ => true

theorem M_num (q : Q) : M (.num q) = 2 := rfl
theorem M_var (x : String) : M (.var x) = 8 := rfl
theorem M_add (es : List Expr) : M (.add es) = 4 + ML es := rfl
theorem M_mul (es : List Expr) : M (.mul es) = 4 + ML es := rfl
theorem M_pow (b x : Expr) : M (.pow b x) = 5 + M b + M x := rfl
theorem M_fn (f : String) (es : List Expr) : M (.fn f es) = 8 + ML es := rfl
theorem M_matrix (rows : List (List Expr)) : M (.matrix rows) = 8 + measureRows simpW rows := rfl
theorem ML_nil : ML [] = 0 := rfl
theorem M_zero : M Expr.zero = 2 := rfl
theorem M_one : M Expr.one = 2 := rfl

theorem bigBase_measure {e : Expr} (h : bigBase e = true) : 8 ≤ M e := by
  cases e with
  | add es => match es, h with
    | x :: y :: _, _ => rw [M_add, ML_cons, ML_cons]; have := measure_ge_two x; have := measure_ge_two y; omega
  | mul es => match es, h with
    | x :: y :: _, _ => rw [M_mul, ML_cons, ML_cons]; have := measure_ge_two x; have := measure_ge_two y; omega
  | num _ => simp [bigBase] at h
  | pow b x => rw [M_pow]; have := measure_ge_two b; have := measure_ge_two x; omega
  | var _ => rw [M_var]; omega
  | fn _ _ => rw [M_fn]; omega
  | matrix _ => rw [M_matrix]; omega

-- ---------------------------------------------------------------------------
-- Generic list lemmas about the measure
-- ---------------------------------------------------------------------------

theorem ML_filter_le (p : Expr → Bool) (es : List Expr) : ML (es.filter p) ≤ ML es := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hp : p e = true
    · simp only [hp, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, measureList]; omega

theorem ML_filter_lt (p : Expr → Bool) (es : List Expr) (h : es.any (fun e => !p e) = true) :
    ML (es.filter p) < ML es := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp only [List.filter_cons]
    have hle := ML_filter_le p es
    have h2 := measure_ge_two e
    by_cases hp : p e = true
    · have h' : es.any (fun e => !p e) = true := by
        rcases h with h | h
        · rw [hp] at h; exact absurd h (by decide)
        · exact h
      have := ih h'
      simp only [hp, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, measureList]; omega

/-- Splitting a list by a predicate splits its measure. -/
theorem ML_filter_split (p : Expr → Bool) (es : List Expr) :
    ML es = ML (es.filter p) + ML (es.filter (fun e => !p e)) := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hp : p e = true
    · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.not_false, Bool.false_eq_true, ↓reduceIte, measureList]; omega

theorem ML_removeFirst {p : Expr → Bool} {f : Expr} {es : List Expr} (h : es.find? p = some f) :
    ML (removeFirst p es) + M f = ML es := by
  have := measureList_perm simpW (perm_find?_removeFirst p es f h)
  simp only [measureList] at this; omega

theorem M_addN_le (l : List Expr) : M (addN l) ≤ 4 + ML l := by
  match l with
  | [e] => simp only [addN, measureList]; omega
  | [] | _ :: _ :: _ => simp [addN, measure, simpW, simpWeight]

theorem M_mulN_le (l : List Expr) : M (mulN l) ≤ 4 + ML l := by
  match l with
  | [e] => simp only [mulN, measureList]; omega
  | [] | _ :: _ :: _ => simp [mulN, measure, simpW, simpWeight]

-- ---------------------------------------------------------------------------
-- Helpers shared with the reference implementation
-- ---------------------------------------------------------------------------

def isAdd : Expr → Bool | .add _ => true | _ => false
def isMul : Expr → Bool | .mul _ => true | _ => false
def unAdd : Expr → List Expr | .add xs => xs | e => [e]
def unMul : Expr → List Expr | .mul xs => xs | e => [e]
def numOf : Expr → Q | .num q => q | _ => Q.zero
def sumQ (es : List Expr) : Q := es.foldl (fun s e => s + numOf e) Q.zero
def prodQ (es : List Expr) : Q := es.foldl (fun s e => s * numOf e) Q.one
/-- `base ^ exp`; a non-power is `base ^ 1`. -/
def baseExp : Expr → Expr × Expr | .pow b x => (b, x) | e => (e, Expr.one)
/-- Sum of two exponents, folded when both are numerals. -/
def addExp (a b : Expr) : Expr :=
  match a, b with
  | .num p, .num q => .num (p + q)
  | _, _ => .add [a, b]

/-- Binary search for a `y` with `y ^ n = x`. Top-level (rather than a `let rec`) so that
`proofs/` can state its specification: it only ever returns a `y` whose power it has *checked*,
so correctness is read straight off the final guard and completeness is never needed. -/
def natRootGo (n x : Nat) : Nat → Nat → Nat → Option Nat
  | _, _, 0 => none
  | lo, hi, fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if mid ^ n < x then natRootGo n x (mid + 1) hi fuel else natRootGo n x lo mid fuel
    else if lo ^ n = x then some lo else none

/-- Exact natural `n`-th root of `x`, if there is one. -/
def natRoot (n x : Nat) : Option Nat :=
  if x < 2 then some x else natRootGo n x 1 x 200

/-- Integer `n`-th root of a rational, if exact. -/
def exactRoot (r : Rat) (n : Nat) : Option Rat :=
  if r < 0 || n = 0 then none else
  do let a ← natRoot n r.num.natAbs; let b ← natRoot n r.den; some (mkRat a b)

-- ---------------------------------------------------------------------------
-- simp.flatten (silent)
-- ---------------------------------------------------------------------------

def flattenApply : Expr → Option RuleResult
  | .add es => if es.any isAdd then some ⟨.add (es.flatMap unAdd), "associativity", none, none⟩ else none
  | .mul es => if es.any isMul then some ⟨.mul (es.flatMap unMul), "associativity", none, none⟩ else none
  | _ => none

theorem ML_unAdd_le (e : Expr) : ML (unAdd e) ≤ M e := by
  cases e <;> simp [unAdd, measure, simpW, simpWeight, measureList]
theorem ML_unAdd_lt (e : Expr) (h : isAdd e = true) : ML (unAdd e) < M e := by
  cases e <;> simp [isAdd] at h <;> simp [unAdd, measure, simpW, simpWeight]
theorem ML_unMul_le (e : Expr) : ML (unMul e) ≤ M e := by
  cases e <;> simp [unMul, measure, simpW, simpWeight, measureList]
theorem ML_unMul_lt (e : Expr) (h : isMul e = true) : ML (unMul e) < M e := by
  cases e <;> simp [isMul] at h <;> simp [unMul, measure, simpW, simpWeight]

theorem ML_flatMap_lt (f : Expr → List Expr) (p : Expr → Bool) (hle : ∀ e, ML (f e) ≤ M e)
    (hlt : ∀ e, p e = true → ML (f e) < M e) (es : List Expr) (h : es.any p = true) :
    ML (es.flatMap f) < ML es := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.flatMap_cons, List.any_cons, Bool.or_eq_true] at h ⊢
    have hb := ML_flatMap_le f hle es
    simp only [measureList_append, measureList] at *
    rcases h with h | h
    · have := hlt e h; omega
    · have := ih h; have := hle e; omega
where
  ML_flatMap_le (f : Expr → List Expr) (hle : ∀ e, ML (f e) ≤ M e) : ∀ es : List Expr, ML (es.flatMap f) ≤ ML es
    | [] => by simp [measureList]
    | e :: es => by
      simp only [List.flatMap_cons, measureList_append, measureList]
      have := hle e; have := ML_flatMap_le f hle es; omega

def flatten : Rule simpW where
  name := "simp.flatten"
  silent := true
  apply := flattenApply
  decreasing e r h := by
    cases e <;> simp only [flattenApply, reduceCtorEq] at h
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; rename_i hany
      simp only [M_add]; have := ML_flatMap_lt unAdd isAdd ML_unAdd_le ML_unAdd_lt _ hany; omega
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; rename_i hany
      simp only [M_mul]; have := ML_flatMap_lt unMul isMul ML_unMul_le ML_unMul_lt _ hany; omega

-- ---------------------------------------------------------------------------
-- simp.identity
-- ---------------------------------------------------------------------------

def identityApply : Expr → Option RuleResult
  | .add [] => some ⟨Expr.zero, "An empty sum is 0.", none, none⟩
  | .add [e] => some ⟨e, "A sum of one term is that term.", none, none⟩
  | .add es => if es.any isZero then some ⟨addN (es.filter (fun e => !isZero e)), "$a + 0 = a$: zero is the additive identity.", none, none⟩ else none
  | .mul [] => some ⟨Expr.one, "An empty product is 1.", none, none⟩
  | .mul [e] => some ⟨e, "A product of one factor is that factor.", none, none⟩
  | .mul es =>
    if es.any isZero then some ⟨Expr.zero, "$a \\cdot 0 = 0$: zero annihilates products.", none, none⟩
    else if es.any isOne then some ⟨mulN (es.filter (fun e => !isOne e)), "$a \\cdot 1 = a$: one is the multiplicative identity.", none, none⟩
    else none
  | _ => none

def identity : Rule simpW where
  name := "simp.identity"
  apply := identityApply
  decreasing e r h := by
    cases e with
    | add es =>
      match es, h with
      | [], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp [measure, measureList, simpW, simpWeight, Expr.zero]
      | [e], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp only [M_add, ML_cons, measureList]; omega
      | x :: y :: rest, h =>
        simp only [identityApply] at h
        split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; rename_i hany
        have h1 := M_addN_le ((x :: y :: rest).filter (fun e => !isZero e))
        have h2 := ML_filter_lt (fun e => !isZero e) (x :: y :: rest) (by simpa using hany)
        simp only [M_add] at *; omega
    | mul es =>
      match es, h with
      | [], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp [measure, measureList, simpW, simpWeight, Expr.one]
      | [e], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp only [M_mul, ML_cons, measureList]; omega
      | x :: y :: rest, h =>
        simp only [identityApply] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; simp only [M_zero, M_mul]; omega
        · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
          subst h; rename_i hany
          have h1 := M_mulN_le ((x :: y :: rest).filter (fun e => !isOne e))
          have h2 := ML_filter_lt (fun e => !isOne e) (x :: y :: rest) (by simpa using hany)
          simp only [M_mul] at *; omega
    | _ => simp [identityApply] at h

-- ---------------------------------------------------------------------------
-- simp.fold-constants
-- ---------------------------------------------------------------------------

/-- Fold the numerals of a sum or product into one. The result is built with `addN`/`mulN`, so when
every term was a numeral the answer is that numeral, not a one-element sum or product that
`simp.identity` would then have to collapse in a step of its own. -/
def foldApply : Expr → Option RuleResult
  | .add es =>
    let nums := es.filter isNum
    if 2 ≤ nums.length then
      some ⟨addN (.num (sumQ nums) :: es.filter (fun e => !isNum e)),
        s!"Arithmetic on constants: {" + ".intercalate (nums.map Expr.toText)} = {(sumQ nums).toText}.", none, none⟩
    else none
  | .mul es =>
    let nums := es.filter isNum
    if 2 ≤ nums.length then
      some ⟨mulN (.num (prodQ nums) :: es.filter (fun e => !isNum e)),
        s!"Arithmetic on constants: {" × ".intercalate (nums.map Expr.toText)} = {(prodQ nums).toText}.", none, none⟩
    else none
  | _ => none

theorem M_of_isNum {e : Expr} (h : isNum e = true) : M e = 2 := by
  cases e with
  | num q => rfl
  | _ => simp [isNum] at h

theorem ML_nums (es : List Expr) : ML (es.filter isNum) = 2 * (es.filter isNum).length := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h : isNum e = true
    · simp only [h, ↓reduceIte, measureList, List.length_cons, M_of_isNum h]; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem fold_decreasing (es : List Expr) (h : 2 ≤ (es.filter isNum).length) (q : Q) :
    4 + ML (.num q :: es.filter (fun e => !isNum e)) < 4 + ML es := by
  have := ML_filter_split isNum es
  have := ML_nums es
  simp only [ML_cons, M_num] at *; omega

def foldConstants : Rule simpW where
  name := "simp.fold-constants"
  apply := foldApply
  decreasing e r h := by
    cases e <;> simp only [foldApply, reduceCtorEq] at h
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [M_add]; exact Nat.lt_of_le_of_lt (M_addN_le _) (fold_decreasing _ ‹_› _)
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [M_mul]; exact Nat.lt_of_le_of_lt (M_mulN_le _) (fold_decreasing _ ‹_› _)

-- ---------------------------------------------------------------------------
-- simp.function
-- ---------------------------------------------------------------------------

/-- The first element satisfying `p`, and the list without it. -/
def splitFirst (p : Expr → Bool) : List Expr → Option (Expr × List Expr)
  | [] => none
  | x :: xs => if p x then some (x, xs) else (splitFirst p xs).map fun r => (r.1, x :: r.2)

theorem splitFirst_perm (p : Expr → Bool) : ∀ (l : List Expr) {c l'}, splitFirst p l = some (c, l') →
    p c = true ∧ l.Perm (c :: l')
  | [], _, _, h => by simp [splitFirst] at h
  | x :: xs, c, l', h => by
    simp only [splitFirst] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨‹_›, List.Perm.refl _⟩
    · cases hs : splitFirst p xs with
      | none => simp [hs] at h
      | some r =>
        obtain ⟨c', l''⟩ := r
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hp, hperm⟩ := splitFirst_perm p xs hs
        exact ⟨hp, (hperm.cons x).trans (List.Perm.swap c' x l'')⟩

/-- `cos u ^ (-1)`, structurally. -/
def isCosInv (u : Expr) : Expr → Bool
  | .pow (.fn "cos" [v]) x => equal u v && equal x Expr.minusOne
  | _ => false

theorem isCosInv_eq {u c : Expr} (h : isCosInv u c = true) : c = .pow (.fn "cos" [u]) Expr.minusOne := by
  unfold isCosInv at h
  split at h
  · rename_i v x
    simp only [Bool.and_eq_true] at h
    rw [Expr.beq_eq u v h.1, Expr.beq_eq x Expr.minusOne h.2]
  · simp at h

def sinArg : Expr → Option Expr | .fn "sin" [u] => some u | _ => none

theorem sinArg_eq {f u : Expr} (h : sinArg f = some u) : f = .fn "sin" [u] := by
  unfold sinArg at h; split at h <;> simp_all

/-- `sin u` and `cos u ^ (-1)` among the factors of a product, and the other factors. `acc` holds
the factors already passed over, so the cosine may sit on either side of the sine. -/
def findTanGo (acc : List Expr) : List Expr → Option (Expr × List Expr)
  | [] => none
  | f :: rest =>
    match sinArg f with
    | some u =>
      match splitFirst (isCosInv u) (acc ++ rest) with
      | some (_, others) => some (u, others)
      | none => findTanGo (acc ++ [f]) rest
    | none => findTanGo (acc ++ [f]) rest

def findTan (es : List Expr) : Option (Expr × List Expr) := findTanGo [] es

theorem findTanGo_perm : ∀ (l acc : List Expr) {u others}, findTanGo acc l = some (u, others) →
    ∃ c, isCosInv u c = true ∧ (acc ++ l).Perm (.fn "sin" [u] :: c :: others)
  | [], _, _, _, h => by simp [findTanGo] at h
  | f :: rest, acc, u, others, h => by
    simp only [findTanGo] at h
    split at h
    · rename_i u' hu'
      split at h
      · rename_i c os hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hperm⟩ := splitFirst_perm _ _ hs
        rw [sinArg_eq hu']
        exact ⟨c, hc, List.perm_middle.trans (hperm.cons _)⟩
      · obtain ⟨c, hc, hperm⟩ := findTanGo_perm rest (acc ++ [f]) h
        exact ⟨c, hc, by simpa [List.append_assoc] using hperm⟩
    · obtain ⟨c, hc, hperm⟩ := findTanGo_perm rest (acc ++ [f]) h
      exact ⟨c, hc, by simpa [List.append_assoc] using hperm⟩

theorem findTan_perm (es : List Expr) {u others} (h : findTan es = some (u, others)) :
    ∃ c, isCosInv u c = true ∧ es.Perm (.fn "sin" [u] :: c :: others) := by
  simpa using findTanGo_perm es [] h

def functionApply : Expr → Option RuleResult
  | .mul es =>
    match findTan es with
    | some (u, others) => some ⟨mulN (.fn "tan" [u] :: others), "$\\sin u / \\cos u = \\tan u$.", none, none⟩
    | none => none
  | .fn "sqrt" [a] => some ⟨.pow a (.num (Q.ofRat (mkRat 1 2))), "$\\sqrt{a} = a^{1/2}$; we work with a single power form internally.", none, none⟩
  | .fn "ln" [a] =>
    if isOne a then some ⟨Expr.zero, "$\\ln 1 = 0$.", none, none⟩ else
    match a with
    | .fn "exp" [x] => some ⟨x, "$\\ln(e^x) = x$: ln and exp are inverses.", none, none⟩
    | .pow b p => some ⟨.mul [p, .fn "ln" [b]], "$\\ln(b^p) = p \\ln b$.", none, none⟩
    | _ => none
  | .fn "exp" [a] =>
    if isZero a then some ⟨Expr.one, "$e^0 = 1$.", none, none⟩ else
    match a with
    | .fn "ln" [x] => some ⟨x, "$e^{\\ln x} = x$: exp and ln are inverses.", none, none⟩
    | _ => none
  | .fn "sin" [a] => if isZero a then some ⟨Expr.zero, "$\\sin 0 = 0$.", none, none⟩ else none
  | .fn "cos" [a] => if isZero a then some ⟨Expr.one, "$\\cos 0 = 1$.", none, none⟩ else none
  | .fn "abs" [.num q] => some ⟨.num q.abs, "Absolute value of a constant.", none, none⟩
  | .fn "sign" [.num q] =>
    some ⟨.num (if q.isNeg then Q.minusOne else if q.isZero then Q.zero else Q.one), "The sign of a constant: $-1$, $0$ or $1$.", none, none⟩
  | _ => none

/-- Closes a leaf of a rule proof: either the arm returned `none`, or substitute the result and
count nodes. -/
macro "rule_leaf" h:ident : tactic =>
  `(tactic| first
    | (simp only [reduceCtorEq] at $h:ident; done)
    | (simp only [Option.some.injEq] at $h:ident; subst $h:ident
       (try subst_vars)
       simp only [M_num, M_var, M_add, M_mul, M_pow, M_fn, M_matrix, ML_cons, ML_nil, M_zero, M_one]
       omega))

def functionRules : Rule simpW where
  name := "simp.function"
  apply := functionApply
  decreasing e r h := by
    cases e <;> simp only [functionApply, reduceCtorEq] at h
    · -- sin u / cos u = tan u
      rename_i es
      split at h
      · rename_i u others hft
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨c, hc, hperm⟩ := findTan_perm es hft
        rw [isCosInv_eq hc] at hperm
        have hml := measureList_perm simpW hperm
        cases others with
        | nil =>
          simp only [mulN, M_mul, hml, ML_cons, ML_nil, M_fn, M_pow, M_num, Expr.minusOne]; omega
        | cons o os =>
          simp only [mulN, M_mul, hml, ML_cons, ML_nil, M_fn, M_pow, M_num, Expr.minusOne]; omega
      · simp at h
    · rename_i f args
      repeat' split at h
      all_goals (try injections)
      all_goals (try subst_vars)
      all_goals (simp only [M_num, M_var, M_add, M_mul, M_pow, M_fn, M_matrix, ML_cons, ML_nil, M_zero, M_one]; omega)

-- ---------------------------------------------------------------------------
-- simp.power
-- ---------------------------------------------------------------------------

/-- `p ^ q` for numerals: integer exponents evaluate; `p^(1/n)` evaluates when `p` is a perfect `n`-th power. -/
def powNumeric (p q : Q) : Option RuleResult :=
  if q.isInt then some ⟨.num (p.zpow q.val.num), s!"Evaluate the numeric power: {p.toText}^{q.toText} = {(p.zpow q.val.num).toText}.", none, none⟩
  else if q.val.num == 1 then
    match exactRoot p.val q.val.den with
    | some r => some ⟨.num (Q.ofRat r p.approx), s!"{p.toText} is a perfect {q.val.den}th power: ${p.toText}^\{1/{q.val.den}} = {r}$.", none, none⟩
    | none => none
  else none

def isPosNum : Expr → Bool | .num q => !q.isNeg && !q.isZero | _ => false

/-- The structural power rules: numeric evaluation and `(b^m)^n = b^(mn)` — for integer `m` and `n`
(any base), or for an integer `n` and a positive numeral base (so `sqrt(2)^2 = 2`; a symbolic base
would need `b ≥ 0`, which `sqrt(x)^2` cannot promise over ℝ). -/
def powerNum : Expr → Expr → Option RuleResult
  | .num p, .num q => powNumeric p q
  | .pow b' (.num m), .num n =>
    if n.isInt && m.isInt then some ⟨.pow b' (.num (m * n)), "$(b^m)^n = b^{mn}$ for integer $n$.", none, none⟩
    else if n.isInt && isPosNum b' then
      some ⟨.pow b' (.num (m * n)), "$(b^m)^n = b^{mn}$ for an integer $n$ and a positive base $b$ (so $\\sqrt{b}^2 = b$).", none, none⟩
    else none
  | _, _ => none

def powerAt (b x : Expr) : Option RuleResult :=
  if isZero x then some ⟨Expr.one, "$b^0 = 1$ (for the domain we work in, $b \\neq 0$).", none, none⟩
  else if isOne x then some ⟨b, "$b^1 = b$.", none, none⟩
  else if isOne b then some ⟨Expr.one, "$1^n = 1$.", none, none⟩
  else if isZero b && isPosNum x then some ⟨Expr.zero, "$0^n = 0$ for $n > 0$.", none, none⟩
  else powerNum b x

def powerApply : Expr → Option RuleResult
  | .pow b x => powerAt b x
  | _ => none

def powerRules : Rule simpW where
  name := "simp.power"
  apply := powerApply
  decreasing e r h := by
    cases e <;> simp only [powerApply, reduceCtorEq] at h
    rename_i b x
    simp only [powerAt] at h
    repeat' split at h
    all_goals try (simp only [powerNum, powNumeric] at h; repeat' split at h)
    all_goals rule_leaf h

-- ---------------------------------------------------------------------------
-- simp.collect-powers
-- ---------------------------------------------------------------------------

/-- Merge `t^a · t^b` into `t^(a+b)` for the first pair of factors with equal, big bases. -/
def mergePowers : List Expr → Option (List Expr × Expr)
  | [] => none
  | e :: rest =>
    let (b, x) := baseExp e
    if bigBase b then
      match rest.find? (fun f => equal (baseExp f).1 b) with
      | some f => some ((.pow b (addExp x (baseExp f).2)) :: removeFirst (fun f => equal (baseExp f).1 b) rest, b)
      | none => (mergePowers rest).map fun (l, t) => (e :: l, t)
    else (mergePowers rest).map fun (l, t) => (e :: l, t)

def collectPowersApply : Expr → Option RuleResult
  | .mul es =>
    match mergePowers es with
    | some (es', base) => some ⟨.mul es', s!"Same base ${base.toText}$: multiplying powers adds exponents, $b^m \\cdot b^n = b^\{m+n}$.", none, none⟩
    | none => none
  | _ => none

theorem baseExp_cases (e b x : Expr) (h : baseExp e = (b, x)) : e = .pow b x ∨ (e = b ∧ x = Expr.one) := by
  cases e <;> simp [baseExp] at h <;> simp [h]

theorem M_addExp_le (x y : Expr) : M (addExp x y) ≤ 4 + M x + M y := by
  cases x <;> cases y <;> simp [addExp, M_num, M_add, ML_cons, ML_nil] <;> omega

theorem M_addExp_num (p q : Q) : M (addExp (.num p) (.num q)) = 2 := rfl

/-- The merged power is lighter than the two factors it replaces. -/
theorem M_merged_lt (e f b x xf : Expr) (he : baseExp e = (b, x)) (hf : baseExp f = (b, xf)) (hb : bigBase b = true) :
    M (.pow b (addExp x xf)) < M e + M f := by
  have hb8 := bigBase_measure hb
  rcases baseExp_cases e b x he with he' | ⟨he', hx'⟩ <;> rcases baseExp_cases f b xf hf with hf' | ⟨hf', hxf'⟩
  · rw [he', hf']; have := M_addExp_le x xf; rw [M_pow, M_pow, M_pow]; omega
  · rw [he', hf', hxf']; have := M_addExp_le x Expr.one; rw [M_pow, M_pow]; simp only [M_one] at *; omega
  · rw [he', hx', hf']; have := M_addExp_le Expr.one xf; rw [M_pow, M_pow]; simp only [M_one] at *; omega
  · rw [he', hx', hf', hxf', M_pow, Expr.one, M_addExp_num]; omega

theorem mergePowers_lt : ∀ (es l : List Expr) (t : Expr), mergePowers es = some (l, t) → ML l < ML es
  | [], _, _, h => by simp [mergePowers] at h
  | e :: rest, l, t, h => by
    simp only [mergePowers] at h
    obtain ⟨b, x, hbx⟩ : ∃ b x, baseExp e = (b, x) := ⟨_, _, rfl⟩
    rw [hbx] at h
    simp only at h
    split at h
    · rename_i hbig
      split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : equal (baseExp f).1 b = true := by simpa using List.find?_some hf
        have hfb : (baseExp f).1 = b := equal_eq hp
        have hlt := M_merged_lt e f b x (baseExp f).2 hbx (by rw [← hfb]) hbig
        have := ML_removeFirst hf
        rw [ML_cons, ML_cons]; omega
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        have := mergePowers_lt rest l' t' hm
        rw [ML_cons, ML_cons]; omega
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have := mergePowers_lt rest l' t' hm
      rw [ML_cons, ML_cons]; omega

def collectPowers : Rule simpW where
  name := "simp.collect-powers"
  apply := collectPowersApply
  decreasing e r h := by
    cases e <;> simp only [collectPowersApply, reduceCtorEq] at h
    rename_i es
    split at h
    · rename_i l t hm
      simp only [Option.some.injEq] at h; subst h
      simp only [M_mul]; have := mergePowers_lt es l t hm; omega
    · simp at h

-- ---------------------------------------------------------------------------
-- simp.collect-like-terms
-- ---------------------------------------------------------------------------

/-- Merge `a·t + b·t` into `(a+b)·t` for the first pair of terms with equal, big rests. -/
def mergeTerms : List Expr → Option (List Expr × Expr)
  | [] => none
  | e :: rest =>
    let (c, t) := coeffRest e
    if bigBase t then
      match rest.find? (fun f => equal (coeffRest f).2 t) with
      | some f => some ((.mul [.num (c + (coeffRest f).1), t]) :: removeFirst (fun f => equal (coeffRest f).2 t) rest, t)
      | none => (mergeTerms rest).map fun (l, u) => (e :: l, u)
    else (mergeTerms rest).map fun (l, u) => (e :: l, u)

def collectTermsApply : Expr → Option RuleResult
  | .add es =>
    match mergeTerms es with
    | some (es', t) => some ⟨.add es', s!"Like terms share the same variable part, here ${t.toText}$; add their coefficients (distributive law $ax + bx = (a+b)x$).", none, none⟩
    | none => none
  | _ => none

theorem coeffRest_cases (e : Expr) (c : Q) (t : Expr) (h : coeffRest e = (c, t)) :
    (e = .num c ∧ t = Expr.one) ∨ (∃ r, e = .mul (.num c :: r) ∧ t = mulN r) ∨ (e = t ∧ c = Q.one) := by
  cases e with
  | num q => simp [coeffRest] at h; simp [h]
  | mul es =>
    match es with
    | .num q :: r => simp [coeffRest] at h; exact Or.inr (Or.inl ⟨r, by simp [h]⟩)
    | [] => simp [coeffRest] at h; simp [h]
    | .var _ :: r | .add _ :: r | .mul _ :: r | .pow _ _ :: r | .fn _ _ :: r | .matrix _ :: r =>
      simp [coeffRest] at h; simp [h]
  | _ => simp [coeffRest] at h; simp [h]

/-- A term with rest `t` weighs at least `t` (a coefficient only adds). -/
theorem M_coeffRest_ge (e : Expr) (c : Q) (t : Expr) (h : coeffRest e = (c, t)) (hb : bigBase t = true) :
    M t ≤ M e ∧ (e ≠ t → 2 + M t ≤ M e) := by
  rcases coeffRest_cases e c t h with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨rfl, _⟩
  · simp [bigBase, Expr.one] at hb
  · have := M_mulN_le r
    refine ⟨?_, fun _ => ?_⟩ <;> rw [M_mul, ML_cons, M_num] <;> omega
  · exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩

theorem M_mergedTerm_lt (e f : Expr) (c cf : Q) (t : Expr) (he : coeffRest e = (c, t)) (hf : coeffRest f = (cf, t))
    (hb : bigBase t = true) : M (.mul [.num (c + cf), t]) < M e + M f := by
  have hb8 := bigBase_measure hb
  have he' := M_coeffRest_ge e c t he hb
  have hf' := M_coeffRest_ge f cf t hf hb
  rw [M_mul, ML_cons, ML_cons, ML_nil, M_num]
  by_cases h1 : e = t <;> by_cases h2 : f = t
  · subst h1; subst h2; omega
  · subst h1; have := hf'.2 h2; omega
  · subst h2; have := he'.2 h1; omega
  · have := he'.2 h1; have := hf'.2 h2; omega

theorem mergeTerms_lt : ∀ (es l : List Expr) (t : Expr), mergeTerms es = some (l, t) → ML l < ML es
  | [], _, _, h => by simp [mergeTerms] at h
  | e :: rest, l, t, h => by
    simp only [mergeTerms] at h
    obtain ⟨c, u, hcu⟩ : ∃ c u, coeffRest e = (c, u) := ⟨_, _, rfl⟩
    rw [hcu] at h
    simp only at h
    split at h
    · rename_i hbig
      split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hp : equal (coeffRest f).2 u = true := by simpa using List.find?_some hf
        have hfu : (coeffRest f).2 = u := equal_eq hp
        have hlt := M_mergedTerm_lt e f c (coeffRest f).1 u hcu (by rw [← hfu]) hbig
        have := ML_removeFirst hf
        rw [ML_cons, ML_cons]; omega
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        have := mergeTerms_lt rest l' t' hm
        rw [ML_cons, ML_cons]; omega
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hm, hl⟩ := h
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have := mergeTerms_lt rest l' t' hm
      rw [ML_cons, ML_cons]; omega

def collectTerms : Rule simpW where
  name := "simp.collect-like-terms"
  apply := collectTermsApply
  decreasing e r h := by
    cases e <;> simp only [collectTermsApply, reduceCtorEq] at h
    rename_i es
    split at h
    · rename_i l t hm
      simp only [Option.some.injEq] at h; subst h
      simp only [M_add]; have := mergeTerms_lt es l t hm; omega
    · simp at h

-- ---------------------------------------------------------------------------
-- The rule set
-- ---------------------------------------------------------------------------

def simpRules : List (Rule simpW) := [flatten, identity, foldConstants, functionRules, powerRules, collectPowers, collectTerms]

def simplify (e : Expr) : TraceM Expr := normalize simpRules e
def simplify0 (e : Expr) : Expr := (simplify e).run' #[]

end MathEngine
