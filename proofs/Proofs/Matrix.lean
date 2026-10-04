import Proofs.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Matrices get a value

`evalR` and `evalD` send a matrix literal to the junk value 0: a real number cannot be a matrix. So the
matrix rules had theorems with no content. Here a fourth layer, `evalV`, gives every term a *value*
that is either a real number or a matrix of real numbers with its shape, and is undefined (`none`)
where the term has no meaning: adding matrices of different shapes, multiplying ones whose inner
dimensions disagree, a determinant of a non-square matrix.

- `evalV_of_noLit`: on a term with no matrix literal in it, `evalV` is `evalD` — the layer extends
  the one below, as `evalD` extends `evalR`.
- `laAdd_sound`, `laScalarMul_sound`, `laMul_sound`, `laTranspose_sound`, `laDet_sound`,
  `laPow_sound`, `diffMatrix_sound`: wherever the input has a value, the rule's output has the same
  one. The determinant is Mathlib's `Matrix.det` (the engine's Laplace expansion is proved equal to it,
  `detExpr_value`), the power is the power in the monoid of square matrices (`matPow_value`), a product
  is associative and its real factors commute past its matrices (`mulVals_nf`, `mulV_assoc`), and the
  derivative of a matrix is taken entry by entry.

A rule's theorem assumes what the notebook pipeline guarantees when the rule fires: the node's
children are normal, and a normal term holds a matrix literal only at its root (`LitAtRoot`, which
`litAtRoot_of_normal` derives from the engine's `normal_facts`). Without that, `transpose([1, 2]) · [3]`
would be read as a scalar times a matrix.

Matrix values are kept as functions `ℕ → ℕ → ℝ` with their shape, read as 0 outside it (`mk`), so
that values of the same shape are equal exactly when their entries are and no index needs a cast.
`toM` and `ofM` move to and from Mathlib's `Matrix (Fin r) (Fin c) ℝ`.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-! ## Values -/

/-- A real number, or an `r × c` matrix of real numbers. -/
inductive Val where
  | sc (x : ℝ)
  | mat (r c : ℕ) (f : ℕ → ℕ → ℝ)

/-- The matrix with entries `f` inside its shape and 0 outside. -/
def mk (r c : ℕ) (f : ℕ → ℕ → ℝ) : Val := .mat r c fun i j => if i < r ∧ j < c then f i j else 0

theorem mk_congr {r c : ℕ} {f g : ℕ → ℕ → ℝ} (h : ∀ i j, i < r → j < c → f i j = g i j) :
    mk r c f = mk r c g := by
  unfold mk; congr 1; funext i j
  split_ifs with hij
  · exact h i j hij.1 hij.2
  · rfl

/-- Two matrix values are equal when their shapes and their entries inside the shape are. -/
theorem mk_congr' {r c r' c' : ℕ} {f g : ℕ → ℕ → ℝ} (hr : r = r') (hc : c = c')
    (h : ∀ i j, i < r → j < c → f i j = g i j) : mk r c f = mk r' c' g := by
  subst hr hc; exact mk_congr h

/-- As a Mathlib matrix. -/
def toM (r c : ℕ) (f : ℕ → ℕ → ℝ) : Matrix (Fin r) (Fin c) ℝ := Matrix.of fun i j => f i j

/-- A Mathlib matrix, read by natural-number indices. -/
def ofM {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℝ) : ℕ → ℕ → ℝ :=
  fun i j => if h : i < r ∧ j < c then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

@[simp] theorem toM_apply (r c : ℕ) (f : ℕ → ℕ → ℝ) (i : Fin r) (j : Fin c) : toM r c f i j = f i j := rfl

theorem ofM_apply {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℝ) {i j : ℕ} (hi : i < r) (hj : j < c) :
    ofM M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [ofM, hi, hj]

theorem toM_mk_eq (r c : ℕ) (f : ℕ → ℕ → ℝ) :
    toM r c (fun i j => if i < r ∧ j < c then f i j else 0) = toM r c f := by
  ext i j; simp [toM]

def Val.scal : Val → ℝ
  | .sc y => y
  | .mat _ _ _ => 0

def Val.isSc : Val → Bool
  | .sc _ => true
  | .mat _ _ _ => false

/-- The real value a term has, or 0. -/
def scalOf : Option Val → ℝ
  | some (.sc y) => y
  | _ => 0

/-- Entry `(i, j)` of the matrix a term has, or 0. -/
def entOf : Option Val → ℕ → ℕ → ℝ
  | some (.mat _ _ f), i, j => f i j
  | _, _, _ => 0

def addV : Val → Val → Option Val
  | .sc a, .sc b => some (.sc (a + b))
  | .mat r c f, .mat r' c' g => if r = r' ∧ c = c' then some (mk r c fun i j => f i j + g i j) else none
  | _, _ => none

def mulV : Val → Val → Option Val
  | .sc a, .sc b => some (.sc (a * b))
  | .sc a, .mat r c g => some (mk r c fun i j => a * g i j)
  | .mat r c f, .sc b => some (mk r c fun i j => f i j * b)
  | .mat r c f, .mat r' c' g =>
    if c = r' then some (mk r c' fun i j => ∑ k ∈ Finset.range c, f i k * g k j) else none

def addVals : List Val → Option Val
  | [] => some (.sc 0)
  | [v] => some v
  | v :: w :: vs => (addVals (w :: vs)).bind (addV v)

/-- A product, right to left as `prodD` reads it; a lone matrix factor comes out as `M · 1`. -/
def mulVals : List Val → Option Val
  | [] => some (.sc 1)
  | v :: vs => (mulVals vs).bind (mulV v)

/-- `M^k` for a square matrix and a positive integer `k`; real powers of reals as `evalR` has them. -/
def powV : Val → Val → Option Val
  | .sc a, .sc b => some (.sc (a ^ b))
  | .mat r c f, .sc b =>
    if r = c ∧ 1 ≤ b ∧ ((⌊b⌋₊ : ℕ) : ℝ) = b then some (mk r r (ofM (toM r r f ^ ⌊b⌋₊))) else none
  | _, _ => none

/-- A one-argument function: the real ones on reals, `transpose` and `det` on matrices. -/
def fn1 (f : String) : Val → Option Val
  | .sc y => some (.sc (applyFn f y))
  | .mat r c g =>
    if f = "transpose" then some (mk c r fun i j => g j i)
    else if f = "det" ∧ r = c then some (.sc (toM r r g).det)
    else none

/-- A matrix literal: at least one entry, rows of the same length, every entry a real number. The
shape is the number of rows and the length of the first, as the engine's `dims` reads it. (The
parser never makes a literal without entries, and no rule makes one from a literal with them.) -/
def litV (rows : List (List Val)) : Option Val :=
  let c := (rows.head?.map List.length).getD 0
  if 0 < c && rows.all (fun row => row.length == c && row.all Val.isSc) then
    some (mk rows.length c fun i j => ((rows.getD i []).getD j (.sc 0)).scal)
  else none

mutual
  /-- **The value of a term**: a real number or a matrix, or `none` where it has no meaning. -/
  def evalV : EnvR → Expr → Option Val
    | _, .num q => some (.sc (q.val : ℝ))
    | ρ, .var y => some (.sc (ρ y))
    | ρ, .add es => (evalVs ρ es).bind addVals
    | ρ, .mul es => (evalVs ρ es).bind mulVals
    | ρ, .pow b e => (evalV ρ b).bind fun vb => (evalV ρ e).bind (powV vb)
    | ρ, .fn f es => fnV ρ f es
    | ρ, .matrix rows => (evalRows ρ rows).bind litV
  def fnV : EnvR → String → List Expr → Option Val
    | _, f, [] => some (.sc (constR f))
    | ρ, f, [a] => (evalV ρ a).bind (fn1 f)
    | ρ, f, [g, v] =>
      if f = "diff" then
        match v with
        | .var x =>
          match evalV ρ g with
          | some (.sc _) => some (.sc (deriv (fun t => scalOf (evalV (upd ρ x t) g)) (ρ x)))
          | some (.mat r c _) => some (mk r c fun i j => deriv (fun t => entOf (evalV (upd ρ x t) g) i j) (ρ x))
          | none => none
        | _ => some (.sc 0)
      else (evalV ρ g).bind fun a => (evalV ρ v).bind fun b => if a.isSc && b.isSc then some (.sc 0) else none
    | ρ, _, a :: b :: c :: rest =>
      (evalVs ρ (a :: b :: c :: rest)).bind fun vs => if vs.all Val.isSc then some (.sc 0) else none
  def evalVs : EnvR → List Expr → Option (List Val)
    | _, [] => some []
    | ρ, e :: es => (evalV ρ e).bind fun v => (evalVs ρ es).map (v :: ·)
  def evalRows : EnvR → List (List Expr) → Option (List (List Val))
    | _, [] => some []
    | ρ, r :: rs => (evalVs ρ r).bind fun v => (evalRows ρ rs).map (v :: ·)
end


/-! ## Equations -/

section
variable (ρ : EnvR)

@[simp] theorem evalV_num (q : Q) : evalV ρ (.num q) = some (.sc (q.val : ℝ)) := by rw [evalV]
@[simp] theorem evalV_var (y : String) : evalV ρ (.var y) = some (.sc (ρ y)) := by rw [evalV]
@[simp] theorem evalV_add (es : List Expr) : evalV ρ (.add es) = (evalVs ρ es).bind addVals := by rw [evalV]
@[simp] theorem evalV_mul (es : List Expr) : evalV ρ (.mul es) = (evalVs ρ es).bind mulVals := by rw [evalV]
@[simp] theorem evalV_pow (b e : Expr) :
    evalV ρ (.pow b e) = (evalV ρ b).bind fun vb => (evalV ρ e).bind (powV vb) := by rw [evalV]
@[simp] theorem evalV_fn (f : String) (es : List Expr) : evalV ρ (.fn f es) = fnV ρ f es := by rw [evalV]
@[simp] theorem evalV_matrix (rows : List (List Expr)) :
    evalV ρ (.matrix rows) = (evalRows ρ rows).bind litV := by rw [evalV]
@[simp] theorem evalVs_nil : evalVs ρ [] = some [] := by rw [evalVs]
@[simp] theorem evalVs_cons (e : Expr) (es : List Expr) :
    evalVs ρ (e :: es) = (evalV ρ e).bind fun v => (evalVs ρ es).map (v :: ·) := by rw [evalVs]
@[simp] theorem evalRows_nil : evalRows ρ [] = some [] := by rw [evalRows]
@[simp] theorem evalRows_cons (r : List Expr) (rs : List (List Expr)) :
    evalRows ρ (r :: rs) = (evalVs ρ r).bind fun v => (evalRows ρ rs).map (v :: ·) := by rw [evalRows]
@[simp] theorem fnV_nil (f : String) : fnV ρ f [] = some (.sc (constR f)) := by rw [fnV]
@[simp] theorem fnV_one (f : String) (a : Expr) : fnV ρ f [a] = (evalV ρ a).bind (fn1 f) := by rw [fnV]
theorem fnV_diff (g : Expr) (x : String) :
    fnV ρ "diff" [g, .var x] =
      match evalV ρ g with
      | some (.sc _) => some (.sc (deriv (fun t => scalOf (evalV (upd ρ x t) g)) (ρ x)))
      | some (.mat r c _) => some (mk r c fun i j => deriv (fun t => entOf (evalV (upd ρ x t) g) i j) (ρ x))
      | none => none := by
  rw [fnV]; simp
theorem fnV_two_ne {f : String} (hf : f ≠ "diff") (g v : Expr) :
    fnV ρ f [g, v] = (evalV ρ g).bind fun a => (evalV ρ v).bind fun b =>
      if a.isSc && b.isSc then some (.sc 0) else none := by
  cases v <;> rw [fnV] <;> simp [hf]
end

/-- `evalVs` evaluates every term of a list, or fails. -/
theorem evalVs_eq_some (ρ : EnvR) : ∀ (es : List Expr) (vs : List Val),
    evalVs ρ es = some vs ↔ List.Forall₂ (fun e v => evalV ρ e = some v) es vs
  | [], [] => by simp
  | [], _ :: _ => by simp
  | e :: es, [] => by
    simp only [evalVs_cons, List.forall₂_nil_right_iff, reduceCtorEq, iff_false]
    cases evalV ρ e <;> cases evalVs ρ es <;> simp
  | e :: es, v :: vs => by
    rw [List.forall₂_cons, ← evalVs_eq_some ρ es vs, evalVs_cons]
    cases evalV ρ e <;> cases evalVs ρ es <;> simp [eq_comm]

theorem evalRows_eq_some (ρ : EnvR) : ∀ (rows : List (List Expr)) (vals : List (List Val)),
    evalRows ρ rows = some vals ↔ List.Forall₂ (fun r v => evalVs ρ r = some v) rows vals
  | [], [] => by simp
  | [], _ :: _ => by simp
  | r :: rs, [] => by
    simp only [evalRows_cons, List.forall₂_nil_right_iff, reduceCtorEq, iff_false]
    cases evalVs ρ r <;> cases evalRows ρ rs <;> simp
  | r :: rs, v :: vs => by
    rw [List.forall₂_cons, ← evalRows_eq_some ρ rs vs, evalRows_cons]
    cases evalVs ρ r <;> cases evalRows ρ rs <;> simp [eq_comm]

/-- Every term of the list has a value, so the list has one. -/
theorem evalVs_of_forall (ρ : EnvR) : ∀ (es : List Expr), (∀ e ∈ es, ∃ v, evalV ρ e = some v) →
    ∃ vs, evalVs ρ es = some vs
  | [], _ => ⟨[], by simp⟩
  | e :: es, h => by
    obtain ⟨v, hv⟩ := h e (by simp)
    obtain ⟨vs, hvs⟩ := evalVs_of_forall ρ es (fun x hx => h x (by simp [hx]))
    exact ⟨v :: vs, by simp [hv, hvs]⟩

theorem getD_of_lt {α : Type*} (l : List α) (d : α) {n : ℕ} (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i, i < l₁.length → R (l₁.getD i a) (l₂.getD i b)
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab _, 0, _ => by simpa using hab
  | _, _, .cons _ hl, i + 1, h => by simpa using forall₂_getD hl i (by simpa using h)

theorem evalVs_map {α : Type*} (ρ : EnvR) (f : α → Expr) (g : α → Val) :
    ∀ l : List α, (∀ x ∈ l, evalV ρ (f x) = some (g x)) → evalVs ρ (l.map f) = some (l.map g)
  | [], _ => by simp
  | x :: l, h => by
    simp [h x (by simp), evalVs_map ρ f g l (fun y hy => h y (by simp [hy]))]

/-! ## The layer below: without a matrix literal, `evalV` is `evalD` -/

theorem addVals_sc : ∀ xs : List ℝ, addVals (xs.map .sc) = some (.sc xs.sum)
  | [] => by simp [addVals]
  | [x] => by simp [addVals]
  | x :: y :: xs => by
    have ih := addVals_sc (y :: xs)
    simp only [List.map_cons] at ih ⊢
    rw [addVals, ih]; simp [addV]

theorem addVals_map_sc {α : Type*} (l : List α) (f : α → ℝ) :
    addVals (l.map fun x => .sc (f x)) = some (.sc (l.map f).sum) := by
  simpa [Function.comp_def] using addVals_sc (l.map f)

theorem mulVals_sc : ∀ xs : List ℝ, mulVals (xs.map .sc) = some (.sc xs.prod)
  | [] => by simp [mulVals]
  | x :: xs => by
    rw [List.map_cons, mulVals, mulVals_sc xs]; simp [mulV]

theorem sumD_eq_sum (ρ : EnvR) : ∀ es : List Expr, sumD ρ es = (es.map (evalD ρ)).sum
  | [] => rfl
  | e :: es => by simp [sumD_eq_sum ρ es]

theorem prodD_eq_prod (ρ : EnvR) : ∀ es : List Expr, prodD ρ es = (es.map (evalD ρ)).prod
  | [] => rfl
  | e :: es => by simp [prodD_eq_prod ρ es]

mutual
  /-- **`evalV` extends `evalD`**: a term with no matrix literal in it has the real value `evalD`
  gives it. -/
  theorem evalV_of_noLit : ∀ {e : Expr} (ρ : EnvR), hasLit e = false → evalV ρ e = some (.sc (evalD ρ e))
    | .num q, ρ, _ => by simp
    | .var y, ρ, _ => by simp
    | .add es, ρ, h => by
      simp only [hasLit] at h
      rw [evalV_add, evalVs_of_noLit ρ h, Option.bind_some, evalD_add, sumD_eq_sum]
      simpa [Function.comp_def] using addVals_sc (es.map (evalD ρ))
    | .mul es, ρ, h => by
      simp only [hasLit] at h
      rw [evalV_mul, evalVs_of_noLit ρ h, Option.bind_some, evalD_mul, prodD_eq_prod]
      simpa [Function.comp_def] using mulVals_sc (es.map (evalD ρ))
    | .pow b x, ρ, h => by
      simp only [hasLit, Bool.or_eq_false_iff] at h
      simp [evalV_of_noLit ρ h.1, evalV_of_noLit ρ h.2, powV]
    | .fn f es, ρ, h => by
      simp only [hasLit] at h
      match es, h with
      | [], _ => simp
      | [a], h =>
        have ha : hasLit a = false := by simpa [hasLitList] using h
        simp [evalV_of_noLit ρ ha, fn1]
      | [g, v], h =>
        have hg : hasLit g = false := by simp_all [hasLitList]
        have hv : hasLit v = false := by simp_all [hasLitList]
        by_cases hf : f = "diff"
        · subst hf
          cases v with
          | var x =>
            rw [evalV_fn, fnV_diff, evalV_of_noLit ρ hg]
            have hfun : (fun t => scalOf (evalV (upd ρ x t) g)) = fun t => evalD (upd ρ x t) g := by
              funext t; rw [evalV_of_noLit (upd ρ x t) hg]; rfl
            simp only [hfun, evalD_diff]; rfl
          | _ => simp [fnV, evalD, fnD_two]
        · rw [evalV_fn, fnV_two_ne ρ hf, evalV_of_noLit ρ hg, evalV_of_noLit ρ hv, evalD_fn,
            fnD_two_ne _ _ _ hf]
          simp [Val.isSc]
      | a :: b :: c :: rest, h =>
        rw [evalV_fn, fnV, evalVs_of_noLit ρ h]
        simp [Val.isSc]
    | .matrix _, _, h => by simp [hasLit] at h
  theorem evalVs_of_noLit : ∀ {es : List Expr} (ρ : EnvR), hasLitList es = false →
      evalVs ρ es = some (es.map fun e => .sc (evalD ρ e))
    | [], _, _ => by simp
    | e :: es, ρ, h => by
      simp only [hasLitList, Bool.or_eq_false_iff] at h
      simp [evalV_of_noLit ρ h.1, evalVs_of_noLit ρ h.2]
end

/-! ## Literals -/

/-- The real value entry `(i, j)` of a literal has. -/
abbrev entV (ρ : EnvR) (rows : List (List Expr)) (i j : ℕ) : ℝ := scalOf (evalV ρ (entry rows i j))

/-- **A matrix literal's value**: it has one exactly when it has an entry, its rows have one
length, and every entry is a real number; then it is the matrix of those numbers. -/
theorem evalV_matrix_eq_some {ρ : EnvR} {rows : List (List Expr)} {v : Val} :
    evalV ρ (.matrix rows) = some v ↔
      ∃ c, 0 < c ∧ rows ≠ [] ∧ (∀ row ∈ rows, row.length = c) ∧
        (∀ i j, i < rows.length → j < c → ∃ y, evalV ρ (entry rows i j) = some (.sc y)) ∧
        v = mk rows.length c (entV ρ rows) := by
  rw [evalV_matrix, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨vals, hr, hl⟩
    have hF := (evalRows_eq_some ρ rows vals).mp hr
    have hlen := hF.length_eq
    simp only [litV] at hl
    split at hl
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hcond
      obtain ⟨hc, hall⟩ := hcond
      simp only [Option.some.injEq] at hl
      have hrow : ∀ i, i < rows.length → evalVs ρ (rows.getD i []) = some (vals.getD i []) :=
        fun i hi => forall₂_getD hF i hi
      have hvrow : ∀ i, i < rows.length →
          (vals.getD i []).length = (vals.head?.map List.length).getD 0 ∧ ∀ w ∈ vals.getD i [], w.isSc = true := by
        intro i hi
        have := hall (vals.getD i []) (by rw [getD_of_lt vals [] (hlen ▸ hi)]; exact List.getElem_mem _)
        exact ⟨this.1, fun w hw => this.2 w hw⟩
      have hrlen : ∀ i, i < rows.length → (rows.getD i []).length = (vals.head?.map List.length).getD 0 := by
        intro i hi
        rw [← (hvrow i hi).1]
        exact ((evalVs_eq_some ρ _ _).mp (hrow i hi)).length_eq
      have hentry : ∀ i j, i < rows.length → j < (vals.head?.map List.length).getD 0 →
          evalV ρ (entry rows i j) = some ((vals.getD i []).getD j (.sc 0)) := fun i j hi hj =>
        forall₂_getD ((evalVs_eq_some ρ _ _).mp (hrow i hi)) j (by rw [hrlen i hi]; exact hj)
      have hsc : ∀ i j, i < rows.length → j < (vals.head?.map List.length).getD 0 →
          ((vals.getD i []).getD j (.sc 0)).isSc = true := fun i j hi hj =>
        (hvrow i hi).2 _ (by
          rw [getD_of_lt (vals.getD i []) (Val.sc 0) (by rw [(hvrow i hi).1]; exact hj)]; exact List.getElem_mem _)
      refine ⟨_, hc, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        cases vals with
        | nil => simp at hc
        | cons _ _ => simp at hlen
      · intro row hrow'
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow'
        have := hrlen i hi
        rwa [getD_of_lt _ _ hi] at this
      · intro i j hi hj
        rw [hentry i j hi hj]
        have := hsc i j hi hj
        cases hw : (vals.getD i []).getD j (.sc 0) with
        | sc y => exact ⟨y, rfl⟩
        | mat _ _ _ => rw [hw] at this; simp [Val.isSc] at this
      · rw [← hl, hlen]
        apply mk_congr
        intro i j hi hj
        have := hsc i j (hlen ▸ hi) hj
        rw [entV, hentry i j (hlen ▸ hi) hj]
        cases (vals.getD i []).getD j (.sc 0) <;> simp_all [Val.isSc, scalOf, Val.scal]
    · cases hl
  · rintro ⟨c, hc, hne, hrect, hent, rfl⟩
    -- every entry is a real number
    have hentries : ∀ row ∈ rows, ∀ e ∈ row, evalV ρ e = some (.sc (scalOf (evalV ρ e))) := by
      intro row hrow e he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hj' : j < c := by rw [← hrect _ hrow]; exact hj
      obtain ⟨y, hy⟩ := hent i j hi hj'
      have : entry rows i j = rows[i][j] := by rw [entry, getD_of_lt _ _ hi, getD_of_lt _ _ hj]
      rw [this] at hy
      rw [hy]; rfl
    obtain ⟨vals, hvals⟩ : ∃ vals, vals = rows.map fun row => row.map fun e => Val.sc (scalOf (evalV ρ e)) :=
      ⟨_, rfl⟩
    have hr : evalRows ρ rows = some vals := by
      rw [evalRows_eq_some, hvals, List.forall₂_map_right_iff, List.forall₂_same]
      intro row hrow
      have := evalVs_map ρ (fun e => e) (fun e => Val.sc (scalOf (evalV ρ e))) row
        (fun e he => hentries row hrow e he)
      simpa using this
    refine ⟨vals, hr, ?_⟩
    have hhead : (vals.head?.map List.length).getD 0 = c := by
      cases rows with
      | nil => exact absurd rfl hne
      | cons r rs => simp [hvals, hrect r (by simp)]
    have hvij : ∀ i j, i < rows.length → j < c → (vals.getD i []).getD j (.sc 0) = .sc (entV ρ rows i j) := by
      intro i j hi hj
      have hrow : rows[i].length = c := hrect _ (List.getElem_mem hi)
      have hvi : vals.getD i [] = rows[i].map fun e => Val.sc (scalOf (evalV ρ e)) := by
        rw [getD_of_lt vals [] (by simpa [hvals] using hi)]; simp [hvals]
      rw [hvi, getD_of_lt (rows[i].map fun e => Val.sc (scalOf (evalV ρ e))) (Val.sc 0)
          (by rw [List.length_map, hrow]; exact hj), List.getElem_map, entV, entry,
        getD_of_lt rows [] hi, getD_of_lt _ Expr.zero (by rw [hrow]; exact hj)]
    simp only [litV]
    rw [ite_eq_left]
    · rw [hhead, Option.some.injEq]
      have hvl : vals.length = rows.length := by simp [hvals]
      rw [hvl]
      apply mk_congr
      intro i j hi hj
      rw [hvij i j hi hj]; rfl
    · simp only [hhead, hc, decide_true, Bool.true_and, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
      intro row hrow
      simp only [hvals, List.mem_map] at hrow
      obtain ⟨r, hr', rfl⟩ := hrow
      simp [hrect r hr', Val.isSc]

/-- The shape `dims` reads off a literal that has a value. -/
theorem dims_of_rect {rows : List (List Expr)} {c : ℕ} (hne : rows ≠ []) (hr : ∀ row ∈ rows, row.length = c) :
    dims rows = (rows.length, c) := by
  cases rows with
  | nil => exact absurd rfl hne
  | cons r rs => simp [dims, hr r (by simp)]

/-- A literal laid out by `List.range`, as the matrix rules build their results. -/
theorem entry_grid (r c : ℕ) (E : ℕ → ℕ → Expr) {i j : ℕ} (hi : i < r) (hj : j < c) :
    entry ((List.range r).map fun i => (List.range c).map fun j => E i j) i j = E i j := by
  simp [entry, List.getD_eq_getElem?_getD, hi, hj]

theorem grid_rect (r c : ℕ) (E : ℕ → ℕ → Expr) :
    ∀ row ∈ ((List.range r).map fun i => (List.range c).map fun j => E i j), row.length = c := by
  simp

theorem grid_ne_nil {r c : ℕ} (E : ℕ → ℕ → Expr) (hr : 0 < r) :
    ((List.range r).map fun i => (List.range c).map fun j => E i j) ≠ [] := by
  simp; omega

/-- Building a literal: entries with real values, laid out as a grid. -/
theorem evalV_grid {ρ : EnvR} {r c : ℕ} {E : ℕ → ℕ → Expr} (F : ℕ → ℕ → ℝ) (hr : 0 < r) (hc : 0 < c)
    (hE : ∀ i j, i < r → j < c → evalV ρ (E i j) = some (.sc (F i j))) :
    evalV ρ (.matrix ((List.range r).map fun i => (List.range c).map fun j => E i j)) = some (mk r c F) := by
  have hlen : ((List.range r).map fun i => (List.range c).map fun j => E i j).length = r := by simp
  rw [evalV_matrix_eq_some]
  refine ⟨c, hc, grid_ne_nil E hr, grid_rect r c E, fun i j hi hj => ?_, ?_⟩
  · rw [hlen] at hi; rw [entry_grid r c E hi hj]; exact ⟨_, hE i j hi hj⟩
  · rw [hlen]; apply mk_congr; intro i j hi hj
    simp only [entV, entry_grid r c E hi hj, hE i j hi hj, scalOf]


theorem mk_inj {r c : ℕ} {f g : ℕ → ℕ → ℝ} (h : mk r c f = mk r c g) {i j : ℕ} (hi : i < r) (hj : j < c) :
    f i j = g i j := by
  unfold mk at h
  have := congrFun (congrFun (Val.mat.inj h).2.2 i) j
  simpa [hi, hj] using this

/-- An entry of a literal with a value is a real number: its `entV`. -/
theorem entry_value {ρ : EnvR} {rows : List (List Expr)} {v : Val} (h : evalV ρ (.matrix rows) = some v)
    {i j : ℕ} (hi : i < rows.length) (hj : j < (dims rows).2) :
    evalV ρ (entry rows i j) = some (.sc (entV ρ rows i j)) := by
  obtain ⟨c, hc, hne, hrect, hent, -⟩ := evalV_matrix_eq_some.mp h
  rw [dims_of_rect hne hrect] at hj
  obtain ⟨y, hy⟩ := hent i j hi hj
  simp [entV, hy, scalOf]

/-- A literal with a value is the matrix of its entries' values, in the shape `dims` reads. -/
theorem lit_value {ρ : EnvR} {rows : List (List Expr)} {v : Val} (h : evalV ρ (.matrix rows) = some v) :
    0 < rows.length ∧ 0 < (dims rows).2 ∧ v = mk (dims rows).1 (dims rows).2 (entV ρ rows) := by
  obtain ⟨c, hc, hne, hrect, -, rfl⟩ := evalV_matrix_eq_some.mp h
  rw [dims_of_rect hne hrect]
  exact ⟨List.length_pos_iff.mpr hne, hc, rfl⟩

/-! ## The rules -/

/-- A matrix rule that fired without refusing returned its body's result. -/
theorem lit_ok {e : Expr} {res : RuleResult} {body : Option RuleResult}
    (h : Option.map (checkedLit e) body = some res) (he : res.error = none) : ∃ r₀, body = some r₀ ∧ res = r₀ := by
  obtain ⟨r₀, hb, rfl⟩ := lit_apply h
  refine ⟨r₀, hb, ?_⟩
  unfold checkedLit at he ⊢
  split_ifs at he ⊢ <;> simp_all

/-- **`la.transpose`**: rows become columns. -/
theorem laTranspose_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laTranspose.apply e = some res)
    (he : res.error = none) {v : Val} (hv : evalV ρ e = some v) : evalV ρ res.result = some v := by
  unfold laTranspose at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i rows
    cases hb
    simp only [evalV_fn, fnV_one, Option.bind_eq_some_iff] at hv
    obtain ⟨m, hm, hfn⟩ := hv
    obtain ⟨hr, hc, rfl⟩ := lit_value hm
    simp only [mk, fn1, ite_true, Option.some.injEq] at hfn
    subst hfn
    have hg := evalV_grid (ρ := ρ) (r := (dims rows).2) (c := rows.length) (E := fun j i => entry rows i j)
      (fun j i => entV ρ rows i j) hc hr (fun j i hj hi => entry_value hm hi hj)
    simp only [dims] at hg hc ⊢
    rw [hg, mk]
    congr 2; funext j i
    by_cases hji : j < (Option.map List.length rows.head?).getD 0 ∧ i < rows.length
    · simp [hji.1, hji.2]
    · simp only [hji]; simp
  · cases hb

theorem sum_range_list (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Adding matrices of one shape. -/
theorem addVals_mk {r c : ℕ} : ∀ (Fs : List (ℕ → ℕ → ℝ)), Fs ≠ [] →
    addVals (Fs.map (mk r c)) = some (mk r c fun i j => (Fs.map (· i j)).sum)
  | [], h => absurd rfl h
  | [F], _ => by simp [addVals]
  | F :: G :: Fs, _ => by
    have ih := addVals_mk (r := r) (c := c) (G :: Fs) (by simp)
    simp only [List.map_cons] at ih ⊢
    rw [addVals, ih, Option.bind_some]
    simp only [mk, addV, and_self, ite_true, Option.some.injEq]
    congr 1; funext i j
    split_ifs <;> simp_all

theorem mapM_asMat : ∀ {es : List Expr} {ms : List (List (List Expr))}, es.mapM asMat = some ms → es = ms.map .matrix
  | [], ms, h => by simp at h; subst h; rfl
  | e :: es, ms, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨m, hm, ms', hms', rfl⟩ := h
    cases e <;> simp [asMat] at hm
    subst hm
    simp [mapM_asMat hms']

/-- The values of literals of one shape. -/
theorem forall₂_lits {ρ : EnvR} {r c : ℕ} : ∀ {ms : List (List (List Expr))} {vs : List Val},
    List.Forall₂ (fun e v => evalV ρ e = some v) (ms.map .matrix) vs → (∀ m ∈ ms, dims m = (r, c)) →
      vs = ms.map (fun m => mk r c (entV ρ m)) ∧ ∀ m ∈ ms, ∃ w, evalV ρ (.matrix m) = some w
  | [], vs, h, _ => by cases h; simp
  | m :: ms, vs, h, hd => by
    cases h with
    | cons hw hrest =>
      rename_i w ws
      obtain ⟨ih, hex⟩ := forall₂_lits hrest (fun m' hm' => hd m' (by simp [hm']))
      obtain ⟨-, -, hw'⟩ := lit_value hw
      rw [hd m (by simp)] at hw'
      refine ⟨by rw [hw', ih]; rfl, ?_⟩
      intro m' hm'
      simp only [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · exact ⟨w, hw⟩
      · exact hex m' hm'

/-- **`la.add`**: matrices of one shape add entrywise. -/
theorem laAdd_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laAdd.apply e = some res)
    (he : res.error = none) {v : Val} (hv : evalV ρ e = some v) : evalV ρ res.result = some v := by
  unfold laAdd at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i es
    split at hb
    · cases hb
    · split at hb
      · rename_i a rest hmap
        rcases hd : dims a with ⟨r, c⟩
        rw [hd] at hb
        simp only at hb
        split at hb
        · cases hb; simp [refuse] at he
        · rename_i hany
          cases hb
          have hes := mapM_asMat hmap
          subst hes
          simp only [evalV_add, Option.bind_eq_some_iff] at hv
          obtain ⟨vs, hvs, hadd⟩ := hv
          have hall : ∀ m ∈ a :: rest, dims m = (r, c) := by
            intro m hm
            simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact hd
            · simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, not_not] at hany
              exact hany m hm
          obtain ⟨rfl, hex⟩ := forall₂_lits ((evalVs_eq_some ρ _ _).mp hvs) hall
          have hsum := addVals_mk (r := r) (c := c) ((a :: rest).map (entV ρ)) (by simp)
          rw [List.map_map] at hsum
          rw [show (mk r c ∘ entV ρ) = fun m => mk r c (entV ρ m) from rfl] at hsum
          rw [hsum, Option.some.injEq] at hadd
          subst hadd
          obtain ⟨wa, hwa⟩ := hex a (by simp)
          obtain ⟨hr, hc, -⟩ := lit_value hwa
          have hr' : 0 < r := by have : (dims a).1 = r := by rw [hd]
                                 simp only [dims] at this; omega
          rw [hd] at hc
          simp only at hc
          rw [evalV_grid _ hr' hc]
          · intro i j hi hj
            rw [evalV_add, show entry a i j :: rest.map (fun x => entry x i j) =
              (a :: rest).map (fun m => entry m i j) from rfl]
            rw [evalVs_map ρ (fun m => entry m i j) (fun m => .sc (entV ρ m i j)) (a :: rest)]
            · rw [Option.bind_some]
              simpa [List.map_map, Function.comp_def] using addVals_sc ((a :: rest).map fun m => entV ρ m i j)
            · intro m hm
              obtain ⟨w, hw⟩ := hex m hm
              have hdm := hall m hm
              apply entry_value hw
              · have : (dims m).1 = r := by rw [hdm]
                simp only [dims] at this; omega
              · rw [hdm]; exact hj
      · cases hb; simp [refuse] at he
  · cases hb


/-! ## Products: scalars commute with matrices -/

/-- The real factors of a product, in order. -/
def scals : List Val → List ℝ
  | [] => []
  | .sc y :: vs => y :: scals vs
  | .mat _ _ _ :: vs => scals vs

/-- The matrix factors of a product, in order. -/
def mats : List Val → List Val
  | [] => []
  | .sc _ :: vs => mats vs
  | .mat r c f :: vs => .mat r c f :: mats vs

theorem mulV_sc_sc (a P : ℝ) : ∀ X : Val, (mulV (.sc P) X).bind (mulV (.sc a)) = mulV (.sc (a * P)) X
  | .sc y => by simp [mulV, mul_assoc]
  | .mat r c g => by
    simp only [mulV, Option.bind_some, mk, Option.some.injEq, Val.mat.injEq, true_and]
    funext i j; split_ifs <;> ring

theorem mulV_mat_sc_comm (r c : ℕ) (f : ℕ → ℕ → ℝ) (P : ℝ) : ∀ X : Val,
    (mulV (.sc P) X).bind (mulV (.mat r c f)) = (mulV (.mat r c f) X).bind (mulV (.sc P))
  | .sc y => by
    simp only [mulV, Option.bind_some, mk, Option.some.injEq, Val.mat.injEq, true_and]
    funext i j; split_ifs <;> ring
  | .mat r' c' g => by
    simp only [mulV, Option.bind_some, mk]
    split_ifs with h
    · simp only [Option.bind_some, mulV, mk, Option.some.injEq, Val.mat.injEq, true_and]
      funext i j
      split_ifs with hij
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ite_eq_left ⟨h ▸ hk, hij.2⟩]
        ring
      · rfl
    · rfl

/-- **A product's value**: its matrices multiplied in order, times the product of its real factors. -/
theorem mulVals_nf : ∀ vs : List Val, mulVals vs = (mulVals (mats vs)).bind (mulV (.sc (scals vs).prod))
  | [] => by simp [mulVals, mats, scals, mulV]
  | .sc a :: vs => by
    rw [mulVals, mulVals_nf vs, mats, scals, List.prod_cons, Option.bind_assoc]
    congr 1; funext X; exact mulV_sc_sc a _ X
  | .mat r c f :: vs => by
    rw [mulVals, mulVals_nf vs, mats, scals, mulVals, Option.bind_assoc, Option.bind_assoc]
    congr 1; funext X; exact mulV_mat_sc_comm r c f _ X

/-- What the notebook pipeline guarantees of a node's Expr.children when a rule fires: they are normal,
and a normal term holds a matrix literal only at its root. -/
def LitAtRoot (a : Expr) : Prop := hasLitList (Expr.children a) = false

/-- The pipeline fires a rule on a node whose children are normal, and a normal term is literal-free
below its root (`normal_facts`): exactly the hypothesis the matrix rules' theorems take. -/
theorem litAtRoot_of_normal {norm : Norm} {c : Expr} (h : Normal (pipelineRulesWith norm) c) : LitAtRoot c := by
  unfold LitAtRoot
  cases hl : hasLitList (Expr.children c)
  · rfl
  · obtain ⟨d, hd, hd'⟩ := (hasLitList_iff _).mp hl
    rw [((normal_facts h).2.2 d hd).lit] at hd'
    cases hd'

theorem hasLit_of_litAtRoot {a : Expr} (h : LitAtRoot a) (hm : Expr.isMatrix a = false) : hasLit a = false := by
  unfold LitAtRoot at h
  cases a with
  | num _ | var _ => rfl
  | add es | mul es | fn _ es => simpa [hasLit, Expr.children] using h
  | pow b x => simpa [hasLit, Expr.children, hasLitList] using h
  | matrix _ => simp [Expr.isMatrix] at hm

theorem entries_of_litAtRoot {rows : List (List Expr)} (h : LitAtRoot (.matrix rows)) :
    ∀ row ∈ rows, ∀ a ∈ row, hasLit a = false := by
  intro row hrow a ha
  unfold LitAtRoot at h
  simp only [Expr.children] at h
  have := (hasLitList_iff rows.flatten).not.mp (by simp [h])
  simp only [not_exists, not_and, Bool.not_eq_true] at this
  exact this a (List.mem_flatten.mpr ⟨row, hrow, ha⟩)

theorem isMat_of_lit {ρ : EnvR} {rows : List (List Expr)} {v : Val} (h : evalV ρ (.matrix rows) = some v) :
    ∃ r c f, v = .mat r c f := by
  obtain ⟨-, -, rfl⟩ := lit_value h
  exact ⟨_, _, _, rfl⟩

/-- A product's factors, split: the literals give its matrices, the others its real factors. -/
theorem vals_split {ρ : EnvR} : ∀ {es : List Expr} {vs : List Val},
    List.Forall₂ (fun e v => evalV ρ e = some v) es vs → (∀ a ∈ es, Expr.isMatrix a = false → hasLit a = false) →
      List.Forall₂ (fun e v => evalV ρ e = some v) (es.filter Expr.isMatrix) (mats vs) ∧
      scals vs = (es.filter (fun a => !Expr.isMatrix a)).map (evalD ρ)
  | [], [], .nil, _ => by simp [mats, scals]
  | e :: es, v :: vs, .cons hv hrest, hs => by
    obtain ⟨ih₁, ih₂⟩ := vals_split hrest (fun a ha => hs a (by simp [ha]))
    cases hm : Expr.isMatrix e
    · have hl := hs e (by simp) hm
      rw [evalV_of_noLit ρ hl, Option.some.injEq] at hv
      subst hv
      simp [mats, scals, hm, ih₁, ih₂]
    · cases e <;> simp [Expr.isMatrix] at hm
      rename_i rows
      obtain ⟨r, c, f, rfl⟩ := isMat_of_lit hv
      refine ⟨?_, ?_⟩
      · rw [List.filter_cons_of_pos (by rfl)]; exact List.Forall₂.cons hv ih₁
      · rw [List.filter_cons_of_neg (by simp [Expr.isMatrix])]; exact ih₂

theorem hasLit_mulN {l : List Expr} (h : ∀ a ∈ l, hasLit a = false) : hasLit (Expr.mulN l) = false := by
  match l with
  | [x] => simpa [Expr.mulN] using h x (by simp)
  | [] => rfl
  | _ :: _ :: _ =>
    simp only [Expr.mulN, hasLit]
    have := (hasLitList_iff (_ :: _ :: _)).not.mpr (by simp only [not_exists, not_and, Bool.not_eq_true]; exact h)
    simpa using this

theorem evalD_mulN (ρ : EnvR) (l : List Expr) : evalD ρ (Expr.mulN l) = (l.map (evalD ρ)).prod := by
  match l with
  | [x] => simp [Expr.mulN]
  | [] => simp [Expr.mulN]
  | _ :: _ :: _ => simp only [Expr.mulN, evalD_mul]; exact prodD_eq_prod ρ _

theorem entry_map (rows : List (List Expr)) (g : Expr → Expr) {i j : ℕ} (hi : i < rows.length)
    (hj : j < (rows.getD i []).length) : entry (rows.map (·.map g)) i j = g (entry rows i j) := by
  unfold entry
  have h1 : (rows.map (·.map g)).getD i [] = (rows.getD i []).map g := by
    rw [getD_of_lt _ _ (by simpa using hi), getD_of_lt _ _ hi, List.getElem_map]
  rw [h1, getD_of_lt _ _ (by simpa using hj), List.getElem_map, getD_of_lt _ _ hj]

theorem entry_mem {rows : List (List Expr)} {i j : ℕ} (hi : i < rows.length) (hj : j < (rows.getD i []).length) :
    ∃ row ∈ rows, entry rows i j ∈ row := by
  refine ⟨rows.getD i [], ?_, ?_⟩
  · rw [getD_of_lt _ _ hi]; exact List.getElem_mem hi
  · rw [entry, getD_of_lt _ _ hj]; exact List.getElem_mem hj

/-- **`la.scalar-mul`**: a real factor multiplies every entry. -/
theorem laScalarMul_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laScalarMul.apply e = some res)
    (he : res.error = none) (hs : ∀ a ∈ Expr.children e, LitAtRoot a) {v : Val} (hv : evalV ρ e = some v) :
    evalV ρ res.result = some v := by
  unfold laScalarMul at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i es
    simp only [Expr.children] at hs
    dsimp only at hb
    split at hb
    · rename_i rows hmats
      split at hb
      · cases hb
      · cases hb
        simp only [evalV_mul, Option.bind_eq_some_iff] at hv
        obtain ⟨vs, hvs, hmul⟩ := hv
        obtain ⟨hm, hsc⟩ := vals_split ((evalVs_eq_some ρ _ _).mp hvs)
          (fun a ha hma => hasLit_of_litAtRoot (hs a ha) hma)
        rw [hmats] at hm
        obtain ⟨w, u, hw, hnil, hmv⟩ := List.forall₂_cons_left_iff.mp hm
        rw [List.forall₂_nil_left_iff] at hnil
        subst hnil
        rw [mulVals_nf, hmv, hsc] at hmul
        obtain ⟨c, hc, hne, hrect, hent, rfl⟩ := evalV_matrix_eq_some.mp hw
        set P := ((es.filter fun a => !Expr.isMatrix a).map (evalD ρ)).prod with hP
        have hv : v = mk rows.length c fun i j => P * entV ρ rows i j := by
          simp only [mulVals, Option.bind_some, mk, mulV, Option.some.injEq] at hmul
          rw [← hmul]; congr 1; funext i j; split_ifs <;> ring
        subst hv
        have hscal : ∀ a ∈ es.filter (fun a => !Expr.isMatrix a), hasLit a = false := by
          intro a ha
          simp only [List.mem_filter, Bool.not_eq_true'] at ha
          exact hasLit_of_litAtRoot (hs a ha.1) ha.2
        have hsv : evalV ρ (Expr.mulN (es.filter fun a => !Expr.isMatrix a)) = some (.sc P) := by
          rw [evalV_of_noLit ρ (hasLit_mulN hscal), evalD_mulN]
        rw [evalV_matrix_eq_some]
        refine ⟨c, hc, by simpa using hne, ?_, ?_, ?_⟩
        · intro row hrow
          simp only [List.mem_map] at hrow
          obtain ⟨r, hr, rfl⟩ := hrow
          simp [hrect r hr]
        · intro i j hi hj
          rw [List.length_map] at hi
          have hj' : j < (rows.getD i []).length := by
            rw [hrect _ (by rw [getD_of_lt _ _ hi]; exact List.getElem_mem hi)]; exact hj
          rw [entry_map rows _ hi hj']
          obtain ⟨y, hy⟩ := hent i j hi hj
          exact ⟨P * y, by simp [hsv, hy, mulVals, mulV]⟩
        · rw [List.length_map]
          apply mk_congr
          intro i j hi hj
          have hj' : j < (rows.getD i []).length := by
            rw [hrect _ (by rw [getD_of_lt _ _ hi]; exact List.getElem_mem hi)]; exact hj
          simp only [entV]
          rw [entry_map rows _ hi hj']
          obtain ⟨y, hy⟩ := hent i j hi hj
          simp [hsv, hy, mulVals, mulV, scalOf]
    · cases hb
  · cases hb


theorem target_some {e body : Expr} {x : String} (h : target e = some (body, x)) :
    e = .fn "diff" [body, .var x] := by
  unfold target at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h

/-- **`diff.matrix`**: a matrix is differentiated entry by entry. -/
theorem diffMatrix_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : diffMatrix.apply e = some res)
    (he : res.error = none) (hs : ∀ a ∈ Expr.children e, LitAtRoot a) {v : Val} (hv : evalV ρ e = some v) :
    evalV ρ res.result = some v := by
  unfold diffMatrix at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨⟨body, x'⟩, ht, hb⟩ := hb
  obtain rfl := target_some ht
  cases body
  case matrix rows =>
      simp only [Option.some.injEq] at hb
      subst hb
      have hlit : ∀ row ∈ rows, ∀ a ∈ row, hasLit a = false :=
        entries_of_litAtRoot (hs _ (by simp [Expr.children]))
      rw [evalV_fn, fnV_diff] at hv
      cases hm : evalV ρ (.matrix rows) with
      | none => rw [hm] at hv; cases hv
      | some w =>
        rw [hm] at hv
        obtain ⟨c, hc, hne, hrect, hent, rfl⟩ := evalV_matrix_eq_some.mp hm
        simp only [mk, Option.some.injEq] at hv
        subst hv
        have hlen : ∀ i, i < rows.length → (rows.getD i []).length = c := fun i hi =>
          hrect _ (by rw [getD_of_lt _ _ hi]; exact List.getElem_mem hi)
        have hfree : ∀ i j, i < rows.length → j < c → hasLit (entry rows i j) = false := by
          intro i j hi hj
          obtain ⟨row, hrow, hmem⟩ := entry_mem hi (by rw [hlen i hi]; exact hj)
          exact hlit row hrow _ hmem
        -- at every point the literal is the matrix of its entries' values
        have hat : ∀ t, evalV (upd ρ x' t) (.matrix rows) =
            some (mk rows.length c fun i j => evalD (upd ρ x' t) (entry rows i j)) := by
          intro t
          rw [evalV_matrix_eq_some]
          refine ⟨c, hc, hne, hrect, fun i j hi hj => ⟨_, evalV_of_noLit _ (hfree i j hi hj)⟩, ?_⟩
          apply mk_congr; intro i j hi hj
          simp [entV, evalV_of_noLit _ (hfree i j hi hj), scalOf]
        rw [evalV_matrix_eq_some]
        refine ⟨c, hc, by simpa using hne, ?_, ?_, ?_⟩
        · intro row hrow
          simp only [List.mem_map] at hrow
          obtain ⟨r, hr, rfl⟩ := hrow
          simp [hrect r hr]
        · intro i j hi hj
          rw [List.length_map] at hi
          rw [entry_map rows _ hi (by rw [hlen i hi]; exact hj)]
          exact ⟨_, evalV_of_noLit ρ (by simpa [MathEngine.D, hasLit, hasLitList] using hfree i j hi hj)⟩
        · rw [List.length_map, mk]
          congr 1; funext i j
          split_ifs with hij
          · simp only [entV]
            rw [entry_map rows _ hij.1 (by rw [hlen i hij.1]; exact hij.2)]
            rw [evalV_of_noLit ρ (by simpa [MathEngine.D, hasLit, hasLitList] using hfree i j hij.1 hij.2)]
            simp only [scalOf, MathEngine.D, evalD_diff, D]
            congr 1; funext t
            rw [hat t]
            simp [entOf, mk, hij.1, hij.2]
          · rfl
  all_goals simp at hb


/-! ## Powers -/

/-- Entries of a literal with a value, as a Mathlib matrix. -/
abbrev litM (ρ : EnvR) (rows : List (List Expr)) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := toM n n (entV ρ rows)

/-- The value of a product of real-valued entries, and of their sum. -/
theorem evalV_mul2 {ρ : EnvR} {a b : Expr} {x y : ℝ} (ha : evalV ρ a = some (.sc x)) (hb : evalV ρ b = some (.sc y)) :
    evalV ρ (.mul [a, b]) = some (.sc (x * y)) := by
  simp [ha, hb, mulVals, mulV]

theorem evalV_sum_range {ρ : EnvR} (n : ℕ) (E : ℕ → Expr) (f : ℕ → ℝ)
    (h : ∀ k, k < n → evalV ρ (E k) = some (.sc (f k))) :
    evalV ρ (.add ((List.range n).map E)) = some (.sc (∑ k ∈ Finset.range n, f k)) := by
  rw [evalV_add, evalVs_map ρ E (fun k => .sc (f k)) _ (fun k hk => h k (List.mem_range.mp hk)),
    Option.bind_some, ← sum_range_list]
  simpa [Function.comp_def] using addVals_sc ((List.range n).map f)

theorem mulEntry_value {ρ : EnvR} {a b : List (List Expr)} {ra n cb : ℕ} {F G : ℕ → ℕ → ℝ}
    (ha : ∀ i k, i < ra → k < n → evalV ρ (entry a i k) = some (.sc (F i k)))
    (hb : ∀ k j, k < n → j < cb → evalV ρ (entry b k j) = some (.sc (G k j))) {i j : ℕ} (hi : i < ra) (hj : j < cb) :
    evalV ρ (mulEntry a b n i j) = some (.sc (∑ k ∈ Finset.range n, F i k * G k j)) :=
  evalV_sum_range n _ _ fun k hk => evalV_mul2 (ha i k hi hk) (hb k j hk hj)

theorem matMul_sum (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ Finset.range n, ofM A i k * ofM B k j = ofM (A * B) i j := by
  rw [ofM_apply _ hi hj, Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range (fun k => ofM A i k * ofM B k j)]
  apply Finset.sum_congr rfl
  intro k _
  rw [ofM_apply _ hi k.isLt, ofM_apply _ k.isLt hj]

/-- **The literal `matPow` builds is the power** in the monoid of square matrices. -/
theorem matPow_value {ρ : EnvR} {rows : List (List Expr)} {n : ℕ} (hn : 0 < n) (hd : dims rows = (n, n))
    (hne : rows ≠ []) (hrect : ∀ row ∈ rows, row.length = n)
    (hent : ∀ i j, i < n → j < n → evalV ρ (entry rows i j) = some (.sc (entV ρ rows i j))) :
    ∀ m, dims (matPow rows m) = (n, n) ∧ matPow rows m ≠ [] ∧ (∀ row ∈ matPow rows m, row.length = n) ∧
      ∀ i j, i < n → j < n → evalV ρ (entry (matPow rows m) i j) = some (.sc (ofM (litM ρ rows n ^ (m + 1)) i j))
  | 0 => by
    refine ⟨hd, hne, hrect, fun i j hi hj => ?_⟩
    rw [show matPow rows 0 = rows from rfl, hent i j hi hj, pow_one, ofM_apply _ hi hj]; rfl
  | m + 1 => by
    obtain ⟨hdm, -, -, hentm⟩ := matPow_value hn hd hne hrect hent m
    have hgrid : matPow rows (m + 1) = (List.range n).map fun i => (List.range n).map fun j =>
        mulEntry rows (matPow rows m) n i j := by
      simp only [matPow, matMul, hd, hdm]
    refine ⟨?_, ?_, ?_, fun i j hi hj => ?_⟩
    · rw [hgrid]; simp [dims, List.head?_map, List.head?_range, show n ≠ 0 by omega]
    · rw [hgrid]; exact grid_ne_nil _ hn
    · rw [hgrid]; exact grid_rect n n _
    · rw [hgrid, entry_grid n n _ hi hj]
      rw [mulEntry_value (F := ofM (litM ρ rows n)) (G := ofM (litM ρ rows n ^ (m + 1)))
        (fun i k hi hk => by rw [hent i k hi hk, ofM_apply _ hi hk]; rfl) hentm hi hj]
      rw [matMul_sum n _ _ hi hj, ← pow_succ']

theorem Q_isInt_cast {q : Q} (h : q.isInt = true) : (q.val : ℝ) = ((q.val.num : ℤ) : ℝ) := by
  simp only [Q.isInt, beq_iff_eq] at h
  rw [Rat.cast_def, h]; simp

/-- **`la.pow`**: a square matrix to a positive integer power. -/
theorem laPow_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laPow.apply e = some res)
    (he : res.error = none) {v : Val} (hv : evalV ρ e = some v) : evalV ρ res.result = some v := by
  unfold laPow at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i rows q
    rcases hd : dims rows with ⟨r, c⟩
    rw [hd] at hb
    simp only at hb
    split at hb
    · cases hb; simp [refuse] at he
    · rename_i hrc
      simp only [bne_iff_ne, ne_eq, not_not] at hrc
      subst hrc
      split at hb
      · rename_i hq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨hint, hpos⟩ := hq
        simp only [evalV_pow, evalV_num, Option.bind_eq_some_iff, Option.bind_some] at hv
        obtain ⟨w, hw, hpow⟩ := hv
        obtain ⟨c, hc, hne, hrect, hent, rfl⟩ := evalV_matrix_eq_some.mp hw
        rw [dims_of_rect hne hrect, Prod.mk.injEq] at hd
        obtain ⟨hlen, rfl⟩ := hd
        rw [hlen] at hpow
        set k := q.val.num.toNat with hk
        have hkq : ((⌊(q.val : ℝ)⌋₊ : ℕ) : ℝ) = q.val ∧ ⌊(q.val : ℝ)⌋₊ = k ∧ 1 ≤ k := by
          have : (q.val : ℝ) = (k : ℝ) := by
            rw [Q_isInt_cast hint, hk]
            have h0 : (0 : ℤ) ≤ q.val.num := by omega
            exact_mod_cast (Int.toNat_of_nonneg h0).symm
          rw [this, Nat.floor_natCast]; exact ⟨rfl, rfl, by omega⟩
        obtain ⟨hfl, hkk, hk1⟩ := hkq
        have hq1 : (1 : ℝ) ≤ q.val := by rw [← hfl, hkk]; exact_mod_cast hk1
        simp only [mk, powV, and_self, hq1, hfl, ite_true, Option.some.injEq] at hpow
        subst hpow
        have hent' : ∀ i j, i < c → j < c → evalV ρ (entry rows i j) = some (.sc (entV ρ rows i j)) := by
          intro i j hi hj
          obtain ⟨y, hy⟩ := hent i j (hlen ▸ hi) hj
          simp [entV, hy, scalOf]
        have hdims : dims rows = (c, c) := by rw [dims_of_rect hne hrect, hlen]
        split at hb
        · rename_i hk1'
          have hkone : k = 1 := by simpa using hk1'
          cases hb
          rw [hw, hlen, hkk, hkone, pow_one]
          congr 1; apply mk_congr; intro i j hi hj
          rw [ofM_apply _ hi hj]; simp [toM]
        · rename_i hk1'
          have hk2 : k ≠ 1 := by simpa using hk1'
          cases hb
          obtain ⟨hdP, hneP, hrectP, hentP⟩ := matPow_value hc hdims hne (hlen ▸ hrect) hent' (k - 1)
          rw [evalV_matrix_eq_some]
          have hlenP : (matPow rows (k - 1)).length = c := by
            have : (dims (matPow rows (k - 1))).1 = c := by rw [hdP]
            simpa [dims] using this
          refine ⟨c, hc, hneP, hrectP, fun i j hi hj => ⟨_, hentP i j (hlenP ▸ hi) hj⟩, ?_⟩
          rw [hlenP, hkk]
          apply mk_congr; intro i j hi hj
          rw [entV, hentP i j hi hj, scalOf, toM_mk_eq, show k - 1 + 1 = k by omega]
      · cases hb; simp [refuse] at he
  · cases hb


/-! ## Determinants: the engine's Laplace expansion is `Matrix.det` -/

/-- Dropping index `j` by `zipIdx`/`filter`, as `minor` does, is `eraseIdx`. -/
theorem filter_zipIdx_eraseIdx {α : Type*} : ∀ (l : List α) (n j : ℕ),
    ((l.zipIdx n).filter (·.2 != j)).map (·.1) = if n ≤ j then l.eraseIdx (j - n) else l
  | [], n, j => by simp
  | x :: xs, n, j => by
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hnj : n = j
    · subst hnj
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, le_refl, ite_true, Nat.sub_self,
        List.eraseIdx_cons_zero]
      rw [filter_zipIdx_eraseIdx xs (n + 1) n, ite_eq_right (by omega)]
    · have hb : (n != j) = true := by simpa using hnj
      simp only [hb, ite_true, List.map_cons]
      rw [filter_zipIdx_eraseIdx xs (n + 1) j]
      by_cases hle : n ≤ j
      · rw [ite_eq_left (by omega), ite_eq_left hle, show j - n = (j - (n + 1)) + 1 by omega, List.eraseIdx_cons_succ]
      · rw [ite_eq_right (by omega), ite_eq_right hle]

theorem minor_eq (others : List (List Expr)) (j : ℕ) : minor others j = others.map (·.eraseIdx j) := by
  unfold minor
  congr 1; funext row
  have := filter_zipIdx_eraseIdx row 0 j
  simpa using this

theorem sign_value (ρ : EnvR) (j : ℕ) :
    evalV ρ (if j % 2 == 0 then Expr.one else Expr.minusOne) = some (.sc ((-1) ^ j)) := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [ite_eq_left (by simpa [Nat.even_iff] using hj), hj.neg_one_pow]
    simp [Expr.one, Q.one, Q.ofInt]
  · rw [ite_eq_right (by simpa [Nat.odd_iff] using hj), hj.neg_one_pow]
    simp [Expr.minusOne, Q.minusOne, Q.ofInt]

theorem sum_zipIdx {α : Type*} (l : List α) (d : α) (f : α × ℕ → ℝ) :
    (l.zipIdx.map f).sum = ∑ j ∈ Finset.range l.length, f (l.getD j d, j) := by
  have : l.zipIdx = (List.range l.length).map fun j => (l.getD j d, j) := by
    apply List.ext_getElem
    · simp
    · intro k h₁ h₂
      simp only [List.length_zipIdx] at h₁
      simp [List.getElem_zipIdx, List.getElem?_eq_getElem h₁]
  rw [this, List.map_map, sum_range_list]; rfl

theorem succAbove_val {m : ℕ} (j : Fin (m + 1)) (k : Fin m) :
    (j.succAbove k : ℕ) = if (k : ℕ) < j then (k : ℕ) else (k : ℕ) + 1 := by
  by_cases h : (k : ℕ) < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), ite_eq_left h]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega), ite_eq_right h]; rfl

/-- **Laplace expansion**: `detExpr` of a square literal of side `n + 1` has the determinant as its
value. -/
theorem detExpr_cons3 (fuel : ℕ) (first r1 r2 : List Expr) (rest : List (List Expr)) :
    detExpr (fuel + 1) (first :: r1 :: r2 :: rest) =
      .add (first.zipIdx.map fun (a1j, j) =>
        .mul [if j % 2 == 0 then Expr.one else Expr.minusOne, a1j, detExpr fuel (minor (r1 :: r2 :: rest) j)]) := by
  rw [detExpr] <;> simp

theorem detExpr_value {ρ : EnvR} : ∀ (n : ℕ) (rows : List (List Expr)) (F : ℕ → ℕ → ℝ),
    rows.length = n + 1 → (∀ row ∈ rows, row.length = n + 1) →
    (∀ i j, i < n + 1 → j < n + 1 → evalV ρ (entry rows i j) = some (.sc (F i j))) →
    evalV ρ (detExpr (n + 1) rows) = some (.sc (toM (n + 1) (n + 1) F).det)
  | 0, rows, F, hlen, hrect, hent => by
    match rows, hlen with
    | [row], _ =>
      match row, hrect row (by simp) with
      | [a], _ =>
        have := hent 0 0 (by omega) (by omega)
        simp only [entry, List.getD_cons_zero] at this
        simp [detExpr, this, Matrix.det_unique, toM]
  | 1, rows, F, hlen, hrect, hent => by
    match rows, hlen with
    | [r0, r1], _ =>
      match r0, r1, hrect r0 (by simp), hrect r1 (by simp) with
      | [a, b], [c, d], _, _ =>
        have h00 := hent 0 0 (by omega) (by omega)
        have h01 := hent 0 1 (by omega) (by omega)
        have h10 := hent 1 0 (by omega) (by omega)
        have h11 := hent 1 1 (by omega) (by omega)
        simp only [entry, List.getD_cons_zero, List.getD_cons_succ] at h00 h01 h10 h11
        simp only [detExpr, Expr.sub, Expr.neg, evalV_add, evalVs_cons, evalVs_nil, evalV_mul, h00, h01,
          h10, h11, Option.bind_some, Option.map_some, mulVals, mulV]
        simp [Matrix.det_fin_two, toM, Expr.minusOne, Q.minusOne, Q.ofInt, mulVals, mulV, addVals, addV]
        ring
  | n + 2, rows, F, hlen, hrect, hent => by
    match rows, hlen with
    | first :: r1 :: r2 :: rest, hlen =>
      have hfirst : first.length = n + 3 := hrect first (by simp)
      have hlo : (r1 :: r2 :: rest).length = n + 2 := by simp at hlen ⊢; omega
      rw [detExpr_cons3]
      -- each cofactor: the minor is a square literal of side n + 2, the submatrix
      have hminor : ∀ j, j < n + 3 →
          evalV ρ (detExpr (n + 2) (minor (r1 :: r2 :: rest) j)) =
            some (.sc (toM (n + 2) (n + 2) (fun i k => F (i + 1) (if k < j then k else k + 1))).det) := by
        intro j hj
        rw [minor_eq]
        have hmem : ∀ r ∈ r1 :: r2 :: rest, r.length = n + 3 := fun r hr => hrect r (List.mem_cons_of_mem _ hr)
        apply detExpr_value (n + 1)
        · simp only [List.length_map]; exact hlo
        · intro row hrow
          simp only [List.mem_map] at hrow
          obtain ⟨r, hr, rfl⟩ := hrow
          rw [List.length_eraseIdx_of_lt (by rw [hmem r hr]; omega), hmem r hr]
          omega
        · intro i k hi hk
          have hi' : i < (r1 :: r2 :: rest).length := by omega
          have hrow : ((r1 :: r2 :: rest)[i]).length = n + 3 := hmem _ (List.getElem_mem hi')
          have := hent (i + 1) (if k < j then k else k + 1) (by omega) (by split_ifs <;> omega)
          rw [← this]
          congr 1
          unfold entry
          rw [getD_of_lt ((r1 :: r2 :: rest).map (·.eraseIdx j)) [] (n := i) (by simpa using hi'), List.getElem_map,
            getD_of_lt _ _ (by rw [List.length_eraseIdx_of_lt (by omega)]; omega), List.getElem_eraseIdx,
            List.getD_cons_succ, getD_of_lt _ _ hi']
          split_ifs <;> rw [getD_of_lt _ _ (by omega)]
      have hterm : ∀ p ∈ first.zipIdx,
          evalV ρ ((fun (x : Expr × ℕ) => match x with
              | (a1j, j) => Expr.mul [if j % 2 == 0 then Expr.one else Expr.minusOne, a1j,
                  detExpr (n + 2) (minor (r1 :: r2 :: rest) j)]) p) =
            some (.sc ((-1) ^ p.2 * (F 0 p.2 * ((toM (n + 2) (n + 2)
              (fun i k => F (i + 1) (if k < p.2 then k else k + 1))).det * 1)))) := by
        rintro ⟨a, j⟩ hp
        have hj : j < n + 3 := by have := List.snd_lt_of_mem_zipIdx hp; simp [hfirst] at this; omega
        have ha : a = entry (first :: r1 :: r2 :: rest) 0 j := by
          have := List.mk_mem_zipIdx_iff_getElem?.mp hp
          rw [entry, List.getD_cons_zero, List.getD_eq_getElem?_getD, this, Option.getD_some]
        have hav := hent 0 j (by omega) hj
        rw [← ha] at hav
        simp only [evalV_mul, evalVs_cons, sign_value, hav, hminor j hj, evalVs_nil, Option.bind_some,
          Option.map_some, mulVals, mulV]
      rw [evalV_add, evalVs_map ρ _ _ first.zipIdx hterm, Option.bind_some]
      rw [addVals_map_sc, sum_zipIdx first Expr.zero, hfirst]
      congr 2
      rw [Matrix.det_succ_row_zero, Finset.sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp only [toM_apply, Fin.val_zero, mul_one, mul_assoc]
      congr 2
      congr 1
      ext i k
      simp only [Matrix.submatrix_apply, toM_apply, Fin.val_succ, succAbove_val]


/-- **`la.det`**: the determinant, by Laplace expansion along the first row. -/
theorem laDet_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laDet.apply e = some res)
    (he : res.error = none) {v : Val} (hv : evalV ρ e = some v) : evalV ρ res.result = some v := by
  unfold laDet at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i rows
    rcases hd : dims rows with ⟨r, c⟩
    rw [hd] at hb
    simp only at hb
    split at hb
    · cases hb; simp [refuse] at he
    · rename_i hrc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, not_not] at hrc
      obtain ⟨rfl, hr0⟩ := hrc
      obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
      simp only [evalV_fn, fnV_one, Option.bind_eq_some_iff] at hv
      obtain ⟨w, hw, hdet⟩ := hv
      obtain ⟨c', hc, hne, hrect, hent, rfl⟩ := evalV_matrix_eq_some.mp hw
      rw [dims_of_rect hne hrect, Prod.mk.injEq] at hd
      obtain ⟨hlen, rfl⟩ := hd
      simp only [mk, fn1, show ("det" = "transpose") = False by decide, ite_false, true_and, ite_true, hlen,
        Option.some.injEq] at hdet
      subst hdet
      rw [toM_mk_eq]
      have hent' : ∀ i j, i < n + 1 → j < n + 1 → evalV ρ (entry rows i j) = some (.sc (entV ρ rows i j)) := by
        intro i j hi hj
        obtain ⟨y, hy⟩ := hent i j (hlen ▸ hi) hj
        simp [entV, hy, scalOf]
      have hval := detExpr_value (ρ := ρ) n rows (entV ρ rows) hlen hrect hent'
      split at hb
      · rename_i a
        cases hb
        have : detExpr (n + 1) [[a]] = a := by simp [detExpr]
        rw [← this]; exact hval
      · rename_i a b c d
        cases hb
        have : detExpr (n + 1) [[a, b], [c, d]] = Expr.sub (.mul [a, d]) (.mul [b, c]) := by simp [detExpr]
        rw [← this]; exact hval
      · cases hb; exact hval
  · cases hb


/-! ## Products of matrices -/

theorem forall₂_unique {ρ : EnvR} : ∀ {es : List Expr} {vs ws : List Val},
    List.Forall₂ (fun e v => evalV ρ e = some v) es vs → List.Forall₂ (fun e v => evalV ρ e = some v) es ws → vs = ws
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [h₁, Option.some.injEq] at h₂
    rw [h₂, forall₂_unique t₁ t₂]

/-- Matrix multiplication is associative, and a literal product is the product. -/
theorem mulV_assoc {ar ac bc : ℕ} (FA FB : ℕ → ℕ → ℝ) : ∀ X : Val,
    (mulV (mk ac bc FB) X).bind (mulV (mk ar ac FA)) =
      mulV (mk ar bc fun i j => ∑ k ∈ Finset.range ac, FA i k * FB k j) X
  | .sc y => by
    simp only [mk, mulV, Option.bind_some, ite_true, Option.some.injEq, Val.mat.injEq, true_and]
    funext i j
    split_ifs with hij
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k hk
      rw [Finset.mem_range] at hk
      simp only [hk, hij.1, hij.2, and_self, ite_true]; ring
    · rfl
  | .mat r' c' g => by
    simp only [mk, mulV]
    split_ifs with h
    · simp only [Option.bind_some, mulV, mk, ite_true, Option.some.injEq, Val.mat.injEq, true_and]
      funext i j
      split_ifs with hij
      · rw [Finset.sum_congr rfl (g := fun x => ∑ y ∈ Finset.range bc, FA i x * (FB x y * g y j))]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y hy
          rw [Finset.mem_range] at hy
          rw [ite_eq_left ⟨hij.1, hy⟩, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro x _; ring
        · intro x hx
          rw [Finset.mem_range] at hx
          rw [ite_eq_left ⟨hij.1, hx⟩, ite_eq_left ⟨hx, hij.2⟩, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro y hy
          rw [Finset.mem_range] at hy
          rw [ite_eq_left ⟨hx, hy⟩]
      · rfl
    · rfl

theorem mulV_one_mk (r c : ℕ) (F : ℕ → ℕ → ℝ) : mulV (mk r c F) (.sc 1) = some (mk r c F) := by
  simp only [mk, mulV, Option.some.injEq, Val.mat.injEq, true_and]
  funext i j; split_ifs <;> simp

/-- `filter` through `zipIdx` and back. -/
theorem filter_eq_zipIdx {α : Type*} (l : List α) (p : α → Bool) :
    l.filter p = ((l.zipIdx.filter fun x => p x.1).map (·.1)) := by
  conv_lhs => rw [← List.zipIdx_map_fst 0 l]
  rw [List.filter_map]; rfl

/-- The list `la.mul` builds: the factors with the first two matrices replaced by their product. -/
theorem mul_splice (l : List Expr) {xa xb M : Expr} {i j : ℕ} {rest : List (Expr × ℕ)}
    (hL : l.zipIdx.filter (fun p => Expr.isMatrix p.1) = (xa, i) :: (xb, j) :: rest) (hM : Expr.isMatrix M = true) :
    let g : Expr × ℕ → Expr := fun x => match x with | (x, k) => if k == i then M else x
    let es' := (l.zipIdx.filter (·.2 != j)).map g
    es'.filter Expr.isMatrix = M :: rest.map (·.1) ∧
      es'.filter (fun a => !Expr.isMatrix a) = l.filter (fun a => !Expr.isMatrix a) ∧
      ∀ x ∈ es', x = M ∨ x ∈ l := by
  intro g es'
  have hnd : ((l.zipIdx.filter fun p => Expr.isMatrix p.1).map (·.2)).Nodup :=
    List.Nodup.sublist ((List.filter_sublist).map _) (by rw [List.zipIdx_map_snd]; exact List.nodup_range')
  rw [hL] at hnd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or, not_exists, not_and] at hnd
  obtain ⟨⟨hij, hirest⟩, hjrest, -⟩ := hnd
  have hmem : ∀ p, p ∈ l.zipIdx.filter (fun p => Expr.isMatrix p.1) ↔ p ∈ (xa, i) :: (xb, j) :: rest := by rw [hL]; simp
  have hxa := (hmem (xa, i)).mpr (by simp)
  have hxb := (hmem (xb, j)).mpr (by simp)
  simp only [List.mem_filter] at hxa hxb
  have hlA := List.mk_mem_zipIdx_iff_getElem?.mp hxa.1
  have hlB := List.mk_mem_zipIdx_iff_getElem?.mp hxb.1
  -- at index `i` the list holds a matrix; elsewhere `g` is the projection
  have hg : ∀ p ∈ l.zipIdx, p.2 ≠ i → g p = p.1 := by
    rintro ⟨x, k⟩ _ hk; simp [g, hk]
  have hgi : ∀ p ∈ l.zipIdx, p.2 = i → p.1 = xa := by
    rintro ⟨x, k⟩ hp rfl
    have := List.mk_mem_zipIdx_iff_getElem?.mp hp
    rw [hlA] at this; exact (Option.some.inj this).symm
  have hgj : ∀ p ∈ l.zipIdx, p.2 = j → p.1 = xb := by
    rintro ⟨x, k⟩ hp rfl
    have := List.mk_mem_zipIdx_iff_getElem?.mp hp
    rw [hlB] at this; exact (Option.some.inj this).symm
  have hmat : ∀ p ∈ l.zipIdx, Expr.isMatrix (g p) = Expr.isMatrix p.1 := by
    intro p hp
    by_cases hk : p.2 = i
    · rw [hgi p hp hk, hxa.2]; simp [g, hk, hM]
    · rw [hg p hp hk]
  refine ⟨?_, ?_, ?_⟩
  · simp only [es', List.filter_map, List.filter_filter, Function.comp_def]
    rw [List.filter_congr (q := fun p => Expr.isMatrix p.1 && p.2 != j)
      (fun p hp => by rw [hmat p hp])]
    have hzip : ∀ p ∈ rest, p ∈ l.zipIdx := fun p hp =>
      (List.mem_filter.mp ((hmem p).mpr (by simp [hp]))).1
    rw [List.filter_congr (q := fun p : Expr × ℕ => p.2 != j && Expr.isMatrix p.1) (fun p _ => Bool.and_comm _ _),
      ← List.filter_filter, hL, List.filter_cons_of_pos (by simpa using hij), List.filter_cons_of_neg (by simp),
      List.filter_eq_self.mpr (fun p hp => by simpa using hjrest p hp), List.map_cons]
    congr 1
    · simp [g]
    · apply List.map_congr_left
      intro p hp
      exact hg p (hzip p hp) (hirest p hp)
  · simp only [es', List.filter_map, List.filter_filter, Function.comp_def]
    rw [filter_eq_zipIdx l (fun a => !Expr.isMatrix a)]
    rw [List.filter_congr (q := fun p => !Expr.isMatrix p.1) (fun p hp => ?_)]
    · apply List.map_congr_left
      intro p hp
      rw [List.mem_filter] at hp
      by_cases hk : p.2 = i
      · exfalso
        have := hgi p hp.1 hk
        rw [this, hxa.2] at hp
        simp at hp
      · exact hg p hp.1 hk
    · rw [hmat p hp]
      by_cases hk : p.2 = j
      · rw [hgj p hp hk, hxb.2]; simp
      · simp [hk]
  · intro x hx
    simp only [es', List.mem_map, List.mem_filter] at hx
    obtain ⟨⟨y, k⟩, ⟨hp, -⟩, rfl⟩ := hx
    by_cases hk : k = i
    · left; simp [g, hk]
    · right; rw [hg (y, k) hp hk]; exact List.fst_mem_of_mem_zipIdx hp

theorem forall₂_exists {ρ : EnvR} : ∀ {es : List Expr} {vs : List Val},
    List.Forall₂ (fun e v => evalV ρ e = some v) es vs → ∀ x ∈ es, ∃ w, evalV ρ x = some w
  | _, _, .nil => by simp
  | _, _, .cons h t => by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, h⟩
    · exact forall₂_exists t x hx

/-- A product's value through `mulN`, which leaves a lone factor bare. -/
theorem evalV_mulN_of {ρ : EnvR} {l : List Expr} {vs : List Val} {v : Val} (hl : evalVs ρ l = some vs)
    (hv : mulVals vs = some v) (hone : ∀ w, vs = [w] → mulV w (.sc 1) = some w) :
    evalV ρ (Expr.mulN l) = some v := by
  match l, hl with
  | [x], hl =>
    simp only [Expr.mulN]
    simp only [evalVs_cons, evalVs_nil, Option.map_some, Option.bind_eq_some_iff, Option.some.injEq] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    simp only [mulVals, Option.bind_some] at hv
    rw [hone w rfl, Option.some.injEq] at hv
    rw [hw, hv]
  | [], hl => simp only [Expr.mulN, evalV_mul, hl, Option.bind_some]; exact hv
  | _ :: _ :: _, hl => simp only [Expr.mulN, evalV_mul, hl, Option.bind_some]; exact hv

/-- **`la.mul`**: the first two matrix factors are multiplied, entry `(i, j)` the dot product of row `i`
and column `j`; the real factors commute past them. -/
theorem laMul_sound (ρ : EnvR) {e : Expr} {res : RuleResult} (h : laMul.apply e = some res)
    (he : res.error = none) (hs : ∀ a ∈ Expr.children e, LitAtRoot a) {v : Val} (hv : evalV ρ e = some v) :
    evalV ρ res.result = some v := by
  unfold laMul at h
  obtain ⟨r₀, hb, rfl⟩ := lit_ok h he
  split at hb
  · rename_i es
    simp only [Expr.children] at hs
    have hsc : ∀ a ∈ es, Expr.isMatrix a = false → hasLit a = false := fun a ha hm => hasLit_of_litAtRoot (hs a ha) hm
    split at hb
    · rename_i a i b j rest hL
      rcases hda : dims a with ⟨ar, ac⟩
      rcases hdb : dims b with ⟨br, bc⟩
      rw [hda, hdb] at hb
      simp only at hb
      split at hb
      · cases hb; simp [refuse] at he
      · rename_i hab
        simp only [bne_iff_ne, ne_eq, not_not] at hab
        subst hab
        cases hb
        simp only [evalV_mul, Option.bind_eq_some_iff] at hv
        obtain ⟨vs, hvs, hmul⟩ := hv
        have hF := (evalVs_eq_some ρ _ _).mp hvs
        obtain ⟨hm, hscv⟩ := vals_split hF hsc
        rw [filter_eq_zipIdx, hL] at hm
        simp only [List.map_cons] at hm
        obtain ⟨A, u, hA, hm, hu⟩ := List.forall₂_cons_left_iff.mp hm
        obtain ⟨B, Ms, hB, hMs, rfl⟩ := List.forall₂_cons_left_iff.mp hm
        obtain ⟨ca, hca, hnea, hrecta, henta, rfl⟩ := evalV_matrix_eq_some.mp hA
        obtain ⟨cb, hcb, hneb, hrectb, hentb, rfl⟩ := evalV_matrix_eq_some.mp hB
        have hda' := dims_of_rect hnea hrecta
        have hdb' := dims_of_rect hneb hrectb
        rw [hda', Prod.mk.injEq] at hda
        rw [hdb', Prod.mk.injEq] at hdb
        obtain ⟨har, hac⟩ := hda
        obtain ⟨hbr, hbc⟩ := hdb
        subst har hac hbc
        have hea : ∀ i k, i < a.length → k < ca → evalV ρ (entry a i k) = some (.sc (entV ρ a i k)) :=
          fun i k hi hk => by obtain ⟨y, hy⟩ := henta i k hi hk; simp [entV, hy, scalOf]
        have heb : ∀ k j, k < ca → j < cb → evalV ρ (entry b k j) = some (.sc (entV ρ b k j)) :=
          fun k j hk hj => by obtain ⟨y, hy⟩ := hentb k j (hbr ▸ hk) hj; simp [entV, hy, scalOf]
        -- the product of the two literals is a literal with the product's value
        have hprod : evalV ρ (.matrix (matMul a b)) =
            some (mk a.length cb fun i j => ∑ k ∈ Finset.range ca, entV ρ a i k * entV ρ b k j) := by
          have hg : matMul a b = (List.range a.length).map fun i => (List.range cb).map fun j =>
              mulEntry a b ca i j := by
            simp only [matMul, hda', hdb']
          rw [hg]
          exact evalV_grid _ (List.length_pos_iff.mpr hnea) hcb (fun i j hi hj => mulEntry_value hea heb hi hj)
        -- the new factors: the real ones as before, the matrices with the first two multiplied
        have hsp := mul_splice es hL (M := .matrix (matMul a b)) rfl
        dsimp only at hsp
        obtain ⟨hfil1, hfil2, hmemb⟩ := hsp
        have hex' : ∀ x ∈ (es.zipIdx.filter (·.2 != j)).map (fun x => match x with
            | (x, k) => if k == i then Expr.matrix (matMul a b) else x), ∃ w, evalV ρ x = some w := by
          intro x hx
          rcases hmemb x hx with rfl | hx'
          · exact ⟨_, hprod⟩
          · exact forall₂_exists hF x hx'
        obtain ⟨vs', hvs'⟩ := evalVs_of_forall ρ _ hex'
        have hF' := (evalVs_eq_some ρ _ _).mp hvs'
        have hsc' : ∀ x ∈ (es.zipIdx.filter (·.2 != j)).map (fun x => match x with
            | (x, k) => if k == i then Expr.matrix (matMul a b) else x),
            Expr.isMatrix x = false → hasLit x = false := by
          intro x hx hmx
          rcases hmemb x hx with rfl | hx'
          · simp [Expr.isMatrix] at hmx
          · exact hsc x hx' hmx
        obtain ⟨hm', hscv'⟩ := vals_split hF' hsc'
        rw [hfil1] at hm'
        obtain ⟨AB, Ms', hAB, hMs', hmats'⟩ := List.forall₂_cons_left_iff.mp hm'
        rw [hprod, Option.some.injEq] at hAB
        subst hAB
        have hMsEq := forall₂_unique hMs hMs'
        subst hMsEq
        have hscEq : scals vs' = scals vs := by rw [hscv', hscv, hfil2]
        have hval : mulVals vs' = some v := by
          rw [mulVals_nf, hmats', hscEq]
          rw [mulVals_nf, hu, hbr] at hmul
          rw [← hmul]
          congr 1
          simp only [mulVals]
          rw [Option.bind_assoc]
          congr 1; funext X
          exact (mulV_assoc (entV ρ a) (entV ρ b) X).symm
        apply evalV_mulN_of hvs' hval
        intro w hw
        rw [hw] at hmats'
        cases w with
        | sc _ => simp [mats] at hmats'
        | mat r c f =>
          simp only [mats, List.cons.injEq] at hmats'
          rw [hmats'.1]
          exact mulV_one_mk _ _ _
    · cases hb
  · cases hb

end MathProofs
end
