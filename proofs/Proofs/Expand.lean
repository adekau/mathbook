import Proofs.SimpReal
/-!
# `expand` is sound

`Expand.dist` (engine, `ExpandRules.lean`) multiplies out products and powers of sums, collecting
like monomials as it goes. It is a total function rather than a rewrite system, so its soundness
is one structural induction: every intermediate — a monomial, a polynomial, the product of two
polynomials — has the value it should. Nothing here is conditional: distribution holds in every
commutative ring.

The polynomial lemmas are stated for any semantics `S : Sem` that reads sums, products, numerals
and powers the obvious way, because two do: `evalR` (M3) here, and `evalD` (M4, which also reads
`diff`) in `Proofs/Integrate.lean`, where `dist` is part of the integral checker.
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expr
open MathEngine.Expand

/-- What the polynomial arithmetic needs of a semantics. -/
structure Sem where
  ev : EnvR → Expr → ℝ
  ev_add : ∀ ρ es, ev ρ (.add es) = (es.map (ev ρ)).sum
  ev_mul : ∀ ρ es, ev ρ (.mul es) = (es.map (ev ρ)).prod
  ev_num : ∀ ρ q, ev ρ (.num q) = (q.val : ℝ)
  ev_pow : ∀ ρ b e, ev ρ (.pow b e) = ev ρ b ^ ev ρ e

section generic
variable (S : Sem) (ρ : EnvR)

/-- Value of a monomial. -/
def evalM (m : Mono) : ℝ := (m.coeff.val : ℝ) * (m.key.map (S.ev ρ)).prod
/-- Value of a polynomial. -/
def evalP : Poly → ℝ
  | [] => 0
  | m :: ms => evalM S ρ m + evalP ms

@[simp] theorem evalP_nil : evalP S ρ [] = 0 := rfl
@[simp] theorem evalP_cons (m : Mono) (ms : Poly) : evalP S ρ (m :: ms) = evalM S ρ m + evalP S ρ ms := rfl

theorem evalP_append (p q : Poly) : evalP S ρ (p ++ q) = evalP S ρ p + evalP S ρ q := by
  induction p with
  | nil => simp
  | cons m ms ih => simp [ih, add_assoc]

theorem ev_mulN (l : List Expr) : S.ev ρ (Expr.mulN l) = (l.map (S.ev ρ)).prod := by
  cases l with
  | nil => simp [Expr.mulN, S.ev_mul]
  | cons a as => cases as <;> simp [Expr.mulN, S.ev_mul]

theorem ev_Mono_eval (m : Mono) : S.ev ρ m.eval = evalM S ρ m := by
  simp only [Mono.eval, evalM]
  split
  · rename_i h; simp [List.isEmpty_iff.mp h, S.ev_num]
  · split
    · rename_i h; have h1 : m.coeff.val = 1 := by simpa [Q.isOne] using h
      rw [ev_mulN]; simp [h1]
    · simp [S.ev_mul, S.ev_num]

theorem prod_factors (e : Expr) : ((factors e).map (S.ev ρ)).prod = S.ev ρ e := by
  cases e <;> simp [factors, S.ev_mul]

theorem sum_summands (e : Expr) : ((summands e).map (S.ev ρ)).sum = S.ev ρ e := by
  cases e <;> simp [summands, S.ev_add]

theorem numProduct_val : ∀ (nums : List Expr) (c : Q), (∀ f ∈ nums, isNum f = true) →
    ((numProduct nums c).val : ℝ) = (c.val : ℝ) * (nums.map (S.ev ρ)).prod
  | [], c, _ => by simp [numProduct]
  | f :: fs, c, h => by
    have hf := h f (by simp)
    cases f with
    | num q =>
      simp only [numProduct, List.map_cons, List.prod_cons, S.ev_num]
      rw [numProduct_val fs (c * q) (fun g hg => h g (by simp [hg])), Q_val_mul]
      push_cast; ring
    | _ => simp [isNum] at hf

theorem evalM_ofFactors (fs : List Expr) : evalM S ρ (Mono.ofFactors fs) = (fs.map (S.ev ρ)).prod := by
  simp only [Mono.ofFactors, evalM]
  rw [numProduct_val S ρ _ Q.one (fun f hf => (List.mem_filter.mp hf).2)]
  rw [((List.mergeSort_perm _ _).map (S.ev ρ)).prod_eq]
  have hp := List.filter_append_perm isNum fs
  have hp' : (fs.filter isNum ++ fs.filter (fun f => !isNum f)).Perm fs := by
    simpa [Function.comp_def] using hp
  rw [← (hp'.map (S.ev ρ)).prod_eq, List.map_append, List.prod_append]
  simp [Q_val_one]

theorem evalM_mul (a b : Mono) : evalM S ρ (Mono.mul a b) = evalM S ρ a * evalM S ρ b := by
  simp only [Mono.mul, evalM]
  rw [((List.mergeSort_perm _ _).map (S.ev ρ)).prod_eq, List.map_append, List.prod_append, Q_val_mul]
  push_cast; ring

theorem evalP_insertMono (m : Mono) : ∀ (p : Poly), evalP S ρ (insertMono m p) = evalM S ρ m + evalP S ρ p
  | [] => by simp [insertMono]
  | n :: ns => by
    simp only [insertMono]
    split
    · rename_i h
      have hk := Expr.beqList_eq _ _ h
      simp only [evalP_cons, evalM, hk, Q_val_add]
      push_cast; ring
    · simp only [evalP_cons, evalP_insertMono m ns]; ring

theorem evalP_foldl_insert (ms : List Mono) : ∀ (acc : Poly),
    evalP S ρ (ms.foldl (fun acc m => insertMono m acc) acc) = evalP S ρ acc + evalP S ρ ms := by
  induction ms with
  | nil => intro acc; simp
  | cons m ms ih => intro acc; simp only [List.foldl_cons, evalP_cons]; rw [ih, evalP_insertMono]; ring

theorem evalP_collect (ms : List Mono) : evalP S ρ (collect ms) = evalP S ρ ms := by
  simp [collect, evalP_foldl_insert]

theorem evalP_map_mul (a : Mono) (q : Poly) : evalP S ρ (q.map (Mono.mul a)) = evalM S ρ a * evalP S ρ q := by
  induction q with
  | nil => simp
  | cons b bs ih => simp [evalM_mul, ih, mul_add]

theorem evalP_flatMap_mul (p q : Poly) :
    evalP S ρ (p.flatMap fun a => q.map (Mono.mul a)) = evalP S ρ p * evalP S ρ q := by
  induction p with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, evalP_append, evalP_map_mul, ih, add_mul]

theorem evalP_polyMul (p q : Poly) : evalP S ρ (polyMul p q) = evalP S ρ p * evalP S ρ q := by
  simp [polyMul, evalP_collect, evalP_flatMap_mul]

theorem evalP_toPoly (e : Expr) : evalP S ρ (toPoly e) = S.ev ρ e := by
  rw [← sum_summands S ρ e]
  simp only [toPoly]
  induction summands e with
  | nil => simp
  | cons t ts ih => simp [evalM_ofFactors, prod_factors, ih]

theorem ev_ofPoly (p : Poly) : S.ev ρ (ofPoly p) = evalP S ρ p := by
  simp only [ofPoly, S.ev_add, List.map_map]
  induction p with
  | nil => simp
  | cons m ms ih =>
    simp only [List.filter_cons, evalP_cons]
    split
    · simp only [List.map_cons, List.sum_cons, Function.comp_apply, ev_Mono_eval, ih]
    · rename_i h
      have hz : m.coeff.val = 0 := by simpa [Q.isZero] using h
      rw [ih]; simp [evalM, hz]

theorem evalP_foldl_polyMul (ps : List Poly) : ∀ (acc : Poly),
    evalP S ρ (ps.foldl polyMul acc) = evalP S ρ acc * (ps.map (evalP S ρ)).prod := by
  induction ps with
  | nil => intro acc; simp
  | cons p ps ih => intro acc; simp only [List.foldl_cons, List.map_cons, List.prod_cons]; rw [ih, evalP_polyMul]; ring

theorem ev_distMul (fs : List Expr) : S.ev ρ (distMul fs) = (fs.map (S.ev ρ)).prod := by
  simp only [distMul]
  split
  · rw [ev_ofPoly, evalP_foldl_polyMul]
    simp [evalM, evalP_toPoly, List.map_map, Function.comp_def, Q_val_one]
  · exact S.ev_mul ρ fs

theorem ev_powCopies (b e : Expr) : S.ev ρ (powCopies b e) = S.ev ρ (.pow b e) := by
  unfold powCopies
  split
  · rename_i ts n
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hint, h2⟩, _⟩ := h
      rw [ev_distMul, List.map_replicate, List.prod_replicate, S.ev_pow, S.ev_num, Q_cast_isInt hint]
      have hk : ((n.val.num : ℤ) : ℝ) = ((n.val.num.toNat : ℕ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [hk, Real.rpow_natCast]
    · rfl
  · rfl

end generic

/-! ## `evalR` -/

theorem sumR_eq_sum (ρ : EnvR) (es : List Expr) : sumR ρ es = (es.map (evalR ρ)).sum := by
  induction es with
  | nil => simp
  | cons f fs ih => simp [ih]

theorem prodR_eq_prod (ρ : EnvR) (fs : List Expr) : prodR ρ fs = (fs.map (evalR ρ)).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [ih]

/-- ℝ as a `Sem`. -/
def semR : Sem where
  ev := evalR
  ev_add := fun ρ es => by rw [evalR_add, sumR_eq_sum]
  ev_mul := fun ρ es => by rw [evalR_mul, prodR_eq_prod]
  ev_num := fun _ _ => rfl
  ev_pow := fun _ _ _ => rfl

theorem evalR_distMul (ρ : EnvR) (fs : List Expr) : evalR ρ (distMul fs) = prodR ρ fs := by
  have := ev_distMul semR ρ fs; simp only [semR] at this; rw [this, prodR_eq_prod]

theorem evalR_powCopies (ρ : EnvR) (b e : Expr) : evalR ρ (powCopies b e) = evalR ρ (.pow b e) :=
  ev_powCopies semR ρ b e

mutual
  /-- **`expand` is sound over ℝ**: distribution never changes the value. -/
  theorem dist_sound (ρ : EnvR) : ∀ e : Expr, evalR ρ (Expand.dist e) = evalR ρ e
    | .num _ => rfl
    | .var _ => rfl
    | .add es => by simp only [Expand.dist, evalR_add]; exact (distList_sound ρ es).1
    | .mul es => by simp only [Expand.dist]; rw [evalR_distMul, evalR_mul]; exact (distList_sound ρ es).2
    | .pow b e => by simp only [Expand.dist]; rw [evalR_powCopies, evalR_pow, evalR_pow, dist_sound ρ b, dist_sound ρ e]
    | .fn f es => by
      have h := (distList_sound ρ es).1
      simp only [Expand.dist]
      match es, h with
      | [], _ => rfl
      | [a], h => simp only [distList, sumR_cons, sumR_nil, add_zero] at h; simp only [distList, evalR_fn₁, h]
      | _ :: _ :: _, _ => rfl
    | .matrix _ => rfl
  theorem distList_sound (ρ : EnvR) : ∀ es : List Expr,
      sumR ρ (distList es) = sumR ρ es ∧ prodR ρ (distList es) = prodR ρ es
    | [] => ⟨rfl, rfl⟩
    | e :: es => by
      obtain ⟨hs, hp⟩ := distList_sound ρ es
      simp only [distList, sumR_cons, prodR_cons, dist_sound ρ e, hs, hp]; exact ⟨trivial, trivial⟩
end

end MathProofs
end
