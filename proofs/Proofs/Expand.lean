import Proofs.SimpReal
/-!
# `expand` is sound over ℝ

`Expand.dist` (engine, `ExpandRules.lean`) multiplies out products and powers of sums, collecting
like monomials as it goes. It is a total function rather than a rewrite system, so its soundness
is one structural induction: every intermediate — a monomial, a polynomial, the product of two
polynomials — has the value it should. Nothing here is conditional: distribution holds in every
commutative ring.
-/
noncomputable section
namespace MathProofs
open MathEngine
open MathEngine.Expr
open MathEngine.Expand

variable (ρ : EnvR)

/-- Value of a monomial. -/
def evalM (m : Mono) : ℝ := (m.coeff.val : ℝ) * prodR ρ m.key
/-- Value of a polynomial. -/
def evalP : Poly → ℝ
  | [] => 0
  | m :: ms => evalM ρ m + evalP ms

@[simp] theorem evalP_nil : evalP ρ [] = 0 := rfl
@[simp] theorem evalP_cons (m : Mono) (ms : Poly) : evalP ρ (m :: ms) = evalM ρ m + evalP ρ ms := rfl

theorem evalP_append (p q : Poly) : evalP ρ (p ++ q) = evalP ρ p + evalP ρ q := by
  induction p with
  | nil => simp
  | cons m ms ih => simp [ih, add_assoc]

theorem evalR_Mono_eval (m : Mono) : evalR ρ m.eval = evalM ρ m := by
  simp only [Mono.eval, evalM]
  split
  · rename_i h; simp [List.isEmpty_iff.mp h]
  · split
    · rename_i h; have h1 : m.coeff.val = 1 := by simpa [Q.isOne] using h
      rw [evalR_mulN]; simp [h1]
    · simp

theorem prodR_factors (e : Expr) : prodR ρ (factors e) = evalR ρ e := by
  cases e <;> simp [factors]

theorem sumR_summands (e : Expr) : sumR ρ (summands e) = evalR ρ e := by
  cases e <;> simp [summands]

/-- The coefficient fold over numerals is their product. -/
theorem numProduct_val : ∀ (nums : List Expr) (c : Q), (∀ f ∈ nums, isNum f = true) →
    ((numProduct nums c).val : ℝ) = (c.val : ℝ) * prodR ρ nums
  | [], c, _ => by simp [numProduct]
  | f :: fs, c, h => by
    have hf := h f (by simp)
    cases f with
    | num q =>
      simp only [numProduct, prodR_cons, evalR_num]
      rw [numProduct_val fs (c * q) (fun g hg => h g (by simp [hg])), Q_val_mul]
      push_cast; ring
    | _ => simp [isNum] at hf

theorem evalM_ofFactors (fs : List Expr) : evalM ρ (Mono.ofFactors fs) = prodR ρ fs := by
  simp only [Mono.ofFactors, evalM]
  rw [numProduct_val ρ _ Q.one (fun f hf => (List.mem_filter.mp hf).2)]
  rw [prodR_perm ρ (List.mergeSort_perm _ _)]
  have hp := List.filter_append_perm isNum fs
  have hp' : (fs.filter isNum ++ fs.filter (fun f => !isNum f)).Perm fs := by
    simpa [Function.comp_def] using hp
  rw [← prodR_perm ρ hp', prodR_append]
  simp [Q_val_one]

theorem evalM_mul (a b : Mono) : evalM ρ (Mono.mul a b) = evalM ρ a * evalM ρ b := by
  simp only [Mono.mul, evalM]
  rw [prodR_perm ρ (List.mergeSort_perm _ _), prodR_append, Q_val_mul]
  push_cast; ring

theorem evalP_insertMono (m : Mono) : ∀ (p : Poly), evalP ρ (insertMono m p) = evalM ρ m + evalP ρ p
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
    evalP ρ (ms.foldl (fun acc m => insertMono m acc) acc) = evalP ρ acc + evalP ρ ms := by
  induction ms with
  | nil => intro acc; simp
  | cons m ms ih => intro acc; simp only [List.foldl_cons, evalP_cons]; rw [ih, evalP_insertMono]; ring

theorem evalP_collect (ms : List Mono) : evalP ρ (collect ms) = evalP ρ ms := by
  simp [collect, evalP_foldl_insert]

theorem evalP_map_mul (a : Mono) (q : Poly) : evalP ρ (q.map (Mono.mul a)) = evalM ρ a * evalP ρ q := by
  induction q with
  | nil => simp
  | cons b bs ih => simp [evalM_mul, ih, mul_add]

theorem evalP_flatMap_mul (p q : Poly) : evalP ρ (p.flatMap fun a => q.map (Mono.mul a)) = evalP ρ p * evalP ρ q := by
  induction p with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, evalP_append, evalP_map_mul, ih, add_mul]

theorem evalP_polyMul (p q : Poly) : evalP ρ (polyMul p q) = evalP ρ p * evalP ρ q := by
  simp [polyMul, evalP_collect, evalP_flatMap_mul]

theorem evalP_toPoly (e : Expr) : evalP ρ (toPoly e) = evalR ρ e := by
  rw [← sumR_summands ρ e]
  simp only [toPoly]
  induction summands e with
  | nil => simp
  | cons t ts ih => simp [evalM_ofFactors, prodR_factors, ih]

theorem evalR_ofPoly (p : Poly) : evalR ρ (ofPoly p) = evalP ρ p := by
  simp only [ofPoly, evalR_add]
  induction p with
  | nil => simp
  | cons m ms ih =>
    simp only [List.filter_cons, evalP_cons]
    split
    · simp [evalR_Mono_eval, ih]
    · rename_i h
      have hz : m.coeff.val = 0 := by simpa [Q.isZero] using h
      simp [evalM, hz, ih]

theorem evalP_foldl_polyMul (ps : List Poly) : ∀ (acc : Poly),
    evalP ρ (ps.foldl polyMul acc) = evalP ρ acc * (ps.map (evalP ρ)).prod := by
  induction ps with
  | nil => intro acc; simp
  | cons p ps ih => intro acc; simp only [List.foldl_cons, List.map_cons, List.prod_cons]; rw [ih, evalP_polyMul]; ring

theorem prodR_eq_prod (fs : List Expr) : prodR ρ fs = (fs.map (evalR ρ)).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [ih]

theorem evalR_distMul (fs : List Expr) : evalR ρ (distMul fs) = prodR ρ fs := by
  simp only [distMul]
  split
  · rw [evalR_ofPoly, evalP_foldl_polyMul, prodR_eq_prod]
    simp [evalM, evalP_toPoly, List.map_map, Function.comp_def, Q_val_one]
  · rfl

theorem prodR_replicate (b : Expr) : ∀ k : ℕ, prodR ρ (List.replicate k b) = evalR ρ b ^ k
  | 0 => by simp
  | k + 1 => by simp [List.replicate_succ, prodR_replicate b k, pow_succ]; ring

theorem evalR_powCopies (b e : Expr) : evalR ρ (powCopies b e) = evalR ρ (.pow b e) := by
  unfold powCopies
  split
  · rename_i ts n
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hint, h2⟩, _⟩ := h
      rw [evalR_distMul, prodR_replicate, evalR_pow, evalR_num, Q_cast_isInt hint]
      have hk : ((n.val.num : ℤ) : ℝ) = ((n.val.num.toNat : ℕ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [hk, Real.rpow_natCast]
    · rfl
  · rfl

mutual
  /-- **`expand` is sound**: distribution never changes the value. -/
  theorem dist_sound : ∀ e : Expr, evalR ρ (Expand.dist e) = evalR ρ e
    | .num _ => rfl
    | .var _ => rfl
    | .add es => by simp only [Expand.dist, evalR_add]; exact (distList_sound es).1
    | .mul es => by simp only [Expand.dist]; rw [evalR_distMul, evalR_mul]; exact (distList_sound es).2
    | .pow b e => by simp only [Expand.dist]; rw [evalR_powCopies, evalR_pow, evalR_pow, dist_sound b, dist_sound e]
    | .fn f es => by
      have h := (distList_sound es).1
      simp only [Expand.dist]
      match es, h with
      | [], _ => rfl
      | [a], h => simp only [distList, sumR_cons, sumR_nil, add_zero] at h; simp only [distList, evalR_fn₁, h]
      | _ :: _ :: _, _ => rfl
    | .matrix _ => rfl
  theorem distList_sound : ∀ es : List Expr, sumR ρ (distList es) = sumR ρ es ∧ prodR ρ (distList es) = prodR ρ es
    | [] => ⟨rfl, rfl⟩
    | e :: es => by
      obtain ⟨hs, hp⟩ := distList_sound es
      simp only [distList, sumR_cons, prodR_cons, dist_sound e, hs, hp]; exact ⟨trivial, trivial⟩
end

end MathProofs
end
