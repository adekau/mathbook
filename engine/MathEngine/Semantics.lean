import MathEngine.Expr
/-!
# Denotational semantics (integer fragment, total)

`evalZ ρ e` gives the value of `e` in environment `ρ`. Nodes outside the fragment (non-integer
numerals, functions, matrices, non-natural exponents) evaluate to a junk value `0`, the same
convention Lean itself uses for `x / 0`. Junk-value semantics keeps every proof a plain
structural induction; M3 replaces `Int` with `ℝ` and the fragment with the full language.
-/
namespace MathEngine
open Expr

abbrev Env := String → Int

/-- The integer a numeral denotes, or `none` outside the fragment. -/
def Q.asInt? (q : Q) : Option Int := if q.val.den = 1 then some q.val.num else none

def Expr.asNat : Expr → Nat
  | .num q => ((q.asInt?).map Int.toNat).getD 0
  | _ => 0

mutual
  def evalZ (ρ : Env) : Expr → Int
    | .num q      => (q.asInt?).getD 0
    | .var x      => ρ x
    | .add es     => evalSum ρ es
    | .mul es     => evalProd ρ es
    | .pow b e    => (evalZ ρ b) ^ e.asNat
    | .fn _ _     => 0
    | .matrix _   => 0
  def evalSum (ρ : Env) : List Expr → Int
    | []      => 0
    | e :: es => evalZ ρ e + evalSum ρ es
  def evalProd (ρ : Env) : List Expr → Int
    | []      => 1
    | e :: es => evalZ ρ e * evalProd ρ es
end

/-- Semantic equality on the fragment: agreement in every environment. -/
def SemEq (a b : Expr) : Prop := ∀ ρ, evalZ ρ a = evalZ ρ b

end MathEngine

/-!
## Partial semantics: the integer fragment as an `Option`

`evalZ` is total with junk values, which is what the spike's proof needed but makes constant
folding unsound to *state*: `1/2 + 1/2` folds to `1`, yet `evalZ` gives `0 + 0 ≠ 1`. `eval?`
returns `none` outside the fragment (non-integer numerals, functions, matrices, negative
exponents). Soundness of a rewrite `e ⟶ e'` is then *definedness-preserving
equality*: whenever `e` has a value, `e'` has the same one. A rewrite may become more defined
(`sin x · 0 ⟶ 0`) but never less. M3 refines this with ℝ-valued semantics in `proofs/`.
-/
namespace MathEngine
open Expr

mutual
  def eval? (ρ : Env) : Expr → Option Int
    | .num q => q.asInt?
    | .var x => some (ρ x)
    | .add es => evalSum? ρ es
    | .mul es => evalProd? ρ es
    | .pow b e => do let v ← eval? ρ b; let n ← eval? ρ e; if 0 ≤ n then some (v ^ n.toNat) else none
    | .fn _ _ => none
    | .matrix _ => none
  def evalSum? (ρ : Env) : List Expr → Option Int
    | [] => some 0
    | e :: es => do let v ← eval? ρ e; let s ← evalSum? ρ es; some (v + s)
  def evalProd? (ρ : Env) : List Expr → Option Int
    | [] => some 1
    | e :: es => do let v ← eval? ρ e; let p ← evalProd? ρ es; some (v * p)
end

/-- `e ⟶ e'` is sound on the integer fragment: every value of `e` is a value of `e'`. -/
def Refines (e e' : Expr) : Prop := ∀ ρ v, eval? ρ e = some v → eval? ρ e' = some v

theorem Refines.refl (e : Expr) : Refines e e := fun _ _ h => h
theorem Refines.trans {a b c : Expr} (h₁ : Refines a b) (h₂ : Refines b c) : Refines a c :=
  fun ρ v h => h₂ ρ v (h₁ ρ v h)

/-- Elementwise refinement of argument lists. -/
def RefinesList : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => Refines a b ∧ RefinesList as bs
  | _, _ => False

theorem evalSum?_refines (ρ : Env) : ∀ {as bs : List Expr}, RefinesList as bs →
    ∀ v, evalSum? ρ as = some v → evalSum? ρ bs = some v
  | [], [], _, v, h => h
  | a :: as, b :: bs, ⟨hab, hrest⟩, v, h => by
    simp only [evalSum?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨x, hx, s, hs, rfl⟩ := h
    exact ⟨x, hab ρ x hx, s, evalSum?_refines ρ hrest s hs, rfl⟩

theorem evalProd?_refines (ρ : Env) : ∀ {as bs : List Expr}, RefinesList as bs →
    ∀ v, evalProd? ρ as = some v → evalProd? ρ bs = some v
  | [], [], _, v, h => h
  | a :: as, b :: bs, ⟨hab, hrest⟩, v, h => by
    simp only [evalProd?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨x, hx, s, hs, rfl⟩ := h
    exact ⟨x, hab ρ x hx, s, evalProd?_refines ρ hrest s hs, rfl⟩

theorem RefinesList_length : ∀ {as bs : List Expr}, RefinesList as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, ⟨_, h⟩ => by simp [RefinesList_length h]

theorem RefinesList_flatten_regroup (rows : List (List Expr)) (cs : List Expr)
    (h : RefinesList rows.flatten cs) : RefinesList rows.flatten (regroup rows cs).flatten := by
  rw [flatten_regroup rows cs (RefinesList_length h).symm]; exact h

/-- Refinement is a congruence: refine the children, refine the node. -/
theorem Refines.congr (e : Expr) (cs : List Expr) (h : RefinesList (children e) cs) :
    Refines e (withChildren e cs) := by
  intro ρ v hv
  cases e with
  | num q => simpa [withChildren] using hv
  | var x => simpa [withChildren] using hv
  | add es => exact evalSum?_refines ρ h v hv
  | mul es => exact evalProd?_refines ρ h v hv
  | fn f es => simp [eval?] at hv
  | matrix rows => simp [eval?] at hv
  | pow b x =>
    match cs, h with
    | [b', x'], ⟨hb, hx, _⟩ =>
      simp only [withChildren, eval?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv ⊢
      obtain ⟨vb, hvb, n, hn, hrest⟩ := hv
      exact ⟨vb, hb ρ vb hvb, n, hx ρ n hn, hrest⟩

/-- Sums and products do not care about the order of their arguments. -/
theorem evalSum?_perm (ρ : Env) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : evalSum? ρ l₁ = evalSum? ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [evalSum?, ih]
  | swap x y l =>
    simp only [evalSum?, Option.bind_eq_bind]
    cases eval? ρ x <;> cases eval? ρ y <;> cases evalSum? ρ l <;> simp <;> omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalProd?_perm (ρ : Env) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : evalProd? ρ l₁ = evalProd? ρ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [evalProd?, ih]
  | swap x y l =>
    simp only [evalProd?, Option.bind_eq_bind]
    cases eval? ρ x <;> cases eval? ρ y <;> cases evalProd? ρ l <;> simp [Int.mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalSum?_append (ρ : Env) (l₁ l₂ : List Expr) :
    evalSum? ρ (l₁ ++ l₂) = (do let a ← evalSum? ρ l₁; let b ← evalSum? ρ l₂; some (a + b)) := by
  induction l₁ with
  | nil => simp [evalSum?]
  | cons e es ih =>
    simp only [List.cons_append, evalSum?, ih, Option.bind_eq_bind]
    cases eval? ρ e <;> cases evalSum? ρ es <;> cases evalSum? ρ l₂ <;> simp <;> omega

theorem evalProd?_append (ρ : Env) (l₁ l₂ : List Expr) :
    evalProd? ρ (l₁ ++ l₂) = (do let a ← evalProd? ρ l₁; let b ← evalProd? ρ l₂; some (a * b)) := by
  induction l₁ with
  | nil => simp [evalProd?]
  | cons e es ih =>
    simp only [List.cons_append, evalProd?, ih, Option.bind_eq_bind]
    cases eval? ρ e <;> cases evalProd? ρ es <;> cases evalProd? ρ l₂ <;> simp [Int.mul_assoc]

end MathEngine
