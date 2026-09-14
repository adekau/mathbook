import MathEngine.Rewrite
/-!
# The pipeline ordering (M5)

`normalize` (Rewrite.lean) proves termination of the `simp.*` rules with one additive measure. The
notebook pipeline — commands, `diff.*`, `la.*`, `simp.*` and the two parity rules — cannot be
ordered that way: the product and chain rules duplicate subterms, `expand`-style commands grow
terms, and `(ab)^n → a^n b^n` duplicates `n`. This file defines the ordering the pipeline *does*
terminate under: five tiers compared lexicographically,

  `μ e = (cmdCount e, d3Count e, litCount e, M e, size e, numCount e)`

* `cmdCount` — command nodes. A command is eliminated by its rule and never re-created.
* `d3Count` — `diff` nodes of the wrong arity (`diff(f, x, n)`), eliminated by `diff.higher-order`;
  its result is a tower of ordinary `diff` nodes under which `M` explodes, hence a tier of its own.
* `litCount` — matrix literals. Every `la.*` rule turns an operation on literals into one literal.
* `M` — the bespoke measure that orders everything else, including the two rules no standard
  ordering (RPO, KBO, polynomial) can order together with `x·x → x²`:
  `M (pow b e) = (M b + 1) · M e − 1` makes a numeric exponent *multiply* its base, so distributing
  a power over a product is a loss, while `M (mul es) = 2 + Σ (M e + 2)` charges per factor, so
  merging two factors into one power is also a loss; `M (num 1) = 1` is what lets `x · x^a → x^(a+1)`
  decrease, and a non-integer numeral weighs 4 so that an irreducible root like `2^(1/2)` is heavy
  enough for `√2 + √2 → 2√2`; `M (diff f x) = 3 ^ (M f + 3)` dominates any sum of products of pieces of `f`.
* `size` — the tiebreaker for rules that only reassociate.
* `numCount` — the magnitudes of the integer numerals, for the radical rules that shrink a base.

Every rule of the pipeline decreases `μ` **when its children are already normal** (`Normal`). That
hypothesis is what the innermost strategy of the rewriter provides (`Terminate.lean`), and it is
essential: without it `diff.product` could duplicate a still-reducible command or matrix product
inside its body, and no ordering of this shape would survive.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Counting node kinds (tiers 1–3 share this)
-- ---------------------------------------------------------------------------

mutual
  /-- Sum of `own` over the tree. -/
  def count (own : Expr → Nat) : Expr → Nat
    | .num q => own (.num q)
    | .var x => own (.var x)
    | .add es => own (.add es) + countList own es
    | .mul es => own (.mul es) + countList own es
    | .pow b e => own (.pow b e) + count own b + count own e
    | .fn f es => own (.fn f es) + countList own es
    | .matrix rows => own (.matrix rows) + countRows own rows
  def countList (own : Expr → Nat) : List Expr → Nat
    | [] => 0
    | e :: es => count own e + countList own es
  def countRows (own : Expr → Nat) : List (List Expr) → Nat
    | [] => 0
    | r :: rs => countList own r + countRows own rs
end

theorem countList_append (own : Expr → Nat) (l₁ l₂ : List Expr) :
    countList own (l₁ ++ l₂) = countList own l₁ + countList own l₂ := by
  induction l₁ with
  | nil => simp [countList]
  | cons e es ih => simp [countList, ih]; omega

theorem countRows_flatten (own : Expr → Nat) (rows : List (List Expr)) :
    countRows own rows = countList own rows.flatten := by
  induction rows with
  | nil => simp [countRows, countList]
  | cons r rs ih => simp [countRows, countList_append, ih]

theorem count_eq (own : Expr → Nat) (e : Expr) : count own e = own e + countList own (children e) := by
  cases e <;> simp [count, children, countList, countRows_flatten] <;> omega

theorem countList_perm (own : Expr → Nat) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) :
    countList own l₁ = countList own l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [countList, ih]
  | swap => simp [countList]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An own-weight that only looks at the head and the number of children. -/
def HeadOnly (own : Expr → Nat) : Prop :=
  ∀ e cs, cs.length = (children e).length → own (withChildren e cs) = own e

theorem count_withChildren {own : Expr → Nat} (h : HeadOnly own) (e : Expr) (cs : List Expr)
    (hlen : cs.length = (children e).length) :
    count own (withChildren e cs) = own e + countList own cs := by
  rw [count_eq, h e cs hlen, children_withChildren e cs hlen]

theorem countList_le_count (own : Expr → Nat) (e : Expr) : countList own (children e) ≤ count own e := by
  rw [count_eq]; omega

theorem count_mem_le (own : Expr → Nat) {c : Expr} : ∀ {cs : List Expr}, c ∈ cs → count own c ≤ countList own cs
  | _ :: _, List.Mem.head _ => by simp only [countList]; omega
  | _ :: _, List.Mem.tail _ h => by simp only [countList]; have := count_mem_le own h; omega

theorem count_child_le (own : Expr → Nat) {e c : Expr} (h : c ∈ children e) : count own c ≤ count own e :=
  Nat.le_trans (count_mem_le own h) (countList_le_count own e)

theorem size_mem_le {c : Expr} : ∀ {cs : List Expr}, c ∈ cs → size c ≤ sizeList cs
  | _ :: _, List.Mem.head _ => by simp only [sizeList]; omega
  | _ :: _, List.Mem.tail _ h => by simp only [sizeList]; have := size_mem_le h; omega

theorem size_child_lt {e c : Expr} (h : c ∈ children e) : size c < size e :=
  Nat.lt_of_le_of_lt (size_mem_le h) (sizeList_children_lt e)

theorem withChildren_children' (e : Expr) : withChildren e (children e) = e := by
  cases e with
  | pow _ _ => rfl
  | matrix rows =>
    simp only [withChildren, children]
    congr
    induction rows with
    | nil => rfl
    | cons r rs ih => simp [regroup, ih]
  | _ => rfl

/-- Elementwise `≤` of a count lifts to lists. -/
theorem countList_le_of_rel (own : Expr → Nat) :
    ∀ {cs' cs : List Expr}, RelList (fun a b => count own a ≤ count own b) cs' cs →
      countList own cs' ≤ countList own cs
  | [], [], _ => Nat.le_refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by
    simp only [countList]; have := countList_le_of_rel own hs; omega

theorem countList_eq_of_rel (own : Expr → Nat) :
    ∀ {cs' cs : List Expr}, RelList (fun a b => count own a ≤ count own b) cs' cs →
      countList own cs' = countList own cs →
      RelList (fun a b => count own a = count own b) cs' cs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩, heq => by
    simp only [countList] at heq
    have := countList_le_of_rel own hs
    exact ⟨by omega, countList_eq_of_rel own hs (by omega)⟩

-- The three counting tiers.

def cmdNames : List String := ["simplify", "expand", "rref", "N", "subst", "integrate"]

def cmdOwn : Expr → Nat | .fn f _ => if cmdNames.contains f then 1 else 0 | _ => 0
def d3Own : Expr → Nat | .fn f es => if f = "diff" ∧ es.length ≠ 2 then 1 else 0 | _ => 0

theorem cmdOwn_head : HeadOnly cmdOwn := by
  intro e cs hlen; cases e with
  | pow b x => simp only [children, List.length_cons, List.length_nil] at hlen; match cs, hlen with | [_, _], _ => rfl
  | _ => rfl

theorem d3Own_head : HeadOnly d3Own := by
  intro e cs hlen; cases e with
  | fn f es => simp only [children] at hlen; simp [withChildren, d3Own, hlen]
  | pow b x => simp only [children, List.length_cons, List.length_nil] at hlen; match cs, hlen with | [_, _], _ => rfl
  | _ => rfl

mutual
  /-- Is there a matrix literal at or below `e`? -/
  def hasLit : Expr → Bool
    | .num _ | .var _ => false
    | .add es | .mul es | .fn _ es => hasLitList es
    | .pow b e => hasLit b || hasLit e
    | .matrix _ => true
  def hasLitList : List Expr → Bool
    | [] => false
    | e :: es => hasLit e || hasLitList es
end

theorem hasLitList_append (l₁ l₂ : List Expr) : hasLitList (l₁ ++ l₂) = (hasLitList l₁ || hasLitList l₂) := by
  induction l₁ with
  | nil => simp [hasLitList]
  | cons e es ih => simp [hasLitList, ih, Bool.or_assoc]

theorem hasLitList_flatten (rows : List (List Expr)) : hasLitList rows.flatten = rows.any hasLitList := by
  induction rows with
  | nil => simp [hasLitList]
  | cons r rs ih => simp [hasLitList_append, ih]

theorem hasLitList_iff (es : List Expr) : hasLitList es = true ↔ ∃ e ∈ es, hasLit e = true := by
  induction es with
  | nil => simp [hasLitList]
  | cons e es ih => simp [hasLitList, ih]

/-- The literal tier counts nodes that sit on a path to a literal: `hasLit` of a non-literal node
depends on its children, so this own-weight is not head-only, but it is monotone. -/
def litOwn (e : Expr) : Nat := if hasLit e then 1 else 0

theorem hasLit_withChildren (e : Expr) (cs : List Expr) (hlen : cs.length = (children e).length) :
    hasLit (withChildren e cs) = (isMatrix e || hasLitList cs) := by
  cases e with
  | num _ | var _ => simp only [children, List.length_nil] at hlen; match cs, hlen with | [], _ => rfl
  | add _ | mul _ | fn _ _ => rfl
  | pow b x =>
    simp only [children, List.length_cons, List.length_nil] at hlen
    match cs, hlen with | [b', x'], _ => simp [withChildren, hasLit, hasLitList, isMatrix]
  | matrix rows => simp [withChildren, hasLit, isMatrix]

theorem countList_pos_exists (own : Expr → Nat) : ∀ {cs : List Expr}, 0 < countList own cs → ∃ c ∈ cs, 0 < count own c
  | [], h => by simp [countList] at h
  | c :: cs, h => by
    simp only [countList] at h
    by_cases hc : 0 < count own c
    · exact ⟨c, List.mem_cons_self, hc⟩
    · obtain ⟨d, hd, hpos⟩ := countList_pos_exists own (cs := cs) (by omega)
      exact ⟨d, List.mem_cons_of_mem _ hd, hpos⟩

theorem hasLit_of_count_pos_aux : ∀ n, ∀ e : Expr, size e ≤ n → 0 < count litOwn e → hasLit e = true := by
  intro n
  induction n with
  | zero => intro e hs; have := size_pos e; omega
  | succ n ih =>
    intro e hs h
    by_cases hl : hasLit e = true
    · exact hl
    · have hown : litOwn e = 0 := by simp [litOwn, hl]
      rw [count_eq, hown, Nat.zero_add] at h
      obtain ⟨c, hc, hpos⟩ := countList_pos_exists litOwn h
      have hlc := ih c (by have := size_child_lt hc; omega) hpos
      exfalso; apply hl
      have := hasLit_withChildren e (children e) rfl
      rw [withChildren_children'] at this
      rw [this, Bool.or_eq_true, hasLitList_iff]; exact Or.inr ⟨c, hc, hlc⟩

theorem hasLit_of_count_pos {e : Expr} (h : 0 < count litOwn e) : hasLit e = true :=
  hasLit_of_count_pos_aux (size e) e (Nat.le_refl _) h

/-- Tier 6: the magnitude of every integer numeral. Non-integers weigh nothing here, so a rule
that shrinks a radical's base (`8^(1/2) → 2^(3/2)`) decreases it while `M` and `size` stay put. -/
def numOwn : Expr → Nat
  | .num q => if q.isInt then q.val.num.natAbs else 0
  | _ => 0

theorem numOwn_head : HeadOnly numOwn := by
  intro e cs hlen; cases e with
  | pow b x => simp only [children, List.length_cons, List.length_nil] at hlen; match cs, hlen with | [_, _], _ => rfl
  | _ => rfl

abbrev cmdCount := count cmdOwn
abbrev d3Count := count d3Own
abbrev litCount := count litOwn
abbrev numCount := count numOwn

-- ---------------------------------------------------------------------------
-- Tier 4: the bespoke measure M
-- ---------------------------------------------------------------------------

mutual
  def M : Expr → Nat
    | .num q => if q.isOne then 1 else if q.isInt then 2 else 4
    | .var _ => 10
    | .add es => ML es + (if es.isEmpty then 3 else 0)
    | .mul es => 2 + ML es + 2 * es.length
    | .pow b e => (M b + 1) * M e - 1
    | .fn "diff" [g, t] => 3 ^ (M g + 3) + M t
    | .fn _ es => 5 * ML es + 10
    | .matrix rows => 10 + MR rows
  def ML : List Expr → Nat
    | [] => 0
    | e :: es => M e + ML es
  def MR : List (List Expr) → Nat
    | [] => 0
    | r :: rs => ML r + MR rs
end

theorem M.num (q : Q) : M (.num q) = if q.isOne then 1 else if q.isInt then 2 else 4 := by simp [M]
theorem M.var (x : String) : M (.var x) = 10 := by simp [M]
theorem M.add_nil : M (.add []) = 3 := by simp [M, ML]
theorem M.add_cons (e : Expr) (es : List Expr) : M (.add (e :: es)) = M e + ML es := by simp [M, ML]
theorem M.mul (es : List Expr) : M (.mul es) = 2 + ML es + 2 * es.length := by simp [M]
theorem M.pow (b e : Expr) : M (.pow b e) = (M b + 1) * M e - 1 := by simp [M]
theorem M.diff (g t : Expr) : M (.fn "diff" [g, t]) = 3 ^ (M g + 3) + M t := by simp [M]
theorem M.matrix (rows : List (List Expr)) : M (.matrix rows) = 10 + MR rows := by simp [M]
theorem ML.nil : ML [] = 0 := rfl
theorem ML.cons (e : Expr) (es : List Expr) : ML (e :: es) = M e + ML es := rfl

/-- `fn` nodes other than a binary `diff`. -/
theorem M.fn (f : String) (es : List Expr) (h : ¬ (f = "diff" ∧ es.length = 2)) :
    M (.fn f es) = 5 * ML es + 10 := by
  match f, es with
  | "diff", [g, t] => exact absurd ⟨rfl, rfl⟩ h
  | "diff", [] => rfl
  | "diff", [_] => rfl
  | "diff", _ :: _ :: _ :: _ => rfl
  | f, es =>
    unfold M
    split
    all_goals rename_i heq
    all_goals first
      | (simp only [reduceCtorEq] at heq; done)
      | (obtain ⟨rfl, rfl⟩ := Expr.fn.inj heq; first | rfl | exact absurd ⟨rfl, rfl⟩ h)

theorem ML.append (l₁ l₂ : List Expr) : ML (l₁ ++ l₂) = ML l₁ + ML l₂ := by
  induction l₁ with
  | nil => simp [ML]
  | cons e es ih => simp [ML, ih]; omega

theorem MR.flatten (rows : List (List Expr)) : MR rows = ML rows.flatten := by
  induction rows with
  | nil => simp [MR, ML]
  | cons r rs ih => simp [MR, ML.append, ih]

theorem ML.perm {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : ML l₁ = ML l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ML, ih]
  | swap => simp [ML]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ML.mem_le {c : Expr} : ∀ {cs : List Expr}, c ∈ cs → M c ≤ ML cs
  | _ :: _, List.Mem.head _ => by simp only [ML]; omega
  | _ :: _, List.Mem.tail _ h => by simp only [ML]; have := ML.mem_le h; omega

mutual
  theorem M.pos : ∀ e : Expr, 1 ≤ M e
    | .num q => by rw [M.num]; split <;> (try split) <;> omega
    | .var _ => by rw [M.var]; omega
    | .add es => by
      cases es with
      | nil => rw [M.add_nil]; omega
      | cons e es' => rw [M.add_cons]; have := M.pos e; omega
    | .mul _ => by rw [M.mul]; omega
    | .pow b e => by
      rw [M.pow]; have hb := M.pos b; have he := M.pos e
      have : (M b + 1) * M e ≥ 2 * 1 := Nat.mul_le_mul (by omega) he
      omega
    | .fn f es => by
      by_cases hd : f = "diff" ∧ es.length = 2
      · obtain ⟨rfl, hl⟩ := hd
        match es, hl with
        | [g, t], _ => rw [M.diff]; exact Nat.le_trans (M.pos t) (Nat.le_add_left _ _)
      · rw [M.fn f es hd]; omega
    | .matrix _ => by rw [M.matrix]; omega
end

/-- Children weigh no more than the node. -/
theorem M.child_le {e c : Expr} (h : c ∈ children e) : M c ≤ M e := by
  cases e with
  | num _ | var _ => simp [children] at h
  | add es =>
    simp only [children] at h
    cases es with
    | nil => simp at h
    | cons e' es' => simp only [M.add_cons]; have := ML.mem_le h; simp only [ML] at this; omega
  | mul es => simp only [children] at h; rw [M.mul]; have := ML.mem_le h; omega
  | pow b x =>
    simp only [children, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rw [M.pow]; have hb := M.pos b; have hx := M.pos x
    rcases h with rfl | rfl
    · have : (M c + 1) * M x ≥ (M c + 1) * 1 := Nat.mul_le_mul_left _ hx; omega
    · have : (M b + 1) * M c ≥ 2 * M c := Nat.mul_le_mul_right _ (by omega); omega
  | fn f es =>
    simp only [children] at h
    by_cases hd : f = "diff" ∧ es.length = 2
    · obtain ⟨rfl, hl⟩ := hd
      match es, hl, h with
      | [g, t], _, h =>
        rw [M.diff]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        have h1 := Nat.lt_pow_self (n := M g) (a := 3) (by decide)
        have h2 : 3 ^ M g ≤ 3 ^ (M g + 3) := Nat.pow_le_pow_right (by decide) (by omega)
        rcases h with rfl | rfl <;> omega
    · rw [M.fn f es hd]; have := ML.mem_le h; omega
  | matrix rows =>
    simp only [children] at h
    rw [M.matrix, MR.flatten]; have := ML.mem_le h; omega

-- ---------------------------------------------------------------------------
-- The tuple and its order
-- ---------------------------------------------------------------------------

/-- The six tiers. -/
abbrev Mu := Nat × Nat × Nat × Nat × Nat × Nat
def μ (e : Expr) : Mu := (cmdCount e, d3Count e, litCount e, M e, size e, numCount e)

/-- Lexicographic order on the tiers. -/
def MuLt (a b : Mu) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))) a b

def MuLe (a b : Mu) : Prop := MuLt a b ∨ a = b

theorem MuLt_wf : WellFounded MuLt :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))))).wf

/-- Build a lexicographic decrease tier by tier: each tier is `≤`, and the first strict one wins. -/
theorem muLt_of {a₁ b₁ c₁ d₁ s₁ n₁ a₂ b₂ c₂ d₂ s₂ n₂ : Nat}
    (ha : a₁ ≤ a₂) (hb : a₁ = a₂ → b₁ ≤ b₂) (hc : a₁ = a₂ → b₁ = b₂ → c₁ ≤ c₂)
    (hd : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ ≤ d₂)
    (hs : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ ≤ s₂)
    (hn : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ = s₂ → n₁ < n₂) :
    MuLt (a₁, b₁, c₁, d₁, s₁, n₁) (a₂, b₂, c₂, d₂, s₂, n₂) := by
  unfold MuLt
  rcases Nat.lt_or_eq_of_le ha with h | rfl
  · exact Prod.Lex.left _ _ h
  apply Prod.Lex.right
  rcases Nat.lt_or_eq_of_le (hb rfl) with h | rfl
  · exact Prod.Lex.left _ _ h
  apply Prod.Lex.right
  rcases Nat.lt_or_eq_of_le (hc rfl rfl) with h | rfl
  · exact Prod.Lex.left _ _ h
  apply Prod.Lex.right
  rcases Nat.lt_or_eq_of_le (hd rfl rfl rfl) with h | rfl
  · exact Prod.Lex.left _ _ h
  apply Prod.Lex.right
  rcases Nat.lt_or_eq_of_le (hs rfl rfl rfl rfl) with h | rfl
  · exact Prod.Lex.left _ _ h
  exact Prod.Lex.right _ (hn rfl rfl rfl rfl rfl)

theorem muLe_of {a₁ b₁ c₁ d₁ s₁ n₁ a₂ b₂ c₂ d₂ s₂ n₂ : Nat}
    (ha : a₁ ≤ a₂) (hb : a₁ = a₂ → b₁ ≤ b₂) (hc : a₁ = a₂ → b₁ = b₂ → c₁ ≤ c₂)
    (hd : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ ≤ d₂)
    (hs : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ ≤ s₂)
    (hn : a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ = s₂ → n₁ ≤ n₂) :
    MuLe (a₁, b₁, c₁, d₁, s₁, n₁) (a₂, b₂, c₂, d₂, s₂, n₂) := by
  by_cases h : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ ∧ s₁ = s₂ ∧ n₁ = n₂
  · right; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl
  · left
    apply muLt_of ha hb hc hd hs
    intro h1 h2 h3 h4 h5
    have := hn h1 h2 h3 h4 h5
    rcases Nat.lt_or_eq_of_le this with h' | h'
    · exact h'
    · exact absurd ⟨h1, h2, h3, h4, h5, h'⟩ h

/-- Reading a lexicographic decrease back, tier by tier. -/
theorem MuLt.elim {a₁ b₁ c₁ d₁ s₁ n₁ a₂ b₂ c₂ d₂ s₂ n₂ : Nat}
    (h : MuLt (a₁, b₁, c₁, d₁, s₁, n₁) (a₂, b₂, c₂, d₂, s₂, n₂)) :
    a₁ ≤ a₂ ∧ (a₁ = a₂ → b₁ ≤ b₂) ∧ (a₁ = a₂ → b₁ = b₂ → c₁ ≤ c₂) ∧
    (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ ≤ d₂) ∧ (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ ≤ s₂) ∧
    (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ = s₂ → n₁ < n₂) := by
  unfold MuLt at h
  cases h with
  | left _ _ h =>
    exact ⟨Nat.le_of_lt h, fun e => absurd e (Nat.ne_of_lt h), fun e => absurd e (Nat.ne_of_lt h),
      fun e => absurd e (Nat.ne_of_lt h), fun e => absurd e (Nat.ne_of_lt h), fun e => absurd e (Nat.ne_of_lt h)⟩
  | right _ h =>
    cases h with
    | left _ _ h =>
      exact ⟨Nat.le_refl _, fun _ => Nat.le_of_lt h, fun _ e => absurd e (Nat.ne_of_lt h),
        fun _ e => absurd e (Nat.ne_of_lt h), fun _ e => absurd e (Nat.ne_of_lt h), fun _ e => absurd e (Nat.ne_of_lt h)⟩
    | right _ h =>
      cases h with
      | left _ _ h =>
        exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_of_lt h,
          fun _ _ e => absurd e (Nat.ne_of_lt h), fun _ _ e => absurd e (Nat.ne_of_lt h), fun _ _ e => absurd e (Nat.ne_of_lt h)⟩
      | right _ h =>
        cases h with
        | left _ _ h =>
          exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ _ => Nat.le_of_lt h,
            fun _ _ _ e => absurd e (Nat.ne_of_lt h), fun _ _ _ e => absurd e (Nat.ne_of_lt h)⟩
        | right _ h =>
          cases h with
          | left _ _ h =>
            exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ _ => Nat.le_refl _,
              fun _ _ _ _ => Nat.le_of_lt h, fun _ _ _ _ e => absurd e (Nat.ne_of_lt h)⟩
          | right _ h =>
            exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ _ => Nat.le_refl _,
              fun _ _ _ _ => Nat.le_refl _, fun _ _ _ _ _ => h⟩

theorem MuLe.elim {a₁ b₁ c₁ d₁ s₁ n₁ a₂ b₂ c₂ d₂ s₂ n₂ : Nat}
    (h : MuLe (a₁, b₁, c₁, d₁, s₁, n₁) (a₂, b₂, c₂, d₂, s₂, n₂)) :
    a₁ ≤ a₂ ∧ (a₁ = a₂ → b₁ ≤ b₂) ∧ (a₁ = a₂ → b₁ = b₂ → c₁ ≤ c₂) ∧
    (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ ≤ d₂) ∧ (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ ≤ s₂) ∧
    (a₁ = a₂ → b₁ = b₂ → c₁ = c₂ → d₁ = d₂ → s₁ = s₂ → n₁ ≤ n₂) := by
  rcases h with h | h
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.elim
    exact ⟨h1, h2, h3, h4, h5, fun a b c d e => Nat.le_of_lt (h6 a b c d e)⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ _ => Nat.le_refl _,
      fun _ _ _ _ => Nat.le_refl _, fun _ _ _ _ _ => Nat.le_refl _⟩

theorem MuLt.trans_le {a b c} (h₁ : MuLt a b) (h₂ : MuLe b c) : MuLt a c := by
  rcases h₂ with h₂ | rfl
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := a; obtain ⟨b1, b2, b3, b4, b5, b6⟩ := b; obtain ⟨c1, c2, c3, c4, c5, c6⟩ := c
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h₁.elim; obtain ⟨q1, q2, q3, q4, q5, q6⟩ := h₂.elim
    apply muLt_of (Nat.le_trans p1 q1)
    · intro e; have : a1 = b1 := by omega
      have : b1 = c1 := by omega
      exact Nat.le_trans (p2 ‹_›) (q2 ‹_›)
    · intro e1 e2; have h1 : a1 = b1 := by omega
      have h1' : b1 = c1 := by omega
      have h2 : a2 = b2 := by have := p2 h1; have := q2 h1'; omega
      have h2' : b2 = c2 := by omega
      exact Nat.le_trans (p3 h1 h2) (q3 h1' h2')
    · intro e1 e2 e3; have h1 : a1 = b1 := by omega
      have h1' : b1 = c1 := by omega
      have h2 : a2 = b2 := by have := p2 h1; have := q2 h1'; omega
      have h2' : b2 = c2 := by omega
      have h3 : a3 = b3 := by have := p3 h1 h2; have := q3 h1' h2'; omega
      have h3' : b3 = c3 := by omega
      exact Nat.le_trans (p4 h1 h2 h3) (q4 h1' h2' h3')
    · intro e1 e2 e3 e4; have h1 : a1 = b1 := by omega
      have h1' : b1 = c1 := by omega
      have h2 : a2 = b2 := by have := p2 h1; have := q2 h1'; omega
      have h2' : b2 = c2 := by omega
      have h3 : a3 = b3 := by have := p3 h1 h2; have := q3 h1' h2'; omega
      have h3' : b3 = c3 := by omega
      have h4 : a4 = b4 := by have := p4 h1 h2 h3; have := q4 h1' h2' h3'; omega
      have h4' : b4 = c4 := by omega
      exact Nat.le_trans (p5 h1 h2 h3 h4) (q5 h1' h2' h3' h4')
    · intro e1 e2 e3 e4 e5; have h1 : a1 = b1 := by omega
      have h1' : b1 = c1 := by omega
      have h2 : a2 = b2 := by have := p2 h1; have := q2 h1'; omega
      have h2' : b2 = c2 := by omega
      have h3 : a3 = b3 := by have := p3 h1 h2; have := q3 h1' h2'; omega
      have h3' : b3 = c3 := by omega
      have h4 : a4 = b4 := by have := p4 h1 h2 h3; have := q4 h1' h2' h3'; omega
      have h4' : b4 = c4 := by omega
      have h5 : a5 = b5 := by have := p5 h1 h2 h3 h4; have := q5 h1' h2' h3' h4'; omega
      have h5' : b5 = c5 := by omega
      exact Nat.lt_trans (p6 h1 h2 h3 h4 h5) (q6 h1' h2' h3' h4' h5')
  · exact h₁

theorem MuLe.trans {a b c} (h₁ : MuLe a b) (h₂ : MuLe b c) : MuLe a c := by
  rcases h₁ with h₁ | rfl
  · exact Or.inl (h₁.trans_le h₂)
  · exact h₂

theorem MuLe.refl (a) : MuLe a a := Or.inr rfl

-- ---------------------------------------------------------------------------
-- μ and the tree: subterms, canonical order, rebuilding with smaller children
-- ---------------------------------------------------------------------------

theorem μ_child_lt {e c : Expr} (h : c ∈ children e) : MuLt (μ c) (μ e) :=
  muLt_of (count_child_le _ h) (fun _ => count_child_le _ h) (fun _ _ => count_child_le _ h)
    (fun _ _ _ => M.child_le h) (fun _ _ _ _ => Nat.le_of_lt (size_child_lt h))
    (fun _ _ _ _ h5 => absurd h5 (Nat.ne_of_lt (size_child_lt h)))

theorem count_canon (own : Expr → Nat) (h : HeadOnly own) (e : Expr) : count own (canon e) = count own e := by
  cases e with
  | add es =>
    have := count_withChildren h (.add es) (es.mergeSort leAdd) (by simp [children, (List.mergeSort_perm es leAdd).length_eq])
    simp only [withChildren] at this
    simp only [canon, this, count_eq (e := .add es), countList_perm own (List.mergeSort_perm es leAdd), children]
  | mul es =>
    simp only [canon]; split
    · rfl
    · have := count_withChildren h (.mul es) (es.mergeSort leMul) (by simp [children, (List.mergeSort_perm es leMul).length_eq])
      simp only [withChildren] at this
      simp only [this, count_eq (e := .mul es), countList_perm own (List.mergeSort_perm es leMul), children]
  | _ => rfl

theorem hasLit_canon (e : Expr) : hasLit (canon e) = hasLit e := by
  cases e with
  | add es => simp only [canon, hasLit]; rw [Bool.eq_iff_iff, hasLitList_iff, hasLitList_iff]; simp [(List.mergeSort_perm es leAdd).mem_iff]
  | mul es =>
    simp only [canon]; split
    · rfl
    · simp only [hasLit]; rw [Bool.eq_iff_iff, hasLitList_iff, hasLitList_iff]; simp [(List.mergeSort_perm es leMul).mem_iff]
  | _ => rfl

theorem count_canon_lit (e : Expr) : count litOwn (canon e) = count litOwn e := by
  cases e with
  | add es =>
    simp only [canon]
    rw [count_eq (e := .add _), count_eq (e := .add es), children, children, countList_perm litOwn (List.mergeSort_perm es leAdd)]
    have := hasLit_canon (.add es); simp only [canon] at this
    simp only [litOwn, this]
  | mul es =>
    simp only [canon]; split
    · rfl
    · rw [count_eq (e := .mul _), count_eq (e := .mul es), children, children, countList_perm litOwn (List.mergeSort_perm es leMul)]
      have := hasLit_canon (.mul es); simp only [canon, ‹¬ es.any isMatrix = true›, Bool.false_eq_true, ↓reduceIte] at this
      simp only [litOwn, this]
  | _ => rfl

theorem M.canon_eq (e : Expr) : M (canon e) = M e := by
  cases e with
  | add es =>
    have hp := List.mergeSort_perm es leAdd
    have h1 : (es.mergeSort leAdd).isEmpty = es.isEmpty := by
      cases es with
      | nil => simp
      | cons e es' =>
        have : es'.length + 1 = ((e :: es').mergeSort leAdd).length := by rw [hp.length_eq]; rfl
        cases hm : (e :: es').mergeSort leAdd with
        | nil => rw [hm] at this; simp at this
        | cons _ _ => rfl
    simp only [canon, M, ML.perm hp, h1]
  | mul es =>
    simp only [canon]; split
    · rfl
    · simp only [M, ML.perm (List.mergeSort_perm es leMul), (List.mergeSort_perm es leMul).length_eq]
  | _ => rfl

theorem sizeList_perm {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : sizeList l₁ = sizeList l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sizeList, ih]
  | swap => simp [sizeList]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem size_canon (e : Expr) : size (canon e) = size e := by
  cases e with
  | add es => simp only [canon, size, sizeList_perm (List.mergeSort_perm es leAdd)]
  | mul es =>
    simp only [canon]; split
    · rfl
    · simp only [size, sizeList_perm (List.mergeSort_perm es leMul)]
  | _ => rfl

theorem μ_canon (e : Expr) : μ (canon e) = μ e := by
  simp only [μ, cmdCount, d3Count, litCount, numCount, count_canon _ cmdOwn_head, count_canon _ d3Own_head,
    count_canon_lit, count_canon _ numOwn_head, M.canon_eq, size_canon]

/-- For rules that consume a matrix literal (`la.*`, `diff.matrix`): the output is checked to contain
no command or malformed `diff` and strictly fewer nodes on paths to literals — tier 3 of `μ`. The
matrix arithmetic itself is unverified (M7), so its outputs are checked rather than proved. -/
def checkedLit (e : Expr) (r : RuleResult) : RuleResult :=
  if r.error.isSome then r
  else if count cmdOwn r.result = 0 ∧ count d3Own r.result = 0 ∧ count litOwn r.result < count litOwn e then r
  else ⟨Expr.zero, "", none, some "a matrix rule produced an unexpected term"⟩

end MathEngine
