import MathEngine.Expr
/-!
# Provenance-carrying rewriting, with termination as a proof obligation

A `Rule` looks at one node and either rewrites it (returning the new node and *why* the rewrite
is valid) or declines. `normalize` applies rules innermost-first to a fixed point and records
every firing as a `Step`: the whole term before and after, and the path where it fired.

**Termination.** The reference engine hides termination behind a 10 000-step budget. Here it is
a proof obligation: a `Rule` carries a proof that its result is strictly smaller than its input
under a *weighted node count* (`measure`), and `normalize` recurses by well-founded recursion on
`(measure e, size e)`. Nothing is `partial`. The weights are a parameter (`Weights`): each rule
set chooses weights that make its rules decrease, and proves it once per rule. The argument only
needs two facts about the measure, both proved below for every weight assignment:

* it is *additive*, so replacing children by smaller children makes the parent smaller
  (`measure_withChildren`), and
* it is invariant under reordering arguments (`measure_canon`), so canonical ordering can happen
  silently inside the loop without being a rule.

The notebook pipeline needs a different argument (rules that duplicate subterms): see `Order.lean`
and `Terminate.lean`. `normalizeFuel` below remains only for the `expand` command's nested rule set.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Derivations: the "show work" data model (mirrors `Step`/`Derivation` in the protocol)
-- ---------------------------------------------------------------------------

mutual
  structure Step where
    rule : String
    explanation : String
    path : Path
    before : Expr
    after : Expr
    sub : Option Derivation := none
  structure Derivation where
    input : Expr
    steps : Array Step
    output : Expr
end

instance : Inhabited Derivation := ⟨⟨default, #[], default⟩⟩
instance : Inhabited Step := ⟨⟨"", "", [], default, default, none⟩⟩

structure RuleResult where
  result : Expr
  explanation : String
  /-- Steps taken inside this rewrite (e.g. the row operations behind an `rref` command). -/
  sub : Option Derivation := none
  /-- A rule may refuse the whole evaluation (the reference throws, e.g. on a dimension mismatch).
  Only `normalizeFuel` honours this; verified rule sets never set it. -/
  error : Option String := none

-- ---------------------------------------------------------------------------
-- The measure
-- ---------------------------------------------------------------------------

/-- Node weights. A weight depends only on the node's head, never on its children (`head`), and
is at least 1 (`pos`), which is what makes the weighted node count a strict subterm order. -/
structure Weights where
  w : Expr → Nat
  pos : ∀ e, 1 ≤ w e
  head : ∀ e cs, w (withChildren e cs) = w e

/-- Every node weighs 1: plain `size`. -/
def unitWeights : Weights where
  w _ := 1
  pos _ := Nat.le_refl 1
  head _ _ := rfl

mutual
  /-- Weighted node count. -/
  def measure (W : Weights) : Expr → Nat
    | .num q => W.w (.num q)
    | .var x => W.w (.var x)
    | .add es => W.w (.add es) + measureList W es
    | .mul es => W.w (.mul es) + measureList W es
    | .pow b e => W.w (.pow b e) + measure W b + measure W e
    | .fn f es => W.w (.fn f es) + measureList W es
    | .matrix rows => W.w (.matrix rows) + measureRows W rows
  def measureList (W : Weights) : List Expr → Nat
    | [] => 0
    | e :: es => measure W e + measureList W es
  def measureRows (W : Weights) : List (List Expr) → Nat
    | [] => 0
    | r :: rs => measureList W r + measureRows W rs
end

theorem measureList_append (W : Weights) (l₁ l₂ : List Expr) :
    measureList W (l₁ ++ l₂) = measureList W l₁ + measureList W l₂ := by
  induction l₁ with
  | nil => simp [measureList]
  | cons e es ih => simp [measureList, ih]; omega

theorem measureRows_flatten (W : Weights) (rows : List (List Expr)) :
    measureRows W rows = measureList W rows.flatten := by
  induction rows with
  | nil => simp [measureRows, measureList]
  | cons r rs ih => simp [measureRows, measureList_append, ih]

/-- The measure is the head weight plus the children's measures. -/
theorem measure_eq (W : Weights) (e : Expr) : measure W e = W.w e + measureList W (children e) := by
  cases e <;> simp [measure, children, measureList, measureRows_flatten] <;> omega

theorem measureList_perm (W : Weights) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) :
    measureList W l₁ = measureList W l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [measureList, ih]
  | swap => simp [measureList]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem measureList_take_drop (W : Weights) (n : Nat) (l : List Expr) :
    measureList W (l.take n) + measureList W (l.drop n) = measureList W l := by
  rw [← measureList_append, List.take_append_drop]

/-- Rebuilding a node from children: the measure is the head weight plus the new children's. -/
theorem measure_withChildren (W : Weights) (e : Expr) (cs : List Expr)
    (hlen : cs.length = (children e).length) :
    measure W (withChildren e cs) = W.w e + measureList W cs := by
  rw [measure_eq, W.head, children_withChildren e cs hlen]

theorem measureList_children_lt (W : Weights) (e : Expr) : measureList W (children e) < measure W e := by
  rw [measure_eq]; have := W.pos e; omega

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

/-- A rewrite rule with its termination obligation under the weights `W`. -/
structure Rule (W : Weights) where
  name : String
  /-- Silent rules still fire but leave no `Step` (canonical reordering, flattening). -/
  silent : Bool := false
  apply : Expr → Option RuleResult
  decreasing : ∀ e r, apply e = some r → measure W r.result < measure W e

/-- First applicable rule, with the evidence that it applied. -/
def fire (rules : List (Rule W)) (e : Expr) : Option {p : Rule W × RuleResult // p.1.apply e = some p.2} :=
  match rules with
  | [] => none
  | r :: rs =>
    match h : r.apply e with
    | some res => some ⟨(r, res), h⟩
    | none => fire rs e

theorem fire_mem (rules : List (Rule W)) (e : Expr) (p) (h : fire rules e = some p) : p.1.1 ∈ rules := by
  induction rules with
  | nil => simp [fire] at h
  | cons r rs ih =>
    simp only [fire] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

-- ---------------------------------------------------------------------------
-- Canonical argument order (silent, measure-preserving)
-- ---------------------------------------------------------------------------

/-- Total degree in all variables, for ordering sums the way people write them (`x^3 + 3x^2 + 3x + 1`). -/
partial def degree : Expr → Rat
  | .num _ => 0
  | .var _ => 1
  | .pow b (.num q) => degree b * q.val
  | .pow b _ => degree b
  | .mul es => es.foldl (fun d a => d + degree a) 0
  | .add es => es.foldl (fun d a => max d (degree a)) 0
  | .fn _ _ | .matrix _ => 0

/-- `c * rest` with numeric `c`; a term without a coefficient is `1 * itself`. -/
def coeffRest : Expr → Q × Expr
  | .num q => (q, Expr.one)
  | .mul (.num q :: rest) => (q, mulN rest)
  | e => (Q.one, e)

def cmpRat (a b : Rat) : Ordering := if a < b then .lt else if a == b then .eq else .gt
def leMul (a b : Expr) : Bool := compare a b != Ordering.gt
/-- Sums: highest degree first, constants last, otherwise the structural order. -/
def leAdd (a b : Expr) : Bool :=
  let ra := (coeffRest a).2
  let rb := (coeffRest b).2
  let o := (cmpRat (degree rb) (degree ra)).then
    ((Ord.compare (kindRank rb) (kindRank ra)).then ((compare ra rb).then (compare a b)))
  o != Ordering.gt

/-- Sort the arguments of a sum or product; other nodes are unchanged. Products containing a matrix
are not commutative and are left in place (the reference gets this by trying `la.mul` before its sort rule). -/
def canon : Expr → Expr
  | .add es => .add (es.mergeSort leAdd)
  | .mul es => if es.any isMatrix then .mul es else .mul (es.mergeSort leMul)
  | e => e

theorem measure_canon (W : Weights) (e : Expr) : measure W (canon e) = measure W e := by
  cases e with
  | add es =>
    have hw : W.w (.add (es.mergeSort leAdd)) = W.w (.add es) := W.head (.add es) _
    simp only [canon, measure, hw, measureList_perm W (List.mergeSort_perm es leAdd)]
  | mul es =>
    have hw : W.w (.mul (es.mergeSort leMul)) = W.w (.mul es) := W.head (.mul es) _
    simp only [canon]
    split
    · rfl
    · simp only [measure, hw, measureList_perm W (List.mergeSort_perm es leMul)]
  | _ => rfl

-- ---------------------------------------------------------------------------
-- The rewriter
-- ---------------------------------------------------------------------------

/-- A firing as recorded during normalization: only the local result. Whole-term `before`/`after`
are reconstructed afterwards by replaying the firings from the input (`buildSteps`). -/
structure RawStep where
  rule : String
  silent : Bool
  explanation : String
  path : Path
  after : Expr
  sub : Option Derivation

/-- Lexicographic order on pairs of naturals, in the form the termination proofs need. -/
theorem lex_of_le {a a' b b' : Nat} (h₁ : a ≤ a') (h₂ : a = a' → b < b') :
    Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := by
  rcases Nat.lt_or_eq_of_le h₁ with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ (h₂ rfl)

/-- Same for triples: `normAt` and `normChildren` share one well-founded order
`(measure, size, phase)` where the phase separates "at a node" (0) from "in its children" (1). -/
theorem lex3 {a a' b b' c c' : Nat} (h₁ : a ≤ a') (h₂ : a = a' → b ≤ b') (h₃ : a = a' → b = b' → c < c') :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a, b, c) (a', b', c') := by
  rcases Nat.lt_or_eq_of_le h₁ with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ (lex_of_le (h₂ rfl) (h₃ rfl))

mutual
  /-- Normalize the subterm `e` sitting at `path`: children first, then rules at the node until
  none applies, re-normalizing after each firing. Returns the result and the firings so far,
  together with the fact that the result is no heavier than the input. -/
  def normAt (rules : List (Rule W)) (e : Expr) (path : Path) (acc : Array RawStep) :
      {r : Expr × Array RawStep // measure W r.1 ≤ measure W e} :=
    match normChildren rules (children e) path 0 acc with
    | ⟨(cs, acc₀), hcs⟩ =>
      let e₀ := withChildren e cs
      let e₁ := canon e₀
      -- canonical order is silent but must be replayed, or later paths would not line up
      let acc₁ := if equal e₁ e₀ then acc₀ else acc₀.push ⟨"simp.sort", true, "commutativity", path, e₁, none⟩
      have h₁ : measure W e₁ ≤ measure W e := by
        have hm : measureList W cs ≤ measureList W (children e) := hcs.2
        simp only [e₁, e₀]; rw [measure_canon, measure_withChildren W e cs hcs.1, measure_eq W e]; omega
      match hf : fire rules e₁ with
      | none => ⟨(e₁, acc₁), h₁⟩
      | some ⟨(rule, res), hr⟩ =>
        have hdec : measure W res.result < measure W e := Nat.lt_of_lt_of_le (rule.decreasing e₁ res hr) h₁
        let acc₂ := acc₁.push ⟨rule.name, rule.silent, res.explanation, path, res.result, res.sub⟩
        match normAt rules res.result path acc₂ with
        | ⟨r, hr'⟩ => ⟨r, Nat.le_of_lt (Nat.lt_of_le_of_lt hr' hdec)⟩
  termination_by (measure W e, size e, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (measureList_children_lt W e)
    · exact Prod.Lex.left _ _ hdec

  def normChildren (rules : List (Rule W)) (cs : List Expr) (path : Path) (i : Nat) (acc : Array RawStep) :
      {r : List Expr × Array RawStep // r.1.length = cs.length ∧ measureList W r.1 ≤ measureList W cs} :=
    match cs with
    | [] => ⟨([], acc), by simp [measureList]⟩
    | c :: cs' =>
      match normAt rules c (path ++ [i]) acc with
      | ⟨(c', acc₁), hc⟩ =>
        match normChildren rules cs' path (i + 1) acc₁ with
        | ⟨(cs'', acc₂), hcs⟩ =>
          ⟨(c' :: cs'', acc₂), by
            have hc' : measure W c' ≤ measure W c := hc
            have hl : cs''.length = cs'.length := hcs.1
            have hm : measureList W cs'' ≤ measureList W cs' := hcs.2
            simp only [measureList, List.length_cons]; omega⟩
  termination_by (measureList W cs, sizeList cs, 1)
  decreasing_by
    · exact lex3 (by simp only [measureList]; omega) (fun _ => by simp only [sizeList]; omega) (fun _ _ => Nat.zero_lt_one)
    · exact lex3 (by simp only [measureList]; omega) (fun _ => by simp only [sizeList]; omega)
        (fun _ h => by simp only [sizeList] at h; have := size_pos c; omega)
end

/-- Replace the subterm at `path`. -/
def replaceAt (e : Expr) (path : Path) (new : Expr) : Expr :=
  match path with
  | [] => new
  | i :: rest =>
    let cs := children e
    match cs[i]? with
    | some c => withChildren e (cs.set i (replaceAt c rest new))
    | none => e

/-- Replay the firings from `input`, producing steps with whole-term `before`/`after`. -/
def buildSteps (input : Expr) (raw : Array RawStep) : Array Step × Expr :=
  raw.foldl (init := (#[], input)) fun (out, cur) s =>
    let next := replaceAt cur s.path s.after
    (if s.silent then out else out.push { rule := s.rule, explanation := s.explanation, path := s.path, before := cur, after := next, sub := s.sub }, next)

abbrev TraceM := StateM (Array Step)

/-- Rewrite `e` to a normal form under `rules`, appending the steps to the trace. The result is the
normalizer's own (the replay in `buildSteps` reconstructs the same term for the step snapshots). -/
def normalize (rules : List (Rule W)) (e : Expr) : TraceM Expr := do
  let ⟨(out, raw), _⟩ := normAt rules e [] #[]
  let (steps, _) := buildSteps e raw
  modify (· ++ steps)
  pure out

theorem normalize_run (rules : List (Rule W)) (e : Expr) (s : Array Step) :
    ((normalize rules e).run' s) = (normAt rules e [] #[]).1.1 := by
  simp only [normalize, StateT.run', bind, StateT.bind, modify, pure, StateT.pure, MonadStateOf.modifyGet, StateT.modifyGet, Id.run]
  rfl

/-- Rewrite and package the whole derivation. -/
def derive (rules : List (Rule W)) (e : Expr) : Derivation :=
  let (out, steps) := (normalize rules e).run #[]
  ⟨e, steps, out⟩

-- ---------------------------------------------------------------------------
-- Fuel-based variant, used only by the `expand` command's nested set (book/TRACKING.md)
-- ---------------------------------------------------------------------------

structure PlainRule where
  name : String
  silent : Bool := false
  apply : Expr → Option RuleResult

def fireP (rules : List PlainRule) (e : Expr) : Option (PlainRule × RuleResult) :=
  match rules with
  | [] => none
  | r :: rs => match r.apply e with | some res => some (r, res) | none => fireP rs e

/-- Result of a fuel-bounded normalization. `exhausted` means a rule wanted to fire with no fuel left;
`error` is a rule's refusal (`RuleResult.error`). -/
structure FuelState where
  steps : Array RawStep := #[]
  exhausted : Bool := false
  error : Option String := none

mutual
  def normAtF (rules : List PlainRule) (fuel : Nat) (e : Expr) (path : Path) (st : FuelState) : Expr × FuelState :=
    let (cs, st₀) := normChildrenF rules fuel (children e) path 0 st
    let e₀ := withChildren e cs
    let e₁ := canon e₀
    let st₁ := if equal e₁ e₀ then st₀ else { st₀ with steps := st₀.steps.push ⟨"simp.sort", true, "commutativity", path, e₁, none⟩ }
    if st₁.error.isSome then (e₁, st₁) else
    match fireP rules e₁ with
    | none => (e₁, st₁)
    | some (rule, res) =>
      if res.error.isSome then (e₁, { st₁ with error := res.error }) else
      match fuel with
      | 0 => (e₁, { st₁ with exhausted := true })
      | fuel' + 1 =>
        let st₂ := { st₁ with steps := st₁.steps.push ⟨rule.name, rule.silent, res.explanation, path, res.result, res.sub⟩ }
        normAtF rules fuel' res.result path st₂
  termination_by (fuel, size e, 0)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (sizeList_children_lt e))
    · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)

  def normChildrenF (rules : List PlainRule) (fuel : Nat) (cs : List Expr) (path : Path) (i : Nat) (st : FuelState) : List Expr × FuelState :=
    match cs with
    | [] => ([], st)
    | c :: cs' =>
      let (c', st₁) := normAtF rules fuel c (path ++ [i]) st
      let (cs'', st₂) := normChildrenF rules fuel cs' path (i + 1) st₁
      (c' :: cs'', st₂)
  termination_by (fuel, sizeList cs, 1)
  decreasing_by
    · exact Prod.Lex.right _ (lex_of_le (by simp only [sizeList]; omega) (fun _ => Nat.zero_lt_one))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [sizeList]; have := size_pos c; omega))
end

/-- Fuel-bounded normalization. Fails if the fuel ran out or a rule refused. -/
def normalizeFuel (rules : List PlainRule) (fuel : Nat) (e : Expr) : TraceM (Except String Expr) := do
  let (out, st) := normAtF rules fuel e [] {}
  match st.error with
  | some msg => pure (.error msg)
  | none =>
    if st.exhausted then pure (.error s!"rewriting exceeded {fuel} steps (non-terminating rule set?)") else
    let (steps, _) := buildSteps e st.steps
    modify (· ++ steps)
    pure (.ok out)

/-- Run a nested normalization and package its steps as a sub-derivation (the reference's `trace.nested`). -/
def nested (rules : List PlainRule) (fuel : Nat) (e : Expr) : Except String (Expr × Option Derivation) :=
  match (normalizeFuel rules fuel e).run #[] with
  | (.error msg, _) => .error msg
  | (.ok out, steps) => .ok (out, if steps.isEmpty then none else some ⟨e, steps, out⟩)

/-- A verified rule, forgetting its proof. -/
def Rule.toPlain (r : Rule W) : PlainRule := { name := r.name, silent := r.silent, apply := r.apply }

end MathEngine
