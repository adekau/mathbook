import MathEngine.Relation
/-!
# What is proved about relations

- `transitiveFailure_none`: when the check finds no counterexample, the relation is transitive.
- `round_sub_transitive`: a round of transitive closure adds only pairs that every transitive relation
  containing the original has; so does every round after it (`transClosure_sub`), and the closure is
  inside every transitive relation containing the original.
- `stable_transitive`: when a round adds nothing, the relation is transitive. The closure stops
  exactly then (`transClosure` reports it), so it is the least transitive relation containing the
  original.
- `wf_of_measure`: a measure that goes down along every step (`measureFailure` finds none) makes the
  relation, read as "steps to", well-founded in Lean's sense: no infinite chain of steps.
- `not_wf_of_closed`: a nonempty set every element of which steps into the set (a cycle) makes it not
  well-founded. `wellfounded` decides by one or the other, so each answer comes with its proof
  (`wellfounded_none`, `wellfounded_some`).
-/
namespace MathEngine
namespace Ord

/-- A relation (as its pair list) is transitive. -/
def Transitive (ps : List (String × String)) : Prop :=
  ∀ x y z, (x, y) ∈ ps → (y, z) ∈ ps → (x, z) ∈ ps

theorem Rel.has_iff (R : Rel) (x y : String) : R.has x y = true ↔ (x, y) ∈ R.pairs := by
  simp [Rel.has, List.contains_iff_mem]

theorem transitiveFailure_none (R : Rel) (h : transitiveFailure R = none) : Transitive R.pairs := by
  intro x y z hxy hyz
  unfold transitiveFailure at h
  have h1 := List.findSome?_eq_none_iff.mp h (x, y) hxy
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at h1
  have h2 := h1 (y, z) hyz
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at h2
  simpa [Rel.has_iff] using h2

/-- Every pair a round adds is in every transitive relation containing the original. -/
theorem round_sub_transitive (R : Rel) (T : List (String × String)) (hT : Transitive T)
    (hsub : ∀ p ∈ R.pairs, p ∈ T) : ∀ p ∈ R.round, p ∈ T := by
  intro p hp
  simp only [Rel.round, List.mem_flatMap, List.mem_filterMap] at hp
  obtain ⟨⟨a, b⟩, hab, ⟨c, d⟩, hcd, hsome⟩ := hp
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hbc, _⟩ := hcond
    subst hbc
    cases hsome
    exact hT a b d (hsub _ hab) (hsub _ hcd)
  · cases hsome

/-- The closure, whatever its rounds, stays inside every transitive relation containing the original. -/
theorem transClosure_go_sub (T : List (String × String)) (hT : Transitive T) :
    ∀ (n : Nat) (R : Rel) (acc : List (List (String × String))), (∀ p ∈ R.pairs, p ∈ T) →
      ∀ p ∈ (transClosure.go n R acc).1.pairs, p ∈ T := by
  intro n
  induction n with
  | zero => intro R acc h; simpa [transClosure.go] using h
  | succ n ih =>
    intro R acc h
    simp only [transClosure.go]
    split
    · simpa using h
    · apply ih
      intro p hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h p hp
      · exact round_sub_transitive R T hT h p (List.mem_eraseDups.mp hp)

theorem transClosure_sub (R : Rel) (T : List (String × String)) (hT : Transitive T)
    (hsub : ∀ p ∈ R.pairs, p ∈ T) : ∀ p ∈ (transClosure R).1.pairs, p ∈ T :=
  transClosure_go_sub T hT _ R [] hsub

/-- A relation a round adds nothing to is transitive. -/
theorem stable_transitive (R : Rel) (h : R.round = []) : Transitive R.pairs := by
  intro x y z hxy hyz
  by_cases hxz : (x, z) ∈ R.pairs
  · exact hxz
  exfalso
  have : (x, z) ∈ R.round := by
    simp only [Rel.round, List.mem_flatMap, List.mem_filterMap]
    refine ⟨(x, y), hxy, (y, z), hyz, ?_⟩
    have : R.has x z = false := by
      cases hh : R.has x z
      · rfl
      · exact absurd ((Rel.has_iff R x z).mp hh) hxz
    simp [this]
  rw [h] at this
  simp at this

/-- The closure the engine returns is transitive whenever it reports it settled. -/
theorem transClosure_transitive : ∀ (n : Nat) (R : Rel) (acc : List (List (String × String))),
    (transClosure.go n R acc).2.2 = true → Transitive (transClosure.go n R acc).1.pairs := by
  intro n
  induction n with
  | zero => intro R acc h; simp only [transClosure.go, List.isEmpty_iff] at h ⊢; exact stable_transitive R h
  | succ n ih =>
    intro R acc h
    by_cases hemp : R.round.eraseDups.isEmpty = true
    · simp only [transClosure.go, hemp, if_true] at h ⊢
      simp only [List.isEmpty_iff] at hemp
      apply stable_transitive
      -- no new pair: the round adds nothing
      cases hr : R.round with
      | nil => rfl
      | cons p ps =>
        have : p ∈ R.round.eraseDups := List.mem_eraseDups.mpr (by rw [hr]; simp)
        rw [hemp] at this; simp at this
    · simp only [transClosure.go, hemp] at h ⊢
      exact ih _ _ h

/-! ## Well-founded relations -/

/-- `R` read as "steps to", for `WellFounded`: `y` is below `x` when `x` steps to `y`. -/
def Below (R : Rel) (y x : String) : Prop := (x, y) ∈ R.pairs

theorem measureFailure_none {R : Rel} {m : String → Option Int} (h : measureFailure R m = none) :
    ∀ x y, (x, y) ∈ R.pairs → ∃ a b, m x = some a ∧ m y = some b ∧ b < a := by
  intro x y hxy
  unfold measureFailure at h
  have := List.find?_eq_none.mp h (x, y) hxy
  cases hx : m x <;> cases hy : m y <;> simp_all

theorem natAbs_le_sum {a : Int} : ∀ {l : List Int}, a ∈ l → a.natAbs ≤ (l.map Int.natAbs).sum
  | [], h => by simp at h
  | b :: l, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := natAbs_le_sum h; simp; omega

/-- **A measure that goes down along every step makes the relation well-founded**: the values on the
finitely many elements the pairs mention are bounded below, so the measure is a natural number in
disguise. -/
theorem wf_of_measure (R : Rel) (m : String → Option Int) (h : measureFailure R m = none) :
    WellFounded (Below R) := by
  let vals : List Int := (R.pairs.flatMap fun p => [p.1, p.2]).filterMap m
  let S : Int := ((vals.map Int.natAbs).sum : Nat)
  have hbound : ∀ z a, (∃ p ∈ R.pairs, z = p.1 ∨ z = p.2) → m z = some a → -S ≤ a := by
    intro z a ⟨p, hp, hz⟩ hza
    have hmem : a ∈ vals := by
      simp only [vals, List.mem_filterMap, List.mem_flatMap]
      exact ⟨z, ⟨p, hp, by rcases hz with rfl | rfl <;> simp⟩, hza⟩
    have := natAbs_le_sum hmem
    simp only [S]; omega
  let f : String → Nat := fun x => ((m x).getD 0 + S).toNat
  refine Subrelation.wf (r := InvImage (· < ·) f) ?_ (InvImage.wf f Nat.lt_wfRel.wf)
  intro y x hyx
  obtain ⟨a, b, ha, hb, hlt⟩ := measureFailure_none h x y hyx
  have ha' := hbound x a ⟨(x, y), hyx, Or.inl rfl⟩ ha
  have hb' := hbound y b ⟨(x, y), hyx, Or.inr rfl⟩ hb
  show f y < f x
  simp only [f, ha, hb, Option.getD_some]
  omega

/-- **A set every element of which steps into it makes the relation not well-founded.** -/
theorem not_wf_of_closed {R : Rel} {c : List String} (h : stepClosed R c = true) : ¬ WellFounded (Below R) := by
  intro hwf
  simp only [stepClosed, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_true] at h
  obtain ⟨hne, hall⟩ := h
  have key : ∀ x, x ∈ c → False := fun x =>
    hwf.induction (C := fun x => x ∈ c → False) x fun x ih hx => by
      obtain ⟨y, hy, hxy⟩ := hall x hx
      exact ih y ((Rel.has_iff R x y).mp hxy) hy
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil c hne
  exact key x hx

/-- **`rel.wellfounded`, answering yes**: the relation is well-founded. -/
theorem wellfounded_none {R : Rel} (h : wellfounded R = .ok none) : WellFounded (Below R) := by
  unfold wellfounded at h
  rcases hp : peelRanks R with ⟨ranks, left⟩
  simp only [hp] at h
  by_cases hl : left.isEmpty = true
  · rw [ite_eq_left hl] at h
    by_cases hm : (measureFailure R fun x => (ranks.lookup x).map Int.ofNat).isNone = true
    · exact wf_of_measure R _ (Option.isNone_iff_eq_none.mp hm)
    · rw [ite_eq_right hm] at h; cases h
  · rw [ite_eq_right hl] at h
    split at h
    · split at h <;> cases h
    · cases h

/-- **`rel.wellfounded`, answering no**: the cycle it shows steps back into itself, so the relation is
not well-founded. -/
theorem wellfounded_some {R : Rel} {c : List String} (h : wellfounded R = .ok (some c)) :
    stepClosed R c = true ∧ ¬ WellFounded (Below R) := by
  unfold wellfounded at h
  rcases hp : peelRanks R with ⟨ranks, left⟩
  simp only [hp] at h
  by_cases hl : left.isEmpty = true
  · rw [ite_eq_left hl] at h
    split at h <;> cases h
  · rw [ite_eq_right hl] at h
    split at h
    · split at h
      · rename_i hc; cases h; exact ⟨hc, not_wf_of_closed hc⟩
      · cases h
    · cases h

end Ord
end MathEngine
