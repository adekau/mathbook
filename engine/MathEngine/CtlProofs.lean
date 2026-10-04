import MathEngine.Systems
/-!
# What is proved about CTL

The systems world computes a CTL operator as the last set of a chain of Kleene rounds, and checks the
answer against a certificate read off the chain (`Sys.Ctl.check*`, `Systems.lean`). Here each check is
proved to pin the set down exactly: where it passes, a state below `n` is in the set if and only if
the formula holds there by the meaning of its paths, over the edges `es` (the graph's transitions,
which `System.explore_edges` proves are exactly the system's between reachable states).

- `checkEF_spec`: `EF φ`, some path reaches φ (`EF`).
- `checkEG_spec`: `EG φ`, an infinite path stays in φ (`EG`).
- `checkAG_spec`: `AG φ`, every state reachable is in φ (`AG`).
- `checkAF_spec`: `AF φ`, every maximal path reaches φ, the infinite ones and the ones that stop where
  no step is possible (`AF`).
- `checkEX_spec`, `checkAX_spec`: one step.

Infinite paths are functions `ℕ → ℕ`; a path that stops is a function with a last index. The proofs are
inductions on the ranks, and for `EG` and `AF` a path built by choosing a step at each state.
-/
namespace MathEngine
namespace Sys
namespace Ctl

section
variable (es : List (Nat × Nat)) (sat : List Nat)

/-- Some path from `s` reaches φ. -/
inductive EF : Nat → Prop
  | here {s : Nat} : s ∈ sat → EF s
  | step {s t : Nat} : (s, t) ∈ es → EF t → EF s

/-- The states reachable from `s`, `s` included. -/
inductive Reach : Nat → Nat → Prop
  | refl (s : Nat) : Reach s s
  | step {s t u : Nat} : (s, t) ∈ es → Reach t u → Reach s u

/-- An infinite path. -/
def IsPath (f : Nat → Nat) : Prop := ∀ k, (f k, f (k + 1)) ∈ es

/-- No step from `s`. -/
def Dead (s : Nat) : Prop := ∀ t, (s, t) ∉ es

/-- An infinite path from `s` along which φ always holds. -/
def EG (s : Nat) : Prop := ∃ f : Nat → Nat, f 0 = s ∧ IsPath es f ∧ ∀ k, f k ∈ sat

/-- Every state reachable from `s` is in φ. -/
def AG (s : Nat) : Prop := ∀ t, Reach es s t → t ∈ sat

/-- Every maximal path from `s` reaches φ: every infinite path, and every path that stops at a state
with no step. -/
def AF (s : Nat) : Prop :=
  (∀ f : Nat → Nat, f 0 = s → IsPath es f → ∃ k, f k ∈ sat) ∧
  (∀ (f : Nat → Nat) (j : Nat), f 0 = s → (∀ i, i < j → (f i, f (i + 1)) ∈ es) → Dead es (f j) →
    ∃ i, i ≤ j ∧ f i ∈ sat)
end

theorem mem_of_contains {l : List Nat} {x : Nat} : l.contains x = true ↔ x ∈ l := by simp

theorem inRange_spec {n : Nat} {es : List (Nat × Nat)} (h : inRange n es = true) {a b : Nat}
    (hab : (a, b) ∈ es) : a < n ∧ b < n := by
  simp only [inRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h _ hab

/-- A check's verdict at one state below `n`. -/
theorem at_state {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) {s : Nat} (hs : s < n) : p s = true := by
  simp only [List.all_eq_true, List.mem_range] at h
  exact h s hs

/-- Strong induction on a rank. -/
theorem rank_induction (r : Nat → Nat) (P : Nat → Prop) (h : ∀ s, (∀ t, r t < r s → P t) → P s) (s : Nat) : P s := by
  have key : ∀ k, ∀ s, r s < k → P s := by
    intro k
    induction k with
    | zero => intro s hs; omega
    | succ k ih =>
      intro s hs
      exact h s fun t ht => ih t (by omega)
  exact key (r s + 1) s (by omega)

/-! ## `EF` -/

theorem checkEF_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} {r : Nat → Nat}
    (h : checkEF n es sat Z r = true) {s : Nat} (hs : s < n) : s ∈ Z ↔ EF es sat s := by
  simp only [checkEF, Bool.and_eq_true] at h
  obtain ⟨hr, hall⟩ := h
  constructor
  · -- a member: in φ, or a step to a member of lower rank
    intro hz
    refine rank_induction r (fun s => s < n → s ∈ Z → EF es sat s) ?_ s hs hz
    intro s ih hs hz
    have := at_state hall hs
    simp only [mem_of_contains.mpr hz, ite_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at this
    rcases this with hsat | ⟨⟨a, t⟩, he, ⟨ha, hzt⟩, hlt⟩
    · exact EF.here (mem_of_contains.mp hsat)
    · dsimp only at ha hzt hlt; subst ha
      exact EF.step he (ih t hlt (inRange_spec hr he).2 (mem_of_contains.mp hzt))
  · -- a non-member is not in φ and steps to no member, so no path from it reaches φ
    intro hef
    induction hef with
    | @here s hsat =>
      refine Classical.byContradiction fun hz => ?_
      have := at_state hall hs
      simp only [show Z.contains s = false by simpa using hz, Bool.false_eq_true, ite_false, Bool.and_eq_true,
        Bool.not_eq_true'] at this
      simp [hsat] at this
    | @step s t he _ ih =>
      have ht := (inRange_spec hr he).2
      have htz := ih ht
      refine Classical.byContradiction fun hz => ?_
      have := at_state hall hs
      simp only [show Z.contains s = false by simpa using hz, Bool.false_eq_true, ite_false, Bool.and_eq_true,
        Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
      have := this.2 (s, t) he
      simp [htz] at this

/-! ## `AG` -/

theorem checkAG_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} {r : Nat → Nat}
    (h : checkAG n es sat Z r = true) {s : Nat} (hs : s < n) : s ∈ Z ↔ AG es sat s := by
  simp only [checkAG, Bool.and_eq_true] at h
  obtain ⟨hr, hall⟩ := h
  constructor
  · -- members are in φ and step only to members: everything reachable is a member
    intro hz t hreach
    have key : ∀ u v, Reach es u v → u < n → u ∈ Z → v ∈ Z ∧ v < n := by
      intro u v hrv
      induction hrv with
      | refl u => exact fun hu hz => ⟨hz, hu⟩
      | @step u w _ he _ ih =>
        intro hu hz
        have := at_state hall hu
        simp only [mem_of_contains.mpr hz, ite_true, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
          bne_iff_ne, ne_eq] at this
        have hw := this.2 (u, w) he
        simp only [not_true_eq_false, false_or] at hw
        exact ih (inRange_spec hr he).2 (mem_of_contains.mp hw)
    obtain ⟨htz, ht⟩ := key s t hreach hs hz
    have := at_state hall ht
    simp only [mem_of_contains.mpr htz, ite_true, Bool.and_eq_true] at this
    exact mem_of_contains.mp this.1
  · -- a non-member is not in φ, or steps to a non-member of lower rank
    intro hag
    refine Classical.byContradiction fun hz => ?_
    have key : ∀ s, s < n → s ∉ Z → ¬ AG es sat s := by
      intro s
      refine rank_induction r (fun s => s < n → s ∉ Z → ¬ AG es sat s) ?_ s
      intro s ih hs hz hag
      have := at_state hall hs
      simp only [show Z.contains s = false by simpa using hz, Bool.false_eq_true, ite_false, Bool.or_eq_true,
        Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      rcases this with hns | ⟨⟨a, t⟩, he, ⟨ha, hzt⟩, hlt⟩
      · have := mem_of_contains.mpr (hag s (Reach.refl s))
        simp_all
      · dsimp only at ha hzt hlt; subst ha
        refine ih t hlt (inRange_spec hr he).2 (by simpa using hzt) ?_
        intro u hu
        exact hag u (Reach.step he hu)
    exact key s hs hz hag

/-! ## `EG` -/

theorem checkEG_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} {r : Nat → Nat}
    (h : checkEG n es sat Z r = true) {s : Nat} (hs : s < n) : s ∈ Z ↔ EG es sat s := by
  simp only [checkEG, Bool.and_eq_true] at h
  obtain ⟨hr, hall⟩ := h
  -- a member is in φ and has a step to a member
  have hmem : ∀ x, x < n → x ∈ Z → x ∈ sat ∧ ∃ t, (x, t) ∈ es ∧ t ∈ Z := by
    intro x hx hz
    have := at_state hall hx
    simp only [mem_of_contains.mpr hz, ite_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at this
    obtain ⟨hsat, ⟨a, t⟩, he, rfl, hzt⟩ := this
    exact ⟨mem_of_contains.mp hsat, t, he, mem_of_contains.mp hzt⟩
  constructor
  · -- follow steps from member to member, for ever
    intro hz
    classical
    let next (x : Nat) : Nat := if h : ∃ t, (x, t) ∈ es ∧ t ∈ Z then Classical.choose h else x
    let f (k : Nat) : Nat := Nat.rec s (fun _ x => next x) k
    have hfk : ∀ k, f (k + 1) = next (f k) := fun _ => rfl
    have hf : ∀ k, f k < n ∧ f k ∈ Z := by
      intro k
      induction k with
      | zero => exact ⟨hs, hz⟩
      | succ k ih =>
        have hex := (hmem (f k) ih.1 ih.2).2
        have hnext : f (k + 1) = Classical.choose hex := by
          rw [hfk]; simp only [next, dite_eq_left hex]
        have hspec := Classical.choose_spec hex
        rw [hnext]
        exact ⟨(inRange_spec hr hspec.1).2, hspec.2⟩
    refine ⟨f, rfl, fun k => ?_, fun k => (hmem (f k) (hf k).1 (hf k).2).1⟩
    have hex := (hmem (f k) (hf k).1 (hf k).2).2
    have hnext : f (k + 1) = Classical.choose hex := by
      rw [hfk]; simp only [next, dite_eq_left hex]
    rw [hnext]
    exact (Classical.choose_spec hex).1
  · -- a non-member is not in φ, or steps only to non-members of lower rank
    intro heg
    refine Classical.byContradiction fun hz => ?_
    have key : ∀ s, s < n → s ∉ Z → ¬ EG es sat s := by
      intro s
      refine rank_induction r (fun s => s < n → s ∉ Z → ¬ EG es sat s) ?_ s
      intro s ih hs hz ⟨f, hf0, hpath, hsat⟩
      have := at_state hall hs
      simp only [show Z.contains s = false by simpa using hz, Bool.false_eq_true, ite_false, Bool.or_eq_true,
        Bool.not_eq_true', List.all_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with hns | hsteps
      · have := hsat 0; rw [hf0] at this
        have := mem_of_contains.mpr this
        simp_all
      · have he := hpath 0
        rw [hf0] at he
        have hst := hsteps (s, f 1) he
        simp only [not_true_eq_false, false_or] at hst
        refine ih (f 1) hst.2 (inRange_spec hr he).2 (by simpa using hst.1) ⟨fun k => f (k + 1), rfl, ?_, ?_⟩
        · intro k; exact hpath (k + 1)
        · intro k; exact hsat (k + 1)
    exact key s hs hz heg

/-! ## `AF` -/

/-- The first index where a property holds, from any index where it does. -/
theorem exists_first (p : Nat → Prop) : ∀ k, p k → ∃ j, j ≤ k ∧ p j ∧ ∀ i, i < j → ¬ p i := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h : ∃ i, i < k ∧ p i
    · obtain ⟨i, hik, hi⟩ := h
      obtain ⟨j, hj, hpj, hfirst⟩ := ih i hik hi
      exact ⟨j, by omega, hpj, hfirst⟩
    · exact ⟨k, Nat.le_refl _, hk, fun i hi hpi => h ⟨i, hi, hpi⟩⟩

theorem checkAF_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} {r : Nat → Nat}
    (h : checkAF n es sat Z r = true) {s : Nat} (hs : s < n) : s ∈ Z ↔ AF es sat s := by
  simp only [checkAF, Bool.and_eq_true] at h
  obtain ⟨hr, hall⟩ := h
  -- a member is in φ, or has a step and steps only to members of lower rank
  have hmem : ∀ x, x < n → x ∈ Z → x ∈ sat ∨ ((∃ t, (x, t) ∈ es) ∧ ∀ t, (x, t) ∈ es → t ∈ Z ∧ r t < r x) := by
    intro x hx hz
    have := at_state hall hx
    simp only [mem_of_contains.mpr hz, ite_true, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    rcases this with hsat | ⟨⟨⟨a, t⟩, he, rfl⟩, hall'⟩
    · exact Or.inl (mem_of_contains.mp hsat)
    · refine Or.inr ⟨⟨t, he⟩, fun u hu => ?_⟩
      have := hall' (a, u) hu
      simp only [not_true_eq_false, false_or] at this
      exact ⟨mem_of_contains.mp this.1, this.2⟩
  constructor
  · intro hz
    refine rank_induction r (fun s => s < n → s ∈ Z → AF es sat s) ?_ s hs hz
    intro s ih hs hz
    rcases hmem s hs hz with hsat | ⟨⟨t₀, he₀⟩, hsteps⟩
    · exact ⟨fun f hf0 _ => ⟨0, hf0 ▸ hsat⟩, fun f j hf0 _ _ => ⟨0, Nat.zero_le _, hf0 ▸ hsat⟩⟩
    · constructor
      · intro f hf0 hpath
        have he := hpath 0
        rw [hf0] at he
        obtain ⟨hz1, hlt⟩ := hsteps (f 1) he
        obtain ⟨k, hk⟩ := (ih (f 1) hlt (inRange_spec hr he).2 hz1).1 (fun k => f (k + 1)) rfl (fun k => hpath (k + 1))
        exact ⟨k + 1, hk⟩
      · intro f j hf0 hsteps' hdead
        cases j with
        | zero => rw [hf0] at hdead; exact absurd he₀ (hdead t₀)
        | succ j =>
          have he := hsteps' 0 (by omega)
          rw [hf0] at he
          obtain ⟨hz1, hlt⟩ := hsteps (f 1) he
          obtain ⟨i, hi, hfi⟩ := (ih (f 1) hlt (inRange_spec hr he).2 hz1).2 (fun k => f (k + 1)) j rfl
            (fun i hi => hsteps' (i + 1) (by omega)) hdead
          exact ⟨i + 1, by omega, hfi⟩
  · -- a non-member is not in φ, and stops or steps to a non-member: follow such steps
    intro haf
    refine Classical.byContradiction fun hz => ?_
    classical
    have hnon : ∀ x, x < n → x ∉ Z → x ∉ sat ∧ (Dead es x ∨ ∃ t, (x, t) ∈ es ∧ t ∉ Z) := by
      intro x hx hzx
      have := at_state hall hx
      simp only [show Z.contains x = false by simpa using hzx, Bool.false_eq_true, ite_false, Bool.and_eq_true,
        Bool.not_eq_true', Bool.or_eq_true, List.any_eq_false, List.any_eq_true, beq_iff_eq] at this
      obtain ⟨hns, hrest⟩ := this
      refine ⟨by simpa using hns, ?_⟩
      rcases hrest with hdead | ⟨⟨a, t⟩, he, rfl, hzt⟩
      · left; intro t he; exact hdead (x, t) he rfl
      · right; exact ⟨t, he, by simpa using hzt⟩
    let next (x : Nat) : Nat := if h : ∃ t, (x, t) ∈ es ∧ t ∉ Z then Classical.choose h else x
    let f (k : Nat) : Nat := Nat.rec s (fun _ x => next x) k
    have hfk : ∀ k, f (k + 1) = next (f k) := fun _ => rfl
    have hf : ∀ k, f k < n ∧ f k ∉ Z := by
      intro k
      induction k with
      | zero => exact ⟨hs, hz⟩
      | succ k ih =>
        rw [hfk]
        by_cases hex : ∃ t, (f k, t) ∈ es ∧ t ∉ Z
        · simp only [next, dite_eq_left hex]
          have hspec := Classical.choose_spec hex
          exact ⟨(inRange_spec hr hspec.1).2, hspec.2⟩
        · simp only [next, dite_eq_right hex]; exact ih
    -- where `f k` can step, the next state is a step to a non-member
    have hstep : ∀ k, ¬ Dead es (f k) → (f k, f (k + 1)) ∈ es := by
      intro k hlive
      rcases (hnon (f k) (hf k).1 (hf k).2).2 with hdead | hex
      · exact absurd hdead hlive
      · rw [hfk]; simp only [next, dite_eq_left hex]; exact (Classical.choose_spec hex).1
    by_cases hdeadk : ∃ k, Dead es (f k)
    · obtain ⟨k, hk⟩ := hdeadk
      obtain ⟨j, -, hj, hfirst⟩ := exists_first (fun k => Dead es (f k)) k hk
      obtain ⟨i, -, hi⟩ := haf.2 f j rfl (fun i hi => hstep i (hfirst i hi)) hj
      exact (hnon (f i) (hf i).1 (hf i).2).1 hi
    · obtain ⟨k, hk⟩ := haf.1 f rfl (fun k => hstep k fun hd => hdeadk ⟨k, hd⟩)
      exact (hnon (f k) (hf k).1 (hf k).2).1 hk

/-! ## One step -/

theorem checkEX_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} (h : checkEX n es sat Z = true)
    {s : Nat} (hs : s < n) : s ∈ Z ↔ ∃ t, (s, t) ∈ es ∧ t ∈ sat := by
  have := at_state h hs
  simp only [beq_iff_eq] at this
  rw [← mem_of_contains, this]
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, mem_of_contains]
  constructor
  · rintro ⟨⟨a, t⟩, he, rfl, ht⟩; exact ⟨t, he, ht⟩
  · rintro ⟨t, he, ht⟩; exact ⟨(s, t), he, rfl, ht⟩

theorem checkAX_spec {n : Nat} {es : List (Nat × Nat)} {sat Z : List Nat} (h : checkAX n es sat Z = true)
    {s : Nat} (hs : s < n) : s ∈ Z ↔ (∃ t, (s, t) ∈ es) ∧ ∀ t, (s, t) ∈ es → t ∈ sat := by
  have := at_state h hs
  simp only [beq_iff_eq] at this
  rw [← mem_of_contains, this]
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, mem_of_contains]
  constructor
  · rintro ⟨⟨⟨a, t⟩, he, rfl⟩, hall⟩
    exact ⟨⟨t, he⟩, fun u hu => by simpa using hall (a, u) hu⟩
  · rintro ⟨⟨t, he⟩, hall⟩
    exact ⟨⟨(s, t), he, rfl⟩, fun ⟨a, u⟩ hu => by
      by_cases has : a = s
      · subst has; exact Or.inr (hall u hu)
      · exact Or.inl has⟩

end Ctl
end Sys
end MathEngine
