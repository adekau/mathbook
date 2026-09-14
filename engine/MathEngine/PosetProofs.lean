import MathEngine.Poset
/-!
# The order-world's decisions are right

Every order-world answer is a decision over lists; these say what the decisions mean.
-/
namespace MathEngine
namespace Ord

/-- A poset that passes the check is reflexive, antisymmetric and transitive on its order. -/
theorem checkPartialOrder_none {P : Poset} (h : checkPartialOrder P = none) :
    (∀ x ∈ P.elems, P.rel x x = true) ∧
    (∀ p ∈ P.le, p.1 ≠ p.2 → P.rel p.2 p.1 = false) ∧
    (∀ p ∈ P.le, ∀ q ∈ P.le, p.2 = q.1 → P.rel p.1 q.2 = true) := by
  unfold checkPartialOrder at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · rename_i h2
      split at h
      · simp at h
      · rename_i h3
        have n1 : P.elems.find? (fun x => !P.rel x x) = none := by
          cases hf : P.elems.find? (fun x => !P.rel x x) with
          | none => rfl
          | some x => exact (h1 x hf).elim
        have n2 : P.le.find? (fun (x, y) => x != y && P.rel y x) = none := by
          cases hf : P.le.find? (fun (x, y) => x != y && P.rel y x) with
          | none => rfl
          | some xy => exact (h2 xy.1 xy.2 (by simpa using hf)).elim
        have n3 : (P.le.flatMap fun p => P.le.map fun q => (p, q)).find? (fun ((x, y), (y', z)) => y == y' && !P.rel x z) = none := by
          cases hf : (P.le.flatMap fun p => P.le.map fun q => (p, q)).find? (fun ((x, y), (y', z)) => y == y' && !P.rel x z) with
          | none => rfl
          | some q => exact (h3 q.1.1 q.1.2 q.2.1 q.2.2 (by simpa using hf)).elim
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          have := List.find?_eq_none.mp n1 x hx
          simpa using this
        · intro p hp hne
          have := List.find?_eq_none.mp n2 p hp
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Bool.not_eq_true] at this
          exact this hne
        · intro p hp q hq hpq
          have hm : (p, q) ∈ P.le.flatMap fun p => P.le.map fun q => (p, q) := by
            simp only [List.mem_flatMap, List.mem_map]; exact ⟨p, hp, q, hq, rfl⟩
          have := List.find?_eq_none.mp n3 (p, q) hm
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true, not_and] at this
          simpa using this hpq

/-- Hasse edges are exactly the covers. -/
theorem covers_spec (P : Poset) (x y : String) :
    covers P x y = true ↔ P.lt x y = true ∧ ∀ z ∈ P.elems, ¬ (P.lt x z = true ∧ P.lt z y = true) := by
  simp [covers, List.any_eq_true]

/-- What `sup` finds is an upper bound below every upper bound. -/
theorem sup_spec {P : Poset} {xs : List String} {j : String} (h : sup P xs = some j) :
    j ∈ upperBounds P xs ∧ ∀ v ∈ upperBounds P xs, P.rel j v = true := by
  unfold sup at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa [List.all_eq_true] using this

/-- When `sup` finds nothing, no upper bound is below all the others: there is no least one. -/
theorem sup_none {P : Poset} {xs : List String} (h : sup P xs = none) :
    ∀ j ∈ upperBounds P xs, ∃ v ∈ upperBounds P xs, P.rel j v = false := by
  unfold sup at h
  intro j hj
  have := List.find?_eq_none.mp h j hj
  simpa [List.all_eq_true] using this

/-- `f` applied `n` times. -/
def PMap.iter (f : PMap) : Nat → String → String
  | 0, x => x
  | n + 1, x => f.apply (f.iter n x)

/-- A map that passes the monotonicity check is monotone on the order. -/
theorem monotone_of_none {P : Poset} {f : PMap} (h : monotoneFailure P f = none) :
    ∀ p ∈ P.le, P.rel (f.apply p.1) (f.apply p.2) = true := by
  intro p hp
  have := List.find?_eq_none.mp h p hp
  simpa using this

/-- **Every point of the Kleene chain lies below every fixed point above its start.** With
`x = ⊥`, the chain's last element — a fixed point, as checked — is therefore the least one. -/
theorem iter_le_fixed {P : Poset} {f : PMap} (hm : monotoneFailure P f = none) {y : String}
    (hy : f.apply y = y) : ∀ (n : Nat) (x : String), P.rel x y = true → P.rel (f.iter n x) y = true
  | 0, x, hx => hx
  | n + 1, x, hx => by
    have ih := iter_le_fixed hm hy n x hx
    have := monotone_of_none hm (f.iter n x, y) (by simpa [Poset.rel] using ih)
    simp only [PMap.iter]
    rw [hy] at this
    exact this

/-- The chain `iterate` returns is made of iterates of its start. -/
theorem iterate_mem {P : Poset} {f : PMap} {start : String} :
    ∀ z ∈ iterate P f start, ∃ n, z = f.iter n start := by
  unfold iterate
  suffices ∀ (k : Nat) (x : String) (acc : List String) (m : Nat), x = f.iter m start →
      (∀ z ∈ acc, ∃ n, z = f.iter n start) → ∀ z ∈ iterate.go f k x acc, ∃ n, z = f.iter n start by
    intro z hz
    exact this P.elems.length start [start] 0 rfl (fun z hz => ⟨0, by simp only [PMap.iter]; simpa using hz⟩) z hz
  intro k
  induction k with
  | zero => intro x acc m hx hacc z hz; simp [iterate.go] at hz; exact hacc z hz
  | succ k ih =>
    intro x acc m hx hacc z hz
    simp only [iterate.go] at hz
    split at hz
    · exact hacc z (List.mem_reverse.mp hz)
    · exact ih (f.apply x) (f.apply x :: acc) (m + 1) (by simp [PMap.iter, hx])
        (fun w hw => by
          rcases List.mem_cons.mp hw with rfl | hw
          · exact ⟨m + 1, by simp [PMap.iter, hx]⟩
          · exact hacc w hw) z hz

end Ord
end MathEngine
