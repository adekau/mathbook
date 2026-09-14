import MathEngine.Lambda
/-!
# What is proved about the λ-world so far

Two facts the notebook relies on, both Init-only:

* `substRaw_freeVars`: capture-free substitution introduces no free variable that was not already
  free in the argument or the body — the invariant behind "`e[x := s]` has the free variables of
  `e` minus `x`, plus those of `s`".
* `readChurch_church`: the reader that labels a normal form "the Church numeral n" is right on the
  numerals the engine itself builds.

Not yet proved: that `freshen` preserves α-equivalence, hence that a β-step under an α-renaming
is a β-step of the original; and that the de Bruijn view commutes with β. The notebook reports the
β-steps as unverified for that reason.
-/
namespace MathEngine
namespace Lam

theorem mem_freeVars_app {z : String} {a b : Term} :
    z ∈ freeVars (.app a b) ↔ z ∈ freeVars a ∨ z ∈ freeVars b := by
  simp [freeVars, List.mem_eraseDups, List.mem_append]

theorem mem_freeVars_lam {z y : String} {e : Term} :
    z ∈ freeVars (.lam y e) ↔ z ∈ freeVars e ∧ z ≠ y := by
  simp [freeVars, List.mem_filter]

/-- Substitution introduces no new free variables. -/
theorem substRaw_freeVars (x : String) (s : Term) : ∀ (e : Term) (z : String),
    z ∈ freeVars (substRaw x s e) → z ∈ freeVars s ∨ (z ∈ freeVars e ∧ z ≠ x)
  | .var y, z, h => by
    simp only [substRaw] at h
    split at h
    · exact Or.inl h
    · rename_i hyx
      simp only [freeVars, List.mem_singleton] at h ⊢
      subst h; exact Or.inr ⟨rfl, by simpa using hyx⟩
  | .app a b, z, h => by
    simp only [substRaw] at h
    rcases mem_freeVars_app.mp h with h | h
    · rcases substRaw_freeVars x s a z h with h | ⟨h, hz⟩
      · exact Or.inl h
      · exact Or.inr ⟨mem_freeVars_app.mpr (Or.inl h), hz⟩
    · rcases substRaw_freeVars x s b z h with h | ⟨h, hz⟩
      · exact Or.inl h
      · exact Or.inr ⟨mem_freeVars_app.mpr (Or.inr h), hz⟩
  | .lam y e, z, h => by
    simp only [substRaw] at h
    split at h
    · rename_i hyx
      have hyx' : y = x := by simpa using hyx
      obtain ⟨hz, hzy⟩ := mem_freeVars_lam.mp h
      exact Or.inr ⟨h, hyx' ▸ hzy⟩
    · obtain ⟨hz, hzy⟩ := mem_freeVars_lam.mp h
      rcases substRaw_freeVars x s e z hz with h' | ⟨h', hzx⟩
      · exact Or.inl h'
      · exact Or.inr ⟨mem_freeVars_lam.mpr ⟨h', hzy⟩, hzx⟩

theorem readChurch_go_church : ∀ n, readChurch.go "f" "x" (church.go n) = some n
  | 0 => by simp [church.go, readChurch.go]
  | n + 1 => by simp [church.go, readChurch.go, readChurch_go_church n]

/-- The reading "the Church numeral n" is right on the numerals the engine builds. -/
theorem readChurch_church (n : Nat) : readChurch (church n) = some n := by
  simp [church, readChurch, readChurch_go_church]

end Lam
end MathEngine
