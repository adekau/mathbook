import MathEngine.Rewrite
import MathEngine.Semantics
/-!
# Soundness of `normalize` as a fold over per-rule soundness

If every rule is sound, so is normalization: the derivation is a chain of sound steps, and
soundness is transitive and a congruence. The proof follows the recursion of `normAt` through its
functional induction principle.

The theorem is stated for an arbitrary `Congruence` rather than for one semantics, because the
project gains semantics over time: the integer fragment (`Refines`, below), ℝ (`proofs/`, M3),
derivatives (M4), and whatever a new math module brings (`ARCHITECTURE.md` §4). Each one supplies
the four facts in `Congruence` and gets `normalize_sound_for` for free.
-/
namespace MathEngine
open Expr

/-- What a notion of "this rewrite is sound" must satisfy for soundness to be a fold. `rel a b`
reads *rewriting `a` to `b` preserves meaning*; it need not be symmetric (the integer fragment's
`Refines` is not: a rewrite may become more defined, never less). -/
structure Congruence where
  rel : Expr → Expr → Prop
  refl : ∀ e, rel e e
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  /-- Rewriting each child soundly rewrites the node soundly. -/
  congr : ∀ e cs, RelList rel (children e) cs → rel e (withChildren e cs)
  /-- Reordering a sum's or product's arguments is sound — what `canon` does silently. -/
  canon : ∀ e, rel e (canon e)

def RuleSoundFor (C : Congruence) (r : Rule W) : Prop :=
  ∀ e res, r.apply e = some res → C.rel e res.result

/-- **Soundness is a fold.** If every rule in the set is sound for `C`, normalization is. -/
theorem normAt_sound_for (C : Congruence) (rules : List (Rule W)) (hs : ∀ r ∈ rules, RuleSoundFor C r) :
    (∀ (e : Expr) (path : Path) (acc : Array RawStep), C.rel e (normAt rules e path acc).1.1) ∧
    (∀ (cs : List Expr) (path : Path) (i : Nat) (acc : Array RawStep),
      RelList C.rel cs (normChildren rules cs path i acc).1.1) := by
  apply normAt.mutual_induct rules
    (motive1 := fun e path acc => C.rel e (normAt rules e path acc).1.1)
    (motive2 := fun cs path i acc => RelList C.rel cs (normChildren rules cs path i acc).1.1)
  · -- no rule fires: the result is `canon (withChildren e cs)`
    intro e path acc cs acc₀ hcs hnc e₀ e₁ h₁ hf ih
    simp only [e₁, e₀] at hf
    rw [normAt, hnc]; dsimp only
    rw [hf]; dsimp only
    rw [hnc] at ih
    exact C.trans (C.congr e cs ih) (C.canon _)
  · -- a rule fires, then we recurse on its result
    intro e path acc cs acc₀ hcs hnc e₀ e₁ acc₁ h₁ rule res hr hf hdec acc₂ r hr' hn ih₁ ih₂
    simp only [e₁, e₀] at hf hr
    simp only [acc₂, acc₁, e₁, e₀, dite_eq_ite] at hn ih₂
    rw [normAt, hnc]; dsimp only
    rw [hf]; dsimp only
    rw [hn]; dsimp only
    rw [hn] at ih₂
    rw [hnc] at ih₁
    have hmem := fire_mem rules _ _ hf
    have hrule : C.rel (canon (withChildren e cs)) res.result := hs _ hmem _ _ hr
    exact C.trans (C.trans (C.congr e cs ih₁) (C.canon _)) (C.trans hrule ih₂)
  · intro path i acc; simp [normChildren, RelList]
  · intro path i acc e es c' acc₁ hc hn cs'' acc₂ hcs hnc ih₁ ih₂
    rw [normChildren, hn]; dsimp only
    rw [hnc]; dsimp only
    rw [hn] at ih₁; rw [hnc] at ih₂
    exact ⟨ih₁, ih₂⟩

theorem normalize_sound_for (C : Congruence) (rules : List (Rule W)) (hs : ∀ r ∈ rules, RuleSoundFor C r)
    (e : Expr) (s : Array Step) : C.rel e ((normalize rules e).run' s) := by
  rw [normalize_run]; exact (normAt_sound_for C rules hs).1 e [] #[]

-- ---------------------------------------------------------------------------
-- The integer fragment as a `Congruence`
-- ---------------------------------------------------------------------------

theorem canon_refines (e : Expr) : Refines e (canon e) := by
  intro ρ v h
  cases e with
  | add es => simp only [canon, eval?] at h ⊢; rwa [evalSum?_perm ρ (List.mergeSort_perm es _)]
  | mul es =>
    simp only [canon]
    split
    · exact h
    · simp only [eval?] at h ⊢; rwa [evalProd?_perm ρ (List.mergeSort_perm es _)]
  | _ => exact h

/-- The integer fragment (`engine/MathEngine/Semantics.lean`) packaged as a `Congruence`. -/
def refinesCongruence : Congruence where
  rel := Refines
  refl := Refines.refl
  trans := Refines.trans
  congr := Refines.congr
  canon := canon_refines

def RuleSound (r : Rule W) : Prop := RuleSoundFor refinesCongruence r

theorem normalize_sound (rules : List (Rule W)) (hs : ∀ r ∈ rules, RuleSound r) (e : Expr) (s : Array Step) :
    Refines e ((normalize rules e).run' s) :=
  normalize_sound_for refinesCongruence rules hs e s

end MathEngine
