import MathEngine.Rewrite
import MathEngine.Semantics
/-!
# Soundness of `normalize` as a fold over per-rule soundness

If every rule refines its input (`RuleSound`), then so does normalization: the derivation is a
chain of sound steps, and refinement is transitive and a congruence. The proof follows the
recursion of `normAt` through its functional induction principle.
-/
namespace MathEngine
open Expr

def RuleSound (r : Rule W) : Prop := ∀ e res, r.apply e = some res → Refines e res.result

theorem canon_refines (e : Expr) : Refines e (canon e) := by
  intro ρ v h
  cases e with
  | add es => simp only [canon, eval?] at h ⊢; rwa [evalSum?_perm ρ (List.mergeSort_perm es _)]
  | mul es => simp only [canon, eval?] at h ⊢; rwa [evalProd?_perm ρ (List.mergeSort_perm es _)]
  | _ => exact h

theorem normAt_sound (rules : List (Rule W)) (hs : ∀ r ∈ rules, RuleSound r) :
    (∀ (e : Expr) (path : Path) (acc : Array RawStep), Refines e (normAt rules e path acc).1.1) ∧
    (∀ (cs : List Expr) (path : Path) (i : Nat) (acc : Array RawStep), RefinesList cs (normChildren rules cs path i acc).1.1) := by
  apply normAt.mutual_induct rules
    (motive1 := fun e path acc => Refines e (normAt rules e path acc).1.1)
    (motive2 := fun cs path i acc => RefinesList cs (normChildren rules cs path i acc).1.1)
  · -- no rule fires: result is canon (withChildren e cs)
    intro e path acc cs acc₀ hcs hnc e₀ e₁ h₁ hf ih
    simp only [e₁, e₀] at hf
    rw [normAt, hnc]; dsimp only
    rw [hf]; dsimp only
    rw [hnc] at ih
    exact (Refines.congr e cs ih).trans (canon_refines _)
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
    have hrule : Refines (canon (withChildren e cs)) res.result := hs _ hmem _ _ hr
    exact ((Refines.congr e cs ih₁).trans (canon_refines _)).trans (hrule.trans ih₂)
  · intro path i acc; simp [normChildren, RefinesList]
  · intro path i acc e es c' acc₁ hc hn cs'' acc₂ hcs hnc ih₁ ih₂
    rw [normChildren, hn]; dsimp only
    rw [hnc]; dsimp only
    rw [hn] at ih₁; rw [hnc] at ih₂
    exact ⟨ih₁, ih₂⟩

theorem normalize_sound (rules : List (Rule W)) (hs : ∀ r ∈ rules, RuleSound r) (e : Expr) (s : Array Step) :
    Refines e ((normalize rules e).run' s) := by
  rw [normalize_run]; exact (normAt_sound rules hs).1 e [] #[]

end MathEngine
