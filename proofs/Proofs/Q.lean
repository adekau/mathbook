import MathEngine
/-!
# `Q` is Mathlib's `ℚ`

The engine's `Q` wraps core Lean's `Rat` and adds a presentation-only `approx` flag. Mathlib's
`ℚ` is notation for that same `Rat`, so there is nothing to *prove* about the arithmetic: every
operation is Mathlib's operation, definitionally. What the engine must prove is how it *uses*
numbers — the per-rule soundness theorems in `MathEngine/Simp.lean` and, from M3, the ℝ-valued
semantics here. These `rfl`s just make the identification explicit and will fail to compile if
`Q` ever grows its own arithmetic.
-/
namespace MathProofs
open MathEngine

example (a b : Q) : (a + b).val = a.val + b.val := rfl
example (a b : Q) : (a * b).val = a.val * b.val := rfl
example (a : Q) : (-a).val = -a.val := rfl
example (a b : Q) : (a / b).val = a.val / b.val := rfl
example (a : Q) (n : Int) : (a.zpow n).val = a.val ^ n := rfl
/-- The flag never changes the value: two numerals with equal `Rat` are semantically equal. -/
example (a b : Q) (h : a.val = b.val) : Q.eq a b = true := by simp [Q.eq, h]

end MathProofs
