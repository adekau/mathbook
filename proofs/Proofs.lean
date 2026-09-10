import MathEngine
import Proofs.Q
import Proofs.Semantics
/-!
# Proofs about the engine (skeleton)

Nothing in this package is executed. It imports the engine as a library and states theorems
about it. Everything here may be `noncomputable`; ℝ lives here (M3), the engine computes over
ℚ and syntax.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- The split builds: the engine's verified rule is visible from here. -/
theorem simpTop_sound' (e : Expr) : SemEq (simpTop e) e := simpTop_sound e

end MathProofs
end
