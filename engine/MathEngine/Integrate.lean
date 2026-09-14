import MathEngine.PipelineOrder
/-!
# `integrate` as a verified checker (M8)

The finder (`Antiderivative.lean`) guesses; the command (`cmdIntegrate`, Pipeline.lean) accepts a
guess only if differentiating it and normalizing gives the integrand back. This file closes the
knot the pipeline's definition could not: the normalizer the check runs is the pipeline itself with
nested `integrate` refused (`checkNorm`), and the notebook's pipeline is the pipeline with that
checker. Both are `Ordered` by the one theorem `pipelineOrderedWith`, so the check has no step
budget either.

`cmdIntegrate_spec` is the checker's claim, in the engine: an accepted result `F` has
`norm (diff F x) = ok f`, exactly. Its meaning — `deriv F = f` — is `integrate_deriv` in
`proofs/Proofs/Integrate.lean`, under the one hypothesis that the differentiation shown is sound
at the point, which the rule statuses of its steps (M3, M4) say rule by rule.
-/
namespace MathEngine

/-- Inside a check a nested `integrate` is refused rather than searched: one level is enough, and
it is what makes the rule set well-founded. -/
def noIntegrate : Norm := fun _ => .error "integrate: nested integrals are not supported"

/-- The checker: the pipeline with nested `integrate` refused, run with its derivation. -/
def checkNorm : Norm := fun e =>
  match (normalizeT (pipelineRulesWith noIntegrate) (pipelineOrderedWith noIntegrate) e).run #[] with
  | (.error msg, _) => .error msg
  | (.ok out, steps) => .ok (out, if steps.isEmpty then none else some ⟨e, steps, out⟩)

/-- The notebook pipeline. -/
def pipelineRules : List PlainRule := pipelineRulesWith checkNorm

/-- Every rule of the notebook pipeline decreases `μ` on a node whose children are normal. -/
theorem pipelineOrdered : Ordered pipelineRules := pipelineOrderedWith checkNorm

/-- **The checker's claim.** Whatever `integrate(f, x)` returns without error, differentiating it
and normalizing gives back `f` — not something equal to `f`, `f` itself. Nothing about the finder
is assumed. -/
theorem cmdIntegrate_spec (norm : Norm) {f : Expr} {x : String} {res : RuleResult}
    (h : (cmdIntegrate norm).apply (.fn "integrate" [f, .var x]) = some res) (hok : res.error = none) :
    ∃ sub, norm (D res.result x) = .ok (f, sub) := by
  unfold cmdIntegrate at h; simp only [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨hrr, -⟩ := checked_spec rfl hok
  rw [hrr] at hok ⊢
  split at hr
  · cases hr; simp [refuse] at hok
  · rename_i F steps _
    split at hr
    · cases hr; simp [refuse] at hok
    · rename_i g sub hn
      split at hr
      · rename_i heq
        cases hr
        exact ⟨sub, by rw [hn, Expr.beq_eq g f heq]⟩
      · cases hr; simp [refuse] at hok

end MathEngine
