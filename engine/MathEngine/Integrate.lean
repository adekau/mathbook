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
`norm (dist (identNorm (norm (diff F x)))) = norm (dist (identNorm f))`, exactly (`dist` is
`expand`'s distribution and `identNorm` rewrites `cos²` and `exp(u)^k`; both are proved sound, and
they are there because the pipeline neither distributes a numeral over a sum nor applies those two
identities). Its meaning — `deriv F = f` — is `integrate_deriv` in
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
gives a normal form `g` which, expanded and normalized, is the same term as `f` expanded and
normalized. Nothing about the finder is assumed. -/
theorem cmdIntegrate_spec (norm : Norm) {f : Expr} {x : String} {res : RuleResult}
    (h : (cmdIntegrate norm).apply (.fn "integrate" [f, .var x]) = some res) (hok : res.error = none) :
    ∃ g sub g' s₁ s₂, norm (D res.result x) = .ok (g, sub) ∧
      norm (Expand.dist (Expand.identNorm g)) = .ok (g', s₁) ∧
      norm (Expand.dist (Expand.identNorm f)) = .ok (g', s₂) := by
  unfold cmdIntegrate at h; simp only [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨hrr, -⟩ := checked_spec rfl hok
  rw [hrr] at hok ⊢
  split at hr
  · cases hr; simp [refuse] at hok
  · rename_i F₀ steps _
    split at hr
    · cases hr; simp [refuse] at hok
    · rename_i F _ _
      split at hr
      · cases hr; simp [refuse] at hok
      · rename_i g sub hn
        split at hr
        · rename_i g' subg f' s₂ hg hf
          split at hr
          · rename_i heq
            cases hr
            exact ⟨g, sub, g', subg, s₂, hn, hg, by rw [hf, Expr.beq_eq g' f' heq]⟩
          · cases hr; simp [refuse] at hok
        · cases hr; simp [refuse] at hok

end MathEngine
