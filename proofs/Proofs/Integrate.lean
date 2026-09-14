import Proofs.Deriv
/-!
# `integrate` as a verified checker: the semantic reading (M8)

The engine proves `cmdIntegrate_spec`: an accepted antiderivative `F` of `f` has
`norm (diff F x) = ok f`, exactly. Here that becomes the statement the milestone names,
`deriv F = f`, under one hypothesis: that the differentiation the checker ran is sound at the
point — `evalD ρ (diff F x) = evalD ρ g` for the normal form `g` it produced. That hypothesis is
not assumed away; it is what the rule statuses of the check's steps say (M3 for `simp.*`, M4 for
`diff.*`), rule by rule, and the notebook shows them under the `int.check` step. A derivation that
uses only unconditional rules discharges it outright; one that uses `simp.collect-powers` (as the
symbolic-exponent power rule does) carries that rule's side condition.

So the checker is verified in the sense that matters: nothing about the *finder* is trusted, and
what remains to trust is exactly the differentiation, which the notebook already accounts for.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- `deriv (integrate f) = f`: the derivative of an accepted antiderivative, read as a function of
`x`, is the integrand at every point where the check's differentiation was sound. -/
theorem integrate_deriv (norm : Norm) {f : Expr} {x : String} {res : RuleResult}
    (h : (cmdIntegrate norm).apply (.fn "integrate" [f, .var x]) = some res) (hok : res.error = none)
    (ρ : EnvR)
    (hsound : ∀ g sub, norm (MathEngine.D res.result x) = .ok (g, sub) →
      evalD ρ (MathEngine.D res.result x) = evalD ρ g) :
    deriv (fx ρ x res.result) (ρ x) = evalD ρ f := by
  obtain ⟨sub, hn⟩ := cmdIntegrate_spec norm h hok
  rw [← D_eq, ← evalD_diff]
  exact hsound f sub hn

end MathProofs
end
