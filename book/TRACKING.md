# Tracking log — what the book needs, in build order

M0 wasm spike (book/SPIKE-RESULTS.md) — DONE 2026-09-10 on Lean v4.33.1: runtime + Init built from source for wasm32, 1.5 MB, 96 ms to first reply in the browser, no COOP/COEP. One upstream 32-bit runtime bug found and patched (string_to_list_core), to report.
M1 Lean engine parity (book/M1-BRIEF.md) — IN PROGRESS.
   1. DONE 2026-09-10: `Q` over core `Rat` with the approximate flag, full parser with spans, two-target printer with
      `\htmlData` paths, `lake test` driver (55 cases ported from `engine.test.mjs`), `proofs/` skeleton + `scripts/check-engine-deps.sh`.
   2. DONE 2026-09-10: traced rewriter `MathEngine/Rewrite.lean`. Option (a) from the brief: `Rule W` carries
      `decreasing : apply e = some r → measure W r.result < measure W e` for a weighted node count `measure W`
      (weights are head-only, ≥ 1); `normalize` is well-founded on `(measure, size, phase)`, never `partial`.
      Additivity (`measure_withChildren`) and permutation invariance (`measure_canon`) are proved once for all
      weights, so canonical argument order runs silently inside the loop instead of as a rule.
      DECISION TO REVISIT BEFORE M5 (flagged per the brief): a single additive measure cannot cover the combined
      notebook pipeline (`diff.*` duplicates subterms — product/chain rules — and commands like `expand` grow
      terms). Those rule sets run on `normalizeFuel` (total, explicit fuel, reports exhaustion) until M5 replaces
      it with a polynomial/RPO ordering. The `simp.*` set gets a proven measure in step 3.
   3. DONE 2026-09-10: `MathEngine/SimpRules.lean` (seven `simp.*` rules as `Rule simpW`, termination proved per rule
      under weights num 2 / add,mul 4 / pow 5 / var,fn,matrix 8), `MathEngine/SimpSound.lean` (per-rule soundness on the
      integer fragment under the Option-valued `eval?`; `simplify_sound : Refines e (simplify0 e)` is the fold through
      `normAt_sound` in `RewriteSound.lean`; axioms: propext, Classical.choice, Quot.sound). Derivations reach the work panel via
      `showWork`. Deviations from `simplify.ts`, all documented in the file header: bigBase guards on the collect rules,
      `(b^m)^n` only for numeric `m`, exact roots only with unit numerators, `(ab)^n` moved to the expand set.
   4. DONE 2026-09-10: `DiffRules.lean`, `LinAlg.lean` (matrix rules + step-recording `rref`), `ExpandRules.lean`,
      `Numeric.lean` (`N`, `subst`; floats rounded to 15 significant digits like the reference), `Session.lean`
      (commands as rules, `let` env, per-cell derivations, `explain` with the prefix heuristic). The pipeline
      `cmd ++ diff ++ la ++ simp` runs on `normalizeFuel` (fuel 10 000, rule refusals become eval errors).
      `handleS : Store → String → Store × String` is the entry point; the C shim keeps the store in a static,
      `Main.lean` threads it through the stdio loop. All 13 reference test groups pass in `lake test` (109 cases),
      plus the native stdio test and the wasm smoke test. M1 is complete; M2 (wire-level differential test) next.
M2 DONE 2026-09-10: wire-level differential test (scripts/difftest.mjs, 147 sources in one session, text + LaTeX with
   paths + value trees + errors + bindings, zero mismatches) then reference-ts deleted. Its answers are `engine/Tests/golden.tsv`,
   replayed by `lake test`. Found by the diff: matrix products must not be canonically sorted; `(ab)^n` and `(b^m)^n` with
   symbolic `m` are parity rules in the fuel pipeline only. The HTTP host now fronts the native Lean engine.
M3 DONE 2026-09-10: Mathlib pinned at release tag v4.33.1 in `proofs/` — its lean-toolchain is exactly ours, so no
   toolchain move and no engine port. (Mathlib *master* is on v4.34.0-rc2, ahead of stable, so "pin to master" from the
   M1 brief would have been wrong; pin to the release tag whose toolchain matches, and bump both together.)
   `proofs/Proofs/Semantics.lean`: `evalR` over ℝ (rpow, Real.sin/log/sqrt, Mathlib junk conventions), `SemEqR`,
   `SemEqROn`, and the bridge `evalR_of_eval?` — wherever the integer fragment is defined, ℝ agrees, so M1's
   `simplify_sound` was a restriction of the truth. `proofs/Proofs/SimpReal.lean`: every `simp.*` rule gets its ℝ theorem.
   FINDING, worth a chapter: two rules are *not* unconditionally sound over ℝ, and the refutations are proved, not just
   unproven. `simp.collect-powers` turns `x·x⁻¹` into `x⁰`, i.e. 0 into 1 at x = 0 (`not_collectPowers_soundR`); it is
   sound exactly where the merged base is positive (`collectPowers_soundR_on`). `simp.function` turns `exp(ln x)` into
   `x`, i.e. 1 into -1 at x = -1 (`not_functionRules_soundR`), because `Real.log` is even. Both are the standard CAS
   convention (Mathematica simplifies `x/x` to 1 too), so the engine keeps them; what changed is that the assumption is
   now written down. The other five rules are unconditionally sound and `normalizeR_sound` folds them.
   Engine change: `RewriteSound`'s fold is now stated for an abstract `Congruence`, so ℝ (and M4's derivatives, and any
   future module) reuse the M1 theorem instead of re-proving it. Axioms: propext, Classical.choice, Quot.sound only.
M4 DONE 2026-09-10: `proofs/Proofs/Deriv.lean`. `evalR` could not take the `diff` case: a `diff` node's second child is a
   *binder*, and `Expr` does not mark binder positions, so `.var x` and `.add [.var x]` denote the same real while only one
   reads as "the variable we differentiate along" — a semantics interpreting `diff` cannot satisfy `SemEqR.congr`, the law
   M3's fold rests on. So M4 *extends* instead: `evalD` reads `diff` via Mathlib's `deriv`, and `evalD_eq_evalR` proves the
   two agree on every diff-free term. Third layer of the same pattern: eval? ⊂ evalR ⊂ evalD, each shown a restriction of
   the next. Supporting lemmas: `upd`/`upd_self`/`upd_comm` and `evalD_upd_not_free` (rebinding a variable a term does not
   mention changes nothing).
   Unconditional: `diff.constant`, `diff.variable`, `diff.constant-multiple` (`deriv_const_mul_field` needs no
   differentiability). Conditional, hypothesis stated: `diff.sum` (every summand), `diff.product` (two factors),
   `diff.power` (natural exponent, differentiable base — `Real.rpow_natCast` avoids any positivity), `diff.chain` for sin,
   cos, exp. `not_diff_sum_sound` *proves* the sum rule is not unconditional: at 0, `|x| + x` gives 1 where the derivative
   does not exist — the `diff.*` analogue of M3's `not_collectPowers_soundR`.
   Not claimed: `diff.higher-order` is an abbreviation (it eliminates the three-argument form, so there is nothing to
   prove); `diff.matrix` is proved but vacuous while matrices carry no ℝ value — real content is M7. `ln`/`tan` chain
   cases need a domain condition and are open, as is `diff.power` for real exponents.
   The engine reports all of this through `engine.capabilities.ruleStatus`, so the notebook's proof-status panel now says
   "conditional" with the actual hypothesis instead of "no soundness theorem yet". Axioms: the three standard ones.
M5 termination: measure-decreasing proof replaces the step budget (connects to the order-theory book).
M6 origin tracking for `explain` (van Deursen–Klint–Tip 1993); current path-prefix heuristic over-approximates.
M7 linear algebra over ℚ verified (elimination preserves solution set).
M8 integration as a verified *checker* (`deriv (integrate f) = f`), not a verified integrator.
Open: radical simplification (sqrt 8 → 2√2), user functions with parameters, plotting, design file import.
Six-month cut line: M5.
