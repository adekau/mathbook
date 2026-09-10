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
M2 wire-level differential test reference-ts ⇄ engine-lean; then delete reference-ts.
M3 Mathlib: semantics over ℝ (spec only, noncomputable); each `simp.*` rule gets a soundness theorem.
M4 `HasDerivAt` proofs for each `diff.*` rule.
M5 termination: measure-decreasing proof replaces the step budget (connects to the order-theory book).
M6 origin tracking for `explain` (van Deursen–Klint–Tip 1993); current path-prefix heuristic over-approximates.
M7 linear algebra over ℚ verified (elimination preserves solution set).
M8 integration as a verified *checker* (`deriv (integrate f) = f`), not a verified integrator.
Open: radical simplification (sqrt 8 → 2√2), user functions with parameters, plotting, design file import.
Six-month cut line: M5.
