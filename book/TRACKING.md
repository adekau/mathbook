# Tracking log — what the book needs, in build order

M0 wasm spike (book/SPIKE-RESULTS.md) — DONE 2026-09-10 on Lean v4.33.1: runtime + Init built from source for wasm32, 1.5 MB, 96 ms to first reply in the browser, no COOP/COEP. One upstream 32-bit runtime bug found and patched (string_to_list_core), to report.
M1 Lean engine parity (book/M1-BRIEF.md) — IN PROGRESS.
   1. DONE 2026-09-10: `Q` over core `Rat` with the approximate flag, full parser with spans, two-target printer with
      `\htmlData` paths, `lake test` driver (55 cases ported from `engine.test.mjs`), `proofs/` skeleton + `scripts/check-engine-deps.sh`.
   2. traced rewriter — termination by a per-rule measure obligation (brief option a); see the step-2 note when it lands.
   3. `simp.*` rules with per-rule soundness; derivations reach the work panel.
   4. `diff.*`, `la.*`, `rref`, session state through `handle`.
M2 wire-level differential test reference-ts ⇄ engine-lean; then delete reference-ts.
M3 Mathlib: semantics over ℝ (spec only, noncomputable); each `simp.*` rule gets a soundness theorem.
M4 `HasDerivAt` proofs for each `diff.*` rule.
M5 termination: measure-decreasing proof replaces the step budget (connects to the order-theory book).
M6 origin tracking for `explain` (van Deursen–Klint–Tip 1993); current path-prefix heuristic over-approximates.
M7 linear algebra over ℚ verified (elimination preserves solution set).
M8 integration as a verified *checker* (`deriv (integrate f) = f`), not a verified integrator.
Open: radical simplification (sqrt 8 → 2√2), user functions with parameters, plotting, design file import.
Six-month cut line: M5.
