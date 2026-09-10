# Tracking log — what the book needs, in build order

M0 wasm spike (book/SPIKE.md) — DONE 2026-09-10 on Lean v4.33.1: runtime + Init built from source for wasm32, 1.5 MB, 96 ms to first reply in the browser, no COOP/COEP. One upstream 32-bit runtime bug found and patched (string_to_list_core), to report.
M1 Lean engine parity: `Q` normalization/arithmetic, full parser (calls, implicit mul, matrices), printer with `-`/`/` recovery,
   recursive `simp0` (spike's `simpTop` is root-only), traced rewriter as `StateM (Array Step)` with `termination_by` on `size`,
   diff + linalg rules ported from `reference-ts`, session state threaded through `handle`. Port `engine.test.mjs` to `lake test`.
M2 wire-level differential test reference-ts ⇄ engine-lean; then delete reference-ts.
M3 Mathlib: semantics over ℝ (spec only, noncomputable); each `simp.*` rule gets a soundness theorem.
M4 `HasDerivAt` proofs for each `diff.*` rule.
M5 termination: measure-decreasing proof replaces the step budget (connects to the order-theory book).
M6 origin tracking for `explain` (van Deursen–Klint–Tip 1993); current path-prefix heuristic over-approximates.
M7 linear algebra over ℚ verified (elimination preserves solution set).
M8 integration as a verified *checker* (`deriv (integrate f) = f`), not a verified integrator.
Open: radical simplification (sqrt 8 → 2√2), user functions with parameters, plotting, design file import.
Six-month cut line: M5.
