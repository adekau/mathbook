# Architecture

Decisions that outlive any milestone. Milestone-specific plans live in `book/`.

## 1. The spine

One math engine, written in Lean 4, compiled to native (CLI, stdio server) and to wasm32
(web worker). Every host is a shim around one pure function `handle : String → String`
(`engine/MathEngine/Rpc.lean`). The frontend talks to *some* engine through
`packages/protocol` and never learns which one beyond `engine.capabilities`.

The TypeScript reference engine the Lean engine was ported from was deleted after M2 (last present
in commit 680e360). Its test suite lives on in `engine/Tests/Main.lean`
and its answers on a 147-source corpus in `engine/Tests/golden.tsv`, produced by a wire-level
differential test with zero mismatches.

## 2. Protocol rules

1. Everything crossing the boundary is plain JSON: `WireExpr`, `Rendered`, `Derivation`.
2. Transport is abstract (worker `postMessage`, HTTP, WebSocket, stdio). It moves JSON-RPC 2.0
   messages and does not know what they mean.
3. Expressions are trees with *paths* (child-index lists). Paths are the provenance key that lets
   the frontend map "the thing I selected" back to "the step that produced it".
4. The engine is stateful per session (a notebook), stateless across sessions.
5. New capabilities are added as optional fields, never by changing existing ones, so an old
   frontend keeps working against a new engine and vice versa.

## 3. The engine

- `Expr` is deliberately small (`num var add mul pow fn matrix`). Subtraction, division and
  negation are derived forms; the printer recovers the notation. Fewer node kinds means fewer
  rewrite rules and fewer proof cases.
- **Numbers.** `Q` wraps core Lean's `Rat` (normalized by construction) plus a presentation-only
  "approximate" flag. Mathlib's `ℚ` *is* that `Rat`, so the identification is `rfl`
  (`proofs/Proofs/Q.lean`). There is nothing to prove about the arithmetic; what must be proven is
  how the engine uses it, which is the per-rule soundness theorems.
- **Show work is not reconstructed after the fact.** Rewriting records every rule firing as a
  `Step` with the whole term before and after and the path where it fired. The derivation *is*
  the computation, viewed as data.
- **Termination is a proof obligation, not a budget.** A rule bundles a proof that it strictly
  decreases a measure; `normalize` is well-founded on that measure and never `partial`. The
  verified `simplify` uses one additive measure (`Rewrite.lean`). The whole notebook pipeline —
  commands, `diff.*`, `la.*`, `simp.*`, the two parity rules, the radical rules — uses the six-tier ordering of
  `Order.lean` and the innermost rewriter `normalizeT` (`Terminate.lean`), whose obligation is
  conditional: a rule must decrease the ordering *on a node whose children are already normal*.
  That hypothesis is what lets the product rule duplicate its body. The theorem is
  `pipelineOrdered` (`PipelineOrder.lean`), one lemma per rule. Rules that delegate to unverified
  code (commands, matrix arithmetic) have their outputs *checked* for the tier they must decrease
  rather than proved. There is no step budget anywhere: `expand` distributes by a total function
  (`Expand.dist`, proved sound over ℝ in `proofs/Proofs/Expand.lean`) and the pipeline collects
  the result.
- **Elimination is verified over ℚ by construction.** `LinAlgQ.lean` writes Gauss–Jordan as a
  list of the three elementary row operations, each invertible (the degenerate parameters are the
  identity), and proves `sol_rref`: the reduced matrix has the input's solution set. The `rref`
  command replays those operations into its steps when every entry is a numeral; symbolic entries
  fall back to the simplifier-driven algorithm, whose steps are named `la.row-*.symbolic` and
  reported unverified. That the result is in reduced row echelon form is `rref_isRref`
  (`LinAlgRref.lean`), a column-by-column invariant.
- **Radicals take the form the ordering can afford.** `2√2` as a term is `2 · 2^(1/2)`, heavier
  than `8^(1/2)` under any bounded numeral weight, so the engine's normal form is the single power
  `2^(3/2)` (a sixth tier, the magnitudes of integer numerals, orders that step), radicals with the
  same square-free part collect in sums and same-index radicals multiply in products (both decrease
  `M`), and the printer displays the single-power form the textbook way. `RadicalRules.lean`.
- **Plots are sampled by the engine and drawn by the notebook.** `engine.plot` simplifies the
  function under the session, records the cell, and returns a uniform sample with `null` where the
  value is not finite; the notebook's SVG and the studio's graph shot are presentation only.
- **Integration is checked, not found.** `Antiderivative.lean` guesses an antiderivative with a
  few textbook rules and proves nothing; `cmdIntegrate` differentiates the guess with the pipeline
  and accepts it only if the normal form is the integrand itself. `cmdIntegrate_spec` states that;
  `proofs/Proofs/Integrate.lean` reads it as `deriv F = f` wherever the differentiation shown is
  sound, which the statuses of its steps report. Because a rule set cannot contain a rule that
  normalizes with that set, the pipeline is `pipelineRulesWith norm`, generic in the checker's
  normalizer, and `Integrate.lean` closes the knot: the checker is the pipeline with nested
  `integrate` refused, and the notebook's pipeline is the pipeline with that checker.
- **Soundness is a fold, over whichever semantics you bring.** `RewriteSound.normalize_sound_for`
  is stated for an abstract `Congruence` (reflexive, transitive, a congruence under `withChildren`,
  invariant under `canon`). Supply those four facts for a new semantics and normalization's
  soundness follows without touching the rewriter. The integer fragment and ℝ are two instances.
- **Semantics are added in layers, never edited.** `eval?` (integer fragment, M1) ⊂ `evalR` (ℝ, M3) ⊂ `evalD` (ℝ with
  derivatives, M4), each with a theorem that the previous one is a restriction of it. A new layer extends rather than
  replaces because the earlier theorems are stated against the earlier semantics; widening in place would silently
  restate them. It is also forced here: `evalR` cannot interpret `diff`, whose second child is a binder that `Expr`
  does not distinguish from a value, and a semantics reading it breaks the congruence M3's fold needs.
- **A rule that needs a side condition says so.** Over ℝ, `simp.collect-powers` and part of
  `simp.function` are only sound away from `0` (see `book/TRACKING.md`, M3). The engine keeps the
  usual computer-algebra behaviour; `proofs/` states the hypothesis and *proves* that no
  unconditional theorem exists. Silence is not an option: either a rule has an unconditional
  theorem or its condition is written down.
- **Two packages.** `engine/` is executable code and goes into the wasm build: it imports Init
  (Std/Batteries allowed) and never Mathlib. `proofs/` is theorems only, may be `noncomputable`,
  requires `engine/` and (from M3) Mathlib. `scripts/check-engine-deps.sh` enforces the split.

## 4. Adding a math area (group theory, category theory, ...)

The rewriter, derivations, paths and the protocol are module-agnostic: they work on any tree
with `children`/`withChildren`. What a module brings is:

| Concern | Where it plugs in |
|---|---|
| Syntax (literals like a cycle `(1 2 3)`, new commands) | parser extension + reserved `fn` names |
| Node kinds | today: `fn name args` with a module-reserved name; when a second module lands, `Expr` gains typed node kinds per module rather than growing the closed inductive ad hoc |
| Rules with explanations | a `RuleSet` with its own measure and obligations |
| Semantics and proofs | a module in `proofs/` (the engine computes; `proofs/` interprets) |
| Rendering | printer cases (text/LaTeX) plus *visual specs* (§5) |

Explanations are Markdown with `$latex$`, carried on every step. A module that cannot explain a
rule in one sentence has the rule at the wrong granularity.

## 4a. The notebook shell

`apps/notebook` implements the second export of the "Notebook - GitHub" artboard, checked in under
`design/v2/` (the first export, and the Cloud9 palette the shell briefly used, remain under
`design/`). Two palettes — warm dark and paper light — are token sets on `html[data-theme]` in
`index.html`; the toggle in the title bar persists the choice in `localStorage`. The cells sit on a
"paper" whose grain and mottle are inline SVG turbulence filters, and are set in Literata; the
chrome around them stays in the system sans. Re-skinning is a change to the token blocks.

The page owns no mathematics. It does not parse, print, or simplify: every expression on screen is
LaTeX the engine produced, every rule name and explanation is the engine's, and the proof status
beside each step comes from `engine.capabilities.ruleStatus` rather than a list in the frontend
that could drift from `proofs/`. The one thing the page derives from source text is a cell's *kind*
label, which is presentation only.

**Manim Studio** is the third tab. "→ Scene" on an evaluated cell turns its derivation into shots:
the statement, then each step's `afterRendered` term (an optional field on `Step`, per protocol
rule 5). The page adds what a storyboard needs and nothing more — order, on/off, an animation name,
a duration — previews a shot by matching KaTeX glyphs between consecutive terms (longest common
subsequence, then interpolated position and opacity, a browser-side stand-in for
`TransformMatchingTex`), and prints the Python a Manim user would run. Rendering the video is
Manim's job, outside the browser.

## 5. Visuals

The engine never draws. It emits **visual specs**: declarative JSON next to `rendered`
(`EvaluateResult.visuals`, reserved in the protocol, empty until a module uses it): a Cayley
table, a graph, a commutative diagram, sampled plot data, a matrix heat map. The frontend owns
rendering (SVG/canvas/WebGL) and can offer several renderers for one spec. This keeps the engine
pure and portable (wasm has no canvas), keeps proofs about what is *shown* possible (the spec is
data the engine can reason about), and lets exports (§6) reuse the same specs.

## 6. Export

Text and LaTeX come from the engine (`Rendered`). Everything else is a consumer of the wire data,
implemented outside the engine:

- images: render LaTeX (KaTeX/MathJax) or a visual spec to SVG/PNG in the frontend or a headless host;
- manim / animation: a generator from `Derivation` JSON, using each step's whole-term `before`/`after`
  and `path` to animate the rewrite. This is why derivations stay complete and why origin tracking
  (`Origin.lean`, M6) matters beyond `explain`: morphing a subterm needs to know it is "the same"
  subterm. `explain` traces a position backwards through the steps — its own origin outside a
  redex (a theorem), the equal subterms of the redex inside the contractum, or *created* — and
  reports one relation per step (`created` / `copied` / `contains`).

Export formats are added as packages under `packages/` (e.g. `packages/export-manim`); the engine
does not change.

## 7. Toolchain

Lean is pinned in `engine/lean-toolchain` and `proofs/lean-toolchain` (kept equal). Policy: the
latest stable Lean for which a **Mathlib release tag** exists, bumped manually, with
`proofs/lakefile.toml`'s Mathlib `rev` bumped in the same commit. Pin to the tag, not to `master`:
Mathlib master tracks release candidates (it was on `v4.34.0-rc2` while stable was `v4.33.1`), and
the tag `vX.Y.Z` is exactly the Mathlib that targets `leanprover/lean4:vX.Y.Z`.

Mathlib lives only in `proofs/`. `lake exe cache get` there fetches prebuilt oleans (~5 GB;
building from source takes hours). The wasm runtime is built from source for the pinned tag
(`scripts/build-lean-wasm-runtime.sh`, results in `book/SPIKE-RESULTS.md`), cached under
`engine/toolchains/<tag>` and keyed by tag.
