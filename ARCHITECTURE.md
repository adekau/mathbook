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
  decreases a measure; `normalize` is well-founded on that measure and never `partial`. Where a
  rule set has no proven measure yet, the fallback is explicit fuel, recorded in
  `book/TRACKING.md` as debt to be paid in M5, never silently.
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
  and `path` to animate the rewrite. This is why derivations stay complete and why M6 (origin
  tracking, stable subterm identities across steps) matters beyond `explain`: morphing a subterm
  needs to know it is "the same" subterm.

Export formats are added as packages under `packages/` (e.g. `packages/export-manim`); the engine
does not change.

## 7. Toolchain

Lean is pinned in `engine/lean-toolchain` and `proofs/lean-toolchain` (kept equal). Policy: latest
stable, bumped manually; from M3 the pin equals Mathlib's. The wasm runtime is built from source for
the pinned tag (`scripts/build-lean-wasm-runtime.sh`, results in `book/SPIKE-RESULTS.md`), cached under
`engine/toolchains/<tag>` and keyed by tag.
