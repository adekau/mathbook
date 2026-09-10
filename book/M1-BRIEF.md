# M1 brief — Lean engine parity

Read with `book/TRACKING.md` and `book/SPIKE-RESULTS.md`. This file records decisions
already made; do not relitigate them without asking.

## Decisions

**Two packages.** Mathlib must never enter the wasm build (the runtime script emits C for
every imported module; Init alone was 631 modules).

```
engine/   lean_lib MathEngine — executable code only. Imports Init (and Std if needed).
          This is what native + wasm builds compile. No Mathlib, ever.
proofs/   separate Lake package. Requires `engine` (path dependency) and mathlib.
          Theorems only, `noncomputable section` throughout. ℝ lives here; the engine
          computes over ℚ and syntax. Added in M3; create the skeleton now so the split
          is enforced from the first commit (a CI check: `engine/` must build with no
          `require` other than std/batteries).
```

**Toolchain policy.** Pin `engine/lean-toolchain`; bump manually and occasionally. From M3
on, the pin must equal Mathlib's `lean-toolchain` (Mathlib lags stable). Key the runtime
cache in `engine/toolchains/` by tag rather than deleting on bump.

**Std in the engine.** Allowed, but `build-lean-wasm-runtime.sh` currently emits C for Init
only. Either extend it to Std modules or stay on Init for M1 (assoc list for session state is
fine). Check whether 4.33's Std/Batteries ships `Rat` before writing `Q` arithmetic; do not
hand-roll a normalized rational with proofs unless nothing suitable exists.

**Spec is `packages/reference-ts`.** Port its tests, not its structure. It is deleted after M2.

## Order (each step leaves the notebook runnable)

1. **Numbers, parser, printer.** `Q`/`Rat` arithmetic; full grammar from `parser.ts`
   (calls, implicit multiplication, matrices, `let`); printer with `-`/`/`/`sqrt` recovery and
   `\htmlData{path=…}` wrapping, from `printer.ts`. Port `engine.test.mjs` cases to `lake test`
   as you go.
2. **Traced rewriter.** The core of the book. Signatures to start from:

   ```lean
   structure Explanation where
     rule : String
     text : String        -- Markdown + $latex$, the *why*

   /-- A rule inspects one node. `none` = does not apply. -/
   abbrev Rule := Expr → Option (Expr × Explanation)

   structure Step where
     rule : String
     explanation : String
     path : List Nat      -- child indices from the root
     before : Expr        -- whole term
     after : Expr         -- whole term
     sub : Option Derivation := none   -- nested (rref row ops, expand)

   abbrev TraceM := StateM (Array Step)

   /-- Innermost strategy: children first, then rules at the node until quiescent,
       re-normalizing children after a rule fires. -/
   def normalize (rules : List Rule) : Expr → TraceM Expr
   ```

   Termination is the real work. The TS version hides it behind a 10 000-step budget.
   Options, in order of preference:
   a. Well-founded on a measure each rule strictly decreases (`size`, or a lexicographic
      pair `(size, #non-canonical nodes)` once `sort`/`flatten` are in play — those don't
      decrease `size`). Requires a per-rule proof obligation `measure (rule e) < measure e`
      bundled into `Rule`. This is the honest version and chapter material: it is the
      order-theoretic content of "why simplification terminates".
   b. Fuel (`Nat`) threaded explicitly, with the proof that fuel is sufficient deferred.
      Acceptable scaffolding for step 2 if (a) blocks progress; replace in M5.
   Do not use `partial` for `normalize` — that forfeits every theorem about it.
3. **`simp.*` rules** ported from `simplify.ts`, each as a `Rule`; `simp0_sound` becomes
   a fold over per-rule soundness against `evalZ` (Int fragment; ℝ is M3). Derivations now
   reach the work panel — wire `derivation` into `engine.evaluate` responses.
4. **`diff.*` and `la.*` rules**, `rref` as a Step-recording algorithm, session state
   (`let` env + per-cell outputs for `engine.explain`) threaded through `handle`.

M2 (wire-level differential test reference-ts ⇄ engine-lean) can start after step 3.

## Rules for Claude Code
- Keep `MathEngine/Simp.lean` green at every commit; never weaken a theorem to pass a build.
- Nothing under `engine/` imports Mathlib. Nothing under `proofs/` is executed.
- The frontend never learns which engine it is talking to beyond `engine.capabilities`.
- Commit after each numbered step. Update `book/TRACKING.md` when a step lands.
