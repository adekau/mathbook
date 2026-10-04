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
   DECISION 2026-09-13 (Alex, consulted per the M1 brief): option B — tiered measures with an innermost-strategy lemma,
   not a global RPO (not in Mathlib, ~3× the work, and still cannot order collect-powers against (ab)^n) and not fuel-as-
   a-proven-bound. The two parity rules stay in `simplify` (Mathematica distributes integer powers over products) and get
   a bespoke ordering rather than moving to `expand`. `expand`'s nested set stays on fuel in M5 (its own chapter later).
   DONE 2026-09-13. `Order.lean` (the ordering), `Terminate.lean` (`normalizeT`, innermost, with the conditional
   obligation and the returned invariants `μ out ≤ μ in` and `Normal out`), `PipelineOrder.lean` (thirty lemmas and
   `pipelineOrdered`), `Pipeline.lean` (commands and the rule list, moved out of Session). `evaluateCell` no longer takes
   a fuel argument. Axioms: the three standard ones; `lake test` 0 failures; wasm 1,830,991 bytes.
   Findings, in order of how much they changed the design:
   - No single textbook ordering works. `diff.*` is the classic RPO example, but RPO needs pow > mul for
     `(ab)^n → a^n b^n` and mul > pow for `x·x → x²`; every polynomial interpretation tried fails on `(b^m)^n → b^(mn)`
     with symbolic `m` when `x·x → x²` is present. What works is `M (pow b e) = (M b + 1)·M e − 1` (a numeric exponent
     *multiplies* its base), `M (mul es) = 2 + Σ (M e + 2)` (a per-factor charge), `M (num 1) = 1` (so `x · x^a → x^(a+1)`
     decreases), non-integer numerals weighing 4 (so `√2 + √2 → 2√2` decreases: `2^(1/2)` must weigh ≥ 9), and
     `M (diff f x) = 3^(M f + 3)`. Tuning `M` was the real work; each constant is forced by a named rule.
   - The obligation must be conditional on normal children. `diff.product` duplicates its body; if the body could still
     contain a command or a matrix product, no ordering of this shape survives. The rewriter's innermost strategy makes
     the hypothesis true at every firing, and the proof carries `Normal` through the recursion in the result type.
   - Five tiers, lexicographic: commands, malformed `diff`, nodes on a path to a matrix literal, `M`, `size`. Scalar
     multiplication `s·A` copies `s` into every entry, so counting literals alone fails; counting nodes *above* literals
     makes every `la.*` rule a strict decrease and `M` never sees a matrix.
   - Honest boundaries: commands (which call the fuel-based expand set, elimination, floats) and the matrix rules
     (unverified arithmetic until M7) have their outputs checked at run time for exactly the property the proof needs
     (`checked`, `checkedLit`); a failure surfaces as an error, never as non-termination. (The expand set left fuel on 2026-09-14, see the open items below.) Scalar rules skip nodes with a
     matrix child (`scalarOnly`), and `la.context` refuses a literal anywhere no matrix rule handles it, so a normal term
     is literal-free below its root — the lemma the third tier rests on.
   - Behaviour changes, all deliberate: `det` and `M^k` on literals are one step each; `la.mul` multiplies the first two
     literals in a product regardless of interleaved scalars; `N(1/3)` evaluates (the reference left it); `sin(A)`,
     `A + 1`, nested matrices are errors instead of junk normal forms; parity rules leave exponents 0 and 1 to
     `simp.power`; `diff(f, 2)` and `diff(f, x, 0)` are errors.
M6 origin tracking for `explain` (van Deursen–Klint–Tip 1993); current path-prefix heuristic over-approximates.
   DONE 2026-09-14: `engine/MathEngine/Origin.lean`. `explain` now traces the selected position *backwards* through the
   derivation instead of comparing final paths: outside a step's redex a position is its own origin
   (`at?_replaceAt_disjoint`, the theorem that makes skipping the step sound); inside the contractum its origins are the
   positions of equal subterms of the redex (`copied`); with none, the step `created` the node and its children are
   traced on; a position containing the redex is `contains`. Equality is taken up to the argument order `canon` may
   change (`canonDeep`), which is also how the silent reorderings between recorded steps are bridged. The result is one
   relation per step, in derivation order, sent as `ExplainResult.trace`; `explain` also accepts which term the path is
   into (input, output, or the term after step n), and the notebook renders every term with paths, so any subterm of any
   line is selectable and a step click shows the trail up to it with the relations. Findings: (1) a trace must stop at a
   created node but continue into its parts, or the history of `2·x·cos x` would be "the product rule" and nothing
   else; (2) exact equality breaks at the first silent sort (`x^(3+-1)` vs `x^(-1+3)`), which the first test caught;
   (3) what remains over-approximate is equal subterms at several positions, the paper's secondary origins — reported
   as sets, never dropped.
M7 linear algebra over ℚ verified (elimination preserves solution set).
   DONE 2026-09-14: `engine/MathEngine/LinAlgQ.lean`, Init-only. A matrix is read as a homogeneous system (one equation
   `r · x = 0` per row; the augmented matrix of `A x = b` is the same system at `(x, −1)`, so both readings are one
   predicate `Sol`). Elimination is a list of the three elementary row operations, and the theorem is one lemma per
   operation (`sol_swap`, `sol_scale`, `sol_addMul`) folded over the list: `sol_rref : Sol (rref m) x ↔ Sol m x`, three
   standard axioms. The command's numeral path replays the emitted operations into the derivation steps (`la.row-*`,
   now reported `verified`); symbolic entries keep the old simplifier-driven algorithm under `la.row-*.symbolic`
   (`unverified`, since its pivots are only assumed nonzero). Findings: (1) the invertibility that makes each operation
   preserve solutions is had for free by defining the degenerate parameters — scaling by 0, adding a row to itself — as
   the identity, so no lemma needs a side condition and the algorithm needs no proof that it avoids them; (2) padding
   the shorter row instead of truncating (`rowAdd`) removes the rectangularity hypothesis entirely; (3) the field
   algebra over `Rat` is discharged by `grind`, whose ring/field instances ship with core, so Mathlib was not needed —
   the whole proof lives in the engine; (4) what is *not* proved is that the output is in reduced echelon form; it is
   decided at run time (`isRref`) and a failure refuses the evaluation, the same honest boundary as `checked`. Open:
   proving echelon form, `det`/`la.mul` over ℚ, and giving matrices a value in the ℝ semantics (which would give
   `diff.matrix` content).
M8 integration as a verified *checker* (`deriv (integrate f) = f`), not a verified integrator.
   DONE 2026-09-14: `Antiderivative.lean` (the finder: sums, constant factors, powers, `a^u`, the elementary table, each
   under a linear substitution — `int.*` steps, nothing proved), `cmdIntegrate` (Pipeline.lean: differentiate the
   candidate with the pipeline and accept only if the normal form *is* the integrand), `Integrate.lean` (the claim
   `cmdIntegrate_spec`: an accepted `F` has `norm (diff F x) = ok f`, three standard axioms), and
   `proofs/Proofs/Integrate.lean` (`integrate_deriv`: hence `deriv F = f` at every point where the check's
   differentiation is sound — the hypothesis the rule statuses of that derivation state rule by rule, M3/M4). The
   notebook shows the finder's steps as `checked` (a new status: a guess verified by a later step), the `int.check`
   step with the differentiation nested under it, and the command inheriting the weakest status below it.
   Findings: (1) the pipeline could not check with itself — a rule set cannot contain a rule that normalizes with that
   set — so the pipeline became `pipelineRulesWith norm`, generic in the checker's normalizer, the termination theorem
   became `pipelineOrderedWith norm` for every `norm`, and the knot closes after the proof: the checker is the pipeline
   with nested `integrate` refused, the notebook's pipeline is the pipeline with that checker, and neither has a step
   budget; (2) the check is exact, so a correct guess can be refused — `∫ tan x` was, because `d/dx (−ln cos x)`
   normalized to `sin x / cos x`, which the engine did not identify with `tan x` (fixed the same day, see the open
   items); that is the right failure mode (never a wrong answer); (3) `x^a` is accepted through
   `simp.collect-powers` cancelling `(a+1)/(a+1)`, so its check inherits that rule's side condition (`a ≠ −1`) — the
   statuses say so without anyone writing it down. Open: products (integration by parts), `sin² x`, rational functions.
Open items after M8 (2026-09-14, Alex: "go through the open items before the book"):
- expand off fuel — DONE 2026-09-14. Not a joint ordering: an interpretation under which `a(b+c) → ab + ac` decreases
  makes `x·x → x²` increase, the M5 wall again. Instead `Expand.dist` (ExpandRules.lean) is one total, structurally
  recursive function — children first, then multiply out a product whose factor is a sum, collecting like monomials
  as the product is built factor by factor — and the pipeline collects the rest. The fuel rewriter is deleted; there
  is no step budget anywhere. `proofs/Proofs/Expand.lean` proves `dist_sound` over ℝ (unconditional: distribution
  holds in every commutative ring), so `cmd.expand` is now a verified step. Findings: (1) without collecting during
  distribution the pipeline's collect-like-terms took the 4096 monomials of `(x+y)^12` one pair at a time at the root
  with a full canonical sort each — minutes; collecting as a polynomial (sorted keys, coefficients folded) makes it
  instant and cuts the recorded derivation from 49,143 steps to two; (2) a step-recording algorithm and a rewrite
  system read the same in the notebook, which is the argument for doing it this way whenever a joint ordering would
  be forced. Alex's decision (2026-09-14).
- radical simplification (sqrt 8 → 2√2): Alex chose to retune M (2026-09-14). DONE 2026-09-14, but not by retuning `M`,
  which the analysis showed is impossible: as a term `2√2` is `2 · 2^(1/2)`, whose `M` (19) exceeds `8^(1/2)`'s (11)
  because the result contains the input's radical *and more*; only a value-dependent numeral weight could pay for
  that, and numeral weights must stay bounded for `fold-constants` to decrease on arbitrary sums (`1 + 7 → 8`). What
  the ordering does allow is the single-power form: `8^(1/2) → 2^(3/2)` at equal `M` and `size`, ordered by a new
  sixth tier — the magnitudes of the integer numerals (`numCount`, head-only, so the rewriter's monotonicity lemma
  extends without touching its invariants). Two more rules then do what Mathematica does where it matters: same
  square-free part radicals collect in a sum (`√50 − √18 → 2√2`; a sum of two radicals outweighs one product, so this
  *decreases* `M`) and same-index radicals multiply under one root (`√12 · √3 → √36 → 6`). Each rule guards itself
  with the decidable decrease its proof needs, so the ordering lemmas are a split on the guard; the guards never fail
  in practice and are honest boundaries, not fuel. The printer shows the single-power form the textbook way:
  `2^(3/2)` as `2√2`, `12^(1/2)` as `2√3`, `5√12` as `10√3`, `√8/2` as `√2`; text output stays faithful (`2^(3/2)`).
  All three rules are proved sound over ℝ unconditionally (`proofs/Proofs/Radical.lean`), their bases being positive
  integers. Findings: (1) the sixth tier had to be head-only — a tier that reads a *child's* value fails the
  children-monotonicity lemma, since a numeral child of equal weight could be replaced by another; putting the value
  on the numeral node itself sidesteps it; (2) `4^(2/3) → 2^(4/3)` ties every bit-length or value weight on the
  exponent side, which is why the tier weighs integers only and non-integer exponents nothing.
- echelon form of `LinQ.rref` proved rather than checked — DONE 2026-09-14: `engine/MathEngine/LinAlgRref.lean`,
  `rref_isRref : IsRref (rref m) (ncols m)`, Init-only, three standard axioms; the run-time `isRref` check is gone.
  The invariant carried column by column: the first `p` rows are pivot rows whose pivot columns increase, each a 1
  alone in its column with zeros to its left; every later row is zero in every column seen so far. A column step
  either finds no pivot (the invariant moves one column right) or swaps, scales and clears (one more pivot row).
  Findings: (1) the clearing step reads all its factors from the matrix *before* any clearing, so its sequential
  application equals the simultaneous one — the lemma `entry_clears` says each row changes by its own multiple of
  the pivot row, which itself is untouched; that is what makes the invariant proof entry-wise rather than
  operational; (2) `ring` is Mathlib's, so in the Init-only engine the rational identities are `grind`'s; (3) the
  statement is in the width of the input rather than of the output, which sidesteps proving that row operations
  preserve rectangularity — for the rectangular matrices the parser admits the two coincide.
- integration: DONE 2026-09-14. `sin u · cos u⁻¹ → tan u` is a new `simp.function` case (proved in all three layers:
  additive measure, M5 ordering, ℝ soundness — unconditional, since Mathlib's `tan` is `sin/cos` everywhere), so
  `∫ tan x` now verifies. The finder gained u-substitution (`c·g'·H'(g)`, a factor also tried as `g¹`, which gives
  `∫ ln x/x` and `∫ sin x cos x`) and integration by parts (LIATE, three levels), with derivatives supplied by the
  caller's normalizer. Finding: the by-parts candidates were all correct and all refused, because the pipeline never
  distributes a numeral over a sum (the ordering forbids it: distribution is `expand`'s job), so `-(a+b)+b` is a normal
  form. The fix keeps the check sound rather than weakening it: both sides are expanded with `Expand.dist` — proved
  sound for the derivative semantics too (`dist_soundD`) — and simplified before comparison (`int.compare`); the
  spec `cmdIntegrate_spec` and `integrate_deriv` state exactly that. Still refused: `eˣ sin x` (needs the
  "solve for the integral" trick), `sin² x` (a trig identity the simp set lacks), `1/(x²+1)` (no arctan in the engine).
- user functions with parameters — DONE 2026-09-14. `let f(x, y) = e` parses a parameter list; the session keeps
  a function table beside its variable bindings; a cell's input first expands calls (`substituteFns`: the body with
  parameters replaced by the already-expanded arguments, one level, so a self-reference unfolds once per
  evaluation) and then substitutes variables, with a definition's own parameters shielded from the session's
  bindings. The parser's `known` list, which decides whether `f(x)` is a call or a product, is fed the table's names.
  Nothing new to prove: expansion happens before the pipeline, as variable substitution always did.
- plotting (engine samples, notebook draws; studio Graph shot) — DONE 2026-09-14. `plot(f, x, from, to[, n])` is a
  new optional method `engine.plot` (protocol rule 5): the engine simplifies `f` under the session — so a derivative
  or a session function plots as what it is, with its derivation recorded like any other cell, and `explain` works
  on the formula — then samples it on a uniform grid with the numeric evaluator, reporting `null` where the value is
  not finite. The notebook draws the samples as an SVG (axes through the origin when in range, the curve broken at
  the gaps, the tails of the range trimmed so an asymptote does not flatten the rest) under the formula; the studio
  gets a Graph shot that draws the curve over the shot's duration and emits `Axes`/`axes.plot` Manim code with the
  function as a NumPy lambda. One engine, as decided: nothing in the notebook evaluates.
- notebook file open/save — DONE 2026-09-14. The File menu (the menu bar was decorative) opens, saves and names
  `.lemma` files: JSON with the cells' sources, their saved outputs and derivations, and the studio's scenes. Opening
  shows the saved outputs at once and re-runs every cell in order so the engine's session — and with it `explain` —
  matches what is shown. The notebook also autosaves to the browser after every run and comes back on reload the
  same way. Run, Kernel (restart the session), View and Help menus work too.
λ-world (2026-09-14, Alex: "get some stuff in here … like beta reduction (with option for de Bruijn indices on/off)",
   cells written standalone, Lean-style `\lam` input): DONE. `engine/MathEngine/Lambda.lean` — named terms,
   capture-avoiding substitution by a structural renaming pass (`freshen`, so it is total; the book's `subst` had to be
   `partial`), normal-order β one step at a time, the de Bruijn view computed alongside every step, a small parser
   (`λx y. e`, `\x. e`, juxtaposition, digits as Church numerals, `name := term`), and the Church library preloaded. A
   cell is a λ-cell if it has a λ or backslash, a `:=`, or starts with a λ-definition's name; the engine decides, the
   notebook only shows the badge. Terms are *encoded* into `Expr` (`fn "λ" [var x, body]`, `fn "@" [f, a]`), so
   selection, explanation and origin tracking work unchanged and the printer only learned two heads. Reduction runs on
   fuel — the one budget in the engine, and the honest one: whether a term has a normal form is undecidable, so `Ω`
   is refused after 1000 β-steps with what it had become. The notebook toggles de Bruijn indices in the View menu
   (a rendering the engine already sent), completes `\lam` to λ with Tab, converts `\lam`/`\l` on space or dot, and
   reads a normal form that is a Church numeral or boolean out beside the result. Proved (`LambdaProofs.lean`):
   substitution introduces no new free variables; the Church reader is right on the engine's numerals. Not yet:
   that the α-renaming preserves α-equivalence, that the de Bruijn view commutes with β — the β-steps are reported
   unverified for that reason. Finding: the book's `subst` recurses on a renamed body and Lean cannot see it
   terminate; carrying the renaming down one structural pass makes it total without changing what it computes.
Order world (2026-09-14, Alex: partial orders, join/meet, plus monotone maps and fixed points): DONE.
   `engine/MathEngine/Poset.lean` — finite posets as element lists with a relation: `poset({a,b,c}; a<b, a<c)` takes the
   reflexive-transitive closure and decides reflexivity, antisymmetry and transitivity (a failure names its witness),
   `divisors(n)`, `subsets({…})`, `chain(n)`; covers (the Hasse diagram), upper and lower bounds, join and meet,
   lattice with a witness pair when it fails, top and bottom, maximal and minimal, `le` explained by a chain of covers;
   maps as tables, `monotone` with a witness, `lfp`/`gfp` by iterating from ⊥/⊤ — the Kleene chain is the derivation.
   Its own little parser; values encoded into `Expr` (`fn "set"`, `fn "poset"`), so the notebook's machinery applies;
   the notebook draws the Hasse diagram in layers by height. Proved (`PosetProofs.lean`, Init-only): the partial-order
   check means what it says; Hasse edges are exactly the covers; what `join` finds is an upper bound below every upper
   bound, and when it finds nothing no least one exists; every point of the Kleene chain lies below every fixed point
   above its start (`iter_le_fixed`), so the chain's last element — a fixed point, checked — is the least. Honest
   boundary: that the chain stabilizes within |P| steps (pigeonhole on a finite chain) is checked at run time rather
   than proved. Finding: the whole world is decisions over lists, and the theorems are all "the decision means the
   Prop" — the same shape as `checked` in M5, but here the Prop is the textbook definition, which is what a reader
   should see next to a Hasse diagram.
Six-month cut line: M5 — reached 2026-09-13.
Notebook cleanup (2026-09-14, Alex's seven items): nested steps (1.1, 1.1.1) now select — the row lights up and any
   piece of their math is clickable, resolved locally from the path annotations since the engine traces top-level
   terms only; the kind badge and "n rules · ms" line are gone and show-work is off by default; a selected matrix
   is highlighted as a block (the path span is inline-block when it holds a table); View › Input interpretation
   hides the echo; every output has a form chip (matrix [ ] / ( ) / grid / table / input form, standard / input
   form for scalars), a typesetting choice kept in the .lemma file; prompts align with the input line; and `%`,
   `%%`, `%n` work as in Mathematica — the engine numbers every evaluation (`label` in the reply, error or not),
   the notebook shows that number as In/Out, and the session substitutes the referenced output before anything
   else, so the input interpretation shows what `%` stood for. Not done: the "Assuming a matrix | use as a list
   of lists" interpretation bar from the Mathematica screenshot, which needs the engine to report alternatives.
   Follow-ups the same day: View › Math size (small / normal / large; CSS variables on the root, remembered) and every
   step row shows its explanation under the rule name ("Scale R₂ by −1/3 so the pivot becomes 1."), clamped to two
   lines, with the full text as the row's tooltip and in the panel.
Bug found by Alex's `integrate(5y sin(y) sin^2(y), y)` (2026-09-14): two causes. (1) The parser read `sin^2(y)` as a
   variable `sin` squared times `y`; `f^n(x)` is now `f(x)^n` for the unary builtins. (2) The real one: `Expand.dist`
   did not splice a sum nested inside a sum, so `a·(−(−y²sin y + 2y cos y) + 2y cos y)` kept the inner sum as one
   monomial and never collapsed — the integral checker refused a correct by-parts candidate whenever the integrand
   had a constant factor and two rounds of by-parts (`integrate(5 y^2 sin(y), y)`). `flatAdd` fixes it; `dist_sound`
   and `dist_soundD` gained `sumR_flatAdd`/`sumD_flatAdd`. With the parse fixed the original input is refused
   honestly: `∫ 5y sin³y` needs a trig-power reduction (`sin² = 1 − cos²` then u-substitution) the finder lacks.

Trig and exp powers in `integrate` (2026-09-14, Alex: "the word", then `integrate(exp(x)^2, x)`): the finder
   gained the reduction formulas for `sinᵐu cosⁿu` (`int.trig-power`, by parts with the solve-for trick built in,
   applied until only first powers remain) and `(eᵘ)ᵏ = eᵏᵘ` (`int.exp-power`). Neither could verify without a
   change to the check: the derivative of an antiderivative of an even trig power equals the integrand only modulo
   `sin² + cos² = 1`, and the simplifier applies no direction of it (neither decreases the ordering). So the compare
   step now runs `Expand.identNorm` — `cos^k u ↦ (1 − sin² u)^(k/2)·cos^(k mod 2) u`, `exp(u)^k ↦ exp(k·u)` — on both
   sides before `dist`: a total function proved sound in both semantics (`identNorm_sound`, `identNorm_soundD`,
   from `Real.cos_sq'` and `Real.rpow_def_of_pos`), named in `cmdIntegrate_spec` and `integrate_deriv`. After it a
   trig polynomial has cosine to at most the first power, a normal form for ℝ[s,c]/(s²+c²−1). Also: Greek letters
   and `ℯ` are identifiers (`ℯ` parses as `exp(1)`, so `ln ℯ = 1` and `d/dx ℯ^x = ℯ^x` come from the exp rules and
   `N(ℯ)` from the table; the printer shows `exp(1)` as `e`/`ℯ`), and the notebook's `\` completions cover `\pi`,
   `\e`, `\phi` and the Greek alphabet.
Renamed (2026-09-14, Alex: "ChalkMath, chalkmath.com is available"): the notebook is ChalkMath; files are `.chalk`
   (`chalk: 1`; old `.lemma` files with `lemma: 1` still open); local storage keys are `chalkmath.*` with the old
   ones read as a fallback; the engine selector says "kernel · wasm / http". Toolbar trimmed to the Enter hint;
   cell counts moved to the status bar; the "exact arithmetic · verified engine · termination proven" line is gone
   (the statuses on the steps say it where it matters). Light-theme button edges darkened.
Notebook tabs (2026-09-14): several notebooks open at once, one tab each, each with its own engine session (so `%`
   and `let` bindings are per notebook); `+` opens a new one, `×` closes one (an unsaved notebook asks first; the
   last tab closing leaves a fresh one); File › Open goes into a new tab unless the current one is untouched. A tab
   is italic with a `*` while the notebook differs from its last save or open; the browser autosave keeps every open
   tab, which is current, and the unsaved marks; a restored notebook re-runs its cells when its tab is first shown
   and, if it was clean, stays clean.
Cell menu, browser library, Pages (2026-09-14): each cell has a ⋮ menu (send to any scene or a new one, duplicate,
   move, copy input / output / output as LaTeX, clear output, delete). File › Save keeps the notebook in the
   browser's local storage under its name (`chalkmath.library`; Cmd/Ctrl+S), File › Open is a picker over those
   with delete, and Export / Import move `.chalk` files in and out. `.github/workflows/pages.yml` builds the wasm
   engine (runtime cached) and publishes `apps/notebook/dist` to GitHub Pages; the repository needs Settings ›
   Pages › Source set to "GitHub Actions" once.
Complex numbers (2026-09-14, Alex: the logo `e^(π i)` could not be computed; chose "complex arithmetic"). `i` and `π`
   are constants (`fn "i" []`, `fn "π" []`, rank between numerals and variables in the canonical order; `sumRank`
   puts `b·i` after the numerals in a sum so `2 + 3i` reads as written). `ComplexRules.lean`: Gaussian rationals
   (`gauss?`, `gaussE`), `cx.i-power`, `cx.arithmetic` (products, with an integer power of a Gaussian numeral as a
   factor — that is how `1/(1+i)` arrives, and the only affordable form: the bare `(1+i)^(-1)` weighs less than
   `1/2 − i/2`, so the complex rules run before the identity rule strips the leading 1), `cx.power`,
   `cx.conjugate`, `cx.re-im`, `cx.abs`, `cx.exact-trig` (rational multiples of π by period, half turn, reflection,
   reference table), `cx.euler` (only where both values are exact — the general formula duplicates θ, which the
   ordering cannot pay for; Mathematica does the same), `cx.euler-power` (`ℯ^b = exp b`). Every rule self-guards
   with `M res < M e`; the nine decrease lemmas are a split on the guard. A third semantics `evalC` (Cx.lean, with
   `Complex.cpow` = principal branch) and `CxRules.lean`: all nine rules verified over ℂ, exact-trig and euler-power
   over ℝ too; the four algebraic simp rules and `simp.power` ported to ℂ; `ln(exp x) = x` refuted at `x = 2πi`
   (`not_functionRules_soundC`). The reply carries `semantics: "complex"` when a cell mentions `i`; rule statuses
   have a `complex` column; the notebook shows it for such cells and "proved over ℝ only" for the rest. Book: a new
   chapter, complex numbers and Euler's identity (Part I). Not proved over ℂ: collect-powers (needs `b ≠ 0`,
   `Complex.cpow_add`), radicals, expand, the derivative rules (no complex derivative semantics).
- parser: a numeral over a nonzero numeral is that rational — DONE 2026-09-14. `3/4` used to parse as the
   product `3 · 4⁻¹`, so `cos(3/4 π)` showed a `simp.power`, a `simp.fold-constants` and a `simp.identity` step
   before any trigonometry (the reference engine's convention, ported unnoticed). Now `n/d` for numerals is the
   literal `n/d`; `x/y/z` still tests the parser's left associativity, and `8/2/2` is `2`.
- plot: lists of functions — DONE 2026-09-14. `plot([f, g, …], x, from, to[, n])` draws one curve per entry. The
   list is the one-row matrix the parser already reads, so the engine normalizes it as one term (scalar rules
   rewrite inside matrix entries; `plotFns` accepts a row or a column and refuses a genuine matrix) and records
   one derivation, so `explain` still works — a legend entry in the notebook explains that entry of the output
   list (path `[i]`). The reply's `points` became `series: [{rendered, points}]`, one per curve (`PlotSeries` in
   the protocol); old `.chalk` files with a single `points`/`text` migrate on load (`migratePlot`). The notebook
   shares one y-range across the curves, colours them by index (`--curve1…5`, both themes), and the studio's Graph
   shot draws them all; the Manim export emits one `axes.plot` per curve in a `VGroup`.
- simp.fold-constants builds its result with `addN`/`mulN` — DONE 2026-09-14. `2 · 5` folded to the *one-element
   product* `[10]`, which prints as `10`, so the notebook showed a `simp.identity` step ("a product of one factor
   is that factor") that changed nothing visible — after every `la.scale`, every `diff.power` exponent (`3 − 1`),
   every fully numeric sum. The fix is one word in `foldApply`; the termination proof goes through `M_addN_le`, and
   the six-tier decrease through a proxy lemma `muLt_of_clean_via` (the collapsed result is no heavier and no
   larger than the singleton the old proof handled). Soundness over ℤ, ℝ and ℂ rewrites with `eval?_addN` etc.
   `diff(x^3, x)` is now two steps, not three; the origin-tracking test was updated accordingly.
- notebook: signature help — DONE 2026-09-14. While the caret is inside a call the notebook shows the function's
   signature above the input with the current parameter in bold (`diff(f, **x**[, n])`), the way an editor's LSP
   client does. `callContext` walks back from the caret skipping balanced groups (an unclosed `[`/`{` or a bare
   grouping `(` is part of an argument, so the walk continues outward) and counts top-level commas; `sigPieces`
   splits a reference signature into parameters, treating `[, n]` as an optional one and a `[f, g, …]` list as a
   single one; `plot` shows its list form when the first argument starts with `[`. Session functions get it too:
   the evaluate reply's `params` (already emitted by the engine, now in the protocol) are remembered per session.
   Esc dismisses it for that call site until the caret leaves; View → Signature help turns it off (`chalkmath.sighelp`).
- a bare session-function name is its body — DONE 2026-09-14. After `let g(a, b) = a*b`, `integrate(g, a)` gave
   `a*g`: the unapplied `g` was a free variable (Mathematica reads it the same way, silently). `substituteFns` now
   expands a bare name of a function with parameters to its body over those parameters, so `integrate(g, a)`
   integrates `a*b` and `diff(g, b)` is `a`. The reference entry for `let` says so.
- notebook: insert bar between cells, menu off the paper, no hidden input text — DONE 2026-09-14. A thin strip
   between cells (and after the last) shows a rule with a `+ cell` pill on hover; a click inserts a cell there
   (`insertGap`), as Mathematica's insertion bar does. The cell `⋮` menu now lives on the body as a fixed popup,
   flipping above its button when there is no room below and closing when the paper scrolls — it used to sit
   inside the scrolling paper, where a menu near the bottom grew a scrollbar. The input reserves room for the
   action buttons only while they are shown (hover/active); a long input was hidden under invisible buttons.
   `focusCell` focused before re-rendering, so Duplicate/Move/arrow navigation lost focus — now it renders first.
- notebook: no vertical scrollbar on a tall output — DONE 2026-09-14. A 3×3 matrix's output row scrolled by 8px:
   `.outval` is `overflow-x:auto`, which makes `overflow-y` auto too, and KaTeX's vlist struts extend the scroll
   height a few px past the strut that bounds the visible render (nothing visible goes past it — measured). Now
   `overflow-y:hidden`, as `.step .el` already was; the panel's selection line likewise.
- book: code-block glyphs and the CI build — DONE 2026-09-16. Every ρ ∀ → ≤ in a Lean listing was blank in the PDF:
   the preamble asked fontspec for "DejaVu Sans Mono" by name, fontconfig on a machine without the system font
   cannot see TeX Live's copy, and the `\IfFontExistsTF` guard silently fell back to Latin Modern Mono. Now loaded
   by file name, which kpathsea resolves inside TeX Live itself (so CI and local agree). CI (LaTeX 2026-06) failed on
   `\lc{evalR}` inside math — `\ttfamily` in math mode is an error there, a warning on TeX Live 2020 — so `\lc`
   wraps in `\text` under `\ifmmode`. Also: unicode-math's `\setminus` is U+29F5, absent from Latin Modern Math
   (`\smallsetminus`, U+2216, instead); ℯ is absent from DejaVu, so the Try-it box writes `\e`. The log has zero
   "Missing character" lines.

## M9 — Fourier: drawing llamas with circles (from Alex's 2020 article)

Goal: re-derive the article (inner products → orthogonality → the square wave's Fourier coefficients
→ the DFT → epicycles) with the engine doing the calculus, and draw the pictures in the notebook.

- Stage A, the exact engine work — DONE 2026-09-16.
  - `integrate(f, x, a, b)`: the definite integral. The same finder and checker (`findAnti`, factored
    out of `cmdIntegrate`), then `F[x := b] − F[x := a]` (`definite`, one `int.bounds` step). Claim:
    `cmdIntegrate_definite_spec`; reading: `integrate_definite` (Fourier.lean), the fundamental theorem
    of calculus through the engine — `∫_a^b f = F(b) − F(a)` where `F` is differentiable on `[a, b]`,
    `f` interval-integrable, and the checker's normalizations sound (the M8 hypotheses). The
    differentiability hypothesis is real: `deriv` of a non-differentiable function is junk 0.
  - `sum(f, k, a, b)`: integer bounds, one substituted term per index, collected by the pipeline
    (`cmdSum_spec`, `sum_soundR`). Needed a *structural* substitution `substVar` (the old `substitute`
    is `partial`, so nothing could be proved about it): `substVar_soundR`/`soundC`.
  - `exptotrig(e)`: Euler's formula everywhere at once (`expToTrig`), as a command because the
    general rewrite duplicates θ and no simplification rule could pay for it. A negated angle is
    folded there (`cos(−θ) = cos θ`, `sin(−θ) = −sin θ`) because `sin(−t) → −sin t` is a tie in every
    tier of the ordering. Proved over ℂ (`expToTrig_soundC`, `Complex.exp_mul_I`); over ℝ it has no
    content (`i` is junk 0). Write `expand(exptotrig(…))`: the pipeline never distributes a numeral
    over a sum, and `Expand.dist` is proved over ℝ only — its ℂ soundness is open (the generic `Sem`
    in Proofs/Expand.lean is ℝ-specific; parametrizing it over a field is the fix).
  - `dot(u, v)` (bilinear, like Mathematica's `Dot`; the Hermitian product is `dot(u, conj(v))`),
    `norm(v)`, entrywise `conj` of a matrix (`la.dot`, `la.norm`, `la.conj`); `sign(x)` with numeric
    evaluation and a numeral fold (`Real.sign` added to `applyFn`; `sign_fold_soundR`).
  - Summands mentioning `i` now sort last (`sumRank` via `hasI`), so Euler reads `cos θ + i sin θ`.
  - Checked against the article: `c_3 = −2i/(3π)`, `c_2 = 0`, the symbolic `−i/k + i e^{−iπk}/k`,
    `∫e^{ix}dx = −i e^{ix}`, and `expand(exptotrig(2i/π(e^{−it} − e^{it}) + …)) = 4 sin t/π + 4/3 sin 3t/π`.
- Stage B, the visuals — DONE 2026-09-16. `MathEngine/Fourier.lean` (presentation, unverified, and the
  notebook says so): `CF`, a complex float with the arithmetic and principal functions; `evalNumericC`,
  the numeric evaluator over ℂ — `N` uses it when a term mentions `i` or has no finite real value
  (`N(sqrt(-1)) = i`, `N(exp(iπ/4))`); integer powers multiply out so `(1+2i)^2` is exactly `−3+4i`.
  `plot` of a complex-valued curve is drawn in the plane (a `parametric` series, `[re, im]` samples,
  equal scales). `epicycles(f, t)` reads the `(k, c_k)` off a finite Fourier sum (`fourierTerms`,
  distributing first since the pipeline never does) and the notebook animates circles tip to tail
  — radius |c_k|, phase arg c_k, k turns per period — with the tip tracing the curve; the exact
  coefficients are in the legend. `dft(points[, modes])` is the O(N²) discrete Fourier transform of
  sample points (complex numbers or `[x, y]` pairs), keeping the `modes` largest; File → Import SVG
  as epicycles samples a file's paths at equal arc lengths (the article's `getPointAtLength` loop)
  into a `dft` cell. The studio has an Epicycles shot, and the Manim export emits a `ValueTracker`
  with `always_redraw` arms and a `TracedPath`. Checked: the square wave's partial sum traces a
  segment on the real axis (the article's "line"), a heart SVG draws with 21 circles.
- Stage C, the chapter — DONE 2026-09-16. `m11b-fourier-series` (Chapter 13, after echelon form): inner products
  and "a coefficient is an inner product" (Theorem: coefficients from an orthonormal basis); functions as vectors,
  `∫e^{int} = 2πδ` and orthonormality of `e^{ikt}` (paper proofs; the engine does every instance, not the
  symbolic lemma — it cannot know k is an integer); Euler as motion (`d/dt e^{it} = i e^{it}`); Fourier
  coefficients and the finite-sum recovery theorem, with Dirichlet/completeness stated as unproved; the square
  wave's `c_k = i((−1)^k − 1)/(kπ)` re-derived and `S_3 = 4/π sin t + 4/(3π) sin 3t`, every step run in the
  engine; epicycles (the ellipse and the segment as propositions); the DFT with discrete orthogonality and the
  inversion theorem; a "what is proved and what is drawn" section quoting `integrate_definite`; five exercises.
  Every Try-it input was checked against the native engine. Added on the way: `simp.exp-product`
  (`exp(a)·exp(b) = exp(a+b)`, guarded; `expProduct_soundR`/`soundC`), without which the orthogonality integrals
  were refused. Book: 174 pages, zero missing characters. Open: `(√2)^{-2}` does not simplify (powers of
  radicals with an integer outer exponent), so the inner-product Try-it uses (3/5, 4/5) instead of the article's
  (1/√2, 1/√2).
- notebook: syntax highlighting with bound variables — DONE 2026-09-17. The input's text is transparent over an
   overlay with the same metrics (the input keeps caret, selection and horizontal scroll, mirrored by a transform).
   Tokens: numbers, `let`, commands (only when a parenthesis follows), built-in functions, constants, operators;
   names bound in the session by `let` in their own colour; and, as Mathematica colours `Plot[f, {n, …}]`'s `n`,
   the variable a binder command binds — `diff`, `integrate`, `plot`, `epicycles`, `sum`, `subst` — is marked over
   that call's parentheses, `let f(x, y) = …`'s parameters over the line, `λx y.` over the term. View → Syntax
   highlighting toggles it (`chalkmath.highlight`).
- notebook: Markdown and section cells, notebook links — DONE 2026-09-20. Three kinds of cell: math (the engine's),
   Markdown (headings, paragraphs, lists, quotes, rules, fenced code and `code`, *emphasis*, links, images as
   figures, `$…$` and `$$…$$` through KaTeX — a small renderer that builds DOM nodes, never HTML from the text) and
   section headings, which group the cells below them: ▶ Run section runs them in order, ▾ folds them away, the
   outline indents them. The `+ cell` bar between cells has a ▾ for the kind; the ⋮ menu and Edit change a
   cell's kind (Jupyter's M/Y), keeping the text. Markdown cells edit in a growing textarea (Shift+Enter or Esc
   renders; double-click or Enter edits), come back rendered from a file. File → Copy link to notebook puts the
   sources (names, kinds, show-work, folds — no outputs) deflated and base64url-encoded in the fragment
   (`#nb=…`, ≈ a third of the JSON); opening such a link opens the notebook in its own tab and re-runs it.
   Goal: the llama article written in ChalkMath. Fixed on the way: the epicycle trace ran 2 % ahead of the dot
   (a fudge factor in place of the sample index — now the trace ends at the tip itself), and `dft`'s echo
   counted `;` only, so a row of complex points was "1 sample point".
- notebook: show-work rows read for people — DONE 2026-09-20. The row's headline is the rule's own name for
   itself (the lead of its explanation, "Power rule: …", or a table for the ones that do not lead with a name);
   the machine name (`expand.distribute`) moves to the tooltip and the panel. A diff in place between steps: the
   subterm a step rewrote is tinted green in its row and red in the row before (the input's rendering for the
   first step); a rewrite at the root tints nothing, the whole line changed. Hovering a subterm now lights only
   the innermost one (`:hover:not(:has([data-path]:hover))`) — before, every ancestor lit with it, so a hovered
   `2` in `2·d` was indistinguishable from the product.
- notebook: the step diff, second pass — DONE 2026-09-20. Red-then-green misled: an identity step's old and
   new print the same, so the term seemed to wander. Now one tint on the step's own row, on what changed, and
   hovering it shows `old → new` typeset. What changed is a structural diff of the step's `before` and `after`
   (the smallest differing subterms, matrix entries at `row·width + column`), not the recorded path — so rref's
   row operations and nested derivations mark too; the integration finder's guesses each start from the integral
   again (no chain), so they get no "old". Nested derivations now carry `inputRendered` (Wire.lean) so a
   sub-derivation's first step has its "old".
- notebook: the step diff, third pass — DONE 2026-09-20. The `old → new` tooltip was missing on most steps: the
   pipeline canonicalizes silently between recorded steps (flattens `(2·x)·sin x`, reorders), so a step's `before`
   is not the previous row's `after` and the "old" could not be cut from the row above. Every step now carries
   `beforeRendered` (Wire.lean) and the old is cut from the step's own rendering of what it started from.
- notebooks/llamas.chalk — DONE 2026-09-20. Alex's 2020 article "Fourier Analysis: Drawing Llamas with Circles"
   as a ChalkMath notebook: 8 sections, 40 Markdown cells (the article's prose and equations, figures by URL from
   adekau.github.io), 49 math cells for everything it computes — the intro's line/square/fish as `epicycles`,
   complex arithmetic, the (u, v, w) dot products and the exact recombination `c1*u + c2*v = [7/10, 6/5]`,
   symbolic `dot` over ℝ and ℂ, Euler as `exptotrig`, `diff(exp(i*t), t)`, the orthogonality integrals, the
   square wave's `c(k)` as two definite integrals (k symbolic, then k = −3…3, and `c(0)` directly), the partial
   sums, `expand(exptotrig(sum(…)))` to `4/π sin t + 4/(3π) sin 3t`, the 7-term plot, and the llama itself:
   400 points sampled from the article's `llama.svg`, bound with `let`, then `dft(llama, 10 | 60 | all)`. Every
   math cell runs clean in the native engine and in the wasm notebook (0 errors). Saved as sources only: with
   outputs the file was 11 MB — the `sum(c(k)…)` cells' steps alone are 3 MB each (every step carries the whole
   term twice, plus the nested integrate checks) — and the notebook re-runs on open regardless. Fixed on the way:
   steps past 256 KB are no longer persisted (file or autosave, which was past localStorage's quota); the
   epicycle frame is measured (joints padded by their circles over a lap) instead of summing all radii, so a
   60-circle llama fills its box; `dft(name, …)` echoes as itself; near-zero ticks print 0. Engine gaps the
   article exposed: `sqrt(2)^2`, `sqrt(74)^2` and `sqrt(x)^2` do not simplify (products `sqrt(2)*sqrt(2)` do), so
   `u` is written with `sqrt(2)/2` and the norm is shown as `dot(u, u)`; `p(j)` in a `sum` reads as `p·j`.
- engine: powers of radicals — DONE 2026-09-20. `simp.power`'s `(b^m)^n = b^(mn)` was integer-only, so `sqrt(2)^2`,
   `sqrt(74)^2` and `1/sqrt(2)^2` sat there (the notebook's `norm(u)` came out as `sqrt(1/2·sqrt(2)^2)`). New branch:
   integer `n` over a positive numeral base, any rational `m`. Proofs: ℝ by `Real.rpow_mul` (needs `0 ≤ b` — which is
   why a symbolic `sqrt(x)^2` is left alone: `Real.rpow` reads `x^(1/2)` as 0 for negative x, so `sqrt(x)^2 = x` is
   false there); ℂ by routing every power through `Complex.ofReal_cpow` (the principal branch agrees with the real
   power on a non-negative real base) and the same `Real.rpow_mul`; ℤ semantics vacuous (a non-integer exponent has
   no integer value). Termination: the measure has `M (pow b x) = (M b + 1)·M x − 1` and a non-integer numeral has
   `M = 4`, which the branch needs (with only `2 ≤ M` the bound is tight, not strict). Tests: `sqrt(2)^2 = 2`,
   `sqrt(74)^2 = 74`, `1/sqrt(2)^2 = 1/2`, `(2^(3/2))^2 = 8`, `sqrt(x)^2` stays, `norm([√2/2, √2/2]) = 1`.
- notebook: load lag — DONE 2026-09-20. Two causes. Each epicycle box rebuilt its whole SVG every animation frame
   (axes, the trace, and for the full llama 402 circles + 402 arms), five boxes at once; now the SVG is built once
   and each frame moves the arms and circles in place and re-cuts the trace's `d`, at most 30 fps, paused while
   the page is hidden, and circles under a pixel are not created (the llama keeps 84 of 402). And the autosave
   re-serialized every open notebook after each of a hundred cells during hydration; it is now coalesced (700 ms)
   and flushed on unload.
- notebook: files as values — DONE 2026-09-21. A notebook has attachments (File → Attach file…, or paste a file or
   SVG text into any cell): any type, held as text or base64, persisted in the .chalk and in the link. `⟦name⟧`
   refers to one; what it means depends on where it stands — in a Markdown cell an image shows; in a math cell an
   SVG becomes, before the engine sees the cell, the 400 points sampled along its paths (equal arc lengths,
   centred, scaled to [-1, 1]), so `let x = ⟦llama.svg⟧` binds a 400×2 matrix; a non-SVG says "only an SVG can be
   traced into points (yet)". `import("url")` fetches one from the web the same way. The engine only ever sees
   numbers; `epicycles(points[, modes])` is now `dft` under the natural name. The input interpretation names the
   image and its point count instead of typesetting 400 rows, and a matrix output of more than 24 rows is abridged
   (three rows, dots, the last, and its size). The highlighter draws `⟦name⟧` as a chip (red when nothing of that
   name is attached). llamas.chalk now imports the article's llama.svg from its repository and draws it in the
   introduction with 100 circles; the static figures with a live counterpart (the line, square and fish, e^{it},
   the square wave, sin t, cos·sin, the modes animation) are cells now. Left as images: the frequency-domain
   magnitude plot and the vector diagrams, which have no function yet.
- notebook: import as a value, Mathematica-shaped — DONE 2026-09-21. `import("url")`, `⟦name⟧` and `let x =`
   either are image-valued cells: the cell shows the image (the fetched SVG as a data URL — a raw file server
   sends SVG as text/plain, which <img src=url> will not render), and the name is bound. `samplePoints(x)` is the
   explicit step to numbers (a 400×2 matrix); where points are expected the image is accepted too. Two bugs the
   llama exposed: a literal `-0.036` parsed as (−1)·0.036, so a bare 402-row matrix came back with 381
   fold-constants steps each carrying the whole matrix twice — a 63 MB reply that killed the page (0 steps and
   194 KB now: a negative literal is one numeral; `-2^2` is still −4); and the square cell's coefficients — a
   square traced at constant speed has c_k at k = 1, −3, 5, −7, all the same sign, falling as 1/k² (I had a sign
   wrong). The fish is now the fish curve x = cos t − sin²t/√2, y = cos t sin t: four circles and a constant.
- engine: `factor` — DONE 2026-09-21. The normal form of a definite integral in a symbolic parameter reads
   `½·(−(i/k − i e^{ikπ}/k) − i/k + i e^{−ikπ}/k)/π`; by hand one ends at `i(e^{−ikπ} + e^{ikπ} − 2)/(2kπ)`. `factor(e)`
   is that step: expand and collect (the pipeline's own proved steps), put the sum over a common denominator
   (Mathematica's Together: coefficients' lcm, each base at its largest exponent), and pull the numerator's common
   factor out (the coefficients' gcd, each base at its least exponent). A command (one presentation of the
   normal form), unverified in the ledger: a/b + c/d = (ad + cb)/(bd) needs nonzero denominators. Not a
   factorization into irreducibles: x² − 1 stays. Printer: a rational coefficient's denominator now goes into
   the fraction's denominator (`x/(2π)`, not `½·x/π`), which also puts factor's result in the hand form.
- printer: no display-time radical reduction — DONE 2026-09-21. `radicalParts` printed `4^(1/2)` as `2` and `12^(1/2)`
   as `2√3` "the way a textbook writes it", so the step that actually reduces them (`simp.power`'s perfect power,
   `simp.radical`'s base) showed a term identical to the one before it — Alex: "the wording is for if it were
   showing sqrt(4) instead of 2". A base that is itself a perfect power (`4`, `8`, `16`) now prints as it is,
   `√4`, and the step shows. The textbook form stays for the rest (`12^(1/2)` as `2√3`, `2^(3/2)` as `2√2`),
   because there it is the printer's job: the ordering the rules decrease cannot turn one power into a
   product (M(2·3^(1/2)) = 19 > M(12^(1/2)) = 11), so `12^(1/2)` is the normal form. "Perfect 2th power" is
   "perfect square".
- notebook: hover under a radical — DONE 2026-09-21. KaTeX draws the radical sign as an SVG overlay on top of the
   radicand (and the fraction and overline rules as overlays), which swallowed the pointer: a changed subterm
   under a √ could never be hovered or clicked. The overlays are `pointer-events: none` now.
- notebook: order-lattices.chalk — DONE 2026-09-27. Part I of lean4learning's *From Zero to Propagators* (relations,
   partial orders, special elements, monotone maps, lattices, Knaster–Tarski) as a notebook: 169 cells, 117 of them
   live order-world cells replacing the book's `#eval` interludes and hand-drawn Hasse diagrams, the Lean theorems
   kept as code blocks (they are about all posets; the engine decides particular finite ones). Generated by a
   script; every cell run through the native RPC before opening it. Five cells error on purpose (the antisymmetry
   witness, no bottom, no top, no join, lfp of a non-monotone map): the refusal is the lesson. The engine caught
   two errors in the book: §2.2's figure caption says sup{c,d} = g, but g is not below the other upper bounds e, f,
   so c and d have no join (E is not a lattice); §2.5's comment says `iterToFixpoint double12 1` is [1,2,4,12], but
   8 ∤ 12 so double12 fixes 4 and the chain stops at 4. Two notebook fixes it forced: a subsets-poset element is
   named by its set literal, and `\mathit{{a,b}}` lost the braces to LaTeX grouping (now `\{a,b\}`, `\varnothing`);
   and the order rules have step titles ("Least upper bound", "Fixed point") instead of the rule tail.
   Gaps it found, not done: product and dual constructors (Exercises 1.3, 1.4 are written out by hand); maps
   between different posets, and map tables with set-literal keys (S ↦ S ∪ {x} on a powerset cannot be typed);
   nested order expressions (`meet(D, 4, join(D, 4, 6))`); `distributive(P)`; n-ary sup/inf of a set (`upper` and
   `lower` approximate it); `bottom`/`top`/`sup` answer "none" with an error rather than a value.
- engine: order world at powerset scale — DONE 2026-09-27. Alex: "why is `let P3 = subsets({a, b, c, d, e, z, s})` so
   slow?" — over two minutes natively, longer in wasm. `Poset.rel` was a list scan of `le` (3⁷ = 2187 pairs for
   seven elements), and `hasse` asks `covers` for every triple (128³ = 2 million), each a scan: billions of
   string-pair comparisons. `height` was worse, walking every chain below each element (47 000 under the top).
   The poset now carries `le` as a `Std.HashSet` built once, with a proof field `leSet_eq : leSet = ofList le`,
   so `rel` is a hash lookup and `rel_eq` keeps every proof on the list; heights are computed once by relaxing
   along the covers `|elems|` times. subsets of 7 with the lattice check: 0.4 s; of 8 (256 elements): 3 s.
   Untouched and still quadratic-ish: `closure` for a hand-written `poset(...)` (eraseDups over pair lists) and
   `latticeFailure` (every pair, every upper bound) — fine to a few hundred elements.
- engine: exact roots of perfect-power bases — DONE 2026-09-30. `integrate(sqrt(x), x, 0, 4)` answered
   `2*4^(3/2)/3`, while the same integral to 9 answered 18. `simp.radical`'s perfect-power rule (`a^(p/q) → r^(kp/q)`
   for `a = r^k`) was guarded by `M` unchanged and `numCount` down, the right guard for `8^(1/2) → 2^(3/2)`; but
   when the root is exact the new exponent is an integer numeral and `numCount` counts it too: `9 → 3, 3` is 6 < 9,
   `4 → 2, 3` is 5 > 4, so `4^(3/2)` (and `4^(5/2)`, `4^(-3/2)`) never reduced. An exact root does lower `M`
   (11 → 5: an integer exponent is lighter than a fraction), so the guard now also accepts a strict `M` decrease;
   the ordering proof (`dec_radicalBase`) takes that branch first, and the soundness proof is unchanged. The row
   reads `$4 = 2^{2}$, so $4^{3/2} = (2^{2})^{3/2} = 2^{3}$` and `simp.power` evaluates `2^3 = 8` next. Still
   open: a rational base (`(4/9)^(3/2)`) stays, since `simp.power` evaluates only `p^(1/n)` of a rational.
- wasm: Std in the browser engine — DONE 2026-09-27. The poset change imported `Std.Data.HashSet`, and the wasm
   link failed on `initialize_Std_Data_HashMap`: the wasm toolchain built only the runtime and `Init` ("the engine
   only imports Init"), and the failure hid behind a `| tail` — the browser kept running the old wasm, which is
   how the "fixed" powerset still took minutes there while native took 0.4 s. `build-lean-wasm-runtime.sh` step 5
   now emits and compiles the Std modules the engine imports, transitively (139 for HashSet + HashMap, none
   touching libuv), into `libStd.a`, keeps the module list beside it and reruns when an import widens it;
   `build-wasm.sh` always calls the runtime script (it is incremental) and links `-lStd`.

## Productionizing ChalkMath (2026-09-27, Alex: "as usable as possible for anyone, not just me")

- security: KaTeX trusts `\htmlData` only — DONE 2026-09-27. Saved outputs (a `.chalk` file, the library, the
   autosave) render before any re-run, and `trust: true` let that LaTeX carry `\href{javascript:…}`, `\htmlStyle`
   overlays and remote `\includegraphics`: one click on a crafted file ran script. The engine emits nothing but
   `\htmlData` (the paths), so a trust function allowing exactly that command costs nothing.
- autosave kept attachments out — DONE 2026-09-27. The restore skipped `assetsFromFile`, so `llamas.chalk` lost
   its llama on reload.
- kernel: stop, crash, load failure — DONE 2026-09-27. The wasm engine is synchronous inside its worker, so an
   evaluation cannot be interrupted from inside; ■ Stop terminates the worker, starts a fresh one, and rebuilds
   the session by re-running the cells above that had outputs (a failed or stopped cell bound nothing, and one
   that hung would hang again). Protocol (rule 5): `Transport.onError` / `EngineClient.onError`, and `close()`
   fails the calls in flight, which is what lets a terminated call settle. Runs asked for while the engine is
   busy queue (In[*]) instead of being dropped. A worker that fails to load or dies shows a notice with Restart.
- notebook options — DONE 2026-09-27 (Alex's list): don't run notebooks on open (saved outputs plus a "not run
   yet" notice; nothing reaches the engine, no `import()` is fetched); hide work in opened notebooks, and show /
   hide all work; a sidebar that folds away (rail button, View menu, Ctrl/Cmd+B); the active cell's ⋮ actions in
   the toolbar. The kernel picker, log and rule count moved behind Help › Developer mode; what the reader did
   gets a toast.
- repository — DONE 2026-09-27. Packages renamed `@chalkmath/*`, and the GitHub repository is now `adekau/chalkmath`.
   CI (`ci.yml`): engine build + `lake test`, check:engine, TS build + type-check + tests, bundle. Pages deploys
   only a main commit CI passed, after a wasm smoke test. `proofs.yml` builds the theorems when engine/ or proofs/
   change.
- first visit, examples, help — DONE 2026-09-27. A first visit opens `notebooks/welcome.chalk` (generated by
   `scripts/notebooks/mk-welcome.mjs`; CI runs every cell through the native engine, 27 cells, 0 errors) instead
   of five unexplained cells. File › Examples opens the bundled notebooks; Help has Keyboard shortcuts and About.
- no third parties — DONE 2026-09-27. KaTeX (npm) is bundled into app.js, its CSS and fonts and the three page
   families (fontsource) into style.css; the page loads nothing from another site unless a notebook's `import()`
   or Markdown image asks. Minified with source maps; a Content-Security-Policy allows scripts only from the page.
- phones — DONE 2026-09-27. A layout under 760px: sidebar as a drawer, a narrower prompt column, the active
   cell's actions under it, steps stacked, panel folded until used.
- accessibility — DONE 2026-09-27. Keyboard-operable menus and controls, dialogs that trap focus, announced
   results, described plots, landmarks, WCAG AA contrast in both themes, reduced motion; axe-core reports no
   violations on the welcome notebook in either theme. Open: the ⋮ menu's submenus (Send to scene, Change to)
   still open on hover only.

## Visual math input (2026-09-27, Alex: "a WYSIWYG editor for math cell inputs … eventually phase out the input interpretation")

The plan. A cell's source text stays the only thing saved and sent; the editor is a view of it, read
into a tree of notation and written back to text only when the cell is edited in visual mode, so
`.chalk` files, `%`, `let`, error spans and the golden corpus are untouched and the engine stays the
authority on meaning (ARCHITECTURE §4a). Symbolab-style holes, navigable by arrows, Tab and clicks;
the `\` menu grows templates (`\frac`, `\sqrt`, `\int`, `\sum`, `\diff`, `\mat2x3`, `\vec3`, `\abs`,
`\norm`) beside the Greek letters. Raw or visual per cell (a toggle and a shortcut; an optional `input`
field on the cell) and for all cells (View menu, a preference). Cells the grammar does not read —
λ-terms, order theory, `import("…")`, `⟦file⟧`, text that does not parse, very large literals — stay
raw with a note.

Decisions (Alex, 2026-09-27):
- `xy` is one name, as the engine reads it; a space or `*` is the product. (Symbolab reads `xy` as x·y.)
- New cells stay raw by default until the editor is complete (phase 4 below).
- Anything with a well-known notation uses it: d/dx, dⁿ/dxⁿ, ∫, ∫ₐᵇ, Σ, √, |x|, ‖v‖, z̄, Mᵀ, u·v,
  a determinant's bars around a matrix literal, Re/Im, sgn. Commands without one (rref, N, subst,
  expand, …) show as named functions.
- Hiding the input interpretation for visual cells is enough for now; clicking the visual input to
  explain a subterm (which needs the engine to report a text span per path) can wait.
  `inputRendered` stays in the protocol: Manim Studio's statement shot, explain on the input and
  the changed-subterm marks use it.

Phases:
0. Spike — DONE 2026-09-28: KaTeX it is. The tree as LaTeX (with `\displaystyle`) and `\htmlData` on
   every atom and hole, laid out by KaTeX — stretchy delimiters, matrices, ∫ and Σ with their bounds,
   determinant bars come free and the input looks like the outputs — with a caret line placed from
   the tagged boxes and a hidden textarea for keys, IME and phones (`view.ts`, `demo/`). In
   Chromium: a click just inside each of 65 atoms across the demo's inputs puts the caret on that
   atom's left edge within 3px and on its line (the two at 3.06px are the ½ exponent's edge);
   re-rendering on every key costs 2–3 ms for a typical cell and 5.5 ms for a 20×2 matrix.
1. Model, reader and writer — DONE 2026-09-27. `packages/math-editor`: the tree (`model.ts`), the
   engine's grammar reading into it rule for rule with the engine's error messages and spans
   (`read.ts`), the writer that puts back exactly the parentheses the engine needs and maps each atom
   to its text span (`write.ts`), and the notation as LaTeX following `Print.lean` (`notation.ts`).
   Tests: the grammar's hard cases (`2x/3`, `x/2y`, `-2^2`, `2^3^2`, `sin^2(y)`, `% 2` against `%2`),
   the golden parse errors word for word, read ∘ write the identity on all 258 golden sources and
   notebook cells the grammar reads, KaTeX rendering every notation with every atom tagged, and —
   where the native engine is built (CI) — every source and its rewrite evaluated side by side with
   the same parsed input and answer. Writing changes only spacing (`[1,2]` → `[1, 2]`, `a+b` → `a + b`).
2. Editor, basic — DONE 2026-09-28. The editing core (`edit.ts`): arrows walk the slots in the order
   they are on screen (d/dx then the body; ∫'s bounds, integrand, variable), ↑↓ between a fraction's
   parts, a matrix's rows, a bound's top and bottom and into and out of an exponent; Tab to the next
   empty slot, wrapping; Backspace enters a structure from its end and removes it once empty. The raw
   syntax typed into it still works — `diff(` opens d/dx, `,` is the next argument, `)` leaves the
   call, `[1,2;3,4]` fills a matrix, `/` takes what the engine would put in the numerator, a `)` that
   closes a whole denominator or exponent drops its parentheses and leaves the fraction — and `\name`
   inserts a symbol or a template (`\frac \sqrt \int \dint \sum \diff \mat2x3 \vec3 \abs \norm \T
   \det \dot \conj`), a template starting in its first slot on screen, with a list of what the name
   typed so far could become (the notebook's completion menu). A letter typed right after a `\` symbol
   is a product (`\pi r` is π·r; raw mode's `πr` is one name).
   The notebook: View › Visual math input (off by default) and a Visual / Text button on each math
   cell, Ctrl/⌘+Shift+M; the cell's choice is saved in the `.chalk` file (`mode`, optional). λ-terms,
   order theory (including `let D = divisors(12)`, which `cellKind` labelled a definition), file
   references and text that does not parse stay as text, and the button says why. The session's
   functions are the reader's `known`. Enter with an empty slot goes to it instead of running. A
   visual cell hides the input interpretation unless the source has a `%`.
3. Editing — DONE 2026-09-28.
   - Undo and redo (Ctrl/⌘+Z, Ctrl/⌘+Shift+Z, Ctrl+Y): a snapshot of the tree and the caret's path
     before each edit; a run of typed letters or of deletions is one step, and undoing a template goes
     back to the command as typed.
   - Selection (Shift with any move, drag, Shift+click, Ctrl/⌘+A): whole atoms of the smallest block
     holding both ends, so reaching into a fraction selects the fraction. Typing replaces it, `/` makes
     it a numerator, `(` parenthesises it; Copy and Cut give its source text.
   - Paste reads the text: an expression goes in as structure, anything else is typed as far as it
     goes. An image or SVG pasted into a visual cell is attached and the cell goes back to text.
   - The `let` head is an atom whose name and parameters are slots (it was `Stmt.let`, outside the
     tree): `let ` at the start makes one, `(` and `,` build the parameters, and the caret, Tab,
     selection and undo go through it like anything else.
   - `%`, `%%`, `%n` are Out[n] chips; the notebook says which output `%` names, and the tooltip is
     its text. With them a visual cell hides the input interpretation always.
   - A syntax error's span is marked on the atoms it covers (`atomsInSpan`). Only syntax errors carry a
     span and a visual cell's text reads by the engine's grammar, so this shows where the two disagree.
   - Signature help above a visual cell for the call around the caret that shows as `name(args)`;
     d/dx, ∫, Σ and the rest show their slots already.
4. Default and phones — DONE 2026-09-28.
   - View › Math input: automatic (the default), typeset or text; an earlier "visual on" preference
     carries over as typeset. Automatic typesets a cell only when it shows something the text cannot —
     a fraction, a power, a matrix, or a call in its own notation (`hasNotation`) — so a cell like
     `epicycles(llama, 60)` keeps its highlighted text (Alex: "a smart adapt/hybrid"). The choice is
     made for a cell's source when the cell is left, never while it is typed in. A `\template` typed
     (or picked from the `\` completions) in a text cell turns it typeset with the template where it
     was typed: the text is read with a placeholder in the command's place (`templateInText`).
   - Typeset cells keep the highlighter's colours: the notation asks the host to classify each token by
     what it is where it stands (a call's name, a variable bound by a binder or a head's parameters,
     another name, a numeral), and the notebook answers from its highlighter's sets.
   - A math keypad above a phone's keyboard while a math cell has the focus (View › Math keypad, on by
     default on narrow screens): fraction, power, root, d/dx, ∫, ∫ₐᵇ, Σ, matrix, |x|, π, parentheses,
     moves, next slot, run. In a text cell a template key turns it typeset where the text reads, and
     types the call (`sqrt(`) where it does not yet.
5. Retire the View › Input interpretation toggle (text cells still show it); explain on the input
   through engine-reported spans.

## Toolchain v4.34.1 (2026-09-27, Alex: "upgrade our engine to 4.34.1 since mathlib now has a 4.34.1")

- engine — DONE 2026-09-27. `engine/lean-toolchain` → v4.34.1. v4.34 deprecates `if_pos`/`if_neg`/`if_true`/
   `if_false` (for `ite_eq_left`/`ite_eq_right`/`ite_true`/`ite_false`, same statements); `LinAlgRref.lean` and
   `PipelineOrder.lean` use the new names, and the build's warnings are exactly v4.33.1's. `lake test` 0 failures,
   the welcome notebook 27 cells 0 errors, `npm test` green.
- wasm engine — DONE 2026-09-27, Emscripten 6.0.10. The runtime patch applies unchanged: `string_to_list_core`,
   the two libuv stubs (lean4#14973) and the tempfile/tempdir arity mismatch are all still present at v4.34.1.
   `engine-lean.wasm` 2.96 MB. All 200 math cells of the three bundled notebooks (show work and paths on) give
   byte-identical replies from the native and the wasm engine.
- proofs — DONE 2026-09-27. `proofs/lean-toolchain` → v4.34.1, Mathlib `rev` → tag v4.34.1 (d13f23b), `lake
   update mathlib` moved its dependencies in `lake-manifest.json`. Mathlib's cache host was unreachable from
   the session, so the 2,472 Mathlib modules the theorems import were built from source (84 min on 4 cores):
   2,799 jobs, 0 errors, no `sorry`. The bump's deprecations are gone: `if_pos`/`if_neg` → `ite_eq_left`/
   `ite_eq_right` (CxRules, Deriv, Fourier), `Mathlib.Data.Real.Sign` → `Mathlib.Basic.Real.Sign`, `push_neg`
   → `push Not`. The remaining linter warnings (unused simp arguments, tactics that do nothing) were not
   compared against v4.33.1.
- wasm, `-DLEAN_EMSCRIPTEN` — DONE 2026-09-27. lean.h lays out static objects' 64-bit scalars (a Name
   literal's precomputed hash) in two 32-bit slots only under that define, which the runtime had but the C
   emitted for Init, Std and the engine did not: every static Name literal carried a truncated hash. The engine
   never looked such a name up in a hash map (all 200 cells were identical before and after); Lean itself does,
   and failed at initialization. The runtime script records its flags and rebuilds its archives when they change.

## Lean cells (2026-09-28, Alex: "allow lean evaluation (as a cell) … let's use vscode's web editor + the lean4 extension for input and the proof obligation pane … Output will remain our cell output")

- Lean for wasm32 — DONE 2026-09-28. `npm run lean-wasm` (`scripts/build-lean-wasm-compiler.sh`) builds the
   whole v4.34.1 compiler from source with Emscripten 6.0.10: C for Init, Std and Lean emitted by the host
   `lean`, the C++ half, a generated symbol table (214,056 functions, 3,873 constants) standing in for `dlsym`,
   then Init's 649 modules compiled again into 32-bit oleans by the wasm `lean` under Node. Findings in
   `engine/wasm/UPSTREAM.md` §5. A cold build is ~1.5–2 h on 4 cores and keeps ~1.7 GB under `engine/toolchains/`.
- Language server in a worker — DONE 2026-09-28. `LeanWorker.lean` runs Lean's file worker over a shared-memory
   queue; `packages/engine-host/src/lean-server.ts` stands in for the watchdog. `scripts/smoke-lean-server.mjs`
   (Node): `#eval` gives 6765, a false `decide` reports its error, `$/lean/plainGoal` after `constructor` shows
   two goals.
- Editor — DONE 2026-09-28. `packages/lean-editor` on lean4monaco 1.1.16 (the vscode-lean4 extension and its
   infoview on monaco-vscode-api), talking to the worker directly. One document per notebook (cells between
   `--⁅cell⁆` lines, each cell a view of the one model with the rest hidden), the infoview in the panel's
   "Lean goals" tab, each cell's output the messages on its lines.
- Browser — DONE 2026-09-28. `scripts/smoke-lean-cells.mjs` (`npm run smoke:lean`, Chromium via playwright-core):
   the page isolates, `#eval double 21` shows 42 from the cell above (~7 s after load, warm cache), the math cell
   still evaluates, and the cursor after `constructor` shows 2 goals `⊢ q`, `⊢ p` in the Lean goals tab.
   The stall that took longest to find: in a browser, a thread started beyond the pre-created pthread pool never
   became ready while Lean waited on it; pool 32, `LEAN_NUM_THREADS=4`.
- Download: editor ~2.6 MB, server wasm ~24 MB, Init's oleans ~114 MB (all gzip) on the first Lean cell; the
   browser caches them.
- Open:
   - Deploy — DONE 2026-09-28 (Alex: the release route). `lean-wasm.yml` builds Lean when its inputs change on
     main and publishes it as a release named by `scripts/lean-wasm-key.sh` (Lean version + hash of the build's
     inputs; Emscripten pinned in `engine/wasm/emscripten-version`); `pages.yml` downloads the release its
     checkout names (none yet: deploys without Lean) and redeploys when the Lean build finishes. The bundle
     ships the server's wasm gzipped (121 → 24 MB) and the library in 64 MB parts, decompressed in the worker,
     so the site depends on no host compression and no file over 100 MB. Not yet run on GitHub: the first
     build starts when this merges (or from Actions › Lean for wasm › Run workflow).
   - Size: ship only the oleans an ordinary `import`-free file needs, or split the library by module and load it
     lazily; Std/Mathlib imports are out of reach at this size.
   - Monaco does not follow the notebook's theme toggle after start.
   - Adding, removing or reordering Lean cells replaces the document (Lean re-checks all of it); undo is one
     stack across the notebook's Lean cells.
   - Console noise: "unsupported" (VS Code APIs lean4monaco lacks) and cancelled requests (-32800).
   - Reloads downloaded Lean again — FIXED 2026-09-30 (Alex: "every time I reload the page, Lean is
     redownloading"). The HTTP cache does not keep entries the size of the library's parts (Firefox: 50 MB;
     Chrome: an eighth of its cache — reproduced with a 200 MB cache, which kept the 24 MB wasm and refetched
     both parts every load), and every deploy changed the files' URLs. The worker now keeps them in Cache
     Storage under a hash of their contents; the smoke test reloads under a 100 MB HTTP cache and checks
     nothing large is fetched, and a re-bundle with the same Lean fetched only the two small scripts.
   - Lean stuck spinning, "Got unsupported notification method: $/setTrace" — FIXED 2026-10-01 (Alex: "sometimes I
     get this and the notebook and tooltips just perma spin"). The in-browser watchdog relayed every client
     notification once the document was open; Lean's file worker ends its main loop on any it does not handle
     (and on a message without params), and the extension's `$/setTrace` came before or after `didOpen` by
     timing. The bridge now relays only what Lean's watchdog relays (didChange, cancelRequest, rpc release and
     keepAlive). `smoke-lean-server.mjs` sends those notifications after `didOpen`; the old bridge stops there.

## Example notebooks use visual input and Lean cells (2026-09-30, Alex: "make sure they make use of these cell types")

- order-lattices.chalk — DONE. The book's Lean code blocks are Lean cells now (25: the 14 blocks, and 11 new
   ones where the prose already described a Lean proof or computation — the relation properties, the `Nat`,
   product and bounded-`Set` instances, `3 ∣ 12` / `4 ∤ 6`, the `D12` interlude's `#eval`s, Exercises 2.1–2.3
   and 4.2, the `Bool` lattice `by decide`). One Lean file on core Lean alone, so some of the book's code had to
   change, listed in the notebook's coda: an `LE` instance for any partial order (low priority, so `Nat` keeps
   core's and `omega` still works), notation for `⊓ ⊔ ⊥ ⊤`, `Set` as predicates, `mul_eq_one_left`'s `calc`
   written upward (core has no `Trans` instance for `≥`), the partial-order fields `Dual`'s instance was missing,
   and the last step of `knaster_tarski`. Binders renamed `_` where unused, since a warning shows in the cell.
   `scripts/notebooks/check-lean.mjs` checks every notebook's Lean cells with the pinned Lean; CI runs it.
- welcome.chalk — DONE. A "Typing math" section (two cells kept typeset whatever View › Math input says) with the
   keys; a paragraph on Lean cells pointing at order-lattices, but no Lean cell: a first visit should not start a
   ~140 MB download and a reload. Fixed while there: the generator turned every `›` into a backtick, so the
   menu paths read "View ` Show all work"; it now converts only `‹…›` pairs.
- llamas.chalk — DONE. `exp(…)` written `ℯ^(…)` in its 14 cells, so they typeset as the prose's e^{ikt}; same
   answers, one more step each (`cx.euler-power`, eᵇ is exp(b)) when the work is shown.

## Files are values; the data table (2026-10-01, Alex: "Import anything and just display it … if we want to do something with it then we call functions on it like samplePoints")

- notebook: a file is a value — DONE. `import("url")`, `⟦name⟧` and `let x =` either keep the file as it came:
   name, media type (the server's, or the extension's when the server says text/plain or octet-stream) and
   contents (text, or base64). The cell shows it by what it is: an image as the image, CSV/TSV as a table, JSON
   (indented) and other text as text, anything else as a card with its type and size. Nothing is converted on the
   way in: a PNG no longer fails for having no paths. `apps/notebook/src/files.ts`. The engine still never sees a
   file. A file cell asks it to evaluate nothing, which fails and takes the next number, so `In[n]`/`%n` keep one
   count, and `%` after a file cell is that file. Functions called on a file are evaluated by the notebook before
   the cell is sent: `samplePoints(svg[, n])`, and for tables `matrix`, `column(t, k | "name")`, `row`,
   `dimensions` (numerals passed exactly, `1.5e3` as `1500`). A file anywhere else is an error naming the
   functions that apply (`llama is a file (SVG image), not a number: samplePoints(llama) …`), so
   `epicycles(llama, 60)` is now `epicycles(samplePoints(llama), 60)`; llamas.chalk binds `pts` once. A Markdown
   cell shows an attached table as a table. `notebooks/data/planets.csv` (NASA's fact sheet) is served with
   the examples for the reference's table examples. Tests: `apps/notebook/test/files.test.mjs` (`npm test`).
- notebook: the data table — DONE. One display for many rows, shared by a CSV file and a matrix output too
   large to typeset (more than 24 rows or 12 columns, alone as the output): column names or numbers and row
   numbers held in view, rows added 100 at a time as they scroll in, numeric columns right-aligned, entries still
   selectable for `explain`. It is the default form of such a matrix ("data table" in the output-form menu); the
   typeset forms remain, abridged as before. A file table's forms are "table" and "text".

## Selection and statistics (2026-10-01, Alex: "selection and statistics stuff for csv, json … in the usual engine way with proofs if possible"; Part syntax `x[[…]]`, 1-based, chosen over Python's)

- engine: Part — DONE. `m[[i]]`, `m[[i, j]]`, `m[[All, j]]`, spans `a;;b;;s` (both ends included; `;;b` and
   `a;;` as Mathematica reads them), lists `{i, j}`, negative positions from the end. Postfix, tighter than `^`;
   `[[` after a term was a nested matrix, already refused, so no input changes meaning. `part(m, …)`, `span`,
   `All()`, `List(…)` in the tree; printed back as typed and as `m\llbracket…\rrbracket`. `la.part` on a literal:
   a vector takes one index into its entries, a matrix rows then columns; a single index drops the dimension (a
   column stays a column vector). `partSpec_lt` (core Lean, in LinAlg.lean): every position a spec selects is in
   range, so the selection is the entries named and never `getD`'s filler. The visual input refuses a part (the
   cell stays text) and knows the new builtins.
- engine: statistics — DONE. `total`, `mean`, `variance`, `stdev`, `min`, `max`, `median` of a vector, or the row of
   a matrix's column statistics (Mathematica's convention); variance and stdev divide by n − 1. The variance is
   written `(Σxᵢ² − (Σxᵢ)²/n)/(n − 1)`, linear in n; the definition repeats the mean in each of n terms.
   `min`/`max`/`median` compare exact rationals and refuse symbols. One rule per statistic (`stat.*`) through
   `checkedLit`; termination is one generic lemma, `dec_statRule`. Engine tests: 33 more, in `partStatTests`.
- proofs: `Proofs/Stats.lean`. `total_soundR`, `mean_soundR` (the sum, the sum over the count),
   `variance_soundR` (the one-pass form is the sample variance Σ(xᵢ − x̄)²/(n − 1), via `sum_sq_dev`),
   `stdev_soundR`, `minQ_spec`/`maxQ_spec` (an entry, none smaller/larger), `medianQ_spec` (the middle of a
   sorted permutation, by core's `mergeSort_perm` and `sorted_mergeSort`).
- notebook: Part on files — DONE. A CSV takes rows and columns by position or by name in quotes (`t[["mass"]]` alone
   is that column); JSON takes keys and positions one level at a time, `All` applying the rest to each element
   (`j[["planets", All, "mass"]]`). The same semantics as the engine's, in TypeScript; a differential test runs 22
   specs through both, errors included. A selection of numbers goes to the engine as a numeral or matrix literal
   (parts after it stay in the source for the engine); one with text stays the notebook's: a smaller table, JSON,
   or text, shown and bound like a file. JSON that is a list of records or of lists shows as a data table.
   `column`/`row` gave way to Part; `matrix` and `dimensions` read JSON tables too.
- notebook: intellisense in `[[ ]]` — DONE. Signature help names the indices (`planets[[row, column]]`) and says
   what is in range: the rows and columns, a table's column names, an object's keys at the level being indexed,
   the shape of a name bound to a matrix (recorded from its output). Completions offer the names and `All`; a
   quoted name replaces what was typed, its closing quote included. Captions suggest parts with the file's own
   column names (`mean(planets[[All, "mass"]])`).
- visual input: parts and function names — DONE (Alex: "the new functions don't work in visual mode and don't
   show in autocomplete"). A `part` atom in the editor's tree (`x[[…]]`, postfix like `sup`): read from the text and
   written back exactly, drawn `x⟦All, “mass”⟧` (spans as `;;`, lists in braces, a quoted name as text), typed as
   `[[` after a value (the first `[` makes the matrix it always did; the second turns it into a part). In an index,
   `,` moves to the next one outside braces and quotes, `]` leaves the part and the second `]` is taken, and every
   character inside quotes is the name's. The reader lexes a quoted name, which only a part's index may hold;
   elsewhere it is the engine's `unexpected character '"'`. Completions: the visual input lists functions for a
   name being typed (`functions`, from the Reference, as the text input does; Enter takes one only once picked),
   and in a part's index the column names, keys and All (`partNames`), with the same signature line as text. Each
   statistic has its own Reference entry, so `var`, `med`, `stdev` complete and `variance(` has signature help.
- notebook: `%n` as a file, and the suggestions bar — DONE (Alex: "dimensions now doesn't work. But also the `Try: ...`
   is a bit obnoxious. This could be like mathematica's Try: bar that's dismissable"). `dimensions(%18)` read `%`
   then a stray `18`: the reference pattern tried `%%…` first, which matches nothing; digits go first now (with a
   test). The caption's "Try:" line, which spelled out a whole `import("…")` per example, is Mathematica's
   suggestions bar: short chips (`row 1`, `column "id"`, `mean "id"`, `matrix`, `dimensions`), the code in each
   tooltip, written against the cell's name or `%n`; a chip adds its code as a cell below and runs it; × hides the
   bar for that cell (saved with it), View › Suggestions bar for all. Errors offer only the suggestions that make
   numbers.
- visual input: import, files and the notebook's functions; names in completions — DONE (Alex: "get the new
   functions + import working in visual mode. Also visual mode is lacking the autocomplete/intellisense"). The
   notebook's own functions (`import`, `samplePoints`, `matrix`, `dimensions`) are calls in the visual input, as the
   engine's builtins are (`dimensions(%18)` had read as a product). Two atoms in the editor's tree: text in quotes,
   whose characters are typed as they are (a URL's `/` is a slash, not a fraction), and an attached file, `⟦name⟧`,
   drawn as a chip; both read and write back exactly, so file cells are no longer kept out of the visual input,
   and a file pasted or attached into one lands as a chip at the caret. Completions in both inputs list the names
   bound in the session before the functions, with what each is (`planets — CSV, 8 × 5`, a matrix's shape, a
   function's parameters); a function opens its call, a value does not. `dimensions` has its own Reference entry.
- verification: the ledger, matrices and the systems search — DONE 2026-10-03 (Alex: "what can we work on to work
   towards 100% engine verified status"). The ledger had 13 rules the engine reports and never listed (the matrix
   arithmetic, `cmd.simplify`, `cmd.subst`, `cmd.N`, `la.context`, `simp.sort`, three order steps); each has an
   honest entry now, and an engine test fails when a pipeline rule is missing from it. `proofs/Proofs/Ledger.lean`
   reads the ledger from the engine and fails the build unless every theorem a note cites exists; on its first run
   it caught two names that no longer did (`List.sorted_mergeSort`, `Complex.abs_apply`). `subst` uses the
   structural `substVar`, so `cmdSubst_soundR` reads it over ℝ. Matrices get a value: `evalV` (`Matrix.lean`), a
   real number or a matrix with its shape, extends `evalD` (`evalV_of_noLit`), and `la.add`, `la.scalar-mul`,
   `la.mul`, `la.transpose`, `la.det` (Laplace expansion is Mathlib's `det`), `la.pow` and `diff.matrix` are proved
   against it, for a node whose children are normal (`litAtRoot_of_normal`, from `normal_facts`). The systems
   world's search is `exploreWith`, a breadth-first search over any successor function, and `SystemsProofs.lean`
   proves a returned graph has exactly the reachable states, each once, and exactly their transitions; `reach`,
   `invariant`, `unreachable`, `inductive` (`allStates_mem`), `refines` and the no-deadlock answer are verified.
   Finding: with more initial states than the search's limit, the old loop stopped with states unexpanded and could
   report a deadlock that is not there; the search now refuses. Open: shortest traces, the CTL fixed points, the
   lasso search, `rel.wellfounded`, `trs.critical`, `order.concepts`, the symbolic row operations, `cmd.factor`.
- the conditional laws, split at their assumptions — DONE 2026-10-03 (Alex agreed to "prove the unconditional
   fragment, keep the rest conditional with the condition shown in the step"). `simp.collect-powers` now merges only
   pairs that obey `b^m·b^n = b^(m+n)` at every real base, integer exponents of one sign or a positive numeral base,
   and is verified (`collectPowers_soundR`, through `rpow_int_add_of_sameSign`); `simp.collect-powers.assuming`
   merges the rest and its step ends "Assuming $x \neq 0$." (integer exponents) or "Assuming $x > 0$."
   (`collectPowersAssuming_soundR_on`). `simp.function` keeps every case that holds for every real number and is
   verified (`functionRules_soundR`, `SimpAll.lean`); `simp.function.assuming` takes `exp(ln x) = x` and
   `ln(b^p) = p ln b` for a non-integer `p`, assuming the argument positive (`functionAssuming_soundR_on`). Finding:
   the old ledger note called every case but `exp(ln x)` unconditional, but `ln(b^p) = p ln b` fails at `b = -2`,
   `p = 1/2`; with an integer `p` it holds everywhere, since `Real.log` is `ln |x|`. Answers are unchanged: the
   two halves fire on exactly the cases the whole rule did. `normalizeSafe_sound` folds every simp rule but the two
   that assume.
