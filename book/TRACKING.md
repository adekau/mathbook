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
