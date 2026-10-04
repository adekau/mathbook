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
  negation are derived forms; the printer recovers the notation. Operators with no node of their
  own are calls: MATLAB's entrywise `A ./ B` and `A .* B` parse to `ediv(A, B)` and `emul(A, B)`
  (`la.ediv`, `la.emul`), so `/` and `*` keep their matrix meaning, `A·B⁻¹` and the product. Fewer node kinds means fewer
  rewrite rules and fewer proof cases.
- **Numbers.** `Q` wraps core Lean's `Rat` (normalized by construction) plus a presentation-only
  "approximate" flag. Mathlib's `ℚ` *is* that `Rat`, so the identification is `rfl`
  (`proofs/Proofs/Q.lean`). There is nothing to prove about the arithmetic; what must be proven is
  how the engine uses it, which is the per-rule soundness theorems.
- **Show work is not reconstructed after the fact.** Rewriting records every rule firing as a
  `Step` with the whole term before and after and the path where it fired. The derivation *is*
  the computation, viewed as data.
- **Work costs what is read.** Every step carries the whole term before and after it, so the
  derivation of a big term is quadratic in it: 200 steps on a 100-row table were 10 MB of reply.
  Two things keep it in proportion without capping it. A run of rewrites inside one matrix's entries
  is one step, `la.entrywise`, whose nested steps carry the entry alone (`buildSteps`), so an
  entrywise computation is linear in the matrix and reads as a textbook writes it, `2A` then the
  arithmetic of each entry. And the notebook asks for a derivation's *outline* (each step's rule,
  explanation and path, and whether it prints the same before and after) and fetches the terms
  with `engine.steps` when a cell's work is opened; the session already keeps every cell's
  derivation, for `explain`, so nothing is computed twice and nothing is left out.
- **Termination is a proof obligation, not a budget.** A rule bundles a proof that it strictly
  decreases a measure; `normalize` is well-founded on that measure and never `partial`. The
  verified `simplify` uses one additive measure (`Rewrite.lean`). The whole notebook pipeline —
  commands, `diff.*`, `la.*`, `simp.*`, the two parity rules, the radical rules — uses the six-tier ordering of
  `Order.lean` and the innermost rewriter `normalizeT` (`Terminate.lean`), whose obligation is
  conditional: a rule must decrease the ordering *on a node whose children are already normal*.
  That hypothesis is what lets the product rule duplicate its body. The theorem is
  `pipelineOrdered` (`PipelineOrder.lean`), one lemma per rule. Rules that delegate to code the
  ordering cannot see into (commands, matrix arithmetic) have their outputs *checked* for the tier they
  must decrease rather than proved; what the matrix rules compute is proved separately, against `evalV`.
  There is no step budget anywhere: `expand` distributes by a total function
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
  `M`), and the printer displays the single-power form the textbook way. `√a = a^(1/2)` is a
  silent rule where the two print alike and a visible `simp.radical` step where they do not
  (`√18` shows as `3√2`); the arithmetic the textbook writes out (`√32 = (2^5)^(1/2) = 2^2 · 2^(1/2)`)
  lives in the explanations, since those intermediate forms are heavier than the input and could
  not be steps. `RadicalRules.lean`.
- **The λ-calculus is a second world in the same engine.** `Lambda.lean` has its own terms, parser
  and normal-order β-reducer; terms are encoded into `Expr` for the wire, so selection, explanation
  and origin tracking work unchanged. The de Bruijn view is computed with every step. Reduction is
  on fuel, the one budget in the engine, because normalization is undecidable: `Ω` is refused after
  `maxSteps` (10,000), and so is a term that grows past `maxSize` symbols (a fixed-point combinator
  unfolding under call by value). A long reduction keeps its first and last steps, by count and by
  the total size of their terms, and one `lambda.elided` step says how many it leaves out.
  A definition without a normal form (`fact := Y F`) is bound unreduced instead.
  Every step is proved a β-step (`LambdaBeta.lean`): renaming keeps a term's de Bruijn form and
  leaves nothing to capture, capture-free substitution is de Bruijn substitution, and so each step of
  every strategy is one step of `DB.Beta`, β-reduction on terms taken up to α.
  A cell may begin with a command and a colon: a strategy (`normal`, `cbn`, `cbv`, `applicative`,
  each with an optional step count), `eta`, `fv`, `db`, `alpha` and `subst` are the untyped
  calculus's questions, and `type`/`infer` the simply typed calculus's (`Stlc.lean`). Terms parse with
  their binders' types (`λx:A. e`), which reduction erases. `type:` checks a fully annotated term and
  returns the derivation tree, and `check_sound` (`StlcProofs.lean`) proves the checker's derivations
  are typing derivations. `infer:` makes one type variable per missing annotation and per application,
  solves the equations by unification with the occurs check, and then runs the term, annotated with its
  answer, back through the checker, so an inferred type is a type of the term. That it is the most
  general one (Hindley's theorem) is `infer_principal` (`StlcPrincipal.lean`): unification is most
  general (any solution factors through the one found), and generation is complete (any typing of
  the term solves the equations). A λ-command is routed before the other worlds,
  since `type: f : A → B ⊢ f` holds a connective.
- **Finite order theory is a third world.** `Poset.lean` decides everything over lists — closure,
  the partial-order check, covers, bounds, join and meet, lattices, monotone maps, fixed points by
  the Kleene chain — and `PosetProofs.lean` proves the decisions mean the textbook Props. Values
  are encoded into `Expr`; the notebook draws Hasse diagrams from the covers.
- **Replicas are simulated in the systems world.** `replicas(type; a, b; events…)` (`Replicas.lean`)
  runs a state-based CRDT through a schedule of local updates, syncs and delayed or duplicated
  messages. Every type there is a vector of naturals merged by the entrywise maximum, so one merge
  serves them all, proved a join with every update an inflation (`ReplicasProofs.lean`).
- **Term rewriting is in the systems world too.** `let R = rules(l -> r; …)` binds a first-order
  rewriting system (`Rewriting.lean`, its terms a nested inductive with the recursion written as
  mutual definitions so that it can be proved about). `rewrite` takes leftmost-outermost steps,
  `terminates` checks a linear interpretation (the size by default) and `critical` finds critical
  pairs by unification and joins them. `RewritingProofs.lean` proves the steps sound and the
  termination check sound and exact; unification, and so the completeness of the critical pairs, is
  not proved.
- **Commands nest by naming.** Order and systems commands take names; a call written inside another,
  `product(chain(2), chain(3))`, is evaluated first, bound to a hidden name and put in its place
  (`Nested.lean`), its derivation a sub-derivation of the outer cell's first steps. It is a rewriting
  of the source, so no proof changes.
- **Relations live in the order world.** A poset is a relation with three properties built in; a
  relation (`Relation.lean`) is elements and pairs with nothing assumed, so the properties become
  questions. Each check names the elements that break it, and the reply marks those pairs on the
  graph it sends. Closures add the pairs a property forces, the transitive one round by round, a
  round a step, until a round adds nothing; `RelationProofs.lean` proves the result transitive and
  inside every transitive relation containing the original, so the least. The round loop has fuel
  `n² + 1` and reports whether it settled, and the proof of transitivity is conditional on that
  report, which the engine checks: a closure that did not settle would be an error, not an answer.
  Kernels, classes, refinement, cycles and measures complete the set that well-founded induction
  and quotients need.
- **Finite algebra is the order world read the other way.** A lattice is an order with joins and
  meets, or a set with operations obeying laws; `Algebra.lean` is the second reading and the bridges.
  An operation is its table (`op`, or `joinop` of a lattice); its laws are decided over every pair or
  triple, and a failure marks the table's cells it read. A semilattice induces an order
  (`x ≤ y ⇔ x · y = y`), which `AlgebraProofs.lean` proves is a partial order whose join is the
  operation, so the two readings meet. Distributivity, complements and Boolean lattices, products,
  maps between posets, Galois connections, closure operators, concept lattices and Denning's flow
  check complete it. Elements can be pairs `(x, y)` (a product's) and sets `{a, b}` (a powerset's);
  the parser reads them anywhere an element goes, and names are compared by a canonical key (spacing
  dropped, a set's members sorted), in cells and in exercise answers.
- **Transition systems are a fifth world.** `Systems.lean` reads a system (variables over finite
  domains, an init condition, guarded actions with simultaneous updates; clauses separated by `;` or
  line breaks) and decides questions on its finite state graph: reachability by breadth-first search,
  so counterexamples are shortest traces; invariants; inductiveness, refuted by a counterexample to
  induction that says whether its state is reachable; deadlocks; CTL by least and greatest fixed points
  of predicate transformers, each Kleene round a step; liveness under weak and strong fairness,
  refuted by a lasso found among strongly connected sets; refinement under an abstraction map. A trace
  is the derivation, a step per action, so the notebook's stepping applies; each step is re-run against
  the system before it is reported (`checked`). "Holds everywhere" answers rest on the search, which is
  proved: `exploreWith` is breadth-first search along any successor function, and `SystemsProofs.lean`
  shows a returned graph has exactly the reachable states, each once, and exactly the transitions
  between them, so an invariant, an unreachable state, the absence of a deadlock and a refinement are
  decided on all of them; `allStates_mem` does the same for the assignments `inductive` checks. The
  search refuses rather than returns when it cannot expand every state it found (more initial states
  than its limit used to leave some unexpanded). A CTL answer carries a certificate read off its Kleene
  rounds (each state's round is its rank), checked before it is reported; `CtlProofs.lean` proves that
  where the check passes the set is exactly the states where the formula holds by the meaning of its
  paths, infinite paths and paths that stop included. Shortest traces and the lasso search are not
  proved yet. Guards reuse the logic world's formulas, evaluated over the
  state with names (`idle`, `true`) as values.
- **Logic is a fourth world.** `Logic.lean` reads formulas of propositional logic and bounded
  first-order formulas over finite sets of numbers, with its own grammar (ASCII spellings read as
  the glyphs). Propositional questions are decided by truth table, and `LogicProofs.lean` proves the
  table decides: a formula's value depends only on its variables, every assignment to them is a row,
  so what holds in every row holds everywhere. Normal forms are rewrites, one law a step (→ and ↔
  eliminated, De Morgan, double negation, constants, distribution, complementary literals), each
  pass a total structural function proved to keep the value under every assignment. Bounded
  quantifiers evaluate their atoms with the math pipeline and name the element that decided them.
  These rules are outside the notebook pipeline's termination ordering because they never run in
  it: each is a pass over the formula, structurally recursive, and Lean's own termination check is
  the obligation. A `truthtable` reply carries the table as a visual spec.
- **Plots are sampled by the engine and drawn by the notebook.** `engine.plot` simplifies the
  function under the session, records the cell, and returns a uniform sample with `null` where the
  value is not finite; the notebook's SVG and the studio's graph shot are presentation only.
- **Manipulate is every frame at once.** `manipulate(e, p, from, to[, n])` (`engine.manipulate`,
  `manipulateCell`) evaluates `e` as a cell would for `n` exact values of `p` from `from` to `to`, the
  session's names substituted before `p` so a name bound to a term in `p` moves with it, and a `plot`
  body sampled at every frame; the cell records the first frame. Any other body keeps its calculation
  at each frame (`workChain`: the body with `p` put in, then each step's whole term), and
  `column(e₁, e₂, …)`, Mathematica's `Column`, makes a frame of several parts, each evaluated as its
  own cell. The notebook shows the frames under a
  slider in the cell's output, as Mathematica does, so dragging and ▶ Play never wait for the engine;
  a plot keeps one window for all its frames, and while it plays the page blends neighbouring frames'
  samples (same grid) for smooth motion, showing the engine's own frame wherever the slider stops.
  The frames are not saved: the cell runs again when its notebook opens. A slider on a `let` is the
  other control: it re-runs every cell that read the name, which suits several cells following one
  number but not animation.
- **Integration is checked, not found.** `Antiderivative.lean` guesses an antiderivative with a
  few textbook rules and proves nothing; `cmdIntegrate` differentiates the guess with the pipeline
  and accepts it only if the normal form is the integrand itself. `cmdIntegrate_spec` states that;
  `proofs/Proofs/Integrate.lean` reads it as `deriv F = f` wherever the differentiation shown is
  sound, which the statuses of its steps report. Because a rule set cannot contain a rule that
  normalizes with that set, the pipeline is `pipelineRulesWith norm`, generic in the checker's
  normalizer, and `Integrate.lean` closes the knot: the checker is the pipeline with nested
  `integrate` refused, and the notebook's pipeline is the pipeline with that checker.
- **An exercise is checked by normal forms.** `engine.check` (`Exercise.lean`) evaluates a question
  like any cell (its value is the expected answer, its derivation the worked solution) and reduces the
  reader's answer too; the two are equivalent when their canonical forms are equal — the integration
  check's `identNorm` and `dist`, normalized — as two λ-terms are β-equivalent when they reduce to the
  same normal form (λ answers are compared by their de Bruijn terms; a λ-command's answer is compared
  as written — a strategy's result up to α without reducing it, free variables as a set, `type:`'s
  type exactly and `infer:`'s up to the names of its type variables). "Not equivalent" is "not shown
  equivalent". An answer that calls the question's own commands (`diff` for a `diff` question) is
  refused, and a check is not an evaluation: no `In[n]`, no binding, `%` untouched. In the logic
  world the comparison is decided rather than canonical: two formulas are equivalent exactly when
  their truth tables agree, a `cnf`/`dnf`/`nnf` answer must also have that shape, and a `sat` answer
  may be any satisfiable formula that implies the question's (an assignment is one). In the order
  world an answer is the value itself (`a->b, b->c`, classes `{a, b}, {c}`, `true`), compared as a
  set, so order does not matter.
- **Soundness is a fold, over whichever semantics you bring.** `RewriteSound.normalize_sound_for`
  is stated for an abstract `Congruence` (reflexive, transitive, a congruence under `withChildren`,
  invariant under `canon`). Supply those four facts for a new semantics and normalization's
  soundness follows without touching the rewriter. The integer fragment and ℝ are two instances.
- **Semantics are added in layers, never edited.** `eval?` (integer fragment, M1) ⊂ `evalR` (ℝ, M3) ⊂ `evalD` (ℝ with
  derivatives, M4) ⊂ `evalV` (values: a real number or a matrix with its shape, `proofs/Proofs/Matrix.lean`), each
  with a theorem that the previous one is a restriction of it. A new layer extends rather than
  replaces because the earlier theorems are stated against the earlier semantics; widening in place would silently
  restate them. It is also forced here: `evalR` cannot interpret `diff`, whose second child is a binder that `Expr`
  does not distinguish from a value, and a semantics reading it breaks the congruence M3's fold needs.
- **A rule that needs a side condition says so, in its step.** Over ℝ, `x·x⁻¹ = x⁰` holds only for
  `x ≠ 0`, `x^a·x^b = x^(a+b)` and `ln(b^p) = p ln b` only for a positive base, and `exp(ln x) = x` only for
  `x > 0`. The engine keeps the usual computer-algebra behaviour, but each law is split at its
  assumption: `simp.collect-powers` and `simp.function` are the cases that hold for every real number
  (proved unconditionally), and `simp.collect-powers.assuming` and `simp.function.assuming` the cases
  that need the assumption, whose explanation states it ("Assuming $x > 0$.") and whose theorem takes
  it as a hypothesis; `proofs/` also *proves* that no unconditional theorem exists for them. Silence is
  not an option: either a rule has an unconditional theorem or its condition is written down where
  the step is shown.
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

The visual math input (`packages/math-editor`) is the one exception to "does not parse", and it
reads notation, not meaning. A cell's source text stays what is saved and what the engine is sent.
The editor reads that text into a tree of notation (fractions, powers, calls, matrices) by the
engine's own grammar, shows it, and writes it back to text when the reader edits. What the text
means is still the engine's parse of it. The reader has to agree with `Parser.lean` exactly, or the
input would show a fraction where the engine reads a product, and its tests hold it to that: every
golden source and notebook cell is round-tripped and, against the native engine, has to mean the
same thing before and after.

**Manim Studio** is the third tab. "→ Scene" on an evaluated cell turns its derivation into shots:
the statement, then each step's `afterRendered` term (an optional field on `Step`, per protocol
rule 5). The page adds what a storyboard needs and nothing more — order, on/off, an animation name,
a duration — previews a shot by matching KaTeX glyphs between consecutive terms (longest common
subsequence, then interpolated position and opacity, a browser-side stand-in for
`TransformMatchingTex`), and prints the Python a Manim user would run. Rendering the video is
Manim's job, outside the browser.

**Courses** (File › Courses and examples) opens a tab beside the studio that lists *projects*:
notebooks that belong together, either a course (lessons read in order) or a collection. They are
`notebooks/courses.json` and `notebooks/courses/<course>/*.chalk`, generated by
`scripts/notebooks/mk-courses.mjs` and served under `examples/`. A lesson opens in its own tab with its
place in the project (`project` in the file), a bar with the previous and next lessons, and its
exercises answered, which the page remembers per lesson in local storage. The lessons are built from
what the shell offers for teaching: exercise cells (checked by `engine.check`, §3), steps held back
to be revealed one at a time, sliders on `let n = number` that re-run the cells out of date because of
them, and Markdown callouts. Every lesson's answers are pinned in `notebooks/golden/` and checked in CI.

**Help › Documentation** opens a tab beside the studio: a guide to the notebook (cells, input,
reading the work, files, lookups and their set-up, Lean cells, the studio) and the reference pages.
The pages are Markdown in `src/docs.ts`, drawn by the Markdown cells' renderer; their tables (the
symbols and templates, the shortcuts, the example notebooks) are built from the lists the notebook
itself uses. Every function has a page of its own, laid out as Mathematica's are — usage lines,
details, examples in sections, related functions — from `src/reference.ts`, which is also where
completion, signature help and the sidebar's command list read their entries. A page holds only the
examples' inputs: the engine evaluates each section in a session of its own when the page is shown,
so the outputs are this engine's and cannot go stale (a section that reads a file or asks a question
is shown as inputs, with *Open in a notebook*).

## 4b. Lean cells

A Lean cell is Lean 4 itself, checked as you type, in the browser: the VS Code editor with the Lean 4
extension (lean4monaco, pinned) as its input, what Lean reports on its lines as its output, and the
infoview — goals at the cursor — in the panel's Lean goals tab. It is the one part of the notebook that
does not go through the engine's protocol: the engine answers `engine.*` for math cells, Lean's own
language server answers LSP for Lean cells.

- **Lean compiled to wasm32.** `scripts/build-lean-wasm-compiler.sh` (`npm run lean-wasm`) builds the whole
  compiler — parser, elaborator, kernel, IR interpreter, language server — from the C the host `lean` emits
  for the tagged sources, linked statically with Emscripten. Lean's IR interpreter finds compiled code by
  name; a static link has no dynamic symbol table, so a generated table (name hash → address,
  `scripts/lean-wasm-symtab.py`) stands in for `dlsym`. An `.olean` is a memory image with pointer-sized
  fields, so the library is compiled again, by the wasm `lean` under Node, into 32-bit oleans
  (`scripts/lean-wasm-oleans.py`; Init today). The patches to Lean's sources are in
  `engine/wasm/lean-compiler-emscripten.patch`, the upstream findings in `engine/wasm/UPSTREAM.md`.
- **The server in a web worker.** `engine/wasm/server/LeanWorker.lean` runs Lean's file worker with
  stdin/stdout over a shared-memory queue (`leanweb.c`); `packages/engine-host/src/lean-server.ts` plays
  Lean's watchdog for one document (answers `initialize` with the reply Lean's own watchdog gives, printed
  at build time; drops the cross-file index traffic). The server is threaded: it reads LSP while
  elaboration runs in tasks. So the page must be cross-origin isolated, which a static host gets from
  `coi-sw.js`, a service worker registered the first time a notebook has a Lean cell (one reload). In a
  browser each thread is a worker and one started beyond the pre-created pool is not ready in time, so
  the pool is large (32) and Lean's own pool is capped (4).
- **One document per notebook.** The notebook's Lean cells, in order, are the stretches of one Lean file
  between separator comment lines; each cell's editor is a Monaco view of that one model that hides every
  other line (`packages/lean-editor`). Definitions carry from cell to cell, editing a cell re-elaborates
  it and the cells after it, and every position the extension and the infoview use is real — nothing is
  translated between cells and file.
- **Lean exercises.** An exercise can ask for a proof instead of a value. Its statement (ending
  `:= by`) and the reader's proof are two cells of the same Lean file: the statement a cell no view
  shows (so it cannot be edited), the proof a view of its own. The verdict is Lean's: proved when the
  two have no error and no `sorry`, read once Lean's `$/lean/fileProgress` says it has finished
  checking the file's current version, so a verdict is never about text Lean has not seen. CI checks
  every shipped Lean exercise with the author's proof (`scripts/notebooks/check-lean.mjs`).
- **A course's Lean prelude.** A project with `leanPrelude` gives each lesson the Lean of the lessons
  before it (their Lean cells, and their Lean exercises with the author's proofs) as a first cell no view
  shows, so a course builds one development across its lessons. It is saved with the lesson, and CI
  checks each lesson with it in front. Lean elaborates it each time a lesson opens, so it leaves out
  the earlier lessons' commands that only show something (`#eval`, `#print`, `#check`, `example`;
  `leanForPrelude` in `packages/lean-editor/src/prelude.js`, which the CI check shares). That is
  most of what can be cut: the CRDT course's last lesson still has about 2,800 lines in front of it,
  some 5 s of one native thread, mostly the kernel checking the book's structures and proofs.
  Compiling each course's prelude to 32-bit oleans with the wasm Lean, imported instead of inlined,
  would make it a download; that is not built.
- **Cost.** Nothing loads until a notebook has a Lean cell. Then, compressed: the editor (~3 MB), the
  server (~24 MB) and Init's 32-bit oleans (~114 MB: their private parts, proofs included, are most of it,
  and an ordinary file's implicit `import Init` needs them), once per browser: the worker keeps the large
  files in Cache Storage under an id of their contents (a browser's HTTP cache will not hold entries that
  size, and the files' URLs change with every deploy), so they are downloaded again only when Lean changes. The site gets Lean from a
  release `lean-wasm.yml` publishes whenever Lean's build inputs change (`scripts/lean-wasm-key.sh` names it),
  so a deploy does not spend two hours building it.

## 4c. Lookups (`?` cells)

A math cell that starts with `?` is a question — `?volume of a cone`, `?the first ten primes`,
`let mlb = ?MLB runs and home runs per game for the last 20 years` — answered by a language model
running on the reader's machine, as *source text* the engine then evaluates like any other cell: a
number, a list `[a, b, c]`, a matrix, or a formula (`B*h`; `let V = ?…` defines `V(B, h)`). So the
page still owns no mathematics: the answer is engine input, parsed and normalized by the engine, and
everything after it keeps its steps. The pipeline is `packages/ask`; the notebook's side (models,
settings, the cell) is `apps/notebook/src/ask-cells.ts`.

- **The model plans first.** It says what shape the answer has, names its parts, writes searches,
  names the subject, and says whether the answer is standard knowledge. Standard knowledge of
  mathematics or physical science (a formula, a constant) it answers itself, and nothing leaves the
  machine; the answer is labelled "from the model's knowledge" and the cell offers *Check with a
  search*. A question about the world (teams, people, places, events) is always searched for: a small
  model is sure of far more such facts than it gets right. Where the question's words fix the
  shape ("how many", "the number of", "formula"), they decide it, not the model.
- **The model answers from what was found, in the question's shape.** It is given the stretches of
  the pages read most likely to hold the answer: paragraphs ranked by the question's words they share
  (a page's opening paragraphs, which sum it up, a little ahead) and tables ranked by caption, column
  names and best row, as much as the model's context takes (about 7,000 characters for a 4k-token
  browser model, 30,000 for a cloud one). A table too big for that keeps the rows with the question's
  own words, or its first rows and its last. Held to a JSON schema, the model answers with the
  numbers (or the formula), its sources and a quote; or a model that can search the web itself
  (OpenRouter's web search) does, and its citations are the sources.
- **What the model says is checked, not trusted.** Every number it gives is looked for in what it
  read (a number written in words counts) and flagged ⚠ when it is not there. A formula is read from
  the LaTeX it quotes by code (`tex.ts`), never from the model's translation, and flagged when the
  pages do not write it that way. A question that asks to make something (a random matrix) is no
  lookup and is refused before any search. The model's memory is the last resort, and an answer
  from it is flagged throughout.
- **Why not have the model pick and code copy.** An earlier version showed a small model previews of
  the tables found and had it choose a table, columns and a row range while code copied the cells,
  to keep it from inventing numbers. It chose the wrong table as often as a model misreads a page
  (asked how many World Series the Tigers have won, it counted a table of their best seasons), and
  it read the prose last, though the article's opening said "four". Reading what was found and
  checking the numbers works better with every model tried.
- **Sources are generic, not per subject.** Wikipedia (no key, and it allows other origins) and, if
  the reader sets one, a SearXNG-style endpoint that queries Google, DuckDuckGo, Bing and Brave.
  Most sites refuse cross-origin reads, so a web result is read directly when it allows that and
  otherwise through a page reader the reader configures (`scripts/ask-proxy/worker.js` is one).
  Google's Custom Search API closes on 2027-01-01 and DuckDuckGo has no results API, so neither is
  built in.
- **Models.** Chrome's built-in model (the Prompt API) where the browser has it; elsewhere a WebGPU
  model through WebLLM, bundled separately (`dist/ask/`) and loaded only when a lookup needs it, its
  weights downloaded once from Hugging Face; or, chosen in the settings, a model Ollama serves on
  the reader's own computer (`/api/chat`, held to the schema by its `format`), which can be larger
  than a browser holds; or a cloud model through OpenRouter on the reader's own account (signed in
  with OpenRouter's OAuth PKCE flow from a window that returns to `openrouter-callback.html`, the
  key kept in the browser). Settings has a *Test the model* button that times one small question.
- **What is sent.** With a model on the reader's computer, only a search sends anything: the search
  terms the model wrote, to the sources. With OpenRouter, the question and what was found go to
  OpenRouter and the model's provider. Never the notebook. The first search asks first.
- **Saved with the cell.** The answer, its shape, where it came from and how it was found are saved
  in the `.chalk` file, so running the notebook again evaluates the saved answer without asking
  again; *Look up again* asks afresh.

## 5. Visuals

The engine never draws. It emits **visual specs**: declarative JSON next to `rendered`
(`EvaluateResult.visuals`): a Cayley table, a graph, a commutative diagram, sampled plot data, a
matrix heat map. Six kinds exist (`KnownVisual` in the protocol): `logic.truthtable`, the rows of a
formula's table; `relation.digraph`, a relation's pairs with the ones that break a property (`bad`)
and the ones a closure added (`added`), and, for a state graph, where each step of the work is on it
(`steps`: the transition it takes or the state it is at), so stepping through a trace marks the
current transition (with the answer's marks held back until the answer shows); `algebra.optable`, an operation's table with the cells a
failing law read (`marks`); `context.table`, a formal context's cross table; and `typing.tree`, a
typing derivation as nested judgments, each with its rule and premises; and `replicas.spacetime`, a
replica simulation's lanes, events and messages, with the events each step made. The notebook draws the tables
and the proof tree as HTML and the graph as SVG, keeps them with the cell in a saved file, and ignores a kind it does not know. The frontend owns
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
