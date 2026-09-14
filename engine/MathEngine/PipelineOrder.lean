import MathEngine.Pipeline
/-!
# Termination of the notebook pipeline

`pipelineOrderedWith norm : Ordered (pipelineRulesWith norm)` — every rule of the pipeline decreases the tiered
ordering `μ` (Order.lean) on a node whose children are normal. The proof is one lemma per rule,
grouped by the tier that does the work:

* commands (tier 1) — a command node is consumed; its output is *checked* to contain none;
* `diff.higher-order` (tier 2) — the three-argument `diff` is consumed;
* `la.*` and `diff.matrix` (tier 3) — one node on the path to a literal disappears;
* `simp.*`, the parity rules and the remaining `diff.*` (tier 4, `M`; tier 5, `size`).

The facts about normal forms this needs are proved first: a normal term has no command node, no
malformed `diff`, and no matrix literal below its root (every such node is fired on by some rule —
the commands and `diff.higher-order` refuse malformed arguments, `la.context` refuses a literal in
any position the matrix rules do not evaluate).
-/
namespace MathEngine
open Expr

variable {norm : Norm}

-- ---------------------------------------------------------------------------
-- Membership
-- ---------------------------------------------------------------------------

theorem mem_pipeline_iff (r : PlainRule) : r ∈ (pipelineRulesWith norm) ↔
    r = cmdSimplify ∨ r = cmdExpand ∨ r = cmdRref ∨ r = cmdN ∨ r = cmdSubst ∨ r = cmdIntegrate norm ∨
    r = diffHigherOrder ∨ r = diffConstant ∨ r = diffVariable ∨ r = diffSum ∨ r = diffConstMul ∨
    r = diffProduct ∨ r = diffPower ∨ r = diffChain ∨ r = diffMatrix ∨
    r = laAdd ∨ r = laScalarMul ∨ r = laMul ∨ r = laTranspose ∨ r = laDet ∨ r = laPow ∨
    r = scalarOnly flatten.toPlain ∨ r = scalarOnly identity.toPlain ∨ r = scalarOnly foldConstants.toPlain ∨
    r = scalarOnly functionRules.toPlain ∨ r = scalarOnly powerRules.toPlain ∨ r = scalarOnly collectPowers.toPlain ∨
    r = scalarOnly collectTerms.toPlain ∨ r = scalarOnly parityPowMul ∨ r = scalarOnly parityPowPow ∨
    r = scalarOnly radicalBase ∨ r = scalarOnly collectRadicals ∨ r = scalarOnly mulRadicals ∨ r = laContext := by
  simp [pipelineRulesWith, commandRulesWith, diffRules, matrixRules, simpPlain, simpRules, parityPlain, parityRules,
    radicalPlain, radicalRules, contextRules]

-- ---------------------------------------------------------------------------
-- Clean terms: nothing the first three tiers count
-- ---------------------------------------------------------------------------

/-- No command, no malformed `diff`, no literal at or below. -/
structure Clean (e : Expr) : Prop where
  cmd : count cmdOwn e = 0
  d3 : count d3Own e = 0
  lit : hasLit e = false

theorem countList_eq_zero_iff (own : Expr → Nat) (cs : List Expr) :
    countList own cs = 0 ↔ ∀ c ∈ cs, count own c = 0 := by
  induction cs with
  | nil => simp [countList]
  | cons c cs ih =>
    simp only [countList, List.forall_mem_cons]
    constructor
    · intro h; exact ⟨by omega, ih.1 (by omega)⟩
    · intro ⟨h1, h2⟩; have := ih.2 h2; omega

theorem count_add (own) (es) : count own (.add es) = own (.add es) + countList own es := rfl
theorem count_mul (own) (es) : count own (.mul es) = own (.mul es) + countList own es := rfl
theorem count_pow (own) (b x) : count own (.pow b x) = own (.pow b x) + count own b + count own x := rfl
theorem count_fn (own) (f es) : count own (.fn f es) = own (.fn f es) + countList own es := rfl
theorem count_num (own) (q) : count own (.num q) = own (.num q) := rfl
theorem count_var (own) (x) : count own (.var x) = own (.var x) := rfl
theorem count_matrix (own) (rows) : count own (.matrix rows) = own (.matrix rows) + countList own rows.flatten := by
  rw [count_eq]; rfl

theorem cmdOwn_fn (f es) : cmdOwn (.fn f es) = if cmdNames.contains f then 1 else 0 := rfl
theorem d3Own_fn (f es) : d3Own (.fn f es) = if f = "diff" ∧ es.length ≠ 2 then 1 else 0 := rfl
@[simp] theorem cmdOwn_add (es) : cmdOwn (.add es) = 0 := rfl
@[simp] theorem cmdOwn_mul (es) : cmdOwn (.mul es) = 0 := rfl
@[simp] theorem cmdOwn_pow (b x) : cmdOwn (.pow b x) = 0 := rfl
@[simp] theorem cmdOwn_num (q) : cmdOwn (.num q) = 0 := rfl
@[simp] theorem cmdOwn_var (x) : cmdOwn (.var x) = 0 := rfl
@[simp] theorem cmdOwn_matrix (rows) : cmdOwn (.matrix rows) = 0 := rfl
@[simp] theorem d3Own_add (es) : d3Own (.add es) = 0 := rfl
@[simp] theorem d3Own_mul (es) : d3Own (.mul es) = 0 := rfl
@[simp] theorem d3Own_pow (b x) : d3Own (.pow b x) = 0 := rfl
@[simp] theorem d3Own_num (q) : d3Own (.num q) = 0 := rfl
@[simp] theorem d3Own_var (x) : d3Own (.var x) = 0 := rfl
@[simp] theorem d3Own_matrix (rows) : d3Own (.matrix rows) = 0 := rfl
@[simp] theorem hasLit_add (es) : hasLit (.add es) = hasLitList es := rfl
@[simp] theorem hasLit_mul (es) : hasLit (.mul es) = hasLitList es := rfl
@[simp] theorem hasLit_fn (f es) : hasLit (.fn f es) = hasLitList es := rfl
@[simp] theorem hasLit_pow (b x) : hasLit (.pow b x) = (hasLit b || hasLit x) := rfl
@[simp] theorem hasLit_num (q) : hasLit (.num q) = false := rfl
@[simp] theorem hasLit_var (x) : hasLit (.var x) = false := rfl
@[simp] theorem hasLit_matrix (rows) : hasLit (.matrix rows) = true := rfl
@[simp] theorem hasLitList_nil : hasLitList [] = false := rfl
@[simp] theorem hasLitList_cons (e es) : hasLitList (e :: es) = (hasLit e || hasLitList es) := rfl

theorem hasLitList_eq_false_iff (es : List Expr) : hasLitList es = false ↔ ∀ e ∈ es, hasLit e = false := by
  induction es with
  | nil => simp
  | cons e es ih => simp [ih]

theorem Clean.num (q : Q) : Clean (.num q) := ⟨rfl, rfl, rfl⟩
theorem Clean.var (x : String) : Clean (.var x) := ⟨rfl, rfl, rfl⟩
theorem Clean.add {es : List Expr} (h : ∀ c ∈ es, Clean c) : Clean (.add es) :=
  ⟨by show count cmdOwn _ = 0; rw [count_add, cmdOwn_add, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).cmd],
   by show count d3Own _ = 0; rw [count_add, d3Own_add, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).d3],
   by rw [hasLit_add, hasLitList_eq_false_iff]; exact fun c hc => (h c hc).lit⟩
theorem Clean.mul {es : List Expr} (h : ∀ c ∈ es, Clean c) : Clean (.mul es) :=
  ⟨by show count cmdOwn _ = 0; rw [count_mul, cmdOwn_mul, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).cmd],
   by show count d3Own _ = 0; rw [count_mul, d3Own_mul, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).d3],
   by rw [hasLit_mul, hasLitList_eq_false_iff]; exact fun c hc => (h c hc).lit⟩
theorem Clean.pow {b x : Expr} (hb : Clean b) (hx : Clean x) : Clean (.pow b x) :=
  ⟨by show count cmdOwn _ = 0; rw [count_pow, cmdOwn_pow, hb.cmd, hx.cmd],
   by show count d3Own _ = 0; rw [count_pow, d3Own_pow, hb.d3, hx.d3],
   by rw [hasLit_pow, hb.lit, hx.lit]; rfl⟩
theorem Clean.fn {f : String} {es : List Expr} (hf : cmdNames.contains f = false)
    (hd : f = "diff" → es.length = 2) (h : ∀ c ∈ es, Clean c) : Clean (.fn f es) :=
  ⟨by show count cmdOwn _ = 0; rw [count_fn, cmdOwn_fn, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).cmd]; simp only [hf, Bool.false_eq_true, ↓reduceIte],
   by show count d3Own _ = 0
      rw [count_fn, d3Own_fn, (countList_eq_zero_iff _ _).2 fun c hc => (h c hc).d3]
      split
      · rename_i h'; exact absurd (hd h'.1) h'.2
      · rfl,
   by rw [hasLit_fn, hasLitList_eq_false_iff]; exact fun c hc => (h c hc).lit⟩
/-- A binary `diff` of clean pieces. -/
theorem Clean.diff {g t : Expr} (hg : Clean g) (ht : Clean t) : Clean (.fn "diff" [g, t]) :=
  Clean.fn (by decide) (fun _ => rfl) (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> assumption)
theorem Clean.fn₁ {f : String} {a : Expr} (hf : cmdNames.contains f = false) (hd : f ≠ "diff") (ha : Clean a) :
    Clean (.fn f [a]) :=
  Clean.fn hf (fun h => absurd h hd) (by intro c hc; simp at hc; subst hc; exact ha)

theorem Clean.child {e c : Expr} (h : Clean e) (hc : c ∈ children e) : Clean c :=
  ⟨Nat.eq_zero_of_le_zero (h.cmd ▸ count_child_le _ hc),
   Nat.eq_zero_of_le_zero (h.d3 ▸ count_child_le _ hc),
   by
    cases hl' : hasLit c with
    | false => rfl
    | true =>
      have := hasLit_withChildren e (children e) rfl
      rw [withChildren_children'] at this
      have : hasLit e = true := by rw [this, Bool.or_eq_true, hasLitList_iff]; exact Or.inr ⟨c, hc, hl'⟩
      rw [h.lit] at this; exact absurd this Bool.false_ne_true⟩

theorem Clean.litCount {e : Expr} (h : Clean e) : count litOwn e = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have := hasLit_of_count_pos hpos
  rw [h.lit] at this; exact absurd this Bool.false_ne_true

theorem Clean.addN {es : List Expr} (h : ∀ c ∈ es, Clean c) : Clean (addN es) := by
  match es with
  | [e] => exact h e List.mem_cons_self
  | [] => exact Clean.add h
  | _ :: _ :: _ => exact Clean.add h
theorem Clean.mulN {es : List Expr} (h : ∀ c ∈ es, Clean c) : Clean (mulN es) := by
  match es with
  | [e] => exact h e List.mem_cons_self
  | [] => exact Clean.mul h
  | _ :: _ :: _ => exact Clean.mul h

theorem μ_of_clean {e : Expr} (h : Clean e) : μ e = (0, 0, 0, M e, size e, numCount e) := by
  simp only [μ, cmdCount, d3Count, litCount, h.cmd, h.d3, h.litCount]

/-- Between clean terms only `M`, `size` and the numeral tier matter; almost every rule is settled
by the first two. -/
theorem muLt_of_clean {r e : Expr} (hr : Clean r) (he : Clean e)
    (h : M r < M e ∨ (M r = M e ∧ size r < size e)) : MuLt (μ r) (μ e) := by
  rw [μ_of_clean hr, μ_of_clean he]
  apply muLt_of (Nat.le_refl _) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  · intro _ _ _; rcases h with h | ⟨h, _⟩; exact Nat.le_of_lt h; exact Nat.le_of_eq h
  · intro _ _ _ h4; rcases h with h | ⟨_, h⟩; exact absurd h4 (Nat.ne_of_lt h); exact Nat.le_of_lt h
  · intro _ _ _ h4 h5; rcases h with h | ⟨_, h⟩; exact absurd h4 (Nat.ne_of_lt h); exact absurd h5 (Nat.ne_of_lt h)

/-- The radical rules: `M` and `size` unchanged, an integer numeral shrank. -/
theorem muLt_of_clean' {r e : Expr} (hr : Clean r) (he : Clean e)
    (h : M r = M e ∧ size r = size e ∧ numCount r < numCount e) : MuLt (μ r) (μ e) := by
  rw [μ_of_clean hr, μ_of_clean he]
  obtain ⟨h1, h2, h3⟩ := h
  apply muLt_of (Nat.le_refl _) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  · intro _ _ _; exact Nat.le_of_eq h1
  · intro _ _ _ _; exact Nat.le_of_eq h2
  · intro _ _ _ _ _; exact h3

-- ---------------------------------------------------------------------------
-- Normal forms of the pipeline
-- ---------------------------------------------------------------------------

theorem laContext_mem : laContext ∈ (pipelineRulesWith norm) := (mem_pipeline_iff _).2 (by simp)
theorem diffHigherOrder_mem : diffHigherOrder ∈ (pipelineRulesWith norm) := (mem_pipeline_iff _).2 (by simp)

/-- A node with a matrix literal among its children is never normal. -/
theorem not_noFire_of_lit_child {e : Expr} (h : (children e).any isMatrix = true) : ¬ NoFire (pipelineRulesWith norm) e := by
  intro hnf
  have := hnf laContext laContext_mem
  cases e with
  | matrix rows => simp only [laContext, children] at this h; rw [h] at this; simp at this
  | _ => simp only [laContext] at this; rw [h] at this; simp at this

/-- A command node is never normal: every command evaluates or refuses. -/
theorem not_noFire_of_cmd {f : String} {es : List Expr} (h : cmdNames.contains f = true) :
    ¬ NoFire (pipelineRulesWith norm) (.fn f es) := by
  intro hnf
  simp [cmdNames] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · have := hnf cmdSimplify ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [_], h => simp [cmdSimplify] at h
    | [], h => simp [cmdSimplify] at h
    | _ :: _ :: _, h => simp [cmdSimplify] at h
  · have := hnf cmdExpand ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [a], h => simp [cmdExpand] at h
    | [], h => simp [cmdExpand] at h
    | _ :: _ :: _, h => simp [cmdExpand] at h
  · have := hnf cmdRref ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [.matrix _], h => simp only [cmdRref, Option.map_eq_none_iff] at h; split at h <;> simp at h
    | [.num _], h | [.var _], h | [.add _], h | [.mul _], h | [.pow _ _], h | [.fn _ _], h => simp [cmdRref] at h
    | [], h => simp [cmdRref] at h
    | _ :: _ :: _, h => simp [cmdRref] at h
  · have := hnf cmdN ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [a], h => simp only [cmdN, Option.map_eq_none_iff] at h; split at h <;> simp at h
    | [], h => simp [cmdN] at h
    | _ :: _ :: _, h => simp [cmdN] at h
  · have := hnf cmdSubst ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [_, .var _, _], h => simp [cmdSubst] at h
    | [_, .num _, _], h | [_, .add _, _], h | [_, .mul _, _], h | [_, .pow _ _, _], h | [_, .fn _ _, _], h
    | [_, .matrix _, _], h => simp [cmdSubst] at h
    | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => simp [cmdSubst] at h
  · have := hnf (cmdIntegrate norm) ((mem_pipeline_iff _).2 (by simp))
    match es, this with
    | [_, .var _], h => simp only [cmdIntegrate, Option.map_eq_none_iff] at h; split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp at h
    | [_, .num _], h | [_, .add _], h | [_, .mul _], h | [_, .pow _ _], h | [_, .fn _ _], h | [_, .matrix _], h => simp [cmdIntegrate] at h
    | [], h | [_], h | _ :: _ :: _ :: _, h => simp [cmdIntegrate] at h

/-- A `diff` of the wrong arity is never normal. -/
theorem not_noFire_of_d3 {es : List Expr} (h : es.length ≠ 2) : ¬ NoFire (pipelineRulesWith norm) (.fn "diff" es) := by
  intro hnf
  have := hnf diffHigherOrder diffHigherOrder_mem
  match es, h, this with
  | [], _, h => simp [diffHigherOrder] at h
  | [_], _, h => simp [diffHigherOrder] at h
  | [_, _], h, _ => exact h rfl
  | [_, .var _, .num _], _, h => simp only [diffHigherOrder] at h; split at h <;> simp at h
  | [_, .var _, .var _], _, h | [_, .var _, .add _], _, h | [_, .var _, .mul _], _, h | [_, .var _, .pow _ _], _, h
  | [_, .var _, .fn _ _], _, h | [_, .var _, .matrix _], _, h => simp [diffHigherOrder] at h
  | [_, .num _, _], _, h | [_, .add _, _], _, h | [_, .mul _, _], _, h | [_, .pow _ _, _], _, h
  | [_, .fn _ _, _], _, h | [_, .matrix _, _], _, h => simp [diffHigherOrder] at h
  | _ :: _ :: _ :: _ :: _, _, h => simp [diffHigherOrder] at h

/-- The structural content of normality: nothing the counting tiers see, except a literal at the root. -/
theorem normal_facts {e : Expr} (h : Normal (pipelineRulesWith norm) e) :
    count cmdOwn e = 0 ∧ count d3Own e = 0 ∧ (∀ c ∈ children e, Clean c) := by
  induction h with
  | mk e hnf hc ih =>
    have hclean : ∀ c ∈ children e, Clean c := by
      intro c hc'
      obtain ⟨h1, h2, h3⟩ := ih c hc'
      refine ⟨h1, h2, ?_⟩
      -- `c` is not a literal (else `la.context` fires on `e`), and nothing below `c` is either
      have hnl : isMatrix c = false := by
        cases hm' : isMatrix c with
        | false => rfl
        | true => exact absurd hnf (not_noFire_of_lit_child (List.any_eq_true.2 ⟨c, hc', hm'⟩))
      have := hasLit_withChildren c (children c) rfl
      rw [withChildren_children'] at this
      rw [this, hnl, Bool.false_or, hasLitList_eq_false_iff]
      exact fun d hd => (h3 d hd).lit
    refine ⟨?_, ?_, hclean⟩
    · rw [count_eq, (countList_eq_zero_iff _ _).2 fun c hc' => (hclean c hc').cmd, Nat.add_zero]
      cases e with
      | fn f es =>
        simp only [cmdOwn_fn]; split
        · exact absurd hnf (not_noFire_of_cmd ‹_›)
        · rfl
      | _ => rfl
    · rw [count_eq, (countList_eq_zero_iff _ _).2 fun c hc' => (hclean c hc').d3, Nat.add_zero]
      cases e with
      | fn f es =>
        simp only [d3Own_fn]; split
        · rename_i h'; obtain ⟨rfl, hl⟩ := h'; exact absurd hnf (not_noFire_of_d3 hl)
        · rfl
      | _ => rfl

theorem Clean.of_normal {e : Expr} (h : Normal (pipelineRulesWith norm) e) (hm : isMatrix e = false) : Clean e := by
  obtain ⟨h1, h2, h3⟩ := normal_facts h
  refine ⟨h1, h2, ?_⟩
  have := hasLit_withChildren e (children e) rfl
  rw [withChildren_children'] at this
  rw [this, hm, Bool.false_or, hasLitList_eq_false_iff]
  exact fun d hd => (h3 d hd).lit

/-- What a rule may assume about the node it fires on. -/
theorem childrenNormal_facts {e : Expr} (h : ChildrenNormal (pipelineRulesWith norm) e) :
    (∀ c ∈ children e, isMatrix c = false → Clean c) ∧ (∀ c ∈ children e, ∀ d ∈ children c, Clean d) :=
  ⟨fun c hc hm => Clean.of_normal (h c hc) hm, fun c hc => (normal_facts (h c hc)).2.2⟩

-- ---------------------------------------------------------------------------
-- The obligation, rule by rule
-- ---------------------------------------------------------------------------

/-- `r` decreases `μ` on nodes with normal children. -/
def Dec (norm : Norm) (r : PlainRule) : Prop :=
  ∀ e res, ChildrenNormal (pipelineRulesWith norm) e → r.apply e = some res → res.error = none → MuLt (μ res.result) (μ e)

theorem checked_spec {r r' : RuleResult} (h : checked r = r') (he : r'.error = none) :
    r' = r ∧ count cmdOwn r'.result = 0 := by
  simp only [checked] at h
  split at h
  · subst h; rename_i h'; simp [he] at h'
  · split at h
    · subst h; exact ⟨rfl, ‹_›⟩
    · subst h; simp [refuse] at he

/-- Tier 1: a command node with normal children has `cmdCount = 1`; a checked output has 0. -/
theorem dec_cmd {r : PlainRule} (hname : ∀ e res, r.apply e = some res → ∃ f es, e = .fn f es ∧ cmdNames.contains f = true)
    (hchk : ∀ e res, r.apply e = some res → ∃ r₀, res = checked r₀) : Dec norm r := by
  intro e res hcn happ herr
  obtain ⟨f, es, rfl, hf⟩ := hname e res happ
  obtain ⟨r₀, rfl⟩ := hchk _ _ happ
  obtain ⟨_, hzero⟩ := checked_spec rfl herr
  have hcs := (childrenNormal_facts hcn).1
  have hlist : countList cmdOwn es = 0 := by
    rw [countList_eq_zero_iff]; intro c hc
    exact (normal_facts (hcn c hc)).1
  have : count cmdOwn (.fn f es) = 1 := by rw [count_fn, cmdOwn_fn, hlist, if_pos hf]
  simp only [μ, cmdCount]
  exact Prod.Lex.left _ _ (by rw [hzero, this]; exact Nat.zero_lt_one)

theorem dec_cmdSimplify : Dec norm cmdSimplify := dec_cmd
  (fun e res h => by
    unfold cmdSimplify at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdSimplify at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

theorem dec_cmdExpand : Dec norm cmdExpand := dec_cmd
  (fun e res h => by
    unfold cmdExpand at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdExpand at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

theorem dec_cmdRref : Dec norm cmdRref := dec_cmd
  (fun e res h => by
    unfold cmdRref at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · split at h <;> exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdRref at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

theorem dec_cmdN : Dec norm cmdN := dec_cmd
  (fun e res h => by
    unfold cmdN at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdN at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

theorem dec_cmdSubst : Dec norm cmdSubst := dec_cmd
  (fun e res h => by
    unfold cmdSubst at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdSubst at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

theorem dec_cmdIntegrate : Dec norm (cmdIntegrate norm) := dec_cmd
  (fun e res h => by
    unfold cmdIntegrate at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨_, h, _⟩ := h
    split at h
    · split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · exact ⟨_, _, rfl, by decide⟩
    · simp at h)
  (fun e res h => by
    unfold cmdIntegrate at h; simp only [Option.map_eq_some_iff] at h; obtain ⟨r₀, _, rfl⟩ := h; exact ⟨r₀, rfl⟩)

-- ---------------------------------------------------------------------------
-- Tier 2: diff.higher-order
-- ---------------------------------------------------------------------------

theorem count_D (own : Expr → Nat) (r : Expr) (x : String) :
    count own (D r x) = own (.fn "diff" [r, .var x]) + count own r + own (.var x) := by
  simp only [D, count_fn, countList, count_var]; omega

theorem count_foldD (own : Expr → Nat) (h0 : ∀ r, own (.fn "diff" [r, .var x]) = 0) (hv : own (.var x) = 0)
    (body : Expr) : ∀ k, count own ((List.range k).foldl (fun r _ => D r x) body) = count own body := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, count_D, h0, hv, ih]; omega

theorem dec_diffHigherOrder : Dec norm diffHigherOrder := by
  intro e res hcn happ herr
  unfold diffHigherOrder at happ
  dsimp only at happ
  split at happ
  · rename_i body x n
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ
      have hb := (normal_facts (hcn body (by simp [children]))).1
      have hb2 := (normal_facts (hcn body (by simp [children]))).2.1
      have hc : count cmdOwn (.fn "diff" [body, .var x, .num n]) = 0 := by
        simp [count_fn, cmdOwn_fn, cmdNames, countList, count_var, count_num, hb]
      have hd : count d3Own (.fn "diff" [body, .var x, .num n]) = 1 := by
        simp [count_fn, d3Own_fn, countList, count_var, count_num, hb2]
      have hr1 := count_foldD cmdOwn (x := x) (fun _ => rfl) rfl body n.val.num.toNat
      have hr2 := count_foldD d3Own (x := x) (fun _ => rfl) rfl body n.val.num.toNat
      simp only [μ, cmdCount, d3Count]
      rw [hr1, hr2, hb, hb2, hc, hd]
      exact muLt_of (Nat.le_refl _) (fun _ => Nat.zero_le _) (fun _ h => absurd h (by decide))
        (fun _ h => absurd h (by decide)) (fun _ h => absurd h (by decide)) (fun _ h => absurd h (by decide))
    · simp only [Option.some.injEq] at happ; subst happ; simp at herr
  · simp at happ
  · simp only [Option.some.injEq] at happ; subst happ; simp at herr
  · simp only [Option.some.injEq] at happ; subst happ; simp at herr
  · simp at happ

-- ---------------------------------------------------------------------------
-- Tier 3: the matrix rules and diff.matrix, through `checkedLit`
-- ---------------------------------------------------------------------------

theorem checkedLit_spec {e : Expr} {r r' : RuleResult} (h : checkedLit e r = r') (he : r'.error = none) :
    count cmdOwn r'.result = 0 ∧ count d3Own r'.result = 0 ∧ count litOwn r'.result < count litOwn e := by
  simp only [checkedLit] at h
  split at h
  · subst h; rename_i h'; simp [he] at h'
  · split at h
    · subst h; assumption
    · subst h; simp at he

/-- A rule whose node carries no command and no malformed `diff`, and whose output is `checkedLit`. -/
theorem dec_lit {r : PlainRule} (hshape : ∀ e res, r.apply e = some res → cmdOwn e = 0 ∧ d3Own e = 0)
    (hchk : ∀ e res, r.apply e = some res → ∃ r₀, res = checkedLit e r₀) : Dec norm r := by
  intro e res hcn happ herr
  obtain ⟨h1, h2⟩ := hshape e res happ
  obtain ⟨r₀, rfl⟩ := hchk _ _ happ
  obtain ⟨c1, c2, c3⟩ := checkedLit_spec rfl herr
  have e1 : count cmdOwn e = 0 := by
    rw [count_eq, h1, (countList_eq_zero_iff _ _).2 fun c hc => (normal_facts (hcn c hc)).1]
  have e2 : count d3Own e = 0 := by
    rw [count_eq, h2, (countList_eq_zero_iff _ _).2 fun c hc => (normal_facts (hcn c hc)).2.1]
  simp only [μ, cmdCount, d3Count, litCount]
  exact muLt_of (by rw [c1, e1]; exact Nat.le_refl _) (fun _ => by rw [c2, e2]; exact Nat.le_refl _)
    (fun _ _ => Nat.le_of_lt c3) (fun _ _ h => absurd h (Nat.ne_of_lt c3)) (fun _ _ h => absurd h (Nat.ne_of_lt c3))
    (fun _ _ h => absurd h (Nat.ne_of_lt c3))

/-- `Option.map (checkedLit e)` applied to a rule body: the shape of every matrix rule. -/
theorem lit_apply {e : Expr} {res : RuleResult} {body : Option RuleResult}
    (h : Option.map (checkedLit e) body = some res) : ∃ r₀, body = some r₀ ∧ res = checkedLit e r₀ := by
  cases body with
  | none => simp at h
  | some r₀ => exact ⟨r₀, rfl, by simpa using h.symm⟩

theorem dec_laAdd : Dec norm laAdd := dec_lit
  (fun e res h => by
    unfold laAdd at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨rfl, rfl⟩
    · simp at h)
  (fun e res h => by unfold laAdd at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem dec_laScalarMul : Dec norm laScalarMul := dec_lit
  (fun e res h => by
    unfold laScalarMul at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨rfl, rfl⟩
    · simp at h)
  (fun e res h => by unfold laScalarMul at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem dec_laMul : Dec norm laMul := dec_lit
  (fun e res h => by
    unfold laMul at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨rfl, rfl⟩
    · simp at h)
  (fun e res h => by unfold laMul at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem dec_laTranspose : Dec norm laTranspose := dec_lit
  (fun e res h => by
    unfold laTranspose at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨by simp [cmdOwn, cmdNames], by simp [d3Own]⟩
    · simp at h)
  (fun e res h => by unfold laTranspose at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem dec_laDet : Dec norm laDet := dec_lit
  (fun e res h => by
    unfold laDet at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨by simp [cmdOwn, cmdNames], by simp [d3Own]⟩
    · simp at h)
  (fun e res h => by unfold laDet at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem dec_laPow : Dec norm laPow := dec_lit
  (fun e res h => by
    unfold laPow at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    split at h
    · exact ⟨rfl, rfl⟩
    · simp at h)
  (fun e res h => by unfold laPow at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

theorem target_spec {e : Expr} {p : Expr × String} (h : target e = some p) : e = .fn "diff" [p.1, .var p.2] := by
  unfold target at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

theorem dec_diffMatrix : Dec norm diffMatrix := dec_lit
  (fun e res h => by
    unfold diffMatrix at h; obtain ⟨r₀, h, _⟩ := lit_apply h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, _⟩ := h
    rw [target_spec hp]; exact ⟨by simp [cmdOwn, cmdNames], by simp [d3Own]⟩)
  (fun e res h => by unfold diffMatrix at h; obtain ⟨r₀, _, rfl⟩ := lit_apply h; exact ⟨r₀, rfl⟩)

/-- `la.context` only refuses. -/
theorem dec_laContext : Dec norm laContext := by
  intro e res hcn happ herr
  unfold laContext at happ
  dsimp only at happ
  split at happ
  · split at happ
    · simp only [Option.some.injEq] at happ; subst happ; simp [refuse] at herr
    · simp at happ
  · split at happ
    · simp only [Option.some.injEq] at happ; subst happ; simp [refuse] at herr
    · simp at happ

-- ---------------------------------------------------------------------------
-- Tier 4: the arithmetic behind `M`
-- ---------------------------------------------------------------------------

theorem three_pow_ge (n : Nat) : n + 1 ≤ 3 ^ n := Nat.lt_pow_self (by decide)

theorem foldr_prod_ge_one : ∀ (l : List Nat), (∀ x ∈ l, 1 ≤ x) → 1 ≤ l.foldr (· * ·) 1
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    simp only [List.foldr_cons]
    have := foldr_prod_ge_one l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact Nat.le_trans (h x List.mem_cons_self) (Nat.le_mul_of_pos_right _ this)

/-- Products beat sums: for `x_i ≥ 3` and a nonempty list, `Σ x_i + k ≤ Π x_i + 1`. -/
theorem sum_add_len_le_prod : ∀ (l : List Nat), l ≠ [] → (∀ x ∈ l, 3 ≤ x) →
    l.sum + l.length ≤ l.foldr (· * ·) 1 + 1
  | [], h, _ => absurd rfl h
  | [x], _, _ => by simp
  | x :: y :: l, _, h3 => by
    have ih := sum_add_len_le_prod (y :: l) (by simp) (fun z hz => h3 z (List.mem_cons_of_mem _ hz))
    simp only [List.sum_cons, List.length_cons, List.foldr_cons] at ih ⊢
    have hx := h3 x List.mem_cons_self
    have hy := h3 y (List.mem_cons_of_mem _ List.mem_cons_self)
    have hl : 1 ≤ List.foldr (· * ·) 1 l :=
      foldr_prod_ge_one l (fun z hz => Nat.le_trans (by decide) (h3 z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))))
    have hP : 3 ≤ y * List.foldr (· * ·) 1 l := Nat.le_trans hy (Nat.le_mul_of_pos_right _ hl)
    have h1 : x * 3 ≤ x * (y * List.foldr (· * ·) 1 l) := Nat.mul_le_mul_left _ hP
    have h2 : 3 * (y * List.foldr (· * ·) 1 l) ≤ x * (y * List.foldr (· * ·) 1 l) := Nat.mul_le_mul_right _ hx
    omega

theorem prod_three_pow (es : List Expr) : (es.map fun e => 3 ^ M e).foldr (· * ·) 1 = 3 ^ ML es := by
  induction es with
  | nil => simp [ML]
  | cons e es ih => simp only [List.map_cons, List.foldr_cons, ih, ML.cons, Nat.pow_add]

/-- The product-versus-sum core for `diff`: `Σ 3^(M e) + k ≤ 3^(Σ M e)` for a nonempty list. -/
theorem sum_three_pow_le (es : List Expr) (hne : es ≠ []) :
    (es.map fun e => 3 ^ M e).sum + es.length ≤ 3 ^ ML es + 1 := by
  have h3 : ∀ x ∈ es.map fun e => 3 ^ M e, 3 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact Nat.le_trans (by decide : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by decide) (M.pos e))
  have := sum_add_len_le_prod (es.map fun e => 3 ^ M e) (fun h => hne (List.map_eq_nil_iff.mp h)) h3
  rw [prod_three_pow, List.length_map] at this; exact this

theorem three_pow_add_three (n : Nat) : 3 ^ (n + 3) = 27 * 3 ^ n := by
  rw [Nat.pow_add, Nat.mul_comm]

theorem M_add_ne_nil {es : List Expr} (h : es ≠ []) : M (.add es) = ML es := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es => rw [M.add_cons, ML.cons]

-- ---------------------------------------------------------------------------
-- Tier 4: the easy diff rules
-- ---------------------------------------------------------------------------

/-- The node a `diff.*` rule fires on, when its body is not a literal, is clean. -/
theorem diff_clean {body : Expr} {x : String} (hcn : ChildrenNormal (pipelineRulesWith norm) (.fn "diff" [body, .var x]))
    (hm : isMatrix body = false) : Clean body ∧ Clean (.fn "diff" [body, .var x]) :=
  have hb : Clean body := Clean.of_normal (hcn body (by simp [children])) hm
  ⟨hb, Clean.diff hb (Clean.var x)⟩

theorem Q_one_isOne : Q.one.isOne = true := by decide
theorem Q_zero_isOne : Q.zero.isOne = false := by decide
theorem Q_zero_isInt : Q.zero.isInt = true := by decide
theorem Q_minusOne_isInt : Q.minusOne.isInt = true := by decide

theorem M.zero : M Expr.zero = 2 := by simp [Expr.zero, M.num, Q_zero_isOne, Q_zero_isInt]
theorem M.zero' : M (.num Q.zero) = 2 := M.zero
theorem M.one' : M (.num Q.one) = 1 := by simp [M.num, Q_one_isOne]
theorem M.one : M Expr.one = 1 := by simp [Expr.one, M.num, Q_one_isOne]

theorem dec_diffConstant : Dec norm diffConstant := by
  intro e res hcn happ herr
  unfold diffConstant rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · simp only [Option.some.injEq] at happ; subst happ
    simp only
    cases body with
    | matrix rows =>
      -- the literal disappears: tier 3
      have hf := normal_facts (hcn (.matrix rows) (by simp [children]))
      have hc1 : count cmdOwn (.fn "diff" [.matrix rows, .var x]) = 0 := by
        simp [count_fn, cmdOwn_fn, cmdNames, countList, count_var, hf.1]
      have hc2 : count d3Own (.fn "diff" [.matrix rows, .var x]) = 0 := by
        simp [count_fn, d3Own_fn, countList, count_var, hf.2.1]
      have hl : 1 ≤ count litOwn (.fn "diff" [.matrix rows, .var x]) := by
        rw [count_eq]; simp [litOwn]
      have hz : Clean Expr.zero := Clean.num Q.zero
      simp only [μ, cmdCount, d3Count, litCount]
      rw [hc1, hc2, hz.cmd, hz.d3, hz.litCount]
      exact muLt_of (Nat.le_refl _) (fun _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
        (fun _ _ h => absurd h (by omega)) (fun _ _ h => absurd h (by omega)) (fun _ _ h => absurd h (by omega))
    | _ =>
      obtain ⟨hb, he⟩ := diff_clean hcn rfl
      apply muLt_of_clean (Clean.num _) he
      left
      simp only [Expr.zero, M.num, Q_zero_isOne, Q_zero_isInt, Bool.false_eq_true, ↓reduceIte, M.diff]
      have key : ∀ n, 2 < 3 ^ (n + 3) + 10 := fun n => by have := three_pow_ge (n + 3); omega
      exact key _
  · simp at happ

theorem dec_diffVariable : Dec norm diffVariable := by
  intro e res hcn happ herr
  unfold diffVariable rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i y
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ
      obtain ⟨hb, he⟩ := diff_clean hcn rfl
      apply muLt_of_clean (Clean.num _) he
      left
      simp only [Expr.one, M.num, Q_one_isOne, ↓reduceIte, M.diff, M.var]
      have := three_pow_ge 13; omega
    · simp at happ
  · simp at happ

theorem ML_map_D (x : String) (es : List Expr) :
    ML (es.map (D · x)) = 27 * (es.map fun e => 3 ^ M e).sum + 10 * es.length := by
  induction es with
  | nil => simp [ML]
  | cons e es ih =>
    rw [List.map_cons, ML.cons, ih]
    simp only [D, M.diff, M.var, three_pow_add_three, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem dec_diffSum : Dec norm diffSum := by
  intro e res hcn happ herr
  unfold diffSum rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i a b es
    simp only [Option.some.injEq] at happ; subst happ
    obtain ⟨hb, he⟩ := diff_clean hcn rfl
    have hcs : ∀ c ∈ a :: b :: es, Clean c := fun c hc => hb.child (by simpa [children] using hc)
    have hres : Clean (.add ((a :: b :: es).map (D · x))) := Clean.add fun c hc => by
      simp only [List.mem_map] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      exact Clean.diff (hcs d hd) (Clean.var x)
    apply muLt_of_clean hres he
    left
    rw [M_add_ne_nil (by simp), ML_map_D, M.diff, M.var, M_add_ne_nil (by simp), three_pow_add_three]
    have h2 := sum_three_pow_le (a :: b :: es) (by simp)
    simp only [List.length_cons] at h2 ⊢
    omega
  · simp at happ

-- ---------------------------------------------------------------------------
-- More facts about `M` and normal forms
-- ---------------------------------------------------------------------------

theorem Q_minusOne_isOne : Q.minusOne.isOne = false := by decide
theorem M.minusOne : M Expr.minusOne = 2 := by simp [Expr.minusOne, M.num, Q_minusOne_isOne, Q_minusOne_isInt]

theorem M.fn₁ {f : String} (hf : f ≠ "diff") (a : Expr) : M (.fn f [a]) = 5 * M a + 10 := by
  rw [M.fn f [a] (fun h => hf h.1)]; simp [ML]

theorem length_le_ML : ∀ es : List Expr, es.length ≤ ML es
  | [] => Nat.le_refl _
  | e :: es => by simp only [List.length_cons, ML.cons]; have := M.pos e; have := length_le_ML es; omega

theorem ML_filter_add (p : Expr → Bool) : ∀ es : List Expr,
    ML (es.filter p) + ML (es.filter fun a => !p a) = ML es
  | [] => rfl
  | e :: es => by
    have ih := ML_filter_add p es
    by_cases hp : p e = true
    · simp [List.filter_cons, hp, ML.cons]; omega
    · simp [List.filter_cons, hp, ML.cons]; omega

theorem length_filter_add (p : Expr → Bool) : ∀ es : List Expr,
    (es.filter p).length + (es.filter fun a => !p a).length = es.length
  | [] => rfl
  | e :: es => by
    have ih := length_filter_add p es
    by_cases hp : p e = true
    · simp [List.filter_cons, hp]; omega
    · simp [List.filter_cons, hp]; omega

theorem M_mulN_le' (l : List Expr) : M (mulN l) ≤ 2 + ML l + 2 * l.length := by
  match l with
  | [e] => simp [mulN, ML]; omega
  | [] => exact Nat.le_refl _
  | _ :: _ :: _ => exact Nat.le_refl _

-- A term mentioning a variable weighs at least a variable.
mutual
  theorem M_ge_ten_of_mem (y : String) : ∀ e : Expr, y ∈ freeVars e → 10 ≤ M e
    | .num _, h => by simp [freeVars] at h
    | .var x, _ => by rw [M.var]; exact Nat.le_refl _
    | .add es, h => by
      simp only [freeVars] at h
      have := ML_ge_ten_of_mem y es h
      cases es with
      | nil => simp [freeVars.freeVarsList] at h
      | cons e es => rw [M.add_cons]; rw [ML.cons] at this; exact this
    | .mul es, h => by
      simp only [freeVars] at h
      have := ML_ge_ten_of_mem y es h
      rw [M.mul]; omega
    | .pow b x, h => by
      simp only [freeVars, List.mem_append] at h
      rw [M.pow]
      have hb := M.pos b; have hx := M.pos x
      rcases h with h | h
      · have := M_ge_ten_of_mem y b h
        have : (M b + 1) * M x ≥ (10 + 1) * 1 := Nat.mul_le_mul (by omega) hx
        omega
      · have := M_ge_ten_of_mem y x h
        have : (M b + 1) * M x ≥ (1 + 1) * 10 := Nat.mul_le_mul (by omega) this
        omega
    | .fn f es, _ => by
      by_cases hd : f = "diff" ∧ es.length = 2
      · obtain ⟨rfl, hl⟩ := hd
        match es, hl with
        | [g, t], _ =>
          rw [M.diff]
          have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.le_add_left 3 (M g))
          omega
      · rw [M.fn f es hd]; omega
    | .matrix rows, _ => by rw [M.matrix]; omega
  theorem ML_ge_ten_of_mem (y : String) : ∀ es : List Expr, y ∈ freeVars.freeVarsList es → 10 ≤ ML es
    | [], h => by simp [freeVars.freeVarsList] at h
    | e :: es, h => by
      simp only [freeVars.freeVarsList, List.mem_append] at h
      rw [ML.cons]
      rcases h with h | h
      · have := M_ge_ten_of_mem y e h; omega
      · have := ML_ge_ten_of_mem y es h; omega
end

theorem M_ge_ten_of_dependsOn {e : Expr} {x : String} (h : e.dependsOn x = true) : 10 ≤ M e :=
  M_ge_ten_of_mem x e (by simpa [dependsOn] using h)

-- ---------------------------------------------------------------------------
-- Normal-form facts the power rule needs
-- ---------------------------------------------------------------------------

theorem powerRules_mem : scalarOnly powerRules.toPlain ∈ (pipelineRulesWith norm) := (mem_pipeline_iff _).2 (by simp)
theorem identity_mem : scalarOnly identity.toPlain ∈ (pipelineRulesWith norm) := (mem_pipeline_iff _).2 (by simp)

/-- A normal node has no matrix literal among its children (`la.context` would fire). -/
theorem normal_scalar {e : Expr} (h : Normal (pipelineRulesWith norm) e) : (children e).any isMatrix = false := by
  cases hm : (children e).any isMatrix with
  | false => rfl
  | true => exact absurd h.noFire (not_noFire_of_lit_child hm)

theorem normal_pow_facts {b x : Expr} (h : Normal (pipelineRulesWith norm) (.pow b x)) :
    isZero x = false ∧ isOne x = false ∧ isOne b = false := by
  have := h.noFire _ powerRules_mem
  simp only [scalarOnly, Rule.toPlain, powerRules, powerApply, powerAt, normal_scalar h, Bool.false_eq_true,
    ↓reduceIte] at this
  refine ⟨?_, ?_, ?_⟩
  · cases hz : isZero x with
    | false => rfl
    | true => rw [hz] at this; simp at this
  · cases hz : isZero x <;> cases ho : isOne x <;> simp_all
  · cases hz : isZero x <;> cases ho : isOne x <;> cases hb : isOne b <;> simp_all

/-- A normal power of numerals has a non-integer exponent (else `powNumeric` evaluates it). -/
theorem normal_pow_num {p q : Q} (h : Normal (pipelineRulesWith norm) (.pow (.num p) (.num q))) : q.isInt = false := by
  have := h.noFire _ powerRules_mem
  cases hq : q.isInt with
  | false => rfl
  | true =>
    simp only [scalarOnly, Rule.toPlain, powerRules, powerApply, powerAt, normal_scalar h, Bool.false_eq_true,
      ↓reduceIte, powerNum, powNumeric, hq] at this
    repeat' split at this
    all_goals simp at this

theorem normal_add_len {es : List Expr} (h : Normal (pipelineRulesWith norm) (.add es)) : 2 ≤ es.length := by
  have := h.noFire _ identity_mem
  simp only [scalarOnly, Rule.toPlain, identity, normal_scalar h, Bool.false_eq_true, ↓reduceIte] at this
  match es, this with
  | [], h => simp [identityApply] at h
  | [_], h => simp [identityApply] at h
  | _ :: _ :: _, _ => simp

theorem normal_mul_len {es : List Expr} (h : Normal (pipelineRulesWith norm) (.mul es)) : 2 ≤ es.length := by
  have := h.noFire _ identity_mem
  simp only [scalarOnly, Rule.toPlain, identity, normal_scalar h, Bool.false_eq_true, ↓reduceIte] at this
  match es, this with
  | [], h => simp [identityApply] at h
  | [_], h => simp [identityApply] at h
  | _ :: _ :: _, _ => simp

theorem foldConstants_mem : scalarOnly foldConstants.toPlain ∈ (pipelineRulesWith norm) := (mem_pipeline_iff _).2 (by simp)

theorem normal_add_nums {es : List Expr} (h : Normal (pipelineRulesWith norm) (.add es)) : (es.filter isNum).length < 2 := by
  have := h.noFire _ foldConstants_mem
  simp only [scalarOnly, Rule.toPlain, foldConstants, foldApply, normal_scalar h, Bool.false_eq_true,
    ↓reduceIte] at this
  split at this
  · simp at this
  · omega

theorem normal_mul_nums {es : List Expr} (h : Normal (pipelineRulesWith norm) (.mul es)) : (es.filter isNum).length < 2 := by
  have := h.noFire _ foldConstants_mem
  simp only [scalarOnly, Rule.toPlain, foldConstants, foldApply, normal_scalar h, Bool.false_eq_true,
    ↓reduceIte] at this
  split at this
  · simp at this
  · omega

/-- A normal term other than the literal `1` weighs at least 2 (so that a numeric exponent, being
neither 0 nor 1 in a normal power, always weighs 2). -/
theorem M_ge_two_of_normal {e : Expr} (h : Normal (pipelineRulesWith norm) e) (h1 : isOne e = false) : 2 ≤ M e := by
  induction h with
  | mk e hnf hc ih =>
    cases e with
    | num q => simp only [isOne] at h1; rw [M.num]; simp [h1]; split <;> omega
    | var x => rw [M.var]; omega
    | add es =>
      have hl := normal_add_len ⟨_, hnf, hc⟩
      match es, hl with
      | a :: b :: es, _ => rw [M.add_cons, ML.cons]; have := M.pos a; have := M.pos b; omega
    | mul es => rw [M.mul]; omega
    | pow b x =>
      obtain ⟨_, hx1, hb1⟩ := normal_pow_facts ⟨_, hnf, hc⟩
      have hx := ih x (by simp [children]) hx1
      have hb := M.pos b
      rw [M.pow]
      have : (M b + 1) * M x ≥ (1 + 1) * 2 := Nat.mul_le_mul (by omega) hx
      omega
    | fn f es =>
      by_cases hd : f = "diff" ∧ es.length = 2
      · obtain ⟨rfl, hl⟩ := hd
        match es, hl with
        | [g, t], _ => rw [M.diff]; have := three_pow_ge (M g + 3); omega
      · rw [M.fn f es hd]; omega
    | matrix rows => rw [M.matrix]; omega

-- ---------------------------------------------------------------------------
-- Tier 4: constant multiple, product, chain, power
-- ---------------------------------------------------------------------------

theorem Clean.filter {es : List Expr} (p : Expr → Bool) (h : ∀ c ∈ es, Clean c) : ∀ c ∈ es.filter p, Clean c :=
  fun c hc => h c (List.mem_filter.mp hc).1

theorem dec_diffConstMul : Dec norm diffConstMul := by
  intro e res hcn happ herr
  unfold diffConstMul rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i es
    split at happ
    · simp at happ
    · rename_i hne
      simp only [Option.some.injEq] at happ; subst happ
      obtain ⟨hb, he⟩ := diff_clean hcn rfl
      have hcs : ∀ c ∈ es, Clean c := fun c hc => hb.child (by simpa [children] using hc)
      have hcs' : ∀ c ∈ es.filter (fun a => !a.dependsOn x), Clean c := Clean.filter _ hcs
      have hcs'' : ∀ c ∈ es.filter (fun a => a.dependsOn x), Clean c := Clean.filter _ hcs
      have hres : Clean (.mul (es.filter (fun a => !a.dependsOn x) ++ [D (mulN (es.filter (fun a => a.dependsOn x))) x])) :=
        Clean.mul fun c hc => by
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact hcs' c hc
          · simp only [List.mem_singleton] at hc; subst hc
            exact Clean.diff (Clean.mulN hcs'') (Clean.var x)
      apply muLt_of_clean hres he
      left
      simp only [Bool.or_eq_true, not_or, List.isEmpty_iff] at hne
      have hc1 : 1 ≤ (es.filter (fun a => !a.dependsOn x)).length := by
        cases hcl : es.filter (fun a => !a.dependsOn x) with
        | nil => exact absurd hcl hne.1
        | cons => simp
      have hr1 : 1 ≤ (es.filter (fun a => a.dependsOn x)).length := by
        cases hrl : es.filter (fun a => a.dependsOn x) with
        | nil => exact absurd hrl hne.2
        | cons => simp
      have hsplit := ML_filter_add (fun a => a.dependsOn x) es
      have hlen := length_filter_add (fun a => a.dependsOn x) es
      have hmn := M_mulN_le' (es.filter (fun a => a.dependsOn x))
      have hCle := length_le_ML (es.filter (fun a => !a.dependsOn x))
      rw [M.diff, M.mul, M.mul, ML.append, ML.cons, ML.nil, D, M.diff, M.var, List.length_append, List.length_singleton]
      generalize hC : ML (es.filter (fun a => !a.dependsOn x)) = C at *
      generalize hc : (es.filter (fun a => !a.dependsOn x)).length = c at *
      generalize hR : ML (es.filter (fun a => a.dependsOn x)) = R at *
      generalize hr : (es.filter (fun a => a.dependsOn x)).length = r at *
      generalize hmr : M (mulN (es.filter (fun a => a.dependsOn x))) = mr at *
      have hexp : 2 + ML es + 2 * es.length + 3 = (2 + R + 2 * r + 3) + (C + 2 * c) := by omega
      rw [hexp, Nat.pow_add 3 (2 + R + 2 * r + 3) (C + 2 * c)]
      have hA : 1 ≤ 3 ^ (2 + R + 2 * r + 3) := Nat.one_le_pow _ _ (by decide)
      have hB : C + 2 * c + 1 ≤ 3 ^ (C + 2 * c) := three_pow_ge _
      have h1 : 3 ^ (2 + R + 2 * r + 3) * (C + 2 * c + 1) ≤ 3 ^ (2 + R + 2 * r + 3) * 3 ^ (C + 2 * c) :=
        Nat.mul_le_mul_left _ hB
      have h2 : 3 ^ (2 + R + 2 * r + 3) * (C + 2 * c + 1) = 3 ^ (2 + R + 2 * r + 3) * (C + 2 * c) + 3 ^ (2 + R + 2 * r + 3) :=
        Nat.mul_succ _ _
      have h3 : C + 2 * c ≤ 3 ^ (2 + R + 2 * r + 3) * (C + 2 * c) := Nat.le_mul_of_pos_left _ hA
      have h4 : 3 ^ (mr + 3) ≤ 3 ^ (2 + R + 2 * r + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      have h27 : 27 ≤ 3 ^ (2 + R + 2 * r + 3) := Nat.le_trans (by decide : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_right (by decide) (by omega))
      have h5 : 27 * (C + 2 * c) ≤ 3 ^ (2 + R + 2 * r + 3) * (C + 2 * c) := Nat.mul_le_mul_right _ h27
      omega
  · simp at happ

/-- Bound on the product-rule terms. -/
theorem ML_prodTerms_le (x : String) : ∀ (l acc : List Expr),
    ML (prodTerms x acc l) ≤ 27 * (l.map fun f => 3 ^ M f).sum + l.length * (ML acc + ML l + 2 * (acc.length + l.length) + 14)
  | [], _ => by show ML [] ≤ _; simp [ML]
  | f :: rest, acc => by
    have ih := ML_prodTerms_le x rest (acc ++ [f])
    show ML (Expr.mul (D f x :: (acc ++ rest)) :: prodTerms x (acc ++ [f]) rest) ≤ _
    simp only [ML.cons, M.mul, ML.append, D, M.diff, M.var, List.length_cons, List.length_append,
      List.length_singleton, List.map_cons, List.sum_cons, ML.nil, three_pow_add_three] at ih ⊢
    have hm := M.pos f
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add] at ih
    have key : rest.length * (ML acc + M f + ML rest + 2 * (acc.length + 1 + rest.length) + 14)
        = rest.length * (ML acc + (M f + ML rest) + 2 * (acc.length + (rest.length + 1)) + 14) := by
      congr 1; omega
    rw [key] at ih
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem dec_diffProduct : Dec norm diffProduct := by
  intro e res hcn happ herr
  unfold diffProduct rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i f g fs
    simp only [Option.some.injEq] at happ; subst happ
    obtain ⟨hb, he⟩ := diff_clean hcn rfl
    have hcs : ∀ c ∈ f :: g :: fs, Clean c := fun c hc => hb.child (by simpa [children] using hc)
    have hterms : ∀ acc l, (∀ c ∈ acc, Clean c) → (∀ c ∈ l, Clean c) → ∀ t ∈ prodTerms x acc l, Clean t := by
      intro acc l
      induction l generalizing acc with
      | nil => intro _ _ t ht; simp [prodTerms] at ht
      | cons a l ih =>
        intro hacc hl t ht
        simp only [prodTerms, List.mem_cons] at ht
        rcases ht with rfl | ht
        · apply Clean.mul
          intro c hc
          simp only [List.mem_cons, List.mem_append] at hc
          rcases hc with rfl | hc | hc
          · exact Clean.diff (hl a List.mem_cons_self) (Clean.var x)
          · exact hacc c hc
          · exact hl c (List.mem_cons_of_mem _ hc)
        · have hacc' : ∀ c ∈ acc ++ [a], Clean c := by
            intro c hc
            simp only [List.mem_append, List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact hacc c hc
            · exact hl _ List.mem_cons_self
          exact ih (acc ++ [a]) hacc' (fun c hc => hl c (List.mem_cons_of_mem _ hc)) t ht
    have hres : Clean (.add (prodTerms x [] (f :: g :: fs))) :=
      Clean.add (hterms [] _ (by simp) hcs)
    apply muLt_of_clean hres he
    left
    have hne : prodTerms x [] (f :: g :: fs) ≠ [] := by simp [prodTerms]
    rw [M_add_ne_nil hne, M.diff, M.mul]
    have hb := ML_prodTerms_le x (f :: g :: fs) []
    simp only [ML.nil, List.length_nil, Nat.zero_add] at hb
    have hsum := sum_three_pow_le (f :: g :: fs) (by simp)
    have hk2 : 2 ≤ (f :: g :: fs).length := by simp
    have hSk : (f :: g :: fs).length ≤ ML (f :: g :: fs) := length_le_ML _
    generalize hS : ML (f :: g :: fs) = S at *
    generalize hk : (f :: g :: fs).length = k at *
    have hexp : 2 + S + 2 * k + 3 = (S + (2 * k + 2)) + 3 := by omega
    rw [hexp, three_pow_add_three, Nat.pow_add]
    have hP1 : S + 1 ≤ 3 ^ S := three_pow_ge S
    have hQ1 : 2 * k + 3 ≤ 3 ^ (2 * k + 2) := three_pow_ge _
    generalize hP : 3 ^ S = P at *
    generalize hQ : 3 ^ (2 * k + 2) = Q at *
    have h1 : P * (2 * k + 3) ≤ P * Q := Nat.mul_le_mul_left _ hQ1
    have h2 : P * (2 * k + 3) = 2 * (P * k) + 3 * P := by
      rw [Nat.mul_add, Nat.mul_comm P (2 * k), Nat.mul_assoc, Nat.mul_comm k P, Nat.mul_comm P 3]
    have h3 : k * (S + 1) ≤ P * k := by rw [Nat.mul_comm P k]; exact Nat.mul_le_mul_left _ hP1
    have h4 : k * (S + 1) = k * S + k := Nat.mul_succ _ _
    have h5 : k * k ≤ k * S := Nat.mul_le_mul_left _ hSk
    have h6 : k * (S + 2 * k + 14) = k * S + 2 * (k * k) + 14 * k := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm k (2 * k), Nat.mul_assoc, Nat.mul_comm k 14]
    omega
  · simp at happ

theorem outerOf_spec {f : String} {u fp : Expr} {law : String} (hu : Clean u) (h : outerOf f u = some (fp, law)) :
    Clean fp ∧ M fp ≤ 10 * M u + 21 ∧ f ≠ "diff" ∧ cmdNames.contains f = false := by
  unfold outerOf at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, _⟩ := h
  · exact ⟨Clean.fn₁ (by decide) (by decide) hu, by rw [M.fn₁ (by decide)]; omega, by decide, by decide⟩
  · refine ⟨Clean.mul ?_, ?_, by decide, by decide⟩
    · intro c hc; simp [Expr.neg] at hc
      rcases hc with rfl | rfl
      · exact Clean.num _
      · exact Clean.fn₁ (by decide) (by decide) hu
    · simp only [Expr.neg, M.mul, ML.cons, ML.nil, M.minusOne, M.fn₁ (by decide : "sin" ≠ "diff"),
        List.length_cons, List.length_nil]; omega
  · refine ⟨Clean.pow (Clean.fn₁ (by decide) (by decide) hu) (Clean.num _), ?_, by decide, by decide⟩
    have : M (Expr.ofInt (-2)) = 2 := by simp [Expr.ofInt, M.num]; decide
    rw [M.pow, this, M.fn₁ (by decide)]; omega
  · exact ⟨Clean.fn₁ (by decide) (by decide) hu, by rw [M.fn₁ (by decide)]; omega, by decide, by decide⟩
  · refine ⟨Clean.pow hu (Clean.num _), ?_, by decide, by decide⟩
    rw [M.pow, M.minusOne]; omega

theorem innerOf_cases (u : Expr) (x : String) : innerOf u x = [] ∨ innerOf u x = [D u x] := by
  unfold innerOf
  cases u with
  | var y => by_cases hy : (y == x) = true <;> simp [hy]
  | _ => exact Or.inr rfl

theorem dec_diffChain : Dec norm diffChain := by
  intro e res hcn happ herr
  unfold diffChain rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i f u
    obtain ⟨hb, he⟩ := diff_clean hcn rfl
    have hu : Clean u := hb.child (by simp [children])
    split at happ
    · rename_i fp law hmatch
      obtain ⟨hfc, hfm, hfd, hfn⟩ := outerOf_spec hu hmatch
      simp only [Option.some.injEq] at happ; subst happ
      dsimp only
      have hin := innerOf_cases u x
      generalize hinner : innerOf u x = inner at hin ⊢
      have hinner_clean : ∀ c ∈ inner, Clean c := by
        intro c hc
        rcases hin with h | h <;> rw [h] at hc
        · simp at hc
        · simp only [List.mem_singleton] at hc; subst hc; exact Clean.diff hu (Clean.var x)
      have hinner_M : ML inner + 2 * inner.length ≤ 3 ^ (M u + 3) + 12 := by
        rcases hin with h | h <;> rw [h]
        · simp [ML]
        · simp [ML, D, M.diff, M.var]
      have hres : Clean (.mul (fp :: inner)) := Clean.mul fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hfc
        · exact hinner_clean c hc
      apply muLt_of_clean hres he
      left
      rw [M.diff, M.mul, ML.cons, List.length_cons, M.fn₁ hfd]
      have hMu := M.pos u
      have hexp : 5 * M u + 10 + 3 = M u + (4 * M u + 13) := by omega
      rw [hexp, Nat.pow_add]
      have h4 : 3 ^ (M u + 3) = 27 * 3 ^ M u := three_pow_add_three _
      have hA1 : M u + 1 ≤ 3 ^ M u := three_pow_ge _
      have hB1 : 3 ^ 13 ≤ 3 ^ (4 * M u + 13) := Nat.pow_le_pow_right (by decide) (by omega)
      have h13 : 3 ^ 13 = 1594323 := by decide
      rw [h13] at hB1
      generalize hA : 3 ^ M u = A at *
      generalize hB : 3 ^ (4 * M u + 13) = B at *
      have h1 : A * 1594323 ≤ A * B := Nat.mul_le_mul_left _ hB1
      omega
    · simp at happ
  · simp at happ

theorem dec_diffPower : Dec norm diffPower := by
  intro e res hcn happ herr
  unfold diffPower rule at happ
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at happ
  obtain ⟨⟨body, x⟩, hp, happ⟩ := happ
  rw [target_spec hp] at hcn ⊢
  dsimp only at hcn happ ⊢
  split at happ
  · rename_i base exp
    obtain ⟨hb, he⟩ := diff_clean hcn rfl
    have hbase : Clean base := hb.child (by simp [children])
    have hexp : Clean exp := hb.child (by simp [children])
    have hnorm : Normal (pipelineRulesWith norm) (.pow base exp) := hcn _ (by simp [children])
    obtain ⟨_, hx1, hb1⟩ := normal_pow_facts hnorm
    have hMe2 : 2 ≤ M exp := M_ge_two_of_normal (hnorm.children exp (by simp [children])) hx1
    have hMb2 : 2 ≤ M base := M_ge_two_of_normal (hnorm.children base (by simp [children])) hb1
    have hN : M (.pow base exp) = (M base + 1) * M exp - 1 := M.pow _ _
    have hN2 : (M base + 1) * M exp = M base * M exp + M exp := Nat.succ_mul _ _
    have hnm1 : M (Expr.add [exp, Expr.minusOne]) = M exp + 2 := by
      rw [M.add_cons, ML.cons, ML.nil, M.minusOne]
    have hMp : M (.pow base (Expr.add [exp, Expr.minusOne])) = (M base + 1) * (M exp + 2) - 1 := by
      rw [M.pow, hnm1]
    have hexpand : (M base + 1) * (M exp + 2) = M base * M exp + 2 * M base + M exp + 2 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul]; omega
    have hcl_nm1 : Clean (Expr.add [exp, Expr.minusOne]) :=
      Clean.add (by intro c hc; simp at hc; rcases hc with rfl | rfl; exact hexp; exact Clean.num _)
    have hLHS : M (.fn "diff" [.pow base exp, .var x]) = 27 * 3 ^ ((M base + 1) * M exp - 1) + 10 := by
      rw [M.diff, three_pow_add_three, M.var, hN]
    split at happ
    · -- case (i): base depends on x, exponent does not
      rename_i hdep
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hdep
      have hten : 10 ≤ M base := M_ge_ten_of_dependsOn hdep.1
      have hpow1 := Nat.one_le_pow (M base) 3 (by decide)
      have bound1 : Clean (Expr.mul [exp, .pow base (Expr.add [exp, Expr.minusOne])]) ∧
          M (Expr.mul [exp, .pow base (Expr.add [exp, Expr.minusOne])]) ≤
            M base * M exp + 2 * M base + 2 * M exp + 27 * 3 ^ M base + 19 := by
        refine ⟨Clean.mul ?_, ?_⟩
        · intro c hc; simp at hc; rcases hc with rfl | rfl
          · exact hexp
          · exact Clean.pow hbase hcl_nm1
        · rw [M.mul, ML.cons, ML.cons, ML.nil, hMp]
          simp only [List.length_cons, List.length_nil]; omega
      have bound2 : Clean (Expr.mul [exp, .pow base (Expr.add [exp, Expr.minusOne]), D base x]) ∧
          M (Expr.mul [exp, .pow base (Expr.add [exp, Expr.minusOne]), D base x]) ≤
            M base * M exp + 2 * M base + 2 * M exp + 27 * 3 ^ M base + 19 := by
        refine ⟨Clean.mul ?_, ?_⟩
        · intro c hc; simp at hc; rcases hc with rfl | rfl | rfl
          · exact hexp
          · exact Clean.pow hbase hcl_nm1
          · exact Clean.diff hbase (Clean.var x)
        · rw [M.mul, ML.cons, ML.cons, ML.cons, ML.nil, hMp, D, M.diff, M.var, three_pow_add_three]
          simp only [List.length_cons, List.length_nil]; omega
      have main : ∀ r, Clean r → M r ≤ M base * M exp + 2 * M base + 2 * M exp + 27 * 3 ^ M base + 19 →
          MuLt (μ r) (μ (.fn "diff" [.pow base exp, .var x])) := by
        intro r hr hM
        apply muLt_of_clean hr he
        left
        rw [hLHS]
        have hP1 : 2 * M base ≤ M base * M exp := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hMe2
        generalize hP : M base * M exp = P at *
        have hN' : (M base + 1) * M exp - 1 = (M base + 1) + (P - M base + M exp - 2) := by omega
        rw [hN', Nat.pow_add 3 (M base + 1) (P - M base + M exp - 2)]
        have hA3 : 3 * 3 ^ M base = 3 ^ (M base + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        have hA177 : 3 ^ 11 ≤ 3 ^ (M base + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have h11 : 3 ^ 11 = 177147 := by decide
        rw [h11] at hA177
        generalize hA : 3 ^ (M base + 1) = A at *
        generalize hW : P - M base + M exp - 2 = W at *
        have hW1 : W + 1 ≤ 3 ^ W := three_pow_ge W
        have h1 : A * (W + 1) ≤ A * 3 ^ W := Nat.mul_le_mul_left _ hW1
        have h2 : A * 11 ≤ A * (W + 1) := Nat.mul_le_mul_left _ (by omega)
        have h3 : 177147 * (W + 1) ≤ A * (W + 1) := Nat.mul_le_mul_right _ hA177
        omega
      split at happ
      · rename_i y
        split at happ
        · simp only [Option.some.injEq] at happ; subst happ
          exact main _ bound1.1 bound1.2
        · simp only [Option.some.injEq] at happ; subst happ
          exact main _ bound2.1 bound2.2
      · simp only [Option.some.injEq] at happ; subst happ
        exact main _ bound2.1 bound2.2
    · split at happ
      · -- case (ii): exponent depends on x, base does not
        rename_i hdep
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hdep
        have hten : 10 ≤ M exp := M_ge_ten_of_dependsOn hdep.2
        simp only [Option.some.injEq] at happ; subst happ
        have hres : Clean (.mul [.pow base exp, .fn "ln" [base], D exp x]) :=
          Clean.mul (by intro c hc; simp at hc; rcases hc with rfl | rfl | rfl
                        · exact Clean.pow hbase hexp
                        · exact Clean.fn₁ (by decide) (by decide) hbase
                        · exact Clean.diff hexp (Clean.var x))
        apply muLt_of_clean hres he
        left
        rw [hLHS, M.mul, ML.cons, ML.cons, ML.cons, ML.nil, hN, M.fn₁ (by decide), D, M.diff, M.var,
          three_pow_add_three (M exp)]
        simp only [List.length_cons, List.length_nil]
        have hP1 : 10 * M base ≤ M base * M exp := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hten
        have hP2 : M exp ≤ M base * M exp := Nat.le_mul_of_pos_left _ (by omega)
        generalize hP : M base * M exp = P at *
        have hN' : (M base + 1) * M exp - 1 = M exp + (P - 1) := by omega
        rw [hN', Nat.pow_add 3 (M exp) (P - 1)]
        have hA1 : M exp + 1 ≤ 3 ^ M exp := three_pow_ge _
        have hB1 : P ≤ 3 ^ (P - 1) := by have := three_pow_ge (P - 1); omega
        have hB2 : 3 ^ 19 ≤ 3 ^ (P - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have h19 : 3 ^ 19 = 1162261467 := by decide
        rw [h19] at hB2
        generalize hA : 3 ^ M exp = A at *
        generalize hB : 3 ^ (P - 1) = B at *
        have h1 : A * P ≤ A * B := Nat.mul_le_mul_left _ hB1
        have h2 : 11 * P ≤ A * P := Nat.mul_le_mul_right _ (by omega)
        have h5 : A * 1162261467 ≤ A * B := Nat.mul_le_mul_left _ hB2
        omega
      · split at happ
        · -- case (iii): both depend on x
          rename_i hdep
          simp only [Bool.and_eq_true] at hdep
          have htb : 10 ≤ M base := M_ge_ten_of_dependsOn hdep.1
          have hte : 10 ≤ M exp := M_ge_ten_of_dependsOn hdep.2
          simp only [Option.some.injEq] at happ; subst happ
          have hres : Clean (.mul [.pow base exp, .add [.mul [D exp x, .fn "ln" [base]], .mul [exp, Expr.div (D base x) base]]]) := by
            apply Clean.mul; intro c hc; simp at hc; rcases hc with rfl | rfl
            · exact Clean.pow hbase hexp
            · apply Clean.add; intro c hc; simp at hc; rcases hc with rfl | rfl
              · apply Clean.mul; intro c hc; simp at hc; rcases hc with rfl | rfl
                · exact Clean.diff hexp (Clean.var x)
                · exact Clean.fn₁ (by decide) (by decide) hbase
              · apply Clean.mul; intro c hc; simp at hc; rcases hc with rfl | rfl
                · exact hexp
                · apply Clean.mul; intro c hc; simp [Expr.div] at hc; rcases hc with rfl | rfl
                  · exact Clean.diff hbase (Clean.var x)
                  · exact Clean.pow hbase (Clean.num _)
          apply muLt_of_clean hres he
          left
          rw [hLHS]
          simp only [M.mul, ML.cons, ML.nil, M.add_cons, hN, M.fn₁ (by decide : "ln" ≠ "diff"), D, M.diff, M.var,
            Expr.div, M.pow, M.minusOne, three_pow_add_three, List.length_cons, List.length_nil]
          have hP1 : 10 * M base ≤ M base * M exp := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hte
          have hP2 : M exp ≤ M base * M exp := Nat.le_mul_of_pos_left _ (by omega)
          generalize hP : M base * M exp = P at *
          have hN' : (M base + 1) * M exp - 1 = M exp + (M base + (P - M base - 1)) := by omega
          rw [hN', Nat.pow_add 3 (M exp) (M base + (P - M base - 1)), Nat.pow_add 3 (M base) (P - M base - 1)]
          have hA1 : M exp + 1 ≤ 3 ^ M exp := three_pow_ge _
          have hB1 : M base + 1 ≤ 3 ^ M base := three_pow_ge _
          have hC1 : P - M base ≤ 3 ^ (P - M base - 1) := by have := three_pow_ge (P - M base - 1); omega
          generalize hA : 3 ^ M exp = A at *
          generalize hB : 3 ^ M base = B at *
          generalize hC : 3 ^ (P - M base - 1) = C at *
          have hAB : A + B ≤ A * B := by
            have h1 := Nat.mul_le_mul_left A hB1
            have h2 := Nat.mul_le_mul_right B hA1
            have h3 : A * (M base + 1) = A * M base + A := Nat.mul_succ _ _
            have h4 : (M exp + 1) * B = M exp * B + B := Nat.succ_mul _ _
            have h5 : A ≤ A * M base := Nat.le_mul_of_pos_right _ (by omega)
            have h6 : B ≤ M exp * B := Nat.le_mul_of_pos_left _ (by omega)
            omega
          have h1 : A * (B * (P - M base)) ≤ A * (B * C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hC1)
          have h3 : A * (B * 90) ≤ A * (B * (P - M base)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
          have h3' : A * (B * 90) = 90 * (A * B) := by
            rw [Nat.mul_comm B 90, ← Nat.mul_assoc, Nat.mul_comm A 90, Nat.mul_assoc]
          have h4 : P - M base ≤ A * B * (P - M base) := Nat.le_mul_of_pos_left _ (by omega)
          rw [Nat.mul_assoc] at h4
          omega
        · simp at happ
  · simp at happ

-- ---------------------------------------------------------------------------
-- Numerals: integrality and weight
-- ---------------------------------------------------------------------------

theorem M_num_le_four (q : Q) : M (.num q) ≤ 4 := by rw [M.num]; split <;> (try split) <;> omega
theorem M_num_le_two_of_isInt {q : Q} (h : q.isInt = true) : M (.num q) ≤ 2 := by
  rw [M.num]; split <;> simp [h]
theorem M_num_of_not_isInt {q : Q} (h : q.isInt = false) : M (.num q) = 4 := by
  have h1 : q.isOne = false := by
    cases ho : q.isOne with
    | false => rfl
    | true => simp only [Q.isOne, beq_iff_eq] at ho; simp [Q.isInt, ho] at h
  rw [M.num, h1, h]; rfl

theorem Q_isInt_add {a b : Q} (ha : a.isInt = true) (hb : b.isInt = true) : (a + b).isInt = true := by
  have ha' : a.val.den = 1 := by simpa [Q.isInt] using ha
  have hb' : b.val.den = 1 := by simpa [Q.isInt] using hb
  show ((a.val + b.val).den == 1) = true
  rw [Rat.add_def', ha', hb', Rat.den_mkRat]
  simp [Nat.gcd_one_left]

theorem Q_isInt_mul {a b : Q} (ha : a.isInt = true) (hb : b.isInt = true) : (a * b).isInt = true := by
  have ha' : a.val.den = 1 := by simpa [Q.isInt] using ha
  have hb' : b.val.den = 1 := by simpa [Q.isInt] using hb
  show ((a.val * b.val).den == 1) = true
  rw [Rat.mul_def', ha', hb', Rat.den_mkRat]
  simp [Nat.gcd_one_left]

/-- The weight of a sum of two numerals is at most the sum of the weights. -/
theorem M_num_add_le (p q : Q) : M (.num (p + q)) ≤ M (.num p) + M (.num q) := by
  have hp := M.pos (.num p); have hq := M.pos (.num q)
  cases hi : (p + q).isInt with
  | true => have := M_num_le_two_of_isInt hi; omega
  | false =>
    rw [M_num_of_not_isInt hi]
    cases hpi : p.isInt with
    | false => rw [M_num_of_not_isInt hpi]; omega
    | true =>
      cases hqi : q.isInt with
      | false => rw [M_num_of_not_isInt hqi]; omega
      | true => have := Q_isInt_add hpi hqi; rw [hi] at this; exact absurd this Bool.false_ne_true

theorem sumQ_isInt : ∀ (l : List Expr) (acc : Q), acc.isInt = true → (∀ e ∈ l, (numOf e).isInt = true) →
    (l.foldl (fun s e => s + numOf e) acc).isInt = true
  | [], _, h, _ => h
  | e :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    exact sumQ_isInt l _ (Q_isInt_add h (hl e List.mem_cons_self)) (fun d hd => hl d (List.mem_cons_of_mem _ hd))

theorem prodQ_isInt : ∀ (l : List Expr) (acc : Q), acc.isInt = true → (∀ e ∈ l, (numOf e).isInt = true) →
    (l.foldl (fun s e => s * numOf e) acc).isInt = true
  | [], _, h, _ => h
  | e :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    exact prodQ_isInt l _ (Q_isInt_mul h (hl e List.mem_cons_self)) (fun d hd => hl d (List.mem_cons_of_mem _ hd))

theorem Q_zero_isInt' : Q.zero.isInt = true := by decide
theorem Q_one_isInt : Q.one.isInt = true := by decide

theorem ML_ge_of_mem {e : Expr} : ∀ {l : List Expr}, e ∈ l → M e + (l.length - 1) ≤ ML l
  | [], h => by simp at h
  | c :: l, h => by
    simp only [ML.cons, List.length_cons, Nat.add_sub_cancel]
    rcases List.mem_cons.mp h with rfl | h
    · have := length_le_ML l; omega
    · have hl := ML_ge_of_mem h; have hc := M.pos c
      cases l with
      | nil => simp at h
      | cons d l' => simp only [List.length_cons, Nat.add_sub_cancel] at hl ⊢; omega

/-- A list of at least two numerals weighs at least the weight of their sum, and strictly more than
the weight of their product plus two (the facts `simp.fold-constants` needs). -/
theorem nums_weight (nums : List Expr) (hn : ∀ e ∈ nums, isNum e = true) (h2 : 2 ≤ nums.length) :
    M (.num (sumQ nums)) ≤ ML nums ∧ M (.num (prodQ nums)) + 2 < ML nums + 4 := by
  have hlen := length_le_ML nums
  by_cases hall : ∀ e ∈ nums, (numOf e).isInt = true
  · have hs := M_num_le_two_of_isInt (show (sumQ nums).isInt = true from sumQ_isInt nums Q.zero Q_zero_isInt' hall)
    have hp := M_num_le_two_of_isInt (show (prodQ nums).isInt = true from prodQ_isInt nums Q.one Q_one_isInt hall)
    constructor <;> omega
  · obtain ⟨e, he'⟩ := Classical.not_forall.mp hall
    obtain ⟨he, hne⟩ := Classical.not_imp.mp he'
    have he4 : 4 ≤ M e := by
      have hne' := hn e he
      obtain ⟨q, rfl⟩ : ∃ q, e = .num q := by cases e <;> simp [isNum] at hne' ⊢
      rw [M_num_of_not_isInt (by simpa [numOf] using hne)]; exact Nat.le_refl _
    have := ML_ge_of_mem he
    have := M_num_le_four (sumQ nums); have := M_num_le_four (prodQ nums)
    constructor <;> omega

-- ---------------------------------------------------------------------------
-- Big bases weigh at least 9 in a normal term
-- ---------------------------------------------------------------------------

theorem bigBase_of_normal {e : Expr} (h : Normal (pipelineRulesWith norm) e) (hn : isNum e = false) : bigBase e = true := by
  cases e with
  | num _ => simp [isNum] at hn
  | add es =>
    have := normal_add_len h
    match es, this with
    | _ :: _ :: _, _ => rfl
  | mul es =>
    have := normal_mul_len h
    match es, this with
    | _ :: _ :: _, _ => rfl
  | _ => rfl

theorem filter_isNum_length_lt {es : List Expr} (hlen : 2 ≤ es.length) (hnums : (es.filter isNum).length < 2) :
    ∃ e ∈ es, isNum e = false := by
  by_cases h : ∀ e ∈ es, isNum e = true
  · have : es.filter isNum = es := List.filter_eq_self.mpr h
    rw [this] at hnums; omega
  · obtain ⟨e, he'⟩ := Classical.not_forall.mp h
    obtain ⟨he, hne⟩ := Classical.not_imp.mp he'
    exact ⟨e, he, by cases hn : isNum e with | false => rfl | true => exact absurd hn hne⟩

theorem M_ge_nine_of_normal {e : Expr} (h : Normal (pipelineRulesWith norm) e) (hn : isNum e = false) : 9 ≤ M e := by
  induction h with
  | mk e hnf hc ih =>
    cases e with
    | num _ => simp [isNum] at hn
    | var _ => rw [M.var]; omega
    | add es =>
      have hl := normal_add_len ⟨_, hnf, hc⟩
      obtain ⟨d, hd, hdn⟩ := filter_isNum_length_lt hl (normal_add_nums ⟨_, hnf, hc⟩)
      have := ih d (by simpa [children] using hd) hdn
      have := ML_ge_of_mem (l := es) hd
      rw [M_add_ne_nil (by cases es <;> simp_all)]
      omega
    | mul es =>
      have hl := normal_mul_len ⟨_, hnf, hc⟩
      obtain ⟨d, hd, hdn⟩ := filter_isNum_length_lt hl (normal_mul_nums ⟨_, hnf, hc⟩)
      have := ih d (by simpa [children] using hd) hdn
      have := ML_ge_of_mem (l := es) hd
      rw [M.mul]; omega
    | pow b x =>
      obtain ⟨_, hx1, hb1⟩ := normal_pow_facts ⟨_, hnf, hc⟩
      have hxn := hc x (by simp [children])
      have hbn := hc b (by simp [children])
      rw [M.pow]
      cases hbnum : isNum b with
      | false =>
        have hb9 := ih b (by simp [children]) hbnum
        have hx1 := M.pos x
        have : (M b + 1) * M x ≥ (9 + 1) * 1 := Nat.mul_le_mul (by omega) hx1
        omega
      | true =>
        cases hxnum : isNum x with
        | false =>
          have hx9 := ih x (by simp [children]) hxnum
          have hb1 := M.pos b
          have : (M b + 1) * M x ≥ (1 + 1) * 9 := Nat.mul_le_mul (by omega) hx9
          omega
        | true =>
          obtain ⟨p, rfl⟩ : ∃ p, b = .num p := by cases b <;> simp [isNum] at hbnum ⊢
          obtain ⟨q, rfl⟩ : ∃ q, x = .num q := by cases x <;> simp [isNum] at hxnum ⊢
          have hq := normal_pow_num ⟨_, hnf, hc⟩
          rw [M_num_of_not_isInt hq]
          have := M_ge_two_of_normal hbn hb1
          have : (M (.num p) + 1) * 4 ≥ (2 + 1) * 4 := Nat.mul_le_mul (by omega) (Nat.le_refl _)
          omega
    | fn f es =>
      by_cases hd : f = "diff" ∧ es.length = 2
      · obtain ⟨rfl, hl⟩ := hd
        match es, hl with
        | [g, t], _ =>
          rw [M.diff]
          have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.le_add_left 3 (M g))
          omega
      · rw [M.fn f es hd]; omega
    | matrix rows => rw [M.matrix]; omega

-- ---------------------------------------------------------------------------
-- Scalar rules: the node is clean, so only `M` and `size` matter
-- ---------------------------------------------------------------------------

/-- A `scalarOnly` rule fires only on literal-free nodes; with normal children such a node is clean
provided its head is not a command or a malformed `diff`. -/
theorem clean_of_scalar {e : Expr} (hcn : ChildrenNormal (pipelineRulesWith norm) e) (hm : (children e).any isMatrix = false)
    (h1 : cmdOwn e = 0) (h2 : d3Own e = 0) (hnm : isMatrix e = false) : Clean e ∧ ∀ c ∈ children e, Clean c := by
  have hcs : ∀ c ∈ children e, Clean c := fun c hc =>
    Clean.of_normal (hcn c hc) (by
      cases hmc : isMatrix c with
      | false => rfl
      | true => have := List.any_eq_true.2 ⟨c, hc, hmc⟩; rw [hm] at this; exact absurd this Bool.false_ne_true)
  refine ⟨⟨?_, ?_, ?_⟩, hcs⟩
  · rw [count_eq, h1, (countList_eq_zero_iff _ _).2 fun c hc => (hcs c hc).cmd]
  · rw [count_eq, h2, (countList_eq_zero_iff _ _).2 fun c hc => (hcs c hc).d3]
  · have := hasLit_withChildren e (children e) rfl
    rw [withChildren_children'] at this
    rw [this, (hasLitList_eq_false_iff _).2 fun c hc => (hcs c hc).lit, hnm]; rfl

theorem dec_scalar {r : PlainRule}
    (hdec : ∀ e res, ChildrenNormal (pipelineRulesWith norm) e → (children e).any isMatrix = false →
      r.apply e = some res → res.error = none → MuLt (μ res.result) (μ e)) : Dec norm (scalarOnly r) := by
  intro e res hcn happ herr
  simp only [scalarOnly] at happ
  split at happ
  · simp at happ
  · exact hdec e res hcn (Bool.eq_false_iff.mpr ‹_›) happ herr

/-- For `M ≤` plus `size <`, or `M <`. -/
theorem lt_or_of_le {a b s t : Nat} (h : a ≤ b) (hs : a = b → s < t) : a < b ∨ (a = b ∧ s < t) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hs h⟩

theorem sizeList_filter_add (p : Expr → Bool) : ∀ es : List Expr,
    sizeList (es.filter p) + sizeList (es.filter fun a => !p a) = sizeList es
  | [] => rfl
  | e :: es => by
    have ih := sizeList_filter_add p es
    by_cases hp : p e = true
    · simp [List.filter_cons, hp, sizeList]; omega
    · simp [List.filter_cons, hp, sizeList]; omega

theorem sizeList_nums {nums : List Expr} (h : ∀ e ∈ nums, isNum e = true) : sizeList nums = nums.length := by
  induction nums with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    obtain ⟨q, rfl⟩ : ∃ q, e = .num q := by cases e <;> simp [isNum] at he ⊢
    simp only [sizeList, size, ih fun d hd => h d (List.mem_cons_of_mem _ hd), List.length_cons]; omega

theorem sizeList_length_le : ∀ es : List Expr, es.length ≤ sizeList es
  | [] => Nat.le_refl _
  | e :: es => by simp only [List.length_cons, sizeList]; have := size_pos e; have := sizeList_length_le es; omega

-- simp.fold-constants ------------------------------------------------------

theorem dec_foldConstants : Dec norm (scalarOnly foldConstants.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, foldConstants, foldApply] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i h2
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      have hnums : ∀ d ∈ es.filter isNum, isNum d = true := fun d hd => (List.mem_filter.mp hd).2
      obtain ⟨hw, _⟩ := nums_weight _ hnums h2
      have hres : Clean (.add (.num (sumQ (es.filter isNum)) :: es.filter fun e => !isNum e)) := Clean.add fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Clean.num _
        · exact hcs c (List.mem_filter.mp hc).1
      apply muLt_of_clean hres he
      have hsplit := ML_filter_add isNum es
      have hne : es ≠ [] := by cases es <;> simp_all
      rw [M.add_cons, M_add_ne_nil hne]
      apply lt_or_of_le (by omega)
      intro _
      simp only [size, sizeList]
      have := sizeList_filter_add isNum es
      have := sizeList_nums hnums
      omega
    · simp at happ
  · rename_i es
    split at happ
    · rename_i h2
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      have hnums : ∀ d ∈ es.filter isNum, isNum d = true := fun d hd => (List.mem_filter.mp hd).2
      obtain ⟨_, hw⟩ := nums_weight _ hnums h2
      have hres : Clean (.mul (.num (prodQ (es.filter isNum)) :: es.filter fun e => !isNum e)) := Clean.mul fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Clean.num _
        · exact hcs c (List.mem_filter.mp hc).1
      apply muLt_of_clean hres he
      left
      have hsplit := ML_filter_add isNum es
      have hlen := length_filter_add isNum es
      rw [M.mul, M.mul, ML.cons, List.length_cons]
      omega
    · simp at happ
  · simp at happ

-- simp.flatten ---------------------------------------------------------------

theorem unAdd_M (e : Expr) : ML (unAdd e) ≤ M e ∧ (unAdd e = [] → 3 ≤ M e) := by
  cases e with
  | add es =>
    cases es with
    | nil => simp [unAdd, ML, M.add_nil]
    | cons a l => simp [unAdd, M.add_cons, ML.cons]
  | _ => simp [unAdd, ML]

theorem unAdd_size (e : Expr) : sizeList (unAdd e) ≤ size e ∧ (isAdd e = true → sizeList (unAdd e) < size e) := by
  cases e with
  | add es => simp [unAdd, size] <;> omega
  | _ => simp [unAdd, sizeList, isAdd]

theorem flatMap_unAdd_M : ∀ es : List Expr, ML (es.flatMap unAdd) ≤ ML es ∧ (es.flatMap unAdd = [] → 3 * es.length ≤ ML es)
  | [] => by simp [ML]
  | e :: es => by
    have ih := flatMap_unAdd_M es
    have he := unAdd_M e
    simp only [List.flatMap_cons, ML.append, ML.cons, List.append_eq_nil_iff, List.length_cons]
    constructor
    · omega
    · intro ⟨h1, h2⟩; have := he.2 h1; have := ih.2 h2; omega

theorem flatMap_unAdd_size : ∀ es : List Expr, es.any isAdd = true → sizeList (es.flatMap unAdd) < sizeList es
  | [], h => by simp at h
  | e :: es, h => by
    simp only [List.flatMap_cons, sizeList_append, sizeList]
    have he := unAdd_size e
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · have := he.2 h
      have : sizeList (es.flatMap unAdd) ≤ sizeList es := by
        clear h this he
        induction es with
        | nil => simp
        | cons d l ih => simp only [List.flatMap_cons, sizeList_append, sizeList]; have := (unAdd_size d).1; omega
      omega
    · have := flatMap_unAdd_size es h; omega

theorem unMul_M (e : Expr) : ML (unMul e) + 2 * (unMul e).length ≤ M e + 2 ∧
    (isMul e = true → ML (unMul e) + 2 * (unMul e).length + 4 ≤ M e + 2) := by
  cases e with
  | mul es => simp [unMul, M.mul, isMul]; omega
  | _ => simp [unMul, ML, isMul]

theorem flatMap_unMul_M : ∀ es : List Expr, es.any isMul = true →
    ML (es.flatMap unMul) + 2 * (es.flatMap unMul).length + 4 ≤ ML es + 2 * es.length
  | [], h => by simp at h
  | e :: es, h => by
    simp only [List.flatMap_cons, ML.append, ML.cons, List.length_append, List.length_cons]
    have he := unMul_M e
    simp only [List.any_cons, Bool.or_eq_true] at h
    have hle : ML (es.flatMap unMul) + 2 * (es.flatMap unMul).length ≤ ML es + 2 * es.length := by
      clear h he
      induction es with
      | nil => simp [ML]
      | cons d l ih =>
        simp only [List.flatMap_cons, ML.append, ML.cons, List.length_append, List.length_cons]
        have := (unMul_M d).1; omega
    rcases h with h | h
    · have := he.2 h; omega
    · have := flatMap_unMul_M es h; omega

theorem Clean.flatMap_unAdd {es : List Expr} (h : ∀ c ∈ es, Clean c) : ∀ c ∈ es.flatMap unAdd, Clean c := by
  intro c hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨e, he, hce⟩ := hc
  cases e with
  | add xs => exact (h _ he).child (by simpa [unAdd, children] using hce)
  | _ => simp [unAdd] at hce; subst hce; exact h _ he

theorem Clean.flatMap_unMul {es : List Expr} (h : ∀ c ∈ es, Clean c) : ∀ c ∈ es.flatMap unMul, Clean c := by
  intro c hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨e, he, hce⟩ := hc
  cases e with
  | mul xs => exact (h _ he).child (by simpa [unMul, children] using hce)
  | _ => simp [unMul] at hce; subst hce; exact h _ he

theorem dec_flatten : Dec norm (scalarOnly flatten.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, flatten, flattenApply] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i hany
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      apply muLt_of_clean (Clean.add (Clean.flatMap_unAdd hcs)) he
      have hne : es ≠ [] := by cases es <;> simp_all
      have hM := flatMap_unAdd_M es
      have hS := flatMap_unAdd_size es hany
      rw [M_add_ne_nil hne]
      have hMle : M (.add (es.flatMap unAdd)) ≤ ML es := by
        cases hf : es.flatMap unAdd with
        | nil => rw [M.add_nil]; have := hM.2 hf; have : 1 ≤ es.length := by cases es <;> simp_all
                 omega
        | cons a l => rw [← hf, M_add_ne_nil (by simp [hf])]; exact hM.1
      apply lt_or_of_le hMle
      intro _; simp only [size]; omega
    · simp at happ
  · rename_i es
    split at happ
    · rename_i hany
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      apply muLt_of_clean (Clean.mul (Clean.flatMap_unMul hcs)) he
      left
      rw [M.mul, M.mul]
      have := flatMap_unMul_M es hany
      omega
    · simp at happ
  · simp at happ

-- simp.identity ----------------------------------------------------------------

theorem ML_zeros (l : List Expr) (h : ∀ e ∈ l, isZero e = true) : ML l = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    obtain ⟨q, rfl⟩ : ∃ q, e = .num q := by cases e <;> simp [isZero] at he ⊢
    have hq : q.isOne = false := by
      simp only [isZero, Q.isZero, beq_iff_eq] at he
      cases ho : q.isOne with
      | false => rfl
      | true => simp only [Q.isOne, beq_iff_eq] at ho; rw [he] at ho; exact absurd ho (by decide)
    have hqi : q.isInt = true := by simp only [isZero, Q.isZero, beq_iff_eq] at he; simp [Q.isInt, he]
    simp only [ML.cons, M.num, hq, hqi, Bool.false_eq_true, ↓reduceIte, ih fun d hd => h d (List.mem_cons_of_mem _ hd), List.length_cons]; omega

theorem ML_ones (l : List Expr) (h : ∀ e ∈ l, isOne e = true) : ML l = l.length := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    obtain ⟨q, rfl⟩ : ∃ q, e = .num q := by cases e <;> simp [isOne] at he ⊢
    have hq : q.isOne = true := he
    simp only [ML.cons, M.num, hq, ↓reduceIte, ih fun d hd => h d (List.mem_cons_of_mem _ hd), List.length_cons]; omega

theorem M_addN_le' (l : List Expr) : M (addN l) ≤ ML l + (if l = [] then 3 else 0) := by
  match l with
  | [e] => simp [addN, ML]
  | [] => simp [addN, M.add_nil]
  | a :: b :: l => simp [addN, M.add_cons, ML.cons]

theorem dec_identity : Dec norm (scalarOnly identity.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, identity, identityApply] at happ
  split at happ
  -- add [] → 0
  · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, _⟩ := clean_of_scalar hcn hm rfl rfl rfl
    apply muLt_of_clean (Clean.num _) he
    left; rw [M.add_nil]; simp only [M.zero, M.zero']; omega
  -- add [e] → e
  · rename_i x
    simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
    apply muLt_of_clean (hcs x (by simp [children])) he
    right; refine ⟨by rw [M.add_cons, ML.nil, Nat.add_zero], ?_⟩
    simp [size, sizeList]
  -- add with zeros
  · rename_i es hne hne1
    split at happ
    · rename_i hz
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      apply muLt_of_clean (Clean.addN fun c hc => hcs c (List.mem_filter.mp hc).1) he
      left
      have hsplit := ML_filter_add (fun e => !isZero e) es
      have hz' : ML (es.filter fun a => !(!isZero a)) = 2 * (es.filter fun a => !(!isZero a)).length :=
        ML_zeros _ fun d hd => by have := (List.mem_filter.mp hd).2; simpa using this
      have hcnt : 1 ≤ (es.filter fun a => !(!isZero a)).length := by
        obtain ⟨z, hz, hzz⟩ := List.any_eq_true.mp hz
        have : z ∈ es.filter fun a => !(!isZero a) := List.mem_filter.mpr ⟨hz, by simpa using hzz⟩
        exact List.length_pos_of_mem this
      have hb := M_addN_le' (es.filter fun e => !isZero e)
      have hlen : 2 ≤ es.length := by
        match es, hne, hne1 with
        | [], h, _ => exact absurd rfl h
        | [x], _, h => exact absurd rfl (h x)
        | _ :: _ :: _, _, _ => simp
      have hlen2 := length_filter_add (fun e => !isZero e) es
      rw [M_add_ne_nil (by cases es <;> simp_all)]
      split at hb
      · rename_i hnil
        have h0 : ML (es.filter fun e => !isZero e) = 0 := by rw [hnil]; rfl
        rw [hnil] at hlen2; simp only [List.length_nil] at hlen2; omega
      · omega
    · simp at happ
  -- mul [] → 1
  · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, _⟩ := clean_of_scalar hcn hm rfl rfl rfl
    apply muLt_of_clean (Clean.num _) he
    left; rw [M.mul]; simp only [M.one, M.one', ML, List.length_nil]; omega
  -- mul [e] → e
  · rename_i x
    simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
    apply muLt_of_clean (hcs x (by simp [children])) he
    left; rw [M.mul, ML.cons, ML.nil]; omega
  -- mul with zero / one
  · rename_i es hne hne1
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, _⟩ := clean_of_scalar hcn hm rfl rfl rfl
      apply muLt_of_clean (Clean.num _) he
      left; rw [M.mul]; simp only [M.zero, M.zero']
      have : 1 ≤ es.length := by cases es <;> simp_all
      omega
    · split at happ
      · rename_i ho
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
        simp only [children] at hcs
        apply muLt_of_clean (Clean.mulN fun c hc => hcs c (List.mem_filter.mp hc).1) he
        left
        have hsplit := ML_filter_add (fun e => !isOne e) es
        have ho' : ML (es.filter fun a => !(!isOne a)) = (es.filter fun a => !(!isOne a)).length :=
          ML_ones _ fun d hd => by have := (List.mem_filter.mp hd).2; simpa using this
        have hcnt : 1 ≤ (es.filter fun a => !(!isOne a)).length := by
          obtain ⟨z, hz, hzz⟩ := List.any_eq_true.mp ho
          have : z ∈ es.filter fun a => !(!isOne a) := List.mem_filter.mpr ⟨hz, by simpa using hzz⟩
          exact List.length_pos_of_mem this
        have hb := M_mulN_le' (es.filter fun e => !isOne e)
        have hlen2 := length_filter_add (fun e => !isOne e) es
        rw [M.mul]; omega
      · simp at happ
  · simp at happ

-- simp.function ----------------------------------------------------------------

theorem Q_half_isOne : (Q.ofRat (mkRat 1 2)).isOne = false := by decide
theorem Q_half_isInt : (Q.ofRat (mkRat 1 2)).isInt = false := by decide

theorem M_minusOne : M Expr.minusOne = 2 := by simp only [Expr.minusOne]; rw [M.num]; decide

theorem dec_functionRules : Dec norm (scalarOnly functionRules.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, functionRules, functionApply] at happ
  split at happ
  -- sin u / cos u = tan u
  · rename_i es
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    split at happ
    · rename_i u others hft
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨c, hc, hperm⟩ := findTan_perm es hft
      rw [isCosInv_eq hc] at hperm
      have hsin : Clean (.fn "sin" [u]) := hcs _ (hperm.mem_iff.2 (by simp))
      have hu : Clean u := hsin.child (by simp [children])
      have hothers : ∀ o ∈ others, Clean o := fun o ho => hcs o (hperm.mem_iff.2 (by simp [ho]))
      have hres : Clean (mulN (.fn "tan" [u] :: others)) := Clean.mulN fun c hc => by
        simp only [List.mem_cons] at hc; rcases hc with rfl | hc
        · exact Clean.fn₁ (by decide) (by decide) hu
        · exact hothers c hc
      apply muLt_of_clean hres he
      left
      have hlen := hperm.length_eq
      rw [M.mul, ML.perm hperm, ML.cons, ML.cons, M.fn₁ (by decide), M.pow, M.fn₁ (by decide), M_minusOne]
      have hMu := M.pos u
      cases others with
      | nil => simp only [mulN, ML.nil]; rw [M.fn₁ (by decide)]; simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
      | cons o os =>
        simp only [mulN]; rw [M.mul, ML.cons, M.fn₁ (by decide)]
        simp only [List.length_cons] at hlen ⊢; omega
    · simp at happ
  -- sqrt a
  · rename_i a
    simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    have ha := hcs a (by simp [children])
    apply muLt_of_clean (Clean.pow ha (Clean.num _)) he
    left; rw [M.fn₁ (by decide), M.pow, M.num, Q_half_isOne, Q_half_isInt]; simp; omega
  -- ln a
  · rename_i a
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    have ha := hcs a (by simp [children])
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      apply muLt_of_clean (Clean.num _) he
      left; rw [M.fn₁ (by decide)]; simp only [M.zero, M.zero']; have := M.pos a; omega
    · cases a with
      | fn g xs =>
        split at happ
        · rename_i x hx
          obtain ⟨rfl, rfl⟩ := Expr.fn.inj hx
          simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
          apply muLt_of_clean (ha.child (by simp [children])) he
          left; rw [M.fn₁ (by decide), M.fn₁ (by decide)]; omega
        · rename_i heq; simp at heq
        · simp at happ
      | pow b p =>
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        have hb := ha.child (by simp [children] : b ∈ children (.pow b p))
        have hp := ha.child (by simp [children] : p ∈ children (.pow b p))
        have hres : Clean (.mul [p, .fn "ln" [b]]) := Clean.mul fun c hc => by
          simp at hc; rcases hc with rfl | rfl
          · exact hp
          · exact Clean.fn₁ (by decide) (by decide) hb
        apply muLt_of_clean hres he
        left
        have hnorm : Normal (pipelineRulesWith norm) (.pow b p) := hcn _ (by simp [children])
        obtain ⟨_, hp1, hb1⟩ := normal_pow_facts hnorm
        have hMp := M_ge_two_of_normal (hnorm.children p (by simp [children])) hp1
        have hMb := M_ge_two_of_normal (hnorm.children b (by simp [children])) hb1
        rw [M.fn₁ (by decide), M.pow, M.mul, ML.cons, ML.cons, ML.nil, M.fn₁ (by decide)]
        have hX : (M b + 1) * M p ≥ (M b + 1) * 2 := Nat.mul_le_mul_left _ hMp
        have hX2 : (M b + 1) * M p ≥ 3 * M p := Nat.mul_le_mul_right _ (by omega)
        have hX' := Nat.sub_add_cancel (Nat.le_trans (by omega : 1 ≤ (M b + 1) * 2) hX)
        simp only [List.length_cons, List.length_nil]; omega
      | _ => simp at happ
  -- exp a
  · rename_i a
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    have ha := hcs a (by simp [children])
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      apply muLt_of_clean (Clean.num _) he
      left; rw [M.fn₁ (by decide)]; simp only [M.one, M.one']; have := M.pos a; omega
    · split at happ
      · rename_i x
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        apply muLt_of_clean (ha.child (by simp [children])) he
        left; rw [M.fn₁ (by decide), M.fn₁ (by decide)]; omega
      · simp at happ
  -- sin a
  · rename_i a
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      apply muLt_of_clean (Clean.num _) he
      left; rw [M.fn₁ (by decide)]; simp only [M.zero, M.zero']; have := M.pos a; omega
    · simp at happ
  -- cos a
  · rename_i a
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    split at happ
    · simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      apply muLt_of_clean (Clean.num _) he
      left; rw [M.fn₁ (by decide)]; simp only [M.one, M.one']; have := M.pos a; omega
    · simp at happ
  -- abs (num q)
  · rename_i q
    simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
    obtain ⟨he, _⟩ := clean_of_scalar hcn hm (by simp [cmdOwn, cmdNames]) (by simp [d3Own]) rfl
    apply muLt_of_clean (Clean.num _) he
    left; rw [M.fn₁ (by decide)]; have := M.pos (.num q); have := M_num_le_four q.abs; omega
  · simp at happ

-- simp.power -----------------------------------------------------------------

theorem M_num_of_isZero {q : Q} (h : isZero (.num q) = true) : M (.num q) = 2 := by
  simp only [isZero, Q.isZero, beq_iff_eq] at h
  have h1 : q.isOne = false := by simp [Q.isOne, h]
  have h2 : q.isInt = true := by simp only [Q.isInt, h]; rfl
  rw [M.num, h1, h2]; rfl


theorem dec_powerRules : Dec norm (scalarOnly powerRules.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, powerRules, powerApply] at happ
  split at happ
  · rename_i b x
    obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
    have hb : Clean b := hcs b (by simp [children])
    have hx : Clean x := hcs x (by simp [children])
    have hnb : Normal (pipelineRulesWith norm) b := hcn b (by simp [children])
    have hnx : Normal (pipelineRulesWith norm) x := hcn x (by simp [children])
    have hMb := M.pos b; have hMx := M.pos x
    simp only [powerAt] at happ
    split at happ
    -- b^0 → 1
    · rename_i hz
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      apply muLt_of_clean (Clean.num _) he
      left
      obtain ⟨q, rfl⟩ : ∃ q, x = .num q := by cases x <;> simp [isZero] at hz ⊢
      rw [M.pow, M_num_of_isZero hz]
      simp only [M.one, M.one']
      have : (M b + 1) * 2 ≥ (1 + 1) * 2 := Nat.mul_le_mul (by omega) (Nat.le_refl _); omega
    · split at happ
      -- b^1 → b
      · rename_i ho
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        apply muLt_of_clean hb he
        right
        obtain ⟨q, rfl⟩ : ∃ q, x = .num q := by cases x <;> simp [isOne] at ho ⊢
        refine ⟨?_, by simp only [size]; omega⟩
        have hq : q.isOne = true := ho
        rw [M.pow, M.num, hq]; simp
      · split at happ
        -- 1^x → 1
        · rename_i hx1 hb1
          simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
          apply muLt_of_clean (Clean.num _) he
          left
          obtain ⟨q, rfl⟩ : ∃ q, b = .num q := by cases b <;> simp [isOne] at hb1 ⊢
          have hx2 := M_ge_two_of_normal hnx (by simpa using hx1)
          have : (M (.num q) + 1) * M x ≥ (1 + 1) * 2 := Nat.mul_le_mul (by omega) hx2
          rw [M.pow]; simp only [M.one, M.one']; omega
        · split at happ
          -- 0^n → 0
          · rename_i hx1 hb1 hbz
            simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
            apply muLt_of_clean (Clean.num _) he
            left
            simp only [Bool.and_eq_true] at hbz
            obtain ⟨q, rfl⟩ : ∃ q, b = .num q := by have := hbz.1; cases b <;> simp [isZero] at this ⊢
            have hx2 := M_ge_two_of_normal hnx (by simpa using hx1)
            have : (M (.num q) + 1) * M x ≥ (1 + 1) * 2 := Nat.mul_le_mul (by omega) hx2
            rw [M.pow]; simp only [M.zero, M.zero']; omega
          -- powerNum
          · have hx1' : isOne x = false := Bool.eq_false_iff.mpr ‹¬ isOne x = true›
            have hb1' : isOne b = false := Bool.eq_false_iff.mpr ‹¬ isOne b = true›
            cases b with
            | num p =>
              cases x with
              | num q =>
                simp only [powerNum, powNumeric] at happ
                have hMp : 2 ≤ M (.num p) := M_ge_two_of_normal hnb hb1'
                have hMq : 2 ≤ M (.num q) := M_ge_two_of_normal hnx hx1'
                have key : ∀ r : Q, MuLt (μ (.num r)) (μ (.pow (.num p) (.num q))) := fun r => by
                  apply muLt_of_clean (Clean.num _) he
                  left; rw [M.pow]
                  have := M_num_le_four r
                  have : (M (.num p) + 1) * M (.num q) ≥ (2 + 1) * 2 := Nat.mul_le_mul (by omega) hMq
                  omega
                split at happ
                · simp only [Option.some.injEq] at happ; subst happ; exact key _
                · split at happ
                  · split at happ
                    · simp only [Option.some.injEq] at happ; subst happ; exact key _
                    · simp at happ
                  · simp at happ
              | _ => simp [powerNum] at happ
            | pow b' m =>
              cases m with
              | num m =>
                cases x with
                | num n =>
                  simp only [powerNum] at happ
                  split at happ
                  · rename_i hmn
                    simp only [Bool.and_eq_true] at hmn
                    simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
                    have hb' : Clean b' := hb.child (by simp [children])
                    apply muLt_of_clean (Clean.pow hb' (Clean.num _)) he
                    left
                    have hnb' := normal_pow_facts hnb
                    have hm1 : m.isOne = false := hnb'.2.1
                    have hn1 : n.isOne = false := hx1'
                    have hm2 : M (.num m) = 2 := by rw [M.num, hm1, hmn.2]; rfl
                    have hn2 : M (.num n) = 2 := by rw [M.num, hn1, hmn.1]; rfl
                    have hmn2 := M_num_le_two_of_isInt (Q_isInt_mul hmn.2 hmn.1)
                    rw [M.pow, M.pow, M.pow, hm2, hn2]
                    have hb'1 := M.pos b'
                    have : (M b' + 1) * M (.num (m * n)) ≤ (M b' + 1) * 2 := Nat.mul_le_mul_left _ hmn2
                    omega
                  · simp at happ
                | _ => simp [powerNum] at happ
              | _ => simp [powerNum] at happ
            | _ => simp [powerNum] at happ
  · simp at happ

-- simp.collect-powers ------------------------------------------------------------

theorem Clean.baseExp {e : Expr} (h : Clean e) : Clean (baseExp e).1 ∧ Clean (baseExp e).2 := by
  cases e with
  | pow b x => show Clean b ∧ Clean x; exact ⟨h.child (by simp [children]), h.child (by simp [children])⟩
  | _ => exact ⟨h, Clean.num _⟩

theorem M_baseExp (e : Expr) : M e = (M (baseExp e).1 + 1) * M (baseExp e).2 - 1 := by
  cases e with
  | pow b x => simp [baseExp, M.pow]
  | _ => simp [baseExp, Expr.one, M.num, Q_one_isOne]

theorem M_addExp_le' (x y : Expr) : M (addExp x y) ≤ M x + M y := by
  cases x with
  | num p =>
    cases y with
    | num q => simp only [addExp]; exact M_num_add_le p q
    | _ => simp [addExp, M.add_cons, ML.cons, ML.nil]
  | _ => cases y <;> simp [addExp, M.add_cons, ML.cons, ML.nil]

theorem Clean.addExp {x y : Expr} (hx : Clean x) (hy : Clean y) : Clean (addExp x y) := by
  cases x with
  | num p =>
    cases y with
    | num q => exact Clean.num _
    | _ => exact Clean.add (by intro c hc; simp at hc; rcases hc with rfl | rfl; exact hx; exact hy)
  | _ => cases y <;> exact Clean.add (by intro c hc; simp at hc; rcases hc with rfl | rfl; exact hx; exact hy)

theorem mergePowers_spec : ∀ (es l : List Expr) (t : Expr), mergePowers es = some (l, t) →
    ML l + 2 * l.length + 1 ≤ ML es + 2 * es.length ∧ ((∀ c ∈ es, Clean c) → ∀ c ∈ l, Clean c)
  | [], _, _, h => by simp [mergePowers] at h
  | e :: rest, l, t, h => by
    simp only [mergePowers] at h
    split at h
    · split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hfm := List.mem_of_find?_eq_some hf
        have hfp := List.find?_some hf
        have hfb : (baseExp f).1 = (baseExp e).1 := equal_eq hfp
        have hperm := ML.perm (perm_find?_removeFirst _ rest f hf)
        have hlen := (perm_find?_removeFirst _ rest f hf).length_eq
        have hMe := M_baseExp e
        have hMf := M_baseExp f
        rw [hfb] at hMf
        refine ⟨?_, ?_⟩
        · simp only [ML.cons, List.length_cons, M.pow] at hperm hlen ⊢
          have hax := M_addExp_le' (baseExp e).2 (baseExp f).2
          have h1 : (M (baseExp e).1 + 1) * M (addExp (baseExp e).2 (baseExp f).2) ≤
              (M (baseExp e).1 + 1) * (M (baseExp e).2 + M (baseExp f).2) := Nat.mul_le_mul_left _ hax
          have h2 : (M (baseExp e).1 + 1) * (M (baseExp e).2 + M (baseExp f).2) =
              (M (baseExp e).1 + 1) * M (baseExp e).2 + (M (baseExp e).1 + 1) * M (baseExp f).2 := Nat.mul_add _ _ _
          have h3 : 1 * 1 ≤ (M (baseExp e).1 + 1) * M (baseExp e).2 := Nat.mul_le_mul (by omega) (M.pos _)
          have h4 : 1 * 1 ≤ (M (baseExp e).1 + 1) * M (baseExp f).2 := Nat.mul_le_mul (by omega) (M.pos _)
          omega
        · intro hcs c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · have hce := (hcs e List.mem_cons_self).baseExp
            have hcf := (hcs f (List.mem_cons_of_mem _ hfm)).baseExp
            exact Clean.pow hce.1 (Clean.addExp hce.2 hcf.2)
          · have : c ∈ rest := (perm_find?_removeFirst _ rest f hf).mem_iff.mpr (List.mem_cons_of_mem _ hc)
            exact hcs c (List.mem_cons_of_mem _ this)
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, hl', hp⟩ := h
        simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
        have ih := mergePowers_spec rest l' t' hl'
        refine ⟨?_, ?_⟩
        · simp only [ML.cons, List.length_cons]; omega
        · intro hcs c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hcs c List.mem_cons_self
          · exact ih.2 (fun d hd => hcs d (List.mem_cons_of_mem _ hd)) c hc
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, hl', hp⟩ := h
      simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      have ih := mergePowers_spec rest l' t' hl'
      refine ⟨?_, ?_⟩
      · simp only [ML.cons, List.length_cons]; omega
      · intro hcs c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hcs c List.mem_cons_self
        · exact ih.2 (fun d hd => hcs d (List.mem_cons_of_mem _ hd)) c hc

theorem dec_collectPowers : Dec norm (scalarOnly collectPowers.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, collectPowers, collectPowersApply] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i l t hmp
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      obtain ⟨hM, hcl⟩ := mergePowers_spec es l t hmp
      apply muLt_of_clean (Clean.mul (hcl hcs)) he
      left; rw [M.mul, M.mul]; omega
    · simp at happ
  · simp at happ

-- simp.collect-like-terms ---------------------------------------------------------

/-- `coeffRest e = (c, t)` with `t` a big base: `t` and its weight relative to `e`. -/
theorem coeffRest_M {e : Expr} {c : Q} {t : Expr} (h : coeffRest e = (c, t)) (hb : bigBase t = true) :
    M t + M (.num c) ≤ M e + 1 ∧ (Clean e → Clean t) := by
  rcases coeffRest_cases e c t h with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [bigBase, Expr.one] at hb
  · have := M_mulN_le' r
    refine ⟨?_, fun hc => Clean.mulN fun d hd => hc.child (by simp [children]; exact Or.inr hd)⟩
    rw [M.mul, ML.cons, List.length_cons]; omega
  · exact ⟨by rw [M.one']; exact Nat.le_refl _, fun hc => hc⟩

/-- The base of a like-term in a normal node weighs at least 9. -/
theorem coeffRest_nine {e : Expr} {c : Q} {t : Expr} (hn : Normal (pipelineRulesWith norm) e) (h : coeffRest e = (c, t))
    (hb : bigBase t = true) : 9 ≤ M t := by
  rcases coeffRest_cases e c t h with ⟨_, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨rfl, _⟩
  · simp [bigBase, Expr.one] at hb
  · have hlen := normal_mul_len hn
    have hnums := normal_mul_nums hn
    have hr0 : ∀ d ∈ r, isNum d = false := by
      have h2 : (List.filter isNum (Expr.num c :: r)).length < 2 := hnums
      rw [List.filter_cons_of_pos (by rfl)] at h2
      simp only [List.length_cons] at h2
      have hnil : List.filter isNum r = [] := List.eq_nil_of_length_eq_zero (by omega)
      intro d hd
      have := List.filter_eq_nil_iff.mp hnil d hd
      simpa using this
    have hr : ∀ d ∈ r, 9 ≤ M d := fun d hd =>
      M_ge_nine_of_normal (hn.children d (by simp [children]; exact Or.inr hd)) (hr0 d hd)
    match r, hlen with
    | [d], _ => exact hr d List.mem_cons_self
    | d :: d' :: r', _ =>
      simp only [mulN, M.mul, ML.cons]
      have := hr d List.mem_cons_self
      have := hr d' (List.mem_cons_of_mem _ List.mem_cons_self)
      omega
  · exact M_ge_nine_of_normal hn (by cases e <;> simp_all [bigBase, isNum])

theorem mergeTerms_ne_nil : ∀ (es l : List Expr) (t : Expr), mergeTerms es = some (l, t) → l ≠ []
  | [], _, _, h => by simp [mergeTerms] at h
  | e :: rest, l, t, h => by
    simp only [mergeTerms] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; simp
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', t'⟩, _, hp⟩ := h
        simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, _⟩ := hp; simp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', t'⟩, _, hp⟩ := h
      simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, _⟩ := hp; simp

theorem mergeTerms_spec : ∀ (es l : List Expr) (t : Expr), (∀ c ∈ es, Normal (pipelineRulesWith norm) c) →
    mergeTerms es = some (l, t) →
    ML l + 1 ≤ ML es ∧ ((∀ c ∈ es, Clean c) → ∀ c ∈ l, Clean c)
  | [], _, _, _, h => by simp [mergeTerms] at h
  | e :: rest, l, t, hn, h => by
    simp only [mergeTerms] at h
    split at h
    · rename_i hbig
      split at h
      · rename_i f hf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hfm := List.mem_of_find?_eq_some hf
        have hfp := List.find?_some hf
        have hft : (coeffRest f).2 = (coeffRest e).2 := equal_eq hfp
        have hperm := ML.perm (perm_find?_removeFirst _ rest f hf)
        obtain ⟨hMe, hce'⟩ := coeffRest_M (c := (coeffRest e).1) (t := (coeffRest e).2) rfl hbig
        obtain ⟨hMf, hcf'⟩ := coeffRest_M (c := (coeffRest f).1) (t := (coeffRest e).2) (by rw [← hft]) hbig
        refine ⟨?_, ?_⟩
        · simp only [ML.cons] at hperm ⊢
          have h9 : 9 ≤ M (coeffRest e).2 := coeffRest_nine (hn e List.mem_cons_self) rfl hbig
          have hadd := M_num_add_le (coeffRest e).1 (coeffRest f).1
          rw [M.mul, ML.cons, ML.cons, ML.nil]
          simp only [List.length_cons, List.length_nil]
          omega
        · intro hcs d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Clean.mul (by intro k hk; simp at hk; rcases hk with rfl | rfl
                                · exact Clean.num _
                                · exact hce' (hcs e List.mem_cons_self))
          · have : d ∈ rest := (perm_find?_removeFirst _ rest f hf).mem_iff.mpr (List.mem_cons_of_mem _ hd)
            exact hcs d (List.mem_cons_of_mem _ this)
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨l', u⟩, hl', hp⟩ := h
        simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
        have ih := mergeTerms_spec rest l' u (fun d hd => hn d (List.mem_cons_of_mem _ hd)) hl'
        refine ⟨by simp only [ML.cons]; omega, ?_⟩
        intro hcs d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hcs d List.mem_cons_self
        · exact ih.2 (fun k hk => hcs k (List.mem_cons_of_mem _ hk)) d hd
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l', u⟩, hl', hp⟩ := h
      simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      have ih := mergeTerms_spec rest l' u (fun d hd => hn d (List.mem_cons_of_mem _ hd)) hl'
      refine ⟨by simp only [ML.cons]; omega, ?_⟩
      intro hcs d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hcs d List.mem_cons_self
      · exact ih.2 (fun k hk => hcs k (List.mem_cons_of_mem _ hk)) d hd

theorem dec_collectTerms : Dec norm (scalarOnly collectTerms.toPlain) := dec_scalar fun e res hcn hm happ herr => by
  simp only [Rule.toPlain, collectTerms, collectTermsApply] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i l t hmt
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      simp only [children] at hcs
      have hn : ∀ c ∈ es, Normal (pipelineRulesWith norm) c := fun c hc => hcn c (by simpa [children] using hc)
      obtain ⟨hM, hcl⟩ := mergeTerms_spec es l t hn hmt
      apply muLt_of_clean (Clean.add (hcl hcs)) he
      left
      have hne : es ≠ [] := by cases es <;> simp_all [mergeTerms]
      have hlne : l ≠ [] := mergeTerms_ne_nil es l t hmt
      rw [M_add_ne_nil hne, M_add_ne_nil hlne]; omega
    · simp at happ
  · simp at happ

-- the parity rules ------------------------------------------------------------------

theorem dec_parityPowMul : Dec norm (scalarOnly parityPowMul) := dec_scalar fun e res hcn hm happ herr => by
  simp only [parityPowMul] at happ
  split at happ
  · rename_i fs n
    split at happ
    · rename_i hn
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      have hmul : Clean (.mul fs) := hcs _ (by simp [children])
      have hfs : ∀ c ∈ fs, Clean c := fun c hc => hmul.child (by simpa [children] using hc)
      have hres : Clean (.mul (fs.map fun a => .pow a (.num n))) := Clean.mul fun c hc => by
        simp only [List.mem_map] at hc; obtain ⟨a, ha, rfl⟩ := hc
        exact Clean.pow (hfs a ha) (Clean.num _)
      apply muLt_of_clean hres he
      left
      have hn2 : M (.num n) = 2 := by
        simp only [M.num, hn.2, hn.1.1, Bool.false_eq_true, ↓reduceIte]
      have hlen := normal_mul_len (hcn (.mul fs) (by simp [children]))
      have hmap : ∀ l : List Expr, ML (l.map fun a => .pow a (.num n)) = 2 * ML l + l.length := by
        intro l
        induction l with
        | nil => simp [ML]
        | cons a l ih =>
          simp only [List.map_cons, ML.cons, M.pow, hn2, List.length_cons, ih]
          have := M.pos a; omega
      rw [M.pow, M.mul, M.mul, hn2, hmap]
      simp only [List.length_map]
      have := length_le_ML fs
      omega
    · simp at happ
  · simp at happ

theorem dec_parityPowPow : Dec norm (scalarOnly parityPowPow) := dec_scalar fun e res hcn hm happ herr => by
  simp only [parityPowPow] at happ
  split at happ
  · rename_i b m n
    split at happ
    · rename_i hn
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
      simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
      obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
      have hpow : Clean (.pow b m) := hcs _ (by simp [children])
      have hb : Clean b := hpow.child (by simp [children])
      have hmc : Clean m := hpow.child (by simp [children])
      have hres : Clean (.pow b (.mul [m, .num n])) :=
        Clean.pow hb (Clean.mul (by intro c hc; simp at hc; rcases hc with rfl | rfl; exact hmc; exact Clean.num _))
      apply muLt_of_clean hres he
      left
      have hn2 : M (.num n) = 2 := by
        simp only [M.num, hn.1.2, hn.1.1.1, Bool.false_eq_true, ↓reduceIte]
      have hnorm : Normal (pipelineRulesWith norm) (.pow b m) := hcn _ (by simp [children])
      have hm9 : 9 ≤ M m := M_ge_nine_of_normal (hnorm.children m (by simp [children])) hn.2
      have hm8 : M (.mul [m, .num n]) = M m + 8 := by
        rw [M.mul, ML.cons, ML.cons, ML.nil, hn2]; simp only [List.length_cons, List.length_nil]; omega
      rw [M.pow, M.pow, M.pow, hm8, hn2]
      have h1 : (M b + 1) * M m ≥ (M b + 1) * 9 := Nat.mul_le_mul_left _ hm9
      have h2 : (M b + 1) * (M m + 8) = (M b + 1) * M m + (M b + 1) * 8 := Nat.mul_add _ _ _
      have hX1 : 1 * 1 ≤ (M b + 1) * M m := Nat.mul_le_mul (by omega) (M.pos m)
      have h3 := Nat.sub_add_cancel (by omega : 1 ≤ (M b + 1) * M m)
      omega
    · simp at happ
  · simp at happ

-- simp.radical / simp.collect-radicals ---------------------------------------

theorem mergeRadicals_clean {s t m : Expr} (h : mergeRadicals s t = some m) : Clean m := by
  unfold mergeRadicals at h
  dsimp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      split
      · exact Clean.num _
      · split
        · exact Clean.num _
        · split
          · exact Clean.pow (Clean.num _) (Clean.num _)
          · exact Clean.mul fun c hc => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl
              · exact Clean.num _
              · exact Clean.pow (Clean.num _) (Clean.num _)
    · simp at h
  · simp at h

theorem mulRadicalPair_clean {s t m : Expr} (h : mulRadicalPair s t = some m) : Clean m := by
  unfold mulRadicalPair at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      exact Clean.pow (Clean.num _) (Clean.num _)
    · simp at h
  · simp at h

theorem dec_radicalBase : Dec norm (scalarOnly radicalBase) := dec_scalar fun e res hcn hm happ herr => by
  simp only [radicalBase] at happ
  split at happ
  · rename_i a q
    split at happ
    · split at happ
      · rename_i r k hpp
        split at happ
        · rename_i hg
          simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          obtain ⟨hM, hN⟩ := hg
          have he : Clean (.pow (.num a) (.num q)) := Clean.pow (Clean.num _) (Clean.num _)
          have hr : Clean (.pow (.num (Q.ofInt r)) (.num (q * Q.ofInt k))) := Clean.pow (Clean.num _) (Clean.num _)
          rcases Nat.lt_or_eq_of_le hM with hlt | heq
          · exact muLt_of_clean hr he (Or.inl hlt)
          · exact muLt_of_clean' hr he ⟨heq, rfl, hN⟩
        · simp at happ
      · simp at happ
    · simp at happ
  · simp at happ

theorem dec_collectRadicals : Dec norm (scalarOnly collectRadicals) := dec_scalar fun e res hcn hm happ herr => by
  simp only [collectRadicals] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i m others hfp
      split at happ
      · rename_i hg
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        have hres : Clean (addN (m :: others)) := Clean.addN fun c hc => by
          simp only [List.mem_cons] at hc; rcases hc with rfl | hc
          · exact mergeRadicals_clean hst
          · exact hcs c (by simp only [children]; exact hperm.mem_iff.2 (by simp [hc]))
        exact muLt_of_clean hres he (Or.inl hg)
      · simp at happ
    · simp at happ
  · simp at happ

theorem dec_mulRadicals : Dec norm (scalarOnly mulRadicals) := dec_scalar fun e res hcn hm happ herr => by
  simp only [mulRadicals] at happ
  split at happ
  · rename_i es
    split at happ
    · rename_i m others hfp
      split at happ
      · rename_i hg
        simp only [Option.some.injEq] at happ; subst happ; (try dsimp only)
        obtain ⟨he, hcs⟩ := clean_of_scalar hcn hm rfl rfl rfl
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        have hres : Clean (mulN (m :: others)) := Clean.mulN fun c hc => by
          simp only [List.mem_cons] at hc; rcases hc with rfl | hc
          · exact mulRadicalPair_clean hst
          · exact hcs c (by simp only [children]; exact hperm.mem_iff.2 (by simp [hc]))
        exact muLt_of_clean hres he (Or.inl hg)
      · simp at happ
    · simp at happ
  · simp at happ

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- **Every rule of the notebook pipeline decreases `μ` on a node whose children are normal.**
With `normalizeT`'s innermost strategy this is exactly what makes cell evaluation terminate. -/
theorem pipelineOrderedWith (norm : Norm) : Ordered (pipelineRulesWith norm) := ⟨fun r hr => by
  rw [mem_pipeline_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dec_cmdSimplify
  · exact dec_cmdExpand
  · exact dec_cmdRref
  · exact dec_cmdN
  · exact dec_cmdSubst
  · exact dec_cmdIntegrate
  · exact dec_diffHigherOrder
  · exact dec_diffConstant
  · exact dec_diffVariable
  · exact dec_diffSum
  · exact dec_diffConstMul
  · exact dec_diffProduct
  · exact dec_diffPower
  · exact dec_diffChain
  · exact dec_diffMatrix
  · exact dec_laAdd
  · exact dec_laScalarMul
  · exact dec_laMul
  · exact dec_laTranspose
  · exact dec_laDet
  · exact dec_laPow
  · exact dec_flatten
  · exact dec_identity
  · exact dec_foldConstants
  · exact dec_functionRules
  · exact dec_powerRules
  · exact dec_collectPowers
  · exact dec_collectTerms
  · exact dec_parityPowMul
  · exact dec_parityPowPow
  · exact dec_radicalBase
  · exact dec_collectRadicals
  · exact dec_mulRadicals
  · exact dec_laContext⟩

end MathEngine
