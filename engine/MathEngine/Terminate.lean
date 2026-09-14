import MathEngine.Order
/-!
# The pipeline rewriter: innermost normalization under the tiered ordering

`normalizeT` is `normalize` (Rewrite.lean) for rule sets whose termination argument is the tiered
ordering `μ` of `Order.lean` rather than one additive measure. Two things differ:

* **The obligation is conditional.** An `Ordered` rule set proves that each rule decreases `μ`
  *when the children of the node it fires on are already normal* (`ChildrenNormal`). Rules that
  duplicate subterms (the product rule, substitution) only decrease `μ` because nothing reducible
  is inside what they duplicate, and it is the rewriter's innermost strategy — children first, then
  the node — that makes the hypothesis true at every firing. The proof is carried in the result type:
  `normAtT` returns its output together with `μ output ≤ μ input` and `Normal output`, and the
  recursive call after a firing uses exactly those facts.
* **Rules may refuse.** A refusal (`RuleResult.error`) stops normalization with that message, as
  `normalizeFuel` did; nothing is proven about the term in that case, and nothing needs to be.

Nothing here is `partial`, and there is no step budget: the recursion is well-founded on
`(μ e, phase, remaining children)`.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Normal forms
-- ---------------------------------------------------------------------------

/-- No rule in `rules` fires at the root of `e` (refusals count as firing). -/
def NoFire (rules : List PlainRule) (e : Expr) : Prop := ∀ r ∈ rules, r.apply e = none

/-- No rule fires anywhere in `e`. -/
inductive Normal (rules : List PlainRule) : Expr → Prop
  | mk (e : Expr) (h : NoFire rules e) (hc : ∀ c ∈ children e, Normal rules c) : Normal rules e

theorem Normal.noFire {rules : List PlainRule} {e : Expr} (h : Normal rules e) : NoFire rules e := by
  cases h; assumption

theorem Normal.children {rules : List PlainRule} {e : Expr} (h : Normal rules e) : ∀ c ∈ children e, Normal rules c := by
  cases h; assumption

/-- Every child is normal: the hypothesis a rule's decrease proof may assume. -/
def ChildrenNormal (rules : List PlainRule) (e : Expr) : Prop := ∀ c ∈ children e, Normal rules c

theorem Normal.childrenNormal {rules : List PlainRule} {e : Expr} (h : Normal rules e) : ChildrenNormal rules e :=
  h.children

/-- A rule set with its termination proof under `μ`. -/
structure Ordered (rules : List PlainRule) : Prop where
  decreasing : ∀ r ∈ rules, ∀ e res, ChildrenNormal rules e → r.apply e = some res → res.error = none →
    MuLt (μ res.result) (μ e)

theorem fireP_spec (rules : List PlainRule) (e : Expr) : ∀ {r res}, fireP rules e = some (r, res) →
    r ∈ rules ∧ r.apply e = some res := by
  induction rules with
  | nil => intro _ _ h; simp [fireP] at h
  | cons r' rs ih =>
    intro r res h
    simp only [fireP] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, ‹_›⟩
    · obtain ⟨hm, ha⟩ := ih h; exact ⟨List.mem_cons_of_mem _ hm, ha⟩

theorem noFire_of_fireP_none (rules : List PlainRule) (e : Expr) (h : fireP rules e = none) : NoFire rules e := by
  induction rules with
  | nil => intro r hr; simp at hr
  | cons r' rs ih =>
    intro r hr
    simp only [fireP] at h
    split at h
    · simp at h
    · rcases List.mem_cons.mp hr with rfl | hm
      · assumption
      · exact ih h r hm

-- ---------------------------------------------------------------------------
-- μ is monotone in the children (lexicographically)
-- ---------------------------------------------------------------------------

theorem Expr.RelList.imp {R S : Expr → Expr → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l l' : List Expr}, RelList R l l' → RelList S l l'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h₁, h₂⟩ => ⟨h _ _ h₁, Expr.RelList.imp h h₂⟩

theorem Expr.RelList.and {R S : Expr → Expr → Prop} :
    ∀ {l l' : List Expr}, RelList R l l' → RelList S l l' → RelList (fun a b => R a b ∧ S a b) l l'
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h₁, h₂⟩, ⟨g₁, g₂⟩ => ⟨⟨h₁, g₁⟩, Expr.RelList.and h₂ g₂⟩

theorem Expr.RelList.mem_right {R : Expr → Expr → Prop} :
    ∀ {l l' : List Expr}, RelList R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _ :: _, _ :: _, ⟨h₁, h₂⟩, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h₁⟩
    · obtain ⟨b, hb, hr⟩ := Expr.RelList.mem_right h₂ a ha; exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem ML.le_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => M a ≤ M b) cs' cs → ML cs' ≤ ML cs
  | [], [], _ => Nat.le_refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [ML]; have := ML.le_of_rel hs; omega

theorem ML.eq_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => M a ≤ M b) cs' cs → ML cs' = ML cs →
    RelList (fun a b => M a = M b) cs' cs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩, heq => by
    simp only [ML] at heq; have := ML.le_of_rel hs
    exact ⟨by omega, ML.eq_of_rel hs (by omega)⟩

theorem sizeList_le_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => size a ≤ size b) cs' cs →
    sizeList cs' ≤ sizeList cs
  | [], [], _ => Nat.le_refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [sizeList]; have := sizeList_le_of_rel hs; omega

/-- `M` of a rebuilt node, monotone in the children. -/
theorem M.withChildren_le (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => M a ≤ M b) cs' cs) :
    M (withChildren e cs') ≤ M (withChildren e cs) := by
  have hlen' := RelList_length h
  cases e with
  | num _ | var _ => exact Nat.le_refl _
  | add _ =>
    simp only [withChildren]
    cases cs with
    | nil => cases cs' with | nil => exact Nat.le_refl _ | cons => simp at hlen'
    | cons c cs => cases cs' with
      | nil => simp at hlen'
      | cons c' cs' => rw [M.add_cons, M.add_cons]; exact ML.le_of_rel h
  | mul _ => simp only [withChildren, M.mul, hlen']; have := ML.le_of_rel h; omega
  | pow _ _ =>
    simp only [children, List.length_cons, List.length_nil] at hlen
    match cs, cs', hlen, hlen', h with
    | [b, x], [b', x'], _, _, ⟨hb, hx, _⟩ =>
      simp only [withChildren, M.pow]
      have := Nat.mul_le_mul (Nat.add_le_add_right hb 1) hx
      omega
  | fn f _ =>
    simp only [withChildren]
    by_cases hd : f = "diff" ∧ cs.length = 2
    · obtain ⟨rfl, hl⟩ := hd
      match cs, cs', hl, hlen', h with
      | [g, t], [g', t'], _, _, ⟨hg, ht, _⟩ =>
        rw [M.diff, M.diff]
        have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.add_le_add_right hg 3)
        omega
    · rw [M.fn f cs hd, M.fn f cs' (by rw [hlen']; exact hd)]
      have := ML.le_of_rel h; omega
  | matrix rows =>
    simp only [withChildren, M.matrix, MR.flatten]
    simp only [children] at hlen
    rw [flatten_regroup rows cs hlen, flatten_regroup rows cs' (hlen'.trans hlen)]
    have := ML.le_of_rel h; omega

/-- ... and strictly monotone: equal `M` on the rebuilt nodes forces equal `M` on every child. -/
theorem M.withChildren_eq (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => M a ≤ M b) cs' cs) (heq : M (withChildren e cs') = M (withChildren e cs)) :
    RelList (fun a b => M a = M b) cs' cs := by
  have hlen' := RelList_length h
  cases e with
  | num _ | var _ =>
    simp only [children, List.length_nil] at hlen
    match cs, cs', hlen, hlen' with
    | [], [], _, _ => trivial
  | add _ =>
    simp only [withChildren] at heq
    cases cs with
    | nil => cases cs' with | nil => trivial | cons => simp at hlen'
    | cons c cs => cases cs' with
      | nil => simp at hlen'
      | cons c' cs' => rw [M.add_cons, M.add_cons] at heq; exact ML.eq_of_rel h heq
  | mul _ => simp only [withChildren, M.mul, hlen'] at heq; exact ML.eq_of_rel h (by omega)
  | pow _ _ =>
    simp only [children, List.length_cons, List.length_nil] at hlen
    match cs, cs', hlen, hlen', h with
    | [b, x], [b', x'], _, _, ⟨hb, hx, _⟩ =>
      simp only [withChildren, M.pow] at heq
      have h1 := M.pos b; have h2 := M.pos x; have h3 := M.pos b'; have h4 := M.pos x'
      have p1 : 1 * 1 ≤ (M b' + 1) * M x' := Nat.mul_le_mul (by omega) h4
      have p2 : 1 * 1 ≤ (M b + 1) * M x := Nat.mul_le_mul (by omega) h2
      have heq' : (M b' + 1) * M x' = (M b + 1) * M x := by omega
      refine ⟨?_, ?_, trivial⟩
      · rcases Nat.lt_or_eq_of_le hb with hlt | hlt
        · exfalso
          have : (M b' + 1) * M x' ≤ (M b' + 1) * M x := Nat.mul_le_mul_left _ hx
          have : (M b' + 1) * M x < (M b + 1) * M x := Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.le_refl _) h2
          omega
        · exact hlt
      · rcases Nat.lt_or_eq_of_le hx with hlt | hlt
        · exfalso
          have : (M b' + 1) * M x' < (M b' + 1) * M x := Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) hlt (by omega)
          have : (M b' + 1) * M x ≤ (M b + 1) * M x := Nat.mul_le_mul_right _ (by omega)
          omega
        · exact hlt
  | fn f _ =>
    simp only [withChildren] at heq
    by_cases hd : f = "diff" ∧ cs.length = 2
    · obtain ⟨rfl, hl⟩ := hd
      match cs, cs', hl, hlen', h with
      | [g, t], [g', t'], _, _, ⟨hg, ht, _⟩ =>
        rw [M.diff, M.diff] at heq
        refine ⟨?_, ?_, trivial⟩
        · rcases Nat.lt_or_eq_of_le hg with hlt | hlt
          · exfalso; have := Nat.pow_lt_pow_right (a := 3) (by decide) (Nat.add_lt_add_right hlt 3); omega
          · exact hlt
        · have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.add_le_add_right hg 3); omega
    · rw [M.fn f cs hd, M.fn f cs' (by rw [hlen']; exact hd)] at heq
      exact ML.eq_of_rel h (by omega)
  | matrix rows =>
    simp only [withChildren, M.matrix, MR.flatten] at heq
    simp only [children] at hlen
    rw [flatten_regroup rows cs hlen, flatten_regroup rows cs' (hlen'.trans hlen)] at heq
    exact ML.eq_of_rel h (by omega)

theorem size_withChildren (e : Expr) (cs : List Expr) (hlen : cs.length = (children e).length) :
    size (withChildren e cs) = 1 + sizeList cs := by
  rw [size_eq, children_withChildren e cs hlen]

/-- Replacing the children by lexicographically smaller-or-equal ones makes the node
lexicographically smaller-or-equal. Tier by tier: a strict decrease in the first tier where some
child decreases; before that tier every child is equal. -/
theorem μ_withChildren_le (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => MuLe (μ a) (μ b)) cs' cs) :
    MuLe (μ (withChildren e cs')) (μ (withChildren e cs)) := by
  have hlen' := RelList_length h
  have hlen'' : cs'.length = (children e).length := hlen'.trans hlen
  have hE := fun (a b : Expr) (hab : MuLe (μ a) (μ b)) => (MuLe.elim hab)
  simp only [μ] at hE
  -- tier 1
  have t1 : RelList (fun a b => cmdCount a ≤ cmdCount b) cs' cs := h.imp fun a b hab => (hE a b hab).1
  have lit3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs →
      litOwn (withChildren e cs') ≤ litOwn (withChildren e cs) := by
    intro t3
    simp only [litOwn, hasLit_withChildren e cs hlen, hasLit_withChildren e cs' hlen'']
    split
    · split
      · exact Nat.le_refl _
      · rename_i h1 h2
        exfalso; apply h2
        rw [Bool.or_eq_true] at h1 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · right
          rw [hasLitList_iff] at h1 ⊢
          obtain ⟨a, ha, hl⟩ := h1
          obtain ⟨b, hb, hab⟩ := Expr.RelList.mem_right t3 a ha
          refine ⟨b, hb, hasLit_of_count_pos ?_⟩
          have hc : 0 < count litOwn a := by rw [count_eq]; simp only [litOwn, hl, ↓reduceIte]; omega
          exact Nat.lt_of_lt_of_le hc hab
    · exact Nat.zero_le _
  simp only [μ, cmdCount, d3Count, litCount, count_withChildren cmdOwn_head e _ hlen,
    count_withChildren cmdOwn_head e _ hlen'', count_withChildren d3Own_head e _ hlen,
    count_withChildren d3Own_head e _ hlen'',
    count_eq (e := withChildren e cs), count_eq (e := withChildren e cs'),
    children_withChildren e cs hlen, children_withChildren e cs' hlen'',
    size_withChildren e _ hlen, size_withChildren e _ hlen'']
  refine muLe_of (Nat.add_le_add_left (countList_le_of_rel _ t1) _) ?_ ?_ ?_ ?_
  · intro e1
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    exact Nat.add_le_add_left (countList_le_of_rel _ t2) _
  · intro e1 e2
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    exact Nat.add_le_add (lit3 t3) (countList_le_of_rel _ t3)
  · intro e1 e2 e3
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    have e3' := countList_eq_of_rel _ t3 (by have := lit3 t3; have := countList_le_of_rel _ t3; omega)
    have t4 : RelList (fun a b => M a ≤ M b) cs' cs :=
      (((h.and e1').and e2').and e3').imp fun a b ⟨⟨⟨hab, hc⟩, hd⟩, hl⟩ => (hE a b hab).2.2.2.1 hc hd hl
    exact M.withChildren_le e hlen t4
  · intro e1 e2 e3 e4
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    have e3' := countList_eq_of_rel _ t3 (by have := lit3 t3; have := countList_le_of_rel _ t3; omega)
    have t4 : RelList (fun a b => M a ≤ M b) cs' cs :=
      (((h.and e1').and e2').and e3').imp fun a b ⟨⟨⟨hab, hc⟩, hd⟩, hl⟩ => (hE a b hab).2.2.2.1 hc hd hl
    have e4' := M.withChildren_eq e hlen t4 e4
    have t5 : RelList (fun a b => size a ≤ size b) cs' cs :=
      ((((h.and e1').and e2').and e3').and e4').imp fun a b ⟨⟨⟨⟨hab, hc⟩, hd⟩, hl⟩, hm⟩ =>
        (hE a b hab).2.2.2.2 hc hd hl hm
    exact Nat.add_le_add_left (sizeList_le_of_rel t5) _

theorem children_canon_perm (e : Expr) : (children (canon e)).Perm (children e) := by
  cases e with
  | add es => exact List.mergeSort_perm es leAdd
  | mul es =>
    simp only [canon]; split
    · exact List.Perm.refl _
    · exact List.mergeSort_perm es leMul
  | _ => exact List.Perm.refl _

-- ---------------------------------------------------------------------------
-- The rewriter
-- ---------------------------------------------------------------------------

structure TState where
  steps : Array RawStep := #[]
  error : Option String := none

/-- What `normAtT` promises about its result: no heavier than the input, and normal unless a rule
refused. -/
def Promise (rules : List PlainRule) (e : Expr) (st : TState) (r : Expr × TState) : Prop :=
  MuLe (μ r.1) (μ e) ∧ (r.2.error = none → Normal rules r.1) ∧ (r.2.error = none → st.error = none)

def PromiseList (rules : List PlainRule) (cs : List Expr) (st : TState) (r : List Expr × TState) : Prop :=
  RelList (fun a b => MuLe (μ a) (μ b)) r.1 cs ∧ (r.2.error = none → ∀ c ∈ r.1, Normal rules c) ∧
    (r.2.error = none → st.error = none)

mutual
  def normAtT (rules : List PlainRule) (ord : Ordered rules) (e : Expr) (path : Path) (st : TState) :
      {r : Expr × TState // Promise rules e st r} :=
    match normChildrenT rules ord e (children e) (fun _ h => h) path 0 st with
    | ⟨(cs, st₀), hcs⟩ =>
      have hlen : cs.length = (children e).length := RelList_length hcs.1
      let e₀ := withChildren e cs
      let e₁ := canon e₀
      let st₁ := if equal e₁ e₀ then st₀ else { st₀ with steps := st₀.steps.push ⟨"simp.sort", true, "commutativity", path, e₁, none⟩ }
      have hst₁ : st₁.error = st₀.error := by simp only [st₁]; split <;> rfl
      have h₁ : MuLe (μ e₁) (μ e) := by
        have := μ_withChildren_le e (cs' := cs) (cs := children e) rfl hcs.1
        rw [withChildren_children'] at this
        simp only [e₁, μ_canon]; exact this
      have hnorm : st₀.error = none → ChildrenNormal rules e₁ := fun herr c hc => by
        have hc' := (children_canon_perm e₀).mem_iff.mp hc
        rw [children_withChildren e cs hlen] at hc'
        exact hcs.2.1 herr c hc'
      if herr : st₁.error.isSome then
        ⟨(e₁, st₁), h₁, fun h => by have h' : st₁.error = none := h; simp [h'] at herr,
          fun h => by have h' : st₁.error = none := h; simp [h'] at herr⟩ else
      match hf : fireP rules e₁ with
      | none => ⟨(e₁, st₁), h₁, fun h => ⟨e₁, noFire_of_fireP_none rules e₁ hf, hnorm (hst₁ ▸ h)⟩,
          fun h => hcs.2.2 (hst₁ ▸ h)⟩
      | some (rule, res) =>
        if hres : res.error.isSome then
          ⟨(e₁, { st₁ with error := res.error }), h₁, fun h => by have h' : res.error = none := h; simp [h'] at hres,
            fun h => by have h' : res.error = none := h; simp [h'] at hres⟩ else
        have hnone : st₀.error = none := by
          rw [← hst₁]; cases h : st₁.error with | none => rfl | some => simp [h] at herr
        have hdec : MuLt (μ res.result) (μ e₁) :=
          ord.decreasing rule (fireP_spec rules e₁ hf).1 e₁ res (hnorm hnone) (fireP_spec rules e₁ hf).2
            (by cases h : res.error with | none => rfl | some => simp [h] at hres)
        let st₂ : TState := { st₁ with steps := st₁.steps.push ⟨rule.name, rule.silent, res.explanation, path, res.result, res.sub⟩ }
        have hst₂ : st₂.error = st₀.error := hst₁
        match normAtT rules ord res.result path st₂ with
        | ⟨r, hr⟩ => ⟨r, hr.1.trans (Or.inl (hdec.trans_le h₁)), hr.2.1, fun h => hcs.2.2 (hst₂ ▸ hr.2.2 h)⟩
  termination_by (μ e, 1, 0)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ Nat.zero_lt_one)
    · exact Prod.Lex.left _ _ (hdec.trans_le h₁)

  def normChildrenT (rules : List PlainRule) (ord : Ordered rules) (parent : Expr) (cs : List Expr)
      (hsub : ∀ c ∈ cs, c ∈ children parent) (path : Path) (i : Nat) (st : TState) :
      {r : List Expr × TState // PromiseList rules cs st r} :=
    match cs with
    | [] => ⟨([], st), trivial, fun _ _ h => by simp at h, fun h => h⟩
    | c :: cs' =>
      match normAtT rules ord c (path ++ [i]) st with
      | ⟨(c', st₁), hc⟩ =>
        match normChildrenT rules ord parent cs' (fun d hd => hsub d (List.mem_cons_of_mem _ hd)) path (i + 1) st₁ with
        | ⟨(cs'', st₂), hcs⟩ =>
          ⟨(c' :: cs'', st₂), ⟨hc.1, hcs.1⟩, fun herr d hd => by
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc.2.1 (hcs.2.2 herr)
            · exact hcs.2.1 herr d hd, fun herr => hc.2.2 (hcs.2.2 herr)⟩
  termination_by (μ parent, 0, cs.length)
  decreasing_by
    · exact Prod.Lex.left _ _ (μ_child_lt (hsub c List.mem_cons_self))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))
end

/-- Normalize under an ordered rule set. Fails only if a rule refused. -/
def normalizeT (rules : List PlainRule) (ord : Ordered rules) (e : Expr) : TraceM (Except String Expr) := do
  let ⟨(out, st), _⟩ := normAtT rules ord e [] {}
  match st.error with
  | some msg => pure (.error msg)
  | none =>
    let (steps, _) := buildSteps e st.steps
    modify (· ++ steps)
    pure (.ok out)

end MathEngine
