import MathEngine.Systems
/-!
# What is proved about the systems world's search

`exploreWith` is breadth-first search along an arbitrary successor function `succ`, which may fail
(a system's action can leave a variable's domain). `Reach succ inits` is the set of states reachable
from `inits` along successful steps. When the search returns a graph:

- `exploreWith_complete`: every reachable state is among its states;
- `exploreWith_sound`: every one of its states is reachable;
- `exploreWith_nodup`: each appears once, so the number of states is the number of reachable states;
- `exploreWith_edges_complete`: every transition out of a found state is an edge;
- `exploreWith_edges_sound`: every edge is a transition;
- `exploreWith_inits`: every initial state has an index.

The successor function is a parameter, so nothing here depends on how a guard or an update is
evaluated: those are the definitions of the system's meaning. `System.explore_spec` reads the
theorems for a system, and `allStates_mem` says the enumeration `sys.inductive` checks is every
assignment of the variables' domains.
-/
namespace MathEngine
namespace Sys

/-- The states reachable from `inits` by steps along `succ`. -/
inductive Reach {α : Type} (succ : α → Except String (List (String × α))) (inits : List α) : α → Prop
  | init {s : α} : s ∈ inits → Reach succ inits s
  | step {s t : α} {a : String} {out : List (String × α)} :
      Reach succ inits s → succ s = .ok out → (a, t) ∈ out → Reach succ inits t

namespace Search
variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α]

/-- The index finds exactly the states, at their positions. -/
def Indexed (sr : Search α) : Prop := ∀ (s : α) (j : Nat), sr.index[s]? = some j ↔ sr.states[j]? = some s

/-- What the search keeps true: the index is right, every state found is reachable, every edge is
a transition. -/
structure Good (succ : α → Except String (List (String × α))) (inits : List α) (sr : Search α) : Prop where
  indexed : Indexed sr
  reach : ∀ (j : Nat) (s : α), sr.states[j]? = some s → Reach succ inits s
  edges : ∀ e ∈ sr.edges, ∃ s t out, sr.states[e.1]? = some s ∧ sr.states[e.2.2]? = some t ∧
    succ s = .ok out ∧ (e.2.1, t) ∈ out

/-- The states below `i` have been expanded: each one's successors are found, with their edges. -/
def Closed (succ : α → Except String (List (String × α))) (i : Nat) (sr : Search α) : Prop :=
  ∀ (k : Nat) (s : α), k < i → sr.states[k]? = some s → ∃ out, succ s = .ok out ∧
    ∀ p ∈ out, ∃ j : Nat, sr.states[j]? = some p.2 ∧ (k, p.1, j) ∈ sr.edges

/-- `sr'` extends `sr`: no state moves and no edge is lost. -/
def Extends (sr sr' : Search α) : Prop :=
  (∀ (j : Nat) (s : α), sr.states[j]? = some s → sr'.states[j]? = some s) ∧ (∀ e ∈ sr.edges, e ∈ sr'.edges)

omit [LawfulBEq α] in
theorem Extends.refl (sr : Search α) : Extends sr sr := ⟨fun _ _ h => h, fun _ h => h⟩

omit [LawfulBEq α] in
theorem Extends.trans {a b c : Search α} (h₁ : Extends a b) (h₂ : Extends b c) : Extends a c :=
  ⟨fun j s h => h₂.1 j s (h₁.1 j s h), fun e h => h₂.2 e (h₁.2 e h)⟩

omit [BEq α] [Hashable α] [LawfulBEq α] in
theorem lt_of_getElem?_eq_some {xs : Array α} {j : Nat} {s : α} (h : xs[j]? = some s) : j < xs.size := by
  rcases Nat.lt_or_ge j xs.size with hj | hj
  · exact hj
  · rw [Array.getElem?_eq_none hj] at h
    cases h

omit [BEq α] [Hashable α] [LawfulBEq α] in
theorem getElem?_push_of_some {xs : Array α} {x s : α} {j : Nat} (h : xs[j]? = some s) :
    (xs.push x)[j]? = some s := by
  have := lt_of_getElem?_eq_some h
  rw [Array.getElem?_push]
  simp [show j ≠ xs.size by omega, h]

theorem indexed_empty : Indexed (empty : Search α) := by
  intro s j
  simp [empty]

/-- Adding a state the index does not know keeps the index right. -/
theorem indexed_add {sr : Search α} (hI : Indexed sr) {s : α} (hs : sr.index[s]? = none)
    (p : Option (Nat × String)) : Indexed (sr.add s p) := by
  intro t j
  simp only [add, Std.HashMap.getElem?_insert, Array.getElem?_push]
  by_cases hst : s = t
  · subst hst
    simp only [beq_self_eq_true, ite_true, Option.some.injEq]
    constructor
    · intro h; subst h; simp
    · intro h
      split at h
      · omega
      · exact absurd ((hI s j).mpr h) (by rw [hs]; simp)
  · have hb : (s == t) = false := by simpa using hst
    simp only [hb, Bool.false_eq_true, ite_false]
    rw [hI t j]
    constructor
    · intro h
      have := lt_of_getElem?_eq_some h
      simp [show j ≠ sr.states.size by omega, h]
    · intro h
      split at h
      · cases h; exact absurd rfl hst
      · exact h

omit [LawfulBEq α] in
theorem extends_add (sr : Search α) (s : α) (p : Option (Nat × String)) : Extends sr (sr.add s p) :=
  ⟨fun _ _ h => getElem?_push_of_some h, fun _ h => h⟩

/-- The initial states: the index stays right, and each state found is initial. -/
theorem addInits_good (succ : α → Except String (List (String × α))) (inits : List α) :
    ∀ (l : List α) (sr : Search α), (∀ s ∈ l, s ∈ inits) → Good succ inits sr → sr.edges = #[] →
      Good succ inits (l.foldl addInit sr) ∧ (l.foldl addInit sr).edges = #[] ∧
      Extends sr (l.foldl addInit sr) ∧ ∀ s ∈ l, ∃ j : Nat, (l.foldl addInit sr).states[j]? = some s := by
  intro l
  induction l with
  | nil => intro sr _ hG hE; exact ⟨hG, hE, Extends.refl _, by simp⟩
  | cons x xs ih =>
    intro sr hl hG hE
    simp only [List.foldl_cons]
    have hx : ∃ j : Nat, (sr.addInit x).states[j]? = some x := by
      unfold addInit
      split
      · rename_i hc
        rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hc
        obtain ⟨j, hj⟩ := hc
        exact ⟨j, (hG.indexed x j).mp hj⟩
      · exact ⟨sr.states.size, by simp [add]⟩
    have hG' : Good succ inits (sr.addInit x) ∧ (sr.addInit x).edges = #[] ∧ Extends sr (sr.addInit x) := by
      unfold addInit
      split
      · exact ⟨hG, hE, Extends.refl _⟩
      · rename_i hc
        have hnone : sr.index[x]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          simpa using hc
        refine ⟨⟨indexed_add hG.indexed hnone none, ?_, ?_⟩, hE, extends_add _ _ _⟩
        · intro j s h
          simp only [add, Array.getElem?_push] at h
          split at h
          · cases h; exact Reach.init (hl x (by simp))
          · exact hG.reach j s h
        · intro e he
          simp [add, hE] at he
    obtain ⟨hG₁, hE₁, hX₁⟩ := hG'
    obtain ⟨hG₂, hE₂, hX₂, hmem⟩ := ih (sr.addInit x) (fun s hs => hl s (by simp [hs])) hG₁ hE₁
    refine ⟨hG₂, hE₂, hX₁.trans hX₂, ?_⟩
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · obtain ⟨j, hj⟩ := hx
      exact ⟨j, hX₂.1 j s hj⟩
    · exact hmem s hs

/-- Visiting one successor of a state already found. -/
theorem visit_good {succ : α → Except String (List (String × α))} {inits : List α} {limit i : Nat}
    {sr sr' : Search α} {s : α} {out : List (String × α)} {p : String × α}
    (hG : Good succ inits sr) (hi : sr.states[i]? = some s) (hs : succ s = .ok out) (hp : p ∈ out)
    (h : visit limit i sr p = .ok sr') :
    Good succ inits sr' ∧ Extends sr sr' ∧ ∃ j : Nat, sr'.states[j]? = some p.2 ∧ (i, p.1, j) ∈ sr'.edges := by
  have hreach : Reach succ inits p.2 := Reach.step (hG.reach i s hi) hs hp
  unfold visit at h
  split at h
  · rename_i j hj
    cases h
    have hjs := (hG.indexed p.2 j).mp hj
    refine ⟨⟨hG.indexed, hG.reach, ?_⟩, ⟨fun _ _ h => h, fun e he => by simp [he]⟩, j, hjs, by simp⟩
    intro e he
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hG.edges e he
    · exact ⟨s, p.2, out, hi, hjs, hs, hp⟩
  · rename_i hj
    split at h
    · cases h
    · cases h
      have hX := extends_add sr p.2 (some (i, p.1))
      refine ⟨⟨indexed_add hG.indexed hj (some (i, p.1)), ?_, ?_⟩, ⟨hX.1, fun e he => by simp [he]⟩, sr.states.size,
        by simp [add], by simp⟩
      · intro j t ht
        simp only [add, Array.getElem?_push] at ht
        split at ht
        · cases ht; exact hreach
        · exact hG.reach j t ht
      · intro e he
        simp only [Array.mem_push] at he
        rcases he with he | rfl
        · obtain ⟨s', t', out', h1, h2, h3, h4⟩ := hG.edges e he
          exact ⟨s', t', out', hX.1 _ _ h1, hX.1 _ _ h2, h3, h4⟩
        · exact ⟨s, p.2, out, hX.1 _ _ hi, by simp [add], hs, hp⟩

/-- Visiting every successor of state `i`, in order. -/
theorem visitAll_good {succ : α → Except String (List (String × α))} {inits : List α} {limit i : Nat}
    {s : α} {out : List (String × α)} (hs : succ s = .ok out) :
    ∀ (l : List (String × α)) (sr sr' : Search α), (∀ p ∈ l, p ∈ out) → Good succ inits sr →
      sr.states[i]? = some s → l.foldlM (visit limit i) sr = .ok sr' →
      Good succ inits sr' ∧ Extends sr sr' ∧ ∀ p ∈ l, ∃ j : Nat, sr'.states[j]? = some p.2 ∧ (i, p.1, j) ∈ sr'.edges := by
  intro l
  induction l with
  | nil =>
    intro sr sr' _ hG _ h
    cases h
    exact ⟨hG, Extends.refl _, by simp⟩
  | cons p ps ih =>
    intro sr sr' hl hG hi h
    simp only [List.foldlM_cons] at h
    cases hv : visit limit i sr p with
    | error e => rw [hv] at h; cases h
    | ok sr₁ =>
      rw [hv] at h
      obtain ⟨hG₁, hX₁, hp₁⟩ := visit_good hG hi hs (hl p (by simp)) hv
      obtain ⟨hG₂, hX₂, hps⟩ := ih sr₁ sr' (fun q hq => hl q (by simp [hq])) hG₁ (hX₁.1 _ _ hi) h
      refine ⟨hG₂, hX₁.trans hX₂, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · obtain ⟨j, hj, he⟩ := hp₁
        exact ⟨j, hX₂.1 _ _ hj, hX₂.2 _ he⟩
      · exact hps q hq

omit [LawfulBEq α] in
theorem closed_mono {succ : α → Except String (List (String × α))} {i : Nat} {sr sr' : Search α}
    (hC : Closed succ i sr) (hi : i ≤ sr.states.size) (hX : Extends sr sr') : Closed succ i sr' := by
  intro k s hk hs
  have hs₀ : sr.states[k]? = some sr.states[k] := Array.getElem?_eq_getElem (by omega)
  have : s = sr.states[k] := by
    have := hX.1 _ _ hs₀
    rw [hs] at this
    exact Option.some.inj this
  subst this
  obtain ⟨out, hout, hall⟩ := hC k _ hk hs₀
  refine ⟨out, hout, fun p hp => ?_⟩
  obtain ⟨j, hj, he⟩ := hall p hp
  exact ⟨j, hX.1 _ _ hj, hX.2 _ he⟩

/-- The search loop: from a good search whose states below `i` are expanded, a returned search is
good, extends it, and has every state expanded. -/
theorem run_good {succ : α → Except String (List (String × α))} {inits : List α} {limit : Nat} :
    ∀ (fuel i : Nat) (sr sr' : Search α), Good succ inits sr → Closed succ i sr → i ≤ sr.states.size →
      run succ limit fuel i sr = .ok sr' →
      Good succ inits sr' ∧ Extends sr sr' ∧ Closed succ sr'.states.size sr' := by
  intro fuel
  induction fuel with
  | zero =>
    intro i sr sr' hG hC hi h
    simp only [run] at h
    split at h
    · cases h
    · cases h
      exact ⟨hG, Extends.refl _, by rwa [show i = sr.states.size by omega] at hC⟩
  | succ n ih =>
    intro i sr sr' hG hC hi h
    simp only [run] at h
    split at h
    · rename_i hlt
      have hsi : sr.states[i]? = some sr.states[i] := Array.getElem?_eq_getElem hlt
      cases hs : succ sr.states[i] with
      | error e => rw [hs] at h; cases h
      | ok out =>
        rw [hs] at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i sr₁ hf
          obtain ⟨hG₁, hX₁, hall⟩ := visitAll_good hs out sr sr₁ (fun _ h => h) hG hsi hf
          have hC₁ : Closed succ (i + 1) sr₁ := by
            intro k s hk hks
            by_cases hki : k < i
            · exact closed_mono hC hi hX₁ k s hki hks
            · have hk : k = i := by omega
              subst hk
              have : s = sr.states[k] := by
                have := hX₁.1 _ _ hsi
                rw [hks] at this
                exact Option.some.inj this
              subst this
              exact ⟨out, hs, hall⟩
          have hi₁ : i + 1 ≤ sr₁.states.size := by
            have := lt_of_getElem?_eq_some (hX₁.1 _ _ hsi)
            omega
          obtain ⟨hG₂, hX₂, hC₂⟩ := ih (i + 1) sr₁ sr' hG₁ hC₁ hi₁ h
          exact ⟨hG₂, hX₁.trans hX₂, hC₂⟩
    · cases h
      exact ⟨hG, Extends.refl _, by rwa [show i = sr.states.size by omega] at hC⟩

end Search

open Search in
/-- What a finished search returns: a good search, with every state expanded, holding the initial
states. -/
theorem exploreWith_spec {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    {succ : α → Except String (List (String × α))} {inits : List α} {limit : Nat} {sr : Search α}
    (h : exploreWith succ inits limit = .ok sr) :
    Good succ inits sr ∧ Closed succ sr.states.size sr ∧ ∀ s ∈ inits, ∃ j : Nat, sr.states[j]? = some s := by
  have hG₀ : Good succ inits (empty : Search α) :=
    ⟨indexed_empty, fun j s h => by simp [empty] at h, fun e he => by simp [empty] at he⟩
  obtain ⟨hG₁, -, -, hmem⟩ := addInits_good succ inits inits empty (fun _ h => h) hG₀ rfl
  have hC₁ : Closed succ 0 (inits.foldl addInit empty) := fun _ _ hk => absurd hk (by omega)
  obtain ⟨hG, hX, hC⟩ := run_good (limit + 1) 0 _ sr hG₁ hC₁ (by omega) h
  exact ⟨hG, hC, fun s hs => let ⟨j, hj⟩ := hmem s hs; ⟨j, hX.1 _ _ hj⟩⟩

section
variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
  {succ : α → Except String (List (String × α))} {inits : List α} {limit : Nat} {sr : Search α}

/-- **Every reachable state is found.** -/
theorem exploreWith_complete (h : exploreWith succ inits limit = .ok sr) {t : α}
    (ht : Reach succ inits t) : ∃ j : Nat, sr.states[j]? = some t := by
  obtain ⟨-, hC, hinit⟩ := exploreWith_spec h
  induction ht with
  | init hs => exact hinit _ hs
  | step _ hs hp ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨out', hout', hall⟩ := hC j _ (Search.lt_of_getElem?_eq_some hj) hj
    rw [hs] at hout'
    cases hout'
    obtain ⟨k, hk, -⟩ := hall _ hp
    exact ⟨k, hk⟩

/-- **Every state found is reachable.** -/
theorem exploreWith_sound (h : exploreWith succ inits limit = .ok sr) {j : Nat} {s : α}
    (hs : sr.states[j]? = some s) : Reach succ inits s :=
  (exploreWith_spec h).1.reach j s hs

/-- **Each state is found once**, so the count of states is the count of reachable states. -/
theorem exploreWith_nodup (h : exploreWith succ inits limit = .ok sr) {j k : Nat} {s : α}
    (hj : sr.states[j]? = some s) (hk : sr.states[k]? = some s) : j = k := by
  have hI := (exploreWith_spec h).1.indexed
  have h₁ := (hI s j).mpr hj
  have h₂ := (hI s k).mpr hk
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- **Every transition out of a state found is an edge.** -/
theorem exploreWith_edges_complete (h : exploreWith succ inits limit = .ok sr) {j : Nat} {s : α}
    (hs : sr.states[j]? = some s) {out : List (String × α)} (hout : succ s = .ok out) {a : String} {t : α}
    (hp : (a, t) ∈ out) : ∃ k : Nat, sr.states[k]? = some t ∧ (j, a, k) ∈ sr.edges := by
  obtain ⟨out', hout', hall⟩ := (exploreWith_spec h).2.1 j s (Search.lt_of_getElem?_eq_some hs) hs
  rw [hout] at hout'
  cases hout'
  exact hall _ hp

/-- **Every edge is a transition.** -/
theorem exploreWith_edges_sound (h : exploreWith succ inits limit = .ok sr) {e : Nat × String × Nat}
    (he : e ∈ sr.edges) : ∃ s t out, sr.states[e.1]? = some s ∧ sr.states[e.2.2]? = some t ∧
      succ s = .ok out ∧ (e.2.1, t) ∈ out :=
  (exploreWith_spec h).1.edges e he

/-- **Every initial state is indexed**, so the graph's initial states are all of them. -/
theorem exploreWith_inits (h : exploreWith succ inits limit = .ok sr) {s : α} (hs : s ∈ inits) :
    ∃ j : Nat, sr.index[s]? = some j ∧ sr.states[j]? = some s := by
  obtain ⟨hG, -, hinit⟩ := exploreWith_spec h
  obtain ⟨j, hj⟩ := hinit s hs
  exact ⟨j, (hG.indexed s j).mpr hj, hj⟩

end


/-! ## For a system -/

/-- A state gives each variable, in order, a value of its domain. -/
def Assigns : List Var → State → Prop
  | [], [] => True
  | v :: vs, x :: xs => x ∈ v.dom ∧ Assigns vs xs
  | _, _ => False

/-- The assignments `allStates` enumerates, before the size check. -/
theorem mem_assignments : ∀ (vs : List Var) (s : State),
    s ∈ vs.foldr (fun v acc => v.dom.flatMap fun x => acc.map (x :: ·)) [[]] ↔
      Assigns vs s
  | [], s => by cases s <;> simp [Assigns]
  | v :: vs, s => by
    simp only [List.foldr_cons, List.mem_flatMap, List.mem_map]
    cases s with
    | nil => simp [Assigns]
    | cons x xs =>
      simp only [Assigns, List.cons.injEq]
      constructor
      · rintro ⟨y, hy, ys, hys, rfl, rfl⟩
        exact ⟨hy, (mem_assignments vs ys).mp hys⟩
      · rintro ⟨hx, hxs⟩
        exact ⟨x, hx, xs, (mem_assignments vs xs).mpr hxs, rfl, rfl⟩

/-- **`allStates` is every assignment**: a state is enumerated exactly when it gives each variable a
value of its domain. `sys.inductive` checks every one of them. -/
theorem allStates_mem {S : System} {limit : Nat} {all : List State} (h : S.allStates limit = .ok all)
    (s : State) : s ∈ all ↔ Assigns S.vars s := by
  simp only [System.allStates] at h
  split at h
  · cases h
  · cases h
    exact mem_assignments S.vars s

/-- A system's search is `exploreWith` from its initial states, along its successor function. -/
theorem System.explore_spec {S : System} {limit : Nat} {G : Graph} (h : S.explore limit = .ok G) :
    ∃ inits sr, S.initStates = .ok inits ∧ exploreWith S.successors inits limit = .ok sr ∧
      G.states = sr.states ∧ G.edges = sr.edges.toList ∧ G.inits = inits.filterMap (sr.index[·]?) := by
  simp only [System.explore, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i inits hinits
    split at h
    · cases h
    · simp only [pure, Except.pure] at h
      split at h
      · cases h
      · rename_i sr hsr
        cases h
        exact ⟨inits, sr, hinits, hsr, rfl, rfl, rfl⟩

section
variable {S : System} {limit : Nat} {G : Graph}

/-- **`sys.reach`, `sys.invariant`, `sys.unreachable`: the graph's states are exactly the reachable
ones**, each once. -/
theorem System.explore_states (h : S.explore limit = .ok G) :
    ∃ inits, S.initStates = .ok inits ∧
      (∀ t, Reach S.successors inits t ↔ ∃ j : Nat, G.states[j]? = some t) ∧
      (∀ (j k : Nat) (t : State), G.states[j]? = some t → G.states[k]? = some t → j = k) := by
  obtain ⟨inits, sr, hi, hsr, hs, -, -⟩ := System.explore_spec h
  refine ⟨inits, hi, fun t => ⟨fun ht => ?_, fun ⟨j, hj⟩ => ?_⟩, fun j k t hj hk => ?_⟩
  · rw [hs]; exact exploreWith_complete hsr ht
  · rw [hs] at hj; exact exploreWith_sound hsr hj
  · rw [hs] at hj hk; exact exploreWith_nodup hsr hj hk

/-- **`sys.refines`: the graph's edges are exactly the transitions between reachable states**, and its
initial indices are every initial state. -/
theorem System.explore_edges (h : S.explore limit = .ok G) :
    ∃ inits, S.initStates = .ok inits ∧
      (∀ (j : Nat) (s : State) out a t, G.states[j]? = some s → S.successors s = .ok out → (a, t) ∈ out →
        ∃ k : Nat, G.states[k]? = some t ∧ (j, a, k) ∈ G.edges) ∧
      (∀ e ∈ G.edges, ∃ s t out, G.states[e.1]? = some s ∧ G.states[e.2.2]? = some t ∧
        S.successors s = .ok out ∧ (e.2.1, t) ∈ out) ∧
      (∀ s ∈ inits, ∃ j ∈ G.inits, G.states[j]? = some s) := by
  obtain ⟨inits, sr, hi, hsr, hs, he, hin⟩ := System.explore_spec h
  refine ⟨inits, hi, ?_, ?_, ?_⟩
  · intro j s out a t hj hout hp
    rw [hs] at hj ⊢
    simp only [he, Array.mem_toList_iff]
    exact exploreWith_edges_complete hsr hj hout hp
  · intro e hmem
    simp only [he, Array.mem_toList_iff] at hmem
    rw [hs]
    exact exploreWith_edges_sound hsr hmem
  · intro s hmem
    obtain ⟨j, hidx, hj⟩ := exploreWith_inits hsr hmem
    refine ⟨j, ?_, by rw [hs]; exact hj⟩
    rw [hin, List.mem_filterMap]
    exact ⟨s, hmem, hidx⟩

/-- **`sys.deadlock`: no deadlock is missed.** When every state of the graph has an outgoing edge,
every reachable state has an enabled action. -/
theorem System.no_deadlock (h : S.explore limit = .ok G)
    (hall : ∀ j : Nat, j < G.states.size → ∃ a k, (j, a, k) ∈ G.edges) :
    ∃ inits, S.initStates = .ok inits ∧
      ∀ s, Reach S.successors inits s → ∃ out, S.successors s = .ok out ∧ out ≠ [] := by
  obtain ⟨inits, hi, hreach, -⟩ := System.explore_states h
  obtain ⟨inits', hi', -, hsound, -⟩ := System.explore_edges h
  rw [hi] at hi'
  cases hi'
  refine ⟨inits, hi, fun s hs => ?_⟩
  obtain ⟨j, hj⟩ := (hreach s).mp hs
  obtain ⟨a, k, hjk⟩ := hall j (Search.lt_of_getElem?_eq_some hj)
  obtain ⟨s', t, out, h₁, -, hout, hp⟩ := hsound _ hjk
  rw [hj] at h₁
  cases h₁
  exact ⟨out, hout, List.ne_nil_of_mem hp⟩

end

end Sys
end MathEngine
