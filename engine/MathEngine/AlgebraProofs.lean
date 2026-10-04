import MathEngine.Algebra
/-!
# What is proved about finite algebra

- **The checks decide the laws.** When a search finds no failure, the law holds for every element of
  the set: associativity (`assocFailure_none`), commutativity (`commFailure_none`), idempotence
  (`idemFailure_none`), distributivity (`distribFailure_none`), the Galois condition
  (`galoisFailure_none`), the three closure-operator conditions (`closureOpFailure_none`), monotonicity
  between two posets (`monotoneFailure2_none`), and "no flow down" (`flowFailure_none`).
- **A semilattice is an order** (`semilattice_order`): for an associative, commutative, idempotent
  operation closed on its set (a table's entries are checked to be in the set when it is made),
  `x ≤ y ⇔ x · y = y` is reflexive, antisymmetric and transitive, and `x · y` is the least upper bound
  of `x` and `y`. So `order` draws a partial order in which the operation is the join.
- **The concept lattice is all the concepts** (`concepts_complete`, `concepts_sound`): every pair
  `concepts` lists is a formal concept (its objects are exactly those with all its attributes, its
  attributes exactly those all its objects share), and every concept is listed. The extents are built
  by intersecting attribute extents one attribute at a time, which reaches the extent of every set of
  attributes (`extents_complete`).
-/
namespace MathEngine
namespace Ord

theorem mem_allPairs {xs : List String} {x y : String} : (x, y) ∈ allPairs xs ↔ x ∈ xs ∧ y ∈ xs := by
  simp [allPairs]

theorem mem_allTriples {xs : List String} {x y z : String} :
    (x, y, z) ∈ allTriples xs ↔ x ∈ xs ∧ y ∈ xs ∧ z ∈ xs := by
  simp only [allTriples, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨hx, hy, hz⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, rfl, rfl⟩

/-! ## The laws of an operation -/

theorem assocFailure_none (o : Op) (h : assocFailure o = none) :
    ∀ x ∈ o.elems, ∀ y ∈ o.elems, ∀ z ∈ o.elems, o.ap (o.ap x y) z = o.ap x (o.ap y z) := by
  intro x hx y hy z hz
  have := List.find?_eq_none.mp h (x, y, z) (mem_allTriples.mpr ⟨hx, hy, hz⟩)
  simpa using this

theorem commFailure_none (o : Op) (h : commFailure o = none) :
    ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y = o.ap y x := by
  intro x hx y hy
  have := List.find?_eq_none.mp h (x, y) (mem_allPairs.mpr ⟨hx, hy⟩)
  simpa using this

theorem idemFailure_none (o : Op) (h : idemFailure o = none) : ∀ x ∈ o.elems, o.ap x x = x := by
  intro x hx
  have := List.find?_eq_none.mp h x hx
  simpa using this

/-- An operation whose table stays in its set, with the three laws on it. -/
structure IsSemilattice (o : Op) : Prop where
  closed : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y ∈ o.elems
  assoc : ∀ x ∈ o.elems, ∀ y ∈ o.elems, ∀ z ∈ o.elems, o.ap (o.ap x y) z = o.ap x (o.ap y z)
  comm : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y = o.ap y x
  idem : ∀ x ∈ o.elems, o.ap x x = x

/-- The three searches finding nothing, on a closed table, make a semilattice. -/
theorem isSemilattice_of_none (o : Op) (hc : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y ∈ o.elems)
    (ha : assocFailure o = none) (hm : commFailure o = none) (hi : idemFailure o = none) : IsSemilattice o :=
  ⟨hc, assocFailure_none o ha, commFailure_none o hm, idemFailure_none o hi⟩

theorem order_rel (o : Op) (x y : String) :
    o.order.rel x y = true ↔ x ∈ o.elems ∧ y ∈ o.elems ∧ o.ap x y = y := by
  rw [Poset.rel_eq, List.contains_iff_mem]
  simp only [Op.order, Poset.of, List.mem_filter, mem_allPairs, beq_iff_eq, and_assoc]

/-- The order of a semilattice: a partial order in which `x · y` is the join. -/
theorem semilattice_order (o : Op) (hs : IsSemilattice o) :
    (∀ x ∈ o.elems, o.order.rel x x = true) ∧
    (∀ x y, o.order.rel x y = true → o.order.rel y x = true → x = y) ∧
    (∀ x y z, o.order.rel x y = true → o.order.rel y z = true → o.order.rel x z = true) ∧
    (∀ x ∈ o.elems, ∀ y ∈ o.elems, o.order.rel x (o.ap x y) = true ∧ o.order.rel y (o.ap x y) = true ∧
      ∀ u, o.order.rel x u = true → o.order.rel y u = true → o.order.rel (o.ap x y) u = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (order_rel o x x).mpr ⟨hx, hx, hs.idem x hx⟩
  · intro x y hxy hyx
    obtain ⟨hx, hy, e1⟩ := (order_rel o x y).mp hxy
    obtain ⟨_, _, e2⟩ := (order_rel o y x).mp hyx
    rw [← e2, hs.comm y hy x hx, e1]
  · intro x y z hxy hyz
    obtain ⟨hx, hy, e1⟩ := (order_rel o x y).mp hxy
    obtain ⟨_, hz, e2⟩ := (order_rel o y z).mp hyz
    refine (order_rel o x z).mpr ⟨hx, hz, ?_⟩
    rw [← e2, ← hs.assoc x hx y hy z hz, e1]
  · intro x hx y hy
    have hxy := hs.closed x hx y hy
    refine ⟨?_, ?_, ?_⟩
    · refine (order_rel o x (o.ap x y)).mpr ⟨hx, hxy, ?_⟩
      rw [← hs.assoc x hx x hx y hy, hs.idem x hx]
    · refine (order_rel o y (o.ap x y)).mpr ⟨hy, hxy, ?_⟩
      rw [hs.comm x hx y hy, ← hs.assoc y hy y hy x hx, hs.idem y hy]
    · intro u hxu hyu
      obtain ⟨_, hu, e1⟩ := (order_rel o x u).mp hxu
      obtain ⟨_, _, e2⟩ := (order_rel o y u).mp hyu
      refine (order_rel o (o.ap x y) u).mpr ⟨hxy, hu, ?_⟩
      rw [hs.assoc x hx y hy u hu, e2, e1]

/-! ## Lattice properties, maps, connections -/

theorem distribFailure_none (J M : Op) (h : distribFailure J M = none) :
    ∀ x ∈ J.elems, ∀ y ∈ J.elems, ∀ z ∈ J.elems, M.ap x (J.ap y z) = J.ap (M.ap x y) (M.ap x z) := by
  intro x hx y hy z hz
  have := List.find?_eq_none.mp h (x, y, z) (mem_allTriples.mpr ⟨hx, hy, hz⟩)
  simpa using this

theorem monotoneFailure2_none (P Q : Poset) (f : PMap) (h : monotoneFailure2 P Q f = none) :
    ∀ x y, (x, y) ∈ P.le → Q.rel (f.apply x) (f.apply y) = true := by
  intro x y hxy
  have := List.find?_eq_none.mp h (x, y) hxy
  simpa using this

theorem galoisFailure_none (P Q : Poset) (f g : PMap) (h : galoisFailure P Q f g = none) :
    ∀ x ∈ P.elems, ∀ y ∈ Q.elems, (Q.rel (f.apply x) y = true ↔ P.rel x (g.apply y) = true) := by
  intro x hx y hy
  have := List.find?_eq_none.mp h (x, y) (by simp [hx, hy])
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
  rw [this]

theorem closureOpFailure_none (P : Poset) (f : PMap) (h : closureOpFailure P f = none) :
    (∀ x ∈ P.elems, P.rel x (f.apply x) = true) ∧
    (∀ x y, (x, y) ∈ P.le → P.rel (f.apply x) (f.apply y) = true) ∧
    (∀ x ∈ P.elems, f.apply (f.apply x) = f.apply x) := by
  unfold closureOpFailure at h
  split at h
  · cases h
  · rename_i hext
    split at h
    · cases h
    · rename_i hmono
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have := List.find?_eq_none.mp hext x hx
        simpa using this
      · intro x y hxy
        have := List.find?_eq_none.mp hmono (x, y) hxy
        simpa using this
      · intro x hx
        simp only [Option.map_eq_none_iff] at h
        have := List.find?_eq_none.mp h x hx
        simpa using this

theorem flowFailure_none (P : Poset) (label : String → String) (R : Rel) (h : flowFailure P label R = none) :
    ∀ x y, (x, y) ∈ R.pairs → P.rel (label x) (label y) = true := by
  intro x y hxy
  have := List.find?_eq_none.mp h (x, y) hxy
  simpa using this

/-! ## Formal concepts -/

theorem filter_intersect (C : Ctx) (p : String → Bool) (a : String) :
    (C.objs.filter p).filter (fun x => (C.extentOf [a]).contains x) =
      C.objs.filter fun o => p o && C.has o a := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro o ho
  have : (C.extentOf [a]).contains o = C.has o a := by
    cases h : C.has o a
    · simp [Ctx.extentOf, h]
    · simp [Ctx.extentOf, ho, h]
  rw [this, Bool.and_comm]

/-- One attribute's round of `extents`. -/
def extentsStep (C : Ctx) (acc : List (List String)) (a : String) : List (List String) :=
  let e := C.extentOf [a]
  acc ++ ((acc.map (·.filter (e.contains ·))).filter (fun x => !acc.contains x)).eraseDups

theorem extents_eq (C : Ctx) : C.extents = C.attrs.foldl (extentsStep C) [C.objs] := rfl

theorem mem_extentsStep {C : Ctx} {acc : List (List String)} {a : String} {x : List String} :
    x ∈ extentsStep C acc a ↔ x ∈ acc ∨ ∃ y ∈ acc, x = y.filter ((C.extentOf [a]).contains ·) := by
  simp only [extentsStep, List.mem_append, List.mem_eraseDups, List.mem_filter, List.mem_map]
  constructor
  · rintro (h | ⟨⟨y, hy, rfl⟩, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · by_cases hin : y.filter ((C.extentOf [a]).contains ·) ∈ acc
      · exact Or.inl hin
      · exact Or.inr ⟨⟨y, hy, rfl⟩, by simpa using hin⟩

/-- What `extents` keeps true, attribute by attribute: it holds the extent of every set of attributes
seen so far, and nothing else. -/
theorem extents_fold (C : Ctx) : ∀ (as P : List String) (acc : List (List String)),
    (∀ a ∈ as, a ∈ C.attrs) → (∀ a ∈ P, a ∈ C.attrs) →
    (∀ B : List String, (∀ b ∈ B, b ∈ P) → C.extentOf B ∈ acc) →
    (∀ x ∈ acc, ∃ B : List String, (∀ b ∈ B, b ∈ C.attrs) ∧ x = C.extentOf B) →
    (∀ B : List String, (∀ b ∈ B, b ∈ P ++ as) → C.extentOf B ∈ as.foldl (extentsStep C) acc) ∧
    (∀ x ∈ as.foldl (extentsStep C) acc, ∃ B : List String, (∀ b ∈ B, b ∈ C.attrs) ∧ x = C.extentOf B)
  | [], P, acc, _, _, hc, hs => by simpa using ⟨hc, hs⟩
  | a :: as, P, acc, has, hP, hc, hs => by
    have ha : a ∈ C.attrs := has a (by simp)
    have hc' : ∀ B : List String, (∀ b ∈ B, b ∈ P ++ [a]) → C.extentOf B ∈ extentsStep C acc a := by
      intro B hB
      obtain ⟨B', hB'def⟩ : ∃ B', B' = B.filter (· != a) := ⟨_, rfl⟩
      have hB' : ∀ b ∈ B', b ∈ P := by
        intro b hb
        simp only [hB'def, List.mem_filter, bne_iff_ne, ne_eq] at hb
        have := hB b hb.1
        simp only [List.mem_append, List.mem_singleton] at this
        exact this.resolve_right hb.2
      by_cases haB : a ∈ B
      · refine mem_extentsStep.mpr (Or.inr ⟨C.extentOf B', hc B' hB', ?_⟩)
        rw [show C.extentOf B' = C.objs.filter (fun o => B'.all (C.has o ·)) from rfl, filter_intersect]
        show C.objs.filter (fun o => B.all (C.has o ·)) = _
        apply List.filter_congr
        intro o _
        rw [Bool.eq_iff_iff, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
        constructor
        · intro h
          refine ⟨fun b hb => h b ?_, h a haB⟩
          rw [hB'def, List.mem_filter] at hb; exact hb.1
        · rintro ⟨h1, h2⟩ b hb
          by_cases hba : b = a
          · subst hba; exact h2
          · exact h1 b (by rw [hB'def, List.mem_filter]; exact ⟨hb, by simpa using hba⟩)
      · have hBB : B' = B := by
          rw [hB'def]
          apply List.filter_eq_self.mpr
          intro x hx
          simp only [bne_iff_ne, ne_eq]
          intro hxa; subst hxa; exact haB hx
        rw [← hBB]
        exact mem_extentsStep.mpr (Or.inl (hc B' hB'))
    have hs' : ∀ x ∈ extentsStep C acc a, ∃ B : List String, (∀ b ∈ B, b ∈ C.attrs) ∧ x = C.extentOf B := by
      intro x hx
      rcases mem_extentsStep.mp hx with hx | ⟨y, hy, rfl⟩
      · exact hs x hx
      · obtain ⟨B, hB, rfl⟩ := hs y hy
        refine ⟨B ++ [a], ?_, ?_⟩
        · intro b hb
          simp only [List.mem_append, List.mem_singleton] at hb
          rcases hb with hb | rfl
          · exact hB b hb
          · exact ha
        · rw [show C.extentOf B = C.objs.filter (fun o => B.all (C.has o ·)) from rfl, filter_intersect]
          show _ = C.objs.filter (fun o => (B ++ [a]).all (C.has o ·))
          apply List.filter_congr
          intro o _
          rw [List.all_append]
          simp
    have := extents_fold C as (P ++ [a]) (extentsStep C acc a) (fun b hb => has b (by simp [hb]))
      (fun b hb => by
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hP b hb
        · exact ha) hc' hs'
    simpa [List.foldl_cons, List.append_assoc] using this

theorem extentOf_nil (C : Ctx) : C.extentOf [] = C.objs := by simp [Ctx.extentOf]

/-- **`extents` holds the extent of every set of attributes…** -/
theorem extents_complete (C : Ctx) (B : List String) (hB : ∀ b ∈ B, b ∈ C.attrs) : C.extentOf B ∈ C.extents := by
  rw [extents_eq]
  refine (extents_fold C C.attrs [] [C.objs] (fun _ h => h) (by simp) ?_ ?_).1 B (by simpa using hB)
  · intro B hB
    have : B = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb => by simpa using hB b hb
    subst this; simp [extentOf_nil]
  · intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨[], by simp, by rw [hx, extentOf_nil]⟩

/-- **…and nothing else.** -/
theorem extents_sound (C : Ctx) : ∀ x ∈ C.extents, ∃ B : List String, (∀ b ∈ B, b ∈ C.attrs) ∧ x = C.extentOf B := by
  rw [extents_eq]
  refine (extents_fold C C.attrs [] [C.objs] (fun _ h => h) (by simp) ?_ ?_).2
  · intro B hB
    have : B = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb => by simpa using hB b hb
    subst this; simp [extentOf_nil]
  · intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨[], by simp, by rw [hx, extentOf_nil]⟩

/-- The extent of a set of attributes is closed: the objects with every attribute its objects share
are exactly its objects. -/
theorem extent_closed (C : Ctx) (B : List String) (hB : ∀ b ∈ B, b ∈ C.attrs) :
    C.extentOf (C.intentOf (C.extentOf B)) = C.extentOf B := by
  show C.objs.filter (fun o => (C.intentOf (C.extentOf B)).all (C.has o ·)) =
    C.objs.filter (fun o => B.all (C.has o ·))
  apply List.filter_congr
  intro o ho
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h b hb
    apply h b
    show b ∈ C.attrs.filter fun a => (C.extentOf B).all (C.has · a)
    rw [List.mem_filter, List.all_eq_true]
    refine ⟨hB b hb, fun o' ho' => ?_⟩
    rw [show C.extentOf B = C.objs.filter (fun o => B.all (C.has o ·)) from rfl, List.mem_filter,
      List.all_eq_true] at ho'
    exact ho'.2 b hb
  · intro h a ha
    have ha' : a ∈ C.attrs.filter fun a => (C.extentOf B).all (C.has · a) := ha
    rw [List.mem_filter, List.all_eq_true] at ha'
    apply ha'.2 o
    rw [show C.extentOf B = C.objs.filter (fun o => B.all (C.has o ·)) from rfl, List.mem_filter,
      List.all_eq_true]
    exact ⟨ho, h⟩

/-- **Every pair `concepts` lists is a formal concept**: its objects are those with all its attributes,
and its attributes those all its objects share. -/
theorem concepts_sound (C : Ctx) {A B : List String} (h : (A, B) ∈ C.concepts) :
    C.extentOf B = A ∧ C.intentOf A = B := by
  simp only [Ctx.concepts, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨e, he, rfl, rfl⟩ := h
  obtain ⟨B₀, hB₀, rfl⟩ := extents_sound C e he
  exact ⟨extent_closed C B₀ hB₀, rfl⟩

/-- **Every formal concept is listed.** -/
theorem concepts_complete (C : Ctx) {A B : List String} (hB : ∀ b ∈ B, b ∈ C.attrs)
    (hA : C.extentOf B = A) (hI : C.intentOf A = B) : (A, B) ∈ C.concepts := by
  simp only [Ctx.concepts, List.mem_map, Prod.mk.injEq]
  exact ⟨A, hA ▸ extents_complete C B hB, rfl, hI⟩

end Ord
end MathEngine
