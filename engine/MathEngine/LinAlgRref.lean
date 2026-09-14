import MathEngine.LinAlgQ
/-!
# Elimination reaches reduced row echelon form

M7 proved that `LinQ.rref` preserves the solution set and *checked* at run time that its output
is in echelon form. This file proves the second half (`rref_isRref`), so the check is gone. The invariant carried
column by column (`Inv`): the first `p` rows are pivot rows whose pivot columns `pivs` increase,
each holding a 1 that is alone in its column with zeros to its left; every later row is zero in
every column seen so far. One column step either finds no pivot (the invariant extends to the
next column as is) or swaps, scales and clears (it extends with one more pivot row).
-/
namespace MathEngine
namespace LinQ

/-! ## Entries under the operations -/

theorem entry_of_ge (m : Mat) {i : Nat} (h : m.length ≤ i) (j : Nat) : entry m i j = 0 := by
  unfold entry; rw [List.getElem?_eq_none h]; rfl

theorem entry_eq {m : Mat} {i : Nat} (hi : i < m.length) (j : Nat) : entry m i j = (m[i][j]?).getD 0 := by
  unfold entry; rw [List.getElem?_eq_getElem hi]; rfl

theorem entry_set (m : Mat) (i : Nat) (r : Row) (k j : Nat) :
    entry (m.set i r) k j = if k = i ∧ i < m.length then (r[j]?).getD 0 else entry m k j := by
  unfold entry
  rw [List.getElem?_set]
  by_cases hki : k = i
  · subst hki
    by_cases hi : k < m.length
    · simp [hi]
    · simp [hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · simp [Ne.symm hki, hki]

theorem getD_rowAdd (c : Rat) : ∀ (ri rj : Row) (j : Nat),
    ((rowAdd c ri rj)[j]?).getD 0 = (ri[j]?).getD 0 + c * (rj[j]?).getD 0
  | a :: as, b :: bs, 0 => by simp [rowAdd]
  | a :: as, b :: bs, j + 1 => by simp [rowAdd, getD_rowAdd c as bs j]
  | as, [], j => by cases as <;> simp [rowAdd] <;> grind
  | [], b :: bs, 0 => by simp [rowAdd] <;> grind
  | [], b :: bs, j + 1 => by simp [rowAdd, getD_rowAdd c [] bs j] <;> grind

theorem length_apply (op : Op) (m : Mat) : (op.apply m).length = m.length := by
  cases op <;> simp only [Op.apply] <;> (repeat' split) <;> simp [List.length_set]

theorem entry_swap {m : Mat} {i j : Nat} (hi : i < m.length) (hj : j < m.length) (k l : Nat) :
    entry ((Op.swap i j).apply m) k l = if k = j then entry m i l else if k = i then entry m j l else entry m k l := by
  simp only [Op.apply]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only
  rw [entry_set, entry_set, List.length_set]
  by_cases hkj : k = j
  · subst hkj; simp [hj, entry_eq hi]
  · by_cases hki : k = i
    · subst hki; simp [hkj, hi, entry_eq hj]
    · simp [hkj, hki]

theorem entry_scale {m : Mat} {i : Nat} {c : Rat} (hc : c ≠ 0) (hi : i < m.length) (k l : Nat) :
    entry ((Op.scale i c).apply m) k l = if k = i then c * entry m i l else entry m k l := by
  simp only [Op.apply, if_neg hc]
  rw [List.getElem?_eq_getElem hi]
  simp only
  rw [entry_set]
  by_cases hki : k = i
  · subst hki; simp only [hi, and_self, if_true, entry_eq hi]
    cases hl : m[k][l]? <;> simp [List.getElem?_map, hl]
  · simp [hki]

theorem entry_addMul {m : Mat} {i j : Nat} {c : Rat} (hij : i ≠ j) (hi : i < m.length) (hj : j < m.length) (k l : Nat) :
    entry ((Op.addMul i j c).apply m) k l = if k = i then entry m i l + c * entry m j l else entry m k l := by
  simp only [Op.apply, if_neg hij]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only
  rw [entry_set]
  by_cases hki : k = i
  · subst hki; simp only [hi, and_self, if_true, entry_eq hi, entry_eq hj, getD_rowAdd]
  · simp [hki]

theorem run_map_eq_runOps (col : Nat) (ops : List Op) : ∀ m, run (ops.map (col, ·)) m = runOps ops m := by
  induction ops with
  | nil => intro m; rfl
  | cons o os ih => intro m; simp only [List.map_cons, run, runOps, List.foldl] at *; exact ih _

theorem run_append (a b : List (Nat × Op)) (m : Mat) : run (a ++ b) m = run b (run a m) := by
  simp [run, List.foldl_append]

theorem runOps_append (a b : List Op) (m : Mat) : runOps (a ++ b) m = runOps b (runOps a m) := by
  simp [runOps, List.foldl_append]

theorem length_runOps (ops : List Op) : ∀ m : Mat, (runOps ops m).length = m.length := by
  induction ops with
  | nil => intro m; rfl
  | cons o os ih => intro m; simp only [runOps, List.foldl] at *; rw [ih, length_apply]

theorem length_run (ops : List (Nat × Op)) : ∀ m : Mat, (run ops m).length = m.length := by
  induction ops with
  | nil => intro m; rfl
  | cons o os ih => intro m; simp only [run, List.foldl] at *; rw [ih, length_apply]

/-- The coefficient recorded for row `k`, if any. -/
def coeffOf (k : Nat) : List (Nat × Rat) → Option Rat
  | [] => none
  | (i, c) :: rest => if k = i then some c else coeffOf k rest

theorem coeffOf_eq_none {k : Nat} : ∀ {L : List (Nat × Rat)}, k ∉ L.map Prod.fst → coeffOf k L = none
  | [], _ => rfl
  | (i, c) :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [coeffOf, h.1, coeffOf_eq_none h.2]

/-- Clearing rows `i` with factors `c`, one operation per pair, all against the same row `p`: each
row changes by its own multiple of row `p`, which itself is untouched. -/
theorem entry_clears {p : Nat} : ∀ (L : List (Nat × Rat)) (m : Mat), p < m.length →
    (L.map Prod.fst).Nodup → (∀ x ∈ L, x.1 ≠ p) → (∀ x ∈ L, x.1 < m.length) →
    ∀ k l, entry (runOps (L.map fun x => Op.addMul x.1 p x.2) m) k l =
      match coeffOf k L with
      | some c => entry m k l + c * entry m p l
      | none => entry m k l
  | [], m, _, _, _, _, k, l => by simp [runOps, coeffOf]
  | (i, c) :: rest, m, hp, hnd, hne, hlt, k, l => by
    have hip : i ≠ p := hne (i, c) (by simp)
    have hi : i < m.length := hlt (i, c) (by simp)
    have hnd' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hi_not : i ∉ rest.map Prod.fst := (List.nodup_cons.mp (by simpa using hnd)).1
    have ih := entry_clears rest ((Op.addMul i p c).apply m) (by rw [length_apply]; exact hp) hnd'
      (fun x hx => hne x (by simp [hx])) (fun x hx => by rw [length_apply]; exact hlt x (by simp [hx]))
    show entry (runOps (rest.map fun x => Op.addMul x.1 p x.2) ((Op.addMul i p c).apply m)) k l = _
    rw [ih k l]
    simp only [coeffOf, entry_addMul hip hi hp]
    by_cases hki : k = i
    · subst hki; simp [coeffOf_eq_none hi_not]
    · cases coeffOf k rest <;> simp [hki, Ne.symm hip]

/-! ## The invariant -/

/-- Rows `< p` are pivot rows with pivot columns `pivs`; rows `≥ p` are zero left of `col`. -/
structure Inv (m : Mat) (p col : Nat) (pivs : List Nat) : Prop where
  len : pivs.length = p
  lt : ∀ c ∈ pivs, c < col
  sorted : pivs.Pairwise (· < ·)
  pivot : ∀ i, i < p → entry m i (pivs.getD i 0) = 1
  lead : ∀ i, i < p → ∀ j, j < pivs.getD i 0 → entry m i j = 0
  alone : ∀ i, i < p → ∀ k, k ≠ i → entry m k (pivs.getD i 0) = 0
  below : ∀ i, p ≤ i → ∀ j, j < col → entry m i j = 0
  p_le : p ≤ m.length

theorem Inv.start (m : Mat) : Inv m 0 0 [] where
  len := rfl
  lt := by simp
  sorted := List.Pairwise.nil
  pivot := fun i h => absurd h (Nat.not_lt_zero _)
  lead := fun i h => absurd h (Nat.not_lt_zero _)
  alone := fun i h => absurd h (Nat.not_lt_zero _)
  below := fun _ _ j hj => absurd hj (Nat.not_lt_zero _)
  p_le := Nat.zero_le _

/-- No pivot in this column: the invariant moves one column right. -/
theorem Inv.next_none {m : Mat} {p col : Nat} {pivs : List Nat} (h : Inv m p col pivs)
    (hz : ∀ i, p ≤ i → entry m i col = 0) : Inv m p (col + 1) pivs where
  len := h.len
  lt := fun c hc => Nat.lt_succ_of_lt (h.lt c hc)
  sorted := h.sorted
  pivot := h.pivot
  lead := h.lead
  alone := h.alone
  below := fun i hi j hj => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · exact h.below i hi j hj
    · exact hz i hi
  p_le := h.p_le

theorem getD_append_lt {l l' : List Nat} {n d : Nat} (h : n < l.length) : (l ++ l').getD n d = l.getD n d := by
  induction l generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [List.cons_append, List.getD_cons_succ]; exact ih (by simpa using h)

theorem getD_append_singleton (l : List Nat) (a d : Nat) : (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil => rfl
  | cons b bs ih => simpa using ih

theorem getD_mem {l : List Nat} {n d : Nat} (h : n < l.length) : l.getD n d ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n => simp only [List.getD_cons_succ]; exact List.mem_cons_of_mem _ (ih (by simpa using h))

/-- The column step, entry-wise: `m'` agrees with `m` in row `p`, and every other row had its
entry-`col` multiple of row `p` subtracted; row `p` has a 1 in column `col`. -/
theorem Inv.next_some {m m' : Mat} {p col : Nat} {pivs : List Nat} (h : Inv m p col pivs) (hp : p < m.length)
    (hlen : m'.length = m.length)
    (hrow : ∀ l, entry m' p l = entry m p l)
    (hother : ∀ k, k ≠ p → ∀ l, entry m' k l = entry m k l - entry m k col * entry m p l)
    (hpiv : entry m p col = 1) :
    Inv m' (p + 1) (col + 1) (pivs ++ [col]) := by
  have hlenp : pivs.length = p := h.len
  have hgetD : ∀ i, i < p → (pivs ++ [col]).getD i 0 = pivs.getD i 0 := fun i hi => getD_append_lt (by omega)
  have hgetDp : (pivs ++ [col]).getD p 0 = col := by rw [← hlenp]; exact getD_append_singleton _ _ _
  have hlt : ∀ i, i < p → pivs.getD i 0 < col := fun i hi => h.lt _ (getD_mem (by omega))
  have hrowz : ∀ j, j < col → entry m p j = 0 := fun j hj => h.below p (Nat.le_refl _) j hj
  exact {
    len := by simp [hlenp]
    lt := fun c hc => by
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact Nat.lt_succ_of_lt (h.lt c hc)
      · exact Nat.lt_succ_self _
    sorted := List.pairwise_append.mpr ⟨h.sorted, List.pairwise_singleton _ _, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact h.lt a ha⟩
    pivot := fun i hi => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · rw [hgetD i hi, hother i (by omega), h.pivot i hi, hrowz _ (hlt i hi)]; grind
      · rw [hgetDp, hrow, hpiv]
    lead := fun i hi j hj => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · rw [hgetD i hi] at hj
        rw [hother i (by omega), h.lead i hi j hj, hrowz j (Nat.lt_trans hj (hlt i hi))]; grind
      · rw [hgetDp] at hj
        rw [hrow, hrowz j hj]
    alone := fun i hi k hk => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · rw [hgetD i hi]
        by_cases hkp : k = p
        · subst hkp; rw [hrow, hrowz _ (hlt i hi)]
        · rw [hother k hkp, h.alone i hi k hk, hrowz _ (hlt i hi)]; grind
      · rw [hgetDp, hother k hk, hpiv]; grind
    below := fun i hi j hj => by
      have hip : i ≠ p := by omega
      rw [hother i hip]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · rw [h.below i (by omega) j hj, hrowz j hj]; grind
      · rw [hpiv]; grind
    p_le := by omega }

/-! ## The algorithm -/

theorem Inv.widen {m : Mat} {p col col' : Nat} {pivs : List Nat} (h : Inv m p col pivs)
    (hge : m.length ≤ p) (hcol : col ≤ col') : Inv m p col' pivs where
  len := h.len
  lt := fun c hc => Nat.lt_of_lt_of_le (h.lt c hc) hcol
  sorted := h.sorted
  pivot := h.pivot
  lead := h.lead
  alone := h.alone
  below := fun i hi j _ => entry_of_ge m (Nat.le_trans hge hi) j
  p_le := h.p_le

/-- Swapping row `p` with a row `q ≥ p` keeps the invariant. -/
theorem Inv.swap_ge {m : Mat} {p col : Nat} {pivs : List Nat} (h : Inv m p col pivs) {q : Nat}
    (hpq : p ≤ q) (hq : q < m.length) (hp : p < m.length) : Inv ((Op.swap q p).apply m) p col pivs := by
  have hlt : ∀ i, i < p → pivs.getD i 0 < col := fun i hi => h.lt _ (getD_mem (by rw [h.len]; exact hi))
  have e := entry_swap hq hp
  exact {
    len := h.len, lt := h.lt, sorted := h.sorted
    pivot := fun i hi => by rw [e]; simp only [show i ≠ p by omega, show i ≠ q by omega, if_false]; exact h.pivot i hi
    lead := fun i hi j hj => by rw [e]; simp only [show i ≠ p by omega, show i ≠ q by omega, if_false]; exact h.lead i hi j hj
    alone := fun i hi k hk => by
      rw [e]
      by_cases hkp : k = p
      · subst hkp; simp only [if_true]; exact h.below q hpq _ (hlt i hi)
      · by_cases hkq : k = q
        · subst hkq; simp only [hkp, if_false, if_true]; exact h.below p (Nat.le_refl _) _ (hlt i hi)
        · simp only [hkp, hkq, if_false]; exact h.alone i hi k hk
    below := fun i hi j hj => by
      rw [e]
      by_cases hip : i = p
      · subst hip; simp only [if_true]; exact h.below q hpq j hj
      · by_cases hiq : i = q
        · subst hiq; simp only [hip, if_false, if_true]; exact h.below p (Nat.le_refl _) j hj
        · simp only [hip, hiq, if_false]; exact h.below i hi j hj
    p_le := by rw [length_apply]; exact h.p_le }

/-- Scaling row `p` keeps the invariant. -/
theorem Inv.scale_p {m : Mat} {p col : Nat} {pivs : List Nat} (h : Inv m p col pivs) {c : Rat}
    (hc : c ≠ 0) (hp : p < m.length) : Inv ((Op.scale p c).apply m) p col pivs := by
  have hlt : ∀ i, i < p → pivs.getD i 0 < col := fun i hi => h.lt _ (getD_mem (by rw [h.len]; exact hi))
  have e := entry_scale hc hp
  exact {
    len := h.len, lt := h.lt, sorted := h.sorted
    pivot := fun i hi => by rw [e]; simp only [show i ≠ p by omega, if_false]; exact h.pivot i hi
    lead := fun i hi j hj => by rw [e]; simp only [show i ≠ p by omega, if_false]; exact h.lead i hi j hj
    alone := fun i hi k hk => by
      rw [e]
      by_cases hkp : k = p
      · subst hkp; simp only [if_true]; rw [h.below k (Nat.le_refl _) _ (hlt i hi)]; simp
      · simp only [hkp, if_false]; exact h.alone i hi k hk
    below := fun i hi j hj => by
      rw [e]
      by_cases hip : i = p
      · subst hip; simp only [if_true]; rw [h.below i (Nat.le_refl _) j hj]; simp
      · simp only [hip, if_false]; exact h.below i hi j hj
    p_le := by rw [length_apply]; exact h.p_le }

theorem coeffOf_map (k : Nat) (g : Nat → Rat) : ∀ (l : List Nat), l.Nodup →
    coeffOf k (l.map fun i => (i, g i)) = if k ∈ l then some (g k) else none
  | [], _ => by simp [coeffOf]
  | i :: rest, hnd => by
    simp only [List.map_cons, coeffOf, List.mem_cons]
    by_cases hki : k = i
    · subst hki; simp
    · simp only [hki, if_false, false_or]
      exact coeffOf_map k g rest (List.nodup_cons.mp hnd).2

theorem columnOps_none {m : Mat} {col p : Nat} (h : columnOps m col p = none) :
    ∀ i, p ≤ i → entry m i col = 0 := by
  intro i hi
  simp only [columnOps, Option.map_eq_none_iff] at h
  by_cases hil : i < m.length
  · have := List.find?_eq_none.mp h i (List.mem_range.mpr hil)
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at this
    exact this hi
  · exact entry_of_ge m (Nat.le_of_not_lt hil) col

/-- The column step. -/
theorem columnOps_some {m : Mat} {col p : Nat} {pivs : List Nat} {ops : List Op} (h : Inv m p col pivs)
    (hp : p < m.length) (hs : columnOps m col p = some ops) :
    Inv (runOps ops m) (p + 1) (col + 1) (pivs ++ [col]) := by
  simp only [columnOps] at hs
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hql : q < m.length := List.mem_range.mp (List.mem_of_find?_eq_some hq)
  have hqp := List.find?_some hq
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hqp
  obtain ⟨hpq, hnz⟩ := hqp
  simp only [columnBody]
  -- stage 1: the swap
  have stage1 : ∃ m1 : Mat, runOps (if q = p then [] else [Op.swap q p]) m = m1 ∧ Inv m1 p col pivs ∧
      entry m1 p col ≠ 0 ∧ m1.length = m.length := by
    by_cases hqp' : q = p
    · subst hqp'; exact ⟨m, by simp [runOps, List.foldl], h, hnz, rfl⟩
    · refine ⟨(Op.swap q p).apply m, by simp [runOps, List.foldl, hqp'], h.swap_ge hpq hql hp, ?_, length_apply _ _⟩
      rw [entry_swap hql hp]; simpa using hnz
  obtain ⟨m1, hm1, h1, hnz1, hlen1⟩ := stage1
  rw [runOps_append, runOps_append, hm1]
  have hp1 : p < m1.length := by rw [hlen1]; exact hp
  -- stage 2: the scaling
  have stage2 : ∃ m2 : Mat, runOps (if entry m1 p col = 1 then [] else [Op.scale p (entry m1 p col).inv]) m1 = m2 ∧
      Inv m2 p col pivs ∧ entry m2 p col = 1 ∧ m2.length = m.length := by
    by_cases hone : entry m1 p col = 1
    · exact ⟨m1, by simp [runOps, List.foldl, hone], h1, hone, hlen1⟩
    · have hinv : (entry m1 p col).inv ≠ 0 := by
        show (entry m1 p col)⁻¹ ≠ 0; grind
      refine ⟨(Op.scale p (entry m1 p col).inv).apply m1, by simp [runOps, List.foldl, hone], h1.scale_p hinv hp1, ?_, by rw [length_apply, hlen1]⟩
      rw [entry_scale hinv hp1]; simp only [if_true]
      show (entry m1 p col)⁻¹ * entry m1 p col = 1; grind
  obtain ⟨m2, hm2, h2, hpiv, hlen2⟩ := stage2
  rw [hm2]
  have hp2 : p < m2.length := by rw [hlen2]; exact hp
  -- stage 3: the clearing
  generalize hkeys : ((List.range m.length).filter fun i => i ≠ p ∧ entry m2 i col ≠ 0) = keys
  have hnd : keys.Nodup := hkeys ▸ List.nodup_range.filter _
  have hmem : ∀ i, i ∈ keys ↔ i < m.length ∧ i ≠ p ∧ entry m2 i col ≠ 0 := fun i => by
    rw [← hkeys]; simp [List.mem_filter, List.mem_range]
  have hcl := entry_clears (p := p) (keys.map fun i => (i, -(entry m2 i col))) m2 hp2
    (by simpa [List.map_map, Function.comp_def] using hnd)
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact ((hmem i).mp hi).2.1)
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; rw [hlen2]; exact ((hmem i).mp hi).1)
  refine h2.next_some hp2 (length_runOps _ _) ?_ ?_ hpiv
  · intro l
    rw [hcl, coeffOf_map _ _ keys hnd]
    have : p ∉ keys := fun hpk => ((hmem p).mp hpk).2.1 rfl
    simp [this]
  · intro k hk l
    rw [hcl, coeffOf_map _ _ keys hnd]
    by_cases hkm : k ∈ keys
    · simp only [hkm, if_true]; grind
    · simp only [hkm, if_false]
      have hz : entry m2 k col = 0 := by
        by_cases hkl : k < m.length
        · cases Decidable.em (entry m2 k col = 0) with
          | inl h0 => exact h0
          | inr hne => exact absurd ((hmem k).mpr ⟨hkl, hk, hne⟩) hkm
        · exact entry_of_ge m2 (by rw [hlen2]; exact Nat.le_of_not_lt hkl) col
      rw [hz]; grind

theorem run_map_eq_runOps' (col : Nat) (ops : List Op) (m : Mat) : run (ops.map (col, ·)) m = runOps ops m :=
  run_map_eq_runOps col ops m

theorem go_inv : ∀ (k : Nat) (m : Mat) (col p : Nat) (pivs : List Nat), Inv m p col pivs →
    ∃ p' pivs', Inv (run (go m col p k) m) p' (col + k) pivs'
  | 0, m, col, p, pivs, h => ⟨p, pivs, by simpa [go, run] using h⟩
  | k + 1, m, col, p, pivs, h => by
    simp only [go]
    split
    · rename_i hge
      exact ⟨p, pivs, by simp only [run, List.foldl]; exact h.widen hge (Nat.le_add_right _ _)⟩
    · rename_i hlt
      split
      · rename_i hn
        obtain ⟨p', pivs', h'⟩ := go_inv k m (col + 1) p pivs (h.next_none (columnOps_none hn))
        exact ⟨p', pivs', by rw [show col + (k + 1) = col + 1 + k by omega]; exact h'⟩
      · rename_i ops hs
        rw [run_append, run_map_eq_runOps']
        obtain ⟨p', pivs', h'⟩ := go_inv k (runOps ops m) (col + 1) (p + 1) (pivs ++ [col])
          (columnOps_some h (Nat.lt_of_not_le hlt) hs)
        exact ⟨p', pivs', by rw [show col + (k + 1) = col + 1 + k by omega]; exact h'⟩

/-- **Reduced row echelon form** in width `w`: some `p` pivot rows come first, each with a leading
1 that is alone in its column and strictly right of the previous row's, and every later row is
zero in the first `w` columns — every column, for a matrix of width `w`. -/
def IsRref (m : Mat) (w : Nat) : Prop := ∃ p pivs, Inv m p w pivs

/-- **Elimination reaches reduced row echelon form**, in the width of the input. -/
theorem rref_isRref (m : Mat) : IsRref (rref m) (ncols m) := by
  obtain ⟨p, pivs, h⟩ := go_inv (ncols m) m 0 0 [] (Inv.start m)
  exact ⟨p, pivs, by simpa [rref, rrefOps] using h⟩

end LinQ
end MathEngine
