import MathEngine.Expr
/-!
# Gauss–Jordan elimination over ℚ, verified (M7)

The claim: **row reduction does not change the solution set.** A matrix is read as a homogeneous
system, one equation `r · x = 0` per row; the augmented matrix `[A | b]` of `A x = b` is the same
system in the point `(x, -1)`, so both readings are covered by one predicate `Sol`.

Elimination is written as a sequence of the three elementary row operations, and the theorem is one
lemma per operation: each is invertible, so it preserves `Sol` in both directions. The degenerate
parameters — scaling by 0, adding a row to itself — are defined to be the identity, which is what
makes every operation invertible *by construction*; the algorithm never emits them. The algorithm
itself is structural recursion over the columns, so it terminates without fuel and its correctness
is the fold `sol_run`. That the result is in reduced row echelon form is `rref_isRref`
(`LinAlgRref.lean`).

Only `Init` is used: the field algebra is discharged by `grind`, whose `Rat` instances ship with core.
-/
namespace MathEngine
namespace LinQ

abbrev Row := List Rat
abbrev Mat := List Row

/-- The linear form of a row evaluated at a point; a missing coefficient or coordinate counts as 0. -/
def dot : Row → List Rat → Rat
  | a :: as, x :: xs => a * x + dot as xs
  | _, _ => 0

/-- `x` solves every equation of the matrix. -/
def Sol (m : Mat) (x : List Rat) : Prop := ∀ r ∈ m, dot r x = 0

/-- `ri + c · rj`, padding the shorter row with zeros rather than truncating. -/
def rowAdd (c : Rat) : Row → Row → Row
  | a :: as, b :: bs => (a + c * b) :: rowAdd c as bs
  | as, [] => as
  | [], b :: bs => c * b :: rowAdd c [] bs

/-- The elementary row operations. -/
inductive Op where
  /-- exchange rows `i` and `j` -/
  | swap (i j : Nat)
  /-- `Rᵢ ← c · Rᵢ`; with `c = 0` it is the identity -/
  | scale (i : Nat) (c : Rat)
  /-- `Rᵢ ← Rᵢ + c · Rⱼ`; with `i = j` it is the identity -/
  | addMul (i j : Nat) (c : Rat)
  deriving Repr, BEq

def Op.apply : Op → Mat → Mat
  | .swap i j, m =>
    match m[i]?, m[j]? with
    | some ri, some rj => (m.set i rj).set j ri
    | _, _ => m
  | .scale i c, m =>
    if c = 0 then m else
    match m[i]? with
    | some ri => m.set i (ri.map (c * ·))
    | none => m
  | .addMul i j c, m =>
    if i = j then m else
    match m[i]?, m[j]? with
    | some ri, some rj => m.set i (rowAdd c ri rj)
    | _, _ => m

/-- Apply a tagged operation list in order (the tag is presentation data: the column being cleared). -/
def run (ops : List (Nat × Op)) (m : Mat) : Mat := ops.foldl (fun m o => o.2.apply m) m

/-! ## The three lemmas -/

theorem dot_map_mul (c : Rat) : ∀ (r x : List Rat), dot (r.map (c * ·)) x = c * dot r x
  | [], x => by cases x <;> simp [dot] <;> grind
  | _ :: _, [] => by simp [dot]
  | a :: as, y :: ys => by simp [dot, dot_map_mul c as ys]; grind

theorem dot_rowAdd (c : Rat) : ∀ (ri rj x : Row), dot (rowAdd c ri rj) x = dot ri x + c * dot rj x
  | _ :: as, _ :: bs, _ :: ys => by simp [rowAdd, dot, dot_rowAdd c as bs ys]; grind
  | _ :: _, _ :: _, [] => by simp [rowAdd, dot]; grind
  | as, [], x => by cases as <;> cases x <;> simp [rowAdd, dot] <;> grind
  | [], _ :: bs, _ :: ys => by simp [rowAdd, dot, dot_rowAdd c [] bs ys]; grind
  | [], _ :: _, [] => by simp [rowAdd, dot]; grind

theorem sol_iff (m : Mat) (x : List Rat) : Sol m x ↔ ∀ (i : Nat) r, m[i]? = some r → dot r x = 0 := by
  constructor
  · intro h i r hi; exact h r (List.mem_of_getElem? hi)
  · intro h r hr; obtain ⟨i, hi⟩ := List.getElem?_of_mem hr; exact h i r hi

theorem getElem?_set' {α} (l : List α) (i k : Nat) (a : α) (hi : i < l.length) :
    (l.set i a)[k]? = if k = i then some a else l[k]? := by
  by_cases h : k = i
  · subst h; simp [List.getElem?_set_self hi]
  · simp [List.getElem?_set_ne (Ne.symm h), h]

theorem sol_swap (m : Mat) (i j : Nat) (x : List Rat) : Sol ((Op.swap i j).apply m) x ↔ Sol m x := by
  simp only [Op.apply]
  split
  · rename_i ri rj hi hj
    have hil : i < m.length := (List.getElem?_eq_some_iff.mp hi).1
    have hjl : j < m.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjl' : j < (m.set i rj).length := by simpa [List.length_set] using hjl
    rw [sol_iff, sol_iff]
    simp only [getElem?_set' _ _ _ _ hjl', getElem?_set' _ _ _ _ hil]
    grind
  · exact Iff.rfl

theorem sol_scale (m : Mat) (i : Nat) (c : Rat) (x : List Rat) : Sol ((Op.scale i c).apply m) x ↔ Sol m x := by
  simp only [Op.apply]
  split
  · exact Iff.rfl
  · rename_i hc
    split
    · rename_i ri hi
      have hil : i < m.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [sol_iff, sol_iff]
      simp only [getElem?_set' _ _ _ _ hil]
      have hm := dot_map_mul c ri x
      grind
    · exact Iff.rfl

theorem sol_addMul (m : Mat) (i j : Nat) (c : Rat) (x : List Rat) :
    Sol ((Op.addMul i j c).apply m) x ↔ Sol m x := by
  simp only [Op.apply]
  split
  · exact Iff.rfl
  · rename_i hij
    split
    · rename_i ri rj hi hj
      have hil : i < m.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [sol_iff, sol_iff]
      simp only [getElem?_set' _ _ _ _ hil]
      have hm := dot_rowAdd c ri rj x
      grind
    · exact Iff.rfl

theorem sol_apply (op : Op) (m : Mat) (x : List Rat) : Sol (op.apply m) x ↔ Sol m x := by
  cases op with
  | swap i j => exact sol_swap m i j x
  | scale i c => exact sol_scale m i c x
  | addMul i j c => exact sol_addMul m i j c x

theorem sol_run (ops : List (Nat × Op)) (m : Mat) (x : List Rat) : Sol (run ops m) x ↔ Sol m x := by
  induction ops generalizing m with
  | nil => exact Iff.rfl
  | cons o os ih => simp only [run, List.foldl] at *; rw [ih, sol_apply]

/-! ## The algorithm -/

def entry (m : Mat) (i j : Nat) : Rat := ((m[i]?.getD [])[j]?).getD 0
def ncols (m : Mat) : Nat := (m.head?.map List.length).getD 0

/-- Running untagged operations in order. -/
def runOps (ops : List Op) (m : Mat) : Mat := ops.foldl (fun m o => o.apply m) m

/-- The operations that make column `col` a pivot column with the pivot in row `p`, given a row
`q ≥ p` with a nonzero entry there: a swap to bring it up, a scaling to make it 1, and one row
addition per other nonzero entry in the column. -/
def columnBody (m : Mat) (col p q : Nat) : List Op :=
  let swaps := if q = p then [] else [Op.swap q p]
  let m1 := runOps swaps m
  let piv := entry m1 p col
  let scales := if piv = 1 then [] else [Op.scale p piv.inv]
  let m2 := runOps scales m1
  let factors := ((List.range m.length).filter fun i => i ≠ p ∧ entry m2 i col ≠ 0).map fun i => (i, -(entry m2 i col))
  swaps ++ scales ++ factors.map fun x => Op.addMul x.1 p x.2

/-- `none` when the column has no nonzero entry at or below `p`. -/
def columnOps (m : Mat) (col p : Nat) : Option (List Op) :=
  ((List.range m.length).find? fun i => p ≤ i && entry m i col != 0).map (columnBody m col p)

/-- Column by column; `k` is how many columns remain, `p` the next pivot row. -/
def go (m : Mat) (col p : Nat) : Nat → List (Nat × Op)
  | 0 => []
  | k + 1 =>
    if p ≥ m.length then [] else
    match columnOps m col p with
    | none => go m (col + 1) p k
    | some ops =>
      let tagged := ops.map (col, ·)
      tagged ++ go (run tagged m) (col + 1) (p + 1) k

/-- The row operations Gauss–Jordan performs on `m`, each tagged with its column. -/
def rrefOps (m : Mat) : List (Nat × Op) := go m 0 0 (ncols m)

/-- Reduced row echelon form of `m`. -/
def rref (m : Mat) : Mat := run (rrefOps m) m

/-- **Elimination preserves the solution set.** -/
theorem sol_rref (m : Mat) (x : List Rat) : Sol (rref m) x ↔ Sol m x := sol_run _ _ _

end LinQ
end MathEngine
