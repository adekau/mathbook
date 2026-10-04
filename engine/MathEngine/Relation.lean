import MathEngine.Poset
/-!
# Relations, in the order-theory world

A relation on a finite set is its elements and its pairs. The order world's posets are relations with
three properties built in; here the properties are the question. Each check decides a property and,
when it fails, names the elements that show it (`reflexive`, `symmetric`, `antisymmetric`,
`transitive`, `equivalence`, `preorder`). Closures add exactly the pairs a property forces, round by
round, each round a step; `RelationProofs.lean` proves the transitive closure is transitive and lies
inside every transitive relation containing the original, so it is the least. An equivalence
relation's classes partition the set; one relation is finer than another when its pairs are among
the other's. A relation read as "steps to" is well-founded on a finite set exactly when it has no
cycle, and a measure proves it when every step goes down.
-/
namespace MathEngine
namespace Ord

/-- A relation on a finite set: its elements, and its pairs (each once). -/
structure Rel where
  elems : List String
  pairs : List (String × String)
  deriving Inhabited

def Rel.has (R : Rel) (x y : String) : Bool := R.pairs.contains (x, y)

def Rel.of (elems : List String) (pairs : List (String × String)) : Rel := ⟨elems.eraseDups, pairs.eraseDups⟩

/-- The equivalence relation "same label" of a labelling `x ↦ k`: the kernel of the map. -/
def kernel (elems : List String) (label : List (String × String)) : Rel :=
  let lab (x : String) := (label.lookup x).getD x
  Rel.of elems (elems.flatMap fun x => (elems.filter fun y => lab x == lab y).map (x, ·))

/-! ## Properties, with the elements that break them -/

def reflexiveFailure (R : Rel) : Option String := R.elems.find? fun x => !R.has x x
def symmetricFailure (R : Rel) : Option (String × String) := R.pairs.find? fun (x, y) => !R.has y x
def antisymmetricFailure (R : Rel) : Option (String × String) := R.pairs.find? fun (x, y) => x != y && R.has y x
/-- `x R y`, `y R z`, and not `x R z`. -/
def transitiveFailure (R : Rel) : Option (String × String × String) :=
  R.pairs.findSome? fun (x, y) => (R.pairs.find? fun (y', z) => y' == y && !R.has x z).map fun (_, z) => (x, y, z)

/-! ## Closures -/

/-- One round of transitive closure: every pair forced by two that chain. -/
def Rel.round (R : Rel) : List (String × String) :=
  R.pairs.flatMap fun (a, b) => R.pairs.filterMap fun (c, d) => if b == c && !R.has a d then some (a, d) else none

/-- The transitive closure, round by round: the pairs each round adds. A relation on `n` elements has
at most `n²` pairs, so `n² + 1` rounds reach the fixed point; `stable` says it was reached. -/
def transClosure (R : Rel) : Rel × List (List (String × String)) × Bool :=
  go (R.elems.length * R.elems.length + 1) R []
where
  go : Nat → Rel → List (List (String × String)) → Rel × List (List (String × String)) × Bool
    | 0, R, acc => (R, acc.reverse, R.round.isEmpty)
    | n + 1, R, acc =>
      let add := R.round.eraseDups
      if add.isEmpty then (R, acc.reverse, true) else go n ⟨R.elems, R.pairs ++ add⟩ (add :: acc)

def reflClosureAdds (R : Rel) : List (String × String) := (R.elems.filter fun x => !R.has x x).map fun x => (x, x)
def symmClosureAdds (R : Rel) : List (String × String) := ((R.pairs.filter fun (x, y) => !R.has y x).map fun (x, y) => (y, x)).eraseDups

/-! ## Equivalence classes, refinement -/

/-- The class of `x`: everything related to it. -/
def Rel.classOf (R : Rel) (x : String) : List String := R.elems.filter fun y => R.has x y

/-- The classes of an equivalence relation, each once, in order of first element. -/
def Rel.classes (R : Rel) : List (List String) :=
  R.elems.foldl (fun acc x => if acc.any (·.contains x) then acc else acc ++ [R.classOf x]) []

/-- A pair of `R` that is not in `S`: `R` is not finer than `S`. -/
def finerFailure (R S : Rel) : Option (String × String) := R.pairs.find? fun (x, y) => !S.has x y

/-! ## Well-founded relations and measures -/

/-- A step `x R y` the measure does not decrease along: `m y ≥ m x`. -/
def measureFailure (R : Rel) (m : String → Option Int) : Option (String × String) :=
  R.pairs.find? fun (x, y) => match m x, m y with | some a, some b => !(b < a) | _, _ => true

/-- Every element the relation mentions. -/
def Rel.nodes (R : Rel) : List String := (R.elems ++ R.pairs.flatMap fun (a, b) => [a, b]).eraseDups

/-- Ranks by peeling: the elements with no step to an element still unranked get the next rank. When
everything is ranked, every step goes down in rank; what is left otherwise has a step out of every
element back into it. -/
def peelRanks (R : Rel) : List (String × Nat) × List String :=
  go (R.nodes.length + 1) 0 R.nodes []
where
  go : Nat → Nat → List String → List (String × Nat) → List (String × Nat) × List String
    | 0, _, left, ranks => (ranks, left)
    | f + 1, k, left, ranks =>
      let sinks := left.filter fun x => !(R.pairs.any fun (a, b) => a == x && left.contains b)
      if sinks.isEmpty then (ranks, left)
      else go f (k + 1) (left.filter fun x => !sinks.contains x) (ranks ++ sinks.map (·, k))

/-- Follow steps inside `left` from the head of `path` until an element repeats: the cycle. -/
def walkCycle (R : Rel) (left : List String) : Nat → List String → Option (List String)
  | 0, _ => none
  | f + 1, path =>
    match path.head? with
    | none => none
    | some x =>
      match R.pairs.find? fun (a, b) => a == x && left.contains b with
      | none => none
      | some (_, y) =>
        if path.contains y then some (y :: (path.takeWhile (· != y)).reverse ++ [y])
        else walkCycle R left f (y :: path)

/-- The certificate a cycle gives: a nonempty set in which every element steps to an element of the
set, so following steps never stops (`not_wf_of_closed`). -/
def stepClosed (R : Rel) (c : List String) : Bool := !c.isEmpty && c.all fun x => c.any fun y => R.has x y

/-- **Is `R`, read as "steps to", well-founded?** `none`: yes, and the peeling ranks are a measure that
goes down along every step, checked (`wellfounded_none`). `some c`: no, and `c` is a cycle, checked
to step back into itself (`wellfounded_some`). Either way the answer carries its certificate. -/
def wellfounded (R : Rel) : Except String (Option (List String)) :=
  let (ranks, left) := peelRanks R
  if left.isEmpty then
    if (measureFailure R fun x => (ranks.lookup x).map Int.ofNat).isNone then .ok none
    else .error "internal: the peeling ranks do not go down along a step"
  else
    match left.head? >>= fun x => walkCycle R left (left.length + 1) [x] with
    | some c => if stepClosed R c then .ok (some c) else .error "internal: the cycle does not check"
    | none => .error "internal: no cycle among the elements left"

/-! ## Encoding for the wire -/

def pairExpr (p : String × String) : Expr := .fn "pair" [elemExpr p.1, elemExpr p.2]
def relExpr (R : Rel) : Expr := .fn "rel" [setExpr R.elems, .fn "set" (R.pairs.map pairExpr)]
def partitionExpr (cs : List (List String)) : Expr := .fn "set" (cs.map setExpr)

end Ord
end MathEngine
