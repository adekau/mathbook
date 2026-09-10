import MathEngine.Q
/-!
# Expression syntax

Mirrors `packages/reference-ts/src/ast.ts` node for node; `Wire.lean` serializes to the
same JSON. No subtraction/division/negation constructors — fewer cases in every proof:
`a - b` is `add [a, mul [-1, b]]`, `a / b` is `mul [a, pow b (-1)]`, `-a` is `mul [-1, a]`.
The printer recovers the human notation.
-/
namespace MathEngine

inductive Expr where
  | num    : Q → Expr
  | var    : String → Expr
  | add    : List Expr → Expr
  | mul    : List Expr → Expr
  | pow    : Expr → Expr → Expr
  | fn     : String → List Expr → Expr
  | matrix : List (List Expr) → Expr
  deriving Repr, Inhabited

/-- A path from the root to a subterm: child indices. `[]` is the root. -/
abbrev Path := List Nat

namespace Expr

def zero : Expr := .num Q.zero
def one : Expr := .num Q.one
def minusOne : Expr := .num Q.minusOne
def ofInt (n : Int) : Expr := .num (Q.ofInt n)
def neg (a : Expr) : Expr := .mul [minusOne, a]
def sub (a b : Expr) : Expr := .add [a, neg b]
def div (a b : Expr) : Expr := .mul [a, .pow b minusOne]
/-- `add` with the reference's convention: a one-element sum is that element. -/
def addN : List Expr → Expr | [e] => e | es => .add es
def mulN : List Expr → Expr | [e] => e | es => .mul es

def isNum : Expr → Bool | .num _ => true | _ => false
def isNumEq (e : Expr) (q : Q) : Bool := match e with | .num v => v.eq q | _ => false
def isZero (e : Expr) : Bool := match e with | .num v => v.isZero | _ => false
def isOne (e : Expr) : Bool := match e with | .num v => v.isOne | _ => false
def isMatrix : Expr → Bool | .matrix _ => true | _ => false

/-- Children in path order. A matrix's children are its entries, row-major. -/
def children : Expr → List Expr
  | .num _ | .var _ => []
  | .add es | .mul es | .fn _ es => es
  | .pow b e => [b, e]
  | .matrix rows => rows.flatten

/-- Cut `cs` into rows of the same lengths as `rows` (the inverse of `List.flatten` for that shape). -/
def regroup : List (List Expr) → List Expr → List (List Expr)
  | [], _ => []
  | r :: rs, cs => cs.take r.length :: regroup rs (cs.drop r.length)

theorem flatten_regroup (rows : List (List Expr)) (cs : List Expr) (h : cs.length = rows.flatten.length) :
    (regroup rows cs).flatten = cs := by
  induction rows generalizing cs with
  | nil => simp at h; simp [regroup, h]
  | cons r rs ih =>
    simp only [List.flatten_cons, List.length_append] at h
    simp only [regroup, List.flatten_cons]
    rw [ih (cs.drop r.length) (by rw [List.length_drop]; omega), List.take_append_drop]

/-- Rebuild a node around new children (same count and order as `children`). -/
def withChildren (e : Expr) (cs : List Expr) : Expr :=
  match e with
  | .num _ | .var _ => e
  | .add _ => .add cs
  | .mul _ => .mul cs
  | .fn f _ => .fn f cs
  | .pow _ _ => match cs with | [b, x] => .pow b x | _ => e
  | .matrix rows => .matrix (regroup rows cs)

theorem children_withChildren (e : Expr) (cs : List Expr) (h : cs.length = (children e).length) :
    children (withChildren e cs) = cs := by
  cases e with
  | pow b x =>
    simp only [children, List.length_cons, List.length_nil] at h
    match cs, h with
    | [b', x'], _ => rfl
  | matrix rows => simp only [withChildren, children] at h ⊢; exact flatten_regroup rows cs h
  | _ => simp_all [withChildren, children]

def at? (e : Expr) : Path → Option Expr
  | [] => some e
  | i :: rest => do let c ← (children e)[i]?; c.at? rest

mutual
  /-- Number of nodes. -/
  def size : Expr → Nat
    | .num _ | .var _ => 1
    | .add es | .mul es | .fn _ es => 1 + sizeList es
    | .pow b e => 1 + b.size + e.size
    | .matrix rows => 1 + sizeRows rows
  def sizeList : List Expr → Nat
    | [] => 0
    | e :: es => e.size + sizeList es
  def sizeRows : List (List Expr) → Nat
    | [] => 0
    | r :: rs => sizeList r + sizeRows rs
end

theorem sizeList_append (l₁ l₂ : List Expr) : sizeList (l₁ ++ l₂) = sizeList l₁ + sizeList l₂ := by
  induction l₁ with
  | nil => simp [sizeList]
  | cons e es ih => simp [sizeList, ih]; omega

theorem sizeRows_flatten (rows : List (List Expr)) : sizeRows rows = sizeList rows.flatten := by
  induction rows with
  | nil => simp [sizeRows, sizeList]
  | cons r rs ih => simp [sizeRows, sizeList_append, ih]

theorem size_eq (e : Expr) : size e = 1 + sizeList (children e) := by
  cases e <;> simp [size, children, sizeList, sizeRows_flatten] <;> omega

theorem size_pos (e : Expr) : 0 < size e := by rw [size_eq]; omega
theorem sizeList_children_lt (e : Expr) : sizeList (children e) < size e := by rw [size_eq]; omega

def freeVars : Expr → List String
  | .num _ => []
  | .var x => [x]
  | .add es | .mul es | .fn _ es => freeVarsList es
  | .pow b e => freeVars b ++ freeVars e
  | .matrix rows => freeVarsRows rows
where
  freeVarsList : List Expr → List String
    | [] => []
    | e :: es => freeVars e ++ freeVarsList es
  freeVarsRows : List (List Expr) → List String
    | [] => []
    | r :: rs => freeVarsList r ++ freeVarsRows rs

def dependsOn (e : Expr) (x : String) : Bool := (freeVars e).contains x

/-- Numbers first, then variables, then compound terms — `KIND_RANK` in `ast.ts`. -/
def kindRank : Expr → Nat
  | .num _ => 0 | .var _ => 1 | .pow _ _ => 2 | .fn _ _ => 3 | .mul _ => 4 | .add _ => 5 | .matrix _ => 6

/-- A total order on expressions (the canonical argument order). -/
partial def compare (a b : Expr) : Ordering :=
  match Ord.compare (kindRank a) (kindRank b) with
  | .eq =>
    match a, b with
    | .num p, .num q => p.cmp q
    | .var x, .var y => Ord.compare x y
    | .pow b1 e1, .pow b2 e2 => (compare b1 b2).then (compare e1 e2)
    | .fn f xs, .fn g ys => (Ord.compare f g).then (compareList xs ys)
    | .add xs, .add ys | .mul xs, .mul ys => compareList xs ys
    | .matrix r1, .matrix r2 => compareList r1.flatten r2.flatten
    | _, _ => .eq
  | o => o
where
  compareList : List Expr → List Expr → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs, y :: ys => (compare x y).then (compareList xs ys)

def equal (a b : Expr) : Bool := compare a b == .eq
instance : BEq Expr := ⟨equal⟩

end Expr
end MathEngine
