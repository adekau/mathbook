import MathEngine.Q
/-!
# Expression syntax

Node for node the same tree as the protocol's `WireExpr` (`Wire.lean` serializes to it). No subtraction/division/negation constructors — fewer cases in every proof:
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

mutual
  /-- Structural equality. Written out (rather than derived) so that `beq_eq` can be proved. -/
  def beq : Expr → Expr → Bool
    | .num p, .num q => p == q
    | .var x, .var y => x == y
    | .add xs, .add ys => beqList xs ys
    | .mul xs, .mul ys => beqList xs ys
    | .pow a b, .pow c d => beq a c && beq b d
    | .fn f xs, .fn g ys => f == g && beqList xs ys
    | .matrix r, .matrix s => beqRows r s
    | _, _ => false
  def beqList : List Expr → List Expr → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _, _ => false
  def beqRows : List (List Expr) → List (List Expr) → Bool
    | [], [] => true
    | r :: rs, s :: ss => beqList r s && beqRows rs ss
    | _, _ => false
end

instance : BEq Expr := ⟨beq⟩
def equal (a b : Expr) : Bool := beq a b

/-- Elementwise lifting of a relation on expressions to argument lists. Used to say "these children
were each rewritten soundly", which is the induction hypothesis every congruence proof needs. -/
def RelList (R : Expr → Expr → Prop) : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ RelList R as bs
  | _, _ => False

theorem RelList_length {R : Expr → Expr → Prop} : ∀ {as bs : List Expr}, RelList R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, ⟨_, h⟩ => by simp [RelList_length h]

theorem RelList_refl {R : Expr → Expr → Prop} (h : ∀ e, R e e) : ∀ l : List Expr, RelList R l l
  | [] => trivial
  | e :: es => ⟨h e, RelList_refl h es⟩

mutual
  theorem beq_eq : ∀ a b : Expr, beq a b = true → a = b
    | .num p, b, h => by cases b <;> simp [beq] at h; rw [h]
    | .var x, b, h => by cases b <;> simp [beq] at h; rw [h]
    | .add xs, b, h => by cases b <;> simp [beq] at h; rw [beqList_eq xs _ h]
    | .mul xs, b, h => by cases b <;> simp [beq] at h; rw [beqList_eq xs _ h]
    | .pow a₁ a₂, b, h => by cases b <;> simp [beq] at h; rw [beq_eq a₁ _ h.1, beq_eq a₂ _ h.2]
    | .fn f xs, b, h => by cases b <;> simp [beq] at h; rw [h.1, beqList_eq xs _ h.2]
    | .matrix r, b, h => by cases b <;> simp [beq] at h; rw [beqRows_eq r _ h]
  theorem beqList_eq : ∀ xs ys : List Expr, beqList xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp [beqList] at h; rfl
    | x :: xs, ys, h => by
      cases ys with
      | nil => simp [beqList] at h
      | cons y ys => simp [beqList] at h; rw [beq_eq x y h.1, beqList_eq xs ys h.2]
  theorem beqRows_eq : ∀ rs ss : List (List Expr), beqRows rs ss = true → rs = ss
    | [], ss, h => by cases ss <;> simp [beqRows] at h; rfl
    | r :: rs, ss, h => by
      cases ss with
      | nil => simp [beqRows] at h
      | cons s ss => simp [beqRows] at h; rw [beqList_eq r s h.1, beqRows_eq rs ss h.2]
end

theorem equal_eq {a b : Expr} (h : equal a b = true) : a = b := beq_eq a b h

/-- Remove the first element satisfying `p`. Unlike `List.erase` this needs no lawful `BEq`. -/
def removeFirst (p : Expr → Bool) : List Expr → List Expr
  | [] => []
  | a :: as => if p a then as else a :: removeFirst p as

theorem perm_find?_removeFirst (p : Expr → Bool) : ∀ (l : List Expr) (f : Expr),
    l.find? p = some f → l.Perm (f :: removeFirst p l)
  | [], f, h => by simp at h
  | a :: as, f, h => by
    by_cases hp : p a = true
    · simp [List.find?_cons_of_pos hp] at h; subst h; simp [removeFirst, hp]
    · rw [List.find?_cons_of_neg hp] at h
      simp only [removeFirst, hp, Bool.false_eq_true, ↓reduceIte]
      exact (List.Perm.cons a (perm_find?_removeFirst p as f h)).trans (List.Perm.swap f a _)

end Expr
end MathEngine
