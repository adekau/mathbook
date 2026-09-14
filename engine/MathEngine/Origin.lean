import MathEngine.Rewrite
import MathEngine.SimpRules
/-!
# Origin tracking (M6)

Which steps of a derivation produced the subterm the user is pointing at? The M1–M5 answer compared
paths in the *final* term with the paths where rules fired, which is wrong as soon as a rewrite moves
a subterm (sorting, distributing, the product rule copying a factor). This file traces a position
backwards through the derivation instead, after van Deursen, Klint and Tip, *Origin tracking* (1993):

* a position outside a step's redex is its own origin — the rewrite did not touch it
  (`at?_replaceAt_disjoint` is the theorem that makes skipping such steps sound);
* a position inside the contractum originates at the positions of structurally equal subterms of the
  redex (the rule copied it there);
* a position inside the contractum with no such subterm was **created** by the step; its compound
  children are traced on, so the history of a created node is the history of its parts;
* a position that contains the redex is unchanged as a node but rewritten below (`contains`).

Between two recorded steps the rewriter may also have reordered or flattened arguments silently
(`simp.sort`, `simp.flatten`); those gaps are bridged by the same matching over the whole term, with
equality taken modulo exactly those two changes (`canonDeep`). Matching by equality (up to the argument order `canon` may change) is
ambiguous when a term has equal subterms in several places, so origins are *sets* of positions;
the trace then reports every step any of them passed through. That is the one over-approximation
left, and it is the same one the paper's "secondary origins" accept.
-/
namespace MathEngine
open Expr

/-- Neither path is a prefix of the other: the two positions are in separate subtrees. -/
def Disjoint (p q : Path) : Prop := ¬ p.IsPrefix q ∧ ¬ q.IsPrefix p

theorem at?_cons (e : Expr) (j : Nat) (q : Path) : e.at? (j :: q) = ((children e)[j]?).bind fun c => c.at? q := rfl

/-- **A rewrite at `p` leaves every position disjoint from `p` unchanged.** This is what lets the
tracer skip a step without looking at the term. -/
theorem at?_replaceAt_disjoint (new : Expr) : ∀ (e : Expr) (p q : Path), Disjoint p q →
    (replaceAt e p new).at? q = e.at? q
  | e, [], q, h => absurd (List.nil_prefix) h.1
  | e, i :: p, [], h => absurd (List.nil_prefix) h.2
  | e, i :: p, j :: q, h => by
    simp only [replaceAt]
    split
    · rename_i c hc
      have hlen : ((children e).set i (replaceAt c p new)).length = (children e).length := List.length_set ..
      rw [at?_cons, at?_cons, children_withChildren e _ hlen, List.getElem?_set]
      by_cases hij : i = j
      · subst hij
        have hd : Disjoint p q :=
          ⟨fun hp => h.1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩), fun hq => h.2 (List.cons_prefix_cons.mpr ⟨rfl, hq⟩)⟩
        have hi : i < (children e).length := (List.getElem?_eq_some_iff.mp hc).1
        simp only [hi, ↓reduceIte, hc]
        exact at?_replaceAt_disjoint new c p q hd
      · simp only [hij, ↓reduceIte]
    · rfl

/-- The representative of a term up to what the rewriter changes *silently* — argument order
(`simp.sort`) and nesting of sums in sums and products in products (`simp.flatten`), the two rules
that leave no `Step`. Two terms with the same `canonDeep` are the same term to the tracer, which is
exactly the invariant a silent rule must keep. -/
partial def canonDeep (e : Expr) : Expr :=
  match withChildren e ((children e).map canonDeep) with
  | .add es => canon (.add (es.flatMap unAdd))
  | .mul es => canon (.mul (es.flatMap unMul))
  | e' => canon e'

/-- Positions at or below `root` in `t` whose subterm equals `sub` up to argument order. -/
partial def occurrences (t : Expr) (sub : Expr) (root : Path := []) : List Path :=
  let target := canonDeep sub
  let rec go (root : Path) : List Path :=
    match t.at? root with
    | none => []
    | some here =>
      let below := (children here).zipIdx.flatMap fun x => go (root ++ [x.2])
      if equal (canonDeep here) target then root :: below else below
  go root

/-- How a step relates to a position it was asked about. -/
inductive Relation where
  | created   -- the node at the position was built by the rule
  | copied    -- the rule moved or duplicated it into the contractum
  | contains  -- the rule fired strictly below the node
  deriving Repr, BEq

def Relation.toString : Relation → String
  | .created => "created" | .copied => "copied" | .contains => "contains"

/-- Origins of position `q` in `after` for the step that rewrote `before` at `p`, with the relation
if the step touched the position. `none` origins: the node was created. -/
def originsOfStep (before after : Expr) (p q : Path) : Option (List Path) × Option Relation :=
  if p.isPrefixOf q then
    match after.at? q with
    | none => (some [], none)
    | some sub =>
      match occurrences before sub p with
      | [] => (none, some .created)
      | occ => (some occ, some .copied)
  else if q.isPrefixOf p then (some [q], some .contains)
  else (some [q], none)

/-- Positions in `src` of subterms equal to the one at `q` in `dst` (bridging a silent reordering). -/
def originsAcross (src dst : Expr) (q : Path) : List Path :=
  match dst.at? q with
  | none => []
  | some sub => occurrences src sub

/-- One recorded step. -/
structure StepInfo where
  before : Expr
  after : Expr
  path : Path
  deriving Inhabited

/-- Trace positions `qs` (in `after` of step `i`, or in `output`) back through steps `0..i`,
collecting `(step index, relation)` pairs. `fuel` bounds the work per step (a created node's
children are traced on, so the set can grow). -/
abbrev Acc := List Path × List (Nat × Relation)

/-- Fold one position of `after` through step `i`: its origins in `before`, and the relation. A created
node contributes its children's origins instead. -/
def stepOne (st : StepInfo) (i : Nat) (acc : Acc) (q : Path) : Acc :=
  let (o, r) := originsOfStep st.before st.after st.path q
  let rs := match r with | some rel => (i, rel) :: acc.2 | none => acc.2
  match o with
  | some ps => (acc.1 ++ ps, rs)
  | none =>
    -- a created node's compound parts have their own history; a variable or numeral inside it does
    -- not (every `x` was copied from somewhere, and saying so explains nothing)
    let kids : List Path := match st.after.at? q with
      | some sub => (children sub).zipIdx.filterMap fun x =>
          match x.1 with | .num _ | .var _ => none | _ => some (q ++ [x.2])
      | none => []
    kids.foldl (init := (acc.1, rs)) fun (a : Acc) k =>
      match originsOfStep st.before st.after st.path k with
      | (some ps, rk) => (a.1 ++ ps, match rk with | some rel => (i, rel) :: a.2 | none => a.2)
      | (none, _) => a

/-- Trace positions `qs` (in `after` of step `i - 1`) back through steps `0..i-1`, collecting
`(step index, relation)` pairs. -/
partial def traceBack (steps : Array StepInfo) : Nat → List Path → List (Nat × Relation) → List (Nat × Relation)
  | 0, _, acc => acc
  | i + 1, qs, acc =>
    let st := steps[i]!
    let folded : Acc := qs.foldl (init := (([] : List Path), ([] : List (Nat × Relation)))) (stepOne st i)
    let origins := folded.1.eraseDups
    let acc := acc ++ folded.2.reverse.eraseDups
    if i = 0 then acc else
    -- bridge the silent reordering between step (i-1).after and step i.before
    let prev := steps[i - 1]!
    let bridged := (origins.flatMap fun q => originsAcross prev.after st.before q).eraseDups
    traceBack steps i bridged acc

/-- The steps that produced the subterm at `q` in the term after step `k` (or the output when `k`
is `steps.size`), each with how. -/
def trace (steps : Array StepInfo) (output : Expr) (k : Nat) (q : Path) : List (Nat × Relation) :=
  if steps.isEmpty then [] else
  if k ≥ steps.size then
    -- the output may differ from the last step's `after` by a silent reordering
    let start := originsAcross steps[steps.size - 1]!.after output q
    traceBack steps steps.size start.eraseDups []
  else traceBack steps (k + 1) [q] []

end MathEngine
