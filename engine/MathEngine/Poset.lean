import MathEngine.Print
/-!
# The order-theory world: finite posets

A third little language in the engine: finite partial orders given by their elements and a
relation, with the vocabulary of the order-theory book — Hasse diagrams (covers), upper and lower
bounds, join and meet, lattices, top and bottom, monotone maps given as tables, and least and
greatest fixed points of monotone maps computed by iterating from ⊥ and ⊤ (the Kleene chain, which
is the derivation shown). Everything is a decision over lists, and `PosetProofs.lean` proves the
decisions right: the partial-order check, the covers, join as the least upper bound, and that the
iteration from ⊥ stops at the least fixed point.

Values are encoded into `Expr` for the wire (`fn "set" [...]`, elements as `var`/`num`), so the
notebook's machinery applies; the notebook draws the Hasse diagram from the covers.
-/
namespace MathEngine
namespace Ord

/-- A finite poset: its elements (each once) and its order as a list of pairs, reflexive and
transitively closed by construction (`mk`). -/
structure Poset where
  elems : List String
  le : List (String × String)
  deriving Repr, Inhabited

def Poset.rel (P : Poset) (x y : String) : Bool := P.le.contains (x, y)
def Poset.lt (P : Poset) (x y : String) : Bool := P.rel x y && x != y

/-- Reflexive-transitive closure of `gen` over `elems` (a fixed number of rounds suffices). -/
def closure (elems : List String) (gen : List (String × String)) : List (String × String) :=
  let refl := elems.map fun x => (x, x)
  let start := (refl ++ gen).eraseDups
  go elems.length start
where
  go : Nat → List (String × String) → List (String × String)
    | 0, r => r
    | n + 1, r =>
      let r' := (r ++ r.flatMap fun (a, b) => r.filterMap fun (c, d) => if b == c then some (a, d) else none).eraseDups
      if r'.length == r.length then r else go n r'

/-- Reflexive, antisymmetric, transitive over `elems`; the witness of a failure otherwise. -/
def checkPartialOrder (P : Poset) : Option String :=
  if let some x := P.elems.find? (fun x => !P.rel x x) then some s!"not reflexive: {x} ≤ {x} fails" else
  if let some (x, y) := P.le.find? (fun (x, y) => x != y && P.rel y x) then some s!"not antisymmetric: {x} ≤ {y} and {y} ≤ {x} with {x} ≠ {y}" else
  if let some ((x, y), (_, z)) := (P.le.flatMap fun p => P.le.map fun q => (p, q)).find? (fun ((x, y), (y', z)) => y == y' && !P.rel x z)
    then some s!"not transitive: {x} ≤ {y} ≤ {z} but not {x} ≤ {z}" else
  none

/-- Build a poset from a generating relation, or report why it is not a partial order. -/
def mk (elems : List String) (gen : List (String × String)) : Except String Poset :=
  let elems := elems.eraseDups
  if let some (x, y) := gen.find? (fun (x, y) => !elems.contains x || !elems.contains y) then
    .error s!"{x} < {y} mentions an element outside the set"
  else
    let P : Poset := ⟨elems, closure elems gen⟩
    match checkPartialOrder P with
    | some why => .error s!"not a partial order: {why}"
    | none => .ok P

/-- `x ⋖ y`: `x < y` with nothing strictly between — the edges of the Hasse diagram. -/
def covers (P : Poset) (x y : String) : Bool :=
  P.lt x y && !P.elems.any fun z => P.lt x z && P.lt z y

def hasse (P : Poset) : List (String × String) :=
  P.elems.flatMap fun x => P.elems.filterMap fun y => if covers P x y then some (x, y) else none

/-- Height of an element: the length of the longest chain below it (for the drawing's layers). -/
def height (P : Poset) (x : String) : Nat := go P.elems.length x
where
  go : Nat → String → Nat
    | 0, _ => 0
    | n + 1, x =>
      let below := P.elems.filter fun z => P.lt z x
      (below.map fun z => go n z + 1).foldl max 0

def upperBounds (P : Poset) (xs : List String) : List String :=
  P.elems.filter fun u => xs.all fun x => P.rel x u
def lowerBounds (P : Poset) (xs : List String) : List String :=
  P.elems.filter fun l => xs.all fun x => P.rel l x

/-- The least upper bound of `xs`, if there is one. -/
def sup (P : Poset) (xs : List String) : Option String :=
  let ubs := upperBounds P xs
  ubs.find? fun u => ubs.all fun v => P.rel u v
def inf (P : Poset) (xs : List String) : Option String :=
  let lbs := lowerBounds P xs
  lbs.find? fun l => lbs.all fun m => P.rel m l

def top (P : Poset) : Option String := P.elems.find? fun t => P.elems.all fun x => P.rel x t
def bottom (P : Poset) : Option String := P.elems.find? fun b => P.elems.all fun x => P.rel b x

/-- A pair without a join or without a meet, if any: the witness that this is not a lattice. -/
def latticeFailure (P : Poset) : Option (String × String × String) :=
  (P.elems.flatMap fun x => P.elems.map fun y => (x, y)).findSome? fun (x, y) =>
    if (sup P [x, y]).isNone then some (x, y, "join") else if (inf P [x, y]).isNone then some (x, y, "meet") else none

/-- Maximal and minimal elements. -/
def maximal (P : Poset) : List String := P.elems.filter fun x => !P.elems.any fun y => P.lt x y
def minimal (P : Poset) : List String := P.elems.filter fun x => !P.elems.any fun y => P.lt y x

/-- The divisors of `n` under divisibility. -/
def divisors (n : Nat) : Except String Poset :=
  if n = 0 then .error "divisors(0) is not finite" else
  let ds := (List.range (n + 1)).filter fun d => d > 0 && n % d == 0
  let elems := ds.map toString
  .ok ⟨elems, ds.flatMap fun a => ds.filterMap fun b => if b % a == 0 then some (toString a, toString b) else none⟩

/-- All subsets of a finite set under inclusion, written `{a,b}`. -/
def subsets (xs : List String) : Poset :=
  let xs := xs.eraseDups
  let pw := xs.foldr (fun x acc => acc ++ acc.map (x :: ·)) [[]]
  let name (s : List String) : String := "{" ++ ",".intercalate (xs.filter (s.contains ·)) ++ "}"
  ⟨pw.map name, pw.flatMap fun a => pw.filterMap fun b => if a.all (b.contains ·) then some (name a, name b) else none⟩

/-- The chain `0 < 1 < … < n-1`. -/
def chain (n : Nat) : Poset :=
  let es := (List.range n).map toString
  ⟨es, (List.range n).flatMap fun a => (List.range n).filterMap fun b => if a ≤ b then some (toString a, toString b) else none⟩

/-! ## Maps -/

/-- A map on a poset, as a table. -/
structure PMap where
  table : List (String × String)
  deriving Repr, Inhabited

def PMap.apply (f : PMap) (x : String) : String := (f.table.lookup x).getD x

/-- A pair `x ≤ y` with `f x ≰ f y`, if any. -/
def monotoneFailure (P : Poset) (f : PMap) : Option (String × String) :=
  P.le.find? fun (x, y) => !P.rel (f.apply x) (f.apply y)

/-- Iterate `f` from `start` until it stops changing (at most `|P|` steps are needed on a finite
chain); the chain itself is returned. -/
def iterate (P : Poset) (f : PMap) (start : String) : List String := go P.elems.length start [start]
where
  go : Nat → String → List String → List String
    | 0, _, acc => acc.reverse
    | n + 1, x, acc =>
      let y := f.apply x
      if y == x then acc.reverse else go n y (y :: acc)

def fixedPoints (P : Poset) (f : PMap) : List String := P.elems.filter fun x => f.apply x == x

/-! ## Encoding for the wire -/

def elemExpr (x : String) : Expr := match x.toNat? with | some n => .num (Q.ofInt n) | none => .var x
def setExpr (xs : List String) : Expr := .fn "set" (xs.map elemExpr)
def posetExpr (P : Poset) : Expr := .fn "poset" [setExpr P.elems, .fn "hasse" (hasse P |>.map fun (a, b) => .fn "covers" [elemExpr a, elemExpr b])]

end Ord
end MathEngine

/-! ## Statements: the order-world's own little parser -/

namespace MathEngine
namespace Ord

inductive Tok where
  | ident (s : String) | lp | rp | lb | rb | comma | semi | lt | arrow | eq | eof
  deriving Repr, BEq, Inhabited

partial def lex (src : String) : Except String (List Tok) := go src.toList []
where
  go : List Char → List Tok → Except String (List Tok)
    | [], acc => .ok (acc.reverse ++ [.eof])
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c == '(' then go cs (.lp :: acc) else if c == ')' then go cs (.rp :: acc)
      else if c == '{' then go cs (.lb :: acc) else if c == '}' then go cs (.rb :: acc)
      else if c == ',' then go cs (.comma :: acc) else if c == ';' then go cs (.semi :: acc)
      else if c == '<' || c == '≤' then go cs (.lt :: acc)
      else if c == '=' then go cs (.eq :: acc)
      else if c == '↦' || c == '→' then go cs (.arrow :: acc)
      else if c == '-' then match cs with | '>' :: r => go r (.arrow :: acc) | _ => .error "expected '->'"
      else if c.isAlphanum || c == '_' then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_' || d == '\''
        go ((c :: cs).drop ds.length) (.ident (String.ofList ds) :: acc)
      else .error s!"unexpected character '{c}' in an order-world cell"

/-- One argument of an order command. -/
inductive Arg where
  | elem (x : String)
  | set (xs : List String)
  | rels (ps : List (String × String))      -- a<b, c<d
  | maps (ps : List (String × String))      -- a->b, c->d
  deriving Repr, Inhabited

/-- `head(arg; arg, …)`: arguments separated by commas, relation lists by `;` or commas after the
first `<`/`->`. Returns the head, the arguments, and the tokens left. -/
partial def parseCall : List Tok → Except String (String × List Arg × List Tok)
  | .ident head :: .lp :: ts => do
    let (args, ts) ← args ts []
    pure (head, args, ts)
  | _ => throw "expected a command: name(…)"
where
  elemOrSet : List Tok → Except String (Arg × List Tok)
    | .ident x :: ts => pure (.elem x, ts)
    | .lb :: ts => do
      let (xs, ts) ← setBody ts []
      pure (.set xs, ts)
    | _ => throw "expected an element or a set"
  setBody : List Tok → List String → Except String (List String × List Tok)
    | .rb :: ts, acc => pure (acc.reverse, ts)
    | .ident x :: .comma :: ts, acc => setBody ts (x :: acc)
    | .ident x :: .rb :: ts, acc => pure ((x :: acc).reverse, ts)
    | _, _ => throw "expected '}' or ',' in a set"
  args : List Tok → List Arg → Except String (List Arg × List Tok)
    | .rp :: ts, acc => pure (acc.reverse, ts)
    | ts, acc => do
      let (a, ts) ← elemOrSet ts
      match ts with
      | .lt :: .ident y :: ts =>
        let x := match a with | .elem x => x | _ => ""
        let (ps, ts) ← pairs .lt ts [(x, y)]
        args ts (.rels ps :: acc)
      | .arrow :: .ident y :: ts =>
        let x := match a with | .elem x => x | _ => ""
        let (ps, ts) ← pairs .arrow ts [(x, y)]
        args ts (.maps ps :: acc)
      | .comma :: ts | .semi :: ts => args ts (a :: acc)
      | .rp :: ts => pure ((a :: acc).reverse, ts)
      | _ => throw "expected ',' or ')' after an argument"
  pairs (sep : Tok) : List Tok → List (String × String) → Except String (List (String × String) × List Tok)
    | .comma :: .ident x :: t :: .ident y :: ts, acc => if t == sep then pairs sep ts ((x, y) :: acc) else throw "mixed relation list"
    | .semi :: .ident x :: t :: .ident y :: ts, acc => if t == sep then pairs sep ts ((x, y) :: acc) else throw "mixed relation list"
    | .rp :: ts, acc => pure (acc.reverse, .rp :: ts)
    | .comma :: ts, acc => pure (acc.reverse, .comma :: ts)
    | .semi :: ts, acc => pure (acc.reverse, .semi :: ts)
    | _, _ => throw "expected the next pair, ',' or ')'"

/-- `[let name =] head(args)`. -/
def parseStmt (src : String) : Except String (Option String × String × List Arg) := do
  let toks ← lex src
  match toks with
  | .ident "let" :: .ident n :: .eq :: ts => do
    let (h, as, rest) ← parseCall ts
    if rest != [.eof] then throw "unexpected input after the command"
    pure (some n, h, as)
  | ts => do
    let (h, as, rest) ← parseCall ts
    if rest != [.eof] then throw "unexpected input after the command"
    pure (none, h, as)

def commands : List String :=
  ["poset", "divisors", "subsets", "chain", "map", "hasse", "join", "meet", "sup", "inf", "upper", "lower",
   "lattice", "top", "bottom", "le", "maximal", "minimal", "monotone", "lfp", "gfp", "fixpoints"]

/-- Is this an order-world cell? Its command (after an optional `let name =`) is one of ours. -/
def isOrderSource (src : String) : Bool :=
  match lex src with
  | .ok (.ident "let" :: .ident _ :: .eq :: .ident h :: .lp :: _) => commands.contains h
  | .ok (.ident h :: .lp :: _) => commands.contains h
  | _ => false

end Ord
end MathEngine
