import MathEngine.Print
/-!
# The λ-calculus world

A second little language inside the same engine: untyped λ-terms with named variables, reduced in
normal order one β-step at a time, each step recorded like the rewriter's. Terms are *encoded* into
`Expr` for the wire (`fn "λ" [var x, body]`, `fn "@" [f, a]`), so the notebook's selection,
explanation and origin tracking work unchanged; the printer knows the two heads. The de Bruijn view
is computed alongside every step (`toDB`), so the notebook's toggle is a rendering, not a
recomputation. Definitions (`name := term`, with the Church library preloaded) are unfolded first,
as one δ-step.

Reduction is on fuel — the one budget in the engine, and the honest one: whether a term has a
normal form is undecidable, so a term that has not reached one after `maxSteps` β-steps is refused
with what it has become so far. The parts that are proved are in `LambdaProofs.lean`.
-/
namespace MathEngine
namespace Lam

/-- Named terms. -/
inductive Term where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq, Inhabited

/-- De Bruijn terms; a free variable keeps its name. -/
inductive DB where
  | bvar : Nat → DB
  | free : String → DB
  | lam : DB → DB
  | app : DB → DB → DB
  deriving Repr, DecidableEq, Inhabited

open Term

def freeVars : Term → List String
  | .var x => [x]
  | .lam x e => (freeVars e).filter (· != x)
  | .app a b => (freeVars a ++ freeVars b).eraseDups

def size : Term → Nat
  | .var _ => 1
  | .lam _ e => 1 + size e
  | .app a b => 1 + size a + size b

/-- A name not in `avoid`, derived from `base`: `x`, `x'`, `x''`, … -/
def freshVar (avoid : List String) (base : String) : String :=
  go base avoid.length
where
  go (cand : String) : Nat → String
    | 0 => cand
    | n + 1 => if cand ∈ avoid then go (cand ++ "'") n else cand

/-- Rename every binder whose name is in `clash` to a fresh name, so that a following substitution
cannot capture. One structural pass with the renaming carried down (`ren`), hence total. -/
def freshen (clash : List String) (ren : List (String × String)) : Term → Term
  | .var w => .var ((ren.lookup w).getD w)
  | .app a b => .app (freshen clash ren a) (freshen clash ren b)
  | .lam y e =>
    let y' := if y ∈ clash then freshVar (clash ++ freeVars e ++ ren.map (·.2)) y else y
    .lam y' (freshen clash ((y, y') :: ren) e)

/-- Capture-free substitution `e[x := s]`, assuming no binder of `e` is free in `s`. -/
def substRaw (x : String) (s : Term) : Term → Term
  | .var y => if y == x then s else .var y
  | .app a b => .app (substRaw x s a) (substRaw x s b)
  | .lam y e => if y == x then .lam y e else .lam y (substRaw x s e)

/-- Capture-avoiding substitution: first rename the binders that would capture, then substitute.
Whether any renaming happened is reported, so the derivation can show the α-step. -/
def subst (x : String) (s : Term) (e : Term) : Term × Bool :=
  let clash := (freeVars s).filter (· != x)
  let e' := freshen clash [] e
  (substRaw x s e', e' != e)

/-- One normal-order β-step: the leftmost-outermost redex. Returns the contractum and whether an
α-renaming preceded it. -/
def betaStep : Term → Option (Term × Bool)
  | .app (.lam x body) arg => some (subst x arg body)
  | .app a b =>
    match betaStep a with
    | some (a', r) => some (.app a' b, r)
    | none => (betaStep b).map fun (b', r) => (.app a b', r)
  | .lam x e => (betaStep e).map fun (e', r) => (.lam x e', r)
  | .var _ => none

/-! ## The de Bruijn view -/

def toDB (ctx : List String := []) : Term → DB
  | .var x => match ctx.idxOf? x with | some i => .bvar i | none => .free x
  | .lam x e => .lam (toDB (x :: ctx) e)
  | .app a b => .app (toDB ctx a) (toDB ctx b)

/-! ## Church encodings -/

def church (n : Nat) : Term :=
  .lam "f" (.lam "x" (go n))
where
  go : Nat → Term
    | 0 => .var "x"
    | k + 1 => .app (.var "f") (go k)

/-- The Church numeral a normal form is, if it is one. -/
def readChurch : Term → Option Nat
  | .lam f (.lam x body) => go f x body
  | _ => none
where
  go (f x : String) : Term → Option Nat
    | .var y => if y == x then some 0 else none
    | .app (.var g) e => if g == f then (go f x e).map (· + 1) else none
    | _ => none

def readBool : Term → Option Bool
  | .lam t (.lam f (.var y)) => if y == t && t != f then some true else if y == f then some false else none
  | _ => none

/-- Unfold definitions: free occurrences of defined names, outermost first; a name that is a
numeral unfolds to its Church numeral. -/
def expandDefs (defs : List (String × Term)) : Term → Term
  | .var x =>
    match defs.lookup x with
    | some t => t
    | none => if x.all Char.isDigit && !x.isEmpty then church x.toNat! else .var x
  | .lam x e => .lam x (expandDefs (defs.filter (·.1 != x)) e)
  | .app a b => .app (expandDefs defs a) (expandDefs defs b)

/-- The library every λ-cell can use: booleans, numerals, pairs, combinators. -/
def churchDefs : List (String × Term) :=
  let t := Term.var
  let l := Term.lam
  let a := Term.app
  [ ("true",  l "t" (l "f" (t "t"))),
    ("false", l "t" (l "f" (t "f"))),
    ("and",   l "p" (l "q" (a (a (t "p") (t "q")) (t "p")))),
    ("or",    l "p" (l "q" (a (a (t "p") (t "p")) (t "q")))),
    ("not",   l "p" (a (a (t "p") (l "t" (l "f" (t "f")))) (l "t" (l "f" (t "t"))))),
    ("if",    l "c" (l "a" (l "b" (a (a (t "c") (t "a")) (t "b"))))),
    ("zero",  church 0),
    ("succ",  l "n" (l "f" (l "x" (a (t "f") (a (a (t "n") (t "f")) (t "x")))))),
    ("add",   l "m" (l "n" (l "f" (l "x" (a (a (t "m") (t "f")) (a (a (t "n") (t "f")) (t "x"))))))),
    ("mul",   l "m" (l "n" (l "f" (a (t "m") (a (t "n") (t "f")))))),
    ("pow",   l "m" (l "n" (a (t "n") (t "m")))),
    ("iszero", l "n" (a (a (t "n") (l "y" (l "t" (l "f" (t "f"))))) (l "t" (l "f" (t "t"))))),
    ("pair",  l "a" (l "b" (l "s" (a (a (t "s") (t "a")) (t "b"))))),
    ("fst",   l "p" (a (t "p") (l "a" (l "b" (t "a"))))),
    ("snd",   l "p" (a (t "p") (l "a" (l "b" (t "b"))))),
    ("id",    l "x" (t "x")),
    ("const", l "x" (l "y" (t "x"))),
    ("K",     l "x" (l "y" (t "x"))),
    ("S",     l "x" (l "y" (l "z" (a (a (t "x") (t "z")) (a (t "y") (t "z")))))),
    ("I",     l "x" (t "x")),
    ("omega", l "x" (a (t "x") (t "x"))),
    ("Y",     l "f" (a (l "x" (a (t "f") (a (t "x") (t "x")))) (l "x" (a (t "f") (a (t "x") (t "x")))))) ]

/-! ## Encoding into `Expr` for the wire -/

def toExpr : Term → Expr
  | .var x => .var x
  | .lam x e => .fn "λ" [.var x, toExpr e]
  | .app a b => .fn "@" [toExpr a, toExpr b]

/-- Decoding, the inverse of `toExpr` on its image. -/
partial def ofExpr : Expr → Option Term
  | .var x => some (.var x)
  | .fn "λ" [.var x, e] => (ofExpr e).map (.lam x)
  | .fn "@" [f, a] => do pure (.app (← ofExpr f) (← ofExpr a))
  | _ => none

def dbToExpr : DB → Expr
  | .bvar n => .num (Q.ofInt n)
  | .free x => .var x
  | .lam e => .fn "λ." [dbToExpr e]
  | .app a b => .fn "@" [dbToExpr a, dbToExpr b]

/-! ## Parsing: `λx y. e`, `\\x. e`, application by juxtaposition, numerals as Church numerals -/

inductive Tok where | lam | dot | lp | rp | ident (s : String) | num (n : Nat) | eof
  deriving Repr, BEq, Inhabited

partial def lex (src : String) : Except String (List Tok) := go src.toList []
where
  go : List Char → List Tok → Except String (List Tok)
    | [], acc => .ok (acc.reverse ++ [.eof])
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c == 'λ' || c == '\\' then go cs (.lam :: acc)
      else if c == '.' then go cs (.dot :: acc)
      else if c == '(' then go cs (.lp :: acc)
      else if c == ')' then go cs (.rp :: acc)
      else if c.isDigit then
        let ds := (c :: cs).takeWhile Char.isDigit
        go ((c :: cs).drop ds.length) (.num ((String.ofList ds).toNat!) :: acc)
      else if c.isAlpha || c == '_' then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_' || d == '\''
        go ((c :: cs).drop ds.length) (.ident (String.ofList ds) :: acc)
      else .error s!"unexpected character '{c}' in a λ-term"

/-- Recursive descent with an explicit fuel (the token list shrinks, but the parser is mutual). -/
partial def parseExpr : List Tok → Except String (Term × List Tok)
  | .lam :: ts => do
    let (names, ts) ← binders ts
    match ts with
    | .dot :: ts =>
      let (body, ts) ← parseExpr ts
      pure (names.foldr (fun x e => .lam x e) body, ts)
    | _ => throw "expected '.' after the λ-binders"
  | ts => parseApp ts
where
  binders : List Tok → Except String (List String × List Tok)
    | .ident x :: ts => do let (xs, ts) ← binders ts; pure (x :: xs, ts)
    | ts => if ts.head? == some .dot then pure ([], ts) else throw "expected a variable after λ"
  parseApp (ts : List Tok) : Except String (Term × List Tok) := do
    let (f, ts) ← atom ts
    loop f ts
  loop (f : Term) : List Tok → Except String (Term × List Tok)
    | ts@(.ident _ :: _) | ts@(.num _ :: _) | ts@(.lp :: _) | ts@(.lam :: _) => do
      let (a, ts') ← if ts.head? == some .lam then parseExpr ts else atom ts
      loop (.app f a) ts'
    | ts => pure (f, ts)
  atom : List Tok → Except String (Term × List Tok)
    | .ident x :: ts => pure (.var x, ts)
    | .num n :: ts => pure (.var (toString n), ts)   -- a numeral is a name, unfolded by the δ-step
    | .lp :: ts => do
      let (e, ts) ← parseExpr ts
      match ts with
      | .rp :: ts => pure (e, ts)
      | _ => throw "expected ')'"
    | .lam :: ts => parseExpr (.lam :: ts)
    | .eof :: _ => throw "unexpected end of the λ-term"
    | _ => throw "unexpected token in the λ-term"

def parseTerm (src : String) : Except String Term := do
  let toks ← lex src
  let (t, rest) ← parseExpr toks
  match rest with
  | [.eof] | [] => pure t
  | _ => throw "unexpected input after the λ-term"

/-- A λ-cell: `name := term`, `let name = term`, or a term. -/
def parseStmt (src : String) : Except String (Option String × Term) := do
  let s := src.trimAscii.copy
  let (name, body) :=
    if s.startsWith "let " then
      let rest := (s.drop 4).trimAscii.copy
      match rest.splitOn "=" with
      | n :: r => (some n.trimAscii.copy, "=".intercalate r)
      | [] => (none, rest)
    else match s.splitOn ":=" with
      | [n, r] => (some n.trimAscii.copy, r)
      | _ => (none, s)
  let t ← parseTerm body
  match name with
  | some n => if n.isEmpty || !(n.all fun c => c.isAlphanum || c == '_' || c == '\'') then throw s!"'{n}' is not a name" else pure (some n, t)
  | none => pure (none, t)

/-- Is this cell a λ-cell? A λ or backslash anywhere, a `:=` definition, or a first word that is a
λ-definition of the session or the Church library. -/
def isLambdaSource (src : String) (defs : List String) : Bool :=
  src.any (fun c => c == 'λ' || c == '\\') || (src.splitOn ":=").length == 2 ||
  (let w := (src.trimAscii.copy.splitOn " ").headD ""
   let w := if w == "let" then "" else w
   defs.contains w && !src.contains '(' || (defs.contains w && src.contains ' '))

def maxSteps : Nat := 1000

/-- Reduce to normal form in normal order, recording every step. The result is the normal form, or
the term after `maxSteps` steps with `false`. -/
def reduce (t : Term) : Term × List (Term × Bool) × Bool := go t maxSteps []
where
  go (t : Term) : Nat → List (Term × Bool) → Term × List (Term × Bool) × Bool
    | 0, acc => (t, acc.reverse, false)
    | n + 1, acc =>
      match betaStep t with
      | none => (t, acc.reverse, true)
      | some (t', renamed) => go t' n ((t', renamed) :: acc)

end Lam
end MathEngine
