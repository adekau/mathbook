import MathEngine.Expr
/-!
# Parser

Input language, identical to `parser.ts`:

```
stmt   := 'let' IDENT '=' expr | expr
expr   := term (('+' | '-') term)*
term   := unary (('*' | '/') unary | <implicit> unary)*
unary  := '-' unary | power
power  := atom ('^' unary)?                       -- right-assoc; -x^2 parses as -(x^2)
atom   := NUMBER | IDENT | IDENT '(' expr,* ')' | '(' expr ')' | '[' row (';' row)* ']'
row    := expr (',' expr)*
```

Implicit multiplication (`2x`, `2(x+1)`, `x y`) is allowed when the previous token ends an atom
and the next begins one, except number-after-number (`3 4` is an error). `IDENT (` is a call
only if IDENT is a builtin or a session-known function.
-/
namespace MathEngine

structure ParseError where
  message : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

inductive Stmt where
  | «let» (name : String) (value : Expr)
  | expr (value : Expr)
  deriving Repr, Inhabited

def Stmt.value : Stmt → Expr | .«let» _ v => v | .expr v => v

inductive TokKind where | num | id | op | eof deriving Repr, BEq, Inhabited

structure Tok where
  kind : TokKind
  s : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

def builtinFunctions : List String :=
  ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs",
   "diff", "simplify", "expand", "N", "det", "rref", "transpose", "solve", "subst", "integrate"]

/-- Lexer over the character list; `i` is the byte-free character index used for spans. -/
partial def lex (src : String) : Except ParseError (Array Tok) := go src.toList 0 #[]
where
  isIdStart (c : Char) := c.isAlpha || c == '_'
  isIdChar (c : Char) := c.isAlphanum || c == '_' || c == '\''
  go : List Char → Nat → Array Tok → Except ParseError (Array Tok)
    | [], i, acc => .ok (acc.push ⟨.eof, "", i, i⟩)
    | c :: cs, i, acc =>
      if c.isWhitespace then go cs (i + 1) acc
      else if c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false) then
        -- [0-9]*\.?[0-9]+ | [0-9]+
        let ds := (c :: cs).takeWhile Char.isDigit
        let rest := (c :: cs).drop ds.length
        let (frac, rest) :=
          match rest with
          | '.' :: r => let f := r.takeWhile Char.isDigit; if f.isEmpty then ([], rest) else ('.' :: f, r.drop f.length)
          | _ => ([], rest)
        let text := String.ofList (ds ++ frac)
        go rest (i + text.length) (acc.push ⟨.num, text, i, i + text.length⟩)
      else if isIdStart c then
        let ds := (c :: cs).takeWhile isIdChar
        let text := String.ofList ds
        go ((c :: cs).drop ds.length) (i + ds.length) (acc.push ⟨.id, text, i, i + ds.length⟩)
      else if "+-*/^()[],;=".contains c then go cs (i + 1) (acc.push ⟨.op, c.toString, i, i + 1⟩)
      else .error ⟨s!"unexpected character '{c}'", i, i + 1⟩

structure PS where
  toks : Array Tok
  i : Nat := 0
  known : List String := []

abbrev PM := StateT PS (Except ParseError)

private def peek : PM Tok := do let s ← get; pure (s.toks.getD s.i ⟨.eof, "", 0, 0⟩)
private def prev : PM (Option Tok) := do let s ← get; pure (if s.i = 0 then none else s.toks[s.i - 1]?)
private def next : PM Tok := do let t ← peek; modify fun s => { s with i := s.i + 1 }; pure t
private def isOp (t : Tok) (s : String) : Bool := t.kind == .op && t.s == s
private def fail (msg : String) (t : Tok) : PM α := throw ⟨msg, t.start, t.stop⟩
private def expectOp (s : String) : PM Unit := do
  let t ← next
  if !isOp t s then fail s!"expected '{s}'" t
private def startsAtom (t : Tok) : Bool := t.kind == .num || t.kind == .id || isOp t "(" || isOp t "["
private def isFn (name : String) : PM Bool := do
  let s ← get; pure (builtinFunctions.contains name || s.known.contains name)

mutual
  partial def expr : PM Expr := do
    let mut lhs ← term
    repeat
      let t ← peek
      if isOp t "+" then discard next; lhs := .add [lhs, ← term]
      else if isOp t "-" then discard next; lhs := Expr.sub lhs (← term)
      else break
    pure lhs
  partial def term : PM Expr := do
    let mut lhs ← unary
    repeat
      let t ← peek
      if isOp t "*" then discard next; lhs := .mul [lhs, ← unary]
      else if isOp t "/" then discard next; lhs := Expr.div lhs (← unary)
      else if startsAtom t && !(t.kind == .num && ((← prev).map (·.kind == .num)).getD false) then
        lhs := .mul [lhs, ← unary]   -- implicit multiplication
      else break
    pure lhs
  partial def unary : PM Expr := do
    let t ← peek
    if isOp t "-" then discard next; pure (Expr.neg (← unary)) else power
  partial def power : PM Expr := do
    let b ← atom
    let t ← peek
    if isOp t "^" then discard next; pure (.pow b (← unary)) else pure b
  partial def atom : PM Expr := do
    let t ← next
    match t.kind with
    | .num =>
      match Q.parse t.s with
      | some q => pure (.num q)
      | none => fail s!"bad number '{t.s}'" t
    | .id =>
      if isOp (← peek) "(" && (← isFn t.s) then
        discard next
        let mut args : List Expr := []
        if !isOp (← peek) ")" then
          args := [← expr]
          while isOp (← peek) "," do
            discard next
            args := args ++ [← expr]
        expectOp ")"
        pure (.fn t.s args)
      else if t.s == "pi" then pure (.var "π")
      else pure (.var t.s)
    | .op =>
      if t.s == "(" then
        let e ← expr; expectOp ")"; pure e
      else if t.s == "[" then
        let mut rows : List (List Expr) := []
        repeat
          let mut row := [← expr]
          while isOp (← peek) "," do
            discard next
            row := row ++ [← expr]
          rows := rows ++ [row]
          if isOp (← peek) ";" then discard next else break
        expectOp "]"
        let w := (rows.head?.map List.length).getD 0
        if rows.any (·.length != w) then fail "ragged matrix rows" t
        pure (.matrix rows)
      else fail s!"unexpected '{t.s}'" t
    | .eof => fail "unexpected end of input" t
end

/-- Parse a statement. `known` lists session-defined function names that may be called. -/
def parseStmt (src : String) (known : List String := []) : Except ParseError Stmt := do
  let toks ← lex src
  let body : PM Stmt := do
    let t ← peek
    let stmt ←
      if t.kind == .id && t.s == "let" then
        discard next
        let name ← next
        if name.kind != .id then fail "expected a name after 'let'" name
        expectOp "="
        pure (Stmt.«let» name.s (← expr))
      else pure (Stmt.expr (← expr))
    let t ← peek
    if t.kind != .eof then fail s!"unexpected '{t.s}'" t
    pure stmt
  body.run' { toks, known }

def parse (src : String) (known : List String := []) : Except ParseError Expr :=
  (parseStmt src known).map Stmt.value

end MathEngine
