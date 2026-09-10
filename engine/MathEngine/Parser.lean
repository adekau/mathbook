import MathEngine.Expr
/-!
# Parser (spike fragment)

Integers, identifiers, `+ - * ^`, parentheses. Same precedence as `parser.ts`. `a - b`
becomes `a + (-1)*b`. The full grammar (calls, implicit multiplication, matrices) is M1.
-/
namespace MathEngine
open Expr

inductive Tok where | num (n : Int) | id (s : String) | op (c : Char) | eof deriving Repr, BEq, Inhabited

partial def lex (s : String) : Except String (Array Tok) := go s.toList #[]
where
  go : List Char → Array Tok → Except String (Array Tok)
    | [], acc => .ok (acc.push .eof)
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c.isDigit then
        let ds := (c :: cs).takeWhile Char.isDigit
        go ((c :: cs).drop ds.length) (acc.push (.num (String.mk ds).toNat!))
      else if c.isAlpha || c == '_' then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_'
        go ((c :: cs).drop ds.length) (acc.push (.id (String.mk ds)))
      else if "+-*^()".contains c then go cs (acc.push (.op c))
      else .error s!"unexpected character '{c}'"

structure PS where
  toks : Array Tok
  i : Nat := 0
abbrev PM := StateT PS (Except String)
def peek : PM Tok := do let s ← get; pure (s.toks.getD s.i .eof)
def adv : PM Unit := modify fun s => { s with i := s.i + 1 }
def expectOp (c : Char) : PM Unit := do
  if (← peek) == .op c then adv else throw s!"expected '{c}'"

mutual
  partial def expr : PM Expr := do
    let mut lhs ← term
    repeat
      match ← peek with
      | .op '+' => adv; lhs := .add [lhs, ← term]
      | .op '-' => adv; lhs := .add [lhs, .mul [.num ⟨-1, 1⟩, ← term]]
      | _ => break
    pure lhs
  partial def term : PM Expr := do
    let mut lhs ← unary
    repeat
      match ← peek with
      | .op '*' => adv; lhs := .mul [lhs, ← unary]
      | _ => break
    pure lhs
  partial def unary : PM Expr := do
    match ← peek with
    | .op '-' => adv; pure (.mul [.num ⟨-1, 1⟩, ← unary])
    | _ => power
  partial def power : PM Expr := do
    let b ← atom
    match ← peek with
    | .op '^' => adv; pure (.pow b (← unary))
    | _ => pure b
  partial def atom : PM Expr := do
    match ← peek with
    | .num n => adv; pure (.num ⟨n, 1⟩)
    | .id x => adv; pure (.var x)
    | .op '(' => adv; let e ← expr; expectOp ')'; pure e
    | .eof => throw "unexpected end of input"
    | t => throw s!"unexpected {repr t}"
end

def parse (s : String) : Except String Expr := do
  let toks ← lex s
  let (e, st) ← expr.run { toks }
  if st.toks.getD st.i .eof != .eof then throw "trailing input"
  pure e

end MathEngine
