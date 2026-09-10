/-!
# Minimal JSON

Hand-rolled on purpose: `Lean.Json` lives in `libLean.a` (118 MB in the wasm32 toolchain)
and drags the compiler's initializer chain into the wasm module. This is ~120 lines,
depends only on `Init`, and is a nice small interpreter exercise for the book.
-/
namespace MathEngine

inductive Json where
  | null | bool (b : Bool) | num (s : String) | str (s : String)
  | arr (xs : Array Json) | obj (kvs : Array (String × Json))
  deriving Repr, Inhabited

namespace Json

def get? (j : Json) (k : String) : Option Json :=
  match j with | .obj kvs => (kvs.find? (·.1 == k)).map (·.2) | _ => none
def getStr? (j : Json) (k : String) : Option String :=
  match j.get? k with | some (.str s) => some s | _ => none
def getBool (j : Json) (k : String) (d := false) : Bool :=
  match j.get? k with | some (.bool b) => b | _ => d

private def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | c => if c.val < 32 then s!"\\u{String.mk (Nat.toDigits 16 c.val.toNat)}" else c.toString) ""

partial def render : Json → String
  | .null => "null"
  | .bool b => toString b
  | .num s => s
  | .str s => "\"" ++ escape s ++ "\""
  | .arr xs => "[" ++ ",".intercalate (xs.toList.map render) ++ "]"
  | .obj kvs => "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => "\"" ++ escape k ++ "\":" ++ render v) ++ "}"

-- --- parser -------------------------------------------------------------
structure P where
  s : String
  i : String.Pos := 0

abbrev PM := StateT P (Except String)

private def peek : PM (Option Char) := do let p ← get; pure (if p.i < p.s.endPos then some (p.s.get p.i) else none)
private def adv : PM Unit := modify fun p => { p with i := p.s.next p.i }
private def ws : PM Unit := do
  repeat
    match ← peek with
    | some c => if c.isWhitespace then adv else break
    | none => break
private def expectC (c : Char) : PM Unit := do
  match ← peek with
  | some d => if d == c then adv else throw s!"expected '{c}' got '{d}'"
  | none => throw s!"expected '{c}' got end of input"
private def lit (w : String) (v : Json) : PM Json := do
  for c in w.toList do expectC c
  pure v

private partial def strLit : PM String := do
  expectC '"'
  let rec go (acc : String) : PM String := do
    match ← peek with
    | none => throw "unterminated string"
    | some '"' => adv; pure acc
    | some '\\' =>
      adv
      match ← peek with
      | some 'n' => adv; go (acc.push '\n')
      | some 't' => adv; go (acc.push '\t')
      | some 'r' => adv; go (acc.push '\r')
      | some 'u' =>
        adv
        let mut code := 0
        for _ in [0:4] do
          match ← peek with
          | some h => adv; code := code * 16 + (if h.isDigit then h.toNat - '0'.toNat else h.toLower.toNat - 'a'.toNat + 10)
          | none => throw "bad \\u escape"
        go (acc.push (Char.ofNat code))
      | some c => adv; go (acc.push c)
      | none => throw "bad escape"
    | some c => adv; go (acc.push c)
  go ""

private partial def number : PM Json := do
  let rec go (acc : String) : PM String := do
    match ← peek with
    | some c => if c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' then adv; go (acc.push c) else pure acc
    | none => pure acc
  pure (.num (← go ""))

partial def value : PM Json := do
  ws
  match ← peek with
  | none => throw "unexpected end of input"
  | some '{' =>
    adv; ws
    let mut kvs : Array (String × Json) := #[]
    if (← peek) == some '}' then adv; pure (.obj kvs) else
    repeat
      ws; let k ← strLit; ws; expectC ':'; let v ← value; kvs := kvs.push (k, v); ws
      match ← peek with
      | some ',' => adv
      | some '}' => adv; break
      | _ => throw "expected ',' or '}'"
    pure (.obj kvs)
  | some '[' =>
    adv; ws
    let mut xs : Array Json := #[]
    if (← peek) == some ']' then adv; pure (.arr xs) else
    repeat
      xs := xs.push (← value); ws
      match ← peek with
      | some ',' => adv
      | some ']' => adv; break
      | _ => throw "expected ',' or ']'"
    pure (.arr xs)
  | some '"' => .str <$> strLit
  | some 't' => lit "true" (.bool true)
  | some 'f' => lit "false" (.bool false)
  | some 'n' => lit "null" .null
  | some _ => number

def parse (s : String) : Except String Json := (value.run' { s }).mapError (s!"JSON: {·}")

end Json
end MathEngine
