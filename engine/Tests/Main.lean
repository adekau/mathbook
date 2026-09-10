import MathEngine
/-!
# Engine tests (`lake test`)

The cases are ported from `packages/reference-ts/test/engine.test.mjs`, which is the spec until
M2 deletes it. Each `check` compares a string; failures are listed and the exit code is 1.
-/
open MathEngine

structure Failure where
  name : String
  expected : String
  actual : String

abbrev TestM := StateT (Array Failure) IO

def check (name : String) (actual expected : String) : TestM Unit :=
  if actual == expected then pure () else modify (·.push ⟨name, expected, actual⟩)

def checkTrue (name : String) (b : Bool) (detail := "") : TestM Unit :=
  if b then pure () else modify (·.push ⟨name, "true", if detail.isEmpty then "false" else detail⟩)

/-- Parse and print without simplification. -/
def roundtrip (src : String) : String :=
  match parse src with
  | .ok e => e.toText
  | .error err => s!"<syntax error: {err.message} @{err.start}-{err.stop}>"

def latexOf (src : String) (paths := false) : String :=
  match parse src with
  | .ok e => e.toLatex paths
  | .error err => s!"<syntax error: {err.message}>"

def rpc (method : String) (params : String) : String :=
  handle s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"{method}\",\"params\":{params}}"

/-- Evaluate through the RPC surface and return the rendered text. -/
def evalText (src : String) : String :=
  let raw := rpc "engine.evaluate" s!"\{\"sessionId\":\"t\",\"cellId\":\"c\",\"source\":\"{src}\"}"
  match Json.parse raw with
  | .ok j =>
    match j.get? "result" >>= (·.get? "rendered") >>= (·.getStr? "text") with
    | some t => t
    | none => match j.get? "result" >>= (·.get? "error") >>= (·.getStr? "message") with
      | some m => s!"<error: {m}>"
      | none => s!"<unexpected: {raw}>"
  | .error m => s!"<bad json: {m}>"

def qParse (s : String) : Q := (Q.parse s).getD default

def tests : TestM Unit := do
  -- rational arithmetic is exact and normalized
  check "Q 6/-4" (Q.ofRat (Rat.divInt 6 (-4))).toText "-3/2"
  check "Q 0.125 approx" (qParse "0.125").toText "0.125"
  check "Q 1/8 exact" (Q.ofRat (mkRat 1 8)).toText "1/8"
  check "Q 2.5" (qParse "2.5").toText "2.5"
  check "Q 0.125+0.875" (qParse "0.125" + qParse "0.875").toText "1"
  check "Q 1.5*2" (qParse "1.5" * Q.ofInt 2).toText "3"
  check "Q 1/3+1/6" (Q.ofRat (mkRat 1 3) + Q.ofRat (mkRat 1 6)).toText "1/2"
  check "Q decimal 15 digits" (Q.ofRat (mkRat 314159265358979323 100000000000000000) true).toText "3.14159265358979"
  check "Q decimal small" (Q.ofRat (mkRat 1 1000) true).toText "0.001"
  check "Q decimal big" (Q.ofRat (mkRat 123456789 1) true).toText "123456789"
  check "Q latex frac" (Q.ofRat (mkRat (-1) 2)).toLatex "-\\frac{1}{2}"
  -- parser: precedence and associativity (raw round trips; simplification is step 3)
  check "parse 2 + 3*4" (roundtrip "2 + 3*4") "2 + 3*4"
  check "parse -2^2" (roundtrip "-2^2") "-2^2"
  check "parse (-2)^2" (roundtrip "(-2)^2") "(-2)^2"
  check "parse 2^3^2" (roundtrip "2^3^2") "2^3^2"
  check "parse 8/2/2" (roundtrip "8/2/2") "8/2/2"
  check "parse a - b - c" (roundtrip "a - b - c") "a - b - c"
  -- parser: implicit multiplication and calls
  check "parse 2x^2" (roundtrip "2x^2") "2*x^2"
  check "parse 2(x+1)" (roundtrip "2(x+1)") "2*(x + 1)"
  check "parse x y" (roundtrip "x y") "x*y"
  check "parse sin(0)" (roundtrip "sin(0)") "sin(0)"
  check "parse diff" (roundtrip "diff(x^2, x)") "diff(x^2, x)"
  check "parse unknown call is implicit mul" (roundtrip "f(x)") "f*x"
  check "parse known call" (match parse "f(x)" ["f"] with | .ok e => e.toText | .error _ => "err") "f(x)"
  check "parse 3 4 error" (roundtrip "3 4") "<syntax error: unexpected '4' @2-3>"
  check "parse x + error" (roundtrip "x +") "<syntax error: unexpected end of input @3-3>"
  check "parse pi" (roundtrip "pi") "π"
  check "parse let" (match parseStmt "let f = x^2 + 3x" with | .ok (.«let» n v) => s!"{n} = {v.toText}" | _ => "err") "f = x^2 + 3*x"
  check "parse matrix" (roundtrip "[1,2;3,4]") "[1, 2; 3, 4]"
  check "parse ragged" (roundtrip "[1,2;3]") "<syntax error: ragged matrix rows @0-1>"
  check "parse decimal" (roundtrip "2.5x + .5") "2.5*x + 0.5"
  -- printer: recovers -, /, sqrt and parenthesizes correctly
  check "print x/(y*z)" (roundtrip "x/(y*z)") "x/(y*z)"
  check "print (x+1)/(x-1)" (roundtrip "(x+1)/(x-1)") "(x + 1)/(x - 1)"
  check "print 1/x" (roundtrip "1/x") "1/x"
  check "print -(-x) raw" (roundtrip "-(-x)") "--x"  -- same as printer.ts on the raw tree; simplify gives x
  check "print sqrt(2)" (roundtrip "sqrt(2)") "sqrt(2)"
  check "print x - 2y" (roundtrip "x - 2y") "x - 2*y"
  check "print -x - 1" (roundtrip "-x - 1") "-x - 1"
  check "print 2/3 x" (Expr.toText (.mul [.num (Q.ofRat (mkRat 2 3)), .var "x"])) "2/3*x"
  check "print 1/x^2" (Expr.toText (.pow (.var "x") (.ofInt (-2)))) "1/x^2"
  check "print x^(1/2)" (Expr.toText (.pow (.var "x") (.num (Q.ofRat (mkRat 1 2))))) "sqrt(x)"
  check "latex x/2 + sqrt(y)" (latexOf "x/2 + sqrt(y)") "\\frac{x}{2} + \\sqrt{y}"
  check "latex diff" (latexOf "diff(x^2, x)") "\\frac{d}{dx}\\left({x}^{2}\\right)"
  check "latex greek and mathit" (latexOf "pi * abc") "\\pi \\cdot \\mathit{abc}"
  check "latex matrix" (latexOf "[1,2;3,4]") "\\begin{bmatrix}1 & 2 \\\\ 3 & 4\\end{bmatrix}"
  check "latex paths" (latexOf "x^3" true) "\\htmlData{path=root}{{\\htmlData{path=0}{x}}^{\\htmlData{path=1}{3}}}"
  -- wire: RPC round trip
  checkTrue "capabilities" ((rpc "engine.capabilities" "{}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"engine\":\"engine-lean\"")
  check "rpc x + 0" (evalText "x + 0") "x"
  check "rpc syntax error" (evalText "x +") "<error: unexpected end of input>"
  checkTrue "rpc error span" ((rpc "engine.evaluate" "{\"source\":\"3 4\"}").endsWith "\"span\":{\"start\":2,\"end\":3}}}}")
  checkTrue "rpc value json" ((rpc "engine.evaluate" "{\"source\":\"2x\"}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"ok\":true,\"value\":{\"k\":\"mul\",\"args\":[{\"k\":\"num\",\"v\":{\"num\":\"2\",\"den\":\"1\"}},{\"k\":\"var\",\"name\":\"x\"}]}")

def main : IO UInt32 := do
  let ((), failures) ← tests.run #[]
  for f in failures do
    IO.println s!"FAIL {f.name}\n  expected: {f.expected}\n  actual:   {f.actual}"
  IO.println s!"{failures.size} failures"
  pure (if failures.isEmpty then 0 else 1)
