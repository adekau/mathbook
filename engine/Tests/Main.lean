import MathEngine
/-!
# Engine tests (`lake test`)

The cases were ported from the TypeScript reference engine's `engine.test.mjs` (deleted in M2, commit
c18b367); `Tests/golden.tsv` holds its answers on a larger corpus. Each `check` compares a string;
failures are listed and the exit code is 1.
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

/-- Substring test, for assertions that should not depend on JSON field order. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def qParse (s : String) : Q := (Q.parse s).getD default

-- --- step 4: a stateful session for the engine tests -------------------------------------------
/-- Evaluate in a persistent session through the RPC surface; returns the rendered text or the error. -/
def sessionEval (st : Store) (src : String) (extra := "") : Store × String :=
  let esc := src.replace "\\" "\\\\" |>.replace "\"" "\\\""
  let (st, raw) := handleS st s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"t\",\"cellId\":\"{esc}\",\"source\":\"{esc}\"{extra}}}"
  match Json.parse raw with
  | .ok j =>
    match j.get? "result" >>= (·.get? "rendered") >>= (·.getStr? "text") with
    | some t => (st, t)
    | none => match j.get? "result" >>= (·.get? "error") >>= (·.getStr? "message") with
      | some m => (st, s!"<error: {m}>")
      | none => match j.get? "error" >>= (·.getStr? "message") with
        | some m => (st, s!"<rpc error: {m}>")
        | none => (st, s!"<unexpected: {raw}>")
  | .error m => (st, s!"<bad json: {m}>")

/-- Rule names of a cell's derivation (needs `showWork`). -/
def derivationRules (st : Store) (src : String) : List String :=
  match (st.get "t").cells.lookup src with
  | some cell => cell.derivation.steps.toList.map (·.rule)
  | none => []

-- --- step 2: the traced rewriter ---------------------------------------------------------
/-- A toy verified rule: a one-element sum or product is that element. Under unit weights the
node it removes weighs 1, so the obligation is immediate. -/
def unwrap : Rule unitWeights where
  name := "test.unwrap"
  apply e := match e with
    | .add [x] => some ⟨x, "A sum of one term is that term.", none, none⟩
    | .mul [x] => some ⟨x, "A product of one factor is that factor.", none, none⟩
    | _ => none
  decreasing e r h := by
    cases e with
    | add es => match es, h with
      | [x], h => simp at h; subst h; simp only [MathEngine.measure, MathEngine.measureList, unitWeights]; omega
    | mul es => match es, h with
      | [x], h => simp at h; subst h; simp only [MathEngine.measure, MathEngine.measureList, unitWeights]; omega
    | _ => simp at h

def unwrapP : PlainRule := { name := "test.unwrap", apply := unwrap.apply }

def showSteps (d : Derivation) : String :=
  ", ".intercalate (d.steps.toList.map fun s => s!"{s.rule}@{s.path} {s.before.toText} -> {s.after.toText}")

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
  -- step 2: normalize records whole-term before/after and the path; innermost order
  let x := Expr.var "x"; let y := Expr.var "y"
  let d := derive [unwrap] (.add [x, .add [y]])
  check "rewrite: one step" (showSteps d) "test.unwrap@[1] x + (y) -> x + y"
  check "rewrite: output" d.output.toText "x + y"
  let d2 := derive [unwrap] (.mul [.add [.add [x]]])
  check "rewrite: innermost, three steps" (showSteps d2)
    "test.unwrap@[0, 0] (x) -> (x), test.unwrap@[0] (x) -> x, test.unwrap@[] x -> x"
  check "rewrite: canonical order is silent" (derive [unwrap] (.add [y, x])).output.toText "x + y"
  check "rewrite: sums ordered by degree" (derive [unwrap] (.add [.ofInt 1, .pow x (.ofInt 2), .mul [.ofInt 3, x]])).output.toText "x^2 + 3*x + 1"
  check "rewrite: fuel exhausted" (match (normalizeFuel [unwrapP] 0 (.add [x])).run' #[] with | .ok e => e.toText | .error _ => "exhausted") "exhausted"
  check "rewrite: fuel sufficient" (match (normalizeFuel [unwrapP] 5 (.mul [.add [.add [x]]])).run' #[] with | .ok e => e.toText | .error _ => "exhausted") "x"
  -- step 3: simplify (rendered text after normalization, as the reference tests do)
  let simp (src : String) : String := match parse src with
    | .ok e => (simplify0 e).toText
    | .error err => s!"<syntax error: {err.message}>"
  check "simp 2 + 3*4" (simp "2 + 3*4") "14"
  check "simp -2^2" (simp "-2^2") "-4"
  check "simp (-2)^2" (simp "(-2)^2") "4"
  check "simp 2^3^2" (simp "2^3^2") "512"
  check "simp 8/2/2" (simp "8/2/2") "2"
  check "simp a - b - c" (simp "a - b - c") "a - b - c"
  check "simp 2x + 3x" (simp "2x + 3x") "5*x"
  check "simp 2(x+1)" (simp "2(x+1)") "2*(x + 1)"
  check "simp sin(0)" (simp "sin(0)") "0"
  check "simp x/(y*z)" (simp "x/(y*z)") "x/(y*z)"
  check "simp (x+1)/(x-1)" (simp "(x+1)/(x-1)") "(x + 1)/(x - 1)"
  check "simp 1/x" (simp "1/x") "1/x"
  check "simp -(-x)" (simp "-(-x)") "x"
  check "simp sqrt(2)" (simp "sqrt(2)") "sqrt(2)"
  check "simp 0*x + 1*y" (simp "0*x + 1*y") "y"
  check "simp x - x" (simp "x - x") "0"
  check "simp x*x*x" (simp "x*x*x") "x^3"
  check "simp x^2 * x^3 / x" (simp "x^2 * x^3 / x") "x^4"
  check "simp (x^2)^3" (simp "(x^2)^3") "x^6"
  check "simp sqrt(16)" (simp "sqrt(16)") "4"
  check "simp ln(exp(x))" (simp "ln(exp(x))") "x"
  check "simp 1/2 + 1/3" (simp "1/2 + 1/3") "5/6"
  check "simp x^2 + 3x + 1 order" (simp "1 + 3x + x^2") "x^2 + 3*x + 1"
  check "simp x + 2x + y" (simp "x + 2x + y") "3*x + y"
  check "simp x*0.5*2" (simp "x*0.5*2") "x"  -- 0.5*2 folds to an approximate 1, which isOne drops (same as the reference)
  checkTrue "simp canonical order" (match parse "x*2 + y", parse "y + 2*x" with
    | .ok a, .ok b => Expr.equal (simplify0 a) (simplify0 b) | _, _ => false)
  let d := match parse "0*x + 1*y" with | .ok e => derive simpRules e | .error _ => default
  check "simp derivation rules" (", ".intercalate (d.steps.toList.map (·.rule))) "simp.identity, simp.identity, simp.identity"
  check "simp derivation before/after" (showSteps d) "simp.identity@[0] 0*x + 1*y -> 0 + 1*y, simp.identity@[1] 0 + 1*y -> 0 + y, simp.identity@[] y + 0 -> y"  -- canonical order (constants last) is silent
  -- step 4: diff, linalg, session, show work, explain (through the stateful RPC surface)
  let mut st : Store := []
  let ev (st : Store) (src : String) : Store × String := sessionEval st src
  let mut r := ""
  (st, r) := ev st "diff(x^3, x)"; check "diff x^3" r "3*x^2"
  (st, r) := ev st "diff(5, x)"; check "diff 5" r "0"
  (st, r) := ev st "diff(sin(x^2), x)"; check "diff sin(x^2)" r "2*x*cos(x^2)"
  (st, r) := ev st "diff(x*sin(x), x)"; check "diff x sin x" r "x*cos(x) + sin(x)"
  (st, r) := ev st "diff(2^x, x)"; check "diff 2^x" r "2^x*ln(2)"
  (st, r) := ev st "diff(x^x, x)"; check "diff x^x" r "x^x*(ln(x) + 1)"
  (st, r) := ev st "diff(x^3, x, 2)"; check "diff x^3 twice" r "6*x"
  (st, r) := ev st "diff(ln(x), x)"; check "diff ln x" r "1/x"
  (st, r) := ev st "expand((x+1)^3)"; check "expand (x+1)^3" r "x^3 + 3*x^2 + 3*x + 1"
  (st, r) := ev st "[1,2;3,4] * [5,6;7,8]"; check "la mul" r "[19, 22; 43, 50]"
  (st, r) := ev st "det([1,2;3,4])"; check "la det 2" r "-2"
  (st, r) := ev st "det([2,0,1;1,3,2;1,1,1])"; check "la det 3 zero" r "0"
  (st, r) := ev st "det([1,2,3;4,5,6;7,8,10])"; check "la det 3" r "-3"
  (st, r) := ev st "transpose([1,2,3;4,5,6])"; check "la transpose" r "[1, 4; 2, 5; 3, 6]"
  (st, r) := ev st "rref([1,2,3;4,5,6;7,8,10])"; check "la rref" r "[1, 0, 0; 0, 1, 0; 0, 0, 1]"
  (st, r) := ev st "rref([1,2;2,4])"; check "la rref rank 1" r "[1, 2; 0, 0]"
  (st, r) := ev st "det([a,b;c,d])"; check "la det symbolic" r "a*d - b*c"
  (st, r) := ev st "[1,2] * [1,2]"; check "la dimension error" r "<error: matrix product: 1×2 times 1×2 is undefined (inner dimensions must match)>"
  (st, r) := ev st "let f = x^2 + 3x"; check "session let" r "x^2 + 3*x"
  (st, r) := ev st "diff(f, x)"; check "session diff f" r "2*x + 3"
  (st, r) := ev st "subst(f, x, 2)"; check "session subst" r "10"
  (st, r) := ev st "N(pi)"; check "session N(pi)" r "3.14159265358979"
  (st, r) := ev st "N(sqrt(2))"; check "N sqrt 2" r "1.4142135623731"
  (st, r) := sessionEval st "diff(x^2 * sin(x), x)" ",\"showWork\":true"
  let rules := derivationRules st "diff(x^2 * sin(x), x)"
  checkTrue "show work: diff rules present" (rules.contains "diff.product" && rules.contains "diff.power" && rules.contains "diff.chain") (", ".intercalate rules)
  (st, r) := sessionEval st "rref([1,2;3,4])" ",\"showWork\":true"
  let rr := (st.get "t").cells.lookup "rref([1,2;3,4])"
  check "show work: rref is a command step" ((rr.map fun c => (c.derivation.steps.toList.map (·.rule))).getD []).toString "[cmd.rref]"
  checkTrue "show work: rref sub steps" ((rr.bind fun c => c.derivation.steps[0]? >>= (·.sub)).map (fun d => d.steps.toList.any (·.rule == "la.row-add")) |>.getD false)
  let (st2, raw) := handleS st "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"source\":\"diff(x^3, x)\",\"showWork\":true,\"paths\":true}}"
  checkTrue "show work: latex paths" ((raw.splitOn "\\htmlData{path=1.0}{x}").length > 1) raw
  let (_, exraw) := handleS st2 "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"path\":[1]}}"
  checkTrue "explain: subterm x^2 with diff.power" ((exraw.splitOn "\"text\":\"x^2\"").length > 1 && (exraw.splitOn "diff.power").length > 1) exraw
  -- wire: RPC round trip
  checkTrue "capabilities" ((rpc "engine.capabilities" "{}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"engine\":\"engine-lean\"")
  check "rpc x + 0" (evalText "x + 0") "x"
  checkTrue "rpc derivation" (contains (rpc "engine.evaluate" "{\"source\":\"x + 0\",\"showWork\":true}") "\"derivation\":{\"input\":{\"k\":\"add\",\"args\":[{\"k\":\"var\",\"name\":\"x\"},{\"k\":\"num\",\"v\":{\"num\":\"0\",\"den\":\"1\"}}]},\"steps\":[{\"rule\":\"simp.identity\",\"explanation\":\"$a + 0 = a$: zero is the additive identity.\",\"path\":[],\"before\":{\"k\":\"add\",\"args\":[{\"k\":\"var\",\"name\":\"x\"},{\"k\":\"num\",\"v\":{\"num\":\"0\",\"den\":\"1\"}}]},\"after\":{\"k\":\"var\",\"name\":\"x\"},\"afterRendered\":{\"text\":\"x\",\"latex\":\"x\"}}],\"output\":{\"k\":\"var\",\"name\":\"x\"}}")
  check "rpc syntax error" (evalText "x +") "<error: unexpected end of input>"
  checkTrue "rpc inputRendered" (contains (rpc "engine.evaluate" "{\"source\":\"x + 0\",\"showWork\":true}") "\"inputRendered\":{\"text\":\"x + 0\"")
  checkTrue "rpc ruleStatus" (contains (rpc "engine.capabilities" "{}") "\"rule\":\"simp.collect-powers\",\"status\":\"conditional\"")
  checkTrue "rpc error span" ((rpc "engine.evaluate" "{\"source\":\"3 4\"}").endsWith "\"span\":{\"start\":2,\"end\":3}}}}")
  checkTrue "rpc value json" ((rpc "engine.evaluate" "{\"source\":\"2x\"}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"ok\":true,\"value\":{\"k\":\"mul\",\"args\":[{\"k\":\"num\",\"v\":{\"num\":\"2\",\"den\":\"1\"}},{\"k\":\"var\",\"name\":\"x\"}]}")

/-- M2 golden test: `Tests/golden.tsv` holds the reference engine's rendered text for a corpus of
sources, evaluated in one session in file order (so `let` bindings carry over). It was produced by the
wire-level differential test that ran both engines (`scripts/difftest.mjs`, last present in commit
680e360) with zero mismatches, and it is what stands in for the deleted reference. -/
def goldenTests : TestM Unit := do
  let lines ← (IO.FS.lines "Tests/golden.tsv").toBaseIO >>= fun r => match r with
    | .ok ls => pure ls.toList
    | .error e => do modify (·.push ⟨"golden file", "readable", toString e⟩); pure []
  let mut st : Store := []
  for line in lines do
    match line.splitOn "\t" with
    | [source, expected] =>
      let (st', actual) := sessionEval st source
      st := st'
      check s!"golden: {source}" actual expected
    | _ => pure ()

def main : IO UInt32 := do
  let ((), failures) ← (do tests; goldenTests).run #[]
  for f in failures do
    IO.println s!"FAIL {f.name}\n  expected: {f.expected}\n  actual:   {f.actual}"
  IO.println s!"{failures.size} failures"
  pure (if failures.isEmpty then 0 else 1)
