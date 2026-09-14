import MathEngine.Expr
/-!
# Printer

Recovers human notation from the minimal AST, mirroring `printer.ts` line for line:

```
add [a, mul [-1, b]]   →  a - b
mul [a, pow b (-1)]    →  a / b     (LaTeX: \frac{a}{b})
mul [-1, a]            →  -a
pow a (1/2)            →  sqrt(a)
```

Every printed subterm knows its `Path`; with `paths := true` the LaTeX output wraps each
subterm in `\htmlData{path=...}{...}`, which KaTeX renders as `<span data-path="0.1">`. That is
how the notebook turns a click into a `Path` for `engine.explain`.
-/
namespace MathEngine
open Expr

/-- What differs between the text and LaTeX outputs. -/
structure Target where
  wrap : Path → String → String
  num : Q → String
  var : String → String
  frac : String → String → String
  pow : String → String → String
  sqrt : String → String
  fn : String → List String → String
  matrix : List (List String) → String
  times : String
  parens : String → String
  /-- Context precedence for a denominator: text needs parens around products (`a/(b*c)`); `\frac` does not. -/
  denomPrec : Nat

-- precedence levels: what the *context* demands vs. what the term *provides*
private def P_ADD := 1
private def P_MUL := 2
private def P_NEG := 2
private def P_POW := 3
private def P_ATOM := 4

def textTarget : Target where
  wrap _ s := s
  num q := q.toText
  var n := n
  frac n d := s!"{n}/{d}"
  pow b e := s!"{b}^{e}"
  sqrt s := s!"sqrt({s})"
  fn n a := let args := ", ".intercalate a; s!"{n}({args})"
  matrix rows := "[" ++ "; ".intercalate (rows.map (", ".intercalate ·)) ++ "]"
  times := "*"
  parens s := s!"({s})"
  denomPrec := P_POW

private def greek : List (String × String) :=
  [("π", "\\pi"), ("alpha", "\\alpha"), ("beta", "\\beta"), ("theta", "\\theta"), ("lambda", "\\lambda")]
private def pathStr (p : Path) : String := if p.isEmpty then "root" else ".".intercalate (p.map toString)

def latexTarget (paths : Bool) : Target where
  wrap p s := if paths then s!"\\htmlData\{path={pathStr p}}\{{s}}" else s
  num q := q.toLatex
  var n := match greek.lookup n with
    | some g => g
    | none => if n.length > 1 then s!"\\mathit\{{n}}" else n
  frac n d := s!"\\frac\{{n}}\{{d}}"
  pow b e := s!"\{{b}}^\{{e}}"
  sqrt s := s!"\\sqrt\{{s}}"
  fn n a :=
    let head := if ["sin", "cos", "tan", "exp", "ln", "log"].contains n then s!"\\{n}" else s!"\\operatorname\{{n}}"
    let args := ", ".intercalate a
    s!"{head}\\left({args}\\right)"
  matrix rows := "\\begin{bmatrix}" ++ " \\\\ ".intercalate (rows.map (" & ".intercalate ·)) ++ "\\end{bmatrix}"
  times := " \\cdot "
  parens s := s!"\\left({s}\\right)"
  denomPrec := P_MUL

/-- Split a term into (coefficient, rest); `rest` keeps the original child paths. `restPathOffset`
is the child index of `rest` inside the term, or `none` when the whole term is the rest. -/
private def enum (l : List α) : List (Nat × α) := (List.range l.length).zip l

private def splitCoeff : Expr → Q × Option Expr × Option Nat
  | .num q => (q, none, none)
  | .mul (.num q :: rest@(_ :: _)) => (q, some (match rest with | [r] => r | rs => .mul rs), some 1)
  | e => (Q.one, some e, none)

mutual
  /-- Print `e` at `path` in a context demanding precedence `ctx`. -/
  partial def print (e : Expr) (path : Path) (T : Target) (ctx : Nat) : String :=
    let (s, prec) := printRaw e path T
    T.wrap path (if prec < ctx then T.parens s else s)

  partial def printRaw (e : Expr) (path : Path) (T : Target) : String × Nat :=
    let child (c : Expr) (i : Nat) (ctx : Nat) := print c (path ++ [i]) T ctx
    match e with
    | .num q => (T.num q, if q.isNeg then P_NEG else P_ATOM)
    | .var x => (T.var x, P_ATOM)
    | .matrix rows =>
      let w := (rows.head?.map List.length).getD 0
      let rs := (enum rows).map fun (r, row) => (enum row).map fun (j, c) => child c (r * w + j) P_ADD
      (T.matrix rs, P_ATOM)
    | .fn name args =>
      let as := (enum args).map fun (i, a) => child a i P_ADD
      match name, args, as with
      | "sqrt", [_], [a] => (T.sqrt a, P_ATOM)
      | "diff", [_, .var _], [a, x] =>
        if T.times != "*" then (s!"\\frac\{d}\{d{x}}\\left({a}\\right)", P_MUL) else (T.fn name as, P_ATOM)
      | "integrate", [_, .var _], [a, x] =>
        if T.times != "*" then (s!"\\int {a} \\, d{x}", P_MUL) else (T.fn name as, P_ATOM)
      | _, _, _ => (T.fn name as, P_ATOM)
    | .pow b x =>
      if x.isNumEq (Q.ofRat (mkRat 1 2)) then (T.sqrt (child b 0 P_ADD), P_ATOM)
      else match x with
      | .num q =>
        if q.isNeg then
          -- standalone x^(-n) → 1/x^n
          let n := q.neg
          let base := child b 0 (if n.isOne then T.denomPrec else P_POW + 1)
          (T.frac (T.num Q.one) (if n.isOne then base else T.pow base (T.wrap (path ++ [1]) (T.num n))), P_MUL)
        else powRaw b x
      | _ => powRaw b x
    | .add args =>
      let s := (enum args).foldl (init := ("" : String)) fun acc (i, a) =>
        let (coeff, rest, restOff) := splitCoeff a
        let negative := coeff.isNeg
        if i == 0 && !negative then acc ++ child a i P_ADD
        else
          let sign := if negative then " - " else " + "
          let termStr :=
            if negative then
              let absC := coeff.neg
              let p := path ++ [i]
              match rest with
              | none => T.wrap p (T.num absC)
              | some r =>
                if absC.isOne then
                  match restOff with
                  | some off => print r (p ++ [off]) T P_MUL
                  | none => print r p T P_MUL
                else T.wrap p (T.num absC ++ T.times ++ print r (p ++ [restOff.getD 0]) T P_MUL)
            else child a i P_MUL
          acc ++ (if i == 0 then sign.trimAscii.copy else sign) ++ termStr
      (s, P_ADD)
    | .mul args =>
      -- Partition into numerator / denominator factors; a leading -1 becomes a unary minus.
      let (sign, numer, denom) := (enum args).foldl (init := (("" : String), ([] : List String), ([] : List String)))
          fun ((sign, numer, denom) : String × List String × List String) ((i, a) : Nat × Expr) =>
        let p := path ++ [i]
        match i, a with
        | 0, .num q => if q.isNeg then (("-" : String), if q.neg.isOne then numer else numer ++ [T.wrap p (T.num q.neg)], denom)
                       else (sign, numer ++ [print a p T (P_MUL + (if i > 0 then 1 else 0))], denom)
        | _, .pow b (.num q) =>
          if q.isNeg then
            let n := q.neg
            let base := print b (p ++ [0]) T (if n.isOne then T.denomPrec else P_POW + 1)
            (sign, numer, denom ++ [T.wrap p (if n.isOne then base else T.pow base (T.wrap (p ++ [1]) (T.num n)))])
          else (sign, numer ++ [print a p T P_MUL], denom)
        | _, _ => (sign, numer ++ [print a p T (P_MUL + (if i > 0 && a.isNum then 1 else 0))], denom)
      let n := if numer.isEmpty then T.num Q.one else T.times.intercalate numer
      if denom.isEmpty then (sign ++ n, if sign.isEmpty then P_MUL else P_NEG)
      else
        let d := if denom.length > 1 && T.denomPrec > P_MUL then T.parens (T.times.intercalate denom) else T.times.intercalate denom
        (sign ++ T.frac n d, if sign.isEmpty then P_MUL else P_NEG)
  where
    powRaw (b x : Expr) : String × Nat :=
      let bs := print b (path ++ [0]) T (P_POW + 1)  -- left of ^ needs parens for anything non-atomic incl. -3 and 2^3
      let xs := print x (path ++ [1]) T P_POW        -- right-assoc: 2^3^4 is 2^(3^4)
      (T.pow bs xs, P_POW)
end

def Expr.toText (e : Expr) : String := print e [] textTarget P_ADD
def Expr.toLatex (e : Expr) (paths := false) : String := print e [] (latexTarget paths) P_ADD

end MathEngine
