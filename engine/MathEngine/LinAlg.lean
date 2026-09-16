import MathEngine.Order
import MathEngine.Print
import MathEngine.SimpRules
import MathEngine.LinAlgQ
import MathEngine.LinAlgRref
/-!
# `la.*` — matrix arithmetic as rewriting, and Gauss–Jordan elimination as a step-recording algorithm

Ported from `linalg.ts`. Dimension errors refuse the evaluation (`RuleResult.error`), as the
reference throws. `la.context` is the catch-all that refuses a matrix literal in any position no rule
handles, which the M5 termination proof relies on.

`rref` has two paths. A matrix of numerals is reduced by the verified `LinQ.rref` (LinAlgQ.lean):
the row operations it emits are replayed here into steps; `LinQ.sol_rref` says the result has the
same solution set and `LinQ.rref_isRref` that it is in reduced row echelon form. A matrix with symbolic
entries goes through the older step-recording algorithm, whose arithmetic is the simplifier's and whose
pivot choice trusts `simplify` to decide zero-ness; its steps carry the `.symbolic` suffix so the
notebook reports them as unverified.
-/
namespace MathEngine
open Expr

def dims (rows : List (List Expr)) : Nat × Nat := (rows.length, (rows.head?.map List.length).getD 0)
def asMat : Expr → Option (List (List Expr)) | .matrix rows => some rows | _ => none
def refuse (msg : String) : RuleResult := ⟨Expr.zero, "", none, some msg⟩
def entry (rows : List (List Expr)) (i j : Nat) : Expr := ((rows.getD i []).getD j Expr.zero)

/-- Entry `(i, j)` of the product of two literal matrices. -/
def mulEntry (a b : List (List Expr)) (ac i j : Nat) : Expr :=
  .add ((List.range ac).map fun k => .mul [entry a i k, entry b k j])

def matMul (a b : List (List Expr)) : List (List Expr) :=
  let (ar, ac) := dims a
  let bc := (dims b).2
  (List.range ar).map fun i => (List.range bc).map fun j => mulEntry a b ac i j

/-- `rows ^ (k + 1)` as one literal (the product tree is left in the entries). -/
def matPow (rows : List (List Expr)) : Nat → List (List Expr)
  | 0 => rows
  | k + 1 => matMul rows (matPow rows k)

def minor (others : List (List Expr)) (j : Nat) : List (List Expr) :=
  others.map fun row => (row.zipIdx.filter (·.2 != j)).map (·.1)

/-- Determinant by Laplace expansion along the first row, fully expanded; `fuel` bounds the recursion
by the number of rows. -/
def detExpr : Nat → List (List Expr) → Expr
  | _, [[a]] => a
  | _, [[a, b], [c, d]] => Expr.sub (.mul [a, d]) (.mul [b, c])
  | fuel + 1, first :: others =>
    .add (first.zipIdx.map fun (a1j, j) =>
      let sign := if j % 2 == 0 then Expr.one else Expr.minusOne
      .mul [sign, a1j, detExpr fuel (minor others j)])
  | _, _ => Expr.zero

/-- The matrix rules. Every node with a matrix literal as a child is handled here: evaluated when it
is an operation on literals, refused otherwise (`la.context`). That is what lets the termination
proof (`PipelineOrder.lean`) know a normal form contains no literal except possibly at the root. -/
def laAdd : PlainRule :=
  { name := "la.add", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .add es =>
        if !es.any isMatrix then none else
        match es.mapM asMat with
        | some (a :: rest) =>
          let (r, c) := dims a
          if rest.any (fun m => dims m != (r, c)) then some (refuse "matrix addition: dimension mismatch")
          else some ⟨.matrix ((List.range r).map fun i => (List.range c).map fun j => .add (entry a i j :: rest.map (entry · i j))),
            "Matrices of the same shape add entrywise.", none, none⟩
        | _ => some (refuse "cannot add a matrix and a scalar")
      | _ => none }

def laScalarMul : PlainRule :=
  { name := "la.scalar-mul", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .mul es =>
        let mats := es.filter isMatrix
        let scalars := es.filter (fun a => !isMatrix a)
        match mats with
        | [.matrix rows] =>
          if scalars.isEmpty then none
          else
            let s := mulN scalars
            some ⟨.matrix (rows.map (·.map fun x => .mul [s, x])), s!"Scalar multiplication: multiply every entry by ${s.toText}$.", none, none⟩
        | _ => none
      | _ => none }

def laMul : PlainRule :=
  { name := "la.mul", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .mul es =>
        match es.zipIdx.filter (fun p => isMatrix p.1) with
        | (.matrix a, i) :: (.matrix b, j) :: _ =>
          let (ar, ac) := dims a
          let (br, bc) := dims b
          if ac != br then some (refuse s!"matrix product: {ar}×{ac} times {br}×{bc} is undefined (inner dimensions must match)")
          else
            let prod := matMul a b
            let es' := (es.zipIdx.filter (·.2 != j)).map fun (x, k) => if k == i then Expr.matrix prod else x
            some ⟨mulN es',
              s!"Matrix product: entry $(i,j)$ is the dot product of row $i$ of the left factor with column $j$ of the right factor ({ar}×{ac} · {br}×{bc} → {ar}×{bc}).", none, none⟩
        | _ => none
      | _ => none }

def laTranspose : PlainRule :=
  { name := "la.transpose", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "transpose" [.matrix rows] =>
        let (r, c) := dims rows
        some ⟨.matrix ((List.range c).map fun j => (List.range r).map fun i => entry rows i j), "Transpose swaps rows and columns.", none, none⟩
      | _ => none }

def laDet : PlainRule :=
  { name := "la.det", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "det" [.matrix rows] =>
        let (r, c) := dims rows
        if r != c || r == 0 then some (refuse "determinant of a non-square matrix is undefined")
        else match rows with
        | [[a]] => some ⟨a, "The determinant of a 1×1 matrix is its entry.", none, none⟩
        | [[a, b], [c2, d]] => some ⟨Expr.sub (.mul [a, d]) (.mul [b, c2]), "$\\det\\begin{bmatrix}a&b\\\\c&d\\end{bmatrix} = ad - bc$.", none, none⟩
        | _ => some ⟨detExpr r rows, "Laplace expansion along the first row, $\\det M = \\sum_j (-1)^{1+j} a_{1j} \\det M_{1j}$ where $M_{1j}$ deletes row 1 and column $j$, applied recursively down to 2×2 minors.", none, none⟩
      | _ => none }

def laPow : PlainRule :=
  { name := "la.pow", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .pow (.matrix rows) (.num n) =>
        let (r, c) := dims rows
        if r != c then some (refuse "only a square matrix can be raised to a power")
        else if n.isInt && n.val.num ≥ 1 then
          let k := n.val.num.toNat
          if k == 1 then some ⟨.matrix rows, "$M^1 = M$.", none, none⟩
          else some ⟨.matrix (matPow rows (k - 1)), s!"$M^\{{k}}$ is $M$ multiplied by itself {k} times; the entries are the accumulated dot products.", none, none⟩
        else some (refuse "a matrix can only be raised to a positive integer power")
      | _ => none }

/-- A row or column vector's entries. -/
def asVector : Expr → Option (List Expr)
  | .matrix [row] => some row
  | .matrix rows => if rows.all (·.length == 1) then some (rows.filterMap List.head?) else none
  | _ => none

/-- `dot(u, v) = Σ uᵢ·vᵢ`, bilinear as Mathematica's `Dot`: the Hermitian inner product of complex
vectors is `dot(u, conj(v))`. -/
def laDot : PlainRule :=
  { name := "la.dot", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "dot" [u, v] =>
        match asVector u, asVector v with
        | some us, some vs =>
          if us.length != vs.length then some (refuse s!"dot: the vectors have different lengths ({us.length} and {vs.length})")
          else if us.isEmpty then some (refuse "dot: empty vectors")
          else some ⟨.add ((us.zip vs).map fun (a, b) => .mul [a, b]), "$\\langle u, v\\rangle = \\sum_i u_i v_i$: multiply matching entries and add.", none, none⟩
        | _, _ => if (children e).any isMatrix then some (refuse "dot takes two vectors (one-row or one-column matrices)") else none
      | _ => none }

/-- `norm(v) = (Σ vᵢ²)^(1/2)`, the Euclidean length; for a complex vector use `norm` of the
entries' moduli, or `sqrt(dot(v, conj(v)))`. -/
def laNorm : PlainRule :=
  { name := "la.norm", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "norm" [v] =>
        match asVector v with
        | some vs =>
          if vs.isEmpty then some (refuse "norm: empty vector")
          else some ⟨.pow (.add (vs.map fun a => .pow a (.num (Q.ofInt 2)))) (.num (Q.ofInt 1 / Q.ofInt 2)), "$\\|v\\| = \\sqrt{\\sum_i v_i^2}$: the Pythagorean length.", none, none⟩
        | none => if (children e).any isMatrix then some (refuse "norm takes a vector (a one-row or one-column matrix)") else none
      | _ => none }

/-- `conj` of a matrix is entrywise. -/
def laConj : PlainRule :=
  { name := "la.conj", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "conj" [.matrix rows] =>
        some ⟨.matrix (rows.map fun r => r.map fun a => .fn "conj" [a]), "The conjugate of a matrix is taken entrywise.", none, none⟩
      | _ => none }

def matrixRules : List PlainRule := [laAdd, laScalarMul, laMul, laTranspose, laDet, laPow, laDot, laNorm, laConj]

/-- The catch-all: a matrix literal anywhere no rule above handles it is an error, not junk. -/
def laContext : PlainRule :=
  { name := "la.context", apply := fun e =>
      match e with
      | .matrix rows => if rows.flatten.any isMatrix then some (refuse "nested matrices are not supported") else none
      | _ => if (children e).any isMatrix then some (refuse s!"a matrix cannot be used here: ${e.toText}$") else none }

def contextRules : List PlainRule := [laContext]

/-- Gauss–Jordan elimination on symbolic entries, recorded as row-operation steps whose before/after
are the whole matrix. Works as long as `simplify` can decide zero-ness of pivots — unverified. -/
def rrefSymbolic (m : List (List Expr)) : Expr × Array Step := Id.run do
  let (nr, nc) := dims m
  let mut rows := m
  let mut steps : Array Step := #[]
  let mut pivotRow := 0
  let snap (rs : List (List Expr)) : Expr := .matrix rs
  for col in [0:nc] do
    if pivotRow ≥ nr then break
    let p? := (List.range nr).find? fun i => i ≥ pivotRow && !(simplify0 (entry rows i col)).isZero
    match p? with
    | none => pure ()
    | some p =>
      if p != pivotRow then
        let before := snap rows
        let rp := rows.getD p []
        let rq := rows.getD pivotRow []
        rows := (rows.set p rq).set pivotRow rp
        steps := steps.push ⟨"la.row-swap.symbolic", s!"Swap $R_\{{p + 1}}$ and $R_\{{pivotRow + 1}}$ so the pivot for column {col + 1} is nonzero (assuming the symbolic entry is not zero).", [], before, snap rows, none⟩
      let pivot := entry rows pivotRow col
      if !pivot.isOne then
        let before := snap rows
        rows := rows.set pivotRow ((rows.getD pivotRow []).map fun x => simplify0 (Expr.div x pivot))
        steps := steps.push ⟨"la.row-scale.symbolic", s!"Scale $R_\{{pivotRow + 1}}$ by $1/({pivot.toText})$ so the pivot becomes 1 (assuming {pivot.toText} ≠ 0).", [], before, snap rows, none⟩
      for i in [0:nr] do
        if i != pivotRow then
          let factor := simplify0 (entry rows i col)
          if !factor.isZero then
            let before := snap rows
            let prow := rows.getD pivotRow []
            rows := rows.set i (((rows.getD i []).zip prow).map fun (x, y) => simplify0 (Expr.sub x (.mul [factor, y])))
            steps := steps.push ⟨"la.row-add.symbolic", s!"$R_\{{i + 1}} \\leftarrow R_\{{i + 1}} - ({factor.toText}) R_\{{pivotRow + 1}}$ to clear column {col + 1}.", [], before, snap rows, none⟩
      pivotRow := pivotRow + 1
  return (snap rows, steps)

/-- The rows as rationals, if every entry is a numeral; the flag says whether any was approximate. -/
def asRatRows (rows : List (List Expr)) : Option (List (List Rat) × Bool) := do
  let rs ← rows.mapM fun r => r.mapM fun | .num q => some q | _ => none
  return (rs.map (·.map (·.val)), rs.any (·.any (·.approx)))

/-- Gauss–Jordan elimination over ℚ: the operations of the verified `LinQ.rref`, replayed into
steps. `LinQ.sol_rref` is the theorem that the output has the input's solution set. -/
def rrefRat (rs : List (List Rat)) (approx : Bool) : Except String (Expr × Array Step) := Id.run do
  let lit (r : Rat) : Expr := .num (Q.ofRat r approx)
  let snap (m : List (List Rat)) : Expr := .matrix (m.map (·.map lit))
  let mut m := rs
  let mut steps : Array Step := #[]
  for (col, op) in LinQ.rrefOps rs do
    let before := snap m
    m := op.apply m
    let (rule, text) := match op with
      | .swap i j => ("la.row-swap", s!"Swap $R_\{{i + 1}}$ and $R_\{{j + 1}}$ so the pivot for column {col + 1} is nonzero. (Elementary row operations preserve the solution set: `LinQ.sol_swap`.)")
      | .scale i c => ("la.row-scale", s!"Scale $R_\{{i + 1}}$ by ${(lit c).toText}$ so the pivot becomes 1. (`LinQ.sol_scale`: the factor is nonzero.)")
      | .addMul i j c => ("la.row-add", s!"$R_\{{i + 1}} \\leftarrow R_\{{i + 1}} - ({(lit (-c)).toText}) R_\{{j + 1}}$ to clear column {col + 1}. (`LinQ.sol_addMul`.)")
    steps := steps.push ⟨rule, text, [], before, snap m, none⟩
  return .ok (snap m, steps)

/-- `rref`: the verified ℚ path when every entry is a numeral, the symbolic path otherwise. -/
def rref (m : List (List Expr)) : Except String (Expr × Array Step) :=
  match asRatRows m with
  | some (rs, approx) => rrefRat rs approx
  | none => .ok (rrefSymbolic m)

end MathEngine
