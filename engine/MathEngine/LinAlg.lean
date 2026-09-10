import MathEngine.Rewrite
import MathEngine.Print
import MathEngine.SimpRules
/-!
# `la.*` — matrix arithmetic as rewriting, and Gauss–Jordan elimination as a step-recording algorithm

Ported from `linalg.ts`. Dimension errors refuse the evaluation (`RuleResult.error`), as the
reference throws. M7 verifies elimination preserves the solution set.
-/
namespace MathEngine
open Expr

private def dims (rows : List (List Expr)) : Nat × Nat := (rows.length, (rows.head?.map List.length).getD 0)
private def asMat : Expr → Option (List (List Expr)) | .matrix rows => some rows | _ => none
private def refuse (msg : String) : RuleResult := ⟨Expr.zero, "", none, some msg⟩
private def entry (rows : List (List Expr)) (i j : Nat) : Expr := ((rows.getD i []).getD j Expr.zero)

def matrixRules : List PlainRule := [
  { name := "la.add", apply := fun e =>
      match e with
      | .add es =>
        match es.mapM asMat with
        | some (a :: rest) =>
          let (r, c) := dims a
          if rest.any (fun m => dims m != (r, c)) then some (refuse "matrix addition: dimension mismatch")
          else some ⟨.matrix ((List.range r).map fun i => (List.range c).map fun j => .add (entry a i j :: rest.map (entry · i j))),
            "Matrices of the same shape add entrywise.", none, none⟩
        | _ => none
      | _ => none },
  { name := "la.scalar-mul", apply := fun e =>
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
      | _ => none },
  { name := "la.mul", apply := fun e =>
      match e with
      | .mul (.matrix a :: .matrix b :: rest) =>
        if !rest.all isMatrix then none else
        let (ar, ac) := dims a
        let (br, bc) := dims b
        if ac != br then some (refuse s!"matrix product: {ar}×{ac} times {br}×{bc} is undefined (inner dimensions must match)")
        else
          let prod := (List.range ar).map fun i => (List.range bc).map fun j =>
            .add ((List.range ac).map fun k => .mul [entry a i k, entry b k j])
          some ⟨.mul (.matrix prod :: rest),
            s!"Matrix product: entry $(i,j)$ is the dot product of row $i$ of the left factor with column $j$ of the right factor ({ar}×{ac} · {br}×{bc} → {ar}×{bc}).", none, none⟩
      | _ => none },
  { name := "la.transpose", apply := fun e =>
      match e with
      | .fn "transpose" [.matrix rows] =>
        let (r, c) := dims rows
        some ⟨.matrix ((List.range c).map fun j => (List.range r).map fun i => entry rows i j), "Transpose swaps rows and columns.", none, none⟩
      | _ => none },
  { name := "la.det", apply := fun e =>
      match e with
      | .fn "det" [.matrix rows] =>
        let (r, c) := dims rows
        if r != c then some (refuse "determinant of a non-square matrix is undefined")
        else match rows with
        | [[a]] => some ⟨a, "The determinant of a 1×1 matrix is its entry.", none, none⟩
        | [[a, b], [c2, d]] => some ⟨Expr.sub (.mul [a, d]) (.mul [b, c2]), "$\\det\\begin{bmatrix}a&b\\\\c&d\\end{bmatrix} = ad - bc$.", none, none⟩
        | first :: others =>
          let terms := first.zipIdx.map fun (a1j, j) =>
            let minor : Expr := .matrix (others.map fun row => (row.zipIdx.filter (·.2 != j)).map (·.1))
            let sign := if j % 2 == 0 then Expr.one else Expr.minusOne
            .mul [sign, a1j, .fn "det" [minor]]
          some ⟨.add terms, "Laplace expansion along the first row: $\\det M = \\sum_j (-1)^{1+j} a_{1j} \\det M_{1j}$, where $M_{1j}$ deletes row 1 and column $j$.", none, none⟩
        | [] => none
      | _ => none },
  { name := "la.pow", apply := fun e =>
      match e with
      | .pow (.matrix rows) (.num n) =>
        if n.isInt && n.val.num ≥ 1 then
          let k := n.val.num.toNat
          if k == 1 then some ⟨.matrix rows, "$M^1 = M$.", none, none⟩
          else some ⟨.mul (List.replicate k (.matrix rows)), s!"$M^\{{k}}$ is $M$ multiplied by itself {k} times.", none, none⟩
        else none
      | _ => none }
]

/-- Gauss–Jordan elimination, recorded as row-operation steps whose before/after are the whole
matrix. Works on symbolic entries as long as `simplify` can decide zero-ness of pivots. -/
def rref (m : List (List Expr)) : Expr × Array Step := Id.run do
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
        steps := steps.push ⟨"la.row-swap", s!"Swap $R_\{{p + 1}}$ and $R_\{{pivotRow + 1}}$ so the pivot for column {col + 1} is nonzero. (Elementary row operations preserve the row space and the solution set.)", [], before, snap rows, none⟩
      let pivot := entry rows pivotRow col
      if !pivot.isOne then
        let before := snap rows
        rows := rows.set pivotRow ((rows.getD pivotRow []).map fun x => simplify0 (Expr.div x pivot))
        steps := steps.push ⟨"la.row-scale", s!"Scale $R_\{{pivotRow + 1}}$ by $1/({pivot.toText})$ so the pivot becomes 1.", [], before, snap rows, none⟩
      for i in [0:nr] do
        if i != pivotRow then
          let factor := simplify0 (entry rows i col)
          if !factor.isZero then
            let before := snap rows
            let prow := rows.getD pivotRow []
            rows := rows.set i (((rows.getD i []).zip prow).map fun (x, y) => simplify0 (Expr.sub x (.mul [factor, y])))
            steps := steps.push ⟨"la.row-add", s!"$R_\{{i + 1}} \\leftarrow R_\{{i + 1}} - ({factor.toText}) R_\{{pivotRow + 1}}$ to clear column {col + 1}.", [], before, snap rows, none⟩
      pivotRow := pivotRow + 1
  return (snap rows, steps)

end MathEngine
