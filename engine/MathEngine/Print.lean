import MathEngine.Expr
/-! # Text printer (spike: no `-`/`/` recovery yet — that is M1, mirroring `printer.ts`). -/
namespace MathEngine

partial def Expr.toText : Expr → String
  | .num q => if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"
  | .var x => x
  | .add es => "(" ++ " + ".intercalate (es.map toText) ++ ")"
  | .mul es => "(" ++ "*".intercalate (es.map toText) ++ ")"
  | .pow b e => s!"{b.toText}^{e.toText}"
  | .fn f es => s!"{f}({", ".intercalate (es.map toText)})"
  | .matrix rs => "[" ++ "; ".intercalate (rs.map fun r => ", ".intercalate (r.map toText)) ++ "]"

end MathEngine
