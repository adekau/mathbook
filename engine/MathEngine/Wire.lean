import MathEngine.Expr
import MathEngine.Json
/-! # Wire format — must match `WireExpr` in `packages/protocol/src/index.ts`. -/
namespace MathEngine

partial def Expr.toJson : Expr → Json
  | .num q => .obj #[("k", .str "num"), ("v", .obj #[("num", .str (toString q.num)), ("den", .str (toString q.den))])]
  | .var x => .obj #[("k", .str "var"), ("name", .str x)]
  | .add es => .obj #[("k", .str "add"), ("args", .arr (es.toArray.map toJson))]
  | .mul es => .obj #[("k", .str "mul"), ("args", .arr (es.toArray.map toJson))]
  | .pow b e => .obj #[("k", .str "pow"), ("base", toJson b), ("exp", toJson e)]
  | .fn f es => .obj #[("k", .str "fn"), ("name", .str f), ("args", .arr (es.toArray.map toJson))]
  | .matrix rs => .obj #[("k", .str "matrix"), ("rows", .arr (rs.toArray.map fun r => .arr (r.toArray.map toJson)))]

end MathEngine
