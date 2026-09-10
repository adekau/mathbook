import MathEngine.Expr
import MathEngine.Json
import MathEngine.Rewrite
/-! # Wire format — must match `WireExpr` in `packages/protocol/src/index.ts`. -/
namespace MathEngine

partial def Expr.toJson : Expr → Json
  | .num q => .obj #[("k", .str "num"), ("v", .obj #[("num", .str (toString q.val.num)), ("den", .str (toString q.val.den))])]
  | .var x => .obj #[("k", .str "var"), ("name", .str x)]
  | .add es => .obj #[("k", .str "add"), ("args", .arr (es.toArray.map toJson))]
  | .mul es => .obj #[("k", .str "mul"), ("args", .arr (es.toArray.map toJson))]
  | .pow b e => .obj #[("k", .str "pow"), ("base", toJson b), ("exp", toJson e)]
  | .fn f es => .obj #[("k", .str "fn"), ("name", .str f), ("args", .arr (es.toArray.map toJson))]
  | .matrix rs => .obj #[("k", .str "matrix"), ("rows", .arr (rs.toArray.map fun r => .arr (r.toArray.map toJson)))]

def Path.toJson (p : Path) : Json := .arr (p.toArray.map fun i => .num (toString i))

mutual
  partial def Step.toJson (s : Step) : Json :=
    let base := #[("rule", .str s.rule), ("explanation", .str s.explanation), ("path", Path.toJson s.path),
                  ("before", s.before.toJson), ("after", s.after.toJson)]
    .obj (match s.sub with | some d => base.push ("sub", d.toJson) | none => base)
  partial def Derivation.toJson (d : Derivation) : Json :=
    .obj #[("input", d.input.toJson), ("steps", .arr (d.steps.map Step.toJson)), ("output", d.output.toJson)]
end

end MathEngine
