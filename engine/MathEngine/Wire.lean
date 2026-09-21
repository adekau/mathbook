import MathEngine.Expr
import MathEngine.Json
import MathEngine.Rewrite
import MathEngine.Print
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
  /-- `paths` annotates the rendered term with subterm paths, so a page can make it selectable. -/
  partial def Step.toJson (s : Step) (paths : Bool := false) : Json :=
    let base := #[("rule", .str s.rule), ("explanation", .str s.explanation), ("path", Path.toJson s.path),
                  ("before", s.before.toJson), ("after", s.after.toJson),
                  -- optional per protocol rule 5: the whole term after the step, rendered
                  ("afterRendered", .obj #[("text", .str s.after.toText), ("latex", .str (s.after.toLatex paths))])]
    .obj (match s.sub with | some d => base.push ("sub", d.toJson paths) | none => base)
  partial def Derivation.toJson (d : Derivation) (paths : Bool := false) : Json :=
    .obj #[("input", d.input.toJson), ("steps", .arr (d.steps.map fun s => Step.toJson s paths)), ("output", d.output.toJson),
           -- the input rendered too, so a nested derivation's first step has a "before" to show
           ("inputRendered", .obj #[("text", .str d.input.toText), ("latex", .str (d.input.toLatex paths))])]
end

end MathEngine
