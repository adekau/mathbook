import MathEngine.Expr
/-!
# Substitution and floating-point evaluation (`N(...)`, `subst(...)`)
-/
namespace MathEngine
open Expr

/-- Replace free occurrences of variables per `bindings`. There are no binders, so this is plain. -/
partial def substitute (bindings : List (String × Expr)) : Expr → Expr
  | .var x => (bindings.lookup x).getD (.var x)
  | e => withChildren e ((children e).map (substitute bindings))

mutual
  /-- `e[x := v]`, structurally (so proofs can unfold it, unlike `substitute`). There are no binders
  in the scalar language, so every occurrence of `x` is free. -/
  def substVar (x : String) (v : Expr) : Expr → Expr
    | .num q => .num q
    | .var y => if y == x then v else .var y
    | .add es => .add (substVarList x v es)
    | .mul es => .mul (substVarList x v es)
    | .pow b e => .pow (substVar x v b) (substVar x v e)
    | .fn f es => .fn f (substVarList x v es)
    | .matrix rows => .matrix (substVarRows x v rows)
  def substVarList (x : String) (v : Expr) : List Expr → List Expr
    | [] => []
    | e :: es => substVar x v e :: substVarList x v es
  def substVarRows (x : String) (v : Expr) : List (List Expr) → List (List Expr)
    | [] => []
    | r :: rs => substVarList x v r :: substVarRows x v rs
end

/-- A session function: its parameters and (normalized) body. -/
abbrev FnDef := List String × Expr

/-- Expand calls of session functions: `f(a, b)` becomes the body with the parameters replaced by
the (already expanded) arguments. A call with the wrong number of arguments is left alone. The body
is not expanded again, so a self-referential definition unfolds one level per evaluation.

A bare `f` — the name of a function of one or more parameters, unapplied — stands for its body over
its own parameters, so after `let g(a, b) = a·b`, `integrate(g, a)` integrates `a·b`. (Mathematica
would read the bare `g` as an unrelated symbol and answer `a·g`; a silent free variable is a trap.) -/
partial def substituteFns (fns : List (String × FnDef)) : Expr → Expr
  | .fn f args =>
    let args' := args.map (substituteFns fns)
    match fns.lookup f with
    | some (params, body) => if params.length = args'.length then substitute (params.zip args') body else .fn f args'
    | none => .fn f args'
  | .var x =>
    match fns.lookup x with
    | some (_ :: _, body) => body
    | _ => .var x
  | e => withChildren e ((children e).map (substituteFns fns))

def constants : List (String × Float) := [("π", 3.141592653589793), ("e", 2.718281828459045)]

private def fns : List (String × (Float → Float)) :=
  [("sin", Float.sin), ("cos", Float.cos), ("tan", Float.tan), ("exp", Float.exp), ("ln", Float.log),
   ("sign", fun x => if x > 0 then 1 else if x < 0 then -1 else 0),
   ("log", Float.log10), ("sqrt", Float.sqrt), ("abs", Float.abs)]

/-- IEEE-754 double value. Fails on unbound variables, unevaluated commands and matrices. -/
partial def evalNumeric (env : List (String × Float)) : Expr → Except String Float
  | .num q => .ok q.toFloat
  | .var x =>
    match env.lookup x <|> constants.lookup x with
    | some v => .ok v
    | none => .error s!"cannot evaluate numerically: '{x}' is unbound"
  | .add es => es.foldlM (fun s a => do pure (s + (← evalNumeric env a))) 0
  | .mul es => es.foldlM (fun s a => do pure (s * (← evalNumeric env a))) 1
  | .pow b e => do pure (Float.pow (← evalNumeric env b) (← evalNumeric env e))
  | .fn f [a] =>
    match fns.lookup f with
    | some g => do pure (g (← evalNumeric env a))
    | none => .error s!"cannot evaluate '{f}' numerically"
  | .fn "π" [] => .ok 3.141592653589793
  | .fn "i" [] => .error "cannot evaluate i numerically: N works over the reals"
  | .fn f _ => .error s!"cannot evaluate '{f}' numerically"
  | .matrix _ => .error "N() of a matrix: apply N to entries instead"

def floatToExpr (x : Float) : Except String Expr :=
  match Q.ofFloat x with
  | some q => .ok (.num q)
  | none => .error s!"non-finite result: {x}"

end MathEngine
