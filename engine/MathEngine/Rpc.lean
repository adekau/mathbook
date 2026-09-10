import MathEngine.Json
import MathEngine.Wire
import MathEngine.Parser
import MathEngine.Print
import MathEngine.Simp
/-!
# JSON-RPC surface

One pure function `handle : String → String`. Every host — the Emscripten worker, the
native stdio server, a future HTTP server — is a shim around this function. Session
state is threaded explicitly from M1 step 4; until then `evaluate` is stateless.
-/
namespace MathEngine
open Json

def capabilities : Json :=
  .obj #[("engine", .str "engine-lean"), ("version", .str "0.1.0-m1"), ("verified", .bool true),
         ("features", .arr #[.str "parse", .str "print", .str "simp.identity"])]

def Rendered.toJson (e : Expr) (paths : Bool) : Json :=
  .obj #[("text", .str e.toText), ("latex", .str (e.toLatex paths))]

private def errorJson (code msg : String) (span : Option (Nat × Nat) := none) : Json :=
  let err := #[("code", .str code), ("message", .str msg)]
  let err := match span with
    | some (s, e) => err.push ("span", .obj #[("start", .num (toString s)), ("end", .num (toString e))])
    | none => err
  .obj #[("ok", .bool false), ("error", .obj err)]

def evaluate (params : Json) : Json :=
  match params.getStr? "source" with
  | none => errorJson "params" "missing source"
  | some src =>
    match parseStmt src with
    | .error e => errorJson "syntax" e.message (some (e.start, e.stop))
    | .ok stmt =>
      let out := simpTop stmt.value
      let paths := params.getBool "paths"
      let res := #[("ok", .bool true), ("value", out.toJson), ("rendered", Rendered.toJson out paths)]
      let res := match stmt with
        | .«let» name _ => res.push ("bound", .arr #[.str name])
        | _ => res
      .obj res

def dispatch (req : Json) : Json :=
  let id := (req.get? "id").getD .null
  let params := (req.get? "params").getD (.obj #[])
  let reply (r : Json) : Json := .obj #[("jsonrpc", .str "2.0"), ("id", id), ("result", r)]
  let fail (code : Int) (msg : String) : Json :=
    .obj #[("jsonrpc", .str "2.0"), ("id", id), ("error", .obj #[("code", .num (toString code)), ("message", .str msg)])]
  match req.getStr? "method" with
  | some "engine.capabilities" => reply capabilities
  | some "engine.evaluate" => reply (evaluate params)
  | some "engine.resetSession" => reply (.obj #[("ok", .bool true)])
  | some m => fail (-32601) s!"unknown method {m}"
  | none => fail (-32600) "missing method"

/-- The single entry point. C symbol `mathengine_handle`, signature `lean_object* (lean_object*)`. -/
@[export mathengine_handle]
def handle (raw : String) : String :=
  match Json.parse raw with
  | .error msg => (Json.obj #[("jsonrpc", .str "2.0"), ("id", .null), ("error", .obj #[("code", .num "-32700"), ("message", .str msg)])]).render
  | .ok req => (dispatch req).render

end MathEngine
