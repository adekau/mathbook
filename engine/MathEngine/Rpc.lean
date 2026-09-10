import MathEngine.Json
import MathEngine.Wire
import MathEngine.Parser
import MathEngine.Print
import MathEngine.Simp
/-!
# JSON-RPC surface

One pure function `handle : String → String`. Every host — the Emscripten worker, the
native stdio server, a future HTTP server — is a shim around this function. Session
state is threaded explicitly in M1; the spike is stateless.
-/
namespace MathEngine
open Json

def capabilities : Json :=
  .obj #[("engine", .str "engine-lean"), ("version", .str "0.0.1-spike"), ("verified", .bool true),
         ("features", .arr #[.str "parse", .str "simp.identity"])]

def evaluate (params : Json) : Json :=
  match params.getStr? "source" with
  | none => .obj #[("ok", .bool false), ("error", .obj #[("code", .str "params"), ("message", .str "missing source")])]
  | some src =>
    match parse src with
    | .error msg => .obj #[("ok", .bool false), ("error", .obj #[("code", .str "syntax"), ("message", .str msg)])]
    | .ok e =>
      let out := simpTop e
      .obj #[("ok", .bool true), ("value", out.toJson),
             ("rendered", .obj #[("text", .str out.toText), ("latex", .str out.toText)])]

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
