/**
 * @mathbook/protocol — the contract between a notebook frontend and a math engine.
 *
 * Design rules (see ARCHITECTURE.md §2; rule 5: new capabilities are optional fields, never changes):
 *  1. Everything crossing the boundary is plain JSON. No classes, no functions, no BigInt.
 *  2. Transport is abstract. A Transport moves JSON-RPC 2.0 messages; it does not know what they mean.
 *  3. Expressions are trees with *paths* (child-index lists). Paths are the provenance key that
 *     lets the frontend map "the thing I selected" back to "the step that produced it".
 *  4. The engine is stateful per *session* (a notebook), stateless across sessions.
 */

// ---------------------------------------------------------------------------
// Wire expression representation (JSON-safe)
// ---------------------------------------------------------------------------

/** Exact rational as decimal strings so BigInt survives JSON. "3" / "1" for integers. */
export interface WireRational { num: string; den: string }

export type WireExpr =
  | { k: "num"; v: WireRational }
  | { k: "var"; name: string }
  | { k: "add"; args: WireExpr[] }
  | { k: "mul"; args: WireExpr[] }
  | { k: "pow"; base: WireExpr; exp: WireExpr }
  | { k: "fn"; name: string; args: WireExpr[] }
  | { k: "matrix"; rows: WireExpr[][] };

/** A path from the root of an expression to a subterm: child indices. [] is the root. */
export type Path = number[];

// ---------------------------------------------------------------------------
// Derivations — the "show work" data model
// ---------------------------------------------------------------------------

/** One rewrite. `path` locates where in `before` the rule fired; `after` is the whole term after. */
export interface Step {
  /** Machine name, e.g. "diff.product", "simp.collect-like-terms", "la.row-swap". */
  rule: string;
  /** Human explanation of *why* this step is valid, for show-work mode. Markdown + $latex$. */
  explanation: string;
  path: Path;
  before: WireExpr;
  after: WireExpr;
  /** `after`, rendered (no path annotations). Optional; used by the notebook's Manim Studio to animate steps. */
  afterRendered?: Rendered;
  /** Nested derivation (e.g. simplification that ran inside a differentiation step). */
  sub?: Derivation;
}

export interface Derivation {
  input: WireExpr;
  steps: Step[];
  output: WireExpr;
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

export interface Rendered {
  text: string;
  /** LaTeX. If `paths` was requested, subterms are wrapped in \htmlData{path=0.1.2}{...}. */
  latex: string;
}

// ---------------------------------------------------------------------------
// Requests / responses (the RPC surface). Keep this small; grow it deliberately.
// ---------------------------------------------------------------------------

/** Proof status of one rewrite rule, as reported by the engine. */
export interface RuleStatus {
  rule: string;
  /** "verified": unconditional soundness theorem. "conditional": theorem with a side condition,
   *  whose necessity is itself proved. "checked": a guess whose result a later step verifies (the
   *  integration finder, checked by differentiation). "unverified": no theorem yet. Rules the
   *  engine omits are unverified. */
  status: "verified" | "conditional" | "checked" | "unverified";
  note: string;
}

export interface EngineCapabilities {
  engine: string;              // "engine-ts" | "engine-lean" | ...
  version: string;
  verified: boolean;           // true iff the implementation has machine-checked proofs
  features: string[];          // "simplify", "diff", "linalg", "integrate", ...
  /** Per-rule proof status, so a frontend can mark derivation steps. Optional; absent means unknown. */
  ruleStatus?: RuleStatus[];
  /** M5: how the engine knows evaluation terminates. */
  termination?: { status: 'proven' | 'fuel'; theorem?: string; summary: string };
}

export interface EvaluateParams {
  sessionId: string;
  cellId: string;
  source: string;
  /** Include the derivation. Off by default — derivations can be large. */
  showWork?: boolean;
  /** Emit \htmlData path annotations in LaTeX so the UI can map selections to subterms. */
  paths?: boolean;
}

/**
 * A declarative picture the frontend may draw (ARCHITECTURE.md §5). The engine never renders;
 * it describes. `kind` is namespaced by the math module that produced it (e.g. "linalg.heatmap",
 * "group.cayley-table", "plot.samples"); `data` is that kind's own JSON schema.
 */
export interface VisualSpec { kind: string; title?: string; data: unknown }

export interface EvaluateResult {
  ok: true;
  value: WireExpr;
  rendered: Rendered;
  derivation?: Derivation;
  /** Names bound by this cell (e.g. `let f = x^2`). */
  bound?: string[];
  /** Visual specs for this result. Reserved; empty until a module emits one. */
  visuals?: VisualSpec[];
  /** The parsed input, rendered by the engine (the frontend owns no printer). Sent with `showWork`. */
  inputRendered?: Rendered;
}

export interface EvaluateError {
  ok: false;
  error: { code: string; message: string; span?: { start: number; end: number } };
}

export interface ExplainParams {
  sessionId: string;
  cellId: string;
  /** Path into the chosen term of the cell (the output unless `term` says otherwise). */
  path: Path;
  /** Which term the path is into: the output (default), the input, or the term after step `index`. Optional. */
  term?: { kind: "output" } | { kind: "input" } | { kind: "step"; index: number };
}

/** How a step relates to the selected subterm (M6 origin tracking). */
export interface StepRelation {
  /** Index into the cell's derivation steps. */
  index: number;
  /** `created`: the rule built this node. `copied`: it moved or duplicated it. `contains`: it fired below it. */
  relation: "created" | "copied" | "contains";
}

export interface ExplainResult {
  /** The subterm at `path` and the steps that produced it, traced backwards through the derivation. */
  subterm: WireExpr;
  rendered: Rendered;
  steps: Step[];
  /** Same steps with how each one relates, in derivation order. Optional (M6). */
  trace?: StepRelation[];
}

export interface Methods {
  "engine.capabilities": { params: Record<string, never>; result: EngineCapabilities };
  "engine.evaluate":     { params: EvaluateParams; result: EvaluateResult | EvaluateError };
  "engine.explain":      { params: ExplainParams; result: ExplainResult };
  "engine.resetSession": { params: { sessionId: string }; result: { ok: true } };
}
export type MethodName = keyof Methods;

// ---------------------------------------------------------------------------
// JSON-RPC 2.0 envelope + transport abstraction
// ---------------------------------------------------------------------------

export interface RpcRequest<M extends MethodName = MethodName> {
  jsonrpc: "2.0"; id: number | string; method: M; params: Methods[M]["params"];
}
export interface RpcSuccess<M extends MethodName = MethodName> {
  jsonrpc: "2.0"; id: number | string; result: Methods[M]["result"];
}
export interface RpcFailure {
  jsonrpc: "2.0"; id: number | string | null; error: { code: number; message: string; data?: unknown };
}
export type RpcResponse = RpcSuccess | RpcFailure;

/**
 * A Transport moves opaque JSON strings. Implementations: postMessage (web worker),
 * fetch (HTTP), WebSocket, stdio (child process running the Lean engine).
 */
export interface Transport {
  send(msg: string): void;
  onMessage(handler: (msg: string) => void): void;
  close?(): void;
}

/** The thing a frontend holds. Built from a Transport by `createClient`. */
export interface EngineClient {
  call<M extends MethodName>(method: M, params: Methods[M]["params"]): Promise<Methods[M]["result"]>;
  close(): void;
}

/** The thing an engine implements. Hosted over a Transport by `serve`. */
export interface EngineHandler {
  handle<M extends MethodName>(method: M, params: Methods[M]["params"]): Promise<Methods[M]["result"]>;
}

export function createClient(t: Transport): EngineClient {
  let nextId = 1;
  const pending = new Map<number | string, { resolve: (v: unknown) => void; reject: (e: Error) => void }>();
  t.onMessage((raw) => {
    const msg = JSON.parse(raw) as RpcResponse;
    if (msg.id === null) return;
    const p = pending.get(msg.id);
    if (!p) return;
    pending.delete(msg.id);
    if ("error" in msg) p.reject(new Error(`${msg.error.code}: ${msg.error.message}`));
    else p.resolve(msg.result);
  });
  return {
    call(method, params) {
      const id = nextId++;
      const req: RpcRequest = { jsonrpc: "2.0", id, method, params };
      return new Promise((resolve, reject) => {
        pending.set(id, { resolve: resolve as (v: unknown) => void, reject });
        t.send(JSON.stringify(req));
      });
    },
    close() { t.close?.(); },
  };
}

export function serve(t: Transport, engine: EngineHandler): void {
  t.onMessage(async (raw) => {
    let req: RpcRequest;
    try { req = JSON.parse(raw) as RpcRequest; }
    catch { t.send(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" } })); return; }
    try {
      const result = await engine.handle(req.method, req.params as never);
      t.send(JSON.stringify({ jsonrpc: "2.0", id: req.id, result }));
    } catch (e) {
      const message = e instanceof Error ? e.message : String(e);
      t.send(JSON.stringify({ jsonrpc: "2.0", id: req.id, error: { code: -32000, message } }));
    }
  });
}
