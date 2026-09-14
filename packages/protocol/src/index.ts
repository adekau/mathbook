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
  /** λ-cells: the same term after the step, with de Bruijn indices. */
  afterDeBruijn?: Rendered;
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
  /** The rule's status over ℂ, when it has a theorem there (`proofs/Proofs/Cx.lean`). A cell whose
   *  input or output mentions `i` is read in the complex semantics and shows this instead; a rule
   *  without it is unverified in such a cell. Optional (rule 5). */
  complex?: { status: "verified" | "conditional" | "checked" | "unverified"; note: string };
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
  /** The evaluation's number in the session — Mathematica's `In[n]`/`Out[n]` — which `%`, `%%`
   *  and `%n` in later cells refer to. Every evaluation takes one, error or not. Optional (rule 5). */
  label?: number;
  /** Which semantics the cell is read in: "complex" when the input or output mentions `i`,
   *  otherwise "real". Decides which of a rule's statuses applies. Optional (rule 5). */
  semantics?: "real" | "complex";
}

export interface EvaluateError {
  ok: false;
  error: { code: string; message: string; span?: { start: number; end: number } };
  /** The evaluation's number (see `EvaluateResult.label`); a failed evaluation still takes one. */
  label?: number;
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

/** `plot(f, x, from, to[, n])`: the engine simplifies `f` under the session, records the cell like
 *  any other (so `engine.explain` works on it), and samples it on a uniform grid. Drawing is the
 *  frontend's; a sample is `null` where `f` has no finite value. Optional method (rule 5). */
export interface PlotParams { sessionId: string; cellId: string; source: string; showWork?: boolean; paths?: boolean }
export interface PlotResult {
  ok: true; kind: "plot";
  value: WireExpr; rendered: Rendered;
  var: string; from: number; to: number;
  points: [number, number | null][];
  derivation?: Derivation; inputRendered?: Rendered; label?: number;
}

/** M-λ: a λ-cell's reply carries the de Bruijn view of the result and of every step
 *  (`Step.afterDeBruijn`), and a reading when the normal form is a Church numeral or boolean. */
export interface HasseData { nodes: { name: string; height: number }[]; covers: [string, string][] }
/** The other worlds' extras on an evaluate reply. λ-cells (`kind: "lambda"`): the de Bruijn view of
 *  the result and of every step (`Step.afterDeBruijn`), and a reading when the normal form is a
 *  Church numeral or boolean. Order cells (`kind: "poset"`): what to draw (elements with their
 *  height, the covers = Hasse edges) and a one-line summary. */
export interface WorldExtras {
  kind?: "lambda" | "poset";
  renderedDeBruijn?: Rendered; reading?: string;
  hasse?: HasseData; summary?: string;
}

export interface Methods {
  "engine.capabilities": { params: Record<string, never>; result: EngineCapabilities };
  "engine.evaluate":     { params: EvaluateParams; result: (EvaluateResult & WorldExtras) | EvaluateError };
  "engine.explain":      { params: ExplainParams; result: ExplainResult };
  "engine.resetSession": { params: { sessionId: string }; result: { ok: true } };
  "engine.plot":         { params: PlotParams; result: PlotResult | EvaluateError };
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
