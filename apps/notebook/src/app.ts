import { createClient, type EngineClient, type Step, type Path, type RuleStatus } from "@mathbook/protocol";
import { workerTransport, httpTransport } from "@mathbook/engine-host";

/**
 * The notebook shell. Structure and type follow `design/Notebook - GitHub.dc.html`; the colour
 * tokens in `index.html` come from `design/Notebook - Cloud9.dc.html`.
 *
 * The page owns no mathematics. It never parses, prints, or simplifies: every expression on screen
 * is LaTeX the engine produced, every rule name and explanation is the engine's, and the proof
 * status beside each step is the engine's `ruleStatus`. The one thing the page does own is which
 * *kind* of command a cell holds, which it reads off the source text purely to label the cell.
 */

declare const katex: { renderToString(tex: string, opts?: object): string };
const tex = (s: string, paths = false) =>
  katex.renderToString(s, { throwOnError: false, trust: paths, strict: false, displayMode: false });

// ---------------------------------------------------------------------------
// Content: the notebook's own vocabulary, from the design's reference copy.
// ---------------------------------------------------------------------------

interface Doc { name: string; sig: string; blurb: string; ref?: string; examples: string[] }

const DOCS: Doc[] = [
  { name: "diff", sig: "diff(f, x[, n])", blurb: "Derivative of f with respect to x; the optional n takes it n times. Implemented as rewrite rules that push d/dx inward, so the derivation reads like a textbook.", ref: "https://mathworld.wolfram.com/Derivative.html", examples: ["diff(x^2 * sin(x), x)", "diff(x^3, x, 2)"] },
  { name: "expand", sig: "expand(e)", blurb: "Multiplies out products and powers of sums by repeated distribution.", ref: "https://mathworld.wolfram.com/Expand.html", examples: ["expand((x+1)^3)", "expand((a+b)^4)"] },
  { name: "simplify", sig: "simplify(e)", blurb: "Explicit request for the normal form. Every cell is simplified anyway; this names the intent.", examples: ["simplify(x + x)"] },
  { name: "rref", sig: "rref(M)", blurb: "Gauss–Jordan elimination to reduced row echelon form. Each row operation is recorded as its own step.", ref: "https://mathworld.wolfram.com/ReducedRowEchelonForm.html", examples: ["rref([1,2,3;4,5,6;7,8,10])", "rref([1,2;2,4])"] },
  { name: "det", sig: "det(M)", blurb: "Determinant by Laplace expansion along the first row. Works on symbolic entries.", ref: "https://mathworld.wolfram.com/Determinant.html", examples: ["det([1,2;3,4])", "det([a,b;c,d])"] },
  { name: "transpose", sig: "transpose(M)", blurb: "Swaps rows and columns.", examples: ["transpose([1,2,3;4,5,6])"] },
  { name: "subst", sig: "subst(e, x, v)", blurb: "Replaces every free occurrence of x with v.", examples: ["subst(x^2 + 1, x, 3)"] },
  { name: "N", sig: "N(e)", blurb: "Numerical approximation in IEEE-754 double precision, printed to fifteen significant digits.", examples: ["N(pi)", "N(sqrt(2))"] },
  { name: "sqrt", sig: "sqrt(x)", blurb: "Square root, i.e. x^(1/2), so the power rule handles it directly.", ref: "https://mathworld.wolfram.com/SquareRoot.html", examples: ["sqrt(16)", "diff(sqrt(x), x)"] },
  { name: "sin", sig: "sin(x)", blurb: "Sine. Derivative cos x.", ref: "https://mathworld.wolfram.com/Sine.html", examples: ["diff(sin(x^2), x)"] },
  { name: "cos", sig: "cos(x)", blurb: "Cosine. Derivative −sin x.", ref: "https://mathworld.wolfram.com/Cosine.html", examples: ["diff(cos(x), x)"] },
  { name: "tan", sig: "tan(x)", blurb: "Tangent, sin x / cos x. Derivative sec² x.", ref: "https://mathworld.wolfram.com/Tangent.html", examples: ["diff(tan(x), x)"] },
  { name: "exp", sig: "exp(x)", blurb: "Its own derivative and its own antiderivative.", ref: "https://mathworld.wolfram.com/ExponentialFunction.html", examples: ["diff(exp(2x), x)", "ln(exp(x))"] },
  { name: "ln", sig: "ln(x)", blurb: "Natural logarithm. Derivative 1/x.", ref: "https://mathworld.wolfram.com/NaturalLogarithm.html", examples: ["diff(ln(x), x)"] },
  { name: "abs", sig: "abs(x)", blurb: "Absolute value; folds on numeric arguments.", examples: ["abs(-3)"] },
  { name: "let", sig: "let name = e", blurb: "Binds a name in this session. Later cells substitute it.", examples: ["let f = x^3 - 3x"] },
];
const DOC_BY_NAME = new Map(DOCS.map((d) => [d.name, d]));

/** Label for a cell, from its source. Presentation only — the engine decides what it means. */
function cellKind(src: string): string | null {
  const s = src.trim();
  if (!s) return null;
  if (/^let\s/.test(s)) return "definition";
  const m = /^([A-Za-z_][A-Za-z0-9_]*)\s*\(/.exec(s);
  const head = m?.[1];
  switch (head) {
    case "diff": return "derivative";
    case "rref": return "row reduce";
    case "det": return "determinant";
    case "transpose": return "transpose";
    case "expand": return "expand";
    case "simplify": return "simplify";
    case "subst": return "substitute";
    case "N": return "numeric";
    default: break;
  }
  if (/[;\[]/.test(s) && s.includes("[")) return "matrix";
  return "simplify";
}

const SAMPLES = [
  "diff(x^2 * sin(x), x)",
  "expand((x+1)^3)",
  "rref([1,2,3;4,5,6;7,8,10])",
  "let f = x^3 - 3x",
  "diff(f, x, 2)",
];

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

interface Cell {
  id: string;
  src: string;
  label: number | null;
  ms?: number;
  outLatex?: string;
  echoLatex?: string;
  steps?: Step[];
  error?: { message: string; span?: { start: number; end: number } };
  showWork: boolean;
  el?: HTMLElement;
  input?: HTMLInputElement;
}

interface Selection { cellId: string; path: Path; latex: string; text: string; steps: Step[] }
interface LogLine { time: string; level: "rpc" | "ok" | "err"; text: string }

const S = {
  cells: [] as Cell[],
  active: 0,
  rail: "outline" as "outline" | "palette",
  tab: "notebook" as "notebook" | "reference",
  panelTab: "explain" as "explain" | "log",
  panelOpen: true,
  sel: null as Selection | null,
  log: [] as LogLine[],
  caps: null as { engine: string; version: string; verified: boolean; features: string[]; ruleStatus?: RuleStatus[]; termination?: { status: string; theorem?: string; summary: string } } | null,
  ruleStatus: new Map<string, RuleStatus>(),
  engineMode: "lean-worker" as "lean-worker" | "http",
  httpUrl: "http://localhost:8787",
  busy: false,
  comp: null as { cell: Cell; items: Doc[]; index: number; x: number; y: number } | null,
  hover: null as { doc: Doc; x: number; y: number } | null,
};

let client: EngineClient | null = null;
const sessionId = crypto.randomUUID();
let nextLabel = 1;
let cellSeq = 0;

const now = () => new Date().toTimeString().slice(0, 8);
function log(level: LogLine["level"], text: string) {
  S.log.push({ time: now(), level, text });
  if (S.log.length > 200) S.log.shift();
  if (S.panelTab === "log") renderPanel();
  renderPanelHead();
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

async function connect() {
  client?.close();
  client = S.engineMode === "lean-worker"
    ? createClient(workerTransport(new Worker("engine-lean.worker.js")))
    : createClient(httpTransport(S.httpUrl));
  const t0 = performance.now();
  try {
    const caps = await client.call("engine.capabilities", {});
    S.caps = caps;
    S.ruleStatus = new Map((caps.ruleStatus ?? []).map((r) => [r.rule, r]));
    log("ok", `${caps.engine} v${caps.version} ready in ${Math.round(performance.now() - t0)} ms`);
  } catch (e) {
    S.caps = null;
    log("err", `capabilities failed: ${e instanceof Error ? e.message : String(e)}`);
  }
  renderChrome();
  renderPanel();
}

async function runCell(cell: Cell) {
  if (!client || S.busy) return;
  const src = cell.input?.value ?? cell.src;
  cell.src = src;
  if (!src.trim()) return;
  S.busy = true;
  renderChrome();
  const t0 = performance.now();
  log("rpc", `engine.evaluate ${JSON.stringify(src)}`);
  try {
    const r = await client.call("engine.evaluate", {
      sessionId, cellId: cell.id, source: src, showWork: true, paths: true,
    });
    cell.ms = performance.now() - t0;
    if (r.ok) {
      cell.label = cell.label ?? nextLabel++;
      cell.outLatex = r.rendered.latex;
      cell.echoLatex = r.inputRendered?.latex;
      cell.steps = r.derivation?.steps ?? [];
      delete cell.error;
      log("ok", `Out[${cell.label}] ${r.rendered.text}  (${cell.ms.toFixed(1)} ms, ${cell.steps.length} steps)`);
      if (r.bound?.length) log("ok", `bound ${r.bound.join(", ")}`);
    } else {
      cell.label = cell.label ?? nextLabel++;
      delete cell.outLatex; delete cell.echoLatex; cell.steps = [];
      cell.error = r.error;
      log("err", `${r.error.code}: ${r.error.message}`);
    }
  } catch (e) {
    cell.ms = performance.now() - t0;
    cell.error = { message: e instanceof Error ? e.message : String(e) };
    log("err", cell.error.message);
  }
  S.busy = false;
  S.sel = null;
  renderCellBody(cell);
  renderChrome();
  renderSidebar();
  renderPanel();
  if (cell === S.cells[S.cells.length - 1]) addCell();
}

async function explain(cell: Cell, path: Path, spanEl: HTMLElement) {
  if (!client) return;
  document.querySelectorAll(".katex [data-path].sel").forEach((s) => s.classList.remove("sel"));
  spanEl.classList.add("sel");
  log("rpc", `engine.explain [${path.join(".") || "root"}]`);
  try {
    const ex = await client.call("engine.explain", { sessionId, cellId: cell.id, path });
    S.sel = { cellId: cell.id, path, latex: ex.rendered.latex, text: ex.rendered.text, steps: ex.steps };
    S.panelTab = "explain"; S.panelOpen = true;
    log("ok", `${ex.rendered.text} — ${ex.steps.length} related steps`);
  } catch (e) {
    log("err", e instanceof Error ? e.message : String(e));
  }
  renderPanelHead(); renderPanel(); renderCells();
}

// ---------------------------------------------------------------------------
// Cell list operations
// ---------------------------------------------------------------------------

function addCell(src = ""): Cell {
  const cell: Cell = { id: `c${++cellSeq}`, src, label: null, showWork: true };
  S.cells.push(cell);
  renderCells();
  return cell;
}

function focusCell(i: number) {
  S.active = Math.max(0, Math.min(i, S.cells.length - 1));
  S.cells[S.active]?.input?.focus();
  renderCells(); renderSidebar(); renderChrome();
}

function clearOutputs() {
  for (const c of S.cells) { delete c.outLatex; delete c.echoLatex; delete c.error; c.steps = []; c.label = null; c.ms = undefined; }
  nextLabel = 1; S.sel = null;
  renderCells(); renderSidebar(); renderPanel();
  log("ok", "outputs cleared");
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

const h = (tag: string, cls?: string, text?: string) => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
};
const app = () => document.getElementById("app")!;

/** Render an engine explanation: Markdown-ish text with `$latex$` spans. */
function inlineMath(md: string, cls?: string): HTMLElement {
  const el = h("span", cls);
  for (const seg of md.split(/(\$[^$]+\$)/g)) {
    if (seg.length > 2 && seg.startsWith("$") && seg.endsWith("$")) {
      const s = document.createElement("span");
      s.innerHTML = tex(seg.slice(1, -1));
      el.append(s);
    } else if (seg) {
      el.append(document.createTextNode(seg));
    }
  }
  return el;
}

function shell() {
  const root = app();
  root.innerHTML = "";
  root.append(
    h("div", "titlebar"), h("div", "tabbar"),
    (() => {
      const body = h("div", "body");
      body.append(h("div", "rail"), h("aside", "sidebar"), (() => {
        const main = h("div", "main");
        main.append(h("div", "toolbar"), h("div", "cells"), h("div", "reference"), h("div", "panel"));
        return main;
      })());
      return body;
    })(),
    h("div", "statusbar"),
  );
}

const $ = <T extends HTMLElement>(sel: string) => app().querySelector(sel) as T;

function renderChrome() {
  // title bar
  const tb = $(".titlebar"); tb.innerHTML = "";
  const brand = h("div", "brand");
  brand.append(h("span", "mark"), h("span", "name", "Lemma"));
  const menus = h("div", "menus");
  for (const m of ["File", "Edit", "View", "Run", "Kernel", "Help"]) menus.append(h("span", undefined, m));
  const kernel = h("div", "kernel");
  const dot = h("span", "dot");
  const state = S.busy ? "running" : S.caps ? "idle" : "offline";
  dot.style.background = S.busy ? "var(--accent)" : S.caps ? "var(--ok)" : "var(--danger)";
  const sel = document.createElement("select");
  for (const [v, label] of [["lean-worker", "lemma-engine · wasm"], ["http", "lemma-engine · http"]] as const) {
    const o = document.createElement("option"); o.value = v; o.textContent = label; o.selected = S.engineMode === v; sel.append(o);
  }
  sel.addEventListener("change", () => { S.engineMode = sel.value as typeof S.engineMode; void connect(); });
  const url = document.createElement("input");
  url.id = "kurl"; url.value = S.httpUrl; url.hidden = S.engineMode !== "http";
  url.addEventListener("change", () => { S.httpUrl = url.value; void connect(); });
  kernel.append(dot, sel, url, h("span", "sep", "·"), h("span", undefined, state));
  tb.append(brand, menus, h("div", "spacer"), kernel);

  // tab bar
  const tabs = $(".tabbar"); tabs.innerHTML = "";
  for (const [key, label] of [["notebook", "lesson-04.lemma"], ["reference", "reference"]] as const) {
    const t = h("div", `tab${S.tab === key ? " on" : ""}`);
    t.append(h("span", "label", label), h("span", "x", "×"));
    t.addEventListener("click", () => { S.tab = key; renderChrome(); renderView(); });
    tabs.append(t);
  }
  tabs.append((() => { const a = h("div", "tabadd", "+"); a.addEventListener("click", () => focusCell(addCell().label ?? S.cells.length - 1)); return a; })());

  // rail
  const rail = $(".rail"); rail.innerHTML = "";
  for (const [key, glyph, title] of [["outline", "≡", "Outline"], ["palette", "ƒ", "Commands"]] as const) {
    const b = h("div", `b${S.rail === key ? " on" : ""}`, glyph);
    b.title = title;
    b.addEventListener("click", () => { S.rail = key; renderChrome(); renderSidebar(); });
    rail.append(b);
  }

  // toolbar
  const tl = $(".toolbar"); tl.innerHTML = "";
  const group = h("div", "bgroup");
  const mk = (label: string, title: string, fn: () => void, primary = false) => {
    const b = document.createElement("button");
    b.className = primary ? "primary" : ""; b.textContent = label; b.title = title;
    b.addEventListener("click", fn); return b;
  };
  group.append(
    mk("▶ Run", "Run the active cell", () => { const c = S.cells[S.active]; if (c) void runCell(c); }, true),
    mk("▶▶ All", "Run every cell in order", async () => { for (const c of [...S.cells]) if (c.src.trim()) await runCell(c); }),
    mk("Clear", "Clear all outputs", clearOutputs),
    mk("+ Cell", "Add a cell", () => { const c = addCell(); focusCell(S.cells.indexOf(c)); }),
  );
  const done = S.cells.filter((c) => c.outLatex || c.error).length;
  tl.append(group, h("div", "vsep"), h("span", "count", `${S.cells.length} cells · ${done} evaluated`),
    h("div", "spacer"), h("span", "hint", "Type to autocomplete · Enter runs the cell"));

  // status bar
  const sb = $(".statusbar"); sb.innerHTML = "";
  const rules = new Set(S.cells.flatMap((c) => c.steps ?? []).map((s) => s.rule));
  sb.append(
    h("span", undefined, `Mode: ${S.tab}`), h("span", "pipe", "|"),
    h("span", undefined, `Cell ${S.active + 1}`), h("span", "pipe", "|"),
    h("span", undefined, `${S.cells.length} cells`),
    h("div", "spacer"),
    h("span", "rules", `${rules.size} rules applied`), h("span", "pipe", "|"),
    h("span", undefined, S.caps?.verified ? "exact arithmetic · verified engine" : "exact arithmetic"),
  );
  if (S.caps?.termination) {
    const t = h("span", undefined, S.caps.termination.status === "proven" ? "· termination proven" : "· step budget");
    t.title = S.caps.termination.summary + (S.caps.termination.theorem ? ` (${S.caps.termination.theorem})` : "");
    sb.append(h("span", "pipe", "|"), t);
  }
}

function renderView() {
  $(".cells").hidden = S.tab !== "notebook";
  $(".toolbar").hidden = S.tab !== "notebook";
  $(".reference").hidden = S.tab !== "reference";
  if (S.tab === "reference") renderReference();
}

function renderSidebar() {
  const side = $(".sidebar"); side.innerHTML = "";
  side.append(h("h2", undefined, S.rail === "outline" ? "Notebook outline" : "Engine commands"));
  const list = h("div", "list");
  if (S.rail === "outline") {
    S.cells.forEach((c, i) => {
      const row = h("div", `olrow${i === S.active ? " on" : ""}`);
      row.append(h("span", "num", c.label ? `[${c.label}]` : "—"));
      const wrap = h("span");
      wrap.append(h("span", "kind", cellKind(c.src) ?? "empty"), h("span", "src", c.src || "…"));
      row.append(wrap);
      row.addEventListener("click", () => focusCell(i));
      list.append(row);
    });
  } else {
    for (const d of DOCS) {
      const row = h("div", "plrow");
      row.append(h("span", "name", d.name), h("span", "sig", d.sig));
      row.addEventListener("click", () => {
        const c = S.cells[S.active];
        if (c?.input) { c.input.value = d.examples[0] ?? `${d.name}(`; c.src = c.input.value; c.input.focus(); renderCellBody(c); renderSidebar(); }
      });
      row.addEventListener("mouseenter", (ev) => showHover(d, ev as MouseEvent));
      row.addEventListener("mouseleave", hideHover);
      list.append(row);
    }
  }
  side.append(list);
}

function renderCells() {
  const host = $(".cells");
  host.innerHTML = "";
  S.cells.forEach((cell, i) => {
    const el = h("div", `cell${i === S.active ? " active" : ""}`);
    cell.el = el;
    el.append(h("div", "prompt", `In[${cell.label ?? " "}]:=`));

    const mid = h("div", "mid");
    const input = document.createElement("input");
    input.className = "cellin"; input.type = "text"; input.value = cell.src;
    input.placeholder = i === 0 ? "e.g. diff(x^2 * sin(x), x)" : "";
    input.spellcheck = false;
    cell.input = input;
    input.addEventListener("focus", () => { S.active = i; renderChrome(); renderSidebar(); markActive(); });
    input.addEventListener("input", () => { cell.src = input.value; updateCompletions(cell); renderSidebar(); });
    input.addEventListener("blur", () => { hideCompletions(); });
    input.addEventListener("keydown", (ev) => onKey(ev, cell, i));
    mid.append(input);

    const body = h("div", "cellbody");
    mid.append(body);
    el.append(mid);

    const acts = h("div", "cellacts");
    const run = h("span", undefined, "▶ Run"); run.title = "Run this cell";
    run.addEventListener("mousedown", (e) => e.preventDefault());
    run.addEventListener("click", () => void runCell(cell));
    acts.append(run);
    if (cell.steps?.length) {
      const tw = h("span", undefined, cell.showWork ? "Hide work" : "Show work");
      tw.addEventListener("mousedown", (e) => e.preventDefault());
      tw.addEventListener("click", () => { cell.showWork = !cell.showWork; renderCellBody(cell); });
      acts.append(tw);
    }
    el.append(acts, h("div", "brk"));
    host.append(el);
    renderCellBody(cell);
  });
  markActive();
}

function markActive() {
  S.cells.forEach((c, i) => c.el?.classList.toggle("active", i === S.active));
}

/** Re-render everything below a cell's input, leaving the input element untouched. */
function renderCellBody(cell: Cell) {
  const el = cell.el; if (!el) return;
  const mid = el.querySelector(".mid")!;
  const body = mid.querySelector(".cellbody") as HTMLElement;
  body.innerHTML = "";

  if (cell.echoLatex) {
    const echo = h("div", "echo");
    echo.innerHTML = tex(cell.echoLatex);
    body.append(echo);
  }

  const meta = h("div", "cellmeta");
  const kind = cellKind(cell.src);
  if (kind) {
    const badge = h("span", "kindbadge");
    badge.append(document.createTextNode(kind), h("span", "i", "i"));
    const head = /^([A-Za-z_][A-Za-z0-9_]*)\s*\(/.exec(cell.src.trim())?.[1] ?? (/^let\s/.test(cell.src.trim()) ? "let" : "");
    const doc = DOC_BY_NAME.get(head);
    if (doc) {
      badge.addEventListener("mouseenter", (ev) => showHover(doc, ev as MouseEvent));
      badge.addEventListener("mouseleave", hideHover);
    }
    meta.append(badge);
  }
  if (cell.ms !== undefined) meta.append(h("span", "timing", `${cell.ms.toFixed(1)} ms`));
  body.append(meta);

  if (cell.error) {
    const err = h("div", "cellerr", cell.error.message);
    if (cell.error.span) {
      const { start, end } = cell.error.span;
      err.append(h("span", "caret", `${cell.src}\n${" ".repeat(start)}${"^".repeat(Math.max(1, end - start))}`));
    }
    body.append(err);
  }

  if (cell.showWork && cell.steps?.length) {
    const work = h("div", "work");
    cell.steps.forEach((st, n) => {
      const row = h("div", "step");
      row.append(h("span", "no", String(n + 1)));
      const rule = h("span", "rule");
      const status = S.ruleStatus.get(st.rule)?.status ?? "unverified";
      const mark = h("span", `vmark ${status}`);
      mark.title = S.ruleStatus.get(st.rule)?.note ?? "No soundness theorem yet.";
      rule.append(mark, document.createTextNode(st.rule));
      row.append(rule);
      row.append(inlineMath(st.explanation, "el"));
      row.addEventListener("click", () => { row.parentElement?.querySelectorAll(".step.on").forEach((s) => s.classList.remove("on")); row.classList.add("on"); });
      work.append(row);
    });
    body.append(work);
  }

  const old = el.querySelector(".outrow"); old?.remove();
  if (cell.outLatex) {
    const out = h("div", "outrow");
    out.append(h("div", "prompt", `Out[${cell.label}]=`));
    const val = h("div", "outval");
    val.innerHTML = tex(cell.outLatex, true);
    val.querySelectorAll<HTMLElement>("[data-path]").forEach((span) => {
      span.addEventListener("click", (ev) => {
        ev.stopPropagation();
        const raw = span.dataset["path"]!;
        void explain(cell, raw === "root" ? [] : raw.split(".").map(Number), span);
      });
    });
    out.append(val, h("div", "brk"));
    el.append(out);
  }

  // the Show/Hide work button only exists once there are steps
  const acts = el.querySelector(".cellacts")!;
  if (cell.steps?.length && acts.childElementCount === 1) {
    const tw = h("span", undefined, cell.showWork ? "Hide work" : "Show work");
    tw.addEventListener("mousedown", (e) => e.preventDefault());
    tw.addEventListener("click", () => { cell.showWork = !cell.showWork; renderCellBody(cell); });
    acts.append(tw);
  } else if (acts.childElementCount === 2) {
    acts.lastElementChild!.textContent = cell.showWork ? "Hide work" : "Show work";
  }
}

function renderReference() {
  const host = $(".reference"); host.innerHTML = "";
  const grid = h("div", "refgrid");
  for (const d of DOCS) {
    const card = h("div", "refcard");
    const left = h("div");
    left.append(h("div", "rname", d.name), h("div", "rsig", d.sig));
    const right = h("div");
    right.append(h("div", "rblurb", d.blurb));
    const ex = h("div", "rex");
    for (const e of d.examples) {
      const b = document.createElement("button"); b.textContent = e;
      b.addEventListener("click", () => {
        S.tab = "notebook"; renderChrome(); renderView();
        const c = S.cells[S.cells.length - 1] ?? addCell();
        if (c.input) { c.input.value = e; c.src = e; }
        focusCell(S.cells.indexOf(c)); void runCell(c);
      });
      ex.append(b);
    }
    right.append(ex);
    if (d.ref) {
      const a = document.createElement("a");
      a.href = d.ref; a.target = "_blank"; a.rel = "noreferrer"; a.textContent = "Reference entry ↗";
      a.style.cssText = "display:inline-block; margin-top:10px; font-size:11.5px";
      right.append(a);
    }
    card.append(left, right);
    grid.append(card);
  }
  host.append(grid);
}

function renderPanelHead() {
  const panel = $(".panel");
  let head = panel.querySelector(".panelhead") as HTMLElement;
  if (!head) { head = h("div", "panelhead"); panel.prepend(head); }
  head.innerHTML = "";
  for (const [key, label, badge] of [["explain", "Explanation", ""], ["log", "Kernel log", String(S.log.length)]] as const) {
    const t = h("div", `ptab${S.panelTab === key ? " on" : ""}`);
    t.append(document.createTextNode(label));
    if (badge) t.append(h("span", "badge", badge));
    t.addEventListener("click", () => { S.panelTab = key; S.panelOpen = true; renderPanelHead(); renderPanel(); });
    head.append(t);
  }
  head.append(h("div", "spacer"));
  const toggle = h("div", "pbtn", S.panelOpen ? "Collapse ▾" : "Expand ▴");
  toggle.addEventListener("click", () => { S.panelOpen = !S.panelOpen; renderPanelHead(); renderPanel(); });
  head.append(toggle);
}

function renderPanel() {
  const panel = $(".panel");
  panel.style.flex = S.panelOpen ? "0 0 250px" : "0 0 38px";
  let body = panel.querySelector(".panelbody") as HTMLElement;
  if (!body) { body = h("div", "panelbody"); panel.append(body); }
  body.hidden = !S.panelOpen;
  body.innerHTML = "";
  if (!S.panelOpen) return;

  if (S.panelTab === "log") {
    const list = h("div", "log");
    for (const l of [...S.log].reverse()) {
      const row = h("div", "logrow");
      row.append(h("span", "t", l.time), h("span", `lv ${l.level}`, l.level.toUpperCase()), h("span", "msg", l.text));
      list.append(row);
    }
    body.append(list);
    return;
  }

  if (!S.sel) {
    body.append(h("div", "hintbox",
      "Click any symbol, factor, fraction, or whole line in a result. This panel names the rules that produced it, the trail of rules leading up to it, and whether each of those rules has a machine-checked soundness theorem."));
    return;
  }

  const grid = h("div", "explain");

  const c1 = h("div", "col");
  c1.append(h("h3", undefined, "Selection"));
  const selEl = h("div", "sel"); selEl.innerHTML = tex(S.sel.latex);
  c1.append(selEl);
  const cell = S.cells.find((c) => c.id === S.sel!.cellId);
  c1.append(h("div", "kindname", cell ? `${cellKind(cell.src) ?? "cell"} · path ${S.sel.path.join(".") || "root"}` : "selection"));
  c1.append(h("p", undefined, `Rendered as ${S.sel.text}. The engine located this subterm by the path recorded when the result was printed, so the selection and the derivation refer to the same node.`));
  grid.append(c1);

  const c2 = h("div", "col");
  c2.append(h("h3", undefined, "Derivation trail"));
  if (S.sel.steps.length) {
    const trail = h("div", "trail");
    S.sel.steps.forEach((st, i) => {
      const row = h("div", "trailrow");
      row.append(h("span", "no", String(i + 1)), h("span", "rule", st.rule));
      trail.append(row);
    });
    c2.append(trail);
    const p = h("p"); p.append(inlineMath(S.sel.steps[0]!.explanation)); c2.append(p);
  } else {
    c2.append(h("p", undefined, "No rule fired at or below this subterm: it came through unchanged from the input."));
  }
  grid.append(c2);

  const c3 = h("div", "col");
  const used = [...new Set(S.sel.steps.map((s) => s.rule))];
  const stats = used.map((r) => S.ruleStatus.get(r)?.status ?? "unverified");
  const overall = stats.length === 0 ? "verified" : stats.includes("unverified") ? "unverified" : stats.includes("conditional") ? "conditional" : "verified";
  const head3 = h("div"); head3.style.cssText = "display:flex; align-items:center; gap:8px; margin-bottom:10px";
  head3.append(h("h3", undefined, "Proof status"), h("span", `checkbadge ${overall}`, overall));
  (head3.firstElementChild as HTMLElement).style.margin = "0";
  c3.append(head3);
  if (used.length === 0) {
    c3.append(h("p", undefined, "Nothing to check: no rewrite produced this subterm."));
  } else {
    for (const r of used) {
      const st = S.ruleStatus.get(r);
      const row = h("div", "rulestat");
      row.append(h("span", `vmark ${st?.status ?? "unverified"}`), h("span", "n", r),
        h("span", "note", st?.note ?? "No soundness theorem yet."));
      c3.append(row);
    }
  }
  grid.append(c3);
  body.append(grid);
}

// ---------------------------------------------------------------------------
// Completions and hover documentation
// ---------------------------------------------------------------------------

function currentWord(input: HTMLInputElement): { word: string; start: number } {
  const caret = input.selectionStart ?? input.value.length;
  const before = input.value.slice(0, caret);
  const m = /[A-Za-z_][A-Za-z0-9_]*$/.exec(before);
  return { word: m?.[0] ?? "", start: m ? caret - m[0].length : caret };
}

function updateCompletions(cell: Cell) {
  const input = cell.input!;
  const { word } = currentWord(input);
  if (word.length < 1) return hideCompletions();
  const items = DOCS.filter((d) => d.name.toLowerCase().startsWith(word.toLowerCase()) && d.name !== word);
  if (!items.length) return hideCompletions();
  const r = input.getBoundingClientRect();
  S.comp = { cell, items: items.slice(0, 7), index: 0, x: r.left + 8, y: r.bottom + 4 };
  renderCompletions();
}

function hideCompletions() { S.comp = null; renderCompletions(); }

function acceptCompletion() {
  if (!S.comp) return false;
  const { cell, items, index } = S.comp;
  const input = cell.input!;
  const { word, start } = currentWord(input);
  const name = items[index]!.name;
  const after = input.value.slice(start + word.length);
  input.value = input.value.slice(0, start) + name + (after.startsWith("(") ? "" : "(") + after;
  const pos = start + name.length + 1;
  input.setSelectionRange(pos, pos);
  cell.src = input.value;
  hideCompletions(); renderSidebar();
  return true;
}

function renderCompletions() {
  document.querySelector(".completions")?.remove();
  if (!S.comp) return;
  const box = h("div", "completions");
  box.style.left = `${S.comp.x}px`; box.style.top = `${S.comp.y}px`;
  S.comp.items.forEach((d, i) => {
    const row = h("div", `comprow${i === S.comp!.index ? " on" : ""}`);
    row.append(h("span", "n", d.sig), h("span", "h", d.blurb.split(".")[0]!));
    row.addEventListener("mousedown", (e) => { e.preventDefault(); S.comp!.index = i; acceptCompletion(); });
    row.addEventListener("mouseenter", () => { S.comp!.index = i; renderCompletions(); });
    box.append(row);
  });
  box.append(h("div", "compfoot", "Tab or Enter to accept · Esc to dismiss"));
  document.body.append(box);
}

function showHover(doc: Doc, ev: MouseEvent) {
  hideHover();
  const box = h("div", "hoverdoc");
  box.style.left = `${Math.min(ev.clientX + 12, window.innerWidth - 346)}px`;
  box.style.top = `${ev.clientY + 14}px`;
  box.append(h("div", "hn", doc.name), h("div", "hs", doc.sig), h("div", "hb", doc.blurb));
  document.body.append(box);
}
function hideHover() { document.querySelector(".hoverdoc")?.remove(); }

// ---------------------------------------------------------------------------
// Keyboard
// ---------------------------------------------------------------------------

function onKey(ev: KeyboardEvent, cell: Cell, i: number) {
  if (S.comp) {
    if (ev.key === "ArrowDown") { ev.preventDefault(); S.comp.index = (S.comp.index + 1) % S.comp.items.length; return renderCompletions(); }
    if (ev.key === "ArrowUp") { ev.preventDefault(); S.comp.index = (S.comp.index - 1 + S.comp.items.length) % S.comp.items.length; return renderCompletions(); }
    if (ev.key === "Tab" || ev.key === "Enter") { ev.preventDefault(); acceptCompletion(); return; }
    if (ev.key === "Escape") { ev.preventDefault(); return hideCompletions(); }
  }
  if (ev.key === "Enter") { ev.preventDefault(); void runCell(cell); return; }
  if (ev.key === "ArrowDown" && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
  if (ev.key === "ArrowUp" && i > 0) { ev.preventDefault(); focusCell(i - 1); }
}

// ---------------------------------------------------------------------------
// Boot
// ---------------------------------------------------------------------------

shell();
renderChrome();
renderSidebar();
renderPanelHead();
renderPanel();
renderView();
for (const s of SAMPLES) addCell(s);
addCell();
renderCells();
renderSidebar();
void connect();
