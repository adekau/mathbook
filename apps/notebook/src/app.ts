import { createClient, type EngineClient, type Step, type Path, type RuleStatus, type Derivation, type WireExpr } from "@mathbook/protocol";
declare const __BUILD_ID__: string;
import { workerTransport, httpTransport } from "@mathbook/engine-host";

/**
 * The notebook shell. Structure, type and colour follow the second export of the
 * "Notebook - GitHub" artboard (`design/v2/Notebook - GitHub.dc.html`): warm dark and paper light
 * palettes switched by `html[data-theme]`, a textured paper for the cells, and a Manim Studio tab
 * that turns a derivation into a storyboard of shots with a browser-side preview of Manim's
 * TransformMatchingTex and the generated Python.
 *
 * The page owns no mathematics. It never parses, prints, or simplifies: every expression on screen
 * is LaTeX the engine produced, every rule name and explanation is the engine's, and the proof
 * status beside each step is the engine's `ruleStatus`. The studio's shots are the engine's steps
 * with their rendered terms; what the page adds is timing, glyph matching, and Python text.
 */

declare const katex: { renderToString(tex: string, opts?: object): string; render(tex: string, el: HTMLElement, opts?: object): void };
const tex = (s: string, paths = false) =>
  katex.renderToString(s, { throwOnError: false, trust: paths, strict: false, displayMode: false });

// ---------------------------------------------------------------------------
// Content: the notebook's own vocabulary, from the design's reference copy.
// ---------------------------------------------------------------------------

interface Doc { name: string; sig: string; blurb: string; ref?: string; examples: string[] }

const DOCS: Doc[] = [
  { name: "diff", sig: "diff(f, x[, n])", blurb: "Derivative of f with respect to x; the optional n takes it n times. Implemented as rewrite rules that push d/dx inward, so the derivation reads like a textbook.", ref: "https://mathworld.wolfram.com/Derivative.html", examples: ["diff(x^2 * sin(x), x)", "diff(x^3, x, 2)"] },
  { name: "integrate", sig: "integrate(f, x) · integrate(f, x, a, b)", blurb: "Antiderivative of f in x, without the constant. A small rule set guesses; the guess is accepted only if differentiating it gives f back, so the check is the proof. With bounds, the definite integral: the checked antiderivative at b minus at a (the fundamental theorem of calculus, integrate_definite).", ref: "https://mathworld.wolfram.com/IndefiniteIntegral.html", examples: ["integrate(x^2 + sin(x), x)", "integrate(exp(2*x), x)", "integrate(cos(t)*sin(t), t, 0, 2pi)", "integrate(exp(-3i*t), t, 0, pi)"] },
  { name: "sum", sig: "sum(f, k, a, b)", blurb: "The finite sum f[k := a] + … + f[k := b] for integer bounds, expanded and collected. A definition, read over ℝ by sum_soundR.", examples: ["sum(k^2, k, 1, 10)", "sum(c*exp(i*k*t), k, -3, 3)"] },
  { name: "exptotrig", sig: "exptotrig(e)", blurb: "Euler's formula exp(iθ) = cos θ + i sin θ applied to every exponential with a pure-imaginary argument, at once (Mathematica's ExpToTrig). It is a command rather than a simplification rule because the general formula makes the term bigger; wrap it in expand to distribute and collect. Proved sound over ℂ.", examples: ["exptotrig(exp(i*t))", "expand(exptotrig(exp(-i*t) - exp(i*t)))"] },
  { name: "dot", sig: "dot(u, v) · norm(v)", blurb: "The dot product Σ uᵢvᵢ of two vectors (one-row or one-column matrices), bilinear like Mathematica's Dot — the Hermitian inner product of complex vectors is dot(u, conj(v)). norm(v) is the Euclidean length √(Σ vᵢ²).", examples: ["dot([1,2,3],[4,5,6])", "dot([i,1], conj([i,1]))", "norm([3,4])"] },
  { name: "epicycles", sig: "epicycles(f, t[, n]) · dft(points[, modes])", blurb: "Draw a finite Fourier sum Σ c_k·exp(i k t) with circles: one per term, radius |c_k| and phase arg c_k, spinning at k turns per period, tip to tail; the tip traces the curve. dft(points) computes the coefficients of sample points numerically (the discrete Fourier transform, keeping the modes largest) and draws the same way — File → Import SVG samples a drawing for it. The drawing is numeric presentation; the sum's algebra is the engine's.", examples: ["epicycles(exp(i*t) + 1/2*exp(-3i*t), t)", "epicycles(sum(2i/(k*pi)*(exp(-i*k*t) - exp(i*k*t)), k, 1, 3), t)", "dft([1, i, -1, -i])"] },
  { name: "sign", sig: "sign(x)", blurb: "The sign function: −1, 0 or 1. Folds on numerals and stays symbolic otherwise, so sign(sin(t)) is the square wave.", examples: ["sign(-3)", "plot(sign(sin(t)), t, -pi, pi)"] },
  { name: "poset", sig: "poset({a,b,c}; a<b, a<c) · divisors(n) · subsets({…}) · chain(n)", blurb: "A finite partial order: the reflexive-transitive closure of the relation given, checked for antisymmetry. Bind it with let and ask about it: hasse, join, meet, sup, inf, upper, lower, top, bottom, maximal, minimal, lattice, le.", examples: ["let D = divisors(12)", "join(D, 4, 6)", "lattice(D)", "le(D, 2, 12)", "let P = poset({a,b,c,d}; a<b, a<c, b<d, c<d)"] },
  { name: "map", sig: "map(P; a->b, c->d, …) · monotone(P, f) · lfp(P, f) · gfp(P, f) · fixpoints(P, f)", blurb: "A map on a poset given as a table (other elements are fixed). monotone checks every pair; lfp and gfp iterate from ⊥ and ⊤ and show the Kleene chain, which is proved to end at the least (greatest) fixed point.", examples: ["let f = map(D; 1->2, 3->6)", "monotone(D, f)", "lfp(D, f)"] },
  { name: "lambda", sig: "λx. e  ·  type \\lam", blurb: "A λ-cell: any cell with a λ (type \\lam, then Tab or space) or a backslash. Application is juxtaposition, λx y. e binds two, digits are Church numerals, and name := term defines. The engine reduces in normal order one β-step at a time; toggle de Bruijn indices in the View menu.", examples: ["(λx. x) y", "(λx. λy. x y) y", "add 2 3", "TWO := succ (succ zero)"] },
  { name: "church", sig: "true false and or not if · zero succ add mul pow iszero · pair fst snd · id const K S I omega Y", blurb: "The Church library, available in every λ-cell; a normal form that is a Church numeral or boolean is read out beside the result.", examples: ["if (iszero 0) a b", "fst (pair 1 2)", "mul 2 3"] },
  { name: "plot", sig: "plot(f, x, from, to[, n])  ·  plot([f, g, …], x, from, to[, n])", blurb: "Graph of f — or of several functions, given as a list — over [from, to]. The engine simplifies each under the session (a derivative plots as the derivative), records the derivation, and samples every curve where it has a finite value; the notebook draws them with a legend.", examples: ["plot(sin(x)/x, x, -10, 10)", "plot([sin(x), cos(x)], x, 0, 2pi)", "plot([x^2, diff(x^2, x)], x, -3, 3)"] },
  { name: "expand", sig: "expand(e)", blurb: "Multiplies out products and powers of sums by repeated distribution.", ref: "https://mathworld.wolfram.com/Expand.html", examples: ["expand((x+1)^3)", "expand((a+b)^4)"] },
  { name: "simplify", sig: "simplify(e)", blurb: "Explicit request for the normal form. Every cell is simplified anyway; this names the intent.", examples: ["simplify(x + x)"] },
  { name: "rref", sig: "rref(M)", blurb: "Gauss–Jordan elimination to reduced row echelon form. Each row operation is recorded as its own step.", ref: "https://mathworld.wolfram.com/ReducedRowEchelonForm.html", examples: ["rref([1,2,3;4,5,6;7,8,10])", "rref([1,2;2,4])"] },
  { name: "det", sig: "det(M)", blurb: "Determinant by Laplace expansion along the first row. Works on symbolic entries.", ref: "https://mathworld.wolfram.com/Determinant.html", examples: ["det([1,2;3,4])", "det([a,b;c,d])"] },
  { name: "transpose", sig: "transpose(M)", blurb: "Swaps rows and columns.", examples: ["transpose([1,2,3;4,5,6])"] },
  { name: "subst", sig: "subst(e, x, v)", blurb: "Replaces every free occurrence of x with v.", examples: ["subst(x^2 + 1, x, 3)"] },
  { name: "N", sig: "N(e)", blurb: "Numerical approximation in IEEE-754 double precision, printed to fifteen significant digits. Over ℂ when the term mentions i, or when the real value is not finite (N(sqrt(-1)) is i).", examples: ["N(pi)", "N(sqrt(2))"] },
  { name: "sqrt", sig: "sqrt(x)", blurb: "Square root, i.e. x^(1/2), so the power rule handles it directly.", ref: "https://mathworld.wolfram.com/SquareRoot.html", examples: ["sqrt(16)", "diff(sqrt(x), x)"] },
  { name: "sin", sig: "sin(x)", blurb: "Sine. Derivative cos x.", ref: "https://mathworld.wolfram.com/Sine.html", examples: ["diff(sin(x^2), x)"] },
  { name: "cos", sig: "cos(x)", blurb: "Cosine. Derivative −sin x.", ref: "https://mathworld.wolfram.com/Cosine.html", examples: ["diff(cos(x), x)"] },
  { name: "tan", sig: "tan(x)", blurb: "Tangent, sin x / cos x. Derivative sec² x.", ref: "https://mathworld.wolfram.com/Tangent.html", examples: ["diff(tan(x), x)"] },
  { name: "exp", sig: "exp(x)", blurb: "Its own derivative and its own antiderivative.", ref: "https://mathworld.wolfram.com/ExponentialFunction.html", examples: ["diff(exp(2x), x)", "ln(exp(x))"] },
  { name: "ln", sig: "ln(x)", blurb: "Natural logarithm. Derivative 1/x.", ref: "https://mathworld.wolfram.com/NaturalLogarithm.html", examples: ["diff(ln(x), x)"] },
  { name: "abs", sig: "abs(x)", blurb: "Absolute value; folds on numeric arguments.", examples: ["abs(-3)"] },
  { name: "i", sig: "i · conj(z) · re(z) · im(z) · abs(z) · pi · ℯ", blurb: "The imaginary unit, with i² = −1. Gaussian numerals a + b·i multiply, divide and take powers exactly; conj, re, im and abs read them; sin, cos and tan take exact values at rational multiples of π; and exp(iθ) becomes cos θ + i sin θ where both are exact, so ℯ^(π i) is −1. A cell that mentions i is read over ℂ and shows each rule's status there.", examples: ["ℯ^(pi*i)", "(1+i)*(2-i)", "abs(3+4i)", "cos(pi/3)"] },
  { name: "%", sig: "% · %% · %n", blurb: "The previous output, the one before it, or Out[n]: Mathematica's output references. The engine numbers every evaluation and substitutes the value before anything else happens, so the input interpretation shows what % stood for.", examples: ["diff(%, x)", "rref(%)", "%1 + %2"] },
  { name: "let", sig: "let name = e · let f(x, y) = e", blurb: "Binds a name in this session, or defines a function of its parameters. Later cells substitute the value or expand the call; a bare function name stands for its body over its own parameters, so after let g(a, b) = a*b, integrate(g, a) integrates a*b.", examples: ["let f = x^3 - 3x", "let sq(x) = x^2 + 1", "diff(sq(x), x)", "let g(a, b) = a*b", "integrate(g, a)"] },
];
const DOC_BY_NAME = new Map(DOCS.map((d) => [d.name, d]));

/** Lean-style backslash abbreviations: type `\`, see them all, filter as you type, Tab inserts the symbol. */
interface Sym { abbr: string; aliases: string[]; sym: string; what: string }
const SYMBOLS: Sym[] = [
  { abbr: "lam", aliases: ["lambda", "l"], sym: "λ", what: "lambda" },
  { abbr: "pi", aliases: [], sym: "π", what: "pi" },
  { abbr: "e", aliases: ["euler"], sym: "ℯ", what: "Euler's number, exp(1)" },
  { abbr: "phi", aliases: [], sym: "φ", what: "phi" },
  { abbr: "alpha", aliases: ["a"], sym: "α", what: "alpha" },
  { abbr: "beta", aliases: ["b"], sym: "β", what: "beta" },
  { abbr: "gamma", aliases: ["g"], sym: "γ", what: "gamma" },
  { abbr: "delta", aliases: ["d"], sym: "δ", what: "delta" },
  { abbr: "eps", aliases: ["epsilon"], sym: "ε", what: "epsilon" },
  { abbr: "theta", aliases: ["th"], sym: "θ", what: "theta" },
  { abbr: "mu", aliases: [], sym: "μ", what: "mu" },
  { abbr: "sigma", aliases: ["s"], sym: "σ", what: "sigma" },
  { abbr: "tau", aliases: ["t"], sym: "τ", what: "tau" },
  { abbr: "psi", aliases: [], sym: "ψ", what: "psi" },
  { abbr: "omega", aliases: ["w"], sym: "ω", what: "omega" },
  { abbr: "Gamma", aliases: ["G"], sym: "Γ", what: "Gamma" },
  { abbr: "Delta", aliases: ["D"], sym: "Δ", what: "Delta" },
  { abbr: "Sigma", aliases: ["S"], sym: "Σ", what: "Sigma" },
  { abbr: "Omega", aliases: ["W"], sym: "Ω", what: "Omega" },
];
/** `\abbr` at the end of the text before the caret → the symbol; longest abbreviations first so `\eps` beats `\e`. */
const SYMBOL_RE = new RegExp("\\\\(" + SYMBOLS.flatMap((s) => [s.abbr, ...s.aliases]).sort((a, b) => b.length - a.length).join("|") + ")$");
const symbolFor = (name: string) => SYMBOLS.find((s) => s.abbr === name || s.aliases.includes(name))?.sym ?? "";
type CompItem = { kind: "doc"; doc: Doc } | { kind: "sym"; sym: Sym };

/** Label for a cell, from its source. Presentation only — the engine decides what it means. */
function cellKind(src: string): string | null {
  const s = src.trim();
  if (!s) return null;
  if (/^let\s/.test(s)) return "definition";
  const m = /^([A-Za-z_][A-Za-z0-9_]*)\s*\(/.exec(s);
  const head = m?.[1];
  switch (head) {
    case "diff": return "derivative";
    case "integrate": return "integral";
    case "plot": return "plot";
    case "epicycles": case "dft": return "epicycles";
    case "sum": return "sum";
    case "exptotrig": return "Euler";
  }
  if (/[λ\\]|:=/.test(s)) return "λ-term";
  if (/^(let\s+\w+\s*=\s*)?(poset|divisors|subsets|chain|map|hasse|join|meet|sup|inf|upper|lower|lattice|top|bottom|le|maximal|minimal|monotone|lfp|gfp|fixpoints)\s*\(/.test(s)) return "order";
  switch (head) {
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

/** One curve of a plot: its normalized term (LaTeX and plain text, the latter for Manim) and its samples. */
interface PlotSeries { latex: string; text: string; points: [number, number | null][]; parametric?: boolean }
/** One epicycle: frequency k and coefficient c_k (with its exact term's LaTeX when there is one). */
interface Epicycle { k: number; re: number; im: number; latex?: string }
interface PlotData { var: string; from: number; to: number; series: PlotSeries[]; terms?: Epicycle[] }
/** How many curve colours the stylesheet defines (`svg .curve.c0` … ). */
const CURVE_COLOURS = 6;
/** A `.chalk` file from before lists in `plot` stored one curve as `points` + `text`. */
function migratePlot(p: PlotData | { var: string; from: number; to: number; points: [number, number | null][]; text: string }): PlotData {
  if ("series" in p) return p;
  return { var: p.var, from: p.from, to: p.to, series: [{ latex: "", text: p.text, points: p.points }] };
}

/** What a cell is: mathematics for the engine (the default), Markdown prose with `$…$` and code, or a
 *  section heading that groups the cells below it (run together, collapsible). */
type CellType = "math" | "markdown" | "section";

interface Cell {
  id: string;
  src: string;
  /** Absent for a math cell. */
  type?: Exclude<CellType, "math">;
  /** A Markdown cell shows its source while editing and its rendering otherwise. */
  editing?: boolean;
  /** A section whose cells are folded away. */
  collapsed?: boolean;
  /** The Markdown cell's editor. */
  ta?: HTMLTextAreaElement;
  /** The syntax-highlight overlay under the input (presentation). */
  hl?: HTMLElement;
  plot?: PlotData;
  /** λ-cells: the result with de Bruijn indices, and what it reads as (a Church numeral or boolean). */
  outDeBruijn?: string;
  reading?: string;
  /** What the engine said the cell was, once it has answered; the badge guesses from the source until then. */
  kind?: string;
  /** Order-world cells: the Hasse diagram to draw, and the one-line summary. */
  hasse?: { nodes: { name: string; height: number }[]; covers: [string, string][] };
  summary?: string;
  label: number | null;
  ms?: number;
  outLatex?: string;
  /** The output in the engine's input syntax (the "input form"). */
  outText?: string;
  /** How the output is displayed: matrix | pmatrix | grid | table | input, or standard. */
  form?: string;
  /** "complex" when the cell mentions `i`: its steps are judged by the rules' statuses over ℂ. */
  semantics?: "real" | "complex";
  echoLatex?: string;
  steps?: Step[];
  error?: { message: string; span?: { start: number; end: number } };
  showWork: boolean;
  el?: HTMLElement;
  input?: HTMLInputElement;
}

type TermRef = { kind: "output" } | { kind: "input" } | { kind: "step"; index: number };
interface Selection {
  cellId: string; term: TermRef; path: Path; latex: string; text: string; related: Step[]; trace: Map<number, string>;
  /** A nested step (a row operation, a finder step): shown with its siblings, no engine trace. */
  sub?: { steps: Step[]; index: number; label: string; top: number; key: string };
}
/** A step with a nested derivation (rref's row operations, integrate's finder and check) inherits
 *  the weakest status among them: a command is only as verified as the work it delegated. */
const RANK = { verified: 0, checked: 1, conditional: 2, unverified: 3 } as const;
type Status = keyof typeof RANK;
/** A rule's status and note in a cell's semantics: over ℝ, or over ℂ for a cell that mentions `i`. */
function ruleStatusIn(rule: string, cx: boolean): { status: Status; note: string } {
  const r = S.ruleStatus.get(rule);
  if (!r) return { status: "unverified", note: "No soundness theorem yet." };
  if (!cx) return { status: r.status, note: r.note };
  return r.complex ?? { status: "unverified", note: `Proved over ℝ only (${r.status}); this cell is read over ℂ, where the rule has no theorem yet.` };
}
function statusOf(st: Step, cx = false): Status {
  let s: Status = ruleStatusIn(st.rule, cx).status;
  for (const sub of st.sub?.steps ?? []) { const t = statusOf(sub, cx); if (RANK[t] > RANK[s]) s = t; }
  return s;
}
const cellComplex = (cell: Cell | undefined) => cell?.semantics === "complex";
const sameStep = (a: Step, b: Step) => a.rule === b.rule && a.explanation === b.explanation && a.path.join(".") === b.path.join(".");
const termKey = (t: TermRef) => t.kind === "step" ? `step${t.index}` : t.kind;
interface LogLine { time: string; level: "rpc" | "ok" | "err"; text: string }

/** One shot of a scene: a rendered term, the animation into it, and its duration. */
interface Shot { id: number; label: string; tex: string; anim: string; dur: number; note: string; on: boolean; cell: number | null; plot?: PlotData }
interface Scene { id: number; name: string; shots: Shot[] }

type Tab = "notebook" | "studio" | "reference";

/** One open notebook: its cells, its studio scenes and its own engine session. The globals below
 *  (`S.cells`, `S.docName`, `ST.scenes`, `sessionId`) are views of the current one; `stashDoc` and
 *  `loadDoc` swap them. */
interface Nb {
  id: string; name: string; sessionId: string;
  cells: Cell[]; scenes: Scene[]; studioActive: number; active: number; nextLabel: number;
  /** The serialized notebook at the last save or open; the tab shows `*` while the live state differs. */
  savedText: string;
  /** The serialized notebook at the last stash, for the dirty mark of a document that is not current. */
  text: string;
  /** Whether the engine session has been rebuilt from the cells since the document was restored. */
  hydrated: boolean;
}

const S = {
  docs: [] as Nb[],
  doc: 0,
  cells: [] as Cell[],
  active: 0,
  rail: "outline" as "outline" | "palette",
  tab: "notebook" as Tab,
  panelTab: "explain" as "explain" | "log",
  panelOpen: true,
  sel: null as Selection | null,
  log: [] as LogLine[],
  caps: null as { engine: string; version: string; verified: boolean; features: string[]; ruleStatus?: RuleStatus[]; termination?: { status: string; theorem?: string; summary: string } } | null,
  ruleStatus: new Map<string, RuleStatus>(),
  engineMode: "lean-worker" as "lean-worker" | "http",
  httpUrl: "http://localhost:8787",
  busy: false,
  comp: null as { cell: Cell; items: CompItem[]; index: number; x: number; y: number } | null,
  /** Signature help: the call the caret is inside, and which argument it is in (View menu toggles it). */
  sig: null as { cell: Cell; key: string; sig: string; blurb: string; arg: number } | null,
  /** A call site dismissed with Esc stays quiet until the caret leaves it. */
  sigDismissed: null as string | null,
  sigHelp: (() => { try { return localStorage.getItem("chalkmath.sighelp") !== "off"; } catch { return true; } })(),
  /** Syntax highlighting in the inputs, with bound variables marked (View menu toggles it). */
  highlight: (() => { try { return localStorage.getItem("chalkmath.highlight") !== "off"; } catch { return true; } })(),
  theme: "dark" as "dark" | "light",
  docName: "untitled.chalk",
  deBruijn: false,
  /** Show the engine's rendering of the parsed input under each cell (View menu). */
  showEcho: (() => { try { return localStorage.getItem("chalkmath.echo") !== "off"; } catch { return true; } })(),
  /** Size of rendered mathematics in the cells (View menu): small, normal or large. */
  outSize: (() => { try { return (localStorage.getItem("chalkmath.outsize") as "s" | "m" | "l" | null) ?? "m"; } catch { return "m" as const; } })() as "s" | "m" | "l",
  menu: null as string | null,
  studio: { scenes: [] as Scene[], active: 0, playing: false, t: 0, speed: 1, codeOpen: true, copied: false },
};

let client: EngineClient | null = null;
let sessionId: string = crypto.randomUUID();
let nextLabel = 1;
let cellSeq = 0;
let shotSeq = 0;

const now = () => new Date().toTimeString().slice(0, 8);
function log(level: LogLine["level"], text: string) {
  S.log.push({ time: now(), level, text });
  if (S.log.length > 200) S.log.shift();
  if (S.panelTab === "log") renderPanel();
  renderPanelHead();
}

// ---------------------------------------------------------------------------
// Theme
// ---------------------------------------------------------------------------

function applyTheme(t: "dark" | "light") {
  S.theme = t;
  document.documentElement.setAttribute("data-theme", t);
  try { localStorage.setItem("chalkmath.theme", t); } catch { /* private mode */ }
}
function initTheme() {
  let t: string | null = null;
  try { t = localStorage.getItem("chalkmath.theme") ?? localStorage.getItem("lemma.theme"); } catch { /* private mode */ }
  applyTheme(t === "light" ? "light" : "dark");
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

async function connect() {
  client?.close();
  client = S.engineMode === "lean-worker"
    ? createClient(workerTransport(new Worker(`engine-lean.worker.js?v=${typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev"}`)))
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
  // prose renders; a section heading is a label, not an evaluation
  if (cell.type === "markdown") {
    cell.src = cellSrc(cell);
    cell.editing = false;
    renderCellBody(cell); renderSidebar(); queueMicrotask(autosave);
    if (cell === S.cells[S.cells.length - 1]) { addCell(); renderSidebar(); }
    return;
  }
  if (cell.type === "section") { cell.src = cellSrc(cell); return; }
  if (!client || S.busy) return;
  const src = cellSrc(cell);
  cell.src = src;
  if (!src.trim()) return;
  S.busy = true;
  renderChrome();
  const t0 = performance.now();
  const isPlot = /^\s*(plot|epicycles|dft)\s*\(/.test(src);
  log("rpc", `${isPlot ? "engine.plot" : "engine.evaluate"} ${JSON.stringify(src)}`);
  try {
    const r = isPlot
      ? await client.call("engine.plot", { sessionId, cellId: cell.id, source: src, showWork: true, paths: true })
      : await client.call("engine.evaluate", { sessionId, cellId: cell.id, source: src, showWork: true, paths: true });
    cell.ms = performance.now() - t0;
    queueMicrotask(autosave);
    if (r.ok) {
      cell.label = r.label ?? cell.label ?? nextLabel++;
      cell.outLatex = r.rendered.latex;
      cell.outText = r.rendered.text;
      cell.semantics = "semantics" in r && r.semantics === "complex" ? "complex" : "real";
      cell.echoLatex = r.inputRendered?.latex;
      // a dft cell's input is a long list of sample points: say how many rather than typeset them
      if (/^\s*dft\s*\(\s*\[/.test(src)) {
        // a literal list is long: say how many points rather than typeset them. Rows `[x, y; …]` are
        // points; a single row `[z₁, z₂, …]` is complex points. A bound name (`dft(llama, 60)`) echoes as itself.
        const body = /\[([^\]]*)\]/.exec(src)?.[1] ?? "";
        const n = body.includes(";") ? body.split(";").length : body.split(",").length;
        cell.echoLatex = `\\text{dft of ${n} sample point${n === 1 ? "" : "s"}}`;
      }
      cell.steps = r.derivation?.steps ?? [];
      delete cell.error;
      delete cell.plot; delete cell.outDeBruijn; delete cell.reading; delete cell.kind; delete cell.hasse; delete cell.summary;
      if ("kind" in r && r.kind === "poset") { cell.kind = "order"; cell.hasse = r.hasse; cell.summary = r.summary; }
      if ("kind" in r && r.kind === "plot") {
        cell.plot = { var: r.var, from: r.from, to: r.to, series: r.series.map((s) => ({ latex: s.rendered.latex, text: s.rendered.text, points: s.points, ...(s.parametric ? { parametric: true } : {}) })) };
        if (r.terms?.length) cell.plot.terms = r.terms.map((t) => ({ k: t.k, re: t.re, im: t.im, ...(t.rendered ? { latex: t.rendered.latex } : {}) }));
      }
      if ("kind" in r && r.kind === "lambda") { cell.outDeBruijn = r.renderedDeBruijn?.latex; cell.reading = r.reading; cell.kind = "λ-term"; }
      log("ok", `Out[${cell.label}] ${r.rendered.text}  (${cell.ms.toFixed(1)} ms, ${cell.steps.length} steps)`);
      if ("bound" in r && r.bound?.length) {
        log("ok", `bound ${r.bound.join(", ")}`);
        const k = `${sessionId}:${r.bound[0]}`;
        if (r.params?.length) USER_FNS.set(k, r.params); else USER_FNS.delete(k);
        USER_NAMES.add(k);
        renderHighlights();
      }
    } else {
      cell.label = r.label ?? cell.label ?? nextLabel++;
      delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.plot; cell.steps = [];
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

async function explain(cell: Cell, term: TermRef, path: Path) {
  if (!client) return;
  const where = term.kind === "step" ? `step ${term.index + 1}` : term.kind;
  log("rpc", `engine.explain ${where} [${path.join(".") || "root"}]`);
  try {
    const ex = await client.call("engine.explain", { sessionId, cellId: cell.id, path, term });
    S.sel = { cellId: cell.id, term, path, latex: ex.rendered.latex, text: ex.rendered.text, related: ex.steps,
      trace: new Map((ex.trace ?? []).map((t) => [t.index, t.relation])) };
    S.panelTab = "explain"; S.panelOpen = true;
    log("ok", `${ex.rendered.text} — ${ex.steps.length} related steps`);
  } catch (e) {
    log("err", e instanceof Error ? e.message : String(e));
  }
  markSelection();
  renderPanelHead(); renderPanel();
}

/** Show the current selection in the cells: the selected subterm and, for a step, its row. */
function markSelection() {
  document.querySelectorAll(".katex [data-path].sel").forEach((x) => x.classList.remove("sel"));
  document.querySelectorAll(".step.on").forEach((x) => x.classList.remove("on"));
  const sel = S.sel; if (!sel) return;
  const cell = S.cells.find((c) => c.id === sel.cellId);
  const host = cell?.el?.querySelector(`[data-term="${sel.sub ? sel.sub.key : termKey(sel.term)}"]`);
  if (!host) return;
  host.querySelector(`[data-path="${sel.path.join(".") || "root"}"]`)?.classList.add("sel");
  if (sel.sub || sel.term.kind === "step") host.closest(".step")?.classList.add("on");
}

/** The LaTeX of the subterm at `path`, cut out of a path-annotated rendering (no engine call). */
function pathLatex(latex: string, path: Path): string | null {
  const key = `\\htmlData{path=${path.join(".") || "root"}}{`;
  const i = latex.indexOf(key); if (i < 0) return null;
  let depth = 1, j = i + key.length;
  for (; j < latex.length && depth > 0; j++) {
    if (latex[j] === "\\") { j++; continue; }
    if (latex[j] === "{") depth++; else if (latex[j] === "}") depth--;
  }
  return latex.slice(i + key.length, j - 1);
}

/** The output forms a cell may choose from (the engine prints once; these are typesetting choices). */
function formsFor(cell: Cell): [string, string][] {
  return cell.outLatex?.includes("\\begin{bmatrix}")
    ? [["matrix", "matrix [ ]"], ["pmatrix", "matrix ( )"], ["grid", "grid"], ["table", "table"], ["input", "input form"]]
    : [["standard", "standard"], ["input", "input form"]];
}
function formLatex(latex: string, form: string | undefined): string {
  if (!form || form === "matrix" || form === "standard") return latex;
  return latex.replace(/\\begin\{bmatrix\}([\s\S]*?)\\end\{bmatrix\}/g, (_m, body: string) => {
    if (form === "pmatrix") return `\\begin{pmatrix}${body}\\end{pmatrix}`;
    if (form === "grid") return `\\begin{matrix}${body}\\end{matrix}`;
    if (form === "table") {
      const rows = body.split(" \\\\ ");
      const cols = (rows[0]?.match(/&/g)?.length ?? 0) + 1;
      return `\\begin{array}{|${"c|".repeat(cols)}}\\hline ${rows.join(" \\\\ \\hline ")} \\\\ \\hline\\end{array}`;
    }
    return `\\begin{bmatrix}${body}\\end{bmatrix}`;
  });
}

/** Make every path-annotated subterm of a rendered term clickable. */
function wireTerm(host: HTMLElement, cell: Cell, term: TermRef) {
  host.dataset["term"] = termKey(term);
  host.querySelectorAll<HTMLElement>("[data-path]").forEach((span) => {
    span.addEventListener("click", (ev) => {
      ev.stopPropagation();
      const raw = span.dataset["path"]!;
      void explain(cell, term, raw === "root" ? [] : raw.split(".").map(Number));
    });
  });
}

// ---------------------------------------------------------------------------
// Documents: several notebooks open as tabs, each with its own engine session
// ---------------------------------------------------------------------------

const currentDoc = () => S.docs[S.doc];

/** Copy the live globals back into the current document. */
function stashDoc() {
  const d = currentDoc(); if (!d) return;
  d.name = S.docName; d.cells = S.cells; d.scenes = ST.scenes; d.studioActive = ST.active; d.active = S.active;
  d.nextLabel = nextLabel; d.sessionId = sessionId; d.text = serializeNotebook();
}

/** Make document `i` current: its cells, scenes and session become the live ones. A document whose
 *  session has not been rebuilt since it was restored is re-run once the engine is up. */
function loadDoc(i: number) {
  stashDoc();
  const d = S.docs[i]; if (!d) return;
  S.doc = i;
  S.docName = d.name; S.cells = d.cells; ST.scenes = d.scenes; ST.active = d.studioActive; ST.t = 0; stopPlayback();
  S.active = Math.min(d.active, Math.max(0, d.cells.length - 1)); nextLabel = d.nextLabel; sessionId = d.sessionId;
  S.sel = null; hideCompletions(); hideSigHelp(); hideHover();
  renderChrome(); renderCells(); renderSidebar(); renderPanelHead(); renderPanel();
  if (S.tab === "studio") renderStudio();
  if (!d.hydrated && client) hydrate(d);
}

/** Rebuild a restored document's engine session by re-running its cells. Re-running renumbers the
 *  cells, so a document that was clean stays clean: its saved baseline moves to the re-run state. */
function hydrate(d: Nb) {
  d.hydrated = true;
  const wasClean = !docDirty(d);
  void runAll().then(() => { if (wasClean && d === currentDoc()) { d.savedText = serializeNotebook(); renderTabs(); autosave(); } });
}

function makeDoc(name: string, cells: Cell[] = [], scenes: Scene[] = []): Nb {
  return { id: `d${Date.now().toString(36)}${Math.random().toString(36).slice(2, 6)}`, name, sessionId: crypto.randomUUID(),
    cells, scenes, studioActive: 0, active: 0, nextLabel: Math.max(0, ...cells.map((c) => c.label ?? 0)) + 1,
    savedText: "", text: "", hydrated: true };
}

/** Open a new, empty notebook in its own tab. */
function newDoc(name = "untitled.chalk"): Nb {
  const d = makeDoc(name);
  S.docs.push(d);
  loadDoc(S.docs.length - 1);
  addCell();
  d.savedText = serializeNotebook();   // an untouched new notebook is not "unsaved"
  renderChrome(); renderCells(); renderSidebar();
  return d;
}

/** Whether a document differs from its last saved (or opened) state. */
function docDirty(d: Nb): boolean {
  const live = d === currentDoc() ? serializeNotebook() : d.text;
  return live !== d.savedText;
}

/** A new notebook nobody has typed in: the natural place to open a file into. */
function docPristine(d: Nb): boolean {
  return d.name === "untitled.chalk" && d.scenes.length === 0 && d.cells.every((c) => !cellSrc(c).trim() && !c.outLatex);
}

/** Close a tab; an unsaved notebook asks first. The last tab closing leaves a fresh one. */
function closeDoc(i: number) {
  const d = S.docs[i]; if (!d) return;
  if (i === S.doc) stashDoc();
  if (docDirty(d) && !window.confirm(`Close ${d.name} without saving?`)) return;
  if (client) void client.call("engine.resetSession", { sessionId: d.sessionId }).catch(() => undefined);
  S.docs.splice(i, 1);
  if (!S.docs.length) { S.doc = -1; newDoc(); }
  else {
    // make the neighbour current without stashing the closed document back
    const j = Math.min(i, S.docs.length - 1);
    S.doc = -1;
    loadDoc(j);
  }
  log("ok", `closed ${d.name}`);
  autosave();
}

/** The tab bar: one tab per open notebook (italic with a star while unsaved), then the studio and the reference. */
function renderTabs() {
  const tabs = $(".tabbar"); tabs.innerHTML = "";
  S.docs.forEach((d, i) => {
    const dirty = docDirty(d);
    const on = S.tab === "notebook" && i === S.doc;
    const t = h("div", `tab${on ? " on" : ""}${dirty ? " dirty" : ""}`);
    t.title = dirty ? `${d.name} — unsaved changes` : d.name;
    const x = h("span", "x", "×"); x.title = "Close";
    x.addEventListener("click", (ev) => { ev.stopPropagation(); closeDoc(i); });
    t.append(h("span", "label", `${d.name}${dirty ? "*" : ""}`), x);
    t.addEventListener("click", () => { if (i !== S.doc) loadDoc(i); switchTab("notebook"); });
    tabs.append(t);
  });
  for (const [key, label] of [["studio", "manim studio"], ["reference", "reference"]] as const) {
    const t = h("div", `tab${S.tab === key ? " on" : ""}`);
    t.append(h("span", "label", label));
    t.addEventListener("click", () => switchTab(key));
    tabs.append(t);
  }
  tabs.append((() => { const a = h("div", "tabadd", "+"); a.title = "New notebook"; a.addEventListener("click", () => { newDoc(); switchTab("notebook"); }); return a; })());
}

// ---------------------------------------------------------------------------
// Notebook files (.chalk): sources, outputs and studio scenes as JSON
// ---------------------------------------------------------------------------

interface ChalkFile {
  /** Format version. Files written as `.lemma` before the rename carry `lemma: 1` instead and still open. */
  chalk?: 1; lemma?: 1; name: string;
  cells: { src: string; type?: Cell["type"] | undefined; collapsed?: boolean | undefined; showWork: boolean; label: number | null; outLatex?: string | undefined; outText?: string | undefined; form?: string | undefined; semantics?: "real" | "complex" | undefined; echoLatex?: string | undefined; steps?: Step[] | undefined; error?: Cell["error"] | undefined; plot?: PlotData | undefined }[];
  scenes: Scene[];
}

/** A cell's source as the user has it now: the live editor's text when there is one. */
const cellSrc = (c: Cell) => c.input?.value ?? c.ta?.value ?? c.src;

/** A cell's steps are kept in a file only up to this size: a long derivation of a big term (a sum
 *  of integrals, with the nested checks) runs to megabytes, and the notebook re-runs every cell
 *  when it opens a file anyway — the steps come back then. The output itself is always kept. */
const STEPS_BUDGET = 256 * 1024;
function stepsToSave(c: Cell): Step[] | undefined {
  if (!c.steps?.length) return c.steps;
  return JSON.stringify(c.steps).length <= STEPS_BUDGET ? c.steps : undefined;
}

function serializeNotebook(): string {
  const doc: ChalkFile = {
    chalk: 1, name: S.docName,
    cells: S.cells.map((c) => ({ src: cellSrc(c), type: c.type, collapsed: c.collapsed || undefined, showWork: c.showWork, label: c.label, outLatex: c.outLatex, outText: c.outText, form: c.form, semantics: c.semantics, echoLatex: c.echoLatex, steps: stepsToSave(c), error: c.error, plot: c.plot })),
    scenes: ST.scenes,
  };
  return JSON.stringify(doc, null, 2);
}

/** Replace the notebook with a file's contents: saved outputs show at once, then every cell is
 *  re-run in order so the engine's session (and with it `explain`) matches what is shown. */
async function loadNotebook(text: string, name?: string) {
  let doc: ChalkFile;
  try { doc = JSON.parse(text) as ChalkFile; } catch { log("err", "not a .chalk file: invalid JSON"); return; }
  if ((doc.chalk !== 1 && doc.lemma !== 1) || !Array.isArray(doc.cells)) { log("err", "not a .chalk file"); return; }
  const d = makeDoc(name ?? doc.name ?? "untitled.chalk", cellsFromFile(doc), Array.isArray(doc.scenes) ? doc.scenes : []);
  if (!d.cells.length) d.cells.push(freshCell());
  // an untouched new notebook is replaced; otherwise the file gets its own tab
  const cur = currentDoc();
  if (cur && docPristine(cur)) { stashDoc(); S.docs[S.doc] = d; S.doc = -1; loadDoc(S.docs.indexOf(d)); }
  else { S.docs.push(d); loadDoc(S.docs.length - 1); }
  switchTab("notebook");
  log("ok", `opened ${d.name}: ${d.cells.length} cells, ${d.scenes.length} scenes`);
  await runAll();
  d.savedText = serializeNotebook();
  renderTabs();
  autosave();
}

/** Cells from a file's records (no DOM yet). */
function cellsFromFile(doc: ChalkFile): Cell[] {
  return doc.cells.map((c) => {
    const cell = freshCell(c.src, c.type === "markdown" || c.type === "section" ? c.type : "math");
    if (cell.type === "markdown") cell.editing = !c.src.trim();   // prose comes back rendered; an empty cell opens for typing
    if (c.collapsed) cell.collapsed = true;
    cell.showWork = c.showWork ?? false; cell.label = c.label ?? null;
    if (c.outLatex) cell.outLatex = c.outLatex;
    if (c.outText) cell.outText = c.outText;
    if (c.form) cell.form = c.form;
    if (c.semantics) cell.semantics = c.semantics;
    if (c.echoLatex) cell.echoLatex = c.echoLatex;
    if (c.steps) cell.steps = c.steps;
    if (c.error) cell.error = c.error;
    if (c.plot) cell.plot = migratePlot(c.plot);
    return cell;
  });
}

async function runAll() { for (const c of [...S.cells]) if (cellSrc(c).trim()) await runCell(c); }

/** The cells a section heads: from the one after it to the next section (or the end). */
function sectionRange(i: number): [number, number] {
  let j = i + 1;
  while (j < S.cells.length && S.cells[j]!.type !== "section") j++;
  return [i + 1, j];
}
/** The section containing cell `i` (the nearest heading at or above it), or −1 when it is above the first. */
function sectionOf(i: number): number {
  for (let k = Math.min(i, S.cells.length - 1); k >= 0; k--) if (S.cells[k]?.type === "section") return k;
  return -1;
}
/** Run every cell of the section headed by cell `i`, in order. */
async function runSection(i: number) {
  const [a, b] = sectionRange(i);
  const cells = S.cells.slice(a, b);
  log("ok", `running section “${cellSrc(S.cells[i]!) || "untitled"}”: ${cells.length} cell${cells.length === 1 ? "" : "s"}`);
  for (const c of cells) if (cellSrc(c).trim()) await runCell(c);
}

async function restartKernel() {
  if (client) { try { await client.call("engine.resetSession", { sessionId }); } catch (e) { log("err", String(e)); } }
  clearOutputs();
  for (const k of [...USER_FNS.keys()]) if (k.startsWith(`${sessionId}:`)) USER_FNS.delete(k);
  for (const k of [...USER_NAMES]) if (k.startsWith(`${sessionId}:`)) USER_NAMES.delete(k);
  log("ok", "kernel restarted: the session is empty");
}

// ---------------------------------------------------------------------------
// The library: notebooks saved in the browser (local storage), by name
// ---------------------------------------------------------------------------

interface LibraryEntry { file: ChalkFile; savedAt: string }
type Library = Record<string, LibraryEntry>;
function readLibrary(): Library {
  try { return JSON.parse(localStorage.getItem("chalkmath.library") ?? "{}") as Library; } catch { return {}; }
}
function writeLibrary(lib: Library): boolean {
  try { localStorage.setItem("chalkmath.library", JSON.stringify(lib)); return true; }
  catch { log("err", "could not save: the browser's storage is full or unavailable"); return false; }
}

/** Save the current notebook in the browser under its name. */
function saveNotebook() {
  const text = serializeNotebook();
  const lib = readLibrary();
  lib[S.docName] = { file: JSON.parse(text) as ChalkFile, savedAt: new Date().toISOString() };
  if (!writeLibrary(lib)) return;
  const d = currentDoc(); if (d) d.savedText = text;
  renderTabs(); autosave();
  log("ok", `saved ${S.docName} in this browser`);
}
function saveNotebookAs() {
  const name = window.prompt("Save notebook as", S.docName);
  if (!name) return;
  S.docName = name.endsWith(".chalk") ? name : `${name.replace(/\.lemma$/, "")}.chalk`;
  const d = currentDoc(); if (d) d.name = S.docName;
  renderChrome(); saveNotebook();
}

/** Open a saved notebook: a small picker over the library, with a delete for each entry. */
function openNotebook() {
  closeModal();
  const lib = readLibrary();
  const names = Object.keys(lib).sort((a, b) => (lib[b]!.savedAt > lib[a]!.savedAt ? 1 : -1));
  const box = h("div", "modal");
  const card = h("div", "modalcard");
  card.append(h("h3", undefined, "Open a notebook"));
  if (!names.length) card.append(h("p", "muted", "Nothing saved in this browser yet. File › Save keeps the current notebook here; File › Import opens a .chalk file."));
  const list = h("div", "liblist");
  for (const name of names) {
    const row = h("div", "librow");
    const when = new Date(lib[name]!.savedAt);
    const main = h("div", "main");
    main.append(h("div", "name", name), h("div", "when", `${lib[name]!.file.cells.length} cells · saved ${when.toLocaleString()}`));
    main.addEventListener("click", () => { closeModal(); openFromLibrary(name); });
    const del = h("span", "del", "delete"); del.title = "Remove from this browser";
    del.addEventListener("click", (ev) => { ev.stopPropagation(); if (window.confirm(`Delete ${name} from this browser?`)) { const l = readLibrary(); delete l[name]; writeLibrary(l); openNotebook(); } });
    row.append(main, del);
    list.append(row);
  }
  card.append(list);
  const foot = h("div", "modalfoot");
  const imp = h("button", undefined, "Import from file…"); imp.addEventListener("click", () => { closeModal(); importNotebook(); });
  const close = h("button", "primary", "Close"); close.addEventListener("click", closeModal);
  foot.append(imp, h("div", "spacer"), close);
  card.append(foot);
  box.append(card);
  box.addEventListener("click", (ev) => { if (ev.target === box) closeModal(); });
  document.body.append(box);
}
function closeModal() { document.querySelectorAll(".modal").forEach((m) => m.remove()); }

/** A notebook from the library becomes a tab (or replaces an untouched one); one already open is shown. */
function openFromLibrary(name: string) {
  const already = S.docs.findIndex((d) => d.name === name);
  if (already >= 0) { loadDoc(already); switchTab("notebook"); return; }
  const entry = readLibrary()[name]; if (!entry) return;
  void loadNotebook(JSON.stringify(entry.file), name);
}

function download(name: string, text: string) {
  const a = document.createElement("a");
  a.href = URL.createObjectURL(new Blob([text], { type: "application/json" }));
  a.download = name; a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}

/** Export the current notebook as a .chalk file (a download). */
function exportNotebook() { download(S.docName, serializeNotebook()); log("ok", `exported ${S.docName}`); }
function importNotebook() {
  const inp = document.createElement("input");
  inp.type = "file"; inp.accept = ".chalk,.lemma,.json,application/json";
  inp.addEventListener("change", () => {
    const f = inp.files?.[0]; if (!f) return;
    void f.text().then((t) => loadNotebook(t, f.name));
  });
  inp.click();
}
// --- Notebook as a link: the sources, deflated and base64url-encoded in the fragment -------------

/** What a link carries: the name and every cell's text and kind. Outputs are not included: the
 *  engine recomputes them when the link opens, which is the point of a verified notebook. */
interface LinkDoc { v: 1; n: string; c: { s: string; t?: "markdown" | "section"; w?: 1; f?: 1 }[] }

async function deflate(text: string): Promise<Uint8Array> {
  const cs = new CompressionStream("deflate-raw");
  const w = cs.writable.getWriter(); void w.write(new TextEncoder().encode(text)); void w.close();
  return new Uint8Array(await new Response(cs.readable).arrayBuffer());
}
async function inflate(bytes: Uint8Array): Promise<string> {
  const ds = new DecompressionStream("deflate-raw");
  const w = ds.writable.getWriter(); void w.write(new Uint8Array(bytes) as Uint8Array<ArrayBuffer>); void w.close();
  return new Response(ds.readable).text();
}
function b64url(bytes: Uint8Array): string {
  let s = "";
  for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}
function unb64url(s: string): Uint8Array {
  const bin = atob(s.replace(/-/g, "+").replace(/_/g, "/").padEnd(Math.ceil(s.length / 4) * 4, "="));
  return Uint8Array.from(bin, (c) => c.charCodeAt(0));
}

/** A link that opens this notebook: `…#nb=<deflated JSON>` (≈ a third of the sources' size). */
async function notebookLink(): Promise<string> {
  const doc: LinkDoc = {
    v: 1, n: S.docName,
    c: S.cells.filter((c) => cellSrc(c).trim()).map((c) => ({ s: cellSrc(c), ...(c.type ? { t: c.type } : {}), ...(c.showWork ? { w: 1 as const } : {}), ...(c.collapsed ? { f: 1 as const } : {}) })),
  };
  const json = JSON.stringify(doc);
  const payload = typeof CompressionStream === "function" ? `nb=${b64url(await deflate(json))}` : `nbj=${b64url(new TextEncoder().encode(json))}`;
  return `${location.origin}${location.pathname}#${payload}`;
}
async function copyNotebookLink() {
  try {
    const url = await notebookLink();
    await navigator.clipboard.writeText(url);
    log("ok", `copied a link to ${S.docName} (${url.length.toLocaleString()} characters); it opens the sources and re-runs them`);
  } catch (e) { log("err", `could not copy the link: ${e instanceof Error ? e.message : String(e)}`); }
}
/** Open the notebook a link carries (the page's fragment), then drop the fragment so a reload does not open it again. */
async function openNotebookLink(hash: string): Promise<boolean> {
  const m = /^#(nb|nbj)=([A-Za-z0-9_-]+)$/.exec(hash); if (!m) return false;
  try {
    const bytes = unb64url(m[2]!);
    const json = m[1] === "nb" ? await inflate(bytes) : new TextDecoder().decode(bytes);
    const doc = JSON.parse(json) as LinkDoc;
    if (doc.v !== 1 || !Array.isArray(doc.c)) throw new Error("not a notebook link");
    const file: ChalkFile = {
      chalk: 1, name: doc.n || "shared.chalk",
      cells: doc.c.map((c) => ({ src: String(c.s ?? ""), type: c.t === "markdown" || c.t === "section" ? c.t : undefined, collapsed: c.f ? true : undefined, showWork: !!c.w, label: null })),
      scenes: [],
    };
    history.replaceState(null, "", location.pathname + location.search);
    await loadNotebook(JSON.stringify(file), file.name);
    return true;
  } catch (e) { log("err", `the link did not open: ${e instanceof Error ? e.message : String(e)}`); return false; }
}

/** Import SVG…: sample the file's paths at evenly spaced arc lengths (the article's
 *  `getPointAtLength` loop), centre and scale them, and add a `dft([...])` cell — the discrete Fourier
 *  transform of the samples drives an epicycle drawing of the picture. Presentation, not exact. */
function importSvg() {
  const inp = document.createElement("input");
  inp.type = "file"; inp.accept = ".svg,image/svg+xml";
  inp.addEventListener("change", () => {
    const f = inp.files?.[0]; if (!f) return;
    void f.text().then((xml) => {
      const doc = new DOMParser().parseFromString(xml, "image/svg+xml");
      const paths = Array.from(doc.querySelectorAll("path"));
      if (!paths.length) { log("err", "Import SVG: no <path> elements in the file"); return; }
      // measure in a hidden host SVG so getTotalLength works
      const NS = "http://www.w3.org/2000/svg";
      const host = document.createElementNS(NS, "svg"); host.setAttribute("width", "0"); host.setAttribute("height", "0"); host.style.position = "absolute";
      document.body.append(host);
      const N = 400;
      const copies = paths.map((p) => { const c = document.createElementNS(NS, "path"); c.setAttribute("d", p.getAttribute("d") ?? ""); host.append(c); return c; });
      const total = copies.reduce((a, c) => a + c.getTotalLength(), 0);
      const pts: [number, number][] = [];
      for (const c of copies) {
        const len = c.getTotalLength(), n = Math.max(1, Math.round((N * len) / (total || 1)));
        for (let i = 0; i < n; i++) { const q = c.getPointAtLength((len * i) / n); pts.push([q.x, q.y]); }
      }
      host.remove();
      // centre, flip y (SVG's y grows downward), scale the larger extent to [-1, 1]
      const xs = pts.map((p) => p[0]), ys = pts.map((p) => p[1]);
      const cx = (Math.min(...xs) + Math.max(...xs)) / 2, cy = (Math.min(...ys) + Math.max(...ys)) / 2;
      const ext = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) / 2 || 1;
      const rows = pts.map(([x, y]) => `${((x - cx) / ext).toFixed(3)}, ${(-(y - cy) / ext).toFixed(3)}`).join("; ");
      const cell = addCell(`dft([${rows}])`);
      renderSidebar(); focusCell(S.cells.length - 1);
      log("ok", `imported ${f.name}: ${pts.length} sample points along ${paths.length} path${paths.length === 1 ? "" : "s"}`);
      void runCell(cell);
    });
  });
  inp.click();
}
function newNotebook() {
  newDoc(); switchTab("notebook");
  autosave();
  log("ok", "new notebook");
}

/** What the browser keeps between reloads: every open notebook, which one is current, and whether
 *  each had unsaved changes. */
interface Autosave { chalkmath: 1; active: number; docs: { file: ChalkFile; dirty: boolean }[] }

/** The notebooks survive a reload: autosaved to the browser after every run or edit. */
function autosave() {
  stashDoc();
  const doc: Autosave = { chalkmath: 1, active: S.doc, docs: S.docs.map((d) => ({ file: JSON.parse(d.text) as ChalkFile, dirty: docDirty(d) })) };
  try { localStorage.setItem("chalkmath.autosave", JSON.stringify(doc)); } catch { /* storage may be unavailable */ }
}
function restoreAutosave(): string | null {
  try { return localStorage.getItem("chalkmath.autosave") ?? localStorage.getItem("lemma.autosave"); } catch { return null; }
}

// ---------------------------------------------------------------------------
// Cell list operations
// ---------------------------------------------------------------------------

function freshCell(src = "", type: CellType = "math"): Cell {
  const cell: Cell = { id: `c${++cellSeq}`, src, label: null, showWork: false };
  if (type === "markdown") { cell.type = "markdown"; cell.editing = true; }
  if (type === "section") cell.type = "section";
  return cell;
}
function addCell(src = "", type: CellType = "math"): Cell {
  const cell: Cell = freshCell(src, type);
  S.cells.push(cell);
  renderCells();
  return cell;
}
/** Insert a fresh cell at `at` and put the caret in it. */
function insertCell(at: number, type: CellType = "math") {
  S.cells.splice(at, 0, freshCell("", type));
  renderCells(); renderSidebar(); focusCell(at); autosave();
}
/** Make a cell another kind, keeping its text. A cell that stops being mathematics loses its output. */
function convertCell(cell: Cell, type: CellType) {
  const cur: CellType = cell.type ?? "math";
  if (cur === type) return;
  cell.src = cellSrc(cell);
  if (type === "math") delete cell.type; else cell.type = type;
  delete cell.editing; delete cell.collapsed;
  if (type === "markdown") cell.editing = !cell.src.trim();
  if (type !== "math") { delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.error; delete cell.plot; delete cell.hasse; delete cell.summary; cell.steps = []; cell.label = null; }
  if (type === "section") cell.src = cell.src.split("\n")[0]!.replace(/^#+\s*/, "");
  renderCells(); renderSidebar(); renderChrome(); autosave();
}

function focusCell(i: number) {
  S.active = Math.max(0, Math.min(i, S.cells.length - 1));
  renderCells(); renderSidebar(); renderChrome();
  const c = S.cells[S.active];
  // after the render: it rebuilds the inputs, and focus on the old one is lost
  (c?.input ?? c?.ta ?? c?.el?.querySelector<HTMLElement>(".mdout"))?.focus();
}

function clearOutputs() {
  for (const c of S.cells) { delete c.outLatex; delete c.outText; delete c.echoLatex; delete c.error; delete c.plot; c.steps = []; c.label = null; c.ms = undefined; }
  nextLabel = 1; S.sel = null;
  renderCells(); renderSidebar(); renderPanel();
  log("ok", "outputs cleared");
}

function switchTab(t: Tab) {
  S.tab = t;
  hideHover(); hideCompletions();
  if (t !== "studio") stopPlayback();
  renderChrome(); renderView();
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
        main.append(h("div", "toolbar"), h("div", "cells"), h("div", "reference"), h("div", "studio"), h("div", "panel"));
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
  const mark = document.createElement("img"); mark.className = "mark"; mark.src = "logo.svg"; mark.alt = ""; mark.draggable = false;
  brand.append(mark, h("span", "name", "ChalkMath"));
  const menus = h("div", "menus");
  const MENUS: Record<string, [string, () => void][]> = {
    File: [["New notebook", newNotebook], ["Open…", openNotebook], ["Save", () => saveNotebook()], ["Save as…", saveNotebookAs], ["Export to file…", exportNotebook], ["Import from file…", importNotebook], ["Import SVG as epicycles…", importSvg], ["Copy link to notebook", () => void copyNotebookLink()]],
    Edit: [["Add math cell", () => { addCell(); focusCell(S.cells.length - 1); }], ["Add Markdown cell", () => { addCell("", "markdown"); focusCell(S.cells.length - 1); }], ["Add section", () => { addCell("", "section"); focusCell(S.cells.length - 1); }],
      ...(S.cells[S.active] ? CELL_TYPES.filter(([t]) => t !== (S.cells[S.active]!.type ?? "math")).map(([t, label]): [string, () => void] => [`Change to ${label.toLowerCase()}`, () => convertCell(S.cells[S.active]!, t)]) : []),
      ["Clear outputs", clearOutputs]],
    View: [["Toggle light / dark", () => { applyTheme(S.theme === "light" ? "dark" : "light"); renderChrome(); }], ["Explanation panel", () => { S.panelOpen = !S.panelOpen; renderPanelHead(); renderPanel(); }], [`${S.deBruijn ? "✓ " : ""}de Bruijn indices (λ-cells)`, () => { S.deBruijn = !S.deBruijn; renderChrome(); renderCells(); }],
      [`${S.showEcho ? "✓ " : ""}Input interpretation`, () => { S.showEcho = !S.showEcho; try { localStorage.setItem("chalkmath.echo", S.showEcho ? "on" : "off"); } catch { /* private mode */ } renderChrome(); renderCells(); }],
      [`${S.highlight ? "✓ " : ""}Syntax highlighting`, () => { S.highlight = !S.highlight; try { localStorage.setItem("chalkmath.highlight", S.highlight ? "on" : "off"); } catch { /* private mode */ } document.documentElement.classList.toggle("nohl", !S.highlight); renderHighlights(); renderChrome(); }],
      [`${S.sigHelp ? "✓ " : ""}Signature help`, () => { S.sigHelp = !S.sigHelp; try { localStorage.setItem("chalkmath.sighelp", S.sigHelp ? "on" : "off"); } catch { /* private mode */ } if (!S.sigHelp) hideSigHelp(); renderChrome(); }],
      ...(["s", "m", "l"] as const).map((sz): [string, () => void] => [`${S.outSize === sz ? "✓ " : "   "}Math size: ${{ s: "small", m: "normal", l: "large" }[sz]}`, () => {
        S.outSize = sz; document.documentElement.dataset["outsize"] = sz;
        try { localStorage.setItem("chalkmath.outsize", sz); } catch { /* private mode */ }
        renderChrome();
      }])],
    Run: [["Run all", () => void runAll()], ["Run cell", () => { const c = S.cells[S.active]; if (c) void runCell(c); }],
      ...(sectionOf(S.active) >= 0 ? [[`Run section “${(cellSrc(S.cells[sectionOf(S.active)]!) || "untitled").slice(0, 24)}”`, () => void runSection(sectionOf(S.active))] as [string, () => void]] : [])],
    Kernel: [["Restart kernel", () => void restartKernel()], ["Restart and run all", async () => { await restartKernel(); await runAll(); }]],
    Help: [["Reference", () => switchTab("reference")], ["Manim Studio", () => switchTab("studio")]],
  };
  for (const m of Object.keys(MENUS)) {
    const sp = h("span", S.menu === m ? "open" : undefined, m);
    sp.addEventListener("click", (ev) => { ev.stopPropagation(); S.menu = S.menu === m ? null : m; renderChrome(); });
    if (S.menu === m) {
      const dd = h("div", "dropdown");
      for (const [label, act] of MENUS[m]!) {
        const it = h("div", "item", label);
        it.addEventListener("click", (ev) => { ev.stopPropagation(); S.menu = null; renderChrome(); act(); });
        dd.append(it);
      }
      sp.append(dd);
    }
    menus.append(sp);
  }
  const theme = h("span", "themebtn", S.theme === "light" ? "◑ Light" : "◐ Dark");
  theme.title = "Toggle light and dark";
  theme.addEventListener("click", () => { applyTheme(S.theme === "light" ? "dark" : "light"); renderChrome(); if (S.tab === "studio") renderStage(); });
  const kernel = h("div", "kernel");
  const dot = h("span", "dot");
  const state = S.busy ? "running" : S.caps ? "idle" : "offline";
  dot.style.background = S.busy ? "var(--acc)" : S.caps ? "var(--ok)" : "var(--danger)";
  const sel = document.createElement("select");
  for (const [v, label] of [["lean-worker", "kernel · wasm"], ["http", "kernel · http"]] as const) {
    const o = document.createElement("option"); o.value = v; o.textContent = label; o.selected = S.engineMode === v; sel.append(o);
  }
  sel.addEventListener("change", () => { S.engineMode = sel.value as typeof S.engineMode; void connect(); });
  const url = document.createElement("input");
  url.id = "kurl"; url.value = S.httpUrl; url.hidden = S.engineMode !== "http";
  url.addEventListener("change", () => { S.httpUrl = url.value; void connect(); });
  kernel.append(dot, sel, url, h("span", "sep", "·"), h("span", undefined, state));
  tb.append(brand, menus, h("div", "spacer"), theme, kernel);

  // tab bar
  renderTabs();

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
    mk("▶▶ All", "Run every cell in order", () => void runAll()),
    mk("Clear", "Clear all outputs", clearOutputs),
    mk("+ Cell", "Add a cell", () => { const c = addCell(); focusCell(S.cells.indexOf(c)); }),
  );
  tl.append(group, h("div", "spacer"), h("span", "hint", "Enter runs the cell"));

  // status bar
  const sb = $(".statusbar"); sb.innerHTML = "";
  const rules = new Set(S.cells.flatMap((c) => c.steps ?? []).map((s) => s.rule));
  const done = S.cells.filter((c) => c.outLatex || c.error).length;
  sb.append(
    h("span", undefined, `Mode: ${S.tab}`), h("span", "pipe", "|"),
    h("span", undefined, `Cell ${S.active + 1}`), h("span", "pipe", "|"),
    h("span", undefined, `${S.cells.length} cells · ${done} evaluated`),
    h("div", "spacer"),
    h("span", "rules", `${rules.size} rules applied`), h("span", "pipe", "|"),
    h("span", undefined, "type \\ for symbols · Tab completes"),
  );
}

function renderView() {
  $(".cells").hidden = S.tab !== "notebook";
  $(".toolbar").hidden = S.tab === "studio";
  $(".reference").hidden = S.tab !== "reference";
  $(".studio").hidden = S.tab !== "studio";
  $(".panel").hidden = S.tab === "studio";
  if (S.tab === "reference") renderReference();
  if (S.tab === "studio") renderStudio();
}

function renderSidebar() {
  const side = $(".sidebar"); side.innerHTML = "";
  side.append(h("h2", undefined, S.rail === "outline" ? "Notebook outline" : "Engine commands"));
  const list = h("div", "list");
  if (S.rail === "outline") {
    let inSection = false, folded = false;
    S.cells.forEach((c, i) => {
      if (c.type === "section") { inSection = true; folded = !!c.collapsed; }
      else if (folded) return;
      const row = h("div", `olrow${i === S.active ? " on" : ""}${c.type ? ` ${c.type}` : ""}${inSection && c.type !== "section" ? " in" : ""}`);
      if (c.type === "section") {
        const [a, b] = sectionRange(i);
        row.append(h("span", "num", c.collapsed ? "▸" : "§"));
        const wrap = h("span");
        wrap.append(h("span", "kind", c.src || "Untitled section"), h("span", "src", `${b - a} cell${b - a === 1 ? "" : "s"}${c.collapsed ? ", folded" : ""}`));
        row.append(wrap);
      } else if (c.type === "markdown") {
        row.append(h("span", "num", "¶"));
        const wrap = h("span");
        wrap.append(h("span", "kind", "markdown"), h("span", "src", c.src.split("\n").find((l) => l.trim())?.replace(/^#+\s*/, "") || "…"));
        row.append(wrap);
      } else {
        row.append(h("span", "num", c.label ? `[${c.label}]` : "—"));
        const wrap = h("span");
        wrap.append(h("span", "kind", c.kind ?? cellKind(c.src) ?? "empty"), h("span", "src", c.src || "…"));
        row.append(wrap);
      }
      row.addEventListener("click", () => { if (S.tab !== "notebook") switchTab("notebook"); focusCell(i); });
      list.append(row);
    });
  } else {
    for (const d of DOCS) {
      const row = h("div", "plrow");
      row.append(h("span", "name", d.name), h("span", "sig", d.sig));
      row.addEventListener("click", () => {
        if (S.tab !== "notebook") switchTab("notebook");
        const c = S.cells[S.active];
        if (c?.input) { c.input.value = d.examples[0] ?? `${d.name}(`; c.src = c.input.value; c.input.focus(); syncHighlight(c); updateSigHelp(c); renderCellBody(c); renderSidebar(); }
      });
      row.addEventListener("mouseenter", (ev) => showHover(d, ev as MouseEvent));
      row.addEventListener("mouseleave", hideHover);
      list.append(row);
    }
  }
  side.append(list);
}

/** Draw sampled points: axes through the origin when in range, a few labelled ticks, the curve
 *  broken wherever the engine reported no finite value. `frac` draws the first part of the curve
 *  (the studio animates it). A parametric (complex-valued) plot is drawn in the plane with equal
 *  scales on the axes, so a circle is a circle. `t01` in [0, 1] adds the epicycles at that phase. */
function plotSvg(p: PlotData, w: number, hgt: number, frac = 1, t01?: number): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  const parametric = p.series.some((s) => s.parametric);
  const ys = p.series.flatMap((s) => s.points.map((q) => q[1])).filter((y): y is number => y !== null).sort((a, b) => a - b);
  let y0 = -1, y1 = 1, x0 = p.from, x1 = p.to;
  if (ys.length) {
    // trim the tails so an asymptote does not flatten the rest
    const lo = ys[Math.floor(ys.length * 0.02)]!, hi = ys[Math.ceil(ys.length * 0.98) - 1]!;
    y0 = Math.min(lo, 0); y1 = Math.max(hi, 0);
    if (y1 - y0 < 1e-9) { y0 -= 1; y1 += 1; }
    const pad = (y1 - y0) * 0.08; y0 -= pad; y1 += pad;
  }
  if (parametric) {
    // the x range is the real parts', and both axes share one scale; the epicycles' reach counts too —
    // measured, not the sum of all radii (a worst case a llama of 60 circles never comes near)
    const xs = p.series.filter((s) => s.parametric).flatMap((s) => s.points.filter((q) => q[1] !== null).map((q) => q[0]));
    x0 = Math.min(...xs); x1 = Math.max(...xs);
    if (p.terms?.length) {
      const e = epiExtent(p.terms);
      x0 = Math.min(x0, e[0]); x1 = Math.max(x1, e[1]); y0 = Math.min(y0, e[2]); y1 = Math.max(y1, e[3]);
    }
    if (!isFinite(x0) || !isFinite(x1)) { x0 = -1; x1 = 1; }
    if (x1 - x0 < 1e-9) { x0 -= 1; x1 += 1; }
    const padx = (x1 - x0) * 0.08; x0 -= padx; x1 += padx;
    const pw = w - 48, ph = hgt - 34;
    const scale = Math.min(pw / (x1 - x0), ph / (y1 - y0));
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
    x0 = cx - pw / scale / 2; x1 = cx + pw / scale / 2; y0 = cy - ph / scale / 2; y1 = cy + ph / scale / 2;
  }
  const L = 38, R = 10, T = 10, B = 24;
  const sx = (x: number) => L + ((x - x0) / (x1 - x0 || 1)) * (w - L - R);
  const sy = (y: number) => T + ((y1 - y) / (y1 - y0)) * (hgt - T - B);
  const line = (x1: number, yA: number, x2: number, yB: number, cls: string) => {
    const l = document.createElementNS(NS, "line");
    l.setAttribute("x1", String(x1)); l.setAttribute("y1", String(yA)); l.setAttribute("x2", String(x2)); l.setAttribute("y2", String(yB));
    l.setAttribute("class", cls); svg.append(l);
  };
  const text = (x: number, y: number, t: string, cls: string) => {
    const e = document.createElementNS(NS, "text");
    e.setAttribute("x", String(x)); e.setAttribute("y", String(y)); e.setAttribute("class", cls); e.textContent = t; svg.append(e);
  };
  // a tick within a thousandth of the span of zero is zero (an off-centre frame lands one at −4.3e-3)
  const span = Math.max(x1 - x0, y1 - y0);
  const nice = (v: number) => Math.abs(v) < Math.max(1e-9, span * 1e-3) ? "0" : (Math.abs(v) >= 1000 || Math.abs(v) < 0.01 ? v.toExponential(1) : String(Math.round(v * 100) / 100));
  // frame and axes
  line(L, T, L, hgt - B, "axis"); line(L, hgt - B, w - R, hgt - B, "axis");
  if (y0 < 0 && y1 > 0) line(L, sy(0), w - R, sy(0), "zero");
  if (x0 < 0 && x1 > 0) line(sx(0), T, sx(0), hgt - B, "zero");
  for (let k = 0; k <= 4; k++) {
    const x = x0 + ((x1 - x0) * k) / 4, y = y0 + ((y1 - y0) * k) / 4;
    line(sx(x), hgt - B, sx(x), hgt - B + 4, "tick"); text(sx(x), hgt - 6, nice(x), "tl");
    line(L - 4, sy(y), L, sy(y), "tick"); text(L - 6, sy(y) + 3, nice(y), "tl r");
  }
  // the epicycles' tip at phase t01: the trace is drawn up to the last sample at or before it and
  // then to the tip itself, so the pen never runs ahead of (or lags) the dot
  const tip = p.terms?.length && t01 !== undefined ? epiTip(p.terms, t01 * 2 * Math.PI) : null;
  // the curves, each in segments
  p.series.forEach((s, si) => {
    const n = tip && t01 !== undefined
      ? Math.min(s.points.length, Math.floor(t01 * s.points.length) + 1)       // sample j is at t = 2πj/N
      : Math.max(0, Math.min(s.points.length, Math.round(s.points.length * frac)));
    let d = "", pen = false;
    for (let i = 0; i < n; i++) {
      const [x, y] = s.points[i]!;
      if (y === null || (!s.parametric && (y < y0 || y > y1))) { pen = false; continue; }
      d += `${pen ? "L" : "M"}${sx(x).toFixed(1)} ${sy(y).toFixed(1)} `; pen = true;
    }
    if (tip && pen) d += `L${sx(tip[0]).toFixed(1)} ${sy(tip[1]).toFixed(1)} `;
    const path = document.createElementNS(NS, "path");
    path.setAttribute("d", d); path.setAttribute("class", `curve c${si % CURVE_COLOURS}`); svg.append(path);
  });
  // the epicycles at phase t01: circles tip to tail, each spinning at its frequency
  if (p.terms?.length && t01 !== undefined) {
    const t = t01 * 2 * Math.PI;
    let x = 0, y = 0;
    const g = document.createElementNS(NS, "g"); g.setAttribute("class", "epi");
    for (const c of p.terms) {
      const r = Math.hypot(c.re, c.im), ph = Math.atan2(c.im, c.re);
      const nx = x + r * Math.cos(c.k * t + ph), ny = y + r * Math.sin(c.k * t + ph);
      if (c.k !== 0) {
        const circ = document.createElementNS(NS, "circle");
        circ.setAttribute("cx", String(sx(x))); circ.setAttribute("cy", String(sy(y)));
        circ.setAttribute("r", String(r * (w - L - R) / (x1 - x0 || 1))); circ.setAttribute("class", "epicircle"); g.append(circ);
      }
      const l = document.createElementNS(NS, "line");
      l.setAttribute("x1", String(sx(x))); l.setAttribute("y1", String(sy(y))); l.setAttribute("x2", String(sx(nx))); l.setAttribute("y2", String(sy(ny)));
      l.setAttribute("class", "epiarm"); g.append(l);
      x = nx; y = ny;
    }
    const tip = document.createElementNS(NS, "circle");
    tip.setAttribute("cx", String(sx(x))); tip.setAttribute("cy", String(sy(y))); tip.setAttribute("r", "3"); tip.setAttribute("class", "epitip");
    g.append(tip); svg.append(g);
  }
  if (!parametric) text(w - R, T + 10, `${p.var}`, "tl r");
  return svg;
}

/** Where the epicycles' tip is at angle `t`: `Σ c_k e^{i k t}`, the terms tip to tail. */
function epiTip(terms: Epicycle[], t: number): [number, number] {
  let x = 0, y = 0;
  for (const c of terms) { const r = Math.hypot(c.re, c.im), ph = Math.atan2(c.im, c.re); x += r * Math.cos(c.k * t + ph); y += r * Math.sin(c.k * t + ph); }
  return [x, y];
}

/** How far the epicycles actually swing: the box around every joint of the chain, each padded by
 *  the circle it carries, over 96 phases of the lap — `[x0, x1, y0, y1]`. */
function epiExtent(terms: Epicycle[]): [number, number, number, number] {
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  const polar = terms.map((c) => [Math.hypot(c.re, c.im), Math.atan2(c.im, c.re), c.k] as const);
  for (let j = 0; j < 96; j++) {
    const t = (2 * Math.PI * j) / 96;
    let x = 0, y = 0;
    for (const [r, ph, k] of polar) {
      x0 = Math.min(x0, x - r); x1 = Math.max(x1, x + r); y0 = Math.min(y0, y - r); y1 = Math.max(y1, y + r);
      x += r * Math.cos(k * t + ph); y += r * Math.sin(k * t + ph);
    }
    x0 = Math.min(x0, x); x1 = Math.max(x1, x); y0 = Math.min(y0, y); y1 = Math.max(y1, y);
  }
  return [x0, x1, y0, y1];
}

/** The epicycle animation in a cell: redraw at the phase of a 12-second loop while the box is on
 *  screen. Returns the box; the loop stops when the box leaves the document. */
function epicycleBox(p: PlotData, w: number, hgt: number): HTMLElement {
  const box = h("div", "plotbox epibox");
  const period = 12000;
  let start = performance.now();
  const draw = () => {
    const t01 = ((performance.now() - start) % period) / period;
    const svg = plotSvg(p, w, hgt, 1, t01);
    box.replaceChildren(svg);
  };
  draw();
  let raf = 0;
  const loop = () => { if (!box.isConnected) return; draw(); raf = requestAnimationFrame(loop); };
  const io = new IntersectionObserver((es) => {
    for (const e of es) { if (e.isIntersecting) { if (!raf) { start = performance.now(); raf = requestAnimationFrame(loop); } } else { cancelAnimationFrame(raf); raf = 0; } }
  });
  io.observe(box);
  return box;
}

/** A Hasse diagram: elements in layers by height, covers as edges, nothing else. */
function hasseSvg(d: { nodes: { name: string; height: number }[]; covers: [string, string][] }): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const layers = new Map<number, string[]>();
  for (const n of d.nodes) layers.set(n.height, [...(layers.get(n.height) ?? []), n.name]);
  const H = Math.max(0, ...d.nodes.map((n) => n.height));
  const widest = Math.max(1, ...[...layers.values()].map((l) => l.length));
  const cw = Math.max(70, Math.min(120, 520 / widest)), w = Math.max(240, widest * cw + 40), rowH = 64, h = (H + 1) * rowH + 24;
  const pos = new Map<string, [number, number]>();
  for (const [ht, names] of layers) names.forEach((name, i) => pos.set(name, [20 + (i + 0.5) * ((w - 40) / names.length), h - 12 - (ht + 0.5) * rowH]));
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("viewBox", `0 0 ${w} ${h}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(h));
  for (const [a, b] of d.covers) {
    const p = pos.get(a), q = pos.get(b); if (!p || !q) continue;
    const l = document.createElementNS(NS, "line");
    l.setAttribute("x1", String(p[0])); l.setAttribute("y1", String(p[1])); l.setAttribute("x2", String(q[0])); l.setAttribute("y2", String(q[1]));
    l.setAttribute("class", "hedge"); svg.append(l);
  }
  for (const [name, [x, y]] of pos) {
    const c = document.createElementNS(NS, "circle");
    c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "hnode"); svg.append(c);
    const t = document.createElementNS(NS, "text");
    t.setAttribute("x", String(x + 9)); t.setAttribute("y", String(y - 7)); t.setAttribute("class", "hlabel"); t.textContent = name; svg.append(t);
  }
  return svg;
}

/** A complex number as LaTeX, to a few digits. */
function fmtC(re: number, im: number): string {
  const f = (v: number) => (Math.abs(v) < 1e-12 ? "0" : String(Math.round(v * 1000) / 1000));
  if (Math.abs(im) < 1e-12) return f(re);
  if (Math.abs(re) < 1e-12) return `${f(im)}i`;
  return `${f(re)} ${im < 0 ? "-" : "+"} ${f(Math.abs(im))}i`;
}

/** The sampled function as a Python expression for Manim: `3*x^2 + sin(x)` → `3*x**2 + np.sin(x)`. */
function pyExpr(text: string): string {
  return text.replace(/\^/g, "**")
    .replace(/\b(sin|cos|tan|exp|sqrt|abs)\(/g, "np.$1(")
    .replace(/\bln\(/g, "np.log(").replace(/\blog\(/g, "np.log10(")
    .replace(/\bpi\b/g, "np.pi").replace(/\be\b/g, "np.e");
}

function renderCells() {
  hideHover(); hideSigHelp();
  const host = $(".cells");
  host.innerHTML = "";
  let folded = false;   // inside a collapsed section: its cells are not built
  S.cells.forEach((cell, i) => {
    if (cell.type === "section") folded = !!cell.collapsed;
    else if (folded) { delete cell.el; delete cell.input; delete cell.ta; delete cell.hl; return; }
    const el = h("div", `cell${i === S.active ? " active" : ""}${cell.label ? " done" : ""}${cell.type ? ` ${cell.type}` : ""}`);
    cell.el = el;
    delete cell.input; delete cell.ta; delete cell.hl;
    if (cell.type === "markdown") {
      el.append(h("div", "prompt", ""));
      const mid = h("div", "mid");
      el.append(mid);
      const acts = h("div", "cellacts");
      el.append(acts, h("div", "brk"));
      insertGap(host, i);
      host.append(el);
      renderCellBody(cell);
      return;
    }
    if (cell.type === "section") {
      el.append(h("div", "prompt", "§"));
      const mid = h("div", "mid");
      const row = h("div", "sectrow");
      const tog = h("span", "secttog", cell.collapsed ? "▸" : "▾");
      tog.title = cell.collapsed ? "Show this section's cells" : "Fold this section's cells away";
      tog.addEventListener("mousedown", (e) => e.preventDefault());
      tog.addEventListener("click", () => { cell.collapsed = !cell.collapsed; S.active = i; renderCells(); renderSidebar(); autosave(); });
      const input = document.createElement("input");
      input.className = "sectin"; input.type = "text"; input.value = cell.src; input.placeholder = "Section title"; input.spellcheck = false;
      cell.input = input;
      input.addEventListener("focus", () => { S.active = i; renderChrome(); renderSidebar(); markActive(); });
      input.addEventListener("input", () => { cell.src = input.value; renderSidebar(); renderTabs(); });
      input.addEventListener("keydown", (ev) => {
        if (ev.key === "Enter") { ev.preventDefault(); cell.src = input.value; if (i === S.cells.length - 1) addCell(); focusCell(i + 1); autosave(); }
        if (ev.key === "ArrowDown" && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
        if (ev.key === "ArrowUp" && i > 0) { ev.preventDefault(); focusCell(i - 1); }
      });
      row.append(tog, input);
      const [a, b] = sectionRange(i);
      if (cell.collapsed) row.append(h("span", "sectcount", `${b - a} cell${b - a === 1 ? "" : "s"} folded`));
      mid.append(row);
      el.append(mid);
      const acts = h("div", "cellacts");
      const run = h("span", undefined, "▶ Run section"); run.title = "Run every cell of this section, in order";
      run.addEventListener("mousedown", (e) => e.preventDefault());
      run.addEventListener("click", () => void runSection(i));
      acts.append(run);
      el.append(acts, h("div", "brk"));
      insertGap(host, i);
      host.append(el);
      renderCellBody(cell);
      return;
    }
    el.append(h("div", "prompt", `In[${cell.label ?? " "}]:=`));

    const mid = h("div", "mid");
    const input = document.createElement("input");
    input.className = "cellin"; input.type = "text"; input.value = cell.src;
    input.placeholder = i === 0 ? "e.g. diff(x^2 * sin(x), x)" : "";
    input.spellcheck = false;
    cell.input = input;
    input.addEventListener("focus", () => { S.active = i; renderChrome(); renderSidebar(); markActive(); });
    input.addEventListener("input", () => { cell.src = input.value; updateCompletions(cell); updateSigHelp(cell); syncHighlight(cell); renderSidebar(); renderTabs(); });
    input.addEventListener("keyup", () => { updateSigHelp(cell); syncHighlight(cell); });   // caret moves without an input event
    input.addEventListener("click", () => updateSigHelp(cell));
    input.addEventListener("scroll", () => syncHighlight(cell));
    input.addEventListener("blur", () => { hideCompletions(); hideSigHelp(); });
    input.addEventListener("keydown", (ev) => onKey(ev, cell, i));
    // the highlight overlay sits under the transparent text of the input; the input keeps caret and selection
    const hl = h("div", "hl"); hl.setAttribute("aria-hidden", "true");
    cell.hl = hl;
    mid.append(hl, input);
    syncHighlight(cell);

    const body = h("div", "cellbody");
    mid.append(body);
    el.append(mid);

    const acts = h("div", "cellacts");
    const run = h("span", undefined, "▶ Run"); run.title = "Run this cell";
    run.addEventListener("mousedown", (e) => e.preventDefault());
    run.addEventListener("click", () => void runCell(cell));
    acts.append(run);
    el.append(acts, h("div", "brk"));
    insertGap(host, i);
    host.append(el);
    renderCellBody(cell);
  });
  insertGap(host, S.cells.length);
  markActive();
}

/** A thin strip between cells (and after the last): hovering shows a rule with a `+ cell` pill, a
 *  click inserts a fresh cell there — Mathematica's cell insertion bar. */
function insertGap(host: HTMLElement, at: number) {
  const gap = h("div", "gap");
  const pill = h("span", "gappill");
  const main = h("span", "gapmain", "+ cell"); main.title = "Insert a math cell here";
  const more = h("span", "gapmore", "▾"); more.title = "Insert a cell of another kind";
  pill.append(main, more);
  gap.append(pill);
  gap.addEventListener("click", (ev) => { if (ev.target === more) return; insertCell(at); });
  more.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); typeMenu(more, (t) => insertCell(at, t)); });
  host.append(gap);
}

const CELL_TYPES: [CellType, string, string][] = [
  ["math", "Math cell", "An input for the engine: In[n]:= …"],
  ["markdown", "Markdown text", "Prose with $math$, $$display math$$, `code` and ``` blocks"],
  ["section", "Section heading", "Groups the cells below it: run them together, fold them away"],
];
/** A small menu of the cell kinds under `anchor`; `pick` gets the chosen one. */
function typeMenu(anchor: HTMLElement, pick: (t: CellType) => void, current?: CellType) {
  const menu = h("div", "cellmenu typemenu");
  for (const [t, label, hint] of CELL_TYPES) {
    const it = h("div", `item${t === current ? " on" : ""}`);
    it.append(h("span", undefined, `${t === current ? "✓ " : ""}${label}`), h("span", "hint", hint));
    it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); pick(t); });
    menu.append(it);
  }
  document.body.append(menu);
  const r = anchor.getBoundingClientRect(), mh = menu.offsetHeight;
  const below = r.bottom + 4 + mh <= window.innerHeight - 8;
  menu.style.top = `${below ? r.bottom + 4 : Math.max(8, r.top - 4 - mh)}px`;
  menu.style.left = `${Math.max(8, Math.min(r.left, window.innerWidth - menu.offsetWidth - 8))}px`;
}

function markActive() {
  S.cells.forEach((c, i) => c.el?.classList.toggle("active", i === S.active));
}

/** A step's explanation for the row: the Lean names (in backticks, usually parenthesized) belong in the panel, not here. */
function plainWhy(md: string): string {
  let out = "";
  for (let i = 0; i < md.length; i++) {
    if (md[i] === "(") {
      const j = md.indexOf(")", i);
      if (j > i && md.slice(i, j).includes("`")) { i = j; out = out.trimEnd(); continue; }
    }
    out += md[i];
  }
  return out.replace(/`([^`]*)`/g, "$1").replace(/\s+([.,;:])/g, "$1").trim();
}

/** A step's headline and the rest of its explanation. The rules name themselves ("Power rule: …",
 *  "Distributive law: …"); the machine name (`diff.power`) is for the tooltip and the panel. When an
 *  explanation has no such lead, the name is read off the rule id: `simp.fold-constants` → "Fold constants". */
function stepTitle(st: Step): { title: string; rest: string } {
  const plain = plainWhy(st.explanation);
  const m = /^([^:$]{3,44}?):\s+(.*)$/s.exec(plain);
  if (m) return { title: m[1]!, rest: m[2]! };
  // diff.chain on a bare variable is just the function's derivative ("sin' = cos."): say so
  const fn = st.rule === "diff.chain" ? /^(\w+)' = /.exec(plain) : null;
  if (fn) return { title: `Derivative of ${fn[1]}`, rest: plain };
  const tail = st.rule.split(".").pop() ?? st.rule;
  return { title: RULE_NAMES[st.rule] ?? tail.replace(/-/g, " ").replace(/^\w/, (c) => c.toUpperCase()), rest: plain };
}
/** Names for the rules whose explanations do not name them. */
const RULE_NAMES: Record<string, string> = {
  "diff.chain": "Chain rule", "diff.sum": "Sum rule", "diff.product": "Product rule", "diff.power": "Power rule", "diff.variable": "Derivative of the variable",
  "diff.constant": "Derivative of a constant", "diff.constant-multiple": "Constant multiple rule", "diff.higher-order": "Higher derivative", "diff.matrix": "Entrywise derivative",
  "simp.power": "Power identity", "simp.identity": "Identity", "simp.flatten": "Flatten", "simp.sort": "Reorder", "simp.function": "Function value",
  "simp.fold-constants": "Arithmetic on constants", "simp.collect-like-terms": "Collect like terms", "simp.collect-powers": "Collect powers", "simp.collect-radicals": "Collect radicals",
  "simp.radical": "Radical", "simp.exp-product": "Exponentials multiply", "expand.distribute": "Distribute", "expand.power": "Expand the power",
  "cx.euler": "Euler's formula", "cx.euler-power": "Euler's formula", "cx.arithmetic": "Complex arithmetic", "cx.i-power": "Power of i", "cx.re-im": "Real and imaginary parts",
  "cx.conjugate": "Conjugate", "cx.abs": "Modulus", "cx.exact-trig": "Exact value", "cx.power": "Complex power",
  "la.row-swap": "Swap rows", "la.row-scale": "Scale a row", "la.row-add": "Add a multiple of a row", "la.det": "Determinant", "la.mul": "Matrix product", "la.add": "Matrix sum",
  "la.scalar-mul": "Scalar multiple", "la.transpose": "Transpose", "la.pow": "Matrix power", "la.dot": "Dot product", "la.norm": "Norm", "la.conj": "Conjugate", "la.context": "Matrix context",
  "int.check": "Check by differentiating", "int.compare": "Compare with the integrand", "int.bounds": "Evaluate at the bounds", "int.table": "Table integral", "int.power": "Power rule for integrals",
  "int.variable": "Integral of the variable", "int.constant": "Integral of a constant", "int.constant-multiple": "Constant multiple", "int.sum": "Sum rule for integrals",
  "int.exponential": "Exponential integral", "int.exp-power": "Exponential of a power", "int.substitution": "Substitution", "int.linear-substitution": "Linear substitution",
  "int.by-parts": "Integration by parts", "int.trig-power": "Trigonometric power",
  "cmd.rref": "Row reduce", "cmd.integrate": "Integrate", "cmd.expand": "Expand", "cmd.subst": "Substitute", "cmd.simplify": "Simplify", "cmd.sum": "Sum", "cmd.exptotrig": "Euler's formula",
};

/** The paths at which two terms differ: the smallest subterms that changed. Children are compared
 *  one to one where the node kind and arity agree; otherwise the node itself is the change. The
 *  indices follow the renderer's paths (a matrix entry is `row·width + column`). */
function changedPaths(a: WireExpr, b: WireExpr, path: Path = [], out: Path[] = []): Path[] {
  if (JSON.stringify(a) === JSON.stringify(b)) return out;
  if (a.k === b.k) {
    if ((a.k === "add" || a.k === "mul" || a.k === "fn") && (b.k === "add" || b.k === "mul" || b.k === "fn")
        && (a.k !== "fn" || b.k !== "fn" || a.name === b.name) && a.args.length === b.args.length) {
      a.args.forEach((x, i) => changedPaths(x, b.args[i]!, [...path, i], out));
      return out;
    }
    if (a.k === "pow" && b.k === "pow") { changedPaths(a.base, b.base, [...path, 0], out); changedPaths(a.exp, b.exp, [...path, 1], out); return out; }
    if (a.k === "matrix" && b.k === "matrix" && a.rows.length === b.rows.length && a.rows.every((r, i) => r.length === b.rows[i]!.length)) {
      const w = a.rows[0]?.length ?? 0;
      a.rows.forEach((r, i) => r.forEach((x, j) => changedPaths(x, b.rows[i]![j]!, [...path, i * w + j], out)));
      return out;
    }
  }
  out.push(path);
  return out;
}

/** What each step changed, in place: the subterms a step rewrote (`before` against `after`) are
 *  tinted in its row, and hovering one shows `old → new`, cut from the step's own renderings of
 *  `before` and `after` (the row above is not always `before`: the pipeline flattens and reorders
 *  silently between recorded steps). A change at the root is the whole line: no tint. */
function markChanges(rows: HTMLElement[], d: Derivation) {
  d.steps.forEach((st, n) => {
    const el = rows[n]?.querySelector<HTMLElement>(".el"); if (!el) return;
    const beforeLatex = st.beforeRendered?.latex ?? (n === 0 ? d.inputRendered?.latex : undefined);
    for (const p of changedPaths(st.before, st.after)) {
      if (!p.length) continue;
      const now = el.querySelector<HTMLElement>(`[data-path="${p.join(".")}"]`); if (!now) continue;
      now.classList.add("chg");
      const old = beforeLatex ? pathLatex(beforeLatex, p) : null;
      const neu = st.afterRendered ? pathLatex(st.afterRendered.latex, p) : null;
      if (old === null || neu === null) continue;
      now.addEventListener("mouseenter", () => showDiffTip(now, stripPaths(old), stripPaths(neu)));
      now.addEventListener("mouseleave", hideDiffTip);
    }
  });
}
/** The `old → new` of a changed subterm, typeset, floating above it. */
function showDiffTip(anchor: HTMLElement, oldTex: string, newTex: string) {
  hideDiffTip();
  const tip = h("div", "difftip");
  const a = h("span", "was"); a.innerHTML = tex(oldTex);
  const b = h("span", "now"); b.innerHTML = tex(newTex);
  tip.append(a, h("span", "arrow", "→"), b);
  document.body.append(tip);
  const r = anchor.getBoundingClientRect();
  tip.style.left = `${Math.max(8, Math.min(r.left + r.width / 2 - tip.offsetWidth / 2, window.innerWidth - tip.offsetWidth - 8))}px`;
  tip.style.top = `${r.top - tip.offsetHeight - 8 < 8 ? r.bottom + 8 : r.top - tip.offsetHeight - 8}px`;
}
function hideDiffTip() { document.querySelector(".difftip")?.remove(); }

/** Re-render everything below a cell's input, leaving the input element untouched. */
function renderCellBody(cell: Cell) {
  const el = cell.el; if (!el) return;
  hideDiffTip();
  if (cell.type === "markdown") return renderMdCell(cell);
  if (cell.type === "section") return appendMore(cell, el.querySelector(".cellacts")!);
  el.classList.toggle("done", !!cell.label);
  el.querySelector(".prompt")!.textContent = `In[${cell.label ?? " "}]:=`;
  const mid = el.querySelector(".mid")!;
  const body = mid.querySelector(".cellbody") as HTMLElement;
  body.innerHTML = "";

  if (cell.echoLatex && S.showEcho) {
    const echo = h("div", "echo");
    echo.innerHTML = tex(cell.echoLatex, true);
    wireTerm(echo, cell, { kind: "input" });
    body.append(echo);
  }


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
    const stepRow = (st: Step, label: string, status: string, term?: TermRef, sub?: { steps: Step[]; index: number; top: number }): HTMLElement => {
      const row = h("div", "step");
      row.append(h("span", "no", label));
      const rulecol = h("span", "rulecol");
      const rule = h("span", "rule");
      const mark = h("span", `vmark ${status}`);
      const { title, rest } = stepTitle(st);
      // the headline is the rule's own name for itself ("Power rule"); the machine name lives in the tooltip and the panel
      mark.title = ruleStatusIn(st.rule, cellComplex(cell)).note;
      rule.append(mark, document.createTextNode(title));
      rule.title = `${st.rule} — ${ruleStatusIn(st.rule, cellComplex(cell)).note}`;
      rulecol.append(rule);
      // what the rule did, in the row itself (the panel repeats it in full)
      if (rest) { const why = inlineMath(rest, "why"); why.title = rest.replace(/\$/g, ""); rulecol.append(why); }
      row.append(rulecol);
      const el = h("span", "el");
      const shown = S.deBruijn && st.afterDeBruijn ? st.afterDeBruijn : st.afterRendered;
      if (shown) {
        el.innerHTML = tex(shown.latex, true);
        if (term && shown === st.afterRendered) wireTerm(el, cell, term);
        else if (sub && shown === st.afterRendered) {
          // a nested step's term: selectable locally (the engine traces top-level terms only)
          el.dataset["term"] = `sub:${label}`;
          el.querySelectorAll<HTMLElement>("[data-path]").forEach((span) => {
            span.addEventListener("click", (ev) => {
              ev.stopPropagation();
              const raw = span.dataset["path"]!;
              selectSubStep(cell, sub.steps, sub.index, label, sub.top, raw === "root" ? [] : raw.split(".").map(Number));
            });
          });
        }
      }
      else el.append(inlineMath(st.explanation));
      row.append(el);
      return row;
    };
    // Nested derivations (rref's row operations, integrate's finder and its check) render below
    // their step, indented one level per depth and numbered 1.2, 1.2.3, …
    const renderSub = (st: Step, label: string, top: number, depth: number) => {
      const rows: HTMLElement[] = [];
      st.sub?.steps.forEach((sub, k) => {
        const l = `${label}.${k + 1}`;
        const srow = stepRow(sub, l, statusOf(sub, cellComplex(cell)), undefined, { steps: st.sub!.steps, index: k, top });
        srow.classList.add("sub");
        srow.style.marginLeft = `${26 * depth}px`;
        srow.title = sub.explanation.replace(/\$/g, "");
        srow.addEventListener("click", (ev) => { ev.stopPropagation(); selectSubStep(cell, st.sub!.steps, k, l, top); });
        work.append(srow);
        rows.push(srow);
        renderSub(sub, l, top, depth + 1);
      });
      if (st.sub) markChanges(rows, st.sub);
    };
    const rows: HTMLElement[] = [];
    cell.steps.forEach((st, n) => {
      const row = stepRow(st, String(n + 1), statusOf(st, cellComplex(cell)), { kind: "step", index: n });
      row.addEventListener("click", () => void explain(cell, { kind: "step", index: n }, []));
      work.append(row);
      rows.push(row);
      renderSub(st, String(n + 1), n, 1);
    });
    // the cell keeps the steps, not the derivation: its input is the first step's before, rendered as the echo
    const first = cell.steps[0]!;
    markChanges(rows, { input: first.before, steps: cell.steps, output: cell.steps[cell.steps.length - 1]!.after, ...(cell.echoLatex ? { inputRendered: { text: "", latex: cell.echoLatex } } : {}) });
    body.append(work);
  }

  const old = el.querySelector(".outrow"); old?.remove();
  if (cell.outLatex) {
    const out = h("div", "outrow");
    out.append(h("div", "prompt", `Out[${cell.label}]=`));
    const val = h("div", "outval");
    if (cell.hasse) {
      const box = h("div", "plotbox");
      box.append(hasseSvg(cell.hasse));
      const cap = h("div", "plotcap", cell.summary ?? "");
      val.classList.add("isplot");
      val.append(box, cap);
    } else if (cell.plot) {
      const epi = !!cell.plot.terms?.length;
      const box = epi ? epicycleBox(cell.plot, 520, 320) : h("div", "plotbox");
      if (!epi) box.append(plotSvg(cell.plot, 520, cell.plot.series.some((s) => s.parametric) ? 320 : 240));
      const cap = h("div", "plotcap");
      if (epi) {
        const terms = cell.plot.terms!;
        const shown = terms.slice(0, 8);
        cap.append(h("span", "epinote", `${terms.length} circle${terms.length === 1 ? "" : "s"}: `));
        shown.forEach((c, i) => {
          const it = h("span", "legend");
          const lab = c.latex ? `k=${c.k}:\ ${c.latex}` : `k=${c.k}:\ ${fmtC(c.re, c.im)}`;
          it.insertAdjacentHTML("beforeend", tex(lab));
          cap.append(it, i < shown.length - 1 ? document.createTextNode(" ") : "");
        });
        if (terms.length > shown.length) cap.append(h("span", "epinote", `… (${terms.length - shown.length} more)`));
        cap.append(h("div", "epinote", "The circles' radii and phases are the coefficients' modulus and argument; the trace is the sum. Sampling is numeric."));
      } else if (cell.plot.series.length > 1) {
        cell.plot.series.forEach((s, i) => {
          const it = h("span", `legend c${i % CURVE_COLOURS}`);
          it.append(h("i", "swatch")); it.insertAdjacentHTML("beforeend", tex(s.latex));
          it.title = "Explain this curve";
          it.addEventListener("click", () => void explain(cell, { kind: "output" }, [i]));   // entry i of the list
          cap.append(it);
        });
      } else {
        cap.innerHTML = tex(cell.outLatex, true);
        wireTerm(cap, cell, { kind: "output" });
      }
      val.classList.add("isplot");
      val.append(box, cap);
    } else if (S.deBruijn && cell.outDeBruijn) {
      val.innerHTML = tex(cell.outDeBruijn, true);
    } else if (cell.form === "input") {
      val.append(h("code", "outtext", cell.outText ?? ""));
    } else {
      val.innerHTML = tex(formLatex(cell.outLatex, cell.form), true);
      wireTerm(val, cell, { kind: "output" });
    }
    // the output form: a per-cell choice of typesetting, like Mathematica's //MatrixForm
    if (!cell.hasse && !cell.plot) {
      const forms = formsFor(cell);
      const fs = document.createElement("select"); fs.className = "formsel"; fs.title = "Output form";
      for (const [v, label] of forms) { const o = document.createElement("option"); o.value = v; o.textContent = label; o.selected = (cell.form ?? forms[0]![0]) === v; fs.append(o); }
      fs.addEventListener("mousedown", (e) => e.stopPropagation());
      fs.addEventListener("change", () => { if (fs.value === forms[0]![0]) delete cell.form; else cell.form = fs.value; renderCellBody(cell); autosave(); });
      out.querySelector(".prompt")!.append(fs);
    }
    if (cell.reading) { const rd = h("span", "reading", `≡ ${cell.reading}`); rd.title = "What the normal form encodes"; val.append(rd); }
    if (cell.summary && !cell.hasse) { const rd = h("span", "reading", cell.summary); val.append(rd); }
    out.append(val, h("div", "brk"));
    el.append(out);
  }
  markSelection();

  // per-cell actions beyond Run exist only once there is output
  const acts = el.querySelector(".cellacts")!;
  while (acts.childElementCount > 1) acts.lastElementChild!.remove();
  if (cell.steps?.length) {
    const tw = h("span", undefined, cell.showWork ? "▾ Hide work" : `▸ Work (${cell.steps.length})`);
    tw.addEventListener("mousedown", (e) => e.preventDefault());
    tw.addEventListener("click", () => { cell.showWork = !cell.showWork; renderCellBody(cell); });
    acts.append(tw);
  }
  appendMore(cell, acts);
}

/** The ⋮ button at the end of a cell's actions (replacing any there). */
function appendMore(cell: Cell, acts: Element) {
  acts.querySelector(".more")?.remove();
  const more = h("span", "more", "⋮"); more.title = "Cell actions";
  more.addEventListener("mousedown", (e) => e.preventDefault());
  more.addEventListener("click", (ev) => { ev.stopPropagation(); toggleCellMenu(cell, more); });
  acts.append(more);
}

/** A Markdown cell: its editor while editing (Shift+Enter renders), its rendering otherwise
 *  (double-click or Enter edits). */
function renderMdCell(cell: Cell) {
  const el = cell.el; if (!el) return;
  const i = S.cells.indexOf(cell);
  const mid = el.querySelector(".mid") as HTMLElement; mid.innerHTML = "";
  delete cell.ta;
  const edit = () => { cell.editing = true; renderMdCell(cell); cell.ta?.focus(); };
  const onFocus = () => { S.active = i; renderChrome(); renderSidebar(); markActive(); };
  if (cell.editing) {
    const ta = document.createElement("textarea");
    ta.className = "mdin"; ta.value = cell.src; ta.rows = 1; ta.spellcheck = true;
    ta.placeholder = "Markdown: # heading, *emphasis*, $x^2$ and $$∫ f$$, `code`, ``` blocks — Shift+Enter renders";
    cell.ta = ta;
    const grow = () => { ta.style.height = "auto"; ta.style.height = `${ta.scrollHeight + 2}px`; };
    ta.addEventListener("focus", onFocus);
    ta.addEventListener("input", () => { cell.src = ta.value; grow(); renderSidebar(); renderTabs(); });
    ta.addEventListener("keydown", (ev) => {
      if ((ev.key === "Enter" && (ev.shiftKey || ev.metaKey || ev.ctrlKey)) || ev.key === "Escape") { ev.preventDefault(); void runCell(cell); return; }
      const caret = ta.selectionStart ?? 0;
      if (ev.key === "ArrowDown" && i < S.cells.length - 1 && !ta.value.slice(caret).includes("\n")) { ev.preventDefault(); focusCell(i + 1); }
      if (ev.key === "ArrowUp" && i > 0 && !ta.value.slice(0, caret).includes("\n")) { ev.preventDefault(); focusCell(i - 1); }
    });
    mid.append(ta);
    grow();   // the cell is in the document already: scrollHeight is real
  } else {
    let out: HTMLElement;
    if (cell.src.trim()) out = mdRender(cell.src);
    else { out = h("div", "mdout"); out.append(h("span", "mdempty", "Empty Markdown cell — double-click to write")); }
    out.tabIndex = 0;
    out.addEventListener("focus", onFocus);
    out.addEventListener("dblclick", edit);
    out.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter") { ev.preventDefault(); edit(); }
      if (ev.key === "ArrowDown" && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
      if (ev.key === "ArrowUp" && i > 0) { ev.preventDefault(); focusCell(i - 1); }
    });
    mid.append(out);
  }
  const acts = el.querySelector(".cellacts")!; acts.innerHTML = "";
  const btn = h("span", undefined, cell.editing ? "▶ Render" : "✎ Edit");
  btn.title = cell.editing ? "Render the Markdown (Shift+Enter)" : "Edit the text (double-click)";
  btn.addEventListener("mousedown", (e) => e.preventDefault());
  btn.addEventListener("click", () => { if (cell.editing) void runCell(cell); else edit(); });
  acts.append(btn);
  appendMore(cell, acts);
}

// ---------------------------------------------------------------------------
// Markdown: a small renderer for prose cells — headings, paragraphs, lists, quotes, rules, fenced
// code, `code`, *emphasis*, links and images, and mathematics in $…$ and $$…$$ (KaTeX). It builds
// DOM nodes, never HTML from the text, so a cell cannot inject markup; KaTeX output is its own.
// ---------------------------------------------------------------------------

/** A block of mathematics, or an inline span, typeset by KaTeX. */
function mdMath(src: string, display: boolean): HTMLElement {
  const e = h(display ? "div" : "span", display ? "mdmath" : "mdimath");
  e.innerHTML = katex.renderToString(src, { throwOnError: false, displayMode: display, strict: false });
  return e;
}
/** Links keep http(s), mailto and relative targets; anything else (javascript:) is dropped. */
function mdUrl(u: string): string {
  return /^\s*(javascript|data|vbscript):/i.test(u) && !/^\s*data:image\//i.test(u) ? "#" : u;
}
const MD_LINK = /^!?\[([^\]]*)\]\(\s*([^)\s]+)(?:\s+"[^"]*")?\s*\)/;

/** Inline Markdown into `host`: code and math first (their text is verbatim), then emphasis, links, images. */
function mdInline(host: HTMLElement, text: string) {
  let buf = "";
  const flush = () => { if (buf) { host.append(document.createTextNode(buf)); buf = ""; } };
  for (let i = 0; i < text.length;) {
    const c = text[i]!, next = text[i + 1];
    if (c === "\\" && next !== undefined && "\\`*_$[]()#!".includes(next)) { buf += next; i += 2; continue; }
    if (c === "`") {
      const j = text.indexOf("`", i + 1);
      if (j > i + 1) { flush(); host.append(h("code", "mdcode", text.slice(i + 1, j))); i = j + 1; continue; }
    }
    if (c === "$") {
      if (next === "$") {
        const j = text.indexOf("$$", i + 2);
        if (j > i + 2) { flush(); host.append(mdMath(text.slice(i + 2, j), true)); i = j + 2; continue; }
      } else if (next !== undefined && !/\s/.test(next)) {
        const j = text.indexOf("$", i + 1);
        if (j > i + 1 && !/\s/.test(text[j - 1]!)) { flush(); host.append(mdMath(text.slice(i + 1, j), false)); i = j + 1; continue; }
      }
    }
    if (c === "!" && next === "[") {
      const m = MD_LINK.exec(text.slice(i));
      if (m) { flush(); const img = document.createElement("img"); img.src = mdUrl(m[2]!); img.alt = m[1]!; img.className = "mdimg"; host.append(img); i += m[0].length; continue; }
    }
    if (c === "[") {
      const m = MD_LINK.exec(text.slice(i));
      if (m) { flush(); const a = document.createElement("a"); a.href = mdUrl(m[2]!); a.target = "_blank"; a.rel = "noopener"; mdInline(a, m[1]!); host.append(a); i += m[0].length; continue; }
    }
    if ((c === "*" || c === "_") && !(c === "_" && i > 0 && /\w/.test(text[i - 1]!))) {
      const mark = next === c ? c + c : c;
      const j = text.indexOf(mark, i + mark.length);
      const inner = text[i + mark.length];
      if (j > i + mark.length && inner !== undefined && !/\s/.test(inner) && !/\s/.test(text[j - 1]!)) {
        flush(); const e = h(mark.length === 2 ? "strong" : "em"); mdInline(e, text.slice(i + mark.length, j)); host.append(e); i = j + mark.length; continue;
      }
    }
    if (c === "\n") { if (buf.endsWith("  ")) { buf = buf.trimEnd(); flush(); host.append(h("br")); } else buf += " "; i++; continue; }
    buf += c; i++;
  }
  flush();
}

/** Block-level Markdown: the cell's rendering. */
function mdRender(src: string): HTMLElement {
  const out = h("div", "mdout");
  const lines = src.replace(/\r\n?/g, "\n").split("\n");
  const para: string[] = [];
  const flush = () => {
    if (!para.length) return;
    const text = para.join("\n"); para.length = 0;
    const fig = /^!\[([^\]]*)\]\(\s*([^)\s]+)(?:\s+"[^"]*")?\s*\)$/.exec(text.trim());
    if (fig) {   // a paragraph that is one image: a figure, its alt text the caption
      const f = h("figure"); const img = document.createElement("img"); img.src = mdUrl(fig[2]!); img.alt = fig[1]!; f.append(img);
      if (fig[1]) { const cap = h("figcaption"); mdInline(cap, fig[1]); f.append(cap); }
      out.append(f); return;
    }
    const p = h("p"); mdInline(p, text); out.append(p);
  };
  for (let i = 0; i < lines.length;) {
    const line = lines[i]!;
    const fence = /^\s*```\s*([\w+-]*)\s*$/.exec(line);
    if (fence) {
      flush(); const buf: string[] = []; i++;
      while (i < lines.length && !/^\s*```\s*$/.test(lines[i]!)) buf.push(lines[i++]!);
      i++;
      const pre = h("pre", "mdpre"); pre.append(h("code", fence[1] ? `lang-${fence[1]}` : undefined, buf.join("\n"))); out.append(pre); continue;
    }
    if (/^\s*\$\$/.test(line)) {   // display math on its own lines; the closing $$ may carry a trailing label
      flush();
      let body = line.replace(/^\s*\$\$/, ""); let closed = false;
      const end = body.indexOf("$$");
      if (end >= 0) { body = body.slice(0, end); closed = true; }
      i++;
      while (!closed && i < lines.length) {
        const l = lines[i++]!, k = l.indexOf("$$");
        if (k >= 0) { body += `\n${l.slice(0, k)}`; closed = true; } else body += `\n${l}`;
      }
      out.append(mdMath(body.trim(), true)); continue;
    }
    if (!line.trim()) { flush(); i++; continue; }
    const hd = /^(#{1,6})\s+(.*?)\s*#*\s*$/.exec(line);
    if (hd) { flush(); const e = h(`h${hd[1]!.length}`); mdInline(e, hd[2]!); out.append(e); i++; continue; }
    if (/^\s*([-*_])(\s*\1){2,}\s*$/.test(line)) { flush(); out.append(h("hr")); i++; continue; }
    if (/^\s*>/.test(line)) {
      flush(); const buf: string[] = [];
      while (i < lines.length && /^\s*>/.test(lines[i]!)) buf.push(lines[i++]!.replace(/^\s*>\s?/, ""));
      const q = h("blockquote"); q.append(...Array.from(mdRender(buf.join("\n")).childNodes)); out.append(q); continue;
    }
    const li = /^\s*(?:[-*+]|\d+[.)])\s+/.exec(line);
    if (li) {
      flush(); const ordered = /^\s*\d/.test(line);
      const list = h(ordered ? "ol" : "ul");
      while (i < lines.length) {
        const m = /^\s*(?:[-*+]|\d+[.)])\s+(.*)$/.exec(lines[i]!); if (!m) break;
        let item = m[1]!; i++;
        while (i < lines.length && /^\s{2,}\S/.test(lines[i]!) && !/^\s*(?:[-*+]|\d+[.)])\s+/.test(lines[i]!)) item += `\n${lines[i++]!.trim()}`;   // a wrapped item
        const e = h("li"); mdInline(e, item); list.append(e);
      }
      out.append(list); continue;
    }
    para.push(line); i++;
  }
  flush();
  return out;
}

/** The ⋮ menu of a cell: send to a scene (any scene, or a new one), duplicate, delete, move, copy. */
function toggleCellMenu(cell: Cell, anchor: HTMLElement) {
  const open = document.querySelector(".cellmenu");
  const wasThis = open?.getAttribute("data-cell") === cell.id;
  closeCellMenu();
  if (wasThis) return;
  const i = S.cells.indexOf(cell);
  const menu = h("div", "cellmenu"); menu.setAttribute("data-cell", cell.id);
  const item = (label: string, act: (() => void) | null, opts: { danger?: boolean; sub?: HTMLElement } = {}) => {
    const it = h("div", `item${act || opts.sub ? "" : " off"}${opts.danger ? " danger" : ""}`);
    it.append(document.createTextNode(label));
    if (opts.sub) { it.append(h("span", "arrow", "▸")); it.append(opts.sub); it.classList.add("hassub"); }
    else if (act) it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); act(); });
    else it.addEventListener("click", (ev) => ev.stopPropagation());
    menu.append(it);
    return it;
  };
  const copy = (text: string | undefined, what: string) => () => {
    if (text === undefined) return;
    void navigator.clipboard?.writeText(text).then(() => log("ok", `copied ${what}`), () => log("err", "the clipboard is not available"));
  };
  // Send to scene ▸ — every scene, then a new one
  const canSend = !!(cell.outLatex && cell.echoLatex);
  if (canSend) {
    const sub = h("div", "submenu");
    ST.scenes.forEach((sc, k) => {
      const it = h("div", "item", `${sc.name} · ${sc.shots.length} shots`);
      it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); sendToScene(cell, k); });
      sub.append(it);
    });
    if (ST.scenes.length) sub.append(h("div", "sep"));
    const nw = h("div", "item", "New scene");
    nw.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); sendToScene(cell, "new"); });
    sub.append(nw);
    item("Send to scene", null, { sub });
  } else item("Send to scene", null);
  menu.append(h("div", "sep"));
  // Change to ▸ — the other kinds of cell, the current one ticked
  {
    const sub = h("div", "submenu");
    const cur: CellType = cell.type ?? "math";
    for (const [t, label] of CELL_TYPES) {
      const it = h("div", `item${t === cur ? " off" : ""}`, `${t === cur ? "✓ " : ""}${label}`);
      if (t !== cur) it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); convertCell(cell, t); });
      else it.addEventListener("click", (ev) => ev.stopPropagation());
      sub.append(it);
    }
    item("Change to", null, { sub });
  }
  if (cell.type === "section") {
    item("Run section", () => void runSection(i));
    item(cell.collapsed ? "Unfold section" : "Fold section", () => { cell.collapsed = !cell.collapsed; renderCells(); renderSidebar(); autosave(); });
  } else if (sectionOf(i) >= 0) item("Run this section", () => void runSection(sectionOf(i)));
  menu.append(h("div", "sep"));
  item("Duplicate cell", () => {
    const c = freshCell(cellSrc(cell), cell.type ?? "math");
    S.cells.splice(i + 1, 0, c); renderCells(); renderSidebar(); focusCell(i + 1); autosave();
  });
  item("Move up", i > 0 ? () => { [S.cells[i - 1], S.cells[i]] = [S.cells[i]!, S.cells[i - 1]!]; renderCells(); renderSidebar(); focusCell(i - 1); autosave(); } : null);
  item("Move down", i < S.cells.length - 1 ? () => { [S.cells[i + 1], S.cells[i]] = [S.cells[i]!, S.cells[i + 1]!]; renderCells(); renderSidebar(); focusCell(i + 1); autosave(); } : null);
  menu.append(h("div", "sep"));
  item("Copy input", copy(cellSrc(cell), "the input"));
  item("Copy output", cell.outText !== undefined ? copy(cell.outText, "the output") : null);
  item("Copy output as LaTeX", cell.outLatex ? copy(stripPaths(cell.outLatex), "the output as LaTeX") : null);
  menu.append(h("div", "sep"));
  item("Clear output", cell.outLatex || cell.error ? () => {
    delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.error; delete cell.plot; delete cell.hasse; cell.steps = []; cell.label = null;
    renderCellBody(cell); renderChrome(); renderSidebar(); autosave();
  } : null);
  item("Delete cell", () => {
    if (S.cells.length === 1) { const c = S.cells[0]!; c.src = ""; if (c.input) { c.input.value = ""; syncHighlight(c); } delete c.outLatex; delete c.outText; delete c.echoLatex; delete c.error; c.steps = []; c.label = null; }
    else S.cells.splice(i, 1);
    S.active = Math.min(S.active, S.cells.length - 1);
    renderCells(); renderSidebar(); renderChrome(); autosave();
  }, { danger: true });
  // on the body, fixed: the paper scrolls and clips, and a menu near its bottom must not grow a scrollbar
  document.body.append(menu);
  const r = anchor.getBoundingClientRect(), mh = menu.offsetHeight;
  const below = r.bottom + 4 + mh <= window.innerHeight - 8;
  menu.style.top = `${below ? r.bottom + 4 : Math.max(8, r.top - 4 - mh)}px`;
  menu.style.right = `${window.innerWidth - r.right}px`;
}
function closeCellMenu() { document.querySelectorAll(".cellmenu").forEach((m) => m.remove()); }

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
        switchTab("notebook");
        const c = S.cells[S.cells.length - 1] ?? addCell();
        if (c.input) { c.input.value = e; c.src = e; syncHighlight(c); }
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
  const toggle = h("div", "pbtn", S.panelOpen ? "▾ Collapse" : "▴ Expand");
  toggle.addEventListener("click", () => { S.panelOpen = !S.panelOpen; renderPanelHead(); renderPanel(); });
  head.append(toggle);
}

/** Select a nested step: the panel shows its result, its explanation, its siblings and its status. */
function selectSubStep(cell: Cell, steps: Step[], index: number, label: string, top: number, path: Path = []) {
  const st = steps[index]!;
  const whole = st.afterRendered?.latex ?? "";
  const latex = (path.length ? pathLatex(whole, path) : null) ?? whole;
  S.sel = { cellId: cell.id, term: { kind: "step", index: top }, path, latex, text: st.afterRendered?.text ?? st.rule,
    related: [st], trace: new Map(), sub: { steps, index, label, top, key: `sub:${label}` } };
  S.panelTab = "explain"; S.panelOpen = true;
  markSelection();
  renderPanelHead(); renderPanel();
}

function renderSubPanel(body: HTMLElement, sel: Selection & { sub: NonNullable<Selection["sub"]> }) {
  const cell = S.cells.find((c) => c.id === sel.cellId);
  const { steps, index, label, top } = sel.sub;
  const st = steps[index]!;
  const grid = h("div", "explain");
  const c1 = h("div", "col");
  c1.append(h("h3", undefined, "Selection"));
  const selEl = h("div", "sel"); selEl.innerHTML = tex(stripPaths(sel.latex));
  c1.append(selEl);
  c1.append(h("div", "kindname", `step ${label} · ${st.rule}${sel.path.length ? ` · path ${sel.path.join(".")}` : ""}`));
  const p = h("p"); p.append(inlineMath(st.explanation)); c1.append(p);
  grid.append(c1);
  const c2 = h("div", "col");
  c2.append(h("h3", undefined, `Inside step ${top + 1}`));
  const trail = h("div", "trail");
  steps.forEach((s, i) => {
    const row = h("div", `trailrow${i === index ? " on" : ""}`);
    row.append(h("span", "n", `${label.split(".").slice(0, -1).join(".")}.${i + 1}`), h("span", "rule", s.rule));
    row.style.cursor = "pointer";
    row.addEventListener("click", () => { if (cell) selectSubStep(cell, steps, i, `${label.split(".").slice(0, -1).join(".")}.${i + 1}`, top); });
    trail.append(row);
  });
  c2.append(trail);
  grid.append(c2);
  const c3 = h("div", "col");
  const cx = cellComplex(cell);
  const status = statusOf(st, cx);
  const head3 = h("div"); head3.style.cssText = "display:flex; align-items:center; gap:8px; margin-bottom:10px";
  head3.append(h("h3", undefined, cx ? "Proof status over ℂ" : "Proof status"), h("span", `checkbadge ${status}`, status));
  (head3.firstElementChild as HTMLElement).style.margin = "0";
  c3.append(head3);
  const rs = h("div", "rulestat");
  rs.append(h("span", `vmark ${status}`), h("span", "n", st.rule), h("span", "note", ruleStatusIn(st.rule, cx).note));
  c3.append(rs);
  grid.append(c3);
  body.append(grid);
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

  if (S.sel.sub) { renderSubPanel(body, S.sel as Selection & { sub: NonNullable<Selection["sub"]> }); return; }
  const grid = h("div", "explain");
  const sel = S.sel;
  const cell = S.cells.find((c) => c.id === sel.cellId);
  const steps = cell?.steps ?? [];
  const where = sel.term.kind === "step" ? `after step ${sel.term.index + 1}` : sel.term.kind === "input" ? "in the input" : "in the output";

  // Selection: the subterm, what it is, and the reference entry for its head function if any
  const c1 = h("div", "col");
  c1.append(h("h3", undefined, "Selection"));
  const selEl = h("div", "sel"); selEl.innerHTML = tex(sel.latex);
  c1.append(selEl);
  const head = /^([A-Za-z_][A-Za-z0-9_]*)\s*\(/.exec(sel.text)?.[1];
  const doc = head ? DOC_BY_NAME.get(head) : undefined;
  c1.append(h("div", "kindname", doc ? `${doc.sig}` : `${cellKind(cell?.src ?? "") ?? "term"} · path ${sel.path.join(".") || "root"}`));
  c1.append(h("p", undefined, doc
    ? `${doc.blurb} This occurrence is ${where}; the engine located it by the path recorded when the term was printed.`
    : `Rendered as ${sel.text}, ${where}. The engine located this subterm by the path recorded when the term was printed, so the selection and the derivation refer to the same node.`));
  if (doc?.ref) {
    const a = document.createElement("a");
    a.href = doc.ref; a.target = "_blank"; a.rel = "noreferrer"; a.textContent = "Definition and identities ↗";
    a.style.cssText = "display:inline-block; margin-top:10px; font-size:11.5px";
    c1.append(a);
  }
  grid.append(c1);

  // Trail: every step up to the selected term; the ones the tracer says produced the selection are
  // marked by how (created / copied / contains), and the note is the last creating step's reason
  const c2 = h("div", "col");
  c2.append(h("h3", undefined, "Derivation trail"));
  const upto = sel.term.kind === "step" ? sel.term.index + 1 : sel.term.kind === "input" ? 0 : steps.length;
  const trailSteps = steps.slice(0, upto);
  const relOf = (i: number) => sel.trace.get(i) ?? (sel.related.some((r) => sameStep(r, steps[i]!)) ? "copied" : null);
  if (trailSteps.length) {
    const trail = h("div", "trail");
    trailSteps.forEach((st, i) => {
      const rel = relOf(i);
      const row = h("div", `trailrow${rel === "created" ? " on" : rel ? " weak" : ""}`);
      row.append(h("span", "no", String(i + 1)), h("span", "rule", st.rule));
      if (rel) row.append(h("span", "rel", rel));
      row.title = rel === "created" ? "This rule built the selected node." : rel === "copied" ? "This rule moved or copied the selected node." : rel === "contains" ? "This rule fired inside the selected node." : "This rule did not touch the selection.";
      row.addEventListener("click", () => { if (cell) void explain(cell, { kind: "step", index: i }, []); });
      row.style.cursor = "pointer";
      trail.append(row);
    });
    c2.append(trail);
    const createdAt = [...trailSteps.keys()].filter((i) => relOf(i) === "created").pop();
    const focus = sel.term.kind === "step" && sel.path.length === 0 ? steps[sel.term.index]
      : createdAt !== undefined ? steps[createdAt] : [...sel.related].pop();
    const p = h("p");
    if (focus) p.append(inlineMath(focus.explanation));
    else p.textContent = "No rule fired at or below this subterm: it came through unchanged.";
    c2.append(p);
  } else {
    c2.append(h("p", undefined, sel.term.kind === "input"
      ? "This is the input as the engine parsed it; no rule has fired yet."
      : "No rule fired at or below this subterm: it came through unchanged from the input."));
  }
  grid.append(c2);

  // Proof status of the rules that touched the selection
  const c3 = h("div", "col");
  const cx = cellComplex(cell);
  const used = [...new Set(sel.related.map((s) => s.rule))];
  const stats = sel.related.map((s) => statusOf(s, cx));
  const overall = stats.length === 0 ? "verified" : stats.includes("unverified") ? "unverified" : stats.includes("conditional") ? "conditional" : stats.includes("checked") ? "checked" : "verified";
  const head3 = h("div"); head3.style.cssText = "display:flex; align-items:center; gap:8px; margin-bottom:10px";
  head3.append(h("h3", undefined, cx ? "Proof status over ℂ" : "Proof status"), h("span", `checkbadge ${overall}`, overall));
  (head3.firstElementChild as HTMLElement).style.margin = "0";
  c3.append(head3);
  if (used.length === 0) {
    c3.append(h("p", undefined, "Nothing to check: no rewrite produced this subterm."));
  } else {
    for (const r of used) {
      const st = ruleStatusIn(r, cx);
      const row = h("div", "rulestat");
      row.append(h("span", `vmark ${st.status}`), h("span", "n", r), h("span", "note", st.note));
      c3.append(row);
    }
  }
  grid.append(c3);
  body.append(grid);
}

// ---------------------------------------------------------------------------
// Manim Studio: glyph-level TeX morphing
// ---------------------------------------------------------------------------
// Renders TeX offscreen with KaTeX, measures every glyph box, matches glyphs between two
// expressions by longest common subsequence, and interpolates position and opacity — the
// browser-side approximation of Manim's TransformMatchingTex. Ported from the design's
// glyphmorph.js; the only difference is that it emits DOM nodes rather than React elements.

interface Glyph { ch: string; rule?: boolean; x: number; y: number; w: number; h: number; font?: string; size?: string; style?: string; weight?: string }
interface Measured { glyphs: Glyph[]; w: number; h: number }

const measureCache = new Map<string, Measured>();
let morphHost: HTMLElement | null = null;

function ensureHost(): HTMLElement {
  if (morphHost?.isConnected) return morphHost;
  morphHost = document.createElement("div");
  morphHost.style.cssText = "position:fixed; left:-99999px; top:0; visibility:hidden; pointer-events:none; z-index:-1";
  document.body.appendChild(morphHost);
  return morphHost;
}

function measure(texSrc: string, fontSize: number): Measured {
  const key = `${fontSize}|${texSrc}`;
  const hit = measureCache.get(key);
  if (hit) return hit;
  const empty: Measured = { glyphs: [], w: 0, h: 0 };
  if (!texSrc) return empty;
  const host = ensureHost();
  host.innerHTML = "";
  const el = document.createElement("div");
  el.style.cssText = `font-size:${fontSize}px; display:inline-block; white-space:nowrap`;
  host.appendChild(el);
  try { katex.render(texSrc, el, { throwOnError: false, displayMode: false, strict: false, trust: true }); } catch { return empty; }
  const root = el.querySelector(".katex-html") as HTMLElement | null;
  if (!root) return empty;
  el.querySelector(".katex-mathml")?.remove();
  const base = root.getBoundingClientRect();
  const glyphs: Glyph[] = [];
  const range = document.createRange();
  const walk = (node: Node) => {
    for (const child of Array.from(node.childNodes)) {
      if (child.nodeType === 3) {
        const txt = child.textContent ?? "";
        if (!txt.trim()) continue;
        const cs = getComputedStyle(child.parentElement!);
        for (let i = 0; i < txt.length; i++) {
          if (!txt[i]!.trim()) continue;
          range.setStart(child, i); range.setEnd(child, i + 1);
          const r = range.getBoundingClientRect();
          if (r.width < 0.05 && r.height < 0.05) continue;
          glyphs.push({ ch: txt[i]!, x: r.left - base.left, y: r.top - base.top, w: r.width, h: r.height,
            font: cs.fontFamily, size: cs.fontSize, style: cs.fontStyle, weight: cs.fontWeight });
        }
      } else if (child.nodeType === 1) {
        const elc = child as HTMLElement;
        const cs = getComputedStyle(elc);
        const bw = parseFloat(cs.borderBottomWidth) || 0;
        if (bw > 0 && elc.clientWidth > 0) {
          const r = elc.getBoundingClientRect();
          glyphs.push({ ch: "─", rule: true, x: r.left - base.left, y: r.bottom - base.top - bw, w: r.width, h: Math.max(1, bw) });
        }
        walk(child);
      }
    }
  };
  walk(root);
  const out = { glyphs, w: base.width, h: base.height };
  measureCache.set(key, out);
  return out;
}

function lcsPairs(A: Glyph[], B: Glyph[]) {
  const n = A.length, m = B.length;
  const pairs: [number, number][] = [], usedA = new Set<number>(), usedB = new Set<number>();
  if (!n || !m) return { pairs, usedA, usedB };
  const dp: Int32Array[] = Array.from({ length: n + 1 }, () => new Int32Array(m + 1));
  for (let i = n - 1; i >= 0; i--)
    for (let j = m - 1; j >= 0; j--)
      dp[i]![j] = A[i]!.ch === B[j]!.ch ? dp[i + 1]![j + 1]! + 1 : Math.max(dp[i + 1]![j]!, dp[i]![j + 1]!);
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (A[i]!.ch === B[j]!.ch) { pairs.push([i, j]); usedA.add(i); usedB.add(j); i++; j++; }
    else if (dp[i + 1]![j]! >= dp[i]![j + 1]!) i++;
    else j++;
  }
  return { pairs, usedA, usedB };
}

const clamp01 = (x: number) => x < 0 ? 0 : x > 1 ? 1 : x;
const easeIO = (p: number) => p < 0.5 ? 2 * p * p : 1 - Math.pow(-2 * p + 2, 2) / 2;

function glyphEl(g: Glyph): HTMLElement {
  if (g.rule) {
    const d = document.createElement("div");
    d.style.cssText = `position:absolute; left:0; top:0; width:${g.w}px; height:${Math.max(1, g.h)}px; will-change:transform,opacity`;
    return d;
  }
  const s = document.createElement("span");
  s.style.cssText = `position:absolute; left:0; top:0; white-space:pre; line-height:normal; will-change:transform,opacity; font-family:${g.font ?? ""}; font-size:${g.size ?? ""}; font-style:${g.style ?? ""}; font-weight:${g.weight ?? ""}`;
  s.textContent = g.ch;
  return s;
}

/**
 * One transition, prevTex → curTex, with its glyph nodes built once. `at(p)` moves them: only
 * transform and opacity change per frame, so the browser composites rather than relaying out —
 * rebuilding the nodes every frame (what a naive port does) is what makes a morph stutter.
 */
class Morph {
  readonly el: HTMLElement;
  readonly gone: string;
  readonly added: string;
  private readonly A: Measured;
  private readonly B: Measured;
  private readonly pairs: { el: HTMLElement; a: Glyph; b: Glyph }[] = [];
  private readonly goneEls: { el: HTMLElement; g: Glyph }[] = [];
  private readonly addedEls: { el: HTMLElement; g: Glyph }[] = [];
  private readonly writeEls: { el: HTMLElement; g: Glyph }[] = [];

  private readonly H: number;

  constructor(prevTex: string | null, curTex: string, fontSize: number, height?: number) {
    this.B = measure(curTex, fontSize);
    this.A = prevTex ? measure(prevTex, fontSize) : { glyphs: [], w: 0, h: 0 };
    this.H = height ?? Math.max(this.A.h, this.B.h);
    this.el = document.createElement("div");
    this.el.style.cssText = `position:relative; height:${this.H}px; margin:0 auto`;
    if (!this.A.glyphs.length) {
      for (const g of this.B.glyphs) { const e = glyphEl(g); this.writeEls.push({ el: e, g }); this.el.append(e); }
      this.gone = ""; this.added = "";
      return;
    }
    const { pairs, usedA, usedB } = lcsPairs(this.A.glyphs, this.B.glyphs);
    for (const [ai, bi] of pairs) { const b = this.B.glyphs[bi]!; const e = glyphEl(b); this.pairs.push({ el: e, a: this.A.glyphs[ai]!, b }); this.el.append(e); }
    const goneChars: string[] = [], addedChars: string[] = [];
    this.A.glyphs.forEach((g, i) => { if (usedA.has(i)) return; if (!g.rule) goneChars.push(g.ch); const e = glyphEl(g); this.goneEls.push({ el: e, g }); this.el.append(e); });
    this.B.glyphs.forEach((g, i) => { if (usedB.has(i)) return; if (!g.rule) addedChars.push(g.ch); const e = glyphEl(g); this.addedEls.push({ el: e, g }); this.el.append(e); });
    this.gone = goneChars.join(""); this.added = addedChars.join("");
  }

  get width() { return this.B.w; }

  /** Place every glyph for progress `p` (0..1). */
  at(p: number) {
    const ink = "var(--ink)", gone = "var(--danger-2)", added = "var(--ok)";
    const put = (el: HTMLElement, g: Glyph, x: number, y: number, o: number, color: string, scale = 1) => {
      el.style.transform = `translate(${x.toFixed(2)}px, ${y.toFixed(2)}px)${scale !== 1 ? ` scale(${scale.toFixed(3)})` : ""}`;
      el.style.opacity = o.toFixed(3);
      if (g.rule) el.style.background = color; else el.style.color = color;
    };
    const q = clamp01(p);
    // every expression is centred vertically in the scene's common height, so a shot boundary
    // (where one morph hands over to the next) moves nothing
    const oyB = (this.H - this.B.h) / 2, oyA = (this.H - this.A.h) / 2;
    if (this.writeEls.length) {
      this.el.style.width = `${this.B.w}px`;
      const n = this.writeEls.length, span = Math.max(1, n * 0.55);
      this.writeEls.forEach(({ el, g }, i) => put(el, g, g.x, g.y + oyB, clamp01((q * (n + span) - i) / span), ink));
      return;
    }
    const e = easeIO(q);
    const W = this.A.w + (this.B.w - this.A.w) * e;
    this.el.style.width = `${W}px`;
    const offA = (W - this.A.w) / 2, offB = (W - this.B.w) / 2;
    for (const { el, a, b } of this.pairs) {
      put(el, b, (a.x + offA) + ((b.x + offB) - (a.x + offA)) * e, (a.y + oyA) + ((b.y + oyB) - (a.y + oyA)) * e, 1, ink);
      if (b.rule) el.style.width = `${a.w + (b.w - a.w) * e}px`;
    }
    for (const { el, g } of this.goneEls) put(el, g, g.x + offA, g.y + oyA, clamp01(1 - q * 1.9), gone, 1 - 0.25 * clamp01(q * 1.9));
    for (const { el, g } of this.addedEls) { const o = clamp01((q - 0.38) / 0.5); put(el, g, g.x + offB, g.y + oyB, o, o > 0.94 ? ink : added); }
  }
}

const STAGE_FONT = 34;

/**
 * Everything a scene's playback needs, built before the first frame: every term measured, one
 * height for the whole scene, and one Morph per shot (from the shot before it, or written on).
 * Doing this lazily at each shot boundary is what makes playback hitch there.
 */
interface Prepared { key: string; morphs: Map<number, Morph>; H: number; maxW: number }
let prepared: Prepared | null = null;
function prepare(on: Live[]): Prepared {
  const key = on.map((s) => `${s.id}:${s.anim}:${s.tex}`).join("|");
  if (prepared?.key === key) return prepared;
  const sizes = on.map((s) => measure(s.tex, STAGE_FONT));
  const H = Math.max(1, ...sizes.map((m) => m.h));
  const maxW = Math.max(1, ...sizes.map((m) => m.w));
  const morphs = new Map<number, Morph>();
  on.forEach((s, i) => {
    const writeOn = i === 0 || s.anim === "Write" || s.anim === "Create";
    morphs.set(s.id, new Morph(writeOn ? null : on[i - 1]!.tex, s.tex, STAGE_FONT, H));
  });
  prepared = { key, morphs, H, maxW };
  return prepared;
}
let stageShot: number | null = null;

// ---------------------------------------------------------------------------
// Manim Studio: scenes, shots, playback, code
// ---------------------------------------------------------------------------

const ANIMS = ["TransformMatchingTex", "TransformMatchingShapes", "FadeTransform", "Write", "Create"];

function defaultAnim(rule: string): string {
  const r = rule.toLowerCase();
  if (r.startsWith("la.") || r.startsWith("cmd.")) return "TransformMatchingShapes";
  if (r === "simp.sort" || r === "simp.flatten") return "FadeTransform";
  return "TransformMatchingTex";
}
const pyName = (s: string) => (s.replace(/[^A-Za-z0-9]+/g, " ").trim().split(" ").map((w) => w.charAt(0).toUpperCase() + w.slice(1)).join("").slice(0, 30)) || "LemmaScene";
const fmtT = (x: number) => `${x.toFixed(1)}s`;
const ST = S.studio;

function activeScene(): Scene | null { return ST.scenes[ST.active] ?? null; }

function newScene() {
  const n = ST.scenes.length + 1;
  ST.scenes.push({ id: Date.now(), name: `Scene ${n}`, shots: [] });
  ST.active = ST.scenes.length - 1; ST.t = 0; stopPlayback();
  renderStudio();
}

function deleteScene(idx: number) {
  stopPlayback();
  ST.scenes.splice(idx, 1);
  ST.active = Math.max(0, Math.min(ST.active > idx ? ST.active - 1 : ST.active, ST.scenes.length - 1));
  ST.t = 0;
  renderStudio();
}

/** Remove the `\htmlData{path=…}{…}` wrappers the engine adds for selection, leaving plain TeX. */
function stripPaths(src: string): string {
  let out = "", i = 0, depth = 0;
  const wrapped: number[] = [];
  while (i < src.length) {
    if (src.startsWith("\\htmlData{", i)) {
      const j = src.indexOf("}{", i);
      if (j < 0) break;
      i = j + 2; depth++; wrapped.push(depth); continue;
    }
    const c = src[i]!;
    if (c === "{") { depth++; out += c; }
    else if (c === "}") { if (wrapped.length && wrapped[wrapped.length - 1] === depth) { wrapped.pop(); depth--; } else { depth--; out += c; } }
    else out += c;
    i++;
  }
  return out;
}

/** Turn a cell's derivation into shots: the statement, then every step's result. */
function sendToScene(cell: Cell, target?: number | "new") {
  if (!cell.outLatex || !cell.echoLatex) return;
  if (target === "new") { ST.scenes.push({ id: Date.now(), name: `Scene ${ST.scenes.length + 1}`, shots: [] }); ST.active = ST.scenes.length - 1; }
  else if (typeof target === "number" && ST.scenes[target]) ST.active = target;
  const mk = (label: string, texSrc: string, anim: string, dur: number, note: string): Shot =>
    ({ id: ++shotSeq, label, tex: stripPaths(texSrc), anim, dur, note, on: true, cell: cell.label });
  const shots: Shot[] = [mk("Statement", cell.echoLatex, "Write", 1.2, "Write the problem exactly as the engine parsed it.")];
  for (const st of cell.steps ?? []) {
    if (!st.afterRendered) continue;
    shots.push(mk(st.rule, st.afterRendered.latex, defaultAnim(st.rule), 1.4, st.explanation));
  }
  if (cell.plot) {
    const k = cell.plot.series.length;
    const epi = !!cell.plot.terms?.length;
    const g = epi
      ? mk("Epicycles", cell.outLatex, "Create", 8.0, `${cell.plot.terms!.length} circles tip to tail, each spinning at its frequency; the tip traces the curve over one period.`)
      : mk("Graph", cell.outLatex, "Create", 2.0, `Plot of ${k > 1 ? `${k} functions` : "the function"} over [${cell.plot.from}, ${cell.plot.to}], sampled by the engine.`);
    g.plot = cell.plot;
    shots.push(g);
  }
  if (!ST.scenes.length) ST.scenes.push({ id: Date.now(), name: "Scene 1", shots: [] });
  if (ST.active >= ST.scenes.length) ST.active = ST.scenes.length - 1;
  ST.scenes[ST.active]!.shots.push(...shots);
  ST.t = 0; stopPlayback();
  log("ok", `${shots.length} shots sent to ${ST.scenes[ST.active]!.name}`);
  switchTab("studio");
}

interface Live extends Shot { start: number; end: number }
function timeline(shots: Shot[]): { on: Live[]; total: number } {
  let at = 0;
  const on = shots.filter((s) => s.on).map((s) => { const e = { ...s, start: at, end: at + s.dur }; at += s.dur; return e; });
  return { on, total: at || 0.001 };
}

let raf = 0, last = 0;
function stopPlayback() { if (raf) cancelAnimationFrame(raf); raf = 0; ST.playing = false; }
function tick() {
  if (!ST.playing) return;
  const t = performance.now();
  const dt = Math.min(0.1, (t - (last || t)) / 1000) * ST.speed;
  last = t;
  const sc = activeScene();
  const { total } = timeline(sc ? sc.shots : []);
  ST.t += dt;
  if (ST.t >= total) { ST.t = total; stopPlayback(); renderStage(); renderTransport(); return; }
  renderStage(); renderTransport();
  raf = requestAnimationFrame(tick);
}
function playPause() {
  if (ST.playing) { stopPlayback(); renderTransport(); return; }
  const sc = activeScene();
  const { total } = timeline(sc ? sc.shots : []);
  if (ST.t >= total - 0.01) ST.t = 0;
  last = performance.now(); ST.playing = true;
  renderTransport();
  raf = requestAnimationFrame(tick);
}

/** The Python a Manim user would run for this scene. */
function manimSceneCode(scene: Scene | null): string {
  if (!scene) return "# Create a scene, then send a cell to it.";
  const on = scene.shots.filter((s) => s.on);
  if (!on.length) return '# This scene has no shots yet.\n# Open the notebook and press "→ Scene" on an evaluated cell.';
  const cls = pyName(scene.name);
  const q = (s: string) => s.replace(/"/g, "'");
  const L = ["from manim import *", ...(on.some((s) => s.plot) ? ["import numpy as np"] : []), "", "", `class ${cls}(Scene):`, `    """${q(scene.name)} — storyboard generated by ChalkMath Manim Studio."""`, "", "    def construct(self):"];
  let first = true;
  for (const s of on) {
    L.push(`        # ${q(s.label)}`);
    if (s.plot?.terms?.length) {
      // epicycles: one rotating vector per term, tip to tail, and a traced path
      const pl = s.plot;
      const terms = pl.terms!;
      const reach = terms.reduce((a, c) => a + Math.hypot(c.re, c.im), 0) || 1;
      if (!first) L.push("        self.play(FadeOut(expr), run_time=0.3)");
      L.push(`        terms = [${terms.map((c) => `(${c.k}, ${c.re.toFixed(6)}, ${c.im.toFixed(6)})`).join(", ")}]  # (k, Re c_k, Im c_k)`);
      L.push(`        scale = ${(3.0 / reach).toFixed(6)}`);
      L.push("        t = ValueTracker(0.0)");
      L.push("        def tip_at(u):");
      L.push("            x, y = 0.0, 0.0");
      L.push("            for k, re, im in terms:");
      L.push("                r, ph = np.hypot(re, im), np.arctan2(im, re)");
      L.push("                x += r * np.cos(k * u + ph); y += r * np.sin(k * u + ph)");
      L.push("            return np.array([x * scale, y * scale, 0.0])");
      L.push("        def arms():");
      L.push("            g = VGroup(); x, y = 0.0, 0.0; u = t.get_value()");
      L.push("            for k, re, im in terms:");
      L.push("                r, ph = np.hypot(re, im), np.arctan2(im, re)");
      L.push("                nx, ny = x + r * np.cos(k * u + ph), y + r * np.sin(k * u + ph)");
      L.push("                if k != 0: g.add(Circle(radius=r * scale, stroke_opacity=0.35, stroke_width=1).move_to([x * scale, y * scale, 0]))");
      L.push("                g.add(Line([x * scale, y * scale, 0], [nx * scale, ny * scale, 0], stroke_width=1.5))");
      L.push("                x, y = nx, ny");
      L.push("            return g");
      L.push("        circles = always_redraw(arms)");
      L.push("        trace = TracedPath(lambda: tip_at(t.get_value()), stroke_color=YELLOW, stroke_width=2.5)");
      L.push(`        label = MathTex(r"${s.tex}", font_size=30).to_corner(UR)`);
      L.push("        self.add(circles, trace)");
      L.push(`        self.play(t.animate.set_value(2 * np.pi), FadeIn(label), run_time=${s.dur.toFixed(1)}, rate_func=linear)`);
      L.push("        expr = VGroup(circles, trace, label)");
      first = false;
      L.push("");
      continue;
    }
    if (s.plot) {
      const pl = s.plot;
      const ys = pl.series.flatMap((c) => c.points.map((pt) => pt[1])).filter((y): y is number => y !== null);
      const ymin = ys.length ? Math.min(0, ...ys) : -1, ymax = ys.length ? Math.max(0, ...ys) : 1;
      const colours = ["YELLOW", "BLUE", "GREEN", "RED", "PURPLE", "ORANGE"];
      if (!first) L.push("        self.play(FadeOut(expr), run_time=0.3)");
      L.push(`        axes = Axes(x_range=[${pl.from}, ${pl.to}], y_range=[${ymin.toFixed(2)}, ${ymax.toFixed(2)}], axis_config={"include_numbers": True})`);
      pl.series.forEach((c, i) => L.push(`        graph${i} = axes.plot(lambda ${pl.var}: ${pyExpr(c.text)}, x_range=[${pl.from}, ${pl.to}], color=${colours[i % colours.length]})`));
      L.push(`        graphs = VGroup(${pl.series.map((_, i) => `graph${i}`).join(", ")})`);
      L.push(`        label = MathTex(r"${s.tex}", font_size=36).to_corner(UR)`);
      L.push("        self.play(Create(axes), run_time=0.8)");
      L.push(`        self.play(Create(graphs), FadeIn(label), run_time=${s.dur.toFixed(1)})`);
      L.push("        expr = VGroup(axes, graphs, label)");
      first = false;
      L.push("");
      continue;
    }
    if (first) {
      L.push(`        expr = MathTex(r"${s.tex}", font_size=54)`);
      L.push(`        self.play(Write(expr), run_time=${s.dur.toFixed(1)})`);
      L.push("        self.wait(0.3)");
      first = false;
    } else {
      L.push(`        caption = Text("${q(s.label)}", font_size=24, color=GREY_B).to_edge(DOWN, buff=0.7)`);
      L.push("        self.play(FadeIn(caption, shift=UP * 0.2), run_time=0.3)");
      L.push(`        nxt = MathTex(r"${s.tex}", font_size=54)`);
      if (s.anim === "Write" || s.anim === "Create") {
        L.push("        self.play(FadeOut(expr), run_time=0.2)");
        L.push(`        self.play(${s.anim}(nxt), run_time=${s.dur.toFixed(1)})`);
      } else {
        L.push(`        self.play(${s.anim}(expr, nxt), run_time=${s.dur.toFixed(1)})`);
      }
      L.push("        expr = nxt");
      L.push("        self.play(FadeOut(caption), run_time=0.25)");
    }
    L.push("");
  }
  L.push("        self.wait(1)");
  return L.join("\n");
}

/** Build the studio's structure. Playback only touches the stage, the transport and shot highlights. */
function renderStudio() {
  const host = $(".studio"); host.innerHTML = "";
  const scene = activeScene();
  const shots = scene ? scene.shots : [];
  const { on, total } = timeline(shots);

  const top = h("div", "studio-top");
  const col = h("div", "stagecol");

  const bar = h("div", "scenebar");
  ST.scenes.forEach((sc, i) => {
    const t = h("span", `scenetab${i === ST.active ? " on" : ""}`, sc.name);
    t.addEventListener("click", () => { stopPlayback(); ST.active = i; ST.t = 0; renderStudio(); });
    const x = h("span", "x", "×"); x.title = "Delete scene";
    x.addEventListener("click", (ev) => { ev.stopPropagation(); deleteScene(i); });
    t.append(x);
    bar.append(t);
  });
  const add = h("span", "smallbtn", "+ New scene"); add.title = "New scene";
  add.addEventListener("click", newScene);
  bar.append(add, h("div", "spacer"), h("span", "info", scene ? `${on.length} shots · ${fmtT(total)} · 60 fps` : "No scene yet"));
  col.append(bar);

  const stage = h("div", "stage");
  stage.append(h("div", "grid"), h("div", "label"), h("div", "center"), h("div", "foot"));
  col.append(stage);

  const tr = h("div", "transport");
  const group = h("div", "bgroup");
  const mk = (label: string, title: string, fn: () => void, cls = "") => {
    const b = document.createElement("button"); b.className = cls; b.textContent = label; b.title = title;
    b.addEventListener("click", fn); return b;
  };
  group.append(
    mk("⏮", "Back to start", () => { stopPlayback(); ST.t = 0; renderStage(); renderTransport(); }),
    mk("▶ Play", "Play or pause", playPause, "primary play"),
    mk("⏭", "Next shot", () => {
      let ci = 0;
      for (let k = 0; k < on.length; k++) if (ST.t >= on[k]!.start - 1e-6) ci = k;
      const nx = on[Math.min(on.length - 1, ci + 1)];
      stopPlayback(); ST.t = nx ? nx.start : total; renderStage(); renderTransport();
    }),
  );
  const range = document.createElement("input");
  range.type = "range"; range.min = "0"; range.max = String(total); range.step = "0.01"; range.value = String(Math.min(ST.t, total));
  range.addEventListener("input", () => { stopPlayback(); ST.t = parseFloat(range.value) || 0; renderStage(); renderTransport(); });
  const speeds = h("div", "bgroup");
  for (const x of [0.5, 1, 2]) {
    const b = mk(`${x}×`, "Playback speed", () => { ST.speed = x; renderTransport(); }, `speed${ST.speed === x ? " on" : ""}`);
    b.dataset["speed"] = String(x);
    speeds.append(b);
  }
  tr.append(group, range, h("span", "time"), speeds);
  col.append(tr);
  top.append(col);

  // shots
  const side = h("div", "shots");
  const head = h("div", "shotshead");
  head.append(h("span", undefined, "Shots"), h("div", "spacer"), h("span", "n", shots.length ? `${on.length} of ${shots.length} on` : "empty"));
  side.append(head);
  const list = h("div", "shotlist");
  shots.forEach((s, i) => {
    const row = h("div", `shot${s.on ? "" : " off"}`);
    row.dataset["shot"] = String(s.id);
    const r1 = h("div", "r1");
    const no = h("span", "no", String(i + 1)); no.title = "Jump to this shot";
    no.addEventListener("click", () => { const live = on.find((x) => x.id === s.id); if (live) { stopPlayback(); ST.t = live.start; renderStage(); renderTransport(); } });
    const lbl = document.createElement("input"); lbl.className = "lbl"; lbl.value = s.label;
    lbl.addEventListener("change", () => { s.label = lbl.value; renderCode(); });
    const tog = h("span", `tog${s.on ? " on" : ""}`, s.on ? "◉" : "○"); tog.title = "Include in render";
    tog.addEventListener("click", () => { s.on = !s.on; ST.t = 0; stopPlayback(); renderStudio(); });
    const up = h("span", "mv", "▲"); up.title = "Move up";
    up.addEventListener("click", () => { if (i > 0) { [shots[i - 1], shots[i]] = [shots[i]!, shots[i - 1]!]; renderStudio(); } });
    const dn = h("span", "mv", "▼"); dn.title = "Move down";
    dn.addEventListener("click", () => { if (i < shots.length - 1) { [shots[i + 1], shots[i]] = [shots[i]!, shots[i + 1]!]; renderStudio(); } });
    const del = h("span", "del", "×"); del.title = "Delete shot";
    del.addEventListener("click", () => { shots.splice(i, 1); ST.t = 0; stopPlayback(); renderStudio(); });
    r1.append(no, lbl, tog, up, dn, del);
    const r2 = h("div", "r2");
    const sel = document.createElement("select");
    for (const a of ANIMS) { const o = document.createElement("option"); o.value = a; o.textContent = a; o.selected = s.anim === a; sel.append(o); }
    sel.addEventListener("change", () => { s.anim = sel.value; renderStage(); renderCode(); });
    const dur = document.createElement("input"); dur.type = "number"; dur.min = "0.2"; dur.max = "8"; dur.step = "0.1"; dur.value = String(s.dur);
    dur.addEventListener("change", () => { const d = parseFloat(dur.value); if (isFinite(d) && d > 0) { s.dur = d; renderStudio(); } });
    r2.append(sel, dur, h("span", "s", "s"));
    row.append(r1, r2);
    list.append(row);
  });
  side.append(list);
  top.append(side);
  host.append(top);

  // code
  const code = h("div", "code");
  const ch = h("div", "codehead");
  const title = h("span", "title", ST.codeOpen ? "▾ Manim scene" : "▸ Manim scene");
  title.addEventListener("click", () => { ST.codeOpen = !ST.codeOpen; renderStudio(); });
  const file = h("span", "file", scene ? `${pyName(scene.name).toLowerCase()}.py` : "chalkmath_scene.py");
  const cmd = h("span", "cmd", scene ? `manim -pqh ${pyName(scene.name).toLowerCase()}.py` : "");
  const copy = h("span", "pbtn", ST.copied ? "Copied" : "Copy");
  copy.addEventListener("click", () => {
    void navigator.clipboard?.writeText(manimSceneCode(activeScene()));
    ST.copied = true; copy.textContent = "Copied";
    setTimeout(() => { ST.copied = false; copy.textContent = "Copy"; }, 1400);
  });
  ch.append(title, file, h("div", "spacer"), cmd, copy);
  code.append(ch);
  const pre = document.createElement("pre");
  pre.hidden = !ST.codeOpen;
  code.style.height = ST.codeOpen ? "200px" : "32px";
  code.append(pre);
  host.append(code);

  renderCode(); renderStage(); renderTransport();
}

function renderCode() {
  const pre = $(".studio .code pre"); if (pre) pre.textContent = manimSceneCode(activeScene());
}

function renderTransport() {
  const tr = $(".studio .transport"); if (!tr) return;
  const sc = activeScene();
  const { total } = timeline(sc ? sc.shots : []);
  const t = Math.min(ST.t, total);
  (tr.querySelector("input[type=range]") as HTMLInputElement).value = String(t);
  tr.querySelector(".time")!.textContent = `${fmtT(t)} / ${fmtT(total)}`;
  tr.querySelector(".play")!.textContent = ST.playing ? "❚❚ Pause" : "▶ Play";
  tr.querySelectorAll<HTMLElement>(".speed").forEach((b) => b.classList.toggle("on", parseFloat(b.dataset["speed"]!) === ST.speed));
}

/** The frame at the current time: which shot, how far into it, and the morph from the previous one. */
function renderStage() {
  const stage = $(".studio .stage"); if (!stage) return;
  const sc = activeScene();
  const shots = sc ? sc.shots : [];
  const { on, total } = timeline(shots);
  const center = stage.querySelector(".center") as HTMLElement;
  const foot = stage.querySelector(".foot") as HTMLElement;
  const label = stage.querySelector(".label") as HTMLElement;
  if (!on.length) {
    stageShot = null;
    center.innerHTML = ""; foot.innerHTML = "";
    label.textContent = "1920×1080 · —";
    const empty = h("div", "empty");
    empty.append(h("div", "t", "This scene is empty"));
    const s = h("div", "s");
    s.append(document.createTextNode("Open the notebook and press "), h("code", undefined, "→ Scene"), document.createTextNode(" on any evaluated cell to send its derivation here as shots."));
    empty.append(s);
    center.append(empty);
    $(".studio .shotlist")?.querySelectorAll(".shot.on").forEach((r) => r.classList.remove("on"));
    return;
  }

  const t = Math.min(ST.t, total);
  let cur = on[0]!, ci = 0;
  for (let k = 0; k < on.length; k++) if (t >= on[k]!.start - 1e-6) { cur = on[k]!; ci = k; }
  const p = Math.max(0, Math.min(1, (t - cur.start) / Math.max(0.001, cur.dur)));
  label.textContent = `1920×1080 · shot ${ci + 1} of ${on.length}`;

  if (cur.plot) {
    // a graph shot: the curve draws itself over the shot's duration
    let gbox = center.querySelector(".plotshot") as HTMLElement | null;
    if (!gbox || gbox.dataset.shot !== String(cur.id)) {
      center.innerHTML = "";
      gbox = h("div", "plotshot"); gbox.dataset.shot = String(cur.id); center.append(gbox);
    }
    const avail = Math.max(240, Math.min(720, stage.clientWidth - 52));
    const epi = !!cur.plot.terms?.length;
    gbox.innerHTML = ""; gbox.append(plotSvg(cur.plot, avail, Math.round(avail * (epi || cur.plot.series.some((s) => s.parametric) ? 0.6 : 0.45)), p, epi ? p : undefined));
    if (stageShot !== cur.id || !foot.childElementCount) {
      stageShot = cur.id; foot.innerHTML = "";
      foot.append(h("span", "caption", cur.label));
    }
    $(".studio .shotlist")?.querySelectorAll(".shot").forEach((r, k) => r.classList.toggle("on", k === ci));
    return;
  }
  const prep = prepare(on);
  const morph = prep.morphs.get(cur.id)!;
  let box = center.querySelector(".morph") as HTMLElement | null;
  if (!box || box.firstElementChild !== morph.el) {
    center.innerHTML = "";
    box = h("div", "morph"); box.append(morph.el); center.append(box);
  }
  morph.at(p);
  // one camera for the whole scene: scale so the widest term fits, and never change it mid-scene
  const avail = Math.max(180, stage.clientWidth - 52);
  box.style.transform = `scale(${prep.maxW > avail ? Math.max(0.3, avail / prep.maxW) : 1})`;

  if (stageShot !== cur.id || !foot.childElementCount) {
    stageShot = cur.id;
    foot.innerHTML = "";
    if (ci > 0) foot.append(h("span", "caption", cur.label));
    if (morph.gone) foot.append(h("span", "mark gone", `− ${morph.gone}`));
    if (morph.added) foot.append(h("span", "mark added", `+ ${morph.added}`));
  }
  const capOpacity = String(Math.min(1, p * 3));
  for (const c of Array.from(foot.children)) (c as HTMLElement).style.opacity = capOpacity;

  const done = t >= total - 1e-6;
  $(".studio .shotlist")?.querySelectorAll<HTMLElement>(".shot").forEach((r) => {
    const live = on.find((x) => String(x.id) === r.dataset["shot"]);
    const active = !!live && ((t >= live.start - 1e-6 && t < live.end - 1e-6) || (done && live.end >= total - 1e-6));
    r.classList.toggle("on", active);
  });
}

// ---------------------------------------------------------------------------
// Completions and hover documentation
// ---------------------------------------------------------------------------

function currentWord(input: HTMLInputElement): { word: string; start: number } {
  const caret = input.selectionStart ?? input.value.length;
  const before = input.value.slice(0, caret);
  // a word, or a backslash abbreviation (possibly still empty: a bare `\` lists every symbol)
  const m = /(\\[A-Za-z_]*|[A-Za-z_][A-Za-z0-9_]*)$/.exec(before);
  return { word: m?.[0] ?? "", start: m ? caret - m[0].length : caret };
}

function updateCompletions(cell: Cell) {
  const input = cell.input!;
  const { word } = currentWord(input);
  if (word.length < 1) return hideCompletions();
  let items: CompItem[];
  if (word.startsWith("\\")) {
    const q = word.slice(1).toLowerCase();
    items = SYMBOLS.filter((s) => [s.abbr, ...s.aliases].some((a) => a.startsWith(q))).map((sym) => ({ kind: "sym", sym }));
  } else {
    items = DOCS.filter((d) => d.name.toLowerCase().startsWith(word.toLowerCase()) && d.name !== word).map((doc) => ({ kind: "doc", doc }));
  }
  if (!items.length) return hideCompletions();
  const r = input.getBoundingClientRect();
  S.comp = { cell, items: items.slice(0, 9), index: 0, x: r.left + 8, y: r.bottom + 4 };
  renderCompletions();
}

function hideCompletions() { S.comp = null; renderCompletions(); }

function acceptCompletion() {
  if (!S.comp) return false;
  const { cell, items, index } = S.comp;
  const input = cell.input!;
  const { word, start } = currentWord(input);
  const item = items[index]!;
  const after = input.value.slice(start + word.length);
  // a symbol abbreviation becomes the symbol itself; a function name opens its parenthesis
  const insert = item.kind === "sym" ? item.sym.sym : item.doc.name + (after.startsWith("(") ? "" : "(");
  input.value = input.value.slice(0, start) + insert + after;
  const pos = start + insert.length;
  input.setSelectionRange(pos, pos);
  cell.src = input.value;
  hideCompletions(); syncHighlight(cell); updateSigHelp(cell); renderSidebar();
  return true;
}

function renderCompletions() {
  document.querySelector(".completions")?.remove();
  if (!S.comp) return;
  const box = h("div", "completions");
  box.style.left = `${S.comp.x}px`; box.style.top = `${S.comp.y}px`;
  S.comp.items.forEach((it, i) => {
    const row = h("div", `comprow${i === S.comp!.index ? " on" : ""}${it.kind === "sym" ? " symrow" : ""}`);
    if (it.kind === "sym") {
      const s = it.sym;
      row.append(h("span", "n", `\\${s.abbr}${s.aliases.length ? ` (${s.aliases.map((a) => "\\" + a).join(", ")})` : ""}`), h("span", "h", s.what), h("span", "sym", s.sym));
    } else {
      const d = it.doc;
      row.append(h("span", "n", d.sig), h("span", "h", d.blurb.split(".")[0]!));
    }
    row.addEventListener("mousedown", (e) => { e.preventDefault(); S.comp!.index = i; acceptCompletion(); });
    row.addEventListener("mouseenter", () => { S.comp!.index = i; renderCompletions(); });
    box.append(row);
  });
  box.append(h("div", "compfoot", "Tab or Enter to accept · Esc to dismiss"));
  document.body.append(box);
}

// --- Syntax highlighting: tokens, and the variables a call binds ---------------------------------

/** Names bound in a session by `let` (values and functions), keyed `session:name`. */
const USER_NAMES = new Set<string>();

/** Commands whose argument at `arg` is a variable bound over the call: `diff(f, x)`, `plot(f, x, …)`. */
const BINDERS: Record<string, number> = { diff: 1, integrate: 1, plot: 1, epicycles: 1, sum: 1, subst: 1 };
const BUILTIN_FN = new Set(["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im", "sign", "det", "rref", "transpose", "dot", "norm", "solve"]);
const COMMANDS = new Set(["diff", "integrate", "plot", "epicycles", "dft", "sum", "exptotrig", "expand", "simplify", "N", "subst", "poset", "map", "monotone", "lfp", "gfp", "fixpoints", "hasse", "join", "meet", "sup", "inf", "upper", "lower", "top", "bottom", "maximal", "minimal", "lattice", "le", "divisors", "subsets", "chain"]);
const CONSTANTS = new Set(["pi", "π", "e", "ℯ", "i", "phi", "φ"]);

type Tok = { kind: "id" | "num" | "op" | "ws" | "kw"; text: string; start: number };
function tokenize(src: string): Tok[] {
  const out: Tok[] = [];
  const re = /(\s+)|(\d+(?:\.\d+)?)|([A-Za-z_\u0370-\u03FFℯ][A-Za-z0-9_\u0370-\u03FFℯ']*)|(:=|->|[^\sA-Za-z0-9_])/gu;
  let m: RegExpExecArray | null;
  while ((m = re.exec(src))) {
    if (m[1] !== undefined) out.push({ kind: "ws", text: m[0], start: m.index });
    else if (m[2] !== undefined) out.push({ kind: "num", text: m[0], start: m.index });
    else if (m[3] !== undefined) out.push({ kind: m[0] === "let" ? "kw" : "id", text: m[0], start: m.index });
    else out.push({ kind: "op", text: m[0], start: m.index });
  }
  return out;
}

/** For each identifier token: is it bound at that position? A binder command's variable argument is
 *  bound over the call's parentheses; `let f(x, y) = …` binds its parameters over the line; a
 *  λ-cell's `λx y.` binds over the term that follows. Returns the set of token indices. */
function boundTokens(src: string, toks: Tok[]): Set<number> {
  const bound = new Set<number>();
  const bindOver = (names: Set<string>, from: number, to: number) => {
    toks.forEach((t, k) => { if (t.kind === "id" && t.start >= from && t.start < to && names.has(t.text)) bound.add(k); });
  };
  // `let f(x, y) = body`
  const mlet = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)\s*=/.exec(src);
  if (mlet) bindOver(new Set(mlet[2]!.split(",").map((p) => p.trim()).filter(Boolean)), 0, src.length);
  // binder commands: find `name(`, its matching `)`, and the top-level arguments
  for (let k = 0; k < toks.length; k++) {
    const t = toks[k]!;
    if (t.kind !== "id" || !(t.text in BINDERS)) continue;
    let j = k + 1; while (j < toks.length && toks[j]!.kind === "ws") j++;
    if (toks[j]?.text !== "(") continue;
    const open = toks[j]!.start;
    let depth = 0, close = src.length; const args: [number, number][] = []; let argStart = open + 1;
    for (let p = open; p < src.length; p++) {
      const c = src[p]!;
      if (c === "(" || c === "[" || c === "{") depth++;
      else if (c === ")" || c === "]" || c === "}") { depth--; if (depth === 0) { args.push([argStart, p]); close = p + 1; break; } }
      else if (c === "," && depth === 1) { args.push([argStart, p]); argStart = p + 1; }
    }
    if (close === src.length && depth > 0) args.push([argStart, src.length]);
    const a = args[BINDERS[t.text]!];
    if (!a) continue;
    const name = src.slice(a[0], a[1]).trim();
    if (/^[A-Za-z_\u0370-\u03FF][A-Za-z0-9_\u0370-\u03FF]*$/u.test(name)) bindOver(new Set([name]), open, close);
  }
  // λx y. body — bound to the end of the enclosing parenthesis or the line
  const lam = /[λ\\]\s*((?:[A-Za-z_][A-Za-z0-9_']*\s*)+)\./gu;
  let m: RegExpExecArray | null;
  while ((m = lam.exec(src))) {
    let depth = 0, end = src.length;
    for (let p = m.index + m[0].length; p < src.length; p++) { const c = src[p]!; if (c === "(") depth++; else if (c === ")") { if (depth === 0) { end = p; break; } depth--; } }
    bindOver(new Set(m[1]!.trim().split(/\s+/)), m.index, end);
  }
  return bound;
}

const esc = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

/** The overlay's HTML for a source line. */
function highlightHtml(src: string): string {
  const toks = tokenize(src);
  const bound = boundTokens(src, toks);
  const lambdaCell = /[λ\\]|:=/.test(src);
  let out = "";
  toks.forEach((t, k) => {
    let cls = "";
    if (t.kind === "num") cls = "hnum";
    else if (t.kind === "kw") cls = "hkw";
    else if (t.kind === "op") cls = /^[()\[\]{};,]$/.test(t.text) ? "hpun" : "hop";
    else if (bound.has(k)) cls = "hbound";
    else if (USER_NAMES.has(`${sessionId}:${t.text}`)) cls = "hdef";
    else if (CONSTANTS.has(t.text)) cls = "hconst";
    else if (!lambdaCell && (COMMANDS.has(t.text) || BUILTIN_FN.has(t.text))) {
      // a name is a call only when a parenthesis follows
      let j = k + 1; while (j < toks.length && toks[j]!.kind === "ws") j++;
      cls = toks[j]?.text === "(" ? (COMMANDS.has(t.text) ? "hcmd" : "hfn") : "hvar";
    } else cls = "hvar";
    out += cls ? `<span class="${cls}">${esc(t.text)}</span>` : esc(t.text);
  });
  return out || "&nbsp;";
}

function syncHighlight(cell: Cell) {
  const hl = cell.hl, input = cell.input;
  if (!hl || !input) return;
  if (!S.highlight) { hl.innerHTML = ""; return; }
  const html = highlightHtml(input.value);
  if (hl.dataset["src"] !== input.value) { hl.innerHTML = `<span class="hlin">${html}</span>`; hl.dataset["src"] = input.value; }
  (hl.firstElementChild as HTMLElement | null)?.style.setProperty("transform", `translateX(${-input.scrollLeft}px)`);
}
/** Redraw every overlay (a name became bound, the toggle changed). */
function renderHighlights() { for (const c of S.cells) { if (c.hl) delete c.hl.dataset["src"]; syncHighlight(c); } }

// --- Signature help: the call around the caret, its parameters, the current one in bold ---------

/** Session-defined functions (`let f(x, y) = e`), keyed by session and name, for signature help. */
const USER_FNS = new Map<string, string[]>();

/** The innermost call the caret is inside: its name, where its `(` is, and which argument the caret
 *  is in. Balanced groups before the caret are skipped; an unclosed `[`/`{` or a bare grouping `(` is
 *  part of an argument, so the walk continues outward. */
function callContext(input: HTMLInputElement): { name: string; open: number; arg: number; firstArg: string } | null {
  const s = input.value, caret = input.selectionStart ?? s.length;
  let depth = 0;
  for (let k = caret - 1; k >= 0; k--) {
    const c = s[k]!;
    if (c === ")" || c === "]" || c === "}") { depth++; continue; }
    if (c !== "(" && c !== "[" && c !== "{") continue;
    if (depth > 0) { depth--; continue; }
    if (c !== "(") continue;
    const m = /([A-Za-z_][A-Za-z0-9_]*)\s*$/.exec(s.slice(0, k));
    if (!m) continue;
    let arg = 0, d = 0;
    for (let j = k + 1; j < caret; j++) {
      const cj = s[j]!;
      if (cj === "(" || cj === "[" || cj === "{") d++;
      else if (cj === ")" || cj === "]" || cj === "}") d--;
      else if (cj === "," && d === 0) arg++;
    }
    return { name: m[1]!, open: k, arg, firstArg: s.slice(k + 1, caret).trim() };
  }
  return null;
}

/** The signature to show for a call: a session function first, else the reference entry whose
 *  signature lists `name(`; `plot` picks its list form when the first argument starts with `[`. */
function sigFor(name: string, firstArg: string): { sig: string; blurb: string } | null {
  const user = USER_FNS.get(`${sessionId}:${name}`);
  if (user) return { sig: `${name}(${user.join(", ")})`, blurb: "Defined in this session with let." };
  for (const d of DOCS) {
    const alts = d.sig.split(" · ").map((a) => a.trim()).filter((a) => a.startsWith(name + "("));
    if (!alts.length) continue;
    const alt = (alts.length > 1 && firstArg.startsWith("[") ? alts.find((a) => a.startsWith(name + "([")) : undefined) ?? alts[0]!;
    return { sig: alt, blurb: d.blurb.split(".")[0]! + "." };
  }
  return null;
}

type SigPiece = { text: string; param: boolean };
/** `diff(f, x[, n])` as pieces: the name and punctuation as text, each parameter on its own, so the
 *  current one can be set in bold. `[, n]` marks an optional parameter; a `[f, g, …]` list is one. */
function sigPieces(sig: string): SigPiece[] {
  const open = sig.indexOf("("), close = sig.lastIndexOf(")");
  if (open < 0 || close < open) return [{ text: sig, param: false }];
  const out: SigPiece[] = [{ text: sig.slice(0, open + 1), param: false }];
  const inside = sig.slice(open + 1, close);
  let buf = "", d = 0, opt = false;
  const flush = () => { if (buf) { out.push({ text: buf, param: true }); buf = ""; } };
  for (let k = 0; k < inside.length; k++) {
    const c = inside[k]!;
    if (d === 0 && c === "[" && inside[k + 1] === ",") { flush(); opt = true; out.push({ text: "[", param: false }); }
    else if (d === 0 && opt && c === "]") { flush(); opt = false; out.push({ text: "]", param: false }); }
    else if (d === 0 && c === ",") { flush(); let sep = ","; while (inside[k + 1] === " ") { sep += " "; k++; } out.push({ text: sep, param: false }); }
    else { if (c === "(" || c === "{" || c === "[") d++; else if (c === ")" || c === "}" || c === "]") d--; buf += c; }
  }
  flush();
  out.push({ text: sig.slice(close), param: false });
  return out;
}

function updateSigHelp(cell: Cell) {
  const input = cell.input;
  if (!S.sigHelp || !input || document.activeElement !== input) return hideSigHelp();
  const ctx = callContext(input);
  const found = ctx && sigFor(ctx.name, ctx.firstArg);
  if (!ctx || !found) { S.sigDismissed = null; return hideSigHelp(); }
  const key = `${cell.id}:${ctx.open}`;
  if (S.sigDismissed === key) return hideSigHelp();
  S.sigDismissed = null;
  S.sig = { cell, key, sig: found.sig, blurb: found.blurb, arg: ctx.arg };
  renderSigHelp();
}
function hideSigHelp() { S.sig = null; renderSigHelp(); }
function dismissSigHelp() { if (S.sig) { S.sigDismissed = S.sig.key; hideSigHelp(); } }

function renderSigHelp() {
  document.querySelector(".sighelp")?.remove();
  const g = S.sig;
  if (!g || !g.cell.input) return;
  const box = h("div", "sighelp");
  const line = h("div", "ss");
  const pieces = sigPieces(g.sig), n = pieces.filter((p) => p.param).length;
  let k = 0;
  for (const p of pieces) {
    if (!p.param) { line.append(p.text); continue; }
    const on = k === g.arg || (g.arg >= n && k === n - 1 && p.text.endsWith("…"));
    line.append(on ? h("b", undefined, p.text) : document.createTextNode(p.text));
    k++;
  }
  box.append(line, h("div", "sb", g.blurb));
  const r = g.cell.input.getBoundingClientRect();
  box.style.left = `${r.left + 8}px`;
  // above the input, like an editor; below it only when there is no room and no completion list there
  if (r.top > 80 || S.comp) box.style.bottom = `${window.innerHeight - r.top + 6}px`; else box.style.top = `${r.bottom + 4}px`;
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
  if (ev.key === "Escape" && S.sig) { ev.preventDefault(); return dismissSigHelp(); }
  if (ev.key === " " || ev.key === ".") {
    // Lean-style input: \lam, \pi, \e, \phi … followed by space or dot becomes the symbol
    const input = cell.input!;
    const caret = input.selectionStart ?? input.value.length;
    const before = input.value.slice(0, caret);
    const m = SYMBOL_RE.exec(before);
    if (m) {
      ev.preventDefault();
      const tail = ev.key === "." ? "." : "";
      const sym = symbolFor(m[1]!);
      input.value = before.slice(0, before.length - m[0].length) + sym + tail + input.value.slice(caret);
      const pos = caret - m[0].length + sym.length + tail.length;
      input.setSelectionRange(pos, pos);
      cell.src = input.value; hideCompletions(); syncHighlight(cell); renderSidebar();
      return;
    }
  }
  if (ev.key === "Enter") { ev.preventDefault(); void runCell(cell); return; }
  if (ev.key === "ArrowDown" && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
  if (ev.key === "ArrowUp" && i > 0) { ev.preventDefault(); focusCell(i - 1); }
}

// ---------------------------------------------------------------------------
// Boot
// ---------------------------------------------------------------------------

initTheme();
document.documentElement.dataset["outsize"] = S.outSize;
document.documentElement.classList.toggle("nohl", !S.highlight);
shell();
renderChrome();
renderSidebar();
renderPanelHead();
renderPanel();
renderView();
document.addEventListener("click", () => { if (S.menu) { S.menu = null; renderChrome(); } closeCellMenu(); });
document.querySelector(".cells")?.addEventListener("scroll", () => closeCellMenu(), { passive: true });   // a fixed menu must not float away from its cell
document.addEventListener("keydown", (ev) => {
  if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === "s") { ev.preventDefault(); if (ev.shiftKey) saveNotebookAs(); else saveNotebook(); }
  if (ev.key === "Escape") closeModal();
});
const saved = restoreAutosave();
let restoredActive = 0;
if (saved) {
  // sources and outputs come back at once; each engine session is rebuilt by re-running when its tab is shown
  try {
    const parsed = JSON.parse(saved) as Autosave | ChalkFile;
    const entries: { file: ChalkFile; dirty: boolean }[] = "chalkmath" in parsed && Array.isArray(parsed.docs)
      ? parsed.docs
      : [{ file: parsed as ChalkFile, dirty: false }];
    for (const { file, dirty } of entries) {
      const d = makeDoc(file.name ?? "untitled.chalk", cellsFromFile(file), Array.isArray(file.scenes) ? file.scenes : []);
      if (!d.cells.length) d.cells.push(freshCell());
      d.hydrated = false;
      S.docs.push(d);
      // the saved text is what the tab compares against; a dirty document compares against nothing
      d.text = JSON.stringify({ chalk: 1, name: d.name, cells: file.cells, scenes: d.scenes }, null, 2);
      d.savedText = dirty ? "" : d.text;
    }
    restoredActive = "chalkmath" in parsed && typeof parsed.active === "number" ? parsed.active : 0;
  } catch { /* ignore a corrupt autosave */ }
}
if (!S.docs.length) {
  const d = makeDoc("untitled.chalk", SAMPLES.map((src) => freshCell(src)));
  d.cells.push(freshCell());
  S.docs.push(d);
}
S.doc = -1;
loadDoc(Math.min(restoredActive, S.docs.length - 1));
if (!saved) { const d = currentDoc(); if (d) d.savedText = serializeNotebook(); }
void connect().then(async () => {
  // a link with a notebook in its fragment opens that notebook (in its own tab unless the current one is untouched)
  if (location.hash.startsWith("#nb") && await openNotebookLink(location.hash)) return;
  const d = currentDoc(); if (d && !d.hydrated) hydrate(d);
});
