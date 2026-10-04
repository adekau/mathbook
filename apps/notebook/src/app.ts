import { createClient, type EngineClient, type Step, type StepOutline, type Path, type RuleStatus, type Derivation, type WireExpr, type PlotResult, type ManipulateResult, type HasseData, type KnownVisual, type TruthTableData, type DigraphData, type OpTableData, type ContextTableData, type TypingNode, type TypingTreeData, type SpacetimeData } from "@chalkmath/protocol";
declare const __BUILD_ID__: string;
import { workerTransport, httpTransport } from "@chalkmath/engine-host";
import { leanForPrelude } from "@chalkmath/lean-editor/prelude";
import { read as readNotation, write as writeNotation, writeText, hasNotation, templateAt, templateInText, TEMPLATES, type Stmt, type Caret, type MathEdit } from "@chalkmath/math-editor";
import { MathInput, type MathInputOptions } from "@chalkmath/math-editor/view";

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

import katex from "katex";
import { ASK_CELL, AskError, askSettings, setAskSettings, runLookup, askSource, savedAsk, backendStatus, ollamaModels, openrouterModels, signInOpenRouter, testModel, WEBGPU_MODELS, type AskResult, type AskSettings } from "./ask-cells.js";
import { fileCellOf, resolveFiles, importsIn, partContext, partHelp, fileExprValue, svgPoints, kindOf, tableOf, jsonOf, jsonTable, numericColumns, fileText, fileSize, fmtSize, mimeLabel, mimeFor, dataUrl, fileFromBytes, helpersFor, type FileValue, type FileRef, type FileScope, type Table } from "./files.js";
import { dataGrid, matrixEntries } from "./datagrid.js";
import { plotYRange, framesWindow, blendable, blend, playPosition, workLine } from "./animate.js";
import { DOC_PAGES, type DocPage, type DocPart } from "./docs.js";
import { FUNCTIONS, FN_BY_NAME, AREAS, fnPage, evaluable, type FnDoc, type ExampleSection } from "./reference.js";
import { ensureLean, syncLean, mountLean, unmountLean, focusLean, setLeanDark, infoview as leanInfoview, leanState, leanFailure, leanProgress, leanChecked, initLeanIsolation, type LeanMessage } from "./lean-cells.js";
/** The one trusted KaTeX command is `\htmlData`, which carries the engine's subterm paths. LaTeX can
 *  come from a file someone else wrote (saved outputs render before any re-run), and a blanket
 *  `trust: true` would let it add `\href{javascript:…}`, arbitrary styles, or remote images. */
const TRUST_PATHS = (ctx: { command: string }) => ctx.command === "\\htmlData";
const tex = (s: string, paths = false) =>
  katex.renderToString(s, { throwOnError: false, trust: paths ? TRUST_PATHS : false, strict: false, displayMode: false });

// ---------------------------------------------------------------------------
// Content: the notebook's own vocabulary, from the function reference (reference.ts)
// ---------------------------------------------------------------------------

/** A command as completion, signature help, hover and the Explanation panel show it. */
interface Doc { name: string; sig: string; blurb: string; ref?: string; examples: string[]; notation?: boolean }

/** A usage line as text: its `code` without the backticks. */
const plainUsage = (s: string) => s.replace(/`([^`]*)`/g, "$1");
const DOCS: Doc[] = FUNCTIONS.map((f) => ({
  name: f.name, sig: f.usage.map(([form]) => form).join(" · "),
  blurb: f.usage.map(([form, what]) => `${form} ${plainUsage(what)}`).join(" "),
  examples: f.examples.flatMap((s) => s.items.filter((it): it is string => typeof it === "string")),
  ...(f.ref ? { ref: f.ref } : {}), ...(f.notation ? { notation: true } : {}),
}));
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
/** The same table for the visual input, whose `\\` also inserts templates (`\\frac`, `\\int`, …).
 *  Not λ: a λ-cell is not the grammar the visual input reads, and stays raw. */
const VISUAL_SYMBOLS: Record<string, string> = Object.fromEntries(
  SYMBOLS.filter((s) => s.sym !== "λ").flatMap((s) => [s.abbr, ...s.aliases].map((a) => [a, s.sym])));
type CompItem = { kind: "doc"; doc: Doc }
  /** A name bound in the session: a value, a file, or a function (which opens its call). */
  | { kind: "name"; name: string; what: string; call: boolean } | { kind: "sym"; sym: Sym } | { kind: "tpl"; name: string; what: string; glyph: string }
  /** Inside `x[[…]]`: a column name, an object key or `All`, replacing what was typed from `start`. */
  | { kind: "part"; insert: string; label: string; hint: string; start: number };

/** An order-theory cell, or a `let` binding one: the engine reads these in their own world. */
const ORDER_CELL = /^(let\s+\w+\s*=\s*)?(poset|divisors|subsets|chain|map|hasse|join|meet|sup|inf|upper|lower|lattice|top|bottom|le|maximal|minimal|monotone|lfp|gfp|fixpoints|rel|kernel|reflexive|symmetric|antisymmetric|transitive|equivalence|preorder|closure|classes|finer|wellfounded|measure|op|joinop|meetop|table|associative|commutative|idempotent|semilattice|identity|fold|order|distributive|complement|complemented|boolean|product|galois|closureop|context|concepts|secure|events|clocks|concurrent)\s*\(/;
/** A logic cell: a logic command, or a formula with a connective or a quantifier (the engine's
 *  `Logic.isLogicSource`; a λ-term is not one). */
const LOGIC_CELL = /^(let\s+\w+\s*=\s*)?(truthtable|taut|sat|falsify|equiv|nnf|cnf|dnf)\s*\(/;
/** A systems-world cell: a system, or a question about one. */
const SYSTEM_CELL = /^(let\s+\w+\s*=\s*)?(system|states|invariant|inductive|reach|deadlock|trace|ctl|eventually|refines|replicas|rules|rewrite|terminates|critical)\s*\(/;
/** A λ-command: a strategy, `eta`, `fv`, `db`, `alpha`, `subst`, `type` or `infer`, then a colon (the
 *  engine's `Lam.commandHead`; `type := …` is a definition). It may hold a connective, `type: f : A → B ⊢ f`. */
const LAMBDA_CMD = /^(normal|cbn|cbv|applicative|eta|fv|db|alpha|subst|type|infer)\s*(\d+\s*)?:(?!=)/;
/** The Church library's names (the engine's `Lam.churchDefs`). */
const CHURCH = ["true", "false", "and", "or", "not", "if", "zero", "succ", "add", "mul", "pow", "iszero", "pair", "fst", "snd", "id", "const", "K", "S", "I", "omega", "Y"];
/** Names bound by λ-cells (`pred := …`), keyed `session:name`. */
const LAMBDA_NAMES = new Set<string>();
/** The engine's `Lam.lex` succeeds: identifiers (Greek letters too), numerals, λ or backslash, `.`,
 *  parentheses, `:` and arrows. Each token is taken whole, as the lexer does. */
const LAMBDA_LEXES = /^(?:[ \t\r\n.():λ\\→]|->|[0-9]+(?![0-9])|[A-Za-z_\u0391-\u03A9\u03B1-\u03C9][A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]*(?![A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]))*$/;
/** A λ-cell without a λ (the engine's `Lam.isLambdaSource`): its first word is a λ-definition, the
 *  session's or the Church library's, it has no parenthesis or goes on after a space — `fst (pair a b)` —
 *  and it lexes as a λ-term (`S + 1` is arithmetic). */
function lambdaHeaded(s: string): boolean {
  const w = s.trim().split(" ")[0] ?? "";
  if (w === "let" || !(CHURCH.includes(w) || LAMBDA_NAMES.has(`${sessionId}:${w}`))) return false;
  return (!s.includes("(") || s.includes(" ")) && LAMBDA_LEXES.test(s);
}
const isLogicCell = (s: string) => !/[λ\\]/.test(s) && !LAMBDA_CMD.test(s) && (LOGIC_CELL.test(s) || /[∧∨¬→↔⊤⊥∀∃]|<->|->|&&|\|\|/.test(s) || /^(let\s+\w+\s*=\s*)?(forall|exists)\b/.test(s));

/** Label for a cell, from its source. Presentation only — the engine decides what it means. */
function cellKind(src: string): string | null {
  const s = src.trim();
  if (!s) return null;
  if (ASK_CELL.test(s)) return "lookup";
  if (/^let\s/.test(s)) return "definition";
  if (/⟦|\bimport\(/.test(s) && !/^(epicycles|dft|plot|manipulate)\s*\(/.test(s)) return "file";
  const m = /^([A-Za-z_][A-Za-z0-9_]*)\s*\(/.exec(s);
  const head = m?.[1];
  switch (head) {
    case "diff": return "derivative";
    case "integrate": return "integral";
    case "plot": return "plot";
    case "epicycles": case "dft": return "epicycles";
    case "manipulate": return "manipulate";
    case "sum": return "sum";
    case "exptotrig": return "Euler";
  }
  if (/[λ\\]|:=/.test(s) || LAMBDA_CMD.test(s) || lambdaHeaded(s)) return "λ-term";
  if (SYSTEM_CELL.test(s)) return "system";
  if (ORDER_CELL.test(s)) return "order";
  if (isLogicCell(s)) return "logic";
  switch (head) {
    case "rref": return "row reduce";
    case "det": return "determinant";
    case "transpose": return "transpose";
    case "expand": return "expand";
    case "factor": return "factor";
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
/** `manipulate(e, p, from, to)`: the parameter and the engine's frames — each value of `p` (where it
 *  sits, and as the engine prints it) and the body there, as a term and, for a plot, its samples. */
interface ManipData { param: string; frames: { value: number; label: string; latex: string; parts: ManipPart[] }[] }
/** One part of a frame: a body of one part, or each part of a `column(…)`. Its value, the name it was
 *  written as, and its samples (a plot) or its calculation (each step's term, LaTeX). */
interface ManipPart { latex: string; name?: string; plot?: PlotData; work?: string[] }
/** How many curve colours the stylesheet defines (`svg .curve.c0` … ). */
const CURVE_COLOURS = 6;
/** A `.chalk` file from before lists in `plot` stored one curve as `points` + `text`. */
function migratePlot(p: PlotData | { var: string; from: number; to: number; points: [number, number | null][]; text: string }): PlotData {
  if ("series" in p) return p;
  return { var: p.var, from: p.from, to: p.to, series: [{ latex: "", text: p.text, points: p.points }] };
}

/** What a cell is: mathematics for the engine (the default), Markdown prose with `$…$` and code, or a
 *  section heading that groups the cells below it (run together, collapsible). */
type CellType = "math" | "markdown" | "section" | "lean" | "exercise";
/** What the engine said of an exercise's answer: equivalent or not, with the answer as it reads it
 *  and the normal form it compared; or why it could not compare it. */
interface Verdict { equivalent: boolean; answerLatex?: string; normalLatex?: string; error?: { message: string; span?: { start: number; end: number } } }

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
  /** A `manipulate` cell's frames (not saved: the cell runs again when its notebook opens), and
   *  where its slider is (a frame index; fractional while it plays). */
  manip?: ManipData;
  manipAt?: number;
  /** A file-valued cell (`import("url")`, `⟦name⟧`, or `let x =` one of them): the file it shows,
   *  by what it is. The engine never sees it; the contents are the attachment's or the import's. */
  file?: FileMeta;
  /** The suggestions bar under a file's output was dismissed for this cell. */
  noSuggest?: boolean;
  /** λ-cells: the result with de Bruijn indices, and what it reads as (a Church numeral or boolean). */
  outDeBruijn?: string | undefined;
  reading?: string | undefined;
  /** What the engine said the cell was, once it has answered; the badge guesses from the source until then. */
  kind?: string;
  /** Order-world cells: the Hasse diagram to draw, and the one-line summary. */
  hasse?: { nodes: { name: string; height: number }[]; covers: [string, string][] } | undefined;
  summary?: string | undefined;
  /** What the engine sent to draw beside the value: a truth table, a relation's graph. */
  visuals?: KnownVisual[] | undefined;
  label: number | null;
  ms?: number | undefined;
  outLatex?: string;
  /** The output in the engine's input syntax (the "input form"). */
  outText?: string;
  /** How the output is displayed: matrix | pmatrix | grid | table | input, or standard. */
  form?: string;
  /** "complex" when the cell mentions `i`: its steps are judged by the rules' statuses over ℂ. */
  semantics?: "real" | "complex";
  echoLatex?: string | undefined;
  /** The work: the evaluation's steps with their terms, once fetched (`loadWork`) or as a file saved them. */
  steps?: Step[];
  /** The work as the evaluation sent it: the steps without their terms (`engine.steps` sends those
   *  when the work is opened). A derivation of a big term weighs what its terms weigh, so a cell's
   *  evaluation does not pay for work nobody opens. */
  outline?: StepOutline[] | undefined;
  /** `la.entrywise` steps whose nested entries are open, by step label (not saved). */
  openEntries?: Set<string>;
  error?: { message: string; span?: { start: number; end: number } };
  showWork: boolean;
  /** Step through the work: the reader reveals the steps one at a time and the output waits for the
   *  last. The number is how many steps show at first (the author's choice, saved); absent shows the
   *  work at once. */
  stepwise?: number;
  /** Exercise cells (`src` is the question, whose value is the answer and whose work is the
   *  solution): the prompt (Markdown), the hints in order, whether the question is shown typeset, and
   *  the reader's state — the answer typed, the hints open, the verdict, the solution shown. */
  prompt?: string;
  hints?: string[];
  hideQuestion?: boolean;
  attempt?: string;
  hintsShown?: number;
  verdict?: Verdict;
  solution?: boolean;
  /** How many steps the reader has revealed (not saved), and the source that count belongs to: the
   *  cell run with another source starts again from `stepwise`. */
  revealed?: number;
  revealedFor?: string;
  /** A `let name = number` cell shown as a slider: its range. Moving it rebinds the name and runs the
   *  cells that read it (saved). */
  slider?: { min: number; max: number; step: number };
  /** The notebook's names this cell read when it last ran, each with the version of its value then
   *  (`BIND_VER`); a name whose value has changed since makes the cell out of date (not saved). */
  deps?: Map<string, number>;
  /** Waiting its turn behind the cell the engine is evaluating (shown as In[*]). */
  queued?: boolean;
  el?: HTMLElement;
  /** The text input: one line, or a textarea when the source runs over several. */
  input?: HTMLInputElement | HTMLTextAreaElement;
  /** Visual (typeset, with holes) or raw text input; absent follows View › Visual math input. */
  mode?: "raw" | "visual";
  /** The visual input, when the cell has one. */
  mi?: MathInput;
  /** The visual input's tree, kept across re-renders while the source is still its text: it may
   *  have empty slots, whose text (`integrate(, x)`) does not read back. */
  tree?: Stmt;
  /** Lean cells: what Lean reports on the cell's lines (lean-cells.ts), shown as its output. */
  leanMessages?: LeanMessage[];
  /** A Lean exercise (an exercise with `lean`): `src` is the statement, ending `:= by`, which the reader
   *  cannot change; `attempt` is the reader's proof, `leanStart` the proof it starts as, `leanSolution`
   *  the author's, shown on request. Lean checks the two as one declaration of the notebook's Lean file. */
  lean?: boolean;
  leanStart?: string;
  leanSolution?: string;
  /** What Lean reports on the statement's lines (an unproved goal is reported at its `by`; not saved). */
  leanStmtMessages?: LeanMessage[];
  /** Math input Auto: whether the cell is typeset, decided for this source (re-decided when the
   *  cell is left with a different source, never while it is being typed in). */
  autoVisual?: boolean;
  autoFor?: string;
  /** A template just opened in the cell's text: the editor to show, caret and history included. */
  openedEdit?: MathEdit;
  /** A `?` cell's lookup (ask-cells.ts): its answer, where it came from, and how it was found. Saved,
   *  so running the notebook again evaluates the answer without asking again. */
  ask?: AskResult;
  /** While a lookup runs: its steps so far (the last is under way), each with when it began, and how
   *  the current one is getting on (a model's download). */
  askSteps?: { text: string; at: number }[];
  askDetail?: string;
  /** A lookup that found nothing: how it searched. */
  askTrail?: string[];
  /** Asking again failed and the cell kept its answer: why, until a lookup succeeds (not saved). */
  askFailed?: string;
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

type Tab = "notebook" | "studio" | "docs" | "courses";

/** One open notebook: its cells, its studio scenes and its own engine session. The globals below
 *  (`S.cells`, `S.docName`, `ST.scenes`, `sessionId`) are views of the current one; `stashDoc` and
 *  `loadDoc` swap them. */
/** A file attached to a notebook (attached or pasted): any type, held as text or as base64. A cell
 *  refers to it as `⟦name⟧`, and it is a value like an import (files.ts): shown by what it is, and
 *  turned into numbers only by a function called on it. */
interface Asset { name: string; mime: string; data: string; binary?: boolean }

interface Nb {
  id: string; name: string; sessionId: string;
  cells: Cell[]; scenes: Scene[]; studioActive: number; active: number; nextLabel: number;
  assets: Record<string, Asset>;
  /** The serialized notebook at the last save or open; the tab shows `*` while the live state differs. */
  savedText: string;
  /** The serialized notebook at the last stash, for the dirty mark of a document that is not current. */
  text: string;
  /** Whether the engine session has been rebuilt from the cells since the document was restored. */
  hydrated: boolean;
  /** The "not run yet" notice was dismissed for this notebook. */
  noticeDismissed?: boolean;
  /** A lesson of a course (or a notebook of a collection): which project, and which of its notebooks. */
  project?: ProjectRef;
  /** For a lesson of a course with a Lean prelude: the Lean of the lessons before it, in scope above the
   *  lesson's own Lean (its cells, and its exercises' statements with the author's proofs). */
  leanPrelude?: string;
}

/** A phone-sized screen: the sidebar floats over the paper and starts closed, the panel starts folded. */
const narrow = () => window.matchMedia("(max-width: 760px)").matches;

/** A remembered on/off preference (local storage; private mode just forgets it). */
function prefOn(key: string, dflt: boolean): boolean {
  try { const v = localStorage.getItem(key); return v === null ? dflt : v !== "off"; } catch { return dflt; }
}
function setPref(key: string, on: boolean) {
  try { localStorage.setItem(key, on ? "on" : "off"); } catch { /* private mode */ }
}

const S = {
  docs: [] as Nb[],
  doc: 0,
  cells: [] as Cell[],
  assets: {} as Record<string, Asset>,
  active: 0,
  rail: "outline" as "outline" | "palette",
  tab: "notebook" as Tab,
  panelTab: "explain" as "explain" | "log" | "lean",
  /** The bottom panel unfolded; the user's last choice is remembered across reloads. */
  panelOpen: prefOn("chalkmath.panel", !narrow()),
  sel: null as Selection | null,
  log: [] as LogLine[],
  caps: null as { engine: string; version: string; verified: boolean; features: string[]; ruleStatus?: RuleStatus[]; termination?: { status: string; theorem?: string; summary: string } } | null,
  ruleStatus: new Map<string, RuleStatus>(),
  engineMode: "lean-worker" as "lean-worker" | "http",
  httpUrl: "http://localhost:8787",
  busy: false,
  /** The engine: loading, ready, or failed — to load, or later (a crash) — with the reason. */
  kernel: "starting" as "starting" | "ready" | "failed",
  kernelError: "",
  kernelDetail: "",
  /** The cell the engine is evaluating now. */
  running: null as Cell | null,
  /** The cell that was running when the engine failed: a restart rebuilds the session up to it. */
  crashed: null as Cell | null,
  /** `picked`: a row was chosen with the arrows, so Enter takes it rather than running the cell. */
  comp: null as { cell: Cell; items: CompItem[]; index: number; picked: boolean; x: number; y: number } | null,
  /** Signature help: the call the caret is inside, and which argument it is in (View menu toggles it). */
  sig: null as { cell: Cell; key: string; sig: string; blurb: string; arg: number; pieces?: { text: string; param: boolean }[] } | null,
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
  /** The suggestions bar under a file's output (View › Suggestions bar). */
  suggestions: prefOn("chalkmath.suggestions", true),
  /** How math cells take their input (View menu): typeset with holes to fill, as text, or Auto —
   *  typeset where there is notation to show (a fraction, a power, a matrix, d/dx, ∫, Σ, √),
   *  highlighted text where there is none (`epicycles(llama, 60)`). A cell's own choice wins. */
  /** The math keypad above the keyboard while a math cell has the focus (View menu; on by default on phones). */
  keypad: prefOn("chalkmath.keypad", narrow()),
  inputMode: ((): "auto" | "visual" | "raw" => {
    try {
      const v = localStorage.getItem("chalkmath.inputmode");
      if (v === "auto" || v === "visual" || v === "raw") return v;
      if (localStorage.getItem("chalkmath.visual") === "on") return "visual";   // the earlier on/off preference
    } catch { /* private mode */ }
    return "auto";
  })(),
  /** Size of rendered mathematics in the cells (View menu): small, normal or large. */
  outSize: (() => { try { return (localStorage.getItem("chalkmath.outsize") as "s" | "m" | "l" | null) ?? "m"; } catch { return "m" as const; } })() as "s" | "m" | "l",
  menu: null as string | null,
  /** Run a notebook's cells when it opens (a file, a link, the tabs restored on reload). Off, the
   *  saved outputs show until Run all — nothing is sent to the engine, and no `import()` is fetched. */
  runOnOpen: prefOn("chalkmath.runonopen", true),
  /** Open files and links with every cell's work folded, whatever the file saved. */
  foldWorkOnOpen: prefOn("chalkmath.foldwork", false),
  /** The sidebar (outline / commands) beside the paper; the rail stays. */
  sidebarOpen: narrow() ? false : prefOn("chalkmath.sidebar", true),
  /** Developer mode (Help menu, or `?dev` in the address): the kernel picker (wasm / HTTP), the
   *  kernel log, and the rule count in the status bar. */
  dev: prefOn("chalkmath.dev", false) || new URLSearchParams(location.search).has("dev"),
  /** Help › Documentation: whether its tab is open, the page shown, and the contents' search. */
  guide: { open: false, page: "start", query: "" },
  courses: { open: false, project: null as string | null },
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

/** Feedback on something the reader did (saved, copied, could not open…): logged, and shown for a
 *  few seconds in the corner, where it is also announced to a screen reader. */
function notify(level: "ok" | "err", text: string) {
  log(level, text);
  let host = document.querySelector<HTMLElement>(".toasts");
  if (!host) { host = h("div", "toasts"); host.setAttribute("role", "status"); host.setAttribute("aria-live", "polite"); document.body.append(host); }
  const t = h("div", `toast ${level}`, text);
  t.addEventListener("click", () => t.remove());
  host.append(t);
  while (host.childElementCount > 3) host.firstElementChild!.remove();
  setTimeout(() => t.remove(), level === "err" ? 8000 : 4000);
}

// ---------------------------------------------------------------------------
// Theme
// ---------------------------------------------------------------------------

function applyTheme(t: "dark" | "light") {
  S.theme = t;
  document.documentElement.setAttribute("data-theme", t);
  setLeanDark(t !== "light");
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

/** Which connection is current: a reply or failure from an older one is ignored. */
let connGen = 0;

/** Start an engine (a fresh worker, or a client for the HTTP one). Closing the old client fails
 *  whatever was in flight on it; the sessions it held are gone with a worker. */
async function connect() {
  const gen = ++connGen;
  client?.close();
  client = null;
  S.caps = null; S.kernel = "starting"; S.kernelError = "";
  renderChrome();
  if (S.engineMode === "lean-worker" && typeof WebAssembly !== "object") {
    kernelFailed("This browser cannot run WebAssembly, which the engine needs. A current Chrome, Firefox, Safari or Edge can.");
    return;
  }
  let c: EngineClient;
  try {
    c = S.engineMode === "lean-worker"
      ? createClient(workerTransport(new Worker(`engine-lean.worker.js?v=${typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev"}`)))
      : createClient(httpTransport(S.httpUrl));
  } catch (e) { kernelFailed("The engine could not start in this browser.", e instanceof Error ? e.message : String(e)); return; }
  client = c;
  c.onError?.((e) => {
    if (gen !== connGen) return;
    if (S.kernel === "starting") kernelFailed("The engine failed to load. Check your connection, then restart it.", e.message);
    else kernelFailed("The engine stopped unexpectedly. Restarting it re-runs the cells that had outputs.", e.message);
  });
  const t0 = performance.now();
  try {
    const caps = await c.call("engine.capabilities", {});
    if (gen !== connGen) return;
    S.caps = caps; S.kernel = "ready";
    S.ruleStatus = new Map((caps.ruleStatus ?? []).map((r) => [r.rule, r]));
    log("ok", `${caps.engine} v${caps.version} ready in ${Math.round(performance.now() - t0)} ms`);
  } catch (e) {
    // kernelFailed drops the client: when it is gone, the failure has been reported already
    if (gen === connGen && client === c) kernelFailed(S.engineMode === "http" ? `The engine at ${S.httpUrl} did not answer.` : "The engine failed to load. Check your connection, then restart it.", e instanceof Error ? e.message : String(e));
    return;
  }
  renderChrome();
  renderPanel();
  if (S.tab === "docs") renderDocs();   // the examples' outputs were waiting for the engine
}

/** The engine is gone, and every session it held with it; `restartEngine` rebuilds them. `why` is
 *  for the reader, `detail` (the browser's error) for the log and the notice's tooltip. */
function kernelFailed(why: string, detail = "") {
  S.kernel = "failed"; S.kernelError = why; S.kernelDetail = detail; S.caps = null;
  if (S.running) S.crashed = S.running;
  client?.close(); client = null;
  log("err", detail ? `${why} (${detail})` : why);
  renderChrome(); renderPanel();
}

/** The cell stopped by `interrupt`, whose pending call fails when its engine is closed. */
let stoppedCell: Cell | null = null;
/** Bumped by an interrupt: runs queued before it, and `runAll` loops started before it, are dropped. */
let runGen = 0;
/** Evaluations happen one at a time, in the order they were asked for. */
let runChain: Promise<void> = Promise.resolve();
/** Stops the lookup in progress (a `?` cell being evaluated). */
let askAbort: AbortController | null = null;
/** A `?` cell asked to look its question up again (its saved answer set aside), or to check an answer
 *  from the model's knowledge with a search. */
const askAgain = new WeakMap<Cell, "again" | "search">();

/** Stop the evaluation in progress. The engine is synchronous wasm in a worker and cannot be
 *  interrupted from outside, so the worker is terminated and a fresh one started; the session is
 *  rebuilt by re-running the cells above the stopped one (their outputs are what the session held). */
async function interrupt() {
  const cell = S.running; if (!cell) return;
  // a lookup is stopped where it is (the engine was not asked anything yet), and runs queued after it are dropped
  if (askAbort) { runGen++; askAbort.abort(); return; }
  stoppedCell = cell; runGen++;
  log("ok", "interrupted: restarting the engine");
  await restartEngine(cell);
}

/** Start a new engine after an interrupt, a crash or a failed load, and rebuild the current
 *  notebook's session from what it held: the cells with an output, above `upTo` when one was
 *  stopped or crashed (a failed or stopped cell bound nothing, and one that hung would hang again).
 *  A notebook never run is run whole if notebooks run on open. An HTTP engine keeps its sessions. */
async function restartEngine(upTo: Cell | null = null) {
  S.crashed = null;
  const http = S.engineMode === "http";
  await connect();
  if (S.kernel !== "ready" || http) return;
  const d = currentDoc(); if (!d) return;
  for (const o of S.docs) if (o !== d) o.hydrated = false;   // their sessions were in the old worker
  if (!d.hydrated) { if (S.runOnOpen) hydrate(d); return; }
  const i = upTo ? S.cells.indexOf(upTo) : -1;
  const gen = runGen;
  for (const c of i >= 0 ? S.cells.slice(0, i) : [...S.cells]) {
    if (gen !== runGen || !S.docs.includes(d)) return;
    if ((c.type ?? "math") === "math" && (c.outLatex || c.file) && cellSrc(c).trim()) await runCell(c);
  }
  renderChrome();
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
  if (cell.type === "lean" || (cell.type === "exercise" && cell.lean)) return;   // Lean checks as you type (lean-cells.ts)
  cell.src = cellSrc(cell);
  if (!cell.src.trim()) return;
  if (S.kernel === "failed") {
    // the notice above the paper says why and offers the restart: draw the eye to it
    const n = $(".notice"); n.classList.remove("flash"); void n.offsetWidth; n.classList.add("flash");
    return;
  }
  // wait for the evaluations asked for before this one; an interrupt meanwhile drops it
  const gen = runGen;
  const prev = runChain;
  let release!: () => void;
  runChain = new Promise<void>((r) => { release = r; });
  cell.queued = true; renderCellBody(cell);
  try {
    await prev;
    cell.queued = false;
    // the cell is evaluated in its own notebook's session, which need not be the current one by now
    // (a notebook re-running when its tab was left); a closed notebook's cells are not evaluated
    const d = docOf(cell);
    if (gen === runGen && client && d) await (cell.type === "exercise" ? checkExercise(cell, client, d.sessionId) : evaluateCell(cell, client, d.sessionId));
    else renderCellBody(cell);
  } finally { release(); }
}

async function evaluateCell(cell: Cell, client: EngineClient, sessionId: string) {
  const src = cell.src;
  S.busy = true; S.running = cell;
  renderChrome(); renderCellBody(cell);
  const t0 = performance.now();
  const isPlot = /^\s*(plot|epicycles|dft)\s*\(/.test(src), isManip = /^\s*manipulate\s*\(/.test(src);
  log("rpc", `${isPlot ? "engine.plot" : isManip ? "engine.manipulate" : "engine.evaluate"} ${JSON.stringify(src)}`);
  try {
    // a question is looked up first (or its saved answer reused); the engine evaluates the answer
    const askM = ASK_CELL.exec(src);
    let asked: string | null = null;
    if (askM) {
      const question = askM[2]!.trim();
      const again = askAgain.get(cell);
      if (!cell.ask || cell.ask.question !== question || again) {
        delete cell.askTrail;
        askAbort = new AbortController();
        log("rpc", `lookup ${JSON.stringify(question)}`);
        try {
          cell.ask = await runLookup(question, {
            signal: askAbort.signal, forceSearch: again === "search",
            onProgress: (line) => { (cell.askSteps ??= []).push({ text: line, at: performance.now() }); delete cell.askDetail; renderCellBody(cell); },
            onDetail: (detail) => { cell.askDetail = detail; tickAsk(); },
            confirmSearch,
          });
          delete cell.askFailed;
          log("ok", `lookup: ${cell.ask.via}, ${cell.ask.source.length > 80 ? `${cell.ask.source.slice(0, 80)}…` : cell.ask.source}`);
        } catch (e) {
          // asking again (or checking) and finding nothing keeps the answer the cell had
          if (!(e instanceof AskError && cell.ask?.question === question)) throw e;
          cell.askFailed = e.message === "Stopped." ? "Stopped." : e.message;
          notify("err", e.message === "Stopped." ? "Stopped: the cell keeps its answer." : `${again === "search" ? "Check" : "Lookup"}: ${e.message} The cell keeps its answer.`);
          log("err", `lookup: ${e.message}`);
        } finally { askAbort = null; delete cell.askSteps; delete cell.askDetail; askAgain.delete(cell); }
      }
      asked = askSource(askM[1], cell.ask);
    }
    // a file is the notebook's: a cell whose value is one shows it, and functions called on one are
    // evaluated here (samplePoints, matrix, …); the engine only ever sees numbers
    const scope = fileScope(sessionId, docOf(cell)?.assets ?? S.assets);
    if (asked === null) await fetchImports(src);
    const fc = asked === null ? fileCellOf(src, scope) : null;
    if (fc) return await evaluateFileCell(cell, fc, client, sessionId, t0);
    const { src: sent, notes } = asked !== null ? { src: asked, notes: [] as string[] } : resolveFiles(src, scope);
    const params = { sessionId, cellId: cell.id, source: sent, showWork: true, paths: true, outline: true };
    const r = isPlot ? await client.call("engine.plot", params)
      : isManip ? await client.call("engine.manipulate", params)
      : await client.call("engine.evaluate", params);
    cell.ms = performance.now() - t0;
    queueMicrotask(autosave);
    if (r.ok) {
      cell.label = r.label ?? cell.label ?? nextLabel++;
      cell.outLatex = r.rendered.latex;
      cell.outText = r.rendered.text;
      cell.semantics = "semantics" in r && r.semantics === "complex" ? "complex" : "real";
      cell.echoLatex = r.inputRendered?.latex;
      // a file's numbers can be hundreds of rows: then the interpretation names what made them instead
      // (a few numbers read better as themselves: mean([0.33; 4.87; …]))
      if (notes.length && sent.length - src.length > 400) cell.echoLatex = `\\text{${notes.map((n) => n.replace(/[\\{}$&#^_%~]/g, "")).join("; ")}}`;
      if (asked !== null) delete cell.echoLatex;   // the input is the question; the answer is the output
      delete cell.file;
      // a dft cell's input is a long list of sample points: say how many rather than typeset them
      if (/^\s*dft\s*\(\s*\[/.test(src)) {
        // a literal list is long: say how many points rather than typeset them. Rows `[x, y; …]` are
        // points; a single row `[z₁, z₂, …]` is complex points. A bound name (`dft(llama, 60)`) echoes as itself.
        const body = /\[([^\]]*)\]/.exec(src)?.[1] ?? "";
        const n = body.includes(";") ? body.split(";").length : body.split(",").length;
        cell.echoLatex = `\\text{dft of ${n} sample point${n === 1 ? "" : "s"}}`;
      }
      // an engine that predates outlines sends the derivation itself
      cell.steps = r.derivation?.steps ?? [];
      cell.outline = r.outline?.steps;
      delete cell.openEntries; WORK_FAILED.delete(cell);
      delete cell.error;
      // this output is a number: a file that had its label before a restart no longer does
      if (r.label) { LAST_LABEL.set(sessionId, r.label); FILE_OUTS.delete(`${sessionId}:${r.label}`); }
      delete cell.plot; delete cell.manip; delete cell.outDeBruijn; delete cell.reading; delete cell.kind; delete cell.hasse; delete cell.summary; delete cell.visuals;
      if ("kind" in r && r.kind === "poset") { cell.kind = "order"; cell.hasse = r.hasse; cell.summary = r.summary; }
      if ("kind" in r && r.kind === "logic") { cell.kind = "logic"; cell.summary = r.summary; }
      if ("kind" in r && r.kind === "system") { cell.kind = "system"; cell.summary = r.summary; }
      const vs = knownVisuals("visuals" in r ? r.visuals : undefined);
      if (vs.length) cell.visuals = vs;
      if ("kind" in r && r.kind === "plot") cell.plot = plotDataOf(r);
      if ("kind" in r && r.kind === "manipulate") {
        // the slider stays where the reader left it, when the cell still has a frame there
        const before = cell.manipAt ?? 0;
        cell.manip = manipDataOf(r);
        cell.manipAt = Math.min(Math.round(before), cell.manip.frames.length - 1);
      } else { delete cell.manip; delete cell.manipAt; }
      if ("kind" in r && r.kind === "lambda") { cell.outDeBruijn = r.renderedDeBruijn?.latex; cell.reading = r.reading; cell.kind = "λ-term"; }
      log("ok", `Out[${cell.label}] ${r.rendered.text}  (${cell.ms.toFixed(1)} ms, ${(cell.outline ?? cell.steps).length} steps)`);
      announce(`Out ${cell.label}: ${r.rendered.text}`);
      recordRun(cell, sessionId, "bound" in r ? r.bound?.[0] : undefined, r.rendered.text);
      if ("bound" in r && r.bound?.length) {
        log("ok", `bound ${r.bound.join(", ")}`);
        const k = `${sessionId}:${r.bound[0]}`;
        if (r.params?.length) USER_FNS.set(k, r.params); else USER_FNS.delete(k);
        USER_NAMES.add(k);
        if ("kind" in r && r.kind === "lambda") LAMBDA_NAMES.add(k); else LAMBDA_NAMES.delete(k);
        FILE_VARS.delete(k);   // a name bound to a number is no longer the file it was
        // a bound matrix's shape, for what `name[[` offers
        const m = matrixEntries(r.rendered.latex);
        if (m) MATRIX_SHAPES.set(k, { rows: m.length, cols: m[0]!.length }); else MATRIX_SHAPES.delete(k);
        renderHighlights();
      }
    } else {
      cell.label = r.label ?? cell.label ?? nextLabel++;
      if (r.label) { LAST_LABEL.set(sessionId, r.label); FILE_OUTS.delete(`${sessionId}:${r.label}`); }
      delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.plot; delete cell.manip; delete cell.file; cell.steps = []; delete cell.outline;
      cell.error = r.error;
      recordRun(cell, sessionId);
      log("err", `${r.error.code}: ${r.error.message}`);
      announce(`Error: ${r.error.message}`);
    }
  } catch (e) {
    cell.ms = performance.now() - t0;
    if (e instanceof AskError) {
      // the lookup found nothing: say why and how it searched; the engine was not asked
      cell.label = cell.label ?? nextLabel++;
      cell.error = { message: e.message === "Stopped." ? "Stopped." : `No answer: ${e.message}` };
      cell.askTrail = e.trail;
      delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.plot; delete cell.manip; delete cell.file; cell.steps = []; delete cell.outline;
      log("err", `lookup: ${e.message}`);
      finishEvaluation(cell);
      return;
    }
    const stopped = S.engineMode === "http" ? "Stopped." : "Stopped. The engine was restarted, and the cells above this one with outputs were run again.";
    cell.error = { message: cell === stoppedCell ? stopped
      : S.kernel === "failed" ? "The engine stopped while evaluating this cell." : e instanceof Error ? e.message : String(e) };
    if (cell === stoppedCell) stoppedCell = null;
    // the output shown must be this run's: a stale one would also be replayed after a restart
    delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.plot; delete cell.manip; delete cell.file; cell.steps = []; delete cell.outline;
    log("err", cell.error.message);
  }
  finishEvaluation(cell);
}

/** Exercises whose next run is the reader's Check (the answer is sent); any other run of an exercise
 *  (Run all, opening the notebook) re-checks only an answer that was checked before. */
const CHECK_NOW = new WeakSet<Cell>();
/** Run an exercise: the engine evaluates the question (its value is the answer, its work the
 *  solution, both held back until the reader asks) and compares the reader's answer with it. */
async function checkExercise(cell: Cell, client: EngineClient, sessionId: string) {
  const answer = (CHECK_NOW.has(cell) || cell.verdict) && cell.attempt?.trim() ? cell.attempt : undefined;
  CHECK_NOW.delete(cell);
  S.busy = true; S.running = cell;
  renderChrome(); renderCellBody(cell);
  const t0 = performance.now();
  log("rpc", `engine.check ${JSON.stringify(cell.src)}${answer !== undefined ? ` answer ${JSON.stringify(answer)}` : ""}`);
  try {
    const r = await client.call("engine.check", { sessionId, cellId: cell.id, source: cell.src, ...(answer !== undefined ? { answer } : {}), showWork: true, paths: true, outline: true });
    cell.ms = performance.now() - t0;
    queueMicrotask(autosave);
    recordRun(cell, sessionId);
    if (!r.ok) {
      cell.error = r.error;
      delete cell.outLatex; delete cell.outText; delete cell.echoLatex; cell.steps = []; delete cell.outline;
      log("err", `${r.error.code}: ${r.error.message}`);
    } else {
      delete cell.error;
      cell.echoLatex = r.inputRendered.latex;
      cell.outLatex = r.rendered.latex; cell.outText = r.rendered.text;
      cell.semantics = mentionsI(r.rendered.text) || mentionsI(cell.src) ? "complex" : "real";
      cell.steps = r.derivation?.steps ?? []; cell.outline = r.outline?.steps;
      delete cell.openEntries; WORK_FAILED.delete(cell);
      if (r.kind === "lambda") cell.kind = "λ-term"; else delete cell.kind;
      if (answer !== undefined && r.answer) {
        cell.verdict = r.answer.ok
          ? { equivalent: !!r.equivalent, answerLatex: r.answer.rendered.latex, normalLatex: r.answer.normalForm.latex }
          : { equivalent: false, error: r.answer.error };
        log(r.equivalent ? "ok" : "err", `answer ${r.equivalent ? "equivalent" : r.answer.ok ? "not equivalent" : r.answer.error.message}`);
        if (docOf(cell) === currentDoc()) queueMicrotask(recordProgress);
        announce(r.equivalent ? "Correct." : r.answer.ok ? "Not equivalent to the answer." : `Error: ${r.answer.error.message}`);
      }
    }
  } catch (e) {
    cell.error = { message: e instanceof Error ? e.message : String(e) };
    log("err", cell.error.message);
  }
  S.busy = false; S.running = null;
  renderCellBody(cell); renderChrome(); renderSidebar();
}
/** Whether a source mentions `i` (the complex unit), as the engine's `semantics` does. */
const mentionsI = (src: string) => /(^|[^A-Za-z0-9_])i([^A-Za-z0-9_(]|$)/.test(src);

/** A plot reply as the notebook draws it: each curve's term and samples, and an epicycle drawing's circles. */
function plotDataOf(r: Pick<PlotResult, "var" | "from" | "to" | "series" | "terms">): PlotData {
  const p: PlotData = { var: r.var, from: r.from, to: r.to, series: r.series.map((s) => ({ latex: s.rendered.latex, text: s.rendered.text, points: s.points, ...(s.parametric ? { parametric: true } : {}) })) };
  if (r.terms?.length) p.terms = r.terms.map((t) => ({ k: t.k, re: t.re, im: t.im, ...(t.rendered ? { latex: t.rendered.latex } : {}) }));
  return p;
}

/** A manipulate reply as the notebook shows it: each frame's value and term, and its plot. */
function manipDataOf(r: ManipulateResult): ManipData {
  const part = (p: { rendered: { latex: string }; label?: string; plot?: Parameters<typeof plotDataOf>[0]; work?: { latex: string }[] }): ManipPart => ({
    latex: p.rendered.latex, ...(p.label ? { name: p.label } : {}), ...(p.plot ? { plot: plotDataOf(p.plot) } : {}),
    ...(p.work?.length ? { work: p.work.map((w) => w.latex) } : {}),
  });
  return { param: r.param, frames: r.frames.map((f) => ({ value: f.value, label: f.valueRendered.latex, latex: f.rendered.latex, parts: f.parts?.length ? f.parts.map(part) : [part(f)] })) };
}

/** After a cell's evaluation: the notebook is free, and the cell shows what it got. */
function finishEvaluation(cell: Cell) {
  S.busy = false; S.running = null;
  S.sel = null;
  renderCellBody(cell);
  refreshRelativeRefs();
  renderChrome();
  renderSidebar();
  renderPanel();
  if (cell === S.cells[S.cells.length - 1]) addCell();
}

/** A cell whose value is a file: it shows the file, and `let x = …` binds the name to it here. The
 *  engine never sees the file, but the evaluation is numbered like any other: the engine is asked
 *  to evaluate nothing, which fails and takes the next number, so `In[n]` and `%n` keep one count
 *  (and `%` after this cell is the file). */
async function evaluateFileCell(cell: Cell, fc: { bind?: string; file: FileValue }, client: EngineClient, sessionId: string, t0: number) {
  const { bind, file } = fc;
  log("rpc", `file ${file.name} (${file.mime}, ${fmtSize(fileSize(file))})${bind ? ` as ${bind}` : ""}`);
  const r = await client.call("engine.evaluate", { sessionId, cellId: cell.id, source: "" });
  cell.ms = performance.now() - t0;
  cell.label = r.label ?? cell.label ?? nextLabel++;
  if (r.label) { LAST_LABEL.set(sessionId, r.label); FILE_OUTS.set(`${sessionId}:${r.label}`, file); }
  recordRun(cell, sessionId, bind, `${file.name} ${fileSize(file)} ${JSON.stringify(file.origin)}`);
  if (bind) {
    const k = `${sessionId}:${bind}`;
    FILE_VARS.set(k, file); USER_NAMES.add(k); USER_FNS.delete(k);
    renderHighlights();
  }
  delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.plot; delete cell.manip; delete cell.error;
  delete cell.outDeBruijn; delete cell.reading; delete cell.kind; delete cell.hasse; delete cell.summary; delete cell.visuals;
  cell.steps = []; delete cell.outline;
  cell.file = { name: file.name, mime: file.mime, size: fileSize(file), origin: file.origin };
  CELL_FILES.set(cell, file);
  if (cell.form && cell.form !== "text") delete cell.form;
  queueMicrotask(autosave);
  log("ok", `Out[${cell.label}] ${file.name}: ${mimeLabel(file.mime)}`);
  announce(`Out ${cell.label}: ${file.name}, ${mimeLabel(file.mime)}`);
  finishEvaluation(cell);
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
    const d = currentDoc();
    notify("err", d && !d.hydrated ? "Run the notebook first: the engine explains what it has evaluated since the notebook was opened." : `Could not explain that: ${e instanceof Error ? e.message : String(e)}`);
  }
  markSelection();
  renderPanelHead(); renderPanel();
}

/** Show the current selection in the cells: the selected subterm and, for a step, its row. */
function markSelection() {
  document.querySelectorAll(".katex [data-path].sel").forEach((x) => x.classList.remove("sel"));
  document.querySelectorAll(".step.on").forEach((x) => x.classList.remove("on"));
  remarkGraphs();
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
  if (cell.file) return [["table", "table"], ["text", "text"]];
  const m = cell.outLatex ? matrixEntries(cell.outLatex) : null;
  if (m) {
    const forms: [string, string][] = [["matrix", "matrix [ ]"], ["pmatrix", "matrix ( )"], ["grid", "grid"], ["table", "table"], ["data", "data table"], ["input", "input form"]];
    // a large matrix is a value to bind and read, not to typeset: it shows as a data table
    return bigMatrix(m) ? [forms[4]!, ...forms.slice(0, 4), forms[5]!] : forms;
  }
  return cell.outLatex?.includes("\\begin{bmatrix}")
    ? [["matrix", "matrix [ ]"], ["pmatrix", "matrix ( )"], ["grid", "grid"], ["table", "table"], ["input", "input form"]]
    : [["standard", "standard"], ["input", "input form"]];
}
/** More rows or columns than typeset well: shown as a data table unless another form is chosen. */
const bigMatrix = (rows: string[][]) => rows.length > 24 || (rows[0]?.length ?? 0) > 12;
/** The output form a cell shows: the one chosen, or the first its output offers. */
const formOf = (cell: Cell) => cell.form ?? formsFor(cell)[0]![0];
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

/** A matrix of more than 24 rows typeset shows its first three, a row of dots with the count, and its
 *  last (a large matrix alone shows as a data table unless typesetting is chosen; this is for one
 *  inside a term). Rows are split at the top level only, so a nested matrix is left alone. */
function abridgeMatrix(latex: string): string {
  return latex.replace(/\\begin\{bmatrix\}([\s\S]*?)\\end\{bmatrix\}/g, (whole, body: string) => {
    const rows = body.split(" \\\\ ");
    if (rows.length <= 24 || body.includes("\\begin{")) return whole;
    const cols = (rows[0]?.match(/&/g)?.length ?? 0) + 1;
    const dots = Array.from({ length: cols }, () => "\\vdots").join(" & ");
    return `\\begin{bmatrix}${rows.slice(0, 3).join(" \\\\ ")} \\\\ ${dots} \\\\ ${rows[rows.length - 1]}\\end{bmatrix}\\;{\\scriptstyle (${rows.length}\\times${cols})}`;
  });
}

/** Make every path-annotated subterm of a rendered term clickable. */
function wireTerm(host: HTMLElement, cell: Cell, term: TermRef) {
  host.dataset["term"] = termKey(term);
  wirePaths(host, cell, term);
}
/** Make the path-annotated subterms inside an element clickable (rows a data table adds later). */
function wirePaths(host: HTMLElement, cell: Cell, term: TermRef) {
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
/** The open notebook a cell belongs to (the current one's cells are the live `S.cells`), if any. */
const docOf = (cell: Cell) => S.docs.find((d) => (d === currentDoc() ? S.cells : d.cells).includes(cell));

/** Copy the live globals back into the current document. */
function stashDoc() {
  const d = currentDoc(); if (!d) return;
  d.name = S.docName; d.cells = S.cells; d.scenes = ST.scenes; d.studioActive = ST.active; d.active = S.active; d.assets = S.assets;
  d.nextLabel = nextLabel; d.sessionId = sessionId; d.text = serializeNotebook();
}

/** Make document `i` current: its cells, scenes and session become the live ones. A document whose
 *  session has not been rebuilt since it was restored is re-run once the engine is up. */
function loadDoc(i: number) {
  stashDoc();
  const d = S.docs[i]; if (!d) return;
  S.doc = i;
  S.docName = d.name; S.cells = d.cells; S.assets = d.assets; ST.scenes = d.scenes; ST.active = d.studioActive; ST.t = 0; stopPlayback();
  S.active = Math.min(d.active, Math.max(0, d.cells.length - 1)); nextLabel = d.nextLabel; sessionId = d.sessionId;
  S.sel = null; hideCompletions(); hideSigHelp(); hideHover();
  renderChrome(); renderCells(); renderSidebar(); renderPanelHead(); renderPanel(); renderLessonBar();
  if (S.tab === "studio") renderStudio();
  if (!d.hydrated && S.kernel === "ready" && S.runOnOpen) hydrate(d);
}

/** Rebuild a restored document's engine session by re-running its cells. Re-running renumbers the
 *  cells, so a document that was clean stays clean: its saved baseline moves to the re-run state. */
function hydrate(d: Nb) {
  const wasClean = !docDirty(d);
  void runAll().then(() => { if (wasClean && d === currentDoc()) { d.savedText = serializeNotebook(); renderTabs(); autosave(); } });
}

function makeDoc(name: string, cells: Cell[] = [], scenes: Scene[] = [], assets: Record<string, Asset> = {}): Nb {
  return { id: `d${Date.now().toString(36)}${Math.random().toString(36).slice(2, 6)}`, name, sessionId: crypto.randomUUID(),
    cells, scenes, assets, studioActive: 0, active: 0, nextLabel: Math.max(0, ...cells.map((c) => c.label ?? 0)) + 1,
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
  return d.name === "untitled.chalk" && d.scenes.length === 0 && !Object.keys(d.assets).length && d.cells.every((c) => !cellSrc(c).trim() && !c.outLatex && !c.file);
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

/** The tab bar: one tab per open notebook (italic with a star while unsaved), then the studio, then
 *  the documentation while it is open (Help › Documentation; its × closes it). */
function renderTabs() {
  const tabs = $(".tabbar"); tabs.innerHTML = "";
  S.docs.forEach((d, i) => {
    const dirty = docDirty(d);
    const on = S.tab === "notebook" && i === S.doc;
    const t = h("div", `tab${on ? " on" : ""}${dirty ? " dirty" : ""}`);
    t.title = dirty ? `${d.name} — unsaved changes` : d.name;
    const x = asButton(h("span", "x", "×"), `Close ${d.name}`); x.title = "Close";
    x.addEventListener("click", (ev) => { ev.stopPropagation(); closeDoc(i); });
    // the label is the button (the × beside it is another; one may not hold the other)
    const label = asButton(h("span", "label", `${d.name}${dirty ? "*" : ""}`), `${d.name}${dirty ? ", unsaved changes" : ""}`);
    label.setAttribute("aria-current", String(on));
    t.append(label, x);
    t.addEventListener("click", () => { if (i !== S.doc) loadDoc(i); switchTab("notebook"); });
    tabs.append(t);
  });
  for (const [key, label] of [["studio", "manim studio"], ...(S.courses.open ? [["courses", "courses"] as const] : []), ...(S.guide.open ? [["docs", "documentation"] as const] : [])] as const) {
    const t = asButton(h("div", `tab${S.tab === key ? " on" : ""}`), label);
    t.setAttribute("aria-current", String(S.tab === key));
    t.append(h("span", "label", label));
    if (key === "docs" || key === "courses") {
      const x = asButton(h("span", "x", "×"), key === "docs" ? "Close the documentation" : "Close the courses"); x.title = "Close";
      x.addEventListener("click", (ev) => { ev.stopPropagation(); if (key === "docs") closeDocs(); else closeCourses(); });
      t.append(x);
    }
    t.addEventListener("click", () => switchTab(key));
    tabs.append(t);
  }
  tabs.append((() => { const a = asButton(h("div", "tabadd", "+"), "New notebook"); a.title = "New notebook"; a.addEventListener("click", () => { newDoc(); switchTab("notebook"); }); return a; })());
}

// ---------------------------------------------------------------------------
// Notebook files (.chalk): sources, outputs and studio scenes as JSON
// ---------------------------------------------------------------------------

interface ChalkFile {
  /** Format version. Files written as `.lemma` before the rename carry `lemma: 1` instead and still open. */
  chalk?: 1; lemma?: 1; name: string;
  cells: { src: string; type?: Cell["type"] | undefined; collapsed?: boolean | undefined; showWork: boolean; stepwise?: number | undefined; prompt?: string | undefined; hints?: string[] | undefined; hideQuestion?: boolean | undefined; attempt?: string | undefined; hintsShown?: number | undefined; verdict?: Verdict | undefined; solution?: boolean | undefined; lean?: boolean | undefined; leanStart?: string | undefined; leanSolution?: string | undefined; slider?: { min: number; max: number; step: number } | undefined; label: number | null; outLatex?: string | undefined; outText?: string | undefined; form?: string | undefined; semantics?: "real" | "complex" | undefined; echoLatex?: string | undefined; steps?: Step[] | undefined; outline?: StepOutline[] | undefined; error?: Cell["error"] | undefined; plot?: PlotData | undefined; visuals?: KnownVisual[] | undefined; summary?: string | undefined; mode?: Cell["mode"] | undefined; ask?: AskResult | undefined; file?: FileMeta | undefined; noSuggest?: true | undefined }[];
  scenes: Scene[];
  /** Images attached to the notebook, by name. */
  assets?: Record<string, Asset>;
  /** The project the notebook was opened from (a course's lesson), so it keeps its place in it. */
  project?: ProjectRef;
  /** The Lean of the course's earlier lessons, in scope in this one (`Nb.leanPrelude`). */
  leanPrelude?: string;
}

/** A cell's source as the user has it now: the live editor's text when there is one. */
const cellSrc = (c: Cell) => c.input?.value ?? c.ta?.value ?? c.src;

/** A cell's steps are kept in a file only up to this size: a long derivation of a big term (a sum
 *  of integrals, with the nested checks) runs to megabytes, and the notebook re-runs every cell
 *  when it opens a file anyway — the steps come back then. The output itself is always kept, and so
 *  is the outline of work that was never opened (it has no terms, so it is small). */
const STEPS_BUDGET = 256 * 1024;
function stepsToSave(c: Cell): Step[] | undefined {
  if (!c.steps?.length) return c.steps;
  return JSON.stringify(c.steps).length <= STEPS_BUDGET ? c.steps : undefined;
}
/** The outline a file keeps when it does not keep the steps, so the cell still offers its work. */
function outlineToSave(c: Cell): StepOutline[] | undefined {
  if (!c.steps?.length) return c.outline;
  return stepsToSave(c) ? undefined : outlineOf(c.steps);
}
/** Steps without their terms, as an `outline` reply would have sent them. */
const outlineOf = (steps: Step[]): StepOutline[] => steps.map((st) => ({ rule: st.rule, explanation: st.explanation, path: st.path,
  ...(printsUnchanged(st) ? { quiet: true } : {}), ...(st.sub ? { sub: { steps: outlineOf(st.sub.steps) } } : {}) }));

function serializeNotebook(): string {
  const doc: ChalkFile = {
    chalk: 1, name: S.docName,
    cells: S.cells.map((c) => ({ src: cellSrc(c), type: c.type, collapsed: c.collapsed || undefined, showWork: c.showWork, stepwise: c.stepwise, slider: c.slider, ...exerciseToSave(c), label: c.label, outLatex: c.outLatex, outText: c.outText, form: c.form, semantics: c.semantics, echoLatex: c.echoLatex, steps: stepsToSave(c), outline: outlineToSave(c), error: c.error, plot: c.plot, visuals: c.visuals, summary: c.visuals ? c.summary : undefined, mode: c.mode, ask: c.ask, file: c.file, noSuggest: c.noSuggest || undefined })),
    scenes: ST.scenes,
    ...(Object.keys(S.assets).length ? { assets: S.assets } : {}),
    ...(currentDoc()?.project ? { project: currentDoc()!.project } : {}),
    ...(currentDoc()?.leanPrelude ? { leanPrelude: currentDoc()!.leanPrelude } : {}),
  };
  return JSON.stringify(doc, null, 2);
}

/** Replace the notebook with a file's contents: saved outputs show at once, then every cell is
 *  re-run in order so the engine's session (and with it `explain`) matches what is shown. */
async function loadNotebook(text: string, name?: string, project?: ProjectRef, prelude?: string) {
  let doc: ChalkFile;
  try { doc = JSON.parse(text) as ChalkFile; } catch { notify("err", "That file is not a ChalkMath notebook (it is not valid JSON)."); return; }
  if ((doc.chalk !== 1 && doc.lemma !== 1) || !Array.isArray(doc.cells)) { notify("err", "That file is not a ChalkMath notebook."); return; }
  const d = makeDoc(name ?? doc.name ?? "untitled.chalk", cellsFromFile(doc, S.foldWorkOnOpen), Array.isArray(doc.scenes) ? doc.scenes : [], assetsFromFile(doc));
  if (!d.cells.length) d.cells.push(freshCell());
  const pr = project ?? projectRefOf(doc);
  if (pr) d.project = pr;
  const pre = prelude ?? (typeof doc.leanPrelude === "string" ? doc.leanPrelude : "");
  if (pre) d.leanPrelude = pre;
  // an untouched new notebook is replaced; otherwise the file gets its own tab
  const cur = currentDoc();
  if (cur && docPristine(cur)) { stashDoc(); S.docs[S.doc] = d; S.doc = -1; loadDoc(S.docs.indexOf(d)); }
  else { S.docs.push(d); loadDoc(S.docs.length - 1); }
  switchTab("notebook");
  log("ok", `opened ${d.name}: ${d.cells.length} cells, ${d.scenes.length} scenes`);
  if (S.runOnOpen && S.kernel !== "failed") await runAll();
  else { d.hydrated = false; renderChrome(); }
  d.savedText = serializeNotebook();
  renderTabs();
  autosave();
}

/** A file's attachments: only well-formed records are kept. */
function assetsFromFile(doc: ChalkFile): Record<string, Asset> {
  const out: Record<string, Asset> = {};
  for (const [name, a] of Object.entries(doc.assets ?? {})) {
    if (!a || typeof a.data !== "string" || typeof a.mime !== "string") continue;
    out[name] = { name, mime: a.mime, data: a.data, ...(a.binary ? { binary: true } : {}) };
  }
  return out;
}

/** An exercise's own fields, as a file keeps them. */
function exerciseToSave(c: Cell): Partial<ChalkFile["cells"][number]> {
  if (c.type !== "exercise") return {};
  return { prompt: c.prompt || undefined, hints: c.hints?.length ? c.hints : undefined, hideQuestion: c.hideQuestion || undefined,
    attempt: c.attempt || undefined, hintsShown: c.hintsShown || undefined, verdict: c.verdict, solution: c.solution || undefined,
    lean: c.lean || undefined, leanStart: c.lean ? c.leanStart : undefined, leanSolution: c.lean ? c.leanSolution : undefined };
}
/** An exercise's fields from a file's record; only well-formed ones are kept. */
function exerciseFromFile(cell: Cell, c: ChalkFile["cells"][number]) {
  cell.editing = !c.src.trim();
  if (typeof c.prompt === "string") cell.prompt = c.prompt;
  if (Array.isArray(c.hints)) cell.hints = c.hints.filter((x) => typeof x === "string");
  if (c.hideQuestion) cell.hideQuestion = true;
  if (typeof c.attempt === "string") cell.attempt = c.attempt;
  if (typeof c.hintsShown === "number") cell.hintsShown = c.hintsShown;
  if (c.verdict && typeof c.verdict.equivalent === "boolean") cell.verdict = c.verdict;
  if (c.solution) cell.solution = true;
  if (c.lean) {
    cell.lean = true;
    if (typeof c.leanStart === "string") cell.leanStart = c.leanStart;
    if (typeof c.leanSolution === "string") cell.leanSolution = c.leanSolution;
  }
}

/** Cells from a file's records (no DOM yet); `foldWork` folds every cell's work whatever was saved. */
function cellsFromFile(doc: ChalkFile, foldWork = false): Cell[] {
  return doc.cells.map((c) => {
    const cell = freshCell(c.src, c.type === "markdown" || c.type === "section" || c.type === "lean" || c.type === "exercise" ? c.type : "math");
    if (cell.type === "exercise") exerciseFromFile(cell, c);
    if (cell.type === "markdown") cell.editing = !c.src.trim();   // prose comes back rendered; an empty cell opens for typing
    if (c.collapsed) cell.collapsed = true;
    cell.showWork = !foldWork && (c.showWork ?? false); cell.label = c.label ?? null;
    // a cell to step through shows its work whatever the reader folds: the steps are the exercise
    if (typeof c.stepwise === "number" && c.stepwise >= 0) { cell.stepwise = Math.floor(c.stepwise); cell.showWork = true; }
    if (c.outLatex) cell.outLatex = c.outLatex;
    if (c.outText) cell.outText = c.outText;
    if (c.form) cell.form = c.form;
    if (c.semantics) cell.semantics = c.semantics;
    if (c.echoLatex) cell.echoLatex = c.echoLatex;
    if (c.steps) cell.steps = c.steps;
    if (c.outline && !c.steps?.length) cell.outline = c.outline;
    if (c.error) cell.error = c.error;
    if (c.plot) cell.plot = migratePlot(c.plot);
    const vs = knownVisuals(c.visuals);
    if (vs.length) { cell.visuals = vs; if (typeof c.summary === "string") cell.summary = c.summary; }
    const f = c.file;
    const o = f?.origin as { url?: unknown; asset?: unknown; derived?: unknown } | undefined;
    if (f && typeof f.name === "string" && typeof f.mime === "string" && o) {
      const origin = typeof o.url === "string" ? { url: o.url } : typeof o.asset === "string" ? { asset: o.asset } : typeof o.derived === "string" ? { derived: o.derived } : null;
      if (origin) cell.file = { name: f.name, mime: f.mime, size: Number(f.size) || 0, origin };
    }
    if (c.mode === "raw" || c.mode === "visual") cell.mode = c.mode;
    if (c.noSuggest) cell.noSuggest = true;
    const sl = c.slider;
    if (sl && [sl.min, sl.max, sl.step].every((x) => typeof x === "number" && isFinite(x)) && sl.max > sl.min && sl.step > 0) cell.slider = { min: sl.min, max: sl.max, step: sl.step };
    const ask = savedAsk(c.ask);
    if (ask) cell.ask = ask;
    return cell;
  });
}

async function runAll() {
  const d = currentDoc(); if (d) d.hydrated = true;   // every cell, in order: the session is the notebook's
  const gen = runGen;
  // switching tabs meanwhile leaves this notebook running in its own session; closing it stops it
  for (const c of [...S.cells]) { if (gen !== runGen || (d && !S.docs.includes(d))) return; if (cellSrc(c).trim()) await runCell(c); }
}

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
// --- Sliders: `let n = 3` as a control -----------------------------------------------------------
// Moving the slider rewrites the cell's number, runs it, and runs the cells below that are out of
// date because of it (and so on down: a cell they bind may make another out of date). Runs do not
// pile up behind a drag: while one is under way only the latest position waits.

/** A cell a slider can drive: `let name = number`. */
const SLIDER_SRC = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(-?\d+(?:\.\d+)?)\s*$/;
/** A first range for a number: around it, in steps of its precision. */
function defaultRange(v: number): { min: number; max: number; step: number } {
  const int = Number.isInteger(v), a = Math.abs(v);
  const max = a === 0 ? 10 : int ? Math.max(2 * a, 10) : 2 * a;
  const min = v < 0 ? -max : 0;
  return { min, max, step: int ? 1 : Number(((max - min) / 100).toPrecision(1)) };
}
function toggleSlider(cell: Cell) {
  if (cell.slider) delete cell.slider;
  else {
    const m = SLIDER_SRC.exec(cellSrc(cell)); if (!m) return;
    cell.slider = defaultRange(Number(m[2]));
    cell.mode = "raw";   // the source is rewritten as the slider moves: text, not a typeset tree
  }
  renderCells(); autosave();
}
/** A number as the slider writes it: no float noise from the step arithmetic. */
const sliderNum = (x: number, step: number) => {
  const d = Math.max(0, -Math.floor(Math.log10(step) + 1e-9));
  return Number(x.toFixed(Math.min(10, d)));
};
/** Sliders whose cell is running, and the position each waits to run next. */
const SLIDING = new WeakMap<Cell, number | null>();
async function slideTo(cell: Cell, v: number) {
  const m = SLIDER_SRC.exec(cellSrc(cell)); if (!m) return;
  cell.src = `let ${m[1]} = ${v}`;
  if (cell.input) { cell.input.value = cell.src; syncHighlight(cell); }
  if (SLIDING.has(cell)) { SLIDING.set(cell, v); return; }
  SLIDING.set(cell, null);
  try {
    for (;;) {
      await runCell(cell);
      await runOutOfDateBelow(cell);
      const next = SLIDING.get(cell);
      if (next === null || next === undefined) break;
      SLIDING.set(cell, null);
    }
  } finally { SLIDING.delete(cell); }
}
/** Run, in order, the cells below `cell` that are out of date. */
async function runOutOfDateBelow(cell: Cell) {
  const d = docOf(cell), gen = runGen;
  for (const c of S.cells.slice(S.cells.indexOf(cell) + 1)) {
    if (gen !== runGen || (d && !S.docs.includes(d))) return;
    if (staleNames(c).length) await runCell(c);
  }
}
/** The slider under a `let name = number` cell: the control, its value, and its range to edit. */
function sliderRow(cell: Cell): HTMLElement {
  const sl = cell.slider!;
  const m = SLIDER_SRC.exec(cellSrc(cell))!;
  const row = h("div", "sliderrow");
  const range = document.createElement("input");
  range.type = "range"; range.min = String(sl.min); range.max = String(sl.max); range.step = String(sl.step); range.value = m[2]!;
  range.setAttribute("aria-label", m[1]!);
  const val = h("span", "sliderval", m[2]!);
  range.addEventListener("input", () => { const v = sliderNum(Number(range.value), sl.step); val.textContent = String(v); void slideTo(cell, v); });
  range.addEventListener("focus", () => { const i = S.cells.indexOf(cell); if (S.active !== i) { S.active = i; renderChrome(); renderSidebar(); markActive(); } });
  const edit = h("span", "sliderrange");
  edit.hidden = true;
  const num = (label: string, key: "min" | "max" | "step") => {
    const l = h("label"); const inp = document.createElement("input");
    inp.type = "number"; inp.value = String(sl[key]); inp.step = "any";
    inp.addEventListener("change", () => {
      const x = Number(inp.value), next = { ...sl, [key]: x };
      if (!isFinite(x) || next.max <= next.min || next.step <= 0) { inp.value = String(sl[key]); return; }
      cell.slider = next; autosave(); renderCells();
    });
    l.append(document.createTextNode(label), inp);
    return l;
  };
  edit.append(num("from ", "min"), num("to ", "max"), num("step ", "step"));
  const gear = asButton(h("span", "sliderbtn", "range"), "Change the slider's range");
  gear.title = "Change the slider's range and step";
  gear.addEventListener("click", () => { edit.hidden = !edit.hidden; });
  row.append(h("code", "slidername", m[1]!), range, val, gear, edit);
  return row;
}

/** Run cell `i` and every cell below it, in order: what a change above leaves to do. */
async function runFrom(i: number) {
  const cells = S.cells.slice(Math.max(0, i));
  const d = currentDoc();
  const gen = runGen;
  for (const c of cells) { if (gen !== runGen || (d && !S.docs.includes(d))) return; if (cellSrc(c).trim()) await runCell(c); }
}

// --- Out of date: a cell whose names have changed since it ran -----------------------------------
// When `let x = …` gives x a new value, the cells that read x keep the answers they had: they are
// marked out of date until they run again. What a cell reads is the session's names in its source.

/** Each name a session binds (`session:name`), with how many times its value has changed and the value. */
const BIND_VER = new Map<string, { v: number; text: string }>();
/** After a cell's evaluation: the names it read and their versions; and, when it bound a name to a
 *  new value, that name's next version (the cells that read it become out of date). */
function recordRun(cell: Cell, sessionId: string, bound?: string, value?: string) {
  const own = bound ?? /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)/.exec(cell.src)?.[1];
  const read = new Map<string, number>();
  for (const t of tokenize(cell.src)) {
    const b = t.kind === "id" && t.text !== own ? BIND_VER.get(`${sessionId}:${t.text}`) : undefined;
    if (b) read.set(t.text, b.v);
  }
  cell.deps = read;
  if (!bound) { renderStale(cell); return; }
  const k = `${sessionId}:${bound}`, prev = BIND_VER.get(k);
  if (prev && prev.text === value) return;
  BIND_VER.set(k, { v: (prev?.v ?? 0) + 1, text: value ?? "" });
  if (prev) for (const c of docOf(cell)?.cells ?? []) if (c !== cell && c.deps?.has(bound)) renderStale(c);
}
/** The names a cell read whose values have changed since it ran. */
function staleNames(cell: Cell): string[] {
  const d = docOf(cell); if (!d || !cell.deps?.size) return [];
  return [...cell.deps].filter(([n, v]) => { const b = BIND_VER.get(`${d.sessionId}:${n}`); return !!b && b.v !== v; }).map(([n]) => n);
}
/** Mark a cell out of date (or not): its output dims and a bar says which names changed. */
function renderStale(cell: Cell) {
  const el = cell.el; if (!el) return;
  const names = staleNames(cell);
  el.classList.toggle("stale", names.length > 0);
  el.querySelector(".stalebar")?.remove();
  if (!names.length || S.running === cell || cell.queued) return;
  const bar = h("div", "stalebar");
  const text = h("span", "staletext", "Out of date: ");
  names.forEach((n, k) => text.append(...(k === 0 ? [] : [document.createTextNode(k === names.length - 1 ? " and " : ", ")]), h("code", undefined, n)));
  text.append(document.createTextNode(` changed since this cell ran.`));
  bar.append(h("span", "stalemark", "⟳"), text);
  const btn = (label: string, title: string, act: () => void) => {
    const b = asButton(h("span", "stalebtn", label), title); b.title = title;
    b.addEventListener("mousedown", (e) => e.preventDefault());
    b.addEventListener("click", (ev) => { ev.stopPropagation(); act(); });
    return b;
  };
  bar.append(btn("Run again", "Run this cell again", () => void runCell(cell)),
    btn("Run this and below", "Run this cell and every cell after it, in order", () => void runFrom(S.cells.indexOf(cell))));
  el.querySelector(".mid")?.append(bar);
}

/** Run every cell of the section headed by cell `i`, in order. */
async function runSection(i: number) {
  const [a, b] = sectionRange(i);
  const cells = S.cells.slice(a, b);
  log("ok", `running section “${cellSrc(S.cells[i]!) || "untitled"}”: ${cells.length} cell${cells.length === 1 ? "" : "s"}`);
  const d = currentDoc();
  const gen = runGen;
  for (const c of cells) { if (gen !== runGen || (d && !S.docs.includes(d))) return; if (cellSrc(c).trim()) await runCell(c); }
}

async function restartKernel() {
  if (S.running) {
    // a busy engine would answer the reset only after the evaluation: start a fresh one instead
    stoppedCell = S.running; runGen++;
    await connect();
    for (const d of S.docs) if (d !== currentDoc()) d.hydrated = false;
  } else if (S.kernel === "failed") await connect();
  else if (client) { try { await client.call("engine.resetSession", { sessionId }); } catch (e) { log("err", String(e)); } }
  const d = currentDoc(); if (d) d.hydrated = true;   // an empty session matches a notebook with no outputs
  clearOutputs();
  for (const k of [...USER_FNS.keys()]) if (k.startsWith(`${sessionId}:`)) USER_FNS.delete(k);
  for (const k of [...USER_NAMES]) if (k.startsWith(`${sessionId}:`)) USER_NAMES.delete(k);
  for (const k of [...BIND_VER.keys()]) if (k.startsWith(`${sessionId}:`)) BIND_VER.delete(k);
  for (const m of [FILE_VARS, FILE_OUTS, MATRIX_SHAPES]) for (const k of [...m.keys()]) if (k.startsWith(`${sessionId}:`)) m.delete(k);
  LAST_LABEL.delete(sessionId);
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
  catch { notify("err", "Could not save: this browser's storage is full or unavailable. File › Export to file keeps a copy."); return false; }
}

/** Save the current notebook in the browser under its name. */
function saveNotebook() {
  const text = serializeNotebook();
  const lib = readLibrary();
  lib[S.docName] = { file: JSON.parse(text) as ChalkFile, savedAt: new Date().toISOString() };
  if (!writeLibrary(lib)) return;
  const d = currentDoc(); if (d) d.savedText = text;
  renderTabs(); autosave();
  notify("ok", `Saved ${S.docName} in this browser`);
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
  card.setAttribute("role", "dialog"); card.setAttribute("aria-modal", "true"); card.setAttribute("aria-label", "Open a notebook");
  card.append(h("h3", undefined, "Open a notebook"));
  if (!names.length) card.append(h("p", "muted", "Nothing saved in this browser yet. File › Save keeps the current notebook here; File › Import opens a .chalk file."));
  const list = h("div", "liblist");
  for (const name of names) {
    const row = h("div", "librow");
    const when = new Date(lib[name]!.savedAt);
    const main = h("div", "main");
    main.append(h("div", "name", name), h("div", "when", `${lib[name]!.file.cells.length} cells · saved ${when.toLocaleString()}`));
    asButton(main, `Open ${name}`);
    main.addEventListener("click", () => { closeModal(); openFromLibrary(name); });
    const del = asButton(h("span", "del", "delete"), `Delete ${name} from this browser`); del.title = "Remove from this browser";
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
  mountModal(box);
  (list.querySelector<HTMLElement>("[role=button]") ?? close).focus();
}
/** Where focus was before a dialog opened; it goes back there when the dialog closes. */
let modalReturn: HTMLElement | null = null;
/** Called once when the open dialog closes, however it closes (a button, Escape, a click outside). */
let modalClosed: (() => void) | null = null;
function closeModal() {
  const done = modalClosed; modalClosed = null; done?.();
  const had = document.querySelector(".modal");
  document.querySelectorAll(".modal").forEach((m) => m.remove());
  if (had && modalReturn?.isConnected) modalReturn.focus();
  modalReturn = null;
}
/** Put a dialog on the page: Tab and Shift+Tab stay inside it. */
function mountModal(box: HTMLElement) {
  modalReturn = document.activeElement instanceof HTMLElement ? document.activeElement : null;
  box.addEventListener("keydown", (ev) => {
    if (ev.key !== "Tab") return;
    const f = [...box.querySelectorAll<HTMLElement>("button, [href], input, [tabindex]:not([tabindex='-1'])")].filter((e) => !e.hidden);
    if (!f.length) return;
    const first = f[0]!, last = f[f.length - 1]!;
    if (ev.shiftKey && document.activeElement === first) { ev.preventDefault(); last.focus(); }
    else if (!ev.shiftKey && document.activeElement === last) { ev.preventDefault(); first.focus(); }
  });
  document.body.append(box);
}

/** A dialog: a title, a body, and a Close button; Esc or a click outside closes it too. */
function showModal(title: string, body: (Node | string)[], wide = false) {
  closeModal();
  const box = h("div", "modal");
  const card = h("div", `modalcard${wide ? " wide" : ""}`);
  card.setAttribute("role", "dialog"); card.setAttribute("aria-modal", "true"); card.setAttribute("aria-label", title);
  card.append(h("h3", undefined, title), ...body);
  const foot = h("div", "modalfoot");
  const close = h("button", "primary", "Close"); close.addEventListener("click", closeModal);
  foot.append(h("div", "spacer"), close);
  card.append(foot);
  box.append(card);
  box.addEventListener("click", (ev) => { if (ev.target === box) closeModal(); });
  mountModal(box);
  close.focus();
}

/** Notebooks that ship with the page (notebooks/ in the repository, examples/ on the site). */
const EXAMPLES: { file: string; title: string; blurb: string }[] = [
  { file: "welcome.chalk", title: "Welcome to ChalkMath", blurb: "A short tour: running cells, reading the steps, and one example from each area." },
  { file: "llamas.chalk", title: "Drawing llamas with circles", blurb: "Fourier series from inner products to epicycles, ending with a llama drawn by spinning circles." },
  { file: "order-lattices.chalk", title: "Order and lattices", blurb: "Part I of From Zero to Propagators: partial orders, joins and meets, monotone maps and fixed points, with the proofs in Lean cells." },
];

/** A bundled notebook's text, by its path under examples/. */
async function fetchExample(file: string): Promise<string> {
  const res = await fetch(`examples/${file}?v=${typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev"}`);
  if (!res.ok) throw new Error(`HTTP ${res.status}`);
  return res.text();
}
/** The Lean of a course's lessons before lesson `k`, in order: their Lean cells, and their Lean exercises
 *  as statement and the author's proof (a theorem proved there may be used later), without the commands
 *  that only show something (`leanForPrelude`: Lean elaborates the prelude each time a lesson opens).
 *  Lessons that are not there are left out; what a lesson needs from them then shows as an error in its Lean. */
async function leanPreludeOf(p: Project, k: number): Promise<string> {
  const parts: string[] = [];
  for (let j = 0; j < k; j++) {
    try {
      const doc = JSON.parse(await fetchExample(lessonPath(p, j))) as ChalkFile;
      const lean = doc.cells.flatMap((c) => c.type === "lean" ? [c.src]
        : c.type === "exercise" && c.lean && c.src.trim() ? [`${c.src}\n${c.leanSolution ?? LEAN_START}`] : []);
      if (lean.length) parts.push(`-- ${p.lessons[j]!.title}\n${leanForPrelude(lean.join("\n\n"))}`);
    } catch (e) { log("err", `Lean prelude: ${lessonPath(p, j)}: ${e instanceof Error ? e.message : String(e)}`); }
  }
  return parts.join("\n\n");
}

/** Open a bundled notebook in a tab (or show it, if it is open already). `file` is its path under
 *  examples/; a lesson opens with its place in its project. */
async function openExample(file: string, project?: ProjectRef): Promise<boolean> {
  const name = file.split("/").pop()!;
  const open = S.docs.findIndex((d) => d.name === name && (!project || (d.project?.id === project.id && d.project.lesson === project.lesson)));
  if (open >= 0) { loadDoc(open); switchTab("notebook"); return true; }
  try {
    const text = await fetchExample(file);
    const p = project && projectById(project.id);
    const prelude = p?.leanPrelude ? await leanPreludeOf(p, project!.lesson) : undefined;
    await loadNotebook(text, name, project, prelude);
    if (project) recordProgress();
    return true;
  } catch (e) {
    notify("err", `Could not open ${file}: ${e instanceof Error ? e.message : String(e)}`);
    return false;
  }
}

// --- Projects: notebooks that belong together ----------------------------------------------------
// A project is a list of notebooks with a title: a course, whose lessons are read in order, or a
// collection. The page ships some (notebooks/courses.json, examples/courses.json on the site); the
// Courses tab lists them, a lesson opens with a bar that leads to the one before and after, and each
// lesson's exercises answered are remembered in this browser.

interface ProjectRef { id: string; lesson: number }
interface Project {
  id: string; title: string; blurb: string;
  /** A course is read in order (lessons numbered, previous and next); a collection is not. */
  kind: "course" | "collection";
  /** The folder of its notebooks under examples/ ("" for the top). */
  path: string;
  level?: string;
  /** Each lesson's Lean sees the Lean of the lessons before it (their cells, and their exercises proved
   *  with the author's proofs), so a course builds one development across its lessons. */
  leanPrelude?: boolean;
  lessons: { file: string; title: string; blurb: string }[];
}
/** What the page knows before courses.json arrives (or when it cannot): the example notebooks. */
let PROJECTS: Project[] = [{ id: "explorations", title: "Explorations", kind: "collection", path: "",
  blurb: "Notebooks that show what ChalkMath does: a tour, Fourier series drawing a llama, and order theory with its proofs in Lean.",
  lessons: EXAMPLES.map((e) => ({ file: e.file, title: e.title, blurb: e.blurb })) }];
const projectById = (id: string) => PROJECTS.find((p) => p.id === id);
/** A project reference from a file, if it is well formed. */
function projectRefOf(file: { project?: unknown }): ProjectRef | undefined {
  const p = file.project as { id?: unknown; lesson?: unknown } | undefined;
  return p && typeof p.id === "string" && typeof p.lesson === "number" && p.lesson >= 0 ? { id: p.id, lesson: Math.floor(p.lesson) } : undefined;
}
async function loadProjects() {
  try {
    const res = await fetch(`examples/courses.json?v=${typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev"}`);
    if (!res.ok) return;
    const j = await res.json() as { projects?: unknown };
    const ok = Array.isArray(j.projects) ? (j.projects as Project[]).filter((p) => p && typeof p.id === "string" && typeof p.title === "string"
      && Array.isArray(p.lessons) && p.lessons.every((l) => typeof l?.file === "string" && typeof l.title === "string")) : [];
    if (ok.length) PROJECTS = ok.map((p) => ({ ...p, kind: p.kind === "collection" ? "collection" : "course", path: typeof p.path === "string" ? p.path : "", blurb: String(p.blurb ?? "") }));
    if (S.tab === "courses") renderCourses();
    renderLessonBar();
  } catch { /* the built-in list stands */ }
}
const lessonPath = (p: Project, k: number) => `${p.path ? `${p.path}/` : ""}${p.lessons[k]!.file}`;
function openLesson(p: Project, k: number) { if (p.lessons[k]) void openExample(lessonPath(p, k), { id: p.id, lesson: k }); }

/** Exercises answered, by project and lesson file: `{ done, total }`, and that it was opened. */
type Progress = Record<string, Record<string, { done: number; total: number }>>;
function readProgress(): Progress {
  try { const j = JSON.parse(localStorage.getItem("chalkmath.progress") ?? "{}") as Progress; return j && typeof j === "object" ? j : {}; } catch { return {}; }
}
/** Remember the current lesson's exercises answered (and that it was opened). */
function recordProgress() {
  const d = currentDoc(), pr = d?.project, p = pr && projectById(pr.id), l = p?.lessons[pr!.lesson];
  if (!d || !pr || !l) return;
  const ex = d.cells.filter((c) => c.type === "exercise");
  const all = readProgress();
  const was = all[pr.id]?.[l.file];
  const now = { done: ex.filter((c) => c.verdict?.equivalent).length, total: ex.length };
  if (was && was.done === now.done && was.total === now.total) return;
  (all[pr.id] ??= {})[l.file] = now;
  try { localStorage.setItem("chalkmath.progress", JSON.stringify(all)); } catch { /* private mode: progress is not kept */ }
  renderLessonBar();
}
/** A lesson's state for the list: not opened, opened, partly done, or every exercise answered. */
function lessonState(p: Project, k: number, prog = readProgress()): { label: string; cls: string; frac: number } {
  const r = prog[p.id]?.[p.lessons[k]!.file];
  if (!r) return { label: "", cls: "new", frac: 0 };
  if (!r.total) return { label: "Read", cls: "seen", frac: 1 };
  if (r.done >= r.total) return { label: `✓ ${r.total} of ${r.total}`, cls: "done", frac: 1 };
  return { label: `${r.done} of ${r.total} exercises`, cls: "part", frac: r.done / r.total };
}

function openCourses(id: string | null = S.courses.project) {
  S.courses.open = true;
  S.courses.project = id && projectById(id) ? id : null;
  switchTab("courses");
}
function closeCourses() {
  S.courses.open = false;
  if (S.tab === "courses") switchTab("notebook"); else renderTabs();
}
/** The Courses tab: every project as a card, or one project's lessons. */
function renderCourses() {
  const host = $(".courses"); host.innerHTML = "";
  const page = h("div", "crspage");
  const prog = readProgress();
  const p = S.courses.project ? projectById(S.courses.project) : undefined;
  if (!p) {
    page.append(h("h1", undefined, "Courses"),
      h("p", "crslead", "Lessons that build on each other, with exercises the engine checks, and collections of notebooks to explore. Each opens in its own tab; what you change stays in this browser."));
    const grid = h("div", "crsgrid");
    for (const q of PROJECTS) {
      const card = asButton(h("div", `crscard ${q.kind}`), q.title);
      const n = q.lessons.length;
      const done = q.lessons.filter((_, k) => lessonState(q, k, prog).cls === "done" || lessonState(q, k, prog).cls === "seen").length;
      card.append(h("div", "crskind", q.kind === "course" ? `Course · ${n} lesson${n === 1 ? "" : "s"}${q.level ? ` · ${q.level}` : ""}` : `Collection · ${n} notebook${n === 1 ? "" : "s"}`),
        h("div", "crstitle", q.title), h("div", "crsblurb", q.blurb));
      if (q.kind === "course") {
        const bar = h("div", "crsbar"); const fill = h("i"); fill.style.width = `${Math.round((done / Math.max(1, n)) * 100)}%`; bar.append(fill);
        const started = q.lessons.filter((_, k) => lessonState(q, k, prog).cls !== "new").length;
        card.append(bar, h("div", "crsmeta", done ? `${done} of ${n} done` : started ? `Started: ${started} of ${n} opened` : "Not started"));
      }
      card.addEventListener("click", () => openCourses(q.id));
      grid.append(card);
    }
    page.append(grid);
  } else {
    const back = asButton(h("span", "crsback", "‹ All courses"), "All courses");
    back.addEventListener("click", () => openCourses(null));
    page.append(back, h("h1", undefined, p.title), h("p", "crslead", p.blurb));
    const list = h("ol", `crslessons ${p.kind}`);
    const next = p.kind === "course" ? p.lessons.findIndex((_, k) => !["done", "seen"].includes(lessonState(p, k, prog).cls)) : -1;
    p.lessons.forEach((l, k) => {
      const st = lessonState(p, k, prog);
      const li = h("li", `crslesson ${st.cls}${k === next ? " next" : ""}`);
      const num = h("span", "crsnum", p.kind === "course" ? String(k + 1) : "•");
      const main = h("div", "crsmain");
      main.append(h("div", "crsltitle", l.title), h("div", "crsblurb", l.blurb));
      if (st.label) main.append(h("div", "crsstate", st.label));
      const go = asButton(h("span", "crsgo", st.cls === "new" ? (k === next || p.kind === "collection" ? "Start" : "Open") : st.cls === "done" ? "Review" : "Continue"), `Open ${l.title}`);
      go.addEventListener("click", () => openLesson(p, k));
      li.append(num, main, go);
      li.addEventListener("dblclick", () => openLesson(p, k));
      list.append(li);
    });
    page.append(list);
  }
  host.append(page);
}

/** Above a lesson's cells: its course, where it is in it, its exercises, and the way on. */
function renderLessonBar() {
  const bar = document.querySelector<HTMLElement>(".lessonbar"); if (!bar) return;
  const pr = currentDoc()?.project, p = pr && projectById(pr.id), l = p?.lessons[pr!.lesson];
  bar.hidden = S.tab !== "notebook" || !p || !l;
  bar.innerHTML = "";
  if (!p || !l || bar.hidden) return;
  const k = pr!.lesson;
  const btn = (label: string, title: string, act: (() => void) | null) => {
    const b = asButton(h("span", `lbbtn${act ? "" : " off"}`, label), title); b.title = title;
    if (act) b.addEventListener("click", act); else b.setAttribute("aria-disabled", "true");
    return b;
  };
  const where = h("span", "lbwhere");
  const crs = asButton(h("span", "lbcourse", p.title), `${p.title}: all lessons`);
  crs.addEventListener("click", () => openCourses(p.id));
  where.append(crs, document.createTextNode(p.kind === "course" ? ` · Lesson ${k + 1} of ${p.lessons.length}` : ""));
  const st = lessonState(p, k);
  bar.append(where, h("span", "lbtitle", l.title), h("span", `lbstate ${st.cls}`, st.label && st.cls !== "seen" ? st.label : ""), h("span", "spacer"),
    btn("‹ Previous", k > 0 ? p.lessons[k - 1]!.title : "", k > 0 ? () => openLesson(p, k - 1) : null),
    btn("Next ›", k < p.lessons.length - 1 ? p.lessons[k + 1]!.title : "", k < p.lessons.length - 1 ? () => openLesson(p, k + 1) : null));
}

const SHORTCUTS: [string, string][] = [
  ["Enter", "Run the cell (in a Markdown cell: a new line)"],
  ["Shift+Enter in a math cell", "A new line: a cell of several lines, such as a system (Enter still runs it)"],
  ["? at the start of a cell", "Ask a question: a number, list, table or formula, looked up (Run › Lookup settings)"],
  ["Shift+Enter or Esc", "Render a Markdown cell"],
  ["Enter on rendered Markdown, or double-click", "Edit it"],
  ["↑ / ↓", "Move to the cell above or below"],
  ["Tab", "Complete a command or a \\-symbol"],
  ["\\pi, \\lam, \\e, \\theta … then space", "Type a symbol: π, λ, ℯ, θ …"],
  ["Ctrl/⌘+Shift+M", "Switch the cell between visual and text input"],
  ["\\frac, \\sqrt, \\int, \\dint, \\sum, \\diff, \\mat2x3 … then space", "Insert a fraction, root, integral, sum, derivative, matrix … (a text cell turns typeset)"],
  ["Tab (visual)", "The next empty slot"],
  ["@ (visual)", "Put the selection in parentheses with a box in front for a function's name: select, @, then type norm"],
  ["Esc", "Close a popup, the signature help, or this dialog"],
  ["Ctrl/⌘+S", "Save in this browser (with Shift: Save as)"],
  ["Ctrl/⌘+B", "Show or hide the sidebar"],
];
function showShortcuts() {
  const t = h("table", "keys");
  for (const [k, what] of SHORTCUTS) {
    const tr = h("tr");
    const kd = h("td"); kd.append(h("kbd", undefined, k));
    tr.append(kd, h("td", undefined, what));
    t.append(tr);
  }
  showModal("Keyboard shortcuts", [t]);
}

function showAbout() {
  const p = (text: string) => h("p", "muted", text);
  const links = h("p", "muted");
  const a = (href: string, text: string) => { const l = document.createElement("a"); l.href = href; l.target = "_blank"; l.rel = "noreferrer"; l.textContent = text; return l; };
  links.append(a("https://github.com/adekau/chalkmath", "Source on GitHub"), " · ", a("https://github.com/adekau/chalkmath/releases", "The book, Show Your Work (PDF)"));
  const legal = h("p", "muted");
  legal.append("Copyright 2026 Alex Dekau. Open source under the ", a("licenses/ChalkMath-LICENSE.txt", "Apache License 2.0"),
    "; the name and logo are covered by the ", a("licenses/TRADEMARKS.md", "trademark policy"), ". ", a("licenses/NOTICE.txt", "Notices and third-party licenses"), ".");
  showModal("About ChalkMath", [
    p("A notebook for mathematics that shows its work: every answer comes with the steps that produced it, and any part of an answer can be traced back to the rule that made it."),
    p("Privacy: the engine runs in your browser. What you type is not sent to a server, and notebooks are kept in this browser's storage until you export them. The page loads nothing from other sites, except what a notebook asks for: an import(\"url\") cell, or an image in a Markdown cell."),
    links,
    legal,
    p(`Build ${typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev"}${S.caps ? ` · engine ${S.caps.version}` : ""}`),
  ]);
}

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
function exportNotebook() { download(S.docName, serializeNotebook()); notify("ok", `Exported ${S.docName}`); }
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
interface LinkDoc { v: 1; n: string; c: { s: string; t?: "markdown" | "section" | "lean" | "exercise"; w?: 1; f?: 1; r?: number; p?: string; hs?: string[]; hq?: 1; sl?: [number, number, number]; ln?: 1; lst?: string; lso?: string }[]; a?: Record<string, { m: string; d: string; b?: 1 }> }

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
    c: S.cells.filter((c) => cellSrc(c).trim()).map((c) => ({ s: cellSrc(c), ...(c.type ? { t: c.type } : {}), ...(c.showWork ? { w: 1 as const } : {}), ...(c.collapsed ? { f: 1 as const } : {}), ...(c.stepwise !== undefined ? { r: c.stepwise } : {}),
      ...(c.prompt ? { p: c.prompt } : {}), ...(c.hints?.length ? { hs: c.hints } : {}), ...(c.hideQuestion ? { hq: 1 as const } : {}),
      ...(c.slider ? { sl: [c.slider.min, c.slider.max, c.slider.step] as [number, number, number] } : {}),
      ...(c.lean ? { ln: 1 as const, ...(c.leanStart ? { lst: c.leanStart } : {}), ...(c.leanSolution ? { lso: c.leanSolution } : {}) } : {}) })),
    ...(Object.keys(S.assets).length ? { a: Object.fromEntries(Object.values(S.assets).map((a) => [a.name, { m: a.mime, d: a.data, ...(a.binary ? { b: 1 as const } : {}) }])) } : {}),
  };
  const json = JSON.stringify(doc);
  const payload = typeof CompressionStream === "function" ? `nb=${b64url(await deflate(json))}` : `nbj=${b64url(new TextEncoder().encode(json))}`;
  return `${location.origin}${location.pathname}#${payload}`;
}
async function copyNotebookLink() {
  try {
    const url = await notebookLink();
    await navigator.clipboard.writeText(url);
    // chat apps and mail clients cut long links; attachments make them long
    notify("ok", url.length > 8000
      ? `Copied a link to ${S.docName}. It is ${url.length.toLocaleString()} characters long, which some apps cut short; File › Export to file is safer to send.`
      : `Copied a link to ${S.docName}`);
  } catch (e) { notify("err", `Could not copy the link: ${e instanceof Error ? e.message : String(e)}`); }
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
      cells: doc.c.map((c) => ({ src: String(c.s ?? ""), type: c.t === "markdown" || c.t === "section" || c.t === "lean" || c.t === "exercise" ? c.t : undefined, collapsed: c.f ? true : undefined, showWork: !!c.w, stepwise: typeof c.r === "number" ? c.r : undefined,
        prompt: typeof c.p === "string" ? c.p : undefined, hints: Array.isArray(c.hs) ? c.hs.map(String) : undefined, hideQuestion: c.hq ? true : undefined,
        slider: Array.isArray(c.sl) && c.sl.length === 3 ? { min: Number(c.sl[0]), max: Number(c.sl[1]), step: Number(c.sl[2]) } : undefined,
        lean: c.ln ? true : undefined, leanStart: typeof c.lst === "string" ? c.lst : undefined, leanSolution: typeof c.lso === "string" ? c.lso : undefined, label: null })),
      scenes: [],
      ...(doc.a ? { assets: Object.fromEntries(Object.entries(doc.a).map(([name, a]) => [name, { name, mime: String(a.m), data: String(a.d), ...(a.b ? { binary: true } : {}) }])) } : {}),
    };
    history.replaceState(null, "", location.pathname + location.search);
    await loadNotebook(JSON.stringify(file), file.name);
    return true;
  } catch (e) { notify("err", `The notebook link did not open: ${e instanceof Error ? e.message : String(e)}`); return false; }
}

// --- Files: `⟦name⟧` for a file attached to the notebook, `import("url")` for one on the web -------
// A file is a value of the notebook, not of the engine (files.ts): a cell whose value is one shows
// it, `let x = …` binds the name here, and the functions that turn a file into numbers are evaluated
// before the cell is sent. In a Markdown cell `⟦name⟧` shows the file the same way.

/** A file-valued cell's output: what the file is and where its contents are (saved with the cell,
 *  so a notebook not yet re-run can say what its outputs were). */
interface FileMeta { name: string; mime: string; size: number; origin: FileValue["origin"] }

/** Imports by URL, fetched once per page (a re-run does not fetch again). */
const IMPORTS = new Map<string, FileValue>();
/** The names bound in a session that start with `prefix`, for completions: what each is (a file and
 *  its type and size, a matrix's shape, a function's parameters). */
function sessionNames(sid: string, prefix: string): { name: string; what: string; call: boolean }[] {
  const out: { name: string; what: string; call: boolean }[] = [];
  const q = prefix.toLowerCase();
  for (const k of USER_NAMES) {
    if (!k.startsWith(`${sid}:`)) continue;
    const name = k.slice(sid.length + 1);
    if (!name.toLowerCase().startsWith(q)) continue;
    const file = FILE_VARS.get(k), params = USER_FNS.get(k), shape = MATRIX_SHAPES.get(k);
    const t = file && tabular(file);
    const what = file ? `${mimeLabel(file.mime)}${t ? `, ${t.rows.length} × ${t.cols}` : ""}`
      : params ? `${name}(${params.join(", ")})` : shape ? `${shape.rows}×${shape.cols} matrix` : "defined with let";
    out.push({ name, what, call: !!params });
  }
  return out.sort((a, b) => a.name.localeCompare(b.name));
}

/** The shapes of names bound to matrices, keyed `session:name`, for completions inside `name[[`. */
const MATRIX_SHAPES = new Map<string, { rows: number; cols: number }>();
/** Names bound to files by `let x = import(…)`, keyed `session:name` like `USER_NAMES`. */
const FILE_VARS = new Map<string, FileValue>();
/** Outputs that are files, keyed `session:label`, for `%` and `%n`; and each session's latest label. */
const FILE_OUTS = new Map<string, FileValue>();
const LAST_LABEL = new Map<string, number>();
/** Points sampled from an SVG, by count and text, so a re-run does not measure the paths again. */
const SVG_SAMPLES = new Map<string, { points: [number, number][]; paths: number }>();

/** An attachment as a file value. */
const assetFile = (a: Asset): FileValue => ({ name: a.name, mime: a.mime, data: a.data, ...(a.binary ? { binary: true } : {}), origin: { asset: a.name } });

/** The files a cell of a notebook may refer to: its attachments, the imports fetched, and the names
 *  and outputs of its session that are files. */
function fileScope(sid: string, assets: Record<string, Asset>): FileScope {
  return {
    lookup: (ref: FileRef) => {
      if (ref.kind === "asset") {
        const a = assets[ref.name];
        if (!a) throw new Error(`nothing named ⟦${ref.name}⟧ is attached to this notebook (File → Attach file…, or paste a file into a cell)`);
        return assetFile(a);
      }
      if (ref.kind === "url") return IMPORTS.get(ref.url);
      if (ref.kind === "name") return FILE_VARS.get(`${sid}:${ref.name}`);
      const last = LAST_LABEL.get(sid) ?? 0;
      const n = /^%\d+$/.test(ref.text) ? Number(ref.text.slice(1)) : last + 1 - ref.text.length;
      return FILE_OUTS.get(`${sid}:${n}`);
    },
    sample: (xml, n) => {
      const key = `${n}:${xml}`;
      let r = SVG_SAMPLES.get(key);
      if (!r) { r = svgPoints(xml, n); SVG_SAMPLES.set(key, r); }
      return r;
    },
  };
}

/** Fetch what a cell imports (once per URL): the media type is the server's, or the extension's
 *  when the server's says nothing (a raw file host sends CSV and SVG as text/plain). */
async function fetchImports(src: string) {
  for (const url of importsIn(src)) {
    if (IMPORTS.has(url)) continue;
    let r: Response;
    try {
      r = await fetch(url);
      if (!r.ok) throw new Error(`${r.status} ${r.statusText}`);
    } catch (e) { throw new Error(`import("${url}") failed: ${e instanceof Error ? e.message : String(e)} — the server must allow cross-origin reads; attach the file instead`); }
    const name = decodeURIComponent(new URL(url, location.href).pathname.split("/").pop() || url);
    const mime = mimeFor(name, r.headers.get("content-type") ?? "");
    IMPORTS.set(url, fileFromBytes(name, mime, new Uint8Array(await r.arrayBuffer()), { url }));
  }
}

/** The file each file-valued cell showed when it last ran (a part of a file exists nowhere else). */
const CELL_FILES = new WeakMap<Cell, FileValue>();

/** A file-valued cell's file, if this page has it: an import and a part of a file are not saved with
 *  the notebook, so until the cell runs again its output says what it was. */
function fileOf(cell: Cell): FileValue | undefined {
  const meta = cell.file; if (!meta) return undefined;
  const ran = CELL_FILES.get(cell);
  if (ran) return ran;
  if ("url" in meta.origin) return IMPORTS.get(meta.origin.url);
  if ("derived" in meta.origin) return undefined;
  const a = (docOf(cell)?.assets ?? S.assets)[meta.origin.asset];
  return a && assetFile(a);
}

/** Attach a file to the notebook under a name (made unique if another file has it) and return the name. */
function attachAsset(name: string, mime: string, data: string, binary = false): string {
  let n = name.replace(/[⟦⟧]/g, "") || "file";
  if (S.assets[n] && S.assets[n]!.data !== data) {
    const m = /^(.*?)(\.[^.]*)?$/.exec(n)!; const base = m[1] ?? n, ext = m[2] ?? "";
    let k = 2; while (S.assets[`${base}-${k}${ext}`]) k++; n = `${base}-${k}${ext}`;
  }
  S.assets[n] = { name: n, mime, data, ...(binary ? { binary: true } : {}) };
  return n;
}
/** An attachment as a URL an <img> or a link can use. */
function assetUrl(name: string): string | undefined {
  const a = S.assets[name];
  return a && dataUrl(assetFile(a));
}
/** Read a file for attaching: text for text types, base64 otherwise. */
async function readAttachment(f: File): Promise<{ mime: string; data: string; binary: boolean }> {
  const v = fileFromBytes(f.name, mimeFor(f.name, f.type), new Uint8Array(await f.arrayBuffer()), { asset: f.name });
  return { mime: v.mime, data: v.data, binary: !!v.binary };
}

/** Put text at the caret of a cell's input (replacing the selection), as if typed. */
function insertAtCaret(cell: Cell, text: string) {
  const input = cell.input; if (!input) return;
  input.setRangeText(text, input.selectionStart ?? input.value.length, input.selectionEnd ?? input.value.length, "end");
  cell.src = input.value; syncHighlight(cell); renderSidebar(); renderTabs();
}

/** How a file shows as an output, or in a Markdown cell: by what it is. `x` is what the cell calls
 *  it, for the functions the caption offers. */
function fileView(f: FileValue, x: string, form?: string, suggest?: { run(code: string): void; dismiss(): void }): { body: HTMLElement; cap: HTMLElement } {
  const kind = kindOf(f);
  const cap = h("div", "plotcap filecap");
  let what = `${f.name} · ${mimeLabel(f.mime)} · ${fmtSize(fileSize(f))}`;
  let body: HTMLElement;
  if (kind === "image") {
    body = h("div", "plotbox imgbox");
    const img = document.createElement("img"); img.src = dataUrl(f); img.alt = f.name; img.className = "outimg";
    body.append(img);
  } else if (form !== "text" && tabular(f)) {
    // a CSV, or JSON that is a list of records or of lists: rows and columns
    const t = tabular(f)!;
    what = `${f.name} · ${mimeLabel(f.mime)} · ${t.rows.length.toLocaleString()} row${t.rows.length === 1 ? "" : "s"} × ${t.cols} column${t.cols === 1 ? "" : "s"}${t.header ? "" : " (no header row)"} · ${fmtSize(fileSize(f))}`;
    body = dataGrid({ rows: t.rows.length, cols: t.cols, header: t.header, cell: (r, c) => t.rows[r]![c]!, numeric: numericColumns(t), label: `${f.name}, a table` });
  } else if (kind === "binary") {
    body = h("div", "filecard");
    body.append(h("span", "fileicon", "⎙"), h("span", "filename", f.name), h("span", "filemeta", `${mimeLabel(f.mime)}, ${fmtSize(fileSize(f))}`));
  } else {
    // text, shown as it is (JSON indented); a long file shows its start
    let text = fileText(f);
    if (kind === "json") { try { text = JSON.stringify(JSON.parse(text), null, 2); } catch { /* shown as it came */ } }
    const MAX = 20000;
    body = h("pre", "filetext", text.length > MAX ? `${text.slice(0, MAX)}\n…` : text);
    if (text.length > MAX) what += ` · the first ${fmtSize(MAX)} shown`;
  }
  if (kind !== "binary") cap.append(h("span", "epinote", what));   // a card says it already
  // Mathematica's suggestions bar: what can be done with the file, each a short label that adds the
  // code (its tooltip) as a cell below and runs it; × hides the bar for this cell
  const helpers = suggest ? helpersFor(f, x) : [];
  if (helpers.length) {
    const bar = h("div", "trybar");
    bar.setAttribute("role", "toolbar"); bar.setAttribute("aria-label", "Suggestions");
    for (const { label, code } of helpers) {
      const chip = asButton(h("span", "trychip", label), `${label}: ${code}`);
      chip.title = code;
      chip.addEventListener("mousedown", (e) => e.preventDefault());
      chip.addEventListener("click", () => suggest!.run(code));
      bar.append(chip);
    }
    const x2 = asButton(h("span", "tryx", "×"), "Hide suggestions for this cell");
    x2.title = "Hide suggestions for this cell (View › Suggestions bar hides them everywhere)";
    x2.addEventListener("click", () => suggest!.dismiss());
    bar.append(x2);
    cap.append(bar);
  }
  return { body, cap };
}

/** A file-valued cell whose file shows as a table, which can also be shown as its text. */
const tabularCell = (cell: Cell) => { const f = fileOf(cell); return !!f && !!tabular(f); };
/** A file as rows and columns, when it is one: a CSV or TSV, or JSON that is a list of records or of lists. */
function tabular(f: FileValue): Table | null {
  try {
    const kind = kindOf(f);
    return kind === "table" ? tableOf(f) : kind === "json" ? jsonTable(jsonOf(f)) : null;
  } catch { return null; }
}

/** File → Attach file…: the file joins the notebook and `⟦name⟧` lands at the caret of the active
 *  cell — a math cell's input, or a Markdown cell's editor (where the file shows); with neither, a
 *  fresh cell `⟦name⟧`, which shows the file when run. */
function attachFile() {
  const inp = document.createElement("input");
  inp.type = "file";
  inp.addEventListener("change", () => {
    const f = inp.files?.[0]; if (!f) return;
    void readAttachment(f).then(({ mime, data, binary }) => {
      const name = attachAsset(f.name, mime, data, binary);
      const c = S.cells[S.active];
      if (c?.input && !c.type) { insertAtCaret(c, `⟦${name}⟧`); c.input.focus(); }
      // a file reference is not something the visual input shows: the cell goes back to text
      else if (c?.mi) { c.mi.apply((e) => e.insert({ k: "asset", name })); c.mi.focus(); }
      else if (c?.ta) { c.ta.setRangeText(`⟦${name}⟧`, c.ta.selectionStart, c.ta.selectionEnd, "end"); c.src = c.ta.value; c.ta.focus(); }
      else { const cell = addCell(`⟦${name}⟧`); renderSidebar(); focusCell(S.cells.indexOf(cell)); }
      notify("ok", `Attached ${name} (${Math.round(data.length / 1024)} KB): ⟦${name}⟧ refers to it`);
      renderHighlights(); autosave();
    });
  });
  inp.click();
}

/** A paste into a cell: a file (an image, say) or SVG text becomes an attachment and its `⟦name⟧`
 *  goes in at the caret; anything else pastes as text. Works in math cells and Markdown editors. */
function onPaste(ev: ClipboardEvent, cell: Cell) {
  const dt = ev.clipboardData; if (!dt) return;
  const put = (name: string) => {
    if (cell.input) insertAtCaret(cell, `⟦${name}⟧`);
    // the visual input shows the file as a chip, where the caret is
    else if (cell.mi) cell.mi.apply((e) => e.insert({ k: "asset", name }));
    else if (cell.ta) { cell.ta.setRangeText(`⟦${name}⟧`, cell.ta.selectionStart, cell.ta.selectionEnd, "end"); cell.src = cell.ta.value; cell.ta.dispatchEvent(new Event("input")); }
    renderHighlights(); autosave();
  };
  const file = Array.from(dt.files)[0];
  if (file) {
    ev.preventDefault();
    void readAttachment(file).then(({ mime, data, binary }) => {
      let k = 1; const ext = file.name ? "" : `.${(mime.split("/")[1] ?? "bin").replace("svg+xml", "svg")}`;
      while (!file.name && S.assets[`pasted-${k}${ext}`]) k++;
      const name = attachAsset(file.name || `pasted-${k}${ext}`, mime, data, binary);
      put(name); notify("ok", `Pasted ${name}: ⟦${name}⟧ refers to it`);
    });
    return;
  }
  const text = dt.getData("text/plain");
  if (cell.input instanceof HTMLInputElement && text.includes("\n") && !/<svg[\s>]/i.test(text)) {
    // several lines into a one-line input: it becomes a textarea, the lines kept
    ev.preventDefault();
    const input = cell.input, a = input.selectionStart ?? input.value.length, b = input.selectionEnd ?? a;
    const t = text.replace(/\r\n?/g, "\n");
    cell.src = input.value.slice(0, a) + t + input.value.slice(b);
    refreshInput(cell);
    cell.input?.focus(); cell.input?.setSelectionRange(a + t.length, a + t.length);
    renderSidebar(); autosave();
    return;
  }
  if (/^\s*(<\?xml[^>]*>\s*)?(<!--[\s\S]*?-->\s*)*(<!DOCTYPE[^>]*>\s*)?<svg[\s>]/i.test(text)) {
    ev.preventDefault();
    let k = 1; while (S.assets[`pasted-${k}.svg`]) k++;
    const name = attachAsset(`pasted-${k}.svg`, "image/svg+xml", text);
    put(name); notify("ok", `Pasted the SVG as ${name}: ⟦${name}⟧ refers to it`);
  }
}
function newNotebook() {
  newDoc(); switchTab("notebook");
  autosave();
  log("ok", "new notebook");
}

/** What the browser keeps between reloads: every open notebook, which one is current, and whether
 *  each had unsaved changes. */
interface Autosave { chalkmath: 1; active: number; docs: { file: ChalkFile; dirty: boolean }[] }

/** The notebooks survive a reload: autosaved to the browser after every run or edit — coalesced,
 *  since serializing every open notebook after each of a hundred cells is most of what makes a
 *  big notebook feel slow while it loads. The pending save is flushed before the page unloads. */
let autosaveTimer = 0;
let autosaveWarned = false;
function autosave() {
  clearTimeout(autosaveTimer);
  autosaveTimer = window.setTimeout(autosaveNow, 700);
}
function autosaveNow() {
  clearTimeout(autosaveTimer); autosaveTimer = 0;
  stashDoc();
  const doc: Autosave = { chalkmath: 1, active: S.doc, docs: S.docs.map((d) => ({ file: JSON.parse(d.text) as ChalkFile, dirty: docDirty(d) })) };
  try { localStorage.setItem("chalkmath.autosave", JSON.stringify(doc)); autosaveWarned = false; }
  catch {
    // storage full (big attachments) or unavailable (private mode): say so once, not after every run
    if (!autosaveWarned) notify("err", "Your notebooks could not be kept in this browser (its storage is full or unavailable). File › Export to file keeps a copy.");
    autosaveWarned = true;
  }
}
window.addEventListener("beforeunload", () => { if (autosaveTimer) autosaveNow(); });
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
  if (type === "lean") cell.type = "lean";
  if (type === "exercise") { cell.type = "exercise"; cell.editing = true; }
  return cell;
}
function addCell(src = "", type: CellType = "math"): Cell {
  const cell: Cell = freshCell(src, type);
  S.cells.push(cell);
  renderCells();
  return cell;
}
/** Insert a fresh cell at `at` and put the caret in it. */
function insertCell(at: number, type: CellType = "math", lean = false) {
  const c = freshCell("", type);
  if (lean && type === "exercise") c.lean = true;
  S.cells.splice(at, 0, c);
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
  if (type !== "math") { delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.error; delete cell.plot; delete cell.manip; delete cell.hasse; delete cell.summary; delete cell.visuals; delete cell.ask; delete cell.askTrail; cell.steps = []; delete cell.outline; cell.label = null; }
  if (type === "section") cell.src = cell.src.split("\n")[0]!.replace(/^#+\s*/, "");
  if (type !== "lean") delete cell.leanMessages;
  if (type === "exercise") cell.editing = true;
  else { delete cell.prompt; delete cell.hints; delete cell.hideQuestion; delete cell.attempt; delete cell.hintsShown; delete cell.verdict; delete cell.solution; }
  if (cur === "exercise" && type === "math") { delete cell.stepwise; cell.showWork = false; }
  renderCells(); renderSidebar(); renderChrome(); autosave();
}

// The per-cell actions, shared by the cell's ⋮ menu and the toolbar (which acts on the active cell).
function duplicateCell(cell: Cell) {
  const i = S.cells.indexOf(cell); if (i < 0) return;
  S.cells.splice(i + 1, 0, freshCell(cellSrc(cell), cell.type ?? "math"));
  renderCells(); renderSidebar(); focusCell(i + 1); autosave();
}
function moveCell(cell: Cell, by: -1 | 1) {
  const i = S.cells.indexOf(cell), j = i + by;
  if (i < 0 || j < 0 || j >= S.cells.length) return;
  [S.cells[i], S.cells[j]] = [S.cells[j]!, S.cells[i]!];
  renderCells(); renderSidebar(); focusCell(j); autosave();
}
const hasOutput = (cell: Cell) => !!(cell.outLatex || cell.file || cell.error);
function clearCellOutput(cell: Cell) {
  delete cell.outLatex; delete cell.outText; delete cell.echoLatex; delete cell.error; delete cell.plot; delete cell.manip; delete cell.hasse; delete cell.summary; delete cell.visuals; delete cell.file; delete cell.outDeBruijn; delete cell.reading;
  delete cell.ask; delete cell.askTrail;
  cell.steps = []; delete cell.outline; cell.label = null;
  renderCellBody(cell); renderChrome(); renderSidebar(); autosave();
}
function deleteCell(cell: Cell) {
  const i = S.cells.indexOf(cell); if (i < 0) return;
  if (S.cells.length === 1) { cell.src = ""; if (cell.input) { cell.input.value = ""; syncHighlight(cell); } if (cell.ta) cell.ta.value = ""; if (cell.mi) renderCells(); clearCellOutput(cell); return; }
  S.cells.splice(i, 1);
  S.active = Math.min(S.active, S.cells.length - 1);
  renderCells(); renderSidebar(); renderChrome(); autosave();
}
/** Show or hide every cell's work at once. */
function setAllWork(on: boolean) {
  for (const c of S.cells) if (workCount(c)) c.showWork = on;
  renderCells(); autosave();
}

function focusCell(i: number) {
  S.active = Math.max(0, Math.min(i, S.cells.length - 1));
  renderCells(); renderSidebar(); renderChrome();
  const c = S.cells[S.active];
  // after the render: it rebuilds the inputs, and focus on the old one is lost
  if (c?.mi) c.mi.focus();
  else if (c?.type === "lean") focusLean(c.id);
  else if (c?.type === "exercise" && c.lean && !c.editing) focusLean(c.id);
  else if (c?.type === "exercise") c.el?.querySelector<HTMLElement>(".xc-edit textarea, .xc-in")?.focus();
  else (c?.input ?? c?.ta ?? c?.el?.querySelector<HTMLElement>(".mdout"))?.focus();
}

function clearOutputs() {
  for (const c of S.cells) { delete c.outLatex; delete c.outText; delete c.echoLatex; delete c.error; delete c.plot; delete c.manip; delete c.file; c.steps = []; delete c.outline; c.label = null; c.ms = undefined; }
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

/** Make a clickable element a keyboard-operable button: focusable, announced as a button, and
 *  activated by Enter or Space like a <button>. */
function asButton<T extends HTMLElement>(el: T, label?: string): T {
  el.setAttribute("role", "button"); el.tabIndex = 0;
  if (label) el.setAttribute("aria-label", label);
  el.addEventListener("keydown", (ev) => { if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); ev.stopPropagation(); el.click(); } });
  return el;
}

/** Arrow keys, Home and End move between a menu's items; Esc calls `onEscape`. */
function menuKeys(menu: HTMLElement, onEscape: () => void, onSide?: (dir: -1 | 1) => void) {
  menu.setAttribute("role", "menu");
  const items = () => [...menu.querySelectorAll<HTMLElement>(":scope > .item")];
  for (const it of items()) { it.setAttribute("role", "menuitem"); it.tabIndex = -1; }
  menu.addEventListener("keydown", (ev) => {
    const all = items(), i = all.indexOf(document.activeElement as HTMLElement);
    const go = (j: number) => { ev.preventDefault(); ev.stopPropagation(); all[(j + all.length) % all.length]?.focus(); };
    if (ev.key === "ArrowDown") go(i + 1);
    else if (ev.key === "ArrowUp") go(i - 1);
    else if (ev.key === "Home") go(0);
    else if (ev.key === "End") go(all.length - 1);
    else if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); ev.stopPropagation(); (document.activeElement as HTMLElement | null)?.click(); }
    else if (ev.key === "Escape") { ev.preventDefault(); ev.stopPropagation(); onEscape(); }
    else if (onSide && (ev.key === "ArrowLeft" || ev.key === "ArrowRight")) { ev.preventDefault(); ev.stopPropagation(); onSide(ev.key === "ArrowLeft" ? -1 : 1); }
  });
}

/** Say something to a screen reader without showing it (a result arriving, an error). */
function announce(text: string) {
  let live = document.getElementById("sr-live");
  if (!live) { live = h("div", "sr-only"); live.id = "sr-live"; live.setAttribute("role", "status"); live.setAttribute("aria-live", "polite"); document.body.append(live); }
  live.textContent = "";
  requestAnimationFrame(() => { live!.textContent = text; });
}
const reducedMotion = () => window.matchMedia("(prefers-reduced-motion: reduce)").matches;

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
    (() => { const t = h("header", "titlebar"); return t; })(),
    (() => { const t = h("nav", "tabbar"); t.setAttribute("aria-label", "Notebooks"); return t; })(),
    (() => {
      const body = h("div", "body");
      const rail = h("nav", "rail"); rail.setAttribute("aria-label", "Sidebar views");
      const side = h("aside", "sidebar"); side.setAttribute("aria-label", "Sidebar");
      body.append(rail, side, (() => {
        const main = h("div", "main"); main.setAttribute("role", "main");
        main.append(h("div", "toolbar"), h("div", "lessonbar"), h("div", "notice"), h("div", "cells"), h("div", "docs"), h("div", "courses"), h("div", "studio"), h("div", "panel"));
        return main;
      })());
      return body;
    })(),
    h("footer", "statusbar"),
  );
}

const $ = <T extends HTMLElement>(sel: string) => app().querySelector(sel) as T;

function renderChrome() {
  // title bar
  const tb = $(".titlebar"); tb.innerHTML = "";
  const brand = h("div", "brand");
  const mark = document.createElement("img"); mark.className = "mark"; mark.src = "logo.svg"; mark.alt = ""; mark.draggable = false;
  brand.append(mark, h("h1", "name", "ChalkMath"));
  const menus = h("div", "menus");
  const MENUS: Record<string, [string, () => void][]> = {
    File: [["New notebook", newNotebook], ["Open…", openNotebook], ["Courses and examples…", () => openCourses()], ["Save", () => saveNotebook()], ["Save as…", saveNotebookAs], ["Export to file…", exportNotebook], ["Import from file…", importNotebook], ["Attach file…", attachFile], ["Copy link to notebook", () => void copyNotebookLink()]],
    Edit: [["Add math cell", () => { addCell(); focusCell(S.cells.length - 1); }], ["Add Markdown cell", () => { addCell("", "markdown"); focusCell(S.cells.length - 1); }], ["Add section", () => { addCell("", "section"); focusCell(S.cells.length - 1); }], ["Add Lean cell", () => { addCell("", "lean"); focusCell(S.cells.length - 1); }], ["Add exercise", () => { addCell("", "exercise"); focusCell(S.cells.length - 1); }], ["Add Lean exercise", () => { insertCell(S.cells.length, "exercise", true); }],
      ...(S.cells[S.active] ? CELL_TYPES.filter(([t]) => t !== (S.cells[S.active]!.type ?? "math")).map(([t, label]): [string, () => void] => [`Change to ${label.toLowerCase()}`, () => convertCell(S.cells[S.active]!, t)]) : []),
      ["Clear outputs", clearOutputs]],
    View: [["Toggle light / dark", () => { applyTheme(S.theme === "light" ? "dark" : "light"); renderChrome(); }], [`${S.sidebarOpen ? "✓ " : ""}Sidebar  (Ctrl+B)`, toggleSidebar], ["Explanation panel", () => setPanelOpen(!S.panelOpen)],
      ["Show all work", () => setAllWork(true)], ["Hide all work", () => setAllWork(false)],
      [`${S.foldWorkOnOpen ? "✓ " : ""}Hide work in opened notebooks`, () => { S.foldWorkOnOpen = !S.foldWorkOnOpen; setPref("chalkmath.foldwork", S.foldWorkOnOpen); renderChrome(); }], [`${S.deBruijn ? "✓ " : ""}de Bruijn indices (λ-cells)`, () => { S.deBruijn = !S.deBruijn; renderChrome(); renderCells(); }],
      ...(["auto", "visual", "raw"] as const).map((m): [string, () => void] => [`${S.inputMode === m ? "✓ " : "   "}Math input: ${{ auto: "automatic", visual: "typeset", raw: "text" }[m]}`, () => {
        S.inputMode = m;
        try { localStorage.setItem("chalkmath.inputmode", m); } catch { /* private mode */ }
        for (const c of S.cells) delete c.autoFor;
        renderChrome(); renderCells();
      }]),
      [`${S.keypad ? "✓ " : ""}Math keypad`, () => { S.keypad = !S.keypad; setPref("chalkmath.keypad", S.keypad); renderChrome(); updateKeypad(); }],
      [`${S.suggestions ? "✓ " : ""}Suggestions bar`, () => { S.suggestions = !S.suggestions; setPref("chalkmath.suggestions", S.suggestions); renderChrome(); renderCells(); }],
      [`${S.showEcho ? "✓ " : ""}Input interpretation`, () => { S.showEcho = !S.showEcho; try { localStorage.setItem("chalkmath.echo", S.showEcho ? "on" : "off"); } catch { /* private mode */ } renderChrome(); renderCells(); }],
      [`${S.highlight ? "✓ " : ""}Syntax highlighting`, () => { S.highlight = !S.highlight; try { localStorage.setItem("chalkmath.highlight", S.highlight ? "on" : "off"); } catch { /* private mode */ } document.documentElement.classList.toggle("nohl", !S.highlight); renderHighlights(); renderChrome(); }],
      [`${S.sigHelp ? "✓ " : ""}Signature help`, () => { S.sigHelp = !S.sigHelp; try { localStorage.setItem("chalkmath.sighelp", S.sigHelp ? "on" : "off"); } catch { /* private mode */ } if (!S.sigHelp) hideSigHelp(); renderChrome(); }],
      ...(["s", "m", "l"] as const).map((sz): [string, () => void] => [`${S.outSize === sz ? "✓ " : "   "}Math size: ${{ s: "small", m: "normal", l: "large" }[sz]}`, () => {
        S.outSize = sz; document.documentElement.dataset["outsize"] = sz;
        try { localStorage.setItem("chalkmath.outsize", sz); } catch { /* private mode */ }
        renderChrome();
      }])],
    Run: [["Run all", () => void runAll()], ["Run cell", () => { const c = S.cells[S.active]; if (c) void runCell(c); }],
      ["Run this cell and below", () => void runFrom(S.active)],
      ...(sectionOf(S.active) >= 0 ? [[`Run section “${(cellSrc(S.cells[sectionOf(S.active)]!) || "untitled").slice(0, 24)}”`, () => void runSection(sectionOf(S.active))] as [string, () => void]] : []),
      [`${S.runOnOpen ? "✓ " : ""}Run notebooks when opened`, () => { S.runOnOpen = !S.runOnOpen; setPref("chalkmath.runonopen", S.runOnOpen); renderChrome(); }],
      ["Lookup settings…", () => void showAskSettings()]],
    Kernel: [...(S.running ? [["Interrupt", () => void interrupt()] as [string, () => void]] : []),
      ["Restart kernel", () => void restartKernel()], ["Restart and run all", async () => { await restartKernel(); await runAll(); }]],
    Help: [["Documentation", () => openDocs()], ["Welcome notebook", () => void openExample("welcome.chalk")], ["Courses…", () => openCourses()], ["Keyboard shortcuts", showShortcuts],
      ["Manim Studio", () => switchTab("studio")], ["About ChalkMath", showAbout],
      [`${S.dev ? "✓ " : ""}Developer mode`, () => { S.dev = !S.dev; setPref("chalkmath.dev", S.dev); if (!S.dev && S.panelTab === "log") S.panelTab = "explain"; renderChrome(); renderPanelHead(); renderPanel(); }]],
  };
  const names = Object.keys(MENUS);
  const openMenu = (m: string | null, kb: boolean) => {
    S.menu = m; renderChrome();
    // opened from the keyboard: focus goes into the menu; closed: back to its title
    if (m && kb) $<HTMLElement>(".menus .dropdown .item")?.focus();
  };
  for (const m of names) {
    // the title and its dropdown are siblings: a menu may not sit inside a button
    const wrap = h("div", "mwrap");
    const sp = h("span", S.menu === m ? "open" : undefined, m);
    wrap.append(sp);
    asButton(sp); sp.setAttribute("aria-haspopup", "menu"); sp.setAttribute("aria-expanded", String(S.menu === m)); sp.dataset["menu"] = m;
    // a click from the keyboard has detail 0
    sp.addEventListener("click", (ev) => { ev.stopPropagation(); openMenu(S.menu === m ? null : m, ev.detail === 0); });
    sp.addEventListener("keydown", (ev) => { if (ev.key === "ArrowDown") { ev.preventDefault(); openMenu(m, true); } });
    if (S.menu === m) {
      const dd = h("div", "dropdown");
      for (const [label, act] of MENUS[m]!) {
        const it = h("div", "item", label);
        it.addEventListener("click", (ev) => { ev.stopPropagation(); S.menu = null; renderChrome(); act(); });
        dd.append(it);
      }
      menuKeys(dd, () => { openMenu(null, false); $<HTMLElement>(`.menus [data-menu="${m}"]`)?.focus(); },
        (dir) => openMenu(names[(names.indexOf(m) + dir + names.length) % names.length]!, true));
      wrap.append(dd);
    }
    menus.append(wrap);
  }
  const theme = asButton(h("span", "themebtn", S.theme === "light" ? "◑ Light" : "◐ Dark"), `Theme: ${S.theme}. Switch to ${S.theme === "light" ? "dark" : "light"}`);
  theme.title = "Toggle light and dark";
  theme.addEventListener("click", () => { applyTheme(S.theme === "light" ? "dark" : "light"); renderChrome(); if (S.tab === "studio") renderStage(); });
  const kernel = h("div", "kernel");
  const dot = h("span", "dot");
  const state = S.kernel === "failed" ? "stopped" : S.kernel === "starting" ? "starting…" : S.busy ? "running" : "ready";
  dot.style.background = S.kernel === "failed" ? "var(--danger)" : S.kernel === "starting" || S.busy ? "var(--acc)" : "var(--ok)";
  kernel.title = S.kernel === "failed" ? S.kernelError : S.kernel === "starting" ? "Loading the engine" : S.caps ? `${S.caps.engine} ${S.caps.version}` : "";
  const sel = document.createElement("select");
  for (const [v, label] of [["lean-worker", "kernel · wasm"], ["http", "kernel · http"]] as const) {
    const o = document.createElement("option"); o.value = v; o.textContent = label; o.selected = S.engineMode === v; sel.append(o);
  }
  sel.addEventListener("change", () => { S.engineMode = sel.value as typeof S.engineMode; void connect(); });
  const url = document.createElement("input");
  url.id = "kurl"; url.value = S.httpUrl; url.hidden = S.engineMode !== "http";
  url.addEventListener("change", () => { S.httpUrl = url.value; void connect(); });
  if (S.dev) kernel.append(dot, sel, url, h("span", "sep", "·"), h("span", undefined, state));
  else kernel.append(dot, h("span", undefined, `engine · ${state}`));
  tb.append(brand, menus, h("div", "spacer"), theme, kernel);

  // tab bar
  renderTabs();

  // rail
  const rail = $(".rail"); rail.innerHTML = "";
  for (const [key, glyph, title] of [["outline", "≡", "Outline"], ["palette", "ƒ", "Commands"]] as const) {
    const on = S.sidebarOpen && S.rail === key;
    const b = asButton(h("div", `b${on ? " on" : ""}`, glyph), title);
    b.setAttribute("aria-pressed", String(on));
    b.title = on ? `${title} (click again to hide the sidebar)` : title;
    // the open view's button folds the sidebar away; any other button opens it on that view
    b.addEventListener("click", () => { if (on) toggleSidebar(); else { S.rail = key; if (!S.sidebarOpen) toggleSidebar(); else { renderChrome(); renderSidebar(); } } });
    rail.append(b);
  }
  // the documentation has its own contents: the notebook's outline and commands step aside
  rail.hidden = S.tab === "docs";
  $(".sidebar").hidden = !S.sidebarOpen || S.tab === "docs";

  // toolbar
  const tl = $(".toolbar"); tl.innerHTML = "";
  const group = h("div", "bgroup");
  const mk = (label: string, title: string, fn: () => void, primary = false, enabled = true) => {
    const b = document.createElement("button");
    b.className = primary ? "primary" : ""; b.textContent = label; b.title = title; b.disabled = !enabled;
    b.addEventListener("mousedown", (e) => e.preventDefault());   // keep the caret in the cell
    b.addEventListener("click", fn); return b;
  };
  group.append(
    S.running
      ? mk("■ Stop", "Stop the evaluation (restarts the engine)", () => void interrupt(), true)
      : mk("▶ Run", "Run the active cell", () => { const c = S.cells[S.active]; if (c) void runCell(c); }, true),
    mk("▶▶ All", "Run every cell in order", () => void runAll()),
    mk("Clear all", "Clear every cell's output", clearOutputs),
    mk("+ Cell", "Add a cell", () => { const c = addCell(); focusCell(S.cells.indexOf(c)); }),
  );
  // the active cell's actions, the same as its ⋮ menu
  const cur = S.cells[S.active];
  const i = cur ? S.active : -1;
  const cellGroup = h("div", "bgroup");
  cellGroup.append(
    mk("↑", "Move the cell up", () => { if (cur) moveCell(cur, -1); }, false, i > 0),
    mk("↓", "Move the cell down", () => { if (cur) moveCell(cur, 1); }, false, i >= 0 && i < S.cells.length - 1),
    mk("Duplicate", "Duplicate the cell", () => { if (cur) duplicateCell(cur); }, false, !!cur),
    ...(cur && workCount(cur) && cur.stepwise === undefined && cur.type !== "exercise" ? [mk(cur.showWork ? "Hide work" : "Show work", "Show or hide the cell's steps", () => { cur.showWork = !cur.showWork; renderCellBody(cur); renderChrome(); autosave(); })] : []),
    mk("Clear output", "Clear the cell's output", () => { if (cur) clearCellOutput(cur); }, false, !!cur && hasOutput(cur)),
    mk("Delete", "Delete the cell", () => { if (cur) deleteCell(cur); }, false, !!cur),
  );
  tl.append(group, h("span", "tlabel", "Cell"), cellGroup, h("div", "spacer"), h("span", "hint", "Enter runs the cell"));

  renderNotice();

  // status bar
  const sb = $(".statusbar"); sb.innerHTML = "";
  const rules = new Set(S.cells.flatMap((c): { rule: string }[] => c.steps?.length ? c.steps : c.outline ?? []).map((s) => s.rule));
  const done = S.cells.filter((c) => c.outLatex || c.file || c.error).length;
  sb.append(
    ...(S.dev ? [h("span", undefined, `Mode: ${S.tab}`), h("span", "pipe", "|")] : []),
    h("span", undefined, `Cell ${S.active + 1}`), h("span", "pipe", "|"),
    h("span", undefined, `${S.cells.length} cells · ${done} evaluated`),
    h("div", "spacer"),
    ...(S.dev ? [h("span", "rules", `${rules.size} rules applied`), h("span", "pipe", "|")] : []),
    h("span", undefined, "type \\ for symbols · Tab completes"),
  );
}

/** The strip above the paper: the engine loading or failed, or a notebook shown with the outputs
 *  it was saved with and not run yet. */
function renderNotice() {
  const n = $(".notice"); n.innerHTML = ""; n.className = "notice";
  const d = currentDoc();
  const btn = (label: string, fn: () => void) => { const b = document.createElement("button"); b.textContent = label; b.addEventListener("click", fn); return b; };
  if (S.kernel === "failed") {
    n.classList.add("bad");
    const msg = h("span", "msg", S.kernelError); msg.title = S.kernelDetail;
    n.append(msg, btn("Restart engine", () => void restartEngine(S.crashed)));
  } else if (S.kernel === "starting") {
    n.classList.add("wait");
    n.append(h("span", "msg", "Starting the engine…"));
  } else if (d && !d.hydrated && !d.noticeDismissed && S.cells.some((c) => ((c.type ?? "math") === "math" || c.type === "exercise") && c.src.trim())) {
    const saved = S.cells.some((c) => c.outLatex || c.file || c.error);
    n.append(h("span", "msg", `This notebook has not been run yet.${saved ? " The outputs shown are the ones it was saved with." : ""}`),
      btn("Run all", () => void runAll().then(() => renderChrome())),
      btn("Dismiss", () => { d.noticeDismissed = true; renderNotice(); }));
  }
  n.hidden = !n.childElementCount || S.tab !== "notebook";
}

function toggleSidebar() {
  S.sidebarOpen = !S.sidebarOpen;
  if (!narrow()) setPref("chalkmath.sidebar", S.sidebarOpen);   // on a phone it is a drawer: not a preference
  renderChrome(); renderSidebar();
}

function renderView() {
  $(".cells").hidden = S.tab !== "notebook";
  renderNotice();
  $(".toolbar").hidden = S.tab !== "notebook";
  $(".docs").hidden = S.tab !== "docs";
  $(".courses").hidden = S.tab !== "courses";
  $(".studio").hidden = S.tab !== "studio";
  $(".panel").hidden = S.tab !== "notebook";
  renderLessonBar();
  if (S.tab === "docs") renderDocs();
  if (S.tab === "courses") renderCourses();
  if (S.tab === "studio") renderStudio();
}

/** The outline lists every cell (`all`), or the sections with only the current one's cells. */
let outlineAll = prefOn("chalkmath.outlineall", false);
/** The section the reader is in: the one heading the first cell on screen (−1 above the first). */
let viewSection = -1;
/** Follow the scroll: the section in view is the outline's current one. */
function trackViewSection() {
  const host = $(".cells");
  let queued = false;
  host.addEventListener("scroll", () => {
    if (queued) return;
    queued = true;
    requestAnimationFrame(() => {
      queued = false;
      const top = host.getBoundingClientRect().top + 8;
      const k = S.cells.findIndex((c) => c.el && c.el.getBoundingClientRect().bottom > top);
      const sec = k < 0 ? -1 : sectionOf(k);
      if (sec !== viewSection) { viewSection = sec; if (S.rail === "outline") renderSidebar(); }
    });
  }, { passive: true });
}
/** A section's exercises: how many there are and how many the reader has answered right. */
function sectionProgress(i: number): { done: number; total: number } {
  const [a, b] = sectionRange(i);
  const ex = S.cells.slice(a, b).filter((c) => c.type === "exercise");
  return { done: ex.filter((c) => c.verdict?.equivalent).length, total: ex.length };
}

function renderSidebar() {
  const side = $(".sidebar"); side.innerHTML = "";
  const head = h("h2", undefined, S.rail === "outline" ? "Notebook outline" : "Engine commands");
  const hasSections = S.cells.some((c) => c.type === "section");
  if (S.rail === "outline" && hasSections) {
    const t = asButton(h("span", "oltoggle", outlineAll ? "Sections" : "Every cell"), outlineAll ? "List the sections only" : "List every cell");
    t.title = outlineAll ? "List the sections, with the cells of the one you are in" : "List every cell of every section";
    t.addEventListener("click", () => { outlineAll = !outlineAll; setPref("chalkmath.outlineall", outlineAll); renderSidebar(); });
    head.append(t);
  }
  side.append(head);
  const list = h("div", "list");
  if (S.rail === "outline") {
    let inSection = false, folded = false, here = false, number = 0;
    // the current section: the one in view, or the active cell's when nothing has scrolled yet
    const cur = viewSection >= 0 || !S.cells[S.active] ? viewSection : sectionOf(S.active);
    S.cells.forEach((c, i) => {
      if (c.type === "section") { inSection = true; folded = !!c.collapsed; here = i === cur; number++; }
      else if (folded) return;
      else if (inSection && !outlineAll && !here && hasSections) return;
      const row = asButton(h("div", `olrow${i === S.active ? " on" : ""}${c.type ? ` ${c.type}` : ""}${inSection && c.type !== "section" ? " in" : ""}`));
      if (c.type === "section") {
        const [a, b] = sectionRange(i);
        const p = sectionProgress(i);
        row.append(h("span", "num", c.collapsed ? "▸" : `§${number}`));
        if (i === cur) row.classList.add("here");
        const wrap = h("span");
        const meta = `${b - a} cell${b - a === 1 ? "" : "s"}${c.collapsed ? ", folded" : ""}${p.total ? ` · ${p.done} of ${p.total} exercise${p.total === 1 ? "" : "s"}` : ""}`;
        wrap.append(h("span", "kind", c.src || "Untitled section"), h("span", "src", meta));
        if (p.total) {
          const bar = h("span", "olprog"); bar.setAttribute("aria-hidden", "true");
          const fill = h("i"); fill.style.width = `${Math.round((p.done / p.total) * 100)}%`; bar.append(fill);
          wrap.append(bar);
        }
        row.append(wrap);
      } else if (c.type === "lean") {
        row.append(h("span", "num", "λ"));
        const wrap = h("span");
        wrap.append(h("span", "kind", "Lean"), h("span", "src", c.src.split("\n").find((l) => l.trim()) || "…"));
        row.append(wrap);
      } else if (c.type === "exercise") {
        row.append(h("span", "num", c.verdict?.equivalent ? "✓" : "?"));
        const wrap = h("span");
        wrap.append(h("span", "kind", "exercise"), h("span", "src", c.prompt?.split("\n").find((l) => l.trim())?.replace(/^#+\s*/, "") || c.src || "…"));
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
      row.addEventListener("click", () => { if (S.tab !== "notebook") switchTab("notebook"); if (narrow() && S.sidebarOpen) toggleSidebar(); focusCell(i); });
      list.append(row);
    });
  } else {
    for (const d of DOCS) {
      const area = FN_BY_NAME.get(d.name)!.area;
      if (area !== FN_BY_NAME.get(DOCS[DOCS.indexOf(d) - 1]?.name ?? "")?.area) list.append(h("div", "plhead", area));
      const row = asButton(h("div", "plrow"));
      row.append(h("span", "name", d.name), h("span", "sig", d.sig));
      row.addEventListener("click", () => {
        if (S.tab !== "notebook") switchTab("notebook");
        const c = S.cells[S.active];
        if (c?.input) { c.input.value = d.examples[0] ?? `${d.name}(`; c.src = c.input.value; c.input.focus(); syncHighlight(c); updateSigHelp(c); renderCellBody(c); renderSidebar(); }
        else if (c?.mi) { c.src = d.examples[0] ?? `${d.name}(`; focusCell(S.active); }
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
function plotSvg(p: PlotData, w: number, hgt: number, frac = 1, t01?: number, yWin?: [number, number] | null): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", p.terms?.length ? `Epicycles: ${p.terms.length} circles drawing ${p.series.map((c) => c.text).join(", ")}`
    : `Plot of ${p.series.map((c) => c.text).join(" and ")} for ${p.var} from ${p.from} to ${p.to}`);
  const parametric = p.series.some((s) => s.parametric);
  // the window: the one given (a manipulated plot's, over all its frames), or the curves' own
  let [y0, y1] = !parametric && yWin ? yWin : plotYRange(p), x0 = p.from, x1 = p.to;
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
  PLOT_MAP.set(svg, { sx, sy, kx: (w - L - R) / (x1 - x0 || 1), y0, y1 });
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

/** The live view of each manipulate cell (its newest drawing, so a play survives a redraw) and the
 *  animation frame of the play under way. */
const MANIP_UI = new WeakMap<Cell, { draw: (at: number) => void; face: () => void }>();
const MANIP_PLAY = new WeakMap<Cell, number>();
function manipStop(cell: Cell) {
  const id = MANIP_PLAY.get(cell);
  if (id !== undefined) { cancelAnimationFrame(id); MANIP_PLAY.delete(cell); }
  MANIP_UI.get(cell)?.face();
}
/** ▶ Play: from where the slider is (or the first frame, from the last) to the last frame, drawn
 *  every animation frame. No engine call: the frames are already here. */
function manipPlay(cell: Cell) {
  const m = cell.manip, n = m?.frames.length ?? 0;
  if (!m || n < 2) return;
  let start = Math.round(cell.manipAt ?? 0);
  if (start >= n - 1) start = 0;
  const t0 = performance.now();
  const done = () => { MANIP_PLAY.delete(cell); MANIP_UI.get(cell)?.face(); };
  const tick = (now: number) => {
    if (cell.manip !== m || !cell.el?.isConnected) return done();   // run again, or its notebook left
    const at = playPosition(start, now - t0, n);
    cell.manipAt = at; MANIP_UI.get(cell)?.draw(at);
    if (at >= n - 1) return done();
    MANIP_PLAY.set(cell, requestAnimationFrame(tick));
  };
  MANIP_PLAY.set(cell, requestAnimationFrame(tick));
  MANIP_UI.get(cell)?.face();
}
/** A manipulate cell's output, like Mathematica's: the parameter's slider with its value and ▶ Play,
 *  and the body at that value, part by part (one part, or each of a `column(…)`): a plot, in one
 *  window for every frame and blended between frames while it plays, or the part's calculation. */
function manipBox(cell: Cell): HTMLElement {
  const m = cell.manip!, n = m.frames.length;
  const box = h("div", "manip");
  const row = h("div", "sliderrow manipctl");
  const range = document.createElement("input");
  range.type = "range"; range.min = "0"; range.max = String(n - 1); range.step = "1";
  range.setAttribute("aria-label", m.param);
  const val = h("span", "sliderval");
  const play = asButton(h("span", "sliderbtn sliderplay"));
  row.append(h("code", "slidername", m.param), range, val, play);
  const view = h("div", "manipview");
  box.append(row, view);
  // each part's place, and for a plot its frames and the one window they share
  const slots = (m.frames[0]?.parts ?? []).map((_, j) => {
    const el = h("div", "manippart"), body = h("div", "manipbody"), cap = h("div", "plotcap");
    el.append(body, cap); view.append(el);
    const plots = m.frames.every((f) => f.parts[j]?.plot && !f.parts[j]!.plot!.terms?.length) ? m.frames.map((f) => f.parts[j]!.plot!) : null;
    return { body, cap, plots, win: plots ? framesWindow(plots) : null };
  });
  const plotBox = (p: PlotData, win: [number, number] | null) => {
    const pb = h("div", "plotbox");
    pb.append(plotSvg(p, 520, p.series.some((s) => s.parametric) ? 320 : 240, 1, undefined, win));
    return pb;
  };
  let shown = -1;   // the frame whose value, terms and legends are on screen
  const draw = (at: number) => {
    const i = Math.max(0, Math.min(n - 1, Math.round(at))), f = m.frames[i]!;
    if (i !== shown) {
      range.value = String(i);
      val.innerHTML = tex(f.label);
      slots.forEach((sl, j) => {
        const pt = f.parts[j];
        sl.cap.replaceChildren();
        if (!pt) { sl.body.replaceChildren(); return; }
        if (!pt.plot) { sl.body.innerHTML = tex(workLine(pt.work, pt.latex, pt.name), true); return; }
        if (!sl.plots) sl.body.replaceChildren(plotBox(pt.plot, null));   // a curve in the plane: its own frame
        if (pt.plot.series.length > 1) {
          pt.plot.series.forEach((s, k) => {
            const it = h("span", `legend c${k % CURVE_COLOURS}`);
            it.append(h("i", "swatch")); it.insertAdjacentHTML("beforeend", tex(s.latex));
            sl.cap.append(it);
          });
        } else sl.cap.innerHTML = tex(pt.latex, true);
      });
      shown = i;
    }
    for (const sl of slots) {
      if (!sl.plots) continue;
      const lo = Math.floor(at), hi = Math.min(n - 1, lo + 1), t = at - lo;
      const a = sl.plots[lo] ?? sl.plots[i]!, b = sl.plots[hi]!;
      sl.body.replaceChildren(plotBox(t > 1e-6 && blendable(a, b) ? { ...a, series: blend(a, b, t) } : sl.plots[i]!, sl.win));
    }
  };
  const face = () => {
    const on = MANIP_PLAY.has(cell);
    play.textContent = on ? "❚❚ Pause" : "▶ Play";
    play.title = on ? "Pause" : `Play: move ${m.param} through its ${n} values`;
    play.setAttribute("aria-label", on ? `Pause ${m.param}` : `Play ${m.param}`);
    play.classList.toggle("on", on);
  };
  play.addEventListener("click", () => {
    if (!MANIP_PLAY.has(cell)) return manipPlay(cell);
    manipStop(cell);
    cell.manipAt = Math.round(cell.manipAt ?? 0); draw(cell.manipAt);   // at rest, the engine's own frame
  });
  // taking hold of the slider stops a play
  range.addEventListener("input", () => { manipStop(cell); cell.manipAt = Number(range.value); draw(cell.manipAt); });
  MANIP_UI.set(cell, { draw, face });
  draw(cell.manipAt ?? 0); face();
  return box;
}

/** A plot's mapping from data to pixels, kept beside the SVG so an animation can move things in it. */
const PLOT_MAP = new WeakMap<SVGSVGElement, { sx: (x: number) => number; sy: (y: number) => number; kx: number; y0: number; y1: number }>();

/** The epicycle animation in a cell: a 12-second lap while the box is on screen. The SVG is built
 *  once — axes, the full trace, one circle and arm per term — and each frame only moves the arms
 *  and circles and re-cuts the trace's `d` (up to the tip), at most 30 times a second; circles
 *  smaller than a pixel are not drawn at all (a 400-term llama has hundreds of them). */
function epicycleBox(p: PlotData, w: number, hgt: number): HTMLElement {
  const box = h("div", "plotbox epibox");
  const NS = "http://www.w3.org/2000/svg";
  const svg = plotSvg(p, w, hgt, 1);
  const map = PLOT_MAP.get(svg)!;
  const terms = p.terms ?? [];
  const polar = terms.map((c) => ({ r: Math.hypot(c.re, c.im), ph: Math.atan2(c.im, c.re), k: c.k }));
  const series = p.series[0];
  const curve = svg.querySelector<SVGPathElement>("path.curve");
  // the chain: a circle (when it is big enough to see) and an arm per term, then the tip
  const g = document.createElementNS(NS, "g"); g.setAttribute("class", "epi");
  const circles = polar.map((c) => {
    if (c.k === 0 || c.r * map.kx < 0.75) return null;
    const el = document.createElementNS(NS, "circle");
    el.setAttribute("r", String(c.r * map.kx)); el.setAttribute("class", "epicircle"); g.append(el);
    return el;
  });
  const arms = polar.map(() => { const l = document.createElementNS(NS, "line"); l.setAttribute("class", "epiarm"); g.append(l); return l; });
  const tip = document.createElementNS(NS, "circle");
  tip.setAttribute("r", "3"); tip.setAttribute("class", "epitip"); g.append(tip);
  svg.append(g);
  box.append(svg);
  const period = 12000;
  let start = performance.now(), lastFrame = 0;
  const draw = (now: number) => {
    const t01 = ((now - start) % period) / period, t = t01 * 2 * Math.PI;
    let x = 0, y = 0;
    polar.forEach((c, i) => {
      const nx = x + c.r * Math.cos(c.k * t + c.ph), ny = y + c.r * Math.sin(c.k * t + c.ph);
      const cx = map.sx(x).toFixed(1), cy = map.sy(y).toFixed(1);
      const circ = circles[i]; if (circ) { circ.setAttribute("cx", cx); circ.setAttribute("cy", cy); }
      const l = arms[i]!;
      l.setAttribute("x1", cx); l.setAttribute("y1", cy); l.setAttribute("x2", map.sx(nx).toFixed(1)); l.setAttribute("y2", map.sy(ny).toFixed(1));
      x = nx; y = ny;
    });
    tip.setAttribute("cx", map.sx(x).toFixed(1)); tip.setAttribute("cy", map.sy(y).toFixed(1));
    if (curve && series) {
      // the trace up to the last sample at or before t, then to the tip itself
      const n = Math.min(series.points.length, Math.floor(t01 * series.points.length) + 1);
      let d = "", pen = false;
      for (let i = 0; i < n; i++) {
        const [px, py] = series.points[i]!;
        if (py === null) { pen = false; continue; }
        d += `${pen ? "L" : "M"}${map.sx(px).toFixed(1)} ${map.sy(py).toFixed(1)} `; pen = true;
      }
      if (pen) d += `L${map.sx(x).toFixed(1)} ${map.sy(y).toFixed(1)} `;
      curve.setAttribute("d", d);
    }
  };
  // with reduced motion, the finished drawing: the whole trace, the circles at the end of the period
  if (reducedMotion()) { draw(start + period - 1); return box; }
  draw(start);
  let raf = 0;
  const loop = (now: number) => {
    if (!box.isConnected) return;
    if (!document.hidden && now - lastFrame >= 33) { lastFrame = now; draw(now); }
    raf = requestAnimationFrame(loop);
  };
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
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `Hasse diagram of ${d.nodes.length} elements${d.covers.length ? `; covers: ${d.covers.map(([a, b]) => `${a} below ${b}`).join(", ")}` : ""}`);
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

/** The visuals this notebook knows how to draw, from a reply or a file: others are left out. */
function knownVisuals(vs: unknown): KnownVisual[] {
  if (!Array.isArray(vs)) return [];
  return vs.filter((v): v is KnownVisual => {
    const d = (v as { data?: Record<string, unknown> } | null)?.data;
    if (!d) return false;
    const kind = (v as { kind?: unknown }).kind;
    if (kind === "logic.truthtable") return Array.isArray(d["vars"]) && Array.isArray(d["rows"]) && typeof (d["formula"] as { latex?: unknown } | undefined)?.latex === "string";
    if (kind === "relation.digraph") return Array.isArray(d["nodes"]) && Array.isArray(d["edges"]) && Array.isArray(d["bad"]) && Array.isArray(d["added"]);
    if (kind === "algebra.optable") return Array.isArray(d["elems"]) && Array.isArray(d["rows"]) && Array.isArray(d["marks"]);
    if (kind === "context.table") return Array.isArray(d["objects"]) && Array.isArray(d["attributes"]) && Array.isArray(d["has"]);
    if (kind === "typing.tree") return typeof (d["root"] as { latex?: unknown } | undefined)?.latex === "string";
    if (kind === "replicas.spacetime") return Array.isArray(d["lanes"]) && Array.isArray(d["events"]) && Array.isArray(d["messages"]) && Array.isArray(d["steps"]);
    return false;
  });
}

/** Mark where steps of the work are on a state graph: the trail of steps so far, and the current one
 *  (its arrow, or its state when it takes none). A step's arrow shows its own mark class too, so a
 *  marked transition keeps its colour under the trail. */
function markGraphSteps(box: HTMLElement, d: DigraphData, trail: number[], cur: number | undefined) {
  box.querySelectorAll(".redge.trail, .redge.cur, .hnode.cur").forEach((x) => x.classList.remove("trail", "cur"));
  box.querySelectorAll<SVGPathElement>(".redge").forEach((p) => {
    const cls = p.classList.contains("bad") ? "-bad" : p.classList.contains("added") ? "-added" : "";
    p.setAttribute("marker-end", `url(#rel-arrow${cls})`);
  });
  const mark = (k: number, cls: "trail" | "cur") => {
    const m = d.steps?.[k];
    if (!m) return;
    if (m.edge) {
      const want = JSON.stringify(m.edge);
      box.querySelectorAll<SVGPathElement>(".redge").forEach((p) => {
        if (p.getAttribute("data-edge") !== want) return;
        p.classList.add(cls);
        if (cls === "cur") p.setAttribute("marker-end", "url(#rel-arrow-cur)");
      });
    }
    const at = m.node ?? (cls === "cur" ? m.edge?.[1] : undefined);
    if (at !== undefined) box.querySelectorAll(".hnode").forEach((c) => { if (c.getAttribute("data-node") === at) c.classList.add(cls); });
  };
  for (const k of trail) mark(k, "trail");
  if (cur !== undefined) mark(cur, "cur");
}

/** A replica simulation as a space-time diagram: a lane per replica, left to right in the order of
 *  events, a dot per event (its label above, the replica's state in its tooltip and, when short,
 *  below), an arrow per message from the event that sent it to the one that delivered it. */
function spacetimeSvg(d: SpacetimeData): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const longest = Math.max(1, ...d.lanes.map((x) => x.length));
  // a column is as wide as the longest label or state shown under a dot (a long state goes in the tooltip only)
  const shownLen = Math.max(1, ...d.events.map((e) => Math.max(e.label.length, e.state.length <= 18 ? e.state.length : 0)));
  const left = longest * 8 + 24, colW = Math.max(64, Math.min(140, shownLen * 6.4 + 16)), laneH = 62, top = 30;
  const w = left + Math.max(1, d.events.length) * colW + 24, hgt = top + d.lanes.length * laneH;
  const laneY = (l: string) => top + Math.max(0, d.lanes.indexOf(l)) * laneH + 14;
  const ex = (i: number) => left + 20 + i * colW;
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `${d.lanes.length} replicas, ${d.events.length} events, ${d.messages.length} messages`);
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  svg.classList.add("spacetime");
  const defs = document.createElementNS(NS, "defs");
  const m = document.createElementNS(NS, "marker");
  m.setAttribute("id", "st-arrow"); m.setAttribute("viewBox", "0 0 10 10"); m.setAttribute("refX", "9"); m.setAttribute("refY", "5");
  m.setAttribute("markerWidth", "6"); m.setAttribute("markerHeight", "6"); m.setAttribute("orient", "auto-start-reverse");
  const head = document.createElementNS(NS, "path"); head.setAttribute("d", "M0,0 L10,5 L0,10 z"); head.setAttribute("class", "sthead");
  m.append(head); defs.append(m); svg.append(defs);
  for (const l of d.lanes) {
    const y = laneY(l);
    const t = document.createElementNS(NS, "text");
    t.setAttribute("x", "8"); t.setAttribute("y", String(y + 4)); t.setAttribute("class", "stlane"); t.textContent = l; svg.append(t);
    const ln = document.createElementNS(NS, "line");
    ln.setAttribute("x1", String(left)); ln.setAttribute("x2", String(w - 12)); ln.setAttribute("y1", String(y)); ln.setAttribute("y2", String(y));
    ln.setAttribute("class", "stline"); svg.append(ln);
  }
  d.messages.forEach(([a, b], k) => {
    const ea = d.events[a], eb = d.events[b]; if (!ea || !eb) return;
    const x1 = ex(a), y1 = laneY(ea.lane), x2 = ex(b), y2 = laneY(eb.lane);
    const len = Math.hypot(x2 - x1, y2 - y1) || 1;
    const p = document.createElementNS(NS, "line");
    p.setAttribute("x1", String(x1 + (x2 - x1) * 6 / len)); p.setAttribute("y1", String(y1 + (y2 - y1) * 6 / len));
    p.setAttribute("x2", String(x2 - (x2 - x1) * 7 / len)); p.setAttribute("y2", String(y2 - (y2 - y1) * 7 / len));
    p.setAttribute("class", "stmsg"); p.setAttribute("marker-end", "url(#st-arrow)");
    p.setAttribute("data-from", String(a)); p.setAttribute("data-to", String(b)); p.setAttribute("data-msg", String(k));
    svg.append(p);
  });
  d.events.forEach((e, i) => {
    const g = document.createElementNS(NS, "g");
    g.setAttribute("data-event", String(i)); g.setAttribute("class", "stev");
    const x = ex(i), y = laneY(e.lane);
    const c = document.createElementNS(NS, "circle");
    c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "stdot");
    const title = document.createElementNS(NS, "title"); title.textContent = `${e.lane}: ${e.label} → ${e.state}`; c.append(title);
    const lab = document.createElementNS(NS, "text");
    lab.setAttribute("x", String(x)); lab.setAttribute("y", String(y - 10)); lab.setAttribute("text-anchor", "middle"); lab.setAttribute("class", "stlabel");
    lab.textContent = e.label;
    g.append(c, lab);
    if (e.state.length <= 18) {
      const st = document.createElementNS(NS, "text");
      st.setAttribute("x", String(x)); st.setAttribute("y", String(y + 19)); st.setAttribute("text-anchor", "middle"); st.setAttribute("class", "ststate");
      st.textContent = e.state; g.append(st);
    }
    svg.append(g);
  });
  return svg;
}

/** Mark a space-time diagram's events for the steps of the work: the steps so far as a trail, the
 *  current one's events; while the answer is held back, the events of later steps are hidden. */
function markSpacetime(box: HTMLElement, d: SpacetimeData, trail: number[], cur: number | undefined, held: boolean) {
  const evs = (ks: number[]) => new Set(ks.flatMap((k) => d.steps[k] ?? []));
  // every step up to the current one has happened, a folded one (a delivery that changed nothing) too
  const upTo = cur === undefined ? -1 : cur;
  const shown = held ? evs(d.steps.map((_, k) => k).filter((k) => k <= upTo)) : evs(trail);
  const now = evs(cur === undefined ? [] : [cur]);
  box.querySelectorAll<SVGGElement>("[data-event]").forEach((g) => {
    const i = Number(g.getAttribute("data-event"));
    g.classList.toggle("trail", shown.has(i) && !now.has(i));
    g.classList.toggle("cur", now.has(i));
    g.style.display = held && !shown.has(i) ? "none" : "";
  });
  box.querySelectorAll<SVGLineElement>("[data-msg]").forEach((l) => {
    const to = Number(l.getAttribute("data-to"));
    l.classList.toggle("cur", now.has(to));
    l.style.display = held && !shown.has(to) ? "none" : "";
  });
}

/** The indices of a cell's shown steps (those the work lists), in order. */
function shownStepIndices(cell: Cell): number[] {
  const steps: { quiet?: boolean }[] = cell.steps?.length ? cell.steps.map((st) => ({ quiet: printsUnchanged(st) })) : (cell.outline ?? []);
  return steps.flatMap((st, i) => st.quiet ? [] : [i]);
}

/** Where a cell's state graph marks its steps: stepping through, the steps shown so far and the last of
 *  them; otherwise the step selected in its work, if any. */
function graphStepMarks(cell: Cell): { trail: number[]; cur: number | undefined } {
  if (answerHeld(cell)) {
    const shown = shownStepIndices(cell).slice(0, revealedCount(cell));
    return { trail: shown, cur: shown[shown.length - 1] };
  }
  const sel = S.sel;
  return { trail: [], cur: sel && sel.cellId === cell.id && sel.term.kind === "step" && !sel.sub ? sel.term.index : undefined };
}

/** A cell's visuals as its output shows them. Stepping through, only a state graph that places the
 *  steps shows, without the answer's marks, so it does not give the answer away. */
function cellVisuals(cell: Cell): HTMLElement[] {
  const held = answerHeld(cell);
  const out: HTMLElement[] = [];
  for (const v of cell.visuals ?? []) {
    const placed = (v.kind === "relation.digraph" && !!v.data.steps) || v.kind === "replicas.spacetime";
    if (held && !placed) continue;
    const box = visualBox(held && v.kind === "relation.digraph" ? { ...v, data: { ...v.data, bad: [], added: [] } } : v);
    if (placed) {
      box.dataset["steps"] = "1";
      const { trail, cur } = graphStepMarks(cell);
      if (v.kind === "relation.digraph") markGraphSteps(box, v.data, trail, cur);
      else if (v.kind === "replicas.spacetime") markSpacetime(box, v.data, held ? trail : [], cur, held);
    }
    out.push(box);
  }
  return out;
}

/** Re-mark every state graph on the page for the current selection. */
function remarkGraphs() {
  for (const cell of S.cells) {
    const box = cell.el?.querySelector<HTMLElement>(".visualbox[data-steps]");
    const v = cell.visuals?.find((x) => (x.kind === "relation.digraph" && !!x.data.steps) || x.kind === "replicas.spacetime");
    if (!box || !v) continue;
    const { trail, cur } = graphStepMarks(cell);
    if (v.kind === "relation.digraph") markGraphSteps(box, v.data, trail, cur);
    else if (v.kind === "replicas.spacetime") markSpacetime(box, v.data, answerHeld(cell) ? trail : [], cur, answerHeld(cell));
  }
}

/** A visual, boxed and captioned as a plot is. */
function visualBox(v: KnownVisual): HTMLElement {
  const box = h("div", "visualbox");
  if (v.kind === "logic.truthtable") box.append(truthTable(v.data));
  else if (v.kind === "relation.digraph") box.append(digraphSvg(v.data), digraphLegend(v.data));
  else if (v.kind === "algebra.optable") box.append(opTable(v.data));
  else if (v.kind === "typing.tree") box.append(typingTree(v.data));
  else if (v.kind === "replicas.spacetime") box.append(spacetimeSvg(v.data));
  else box.append(contextTable(v.data));
  return box;
}

/** A typing derivation as a proof tree: each judgment under a bar, its premises above, the rule to the
 *  bar's right. Var has no premises, so its bar stands alone. */
function typingTree(d: TypingTreeData): HTMLElement {
  const wrap = h("div", "typingtree");
  wrap.setAttribute("role", "img");
  wrap.setAttribute("aria-label", `Typing derivation of ${d.root.text}`);
  const node = (n: TypingNode, depth: number): HTMLElement => {
    const el = h("div", "ptnode");
    if (n.premises.length) {
      const prem = h("div", "ptprem");
      // a deep tree is cut off rather than drawn past any width
      if (depth < 12) for (const p of n.premises) prem.append(node(p, depth + 1));
      else prem.append(h("span", "ptmore", "⋮"));
      el.append(prem);
    }
    const concl = h("div", "ptconc");
    concl.title = n.text;
    concl.innerHTML = tex(n.latex);
    concl.append(h("span", "ptrule", n.rule));
    el.append(concl);
    return el;
  };
  const tree = h("div", "pttree");
  tree.append(node(d.root, 0));
  wrap.append(tree);
  if (d.legend?.length) {
    const lg = h("div", "ptlegend");
    for (const l of d.legend) { const row = h("div"); row.title = l.text; row.innerHTML = tex(l.latex); lg.append(row); }
    wrap.append(lg);
  }
  return wrap;
}

/** An operation's table: the row's element times the column's, the marked cells (a law failing) shaded. */
function opTable(d: OpTableData): HTMLElement {
  const t = h("table", "truthtable optable");
  t.setAttribute("aria-label", `Operation table on ${d.elems.length} elements${d.marks.length ? `; marked: ${d.marks.map(([a, b]) => `${a} · ${b}`).join(", ")}` : ""}`);
  const marked = new Set(d.marks.map(([a, b]) => `${a}\u0000${b}`));
  const head = h("tr");
  head.append(h("th", "optcorner", "·"));
  for (const y of d.elems) head.append(h("th", undefined, y));
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  d.rows.forEach((row, i) => {
    const x = d.elems[i] ?? "";
    const tr = h("tr");
    tr.append(h("th", "oprow", x));
    row.forEach((v, j) => tr.append(h("td", marked.has(`${x}\u0000${d.elems[j] ?? ""}`) ? "opmark" : "", v)));
    body.append(tr);
  });
  t.append(body);
  return t;
}

/** A formal context: a row per object, a column per attribute, × where the object has it. */
function contextTable(d: ContextTableData): HTMLElement {
  const t = h("table", "truthtable ctxtable");
  t.setAttribute("aria-label", `A context of ${d.objects.length} objects and ${d.attributes.length} attributes`);
  const head = h("tr");
  head.append(h("th"));
  for (const a of d.attributes) head.append(h("th", undefined, a));
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  d.objects.forEach((o, i) => {
    const tr = h("tr");
    tr.append(h("th", "oprow", o));
    (d.has[i] ?? []).forEach((b) => tr.append(h("td", undefined, b ? "×" : "")));
    body.append(tr);
  });
  t.append(body);
  return t;
}

/** A truth table: a column per variable, then the formula; T and F, the formula's false rows marked. */
function truthTable(d: TruthTableData): HTMLElement {
  const t = h("table", "truthtable");
  t.setAttribute("aria-label", `Truth table of ${d.formula.text}: ${d.rows.length} rows`);
  const head = h("tr");
  for (const v of d.vars) { const th = h("th"); th.innerHTML = tex(v); head.append(th); }
  const fth = h("th", "ttf"); fth.innerHTML = tex(d.formula.latex); head.append(fth);
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  for (const row of d.rows) {
    const tr = h("tr", row[row.length - 1] ? "" : "ttfalse");
    row.forEach((b, i) => tr.append(h("td", i === row.length - 1 ? "ttf" : "", b ? "T" : "F")));
    body.append(tr);
  }
  t.append(body);
  return t;
}

/** A relation as a directed graph: elements on a circle, a pair as an arrow (a loop for `x R x`). The
 *  arrows that show a property failing are marked, and the ones a closure added are dashed. */
function digraphSvg(d: DigraphData): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const n = d.nodes.length;
  const longest = Math.max(1, ...d.nodes.map((x) => x.length));
  const layered = !!d.layers && d.layers.length === n;
  const pos = new Map<string, [number, number]>();
  let w: number, hgt: number;
  if (layered) {
    // a state graph: the initial states on top, each row one step further on
    const rows = new Map<number, string[]>();
    d.nodes.forEach((name, i) => { const l = d.layers![i]!; rows.set(l, [...(rows.get(l) ?? []), name]); });
    const widest = Math.max(1, ...[...rows.values()].map((r) => r.length));
    const colW = Math.max(70, longest * 7 + 24), rowH = 74;
    w = Math.max(240, widest * colW + 40); hgt = (Math.max(0, ...rows.keys()) + 1) * rowH + 30;
    for (const [l, names] of rows) names.forEach((name, k) => pos.set(name, [20 + (k + 0.5) * ((w - 40) / names.length), 24 + l * rowH]));
  } else {
    const r = n <= 1 ? 0 : Math.max(60, Math.min(150, 26 * n)), pad = Math.max(60, longest * 6.6 + 24);
    w = 2 * r + 2 * pad; hgt = 2 * r + 90;
    d.nodes.forEach((name, i) => {
      const a = -Math.PI / 2 + (2 * Math.PI * i) / Math.max(1, n);
      pos.set(name, [w / 2 + r * Math.cos(a), hgt / 2 + r * Math.sin(a)]);
    });
  }
  const key = ([a, b]: [string, string]) => `${a}\u0000${b}`;
  const bad = new Set(d.bad.map(key)), added = new Set(d.added.map(key)), all = new Set(d.edges.map(key));
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `A relation on ${n} element${n === 1 ? "" : "s"}${d.edges.length ? `; pairs: ${d.edges.map(([a, b]) => `${a} to ${b}`).join(", ")}` : ", no pairs"}`);
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  const defs = document.createElementNS(NS, "defs");
  for (const cls of ["", "bad", "added", "cur"]) {
    const m = document.createElementNS(NS, "marker");
    m.setAttribute("id", `rel-arrow${cls ? `-${cls}` : ""}`); m.setAttribute("viewBox", "0 0 10 10"); m.setAttribute("refX", "9"); m.setAttribute("refY", "5");
    // a marker scales with its arrow's stroke: the current arrow is drawn thicker, so its head is set smaller
    const mw = cls === "cur" ? "4.5" : "7";
    m.setAttribute("markerWidth", mw); m.setAttribute("markerHeight", mw); m.setAttribute("orient", "auto-start-reverse");
    const path = document.createElementNS(NS, "path"); path.setAttribute("d", "M0,0 L10,5 L0,10 z"); path.setAttribute("class", `rhead ${cls}`);
    m.append(path); defs.append(m);
  }
  svg.append(defs);
  for (const e of d.edges) {
    const [a, b] = e;
    const p = pos.get(a), q = pos.get(b); if (!p || !q) continue;
    const cls = bad.has(key(e)) ? "bad" : added.has(key(e)) ? "added" : "";
    const path = document.createElementNS(NS, "path");
    if (a === b) {
      // a loop, outward from the centre
      const ang = Math.atan2(p[1] - hgt / 2, p[0] - w / 2) || -Math.PI / 2;
      const cx = p[0] + 18 * Math.cos(ang), cy = p[1] + 18 * Math.sin(ang);
      const s1 = [p[0] + 7 * Math.cos(ang - 0.6), p[1] + 7 * Math.sin(ang - 0.6)], s2 = [p[0] + 7 * Math.cos(ang + 0.6), p[1] + 7 * Math.sin(ang + 0.6)];
      path.setAttribute("d", `M${s1[0]},${s1[1]} Q${cx + 14 * Math.cos(ang - 1.2)},${cy + 14 * Math.sin(ang - 1.2)} ${cx},${cy} Q${cx + 14 * Math.cos(ang + 1.2)},${cy + 14 * Math.sin(ang + 1.2)} ${s2[0]},${s2[1]}`);
    } else {
      // stop short of the nodes; bend when the reverse pair is drawn too, so the two do not overlap
      const dx = q[0] - p[0], dy = q[1] - p[1], len = Math.hypot(dx, dy) || 1, ux = dx / len, uy = dy / len;
      const x1 = p[0] + ux * 8, y1 = p[1] + uy * 8, x2 = q[0] - ux * 9, y2 = q[1] - uy * 9;
      // bend a pair drawn both ways apart; in a layered drawing, bend edges within a row or back up it
      const bend = all.has(key([b, a])) ? 14 : layered && q[1] <= p[1] ? 26 : 0;
      const mx = (x1 + x2) / 2 - uy * bend, my = (y1 + y2) / 2 + ux * bend;
      path.setAttribute("d", `M${x1},${y1} Q${mx},${my} ${x2},${y2}`);
    }
    path.setAttribute("class", `redge ${cls}`);
    path.setAttribute("marker-end", `url(#rel-arrow${cls ? `-${cls}` : ""})`);
    path.setAttribute("data-edge", JSON.stringify(e));
    svg.append(path);
  }
  for (const [name, [x, y]] of pos) {
    const c = document.createElementNS(NS, "circle");
    c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "hnode"); c.setAttribute("data-node", name); svg.append(c);
    const t = document.createElementNS(NS, "text");
    if (layered) {
      // centred under the node
      t.setAttribute("x", String(x)); t.setAttribute("y", String(y + 19)); t.setAttribute("text-anchor", "middle");
    } else {
      // outward from the centre, past the node's loop when it has one
      const out = Math.atan2(y - hgt / 2, x - w / 2) || -Math.PI / 2, dist = d.edges.some(([a, b]) => a === name && b === name) ? 40 : 14;
      t.setAttribute("x", String(x + dist * Math.cos(out) - (Math.cos(out) < -0.3 ? name.length * 6.6 : 4))); t.setAttribute("y", String(y + dist * Math.sin(out) + 4));
    }
    t.setAttribute("class", "hlabel"); t.textContent = name; svg.append(t);
  }
  return svg;
}

/** What the marked arrows mean, when there are any. */
function digraphLegend(d: DigraphData): HTMLElement {
  const cap = h("div", "plotcap");
  const pairs = (ps: [string, string][]) => ps.map(([a, b]) => `${a}→${b}`).join(", ");
  if (d.bad.length) cap.append(h("span", "legend relbad", `marked: ${pairs(d.bad)}`), " ");
  if (d.added.length) cap.append(h("span", "legend reladded", `added: ${pairs(d.added)}`));
  return cap;
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

// --- The visual input: math cells typeset as they are typed ---------------------------------------

/** The functions this session has defined: after `let f(x) = …`, `f(` is a call. */
/** The notebook's own functions, which act on files before the engine sees a cell (files.ts): calls
 *  in the visual input as the engine's builtins are. */
const NOTEBOOK_FNS = ["import", "samplePoints", "matrix", "dimensions"];
const sessionFns = () => [...NOTEBOOK_FNS, ...[...USER_FNS.keys()].filter((k) => k.startsWith(`${sessionId}:`)).map((k) => k.slice(sessionId.length + 1))];

/** Why a cell cannot be shown visually, or null when it can. λ-terms, order theory and file
 *  references are other grammars; so is text that does not parse, which stays as typed to be fixed. */
function visualBlocked(cell: Cell): string | null {
  if (cell.type) return "it is not a math cell";
  const src = cellSrc(cell);
  if (cell.tree && writeText(cell.tree) === src) return null;   // the visual input's own, holes and all
  const kind = cell.kind ?? cellKind(src);
  if (kind === "lookup") return "questions are edited as text";
  if (kind === "λ-term") return "λ-terms are edited as text";
  if (kind === "order" || ORDER_CELL.test(src.trim())) return "order theory is edited as text";
  if (kind === "logic" || isLogicCell(src.trim())) return "logic is edited as text";
  if (kind === "system" || SYSTEM_CELL.test(src.trim())) return "systems are edited as text";
  if (src.includes("\n")) return "a cell of several lines is edited as text";
  if (src.trim() && !readNotation(src, sessionFns()).ok) return "the text does not parse yet";
  return null;
}
const cellMode = (cell: Cell) => cell.mode ?? S.inputMode;

/** Auto's decision for the cell's source: typeset when it has notation to show, or empty slots of the
 *  visual input's own. */
function decideAuto(cell: Cell) {
  const src = cellSrc(cell);
  const own = cell.tree && writeText(cell.tree) === src ? cell.tree : null;
  const r = own ? null : src.trim() ? readNotation(src, sessionFns()) : null;
  const tree = own ?? (r?.ok ? r.stmt : null);
  cell.autoVisual = !!tree && (hasNotation(tree.body) || writeNotation(tree).holes > 0);
  cell.autoFor = src;
}

function isVisual(cell: Cell): boolean {
  if (visualBlocked(cell)) return false;
  const mode = cellMode(cell);
  if (mode !== "auto") return mode === "visual";
  // the cell being typed in keeps the input it has; it is decided again when it is left
  if (cell.autoFor === undefined || (cell.autoFor !== cellSrc(cell) && S.cells[S.active] !== cell)) decideAuto(cell);
  return !!cell.autoVisual;
}

/** Leaving an Auto cell: typeset if it now has notation, text if not. */
function autoSettle(cell: Cell) {
  setTimeout(() => {
    if (!cell.el?.isConnected || cell.el.contains(document.activeElement) || cellMode(cell) !== "auto") return;
    const was = !!cell.mi;
    decideAuto(cell);
    if (isVisual(cell) !== was) refreshInput(cell);
  }, 0);
}

/** A `\template` typed in a cell's text: the cell goes typeset with the template where it was typed.
 *  False when the cell stays text (Math input: text, a λ-cell, or text that does not read around it). */
function openTemplate(cell: Cell, before: string, after: string): boolean {
  if (cellMode(cell) === "raw" || cell.kind === "λ-term" || !templateAt(before)) return false;
  const rest = before.slice(0, templateAt(before)!.start) + after;
  if (/[λ\\]|:=/.test(rest)) return false;
  const e = templateInText(before, after, { known: sessionFns(), symbols: VISUAL_SYMBOLS });
  if (!e) return false;
  cell.tree = e.stmt; cell.src = writeText(e.stmt); cell.openedEdit = e;
  if (cellMode(cell) === "auto") { cell.autoVisual = true; cell.autoFor = cell.src; }
  refreshInput(cell);
  cell.mi?.focus();
  renderSidebar(); renderTabs();
  return true;
}

/** `?` typed in a typeset input that holds nothing yet, or only `let name =`: the cell becomes a
 *  question (`?…`, `let name = ?…`), which is edited as text, with the caret after the `?`. */
function openQuestion(cell: Cell): boolean {
  const m = /^\s*(?:let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=?\s*)?$/.exec(cell.src);
  if (!m) return false;
  cell.src = m[1] ? `let ${m[1]} = ?` : "?";
  delete cell.tree; delete cell.autoFor;
  refreshInput(cell);
  const input = cell.input;
  if (input) { input.focus(); input.setSelectionRange(input.value.length, input.value.length); syncHighlight(cell); }
  renderSidebar(); renderTabs();
  return true;
}

function visualInput(cell: Cell, i: number): MathInput | null {
  const opts: MathInputOptions = {
    known: sessionFns(), symbols: VISUAL_SYMBOLS, label: `Cell ${i + 1}, math input`,
    onFocus: () => { S.active = i; renderChrome(); renderSidebar(); markActive(); updateKeypad(); },
    onBlur: () => { hideSigHelp(); autoSettle(cell); updateKeypad(); },
    onCaret: () => updateVisualSigHelp(cell),
    onChange: (text) => { cell.src = text; renderSidebar(); renderTabs(); },
    onEnter: () => runFromInput(cell),
    onLeave: (dir) => { const j = i + dir; if (j >= 0 && j < S.cells.length) focusCell(j); },
    onKey: (ev) => {
      if (ev.key === "Escape" && S.sig) { ev.preventDefault(); dismissSigHelp(); return true; }
      // `?` is not notation: at the start of the cell it makes the cell a question, edited as text
      if (ev.key === "?" && !ev.ctrlKey && !ev.metaKey && !ev.altKey) {
        ev.preventDefault();
        if (!openQuestion(cell)) notify("err", "? starts a question: type it at the start of a cell, or after let name =.");
        return true;
      }
      return modeKey(ev, cell);
    },
    onPaste: (ev) => onPaste(ev, cell),
    // in an index of a part: the column names or keys that can go there, and All
    partNames: (before) => {
      const part = partIn(cell, before);
      if (!part) return [];
      return [{ name: "All", what: "every position" }, ...part.help.names.map((n) => ({ name: n, what: part.help.namesAre ?? "name" }))];
    },
    // what a name being typed could be, as the text input lists them: the session's names, then functions
    functions: (prefix) => [
      ...sessionNames(docOf(cell)?.sessionId ?? sessionId, prefix),
      ...DOCS.filter((d) => !d.notation && d.name.toLowerCase().startsWith(prefix.toLowerCase()) && /^[A-Za-z]/.test(d.name)).map((d) => ({ name: d.name, what: d.blurb.split(".")[0]!, call: true })),
    ].slice(0, 9),
    // the text highlighter's colours: what a name is, and where it is bound
    classify: (text, as) => {
      if (as === "num") return "hnum";
      if (as === "keyword") return "hkw";
      if (as === "bound") return "hbound";
      if (USER_NAMES.has(`${sessionId}:${text}`)) return "hdef";
      if (CONSTANTS.has(text)) return "hconst";
      return as === "call" ? (COMMANDS.has(text) ? "hcmd" : BUILTIN_FN.has(text) ? "hfn" : null) : null;
    },
    // `%` is the output before this cell's own (or, not yet run, the latest); `%n` is Out[n]
    outRef: (ref, editing) => {
      // a relative reference: the output this cell's output used (its In[n] counts back from n), or,
      // while it is edited or before it has run, the one a run now would use (counting back from
      // the next number)
      const pending = !/^%\d+$/.test(ref) && (editing || cell.label == null);
      const base = pending ? Math.max(0, ...S.cells.map((c) => c.label ?? 0)) + 1 : cell.label ?? 0;
      const n = /^%\d+$/.test(ref) ? +ref.slice(1) : base - ref.length;
      if (n < 1) return null;
      const out = S.cells.find((c) => c.label === n)?.outText;
      return { label: n, pending, ...(out ? { value: out } : {}) };
    },
  };
  const e = cell.openedEdit;
  delete cell.openedEdit;
  if (e && e.stmt === cell.tree) opts.edit = e;
  const mi = cell.tree && writeText(cell.tree) === cell.src ? new MathInput(cell.tree, opts) : MathInput.fromSource(cell.src, opts);
  if (mi) cell.tree = mi.edit.stmt; else delete cell.tree;
  return mi;
}

/** A run made a new output: the typeset inputs whose `%` or `%%` shows what a run would use (the
 *  one being edited, those not run yet) count from it now. */
function refreshRelativeRefs() {
  for (const c of S.cells) if (c.mi && /%(?![%\d])|%%/.test(c.src)) c.mi.render();
}

/** Enter in a math cell: run it — unless a visual input still has an empty slot, which the engine
 *  could not read: the caret goes there instead. */
function runFromInput(cell: Cell) {
  const mi = cell.mi;
  if (mi?.holes) { mi.edit.hole(1); mi.render(); notify("err", `Fill the empty slot${mi.holes === 1 ? "" : "s"} first (Tab moves between them).`); return; }
  void runCell(cell);
}

// --- The math keypad: templates and moves a phone's keyboard does not have -----------------------

interface PadKey { label: string; title: string; tpl?: string; ch?: string; move?: -1 | 1 | "hole" | "run" }
const KEYPAD: PadKey[] = [
  { label: "a⁄b", title: "Fraction", tpl: "frac" }, { label: "xⁿ", title: "Power", ch: "^" },
  { label: "√", title: "Square root", tpl: "sqrt" }, { label: "d/dx", title: "Derivative", tpl: "diff" },
  { label: "∫", title: "Integral", tpl: "int" }, { label: "∫ₐᵇ", title: "Definite integral", tpl: "dint" },
  { label: "Σ", title: "Sum", tpl: "sum" }, { label: "[ ]", title: "Matrix", tpl: "mat" },
  { label: "|x|", title: "Absolute value", tpl: "abs" }, { label: "π", title: "Pi", ch: "π" },
  { label: "(", title: "Open parenthesis", ch: "(" }, { label: ")", title: "Close parenthesis", ch: ")" },
  { label: "←", title: "Left", move: -1 }, { label: "→", title: "Right", move: 1 },
  { label: "⇥", title: "Next empty slot", move: "hole" }, { label: "▶", title: "Run the cell", move: "run" },
];
/** In a text cell whose text does not read around the caret yet, a template key types the call instead. */
const PAD_TEXT: Record<string, string> = { frac: "/", sqrt: "sqrt(", diff: "diff(", int: "integrate(", dint: "integrate(", sum: "sum(", mat: "[", abs: "abs(" };

/** The math cell whose input has the focus, if any. */
function focusedMathCell(): Cell | null {
  const a = document.activeElement;
  return S.cells.find((c) => !c.type && ((c.input && c.input === a) || (c.mi && c.mi.el.contains(a)))) ?? null;
}

function pressKey(k: PadKey) {
  const cell = focusedMathCell();
  if (!cell) return;
  if (k.move === "run") return runFromInput(cell);
  if (cell.mi) {
    const mi = cell.mi;
    // a fraction takes what is on its left as the numerator, as typing `/` does
    mi.apply((e) => k.tpl === "frac" ? e.type("/") : k.tpl ? e.insert(TEMPLATES[k.tpl]!.make(), true) : k.ch ? e.type(k.ch)
      : k.move === -1 ? e.left() : k.move === 1 ? e.right() : k.move === "hole" ? e.hole(1) : false);
    return;
  }
  const input = cell.input!;
  const at = input.selectionStart ?? input.value.length, end = input.selectionEnd ?? at;
  if (k.move === -1 || k.move === 1) { const p = Math.max(0, Math.min(input.value.length, at + k.move)); input.setSelectionRange(p, p); return; }
  // a template turns the cell typeset where it can, as typing it does
  if (k.tpl && openTemplate(cell, input.value.slice(0, at) + "\\" + k.tpl, input.value.slice(end))) return;
  const ins = k.tpl ? PAD_TEXT[k.tpl] : k.ch;
  if (!ins) return;
  input.setRangeText(ins, at, end, "end");
  cell.src = input.value; syncHighlight(cell); updateSigHelp(cell); renderSidebar(); renderTabs();
}

let keypadEl: HTMLElement | null = null;
/** Show the keypad while a math cell has the focus (View › Math keypad; on by default on phones),
 *  just above the on-screen keyboard. */
function updateKeypad() {
  setTimeout(() => {
    const cell = S.keypad ? focusedMathCell() : null;
    if (!cell) { keypadEl?.remove(); keypadEl = null; return; }
    if (!keypadEl) {
      keypadEl = h("div", "keypad");
      keypadEl.setAttribute("role", "toolbar"); keypadEl.setAttribute("aria-label", "Math keypad");
      for (const k of KEYPAD) {
        const b = document.createElement("button");
        b.type = "button"; b.textContent = k.label; b.title = k.title; b.setAttribute("aria-label", k.title);
        if (k.move === "hole") b.className = "kvisual";
        // the input keeps the focus (and a phone its keyboard)
        b.addEventListener("pointerdown", (e) => e.preventDefault());
        b.addEventListener("mousedown", (e) => e.preventDefault());
        b.addEventListener("click", () => pressKey(k));
        keypadEl.append(b);
      }
      document.body.append(keypadEl);
    }
    keypadEl.classList.toggle("text", !cell.mi);
    const vv = window.visualViewport;
    keypadEl.style.bottom = `${vv ? Math.max(0, window.innerHeight - vv.height - vv.offsetTop) : 0}px`;
  }, 0);
}
window.visualViewport?.addEventListener("resize", () => { if (keypadEl) updateKeypad(); });
window.visualViewport?.addEventListener("scroll", () => { if (keypadEl) updateKeypad(); });

/** Switch a cell between visual and text input (and remember it for the cell). */
function toggleMode(cell: Cell) {
  const blocked = visualBlocked(cell);
  if (!isVisual(cell) && blocked) { notify("err", `This cell stays as text: ${blocked}.`); return; }
  cell.mode = isVisual(cell) ? "raw" : "visual";
  focusCell(S.cells.indexOf(cell));
  autosave();
}
/** Ctrl/⌘+Shift+M in either input. */
function modeKey(ev: KeyboardEvent, cell: Cell): boolean {
  if (!((ev.ctrlKey || ev.metaKey) && ev.shiftKey && ev.key.toLowerCase() === "m")) return false;
  ev.preventDefault();
  toggleMode(cell);
  return true;
}
function modeToggle(cell: Cell): HTMLElement {
  const on = isVisual(cell), blocked = visualBlocked(cell);
  const b = asButton(h("span", "modetog", on ? "Text" : "Visual"), on ? "Edit as text" : "Edit as typeset math");
  b.title = on ? "Edit this cell as text (Ctrl+Shift+M)" : blocked ? `Visual input is not available: ${blocked}` : "Edit this cell as typeset math, with holes to fill (Ctrl+Shift+M)";
  if (!on && blocked) b.setAttribute("aria-disabled", "true");
  b.addEventListener("mousedown", (e) => e.preventDefault());
  b.addEventListener("click", () => toggleMode(cell));
  return b;
}

/** A math cell's input: the visual one, or the text input with its highlight overlay underneath. */
/** A typeset input can be several lines tall (a stack of fractions); its `In[n]:=` sits level with
 *  its middle rather than its top. */
const promptLevel = new ResizeObserver((entries) => {
  for (const { target } of entries) {
    const mi = target as HTMLElement, prompt = mi.closest(".cell")?.querySelector<HTMLElement>(":scope > .prompt");
    if (!prompt || !mi.isConnected) continue;
    const line = parseFloat(getComputedStyle(prompt).lineHeight) || 23;
    const top = mi.getBoundingClientRect().top - prompt.getBoundingClientRect().top;
    prompt.style.paddingTop = `${Math.max(5, top + (mi.offsetHeight - line) / 2)}px`;
  }
});

function inputEls(cell: Cell, i: number): HTMLElement[] {
  const mi = isVisual(cell) ? visualInput(cell, i) : null;
  if (mi) { cell.mi = mi; promptLevel.observe(mi.el); return [mi.el]; }
  // a source of several lines (a system, say) is a textarea; Shift+Enter starts a new line, Enter runs
  const multi = cellSrc(cell).includes("\n");
  const input = multi ? document.createElement("textarea") : document.createElement("input");
  input.className = multi ? "cellin multi" : "cellin"; input.value = cell.src;
  if (input instanceof HTMLInputElement) input.type = "text";
  else { input.wrap = "off"; fitRows(input); }
  input.setAttribute("aria-label", `Cell ${i + 1}, math input`);
  input.autocapitalize = "off"; input.autocomplete = "off"; input.setAttribute("autocorrect", "off"); input.enterKeyHint = "go";
  input.placeholder = i === 0 ? "e.g. diff(x^2 * sin(x), x)" : "";
  input.spellcheck = false;
  cell.input = input;
  input.addEventListener("focus", () => { S.active = i; renderChrome(); renderSidebar(); markActive(); updateKeypad(); });
  input.addEventListener("input", () => { cell.src = input.value; if (input instanceof HTMLTextAreaElement) fitRows(input); updateCompletions(cell); updateSigHelp(cell); syncHighlight(cell); renderSidebar(); renderTabs(); });
  input.addEventListener("keyup", () => { updateSigHelp(cell); syncHighlight(cell); });   // caret moves without an input event
  input.addEventListener("click", () => updateSigHelp(cell));
  input.addEventListener("scroll", () => syncHighlight(cell));
  input.addEventListener("blur", () => { hideCompletions(); hideSigHelp(); autoSettle(cell); updateKeypad(); });
  input.addEventListener("keydown", (ev) => onKey(ev as KeyboardEvent, cell, i));
  input.addEventListener("paste", (ev) => onPaste(ev as ClipboardEvent, cell));
  // the highlight overlay sits under the transparent text of the input; the input keeps caret and selection
  const hl = h("div", "hl"); hl.setAttribute("aria-hidden", "true");
  cell.hl = hl;
  syncHighlight(cell);
  return [hl, input];
}

/** A textarea as tall as its lines. */
function fitRows(ta: HTMLTextAreaElement) { ta.rows = Math.max(1, ta.value.split("\n").length); }

/** Swap one cell's input (typeset ↔ text) in place, without rebuilding the others. */
function refreshInput(cell: Cell) {
  const i = S.cells.indexOf(cell), mid = cell.el?.querySelector(".mid");
  if (i < 0 || !mid) return;
  for (const el of mid.querySelectorAll(":scope > .mi, :scope > .hl, :scope > .cellin")) { promptLevel.unobserve(el); el.remove(); }
  delete cell.mi; delete cell.input; delete cell.hl;
  cell.el?.querySelector<HTMLElement>(":scope > .prompt")?.style.removeProperty("padding-top");
  mid.prepend(...inputEls(cell, i));
  cell.el?.querySelector(".modetog")?.replaceWith(modeToggle(cell));
  renderCellBody(cell);
}

/** Where the notebook is scrolled to, as the first cell in view and how far down the view it is, so a
 *  rebuild can put the page back where it was even when the cells above it change height. */
interface ScrollSpot { cell: Cell | undefined; at: number; offset: number; scrollTop: number }
function scrollSpot(host: HTMLElement): ScrollSpot {
  const top = host.getBoundingClientRect().top;
  const els = [...host.querySelectorAll<HTMLElement>(":scope > .cell")];
  const at = els.findIndex((el) => el.getBoundingClientRect().bottom > top);
  const el = els[at];
  return { cell: el && S.cells.find((c) => c.el === el), at, offset: el ? el.getBoundingClientRect().top - top : 0, scrollTop: host.scrollTop };
}
function restoreScroll(host: HTMLElement, spot: ScrollSpot) {
  if (spot.at < 0) { host.scrollTop = spot.scrollTop; return; }
  // the same cell if it is still there, else (it was deleted) the one that took its place
  const el = spot.cell?.el?.isConnected ? spot.cell.el : host.querySelectorAll<HTMLElement>(":scope > .cell")[spot.at];
  if (!el) { host.scrollTop = spot.scrollTop; return; }
  host.scrollTop += el.getBoundingClientRect().top - host.getBoundingClientRect().top - spot.offset;
}
/** Keep the page where it was while the rebuilt cells settle: a typeset input fits its parens once
 *  it is on screen and a Lean editor mounts later, both changing the height of cells above the view.
 *  Anything else that moves the page meanwhile (focus bringing a new cell into view) is where it
 *  is kept from then on. The hold ends after a moment, or as soon as the reader scrolls. */
let scrollHold: (() => void) | null = null;
function holdScroll(host: HTMLElement, spot: ScrollSpot) {
  scrollHold?.();
  let set = host.scrollTop;
  const ro = new ResizeObserver(() => { restoreScroll(host, spot); set = host.scrollTop; });
  for (const el of host.children) ro.observe(el);
  const moved = () => { if (Math.abs(host.scrollTop - set) > 1) { spot = scrollSpot(host); set = host.scrollTop; } };
  const inputs = ["wheel", "touchstart", "keydown", "mousedown"];
  const stop = () => {
    ro.disconnect(); clearTimeout(timer);
    host.removeEventListener("scroll", moved);
    for (const ev of inputs) host.removeEventListener(ev, stop);
    if (scrollHold === stop) scrollHold = null;
  };
  const timer = setTimeout(stop, 1500);
  host.addEventListener("scroll", moved, { passive: true });
  for (const ev of inputs) host.addEventListener(ev, stop, { passive: true });
  scrollHold = stop;
}

function renderCells() {
  hideHover(); hideSigHelp();
  const host = $(".cells");
  const spot = scrollSpot(host);
  host.innerHTML = "";
  promptLevel.disconnect();
  // Lean cells: one document per notebook, whose views are rebuilt with the cells
  const leanCells = leanDocCells();
  const leanIds = new Set(leanCells.map((c) => c.id));
  unmountLean((id) => leanIds.has(id));
  syncLean(currentDoc(), leanCells);
  if (leanCells.length) void ensureLean(leanHooks());
  let folded = false;   // inside a collapsed section: its cells are not built
  S.cells.forEach((cell, i) => {
    if (cell.type === "section") folded = !!cell.collapsed;
    else if (folded) { delete cell.el; delete cell.input; delete cell.ta; delete cell.hl; delete cell.mi; return; }
    const el = h("div", `cell${i === S.active ? " active" : ""}${cell.label ? " done" : ""}${cell.type ? ` ${cell.type}` : ""}`);
    cell.el = el;
    delete cell.input; delete cell.ta; delete cell.hl; delete cell.mi;
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
    if (cell.type === "lean") {
      el.append(h("div", "prompt", "Lean"));
      const mid = h("div", "mid");
      const view = h("div", "leanview");
      view.setAttribute("aria-label", `Cell ${i + 1}, Lean`);
      view.addEventListener("focusin", () => { if (S.active !== i) { S.active = i; renderChrome(); renderSidebar(); markActive(); } });
      mid.append(view, h("div", "cellbody"));
      el.append(mid);
      const acts = h("div", "cellacts");
      el.append(acts, h("div", "brk"));
      insertGap(host, i);
      host.append(el);
      mountLean(cell.id, view, cell.src);
      renderCellBody(cell);
      return;
    }
    if (cell.type === "exercise") {
      el.append(h("div", "prompt", "Ex."));
      const mid = h("div", "mid");
      const box = h("div", "xc-box");
      box.addEventListener("focusin", () => { if (S.active !== i) { S.active = i; renderChrome(); renderSidebar(); markActive(); } });
      mid.append(box);
      // a Lean exercise's proof is a view of the notebook's Lean file, made once: the parts around it are
      // redrawn as Lean reports, the editor is not (it would lose its cursor)
      if (isLeanCell(cell) && !cell.editing) {
        const view = h("div", "leanview xc-leanproof");
        view.setAttribute("aria-label", `Cell ${i + 1}, your proof in Lean`);
        view.addEventListener("focusin", () => { if (S.active !== i) { S.active = i; renderChrome(); renderSidebar(); markActive(); } });
        mid.append(view, h("div", "xc-below"));
        mountLean(cell.id, view, cell.attempt ?? cell.leanStart ?? LEAN_START);
      }
      mid.append(h("div", "cellbody"));
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
      const tog = asButton(h("span", "secttog", cell.collapsed ? "▸" : "▾"), cell.collapsed ? "Unfold section" : "Fold section");
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
      const run = asButton(h("span", undefined, "▶ Run section")); run.title = "Run every cell of this section, in order";
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
    mid.append(...inputEls(cell, i));
    // a slider sits outside the body, which every evaluation redraws: a drag must survive the runs it starts
    const slider = cell.slider && SLIDER_SRC.test(cellSrc(cell)) ? sliderRow(cell) : null;
    if (slider) mid.append(slider);

    const body = h("div", "cellbody");
    mid.append(body);
    el.append(mid);

    const acts = h("div", "cellacts");
    acts.append(modeToggle(cell));
    const run = asButton(h("span", undefined, "▶ Run")); run.title = "Run this cell";
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
  // the typeset inputs are on the page now: their heights, before the page is put back
  for (const c of S.cells) c.mi?.layout();
  restoreScroll(host, spot);
  holdScroll(host, spot);
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
  more.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); typeMenu(more, (t) => insertCell(at, t), undefined, LEAN_EXERCISE_KIND(() => insertCell(at, "exercise", true))); });
  host.append(gap);
}

const CELL_TYPES: [CellType, string, string][] = [
  ["math", "Math cell", "An input for the engine: In[n]:= …"],
  ["markdown", "Markdown text", "Prose with $math$, $$display math$$, `code` and ``` blocks"],
  ["section", "Section heading", "Groups the cells below it: run them together, fold them away"],
  ["lean", "Lean cell", "Lean 4, checked as you type; goals in the panel, definitions shared with the Lean cells below"],
  ["exercise", "Exercise", "A question the reader answers; the engine checks the answer and holds the worked solution"],
];
/** The one kind of cell that is not a `CellType` of its own: an exercise whose answer is a Lean proof. */
const LEAN_EXERCISE_KIND = (act: () => void): [string, string, () => void] =>
  ["Lean exercise", "A statement in Lean for the reader to prove; Lean checks the proof", act];
/** A small menu of the cell kinds under `anchor`; `pick` gets the chosen one. */
function typeMenu(anchor: HTMLElement, pick: (t: CellType) => void, current?: CellType, extra?: [string, string, () => void]) {
  const menu = h("div", "cellmenu typemenu");
  for (const [t, label, hint] of CELL_TYPES) {
    const it = h("div", `item${t === current ? " on" : ""}`);
    it.append(h("span", undefined, `${t === current ? "✓ " : ""}${label}`), h("span", "hint", hint));
    it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); pick(t); });
    menu.append(it);
  }
  if (extra) {
    const it = h("div", "item");
    it.append(h("span", undefined, extra[0]), h("span", "hint", extra[1]));
    it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); extra[2](); });
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
  "simp.power": "Power identity", "simp.identity": "Identity", "simp.flatten": "Flatten", "simp.sort": "Reorder", "simp.function": "Function value", "simp.function.assuming": "Function value, assuming a positive argument",
  "simp.fold-constants": "Arithmetic on constants", "simp.collect-like-terms": "Collect like terms", "simp.collect-powers": "Collect powers", "simp.collect-powers.assuming": "Collect powers, assuming the base", "simp.collect-radicals": "Collect radicals",
  "simp.radical": "Radical", "simp.exp-product": "Exponentials multiply", "expand.distribute": "Distribute", "expand.power": "Expand the power",
  "cx.euler": "Euler's formula", "cx.euler-power": "Euler's formula", "cx.arithmetic": "Complex arithmetic", "cx.i-power": "Power of i", "cx.re-im": "Real and imaginary parts",
  "cx.conjugate": "Conjugate", "cx.abs": "Modulus", "cx.exact-trig": "Exact value", "cx.power": "Complex power",
  "la.row-swap": "Swap rows", "la.row-scale": "Scale a row", "la.row-add": "Add a multiple of a row", "la.det": "Determinant", "la.mul": "Matrix product", "la.add": "Matrix sum",
  "la.scalar-mul": "Scalar multiple", "la.transpose": "Transpose", "la.pow": "Matrix power", "la.dot": "Dot product", "la.norm": "Norm", "la.conj": "Conjugate", "la.ediv": "Entrywise division", "la.emul": "Entrywise product", "la.part": "Part", "stat.total": "Total", "stat.mean": "Mean", "stat.variance": "Sample variance", "stat.stdev": "Standard deviation", "stat.min": "Minimum", "stat.max": "Maximum", "stat.median": "Median", "la.context": "Matrix context",
  "int.check": "Check by differentiating", "int.compare": "Compare with the integrand", "int.bounds": "Evaluate at the bounds", "int.table": "Table integral", "int.power": "Power rule for integrals",
  "int.variable": "Integral of the variable", "int.constant": "Integral of a constant", "int.constant-multiple": "Constant multiple", "int.sum": "Sum rule for integrals",
  "int.exponential": "Exponential integral", "int.exp-power": "Exponential of a power", "int.substitution": "Substitution", "int.linear-substitution": "Linear substitution",
  "int.by-parts": "Integration by parts", "int.trig-power": "Trigonometric power",
  "order.closure": "Closure", "order.covers": "Covers", "order.upper-bounds": "Upper bounds", "order.least": "Least upper bound",
  "order.lower-bounds": "Lower bounds", "order.greatest": "Greatest lower bound", "order.lattice": "Lattice", "order.cover": "Cover",
  "order.incomparable": "Incomparable", "order.monotone": "Monotone", "order.iterate": "Iterate", "order.fixed": "Fixed point",
  "rel.reflexive": "Reflexive", "rel.symmetric": "Symmetric", "rel.antisymmetric": "Antisymmetric", "rel.transitive": "Transitive",
  "rel.equivalence": "Equivalence relation", "rel.preorder": "Preorder", "rel.reflexive-closure": "Reflexive closure", "rel.symmetric-closure": "Symmetric closure",
  "rel.transitive-closure": "Transitive closure", "rel.kernel": "Kernel", "rel.classes": "Equivalence classes", "rel.finer": "Finer", "rel.wellfounded": "Well-founded", "rel.measure": "Measure",
  "logic.implication": "Eliminate →", "logic.biconditional": "Eliminate ↔", "logic.de-morgan": "De Morgan's law", "logic.double-negation": "Double negation",
  "logic.negate-constant": "Negate a constant", "logic.constants": "Simplify constants", "logic.distribute": "Distribute", "logic.complement": "Complementary literals", "logic.truthtable": "Truth table",
  "logic.evaluate": "Evaluate", "logic.bounded": "Check every element",
  "alg.from-order": "Table from the order", "alg.associative": "Associative", "alg.commutative": "Commutative", "alg.idempotent": "Idempotent",
  "alg.identity": "Identity element", "alg.fold": "Combine", "alg.order": "Order of a semilattice", "order.distributive": "Distributive",
  "order.complement": "Complement", "order.boolean": "Boolean lattice", "order.product": "Product order", "order.galois": "Galois connection",
  "order.closure-operator": "Closure operator", "order.concepts": "Concept lattice", "order.flow": "Information flow",
  "order.happens-before": "Happens-before", "order.clocks": "Vector clocks", "order.concurrent": "Concurrent",
  "sys.init": "Start", "sys.step": "Step", "sys.found": "Found", "sys.violated": "Violated", "sys.deadlock": "Deadlock", "sys.reach": "Reachable states",
  "sys.invariant": "Invariant", "sys.unreachable": "Unreachable", "sys.inductive": "Inductive", "sys.cti": "Counterexample to induction",
  "sys.ctl": "CTL", "sys.iterate": "Iterate", "sys.fixed": "Fixed point", "sys.cycle": "Cycle", "sys.lasso": "Fair loop",
  "sys.eventually": "Eventually", "sys.refines": "Refinement",
  "order.inner": "Inner call", "sys.inner": "Inner call",
  "trs.step": "Rewrite", "trs.decrease": "Decreases", "trs.critical": "Critical pair",
  "crdt.update": "Update", "crdt.merge": "Merge", "crdt.send": "Send", "crdt.converged": "Converged", "crdt.diverged": "Not converged",
  "lambda.eta": "η-reduction", "lambda.elided": "Steps not shown", "lambda.alpha": "Rename bound variables", "lambda.alpha-eq": "Compare", "lambda.subst": "Substitute",
  "lambda.fv": "Free variables", "lambda.db": "De Bruijn indices",
  "stlc.var": "Var", "stlc.abs": "→I (abstraction)", "stlc.app": "→E (application)", "stlc.constraints": "Type equations",
  "stlc.split": "Split an arrow", "stlc.unify": "Unify", "stlc.principal": "Principal type",
  "cmd.rref": "Row reduce", "cmd.integrate": "Integrate", "cmd.expand": "Expand", "cmd.subst": "Substitute", "cmd.simplify": "Simplify", "cmd.sum": "Sum", "cmd.exptotrig": "Euler's formula",
  "cmd.N": "Numerical value", "order.divisors": "Divisors", "order.subsets": "Subsets",
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

/** A step whose term prints the same before and after — a one-factor product unwrapped, `x·1 = x`
 *  under a fraction bar — is part of the derivation but shows nothing happening, so the work list
 *  folds it. The panel's trail keeps it, unnumbered, and the engine's step indices are unchanged.
 *  A step with nested work is always shown. */
function printsUnchanged(st: Step): boolean {
  return !st.sub && !!st.beforeRendered && !!st.afterRendered
    && stripPaths(st.beforeRendered.latex) === stripPaths(st.afterRendered.latex);
}
/** The number each step's row shows (1, 2, … over the shown steps); `undefined` for a folded step. */
function stepNumbers(steps: Step[]): (number | undefined)[] {
  let k = 0;
  return steps.map((st) => printsUnchanged(st) ? undefined : ++k);
}
const shownSteps = (steps: Step[] | undefined): number => (steps ?? []).filter((st) => !printsUnchanged(st)).length;
/** How many steps a cell's work shows: from its steps once they are here, from the outline before
 *  (the engine marks the steps that print the same `quiet`, by the comparison `printsUnchanged` makes). */
const workCount = (cell: Cell): number =>
  cell.steps?.length ? shownSteps(cell.steps) : (cell.outline ?? []).filter((st) => !st.quiet).length;

/** How many of a cell's shown steps are on the page: all of them, unless the cell is stepped through. */
function revealedCount(cell: Cell): number {
  if (cell.stepwise === undefined) return Infinity;
  if (cell.revealedFor !== cell.src) { cell.revealed = cell.stepwise; cell.revealedFor = cell.src; }
  return cell.revealed ?? cell.stepwise;
}
/** Whether a stepped-through cell still holds its answer back: steps remain to reveal. */
const answerHeld = (cell: Cell): boolean => cell.stepwise !== undefined && !cell.error && revealedCount(cell) < workCount(cell);
/** Reveal a stepped-through cell's steps up to `n` (Infinity: all), keeping the focus on its controls. */
function revealSteps(cell: Cell, n: number) {
  const had = !!cell.el?.contains(document.activeElement) && !!document.activeElement?.closest(".stepnext, .outheld");
  revealedCount(cell);
  cell.revealed = Math.max(0, Math.min(n, workCount(cell)));
  renderCellBody(cell);
  if (had) cell.el?.querySelector<HTMLElement>(".stepnext [data-next], .stepnext [data-again]")?.focus();
}
/** Under a stepped-through cell's revealed steps: the next one, all of them, or (once all show) again. */
function stepControls(cell: Cell): HTMLElement {
  const row = h("div", "stepnext");
  const n = workCount(cell), k = revealedCount(cell);
  const btn = (label: string, title: string, act: () => void, key?: string) => {
    const b = asButton(h("span", "stepbtn", label), title); b.title = title;
    if (key) b.dataset[key] = "";
    b.addEventListener("mousedown", (e) => e.preventDefault());
    b.addEventListener("click", (ev) => { ev.stopPropagation(); act(); });
    return b;
  };
  if (k < n) {
    row.append(btn(k === 0 ? "▸ First step" : "▸ Next step", "Show the next step (try to say what it is first)", () => revealSteps(cell, k + 1), "next"),
      h("span", "stepof", `${k} of ${n} step${n === 1 ? "" : "s"} shown`),
      btn("Show all", "Show every step and the answer", () => revealSteps(cell, Infinity)));
  } else {
    row.append(h("span", "stepof", `All ${n} step${n === 1 ? "" : "s"} shown`),
      btn("↺ Step through again", "Hide the steps and the answer again", () => revealSteps(cell, cell.stepwise ?? 0), "again"));
  }
  return row;
}
/** Make a cell one to step through (from `from` steps shown), or show its work at once again. */
function setStepwise(cell: Cell, from: number | undefined) {
  if (from === undefined) { delete cell.stepwise; delete cell.revealed; delete cell.revealedFor; }
  else { cell.stepwise = from; cell.showWork = true; cell.revealed = from; cell.revealedFor = cell.src; }
  renderCellBody(cell); renderChrome(); autosave();
}

/** The fetch of a cell's steps under way, so opening the work twice asks once. */
const WORK_LOADS = new WeakMap<Cell, Promise<void>>();
/** Why a cell's steps could not be fetched, until the cell is evaluated again (not saved). */
const WORK_FAILED = new WeakMap<Cell, string>();
/** Fetch the steps of a cell whose evaluation sent only their outline. The engine keeps every cell's
 *  derivation in the session; it sends the terms now. A reply for an evaluation the cell has since
 *  replaced (its outline changed while the fetch was out) is dropped. */
function loadWork(cell: Cell): Promise<void> {
  if (cell.steps?.length || !cell.outline?.length) return Promise.resolve();
  const pending = WORK_LOADS.get(cell); if (pending) return pending;
  const outline = cell.outline, c = client;
  const p = (async () => {
    try {
      if (!c) throw new Error("the engine is not running");
      log("rpc", `engine.steps ${cell.id}`);
      const r = await c.call("engine.steps", { sessionId, cellId: cell.id, paths: true });
      if (cell.outline !== outline) return;
      cell.steps = r.derivation.steps; delete cell.outline;
      WORK_FAILED.delete(cell);
      queueMicrotask(autosave);
    } catch (e) {
      if (cell.outline !== outline) return;
      const d = currentDoc();
      WORK_FAILED.set(cell, d && !d.hydrated ? "Run the notebook first: the engine has the work of what it has evaluated since the notebook was opened."
        : `Could not fetch the work: ${e instanceof Error ? e.message : String(e)}`);
    } finally { WORK_LOADS.delete(cell); }
  })();
  WORK_LOADS.set(cell, p);
  return p;
}

/** What each step changed, in place: the subterms a step rewrote (`before` against `after`) are
 *  tinted in its row, and hovering one shows `old → new`, cut from the step's own renderings of
 *  `before` and `after` (the row above is not always `before`: the pipeline flattens and reorders
 *  silently between recorded steps). A change at the root is the whole line: no tint. */
function markChanges(rows: HTMLElement[], d: Derivation) {
  d.steps.forEach((st, n) => {
    const el = rows[n]?.querySelector<HTMLElement>(".el"); if (!el) return;
    const beforeLatex = st.beforeRendered?.latex ?? (n === 0 ? d.inputRendered?.latex : undefined);
    const tinted = new Set<string>();
    for (const changed of changedPaths(st.before, st.after)) {
      // a subterm the printer does not show on its own (the 2 and 3/2 of 2^(3/2), shown as 2√2)
      // tints the nearest ancestor it does show
      let p = changed, found: HTMLElement | null = null;
      for (; p.length; p = p.slice(0, -1)) if ((found = el.querySelector<HTMLElement>(`[data-path="${p.join(".")}"]`))) break;
      const now = found;
      if (!now || tinted.has(p.join("."))) continue;
      tinted.add(p.join("."));
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

// --- The notebook's Lean file: its Lean cells, and each Lean exercise as its statement and its proof ---

/** A cell of the notebook's Lean file: a Lean cell, or a Lean exercise (with a statement to prove). */
const isLeanCell = (c: Cell) => c.type === "lean" || (c.type === "exercise" && !!c.lean && !!c.src.trim());
/** The proof a Lean exercise starts with when the author gives none. */
const LEAN_START = "  sorry";
/** The ids of the parts of the Lean file no view edits: a course's prelude, an exercise's statement. */
const PRELUDE_ID = "~prelude", STMT_SUFFIX = "~stmt";
/** The notebook's Lean file, cell by cell: the course's earlier lessons first (a project with a Lean
 *  prelude), then the Lean cells and the Lean exercises in order, each exercise its statement then the
 *  reader's proof. An exercise's statement ends `:= by`, so the proof below it is the declaration's own. */
function leanDocCells(): { id: string; src: string; fixed?: boolean }[] {
  const out: { id: string; src: string; fixed?: boolean }[] = [];
  for (const c of S.cells) {
    if (c.type === "lean") out.push({ id: c.id, src: c.src });
    else if (isLeanCell(c)) out.push({ id: `${c.id}${STMT_SUFFIX}`, src: c.src, fixed: true }, { id: c.id, src: c.attempt ?? c.leanStart ?? LEAN_START });
  }
  const pre = currentDoc()?.leanPrelude;
  if (pre && out.length) out.unshift({ id: PRELUDE_ID, src: pre, fixed: true });
  return out;
}
/** Whether Lean had finished checking the file when it last reported. */
let leanWasChecked = false;
/** Errors in a course's prelude are the course's, not the reader's: logged once per set of messages. */
let lastPreludeErrors = "";
function preludeMessages(ms: LeanMessage[]) {
  const errs = ms.filter((m) => m.severity === "error").map((m) => `prelude ${m.line}:${m.column} ${m.message}`).join("\n");
  if (errs && errs !== lastPreludeErrors) log("err", errs);
  lastPreludeErrors = errs;
}
/** Settle a Lean exercise's verdict from what Lean says, once Lean has checked the file as it is: proved
 *  when neither the statement nor the proof has an error and nothing was left as `sorry`. Returns whether
 *  the verdict changed. */
function leanVerdict(c: Cell): boolean {
  if (!leanChecked()) return false;
  const proof = c.attempt ?? c.leanStart ?? LEAN_START;
  const ms = [...(c.leanStmtMessages ?? []), ...(c.leanMessages ?? [])];
  const err = ms.find((m) => m.severity === "error");
  const sorry = ms.some((m) => m.severity === "warning" && /sorry/.test(m.message)) || /\b(sorry|admit)\b/.test(proof);
  const v: Verdict = !proof.trim() || sorry
    ? { equivalent: false, error: { message: !proof.trim() ? "write a proof" : "the proof still has a sorry" } }
    : err ? { equivalent: false, error: { message: "Lean reports an error, above" } } : { equivalent: true };
  if (JSON.stringify(v) === JSON.stringify(c.verdict)) return false;
  c.verdict = v;
  if (docOf(c) === currentDoc()) queueMicrotask(recordProgress);
  renderSidebar(); autosave();
  return true;
}

/** Re-render everything below a cell's input, leaving the input element untouched. */
/** What Lean cells tell the notebook (lean-cells.ts): typing in a view, Lean's messages, Lean's state. */
function leanHooks() {
  return {
    dark: S.theme !== "light",
    onSource: (id: string, src: string) => {
      const c = S.cells.find((x) => x.id === id); if (!c) return;
      // a Lean exercise's view is its proof; its statement is not the reader's to change
      if (c.type === "exercise") c.attempt = src; else c.src = src;
      renderSidebar(); renderTabs(); autosave();
    },
    onMessages: (id: string, ms: LeanMessage[]) => {
      if (id === PRELUDE_ID) { preludeMessages(ms); return; }
      const stmt = id.endsWith(STMT_SUFFIX);
      const c = S.cells.find((x) => x.id === (stmt ? id.slice(0, -STMT_SUFFIX.length) : id)); if (!c) return;
      if (stmt) c.leanStmtMessages = ms; else c.leanMessages = ms;
      if (c.type === "exercise") leanVerdict(c);
      renderCellBody(c);
    },
    onChecked: () => {
      // every Lean exercise says "checking" while Lean is: each is redrawn when Lean starts on the file, and
      // whenever it reports the file as it is now checked (a small edit can go from checked to checked)
      const now = leanChecked(), started = !now && leanWasChecked;
      leanWasChecked = now;
      for (const c of S.cells) if (c.type === "exercise" && c.lean && (leanVerdict(c) || now || started)) renderCellBody(c);
    },
    onState: () => { renderPanelHead(); for (const c of S.cells) if (isLeanCell(c)) renderCellBody(c); },
    onProgress: () => {
      // the status is in the first Lean cell: updated in place while it shows, re-rendered when it comes or goes
      const first = S.cells.find(isLeanCell);
      const old = first?.el?.querySelector(".leanstatus");
      const next = leanStatus();
      if (old && next) old.replaceWith(next);
      else if (first && (old || next)) renderCellBody(first);
    },
  };
}

const MB = (n: number) => (n / 1e6).toFixed(n < 10e6 ? 1 : 0);
/** What Lean is doing while it loads, with a progress bar; null once it has checked the notebook. */
function leanStatus(): HTMLElement | null {
  const st = leanState(), p = leanProgress();
  if (st === "off" || st === "isolating" || st === "failed" || !p) return null;
  const pct = p.phase === "download" && p.total > 0 ? Math.min(100, Math.round((p.loaded / p.total) * 100)) : null;
  const text = p.phase === "editor" ? "Loading the Lean editor…"
    : p.phase === "starting" ? "Starting Lean…"
    : p.phase === "download" ? (p.total > 0
      ? `Downloading Lean and its library: ${MB(p.loaded)} of ${MB(p.total)} MB. Only the first time: your browser keeps it.`
      : "Downloading Lean and its library…")
    : "Lean is loading its library and checking the notebook…";
  const box = h("div", "leanstatus");
  const bar = h("div", `leanbar${pct === null ? " busy" : ""}`);
  bar.setAttribute("role", "progressbar");
  bar.setAttribute("aria-label", "Loading Lean");
  if (pct !== null) { bar.setAttribute("aria-valuemin", "0"); bar.setAttribute("aria-valuemax", "100"); bar.setAttribute("aria-valuenow", String(pct)); }
  const fill = h("div");
  if (pct !== null) fill.style.width = `${pct}%`;
  bar.append(fill);
  box.append(h("div", "leanstate", text), bar);
  return box;
}

/** A Lean cell's output: what Lean says about its lines (an #eval's value, errors, warnings); the goals
 *  at the cursor are in the panel's Lean goals tab. */
function renderLeanBody(cell: Cell) {
  const el = cell.el; if (!el) return;
  const body = el.querySelector(".cellbody") as HTMLElement;
  body.innerHTML = "";
  const st = leanState();
  if (st === "failed" || st === "isolating") {
    body.append(h("div", `leanstate ${st}`,
      st === "failed" ? `Lean did not start: ${leanFailure()}` : "Preparing the page for Lean: it reloads once."));
  } else if (S.cells.find(isLeanCell) === cell) {
    const status = leanStatus();
    if (status) body.append(status);
  }
  for (const m of cell.leanMessages ?? []) {
    const row = h("div", `leanmsg ${m.severity}`);
    row.append(h("span", "where", `${m.line}:${m.column}`), h("span", "text", m.message));
    body.append(row);
  }
  appendMore(cell, el.querySelector(".cellacts")!);
}

function renderCellBody(cell: Cell) {
  const el = cell.el; if (!el) return;
  hideDiffTip();
  if (cell.type === "markdown") return renderMdCell(cell);
  if (cell.type === "section") return appendMore(cell, el.querySelector(".cellacts")!);
  if (cell.type === "lean") return renderLeanBody(cell);
  const exercise = cell.type === "exercise";
  if (exercise) renderExercise(cell);
  // an exercise shows its question's work and value only as the solution, when the reader asks
  const solving = !exercise || (!!cell.solution && !cell.lean);
  el.classList.toggle("done", !!cell.label);
  const busy = cell.queued || S.running === cell;   // Mathematica's In[*]: waiting or being evaluated
  el.classList.toggle("running", busy);
  if (!exercise) el.querySelector(".prompt")!.textContent = `In[${busy ? "*" : cell.label ?? " "}]:=`;
  const mid = el.querySelector(".mid")!;
  const body = mid.querySelector(".cellbody") as HTMLElement;
  body.innerHTML = "";

  // a visual input already shows what was typed, and a `%` in it as the output it names
  if (!exercise && cell.echoLatex && S.showEcho && !isVisual(cell)) {
    const echo = h("div", "echo");
    echo.innerHTML = tex(cell.echoLatex, true);
    wireTerm(echo, cell, { kind: "input" });
    body.append(echo);
  }


  if (cell.error) {
    const err = h("div", "cellerr", cell.error.message);
    // a visual input marks the error on the symbols themselves; text gets the source with carets
    if (cell.error.span && cell.mi) cell.mi.markError(cell.error.span);
    else if (cell.error.span) {
      const { start, end } = cell.error.span;
      err.append(h("span", "caret", `${cell.src}\n${" ".repeat(start)}${"^".repeat(Math.max(1, end - start))}`));
    }
    body.append(err);
  }
  if (busy && cell.askSteps?.length) body.append(askProgress(cell));
  if (cell.error && cell.askTrail?.length) body.append(askTrail(cell.askTrail));

  if (solving && cell.showWork && !cell.steps?.length && workCount(cell)) {
    // the outline is here, the terms are not yet: fetch them, then draw the work
    const failed = WORK_FAILED.get(cell);
    body.append(h("div", "work pending", failed ?? "Fetching the work…"));
    if (!failed) void loadWork(cell).then(() => { if (cell.el) renderCellBody(cell); });
  }
  if (solving && cell.showWork && cell.steps && shownSteps(cell.steps)) {
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
        // a step on a table's worth of numbers shows the matrix as the output does: its first rows, its last, and the count
        el.innerHTML = tex(abridgeMatrix(shown.latex), true);
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
      // a top-level step is selected by a click anywhere on its row, as its whole result (its part of a
      // state graph is marked); a click on a part of the result selects that part instead
      if (term) row.addEventListener("click", () => { void explain(cell, term, []); });
      return row;
    };
    // Nested derivations (rref's row operations, integrate's finder and its check) render below
    // their step, indented one level per depth and numbered 1.2, 1.2.3, …
    const renderSub = (st: Step, label: string, top: number, depth: number) => {
      // an entrywise step's nested work is one step per entry of a matrix, often hundreds: it opens on request
      if (st.rule === "la.entrywise" && st.sub && !cell.openEntries?.has(label)) {
        const n = st.sub.steps.length;
        const more = asButton(h("div", "step sub more", `▸ ${n} step${n === 1 ? "" : "s"}, entry by entry`), "Show each entry's steps");
        more.style.marginLeft = `${26 * depth}px`;
        more.addEventListener("click", (ev) => { ev.stopPropagation(); (cell.openEntries ??= new Set()).add(label); renderCellBody(cell); });
        work.append(more);
        return;
      }
      const rows: HTMLElement[] = [];   // by step index; a folded step has none
      const nums = stepNumbers(st.sub?.steps ?? []);
      st.sub?.steps.forEach((sub, k) => {
        if (nums[k] === undefined) return;
        const l = `${label}.${nums[k]}`;
        const srow = stepRow(sub, l, statusOf(sub, cellComplex(cell)), undefined, { steps: st.sub!.steps, index: k, top });
        srow.classList.add("sub");
        srow.style.marginLeft = `${26 * depth}px`;
        srow.title = sub.explanation.replace(/\$/g, "");
        srow.addEventListener("click", (ev) => { ev.stopPropagation(); selectSubStep(cell, st.sub!.steps, k, l, top); });
        work.append(srow);
        rows[k] = srow;
        renderSub(sub, l, top, depth + 1);
      });
      if (st.sub) markChanges(rows, st.sub);
    };
    const rows: HTMLElement[] = [];   // by step index, which is what `engine.explain` takes; a folded step has none
    const nums = stepNumbers(cell.steps);
    const upTo = revealedCount(cell);
    cell.steps.forEach((st, n) => {
      if (nums[n] === undefined || nums[n]! > upTo) return;
      const row = stepRow(st, String(nums[n]), statusOf(st, cellComplex(cell)), { kind: "step", index: n });
      row.addEventListener("click", () => void explain(cell, { kind: "step", index: n }, []));
      work.append(row);
      rows[n] = row;
      renderSub(st, String(nums[n]), n, 1);
    });
    // the cell keeps the steps, not the derivation: its input is the first step's before, rendered as the echo
    const first = cell.steps[0]!;
    markChanges(rows, { input: first.before, steps: cell.steps, output: cell.steps[cell.steps.length - 1]!.after, ...(cell.echoLatex ? { inputRendered: { text: "", latex: cell.echoLatex } } : {}) });
    if (cell.stepwise !== undefined) work.append(stepControls(cell));
    body.append(work);
  }

  const old = el.querySelector(".outrow"); old?.remove();
  if (solving && (cell.outLatex || cell.file)) {
    const out = h("div", "outrow");
    out.append(h("div", "prompt", exercise ? "Answer" : `Out[${cell.label}]=`));
    const val = h("div", "outval");
    if (answerHeld(cell)) {
      // stepping through: the answer is the last step's, and waits for it
      const held = asButton(h("span", "outheld", "?"), "Reveal the answer");
      held.title = "The answer shows after the last step. Click to reveal every step and the answer.";
      held.addEventListener("click", () => { revealSteps(cell, Infinity); });
      val.append(held);
    } else if (cell.hasse) {
      const box = h("div", "plotbox");
      box.append(hasseSvg(cell.hasse));
      const cap = h("div", "plotcap", cell.summary ?? "");
      val.classList.add("isplot");
      val.append(box, cap);
    } else if (cell.file) {
      const f = fileOf(cell);
      // what the cell calls the file, for its suggestions: its name, or its output's number
      const x = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)/.exec(cell.src)?.[1] ?? (/^\s*([A-Za-z_][A-Za-z0-9_]*)\s*$/.exec(cell.src)?.[1] ?? (cell.label !== null ? `%${cell.label}` : cell.src.trim()));
      if (f) {
        const suggest = S.suggestions && !cell.noSuggest ? {
          run: (code: string) => {
            const at = S.cells.indexOf(cell) + 1;
            const c = freshCell(code, "math");
            S.cells.splice(at, 0, c);
            renderCells(); renderSidebar(); autosave();
            void runCell(c);
          },
          dismiss: () => { cell.noSuggest = true; renderCellBody(cell); autosave(); },
        } : undefined;
        const { body, cap } = fileView(f, x, cell.form, suggest);
        val.append(body, cap);
      } else {
        // a saved output whose import this page has not fetched yet
        const card = h("div", "filecard");
        card.append(h("span", "fileicon", "⎙"), h("span", "filename", cell.file.name), h("span", "filemeta", `${mimeLabel(cell.file.mime)}, ${fmtSize(cell.file.size)} — run the cell to load it`));
        val.append(card);
      }
      val.classList.add("isplot");
    } else if (cell.manip) {
      val.classList.add("isplot");
      val.append(manipBox(cell));
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
        cap.innerHTML = tex(cell.outLatex ?? "", true);
        wireTerm(cap, cell, { kind: "output" });
      }
      val.classList.add("isplot");
      val.append(box, cap);
    } else if (S.deBruijn && cell.outDeBruijn) {
      val.innerHTML = tex(cell.outDeBruijn, true);
    } else if (cell.form === "input") {
      val.append(h("code", "outtext", cell.outText ?? ""));
    } else if (formOf(cell) === "data") {
      // a matrix to read rather than typeset: rows and columns numbered, rows added as they scroll in
      const rows = matrixEntries(cell.outLatex!)!;
      val.dataset["term"] = termKey({ kind: "output" });
      // a column of numerals aligns right, as a CSV's does
      const numeral = (e: string) => /^-?\d+(\.\d+)?$/.test(stripPaths(e).trim());
      const numeric = rows[0]!.map((_, c) => rows.every((r) => numeral(r[c]!)));
      val.append(dataGrid({ rows: rows.length, cols: rows[0]!.length, cell: (r, c) => tex(rows[r]![c]!, true), html: true, numeric, label: `a ${rows.length} by ${rows[0]!.length} matrix` },
        (trs) => trs.forEach((tr) => wirePaths(tr, cell, { kind: "output" }))));
      val.append(h("div", "plotcap", `${rows.length} × ${rows[0]!.length} matrix`));
      val.classList.add("isplot");
    } else {
      val.innerHTML = tex(abridgeMatrix(formLatex(cell.outLatex ?? "", cell.form)), true);
      wireTerm(val, cell, { kind: "output" });
    }
    // the output form: a per-cell choice of typesetting, like Mathematica's //MatrixForm
    if (!cell.hasse && !cell.plot && (!cell.file || tabularCell(cell)) && !answerHeld(cell)) {
      const forms = formsFor(cell);
      const fs = document.createElement("select"); fs.className = "formsel"; fs.title = "Output form"; fs.setAttribute("aria-label", "Output form");
      for (const [v, label] of forms) { const o = document.createElement("option"); o.value = v; o.textContent = label; o.selected = formOf(cell) === v; fs.append(o); }
      fs.addEventListener("mousedown", (e) => e.stopPropagation());
      fs.addEventListener("change", () => { if (fs.value === forms[0]![0]) delete cell.form; else cell.form = fs.value; renderCellBody(cell); autosave(); });
      out.querySelector(".prompt")!.append(fs);
    }
    // a reading or a summary says the answer, so it waits with it
    if (cell.reading && !answerHeld(cell)) { const rd = h("span", "reading", `≡ ${cell.reading}`); rd.title = "What the normal form encodes"; val.append(rd); }
    if (cell.summary && !cell.hasse && !answerHeld(cell)) { const rd = h("span", "reading", cell.summary); val.append(rd); }
    for (const box of cellVisuals(cell)) val.append(box);
    out.append(val, h("div", "brk"));
    el.append(out);
    if (cell.ask && ASK_CELL.test(cell.src)) out.append(h("div"), askInfo(cell, !!ASK_CELL.exec(cell.src)?.[1]), h("div"));
  }
  markSelection();
  renderStale(cell);

  // per-cell actions beyond Run exist only once there is output
  const acts = el.querySelector(".cellacts")!;
  if (exercise) { exerciseActs(cell, acts); return; }
  while (acts.childElementCount > 1) acts.lastElementChild!.remove();
  if (workCount(cell) && cell.stepwise === undefined) {
    const tw = asButton(h("span", undefined, cell.showWork ? "▾ Hide work" : `▸ Work (${workCount(cell)})`));
    tw.setAttribute("aria-expanded", String(cell.showWork));
    tw.addEventListener("mousedown", (e) => e.preventDefault());
    tw.addEventListener("click", () => {
      const had = document.activeElement === tw;
      cell.showWork = !cell.showWork; renderCellBody(cell); renderChrome(); autosave();
      if (had) cell.el?.querySelector<HTMLElement>(".cellacts [aria-expanded]")?.focus();   // the button was rebuilt
    });
    acts.append(tw);
  }
  if (cell.ask && ASK_CELL.test(cell.src) && !busy) {
    const again = (how: "again" | "search") => { askAgain.set(cell, how); void runCell(cell); };
    if (cell.ask.via === "knowledge" || cell.ask.via === "memory") {
      const chk = asButton(h("span", undefined, "⌕ Check with a search")); chk.title = "Look for a source for this answer";
      chk.addEventListener("click", () => again("search"));
      acts.append(chk);
    }
    const re = asButton(h("span", undefined, "↻ Look up again")); re.title = "Ask again instead of using the saved answer";
    re.addEventListener("click", () => again("again"));
    acts.append(re);
  }
  appendMore(cell, acts);
}

// --- `?` lookups: what the answer is and where it came from (ask-cells.ts) -------------------------

const httpUrl = (u: string) => /^https?:\/\//i.test(u);

/** A lookup under way: the steps done (✓), then the current one with its seconds and any detail. */
function askProgress(cell: Cell): HTMLElement {
  const box = h("div", "askprog");
  box.setAttribute("aria-live", "polite");
  const steps = cell.askSteps ?? [];
  const from = Math.max(0, steps.length - 6);
  steps.slice(from).forEach((st, k) => {
    const now = from + k === steps.length - 1;
    const row = h("div", now ? "now" : "done", `${now ? "" : "✓ "}${st.text}${now ? "…" : ""}`);
    if (now) row.append(h("span", "secs"), h("span", "detail"));
    box.append(row);
  });
  queueMicrotask(tickAsk);
  return box;
}

/** Bring the running lookup's seconds and detail up to date (every half second while one runs). */
function tickAsk() {
  const cell = S.running, st = cell?.askSteps?.[cell.askSteps.length - 1];
  const row = cell?.el?.querySelector(".askprog .now");
  if (!cell || !st || !row) return;
  const secs = Math.floor((performance.now() - st.at) / 1000);
  row.querySelector(".secs")!.textContent = secs >= 1 ? ` ${secs} s` : "";
  row.querySelector(".detail")!.textContent = cell.askDetail ? ` · ${cell.askDetail}` : "";
}
setInterval(() => { if (askAbort) tickAsk(); }, 500);

/** The lines a lookup's trail shows under "How this was found" (or under its error). */
function askTrail(trail: string[], open = false): HTMLElement {
  const d = document.createElement("details"); d.className = "asktrail"; d.open = open;
  d.append(h("summary", undefined, "How this was found"));
  const ol = h("ol");
  for (const line of trail) { const li = h("li"); li.append(inlineMath(line)); ol.append(li); }
  d.append(ol);
  return d;
}

/** One entry of the answer's grid, as the engine text wrote it. */
function askEntry(source: string, r: number, c: number): string {
  const rows = source.replace(/^\[|\]$/g, "").split(";");
  return rows[r]?.split(",")[c]?.trim() ?? "";
}

/** Under a `?` cell's output: where the answer came from, what its parts are, and anything to check. */
function askInfo(cell: Cell, bound: boolean): HTMLElement {
  const a = cell.ask!;
  const box = h("div", "askinfo");
  const VIA: Record<AskResult["via"], [string, string]> = {
    table: ["ok", "Copied from a table"],
    text: [a.flagged.length ? "warn" : "ok", a.shape === "formula" ? "A formula the source states" : "Quoted from the source"],
    search: [a.flagged.length ? "warn" : "ok", "Found by the model's web search"],
    knowledge: ["kn", "From the model's knowledge"],
    memory: ["warn", "From the model's memory: unsourced"],
  };
  const [cls, label] = VIA[a.via];
  const head = h("div", "askhead");
  // asking again failed: say so where the answer is, not only in a passing notice
  if (cell.askFailed) box.append(h("div", "asknote warn", `The last lookup failed, so this is the earlier answer: ${cell.askFailed}`));
  head.append(h("span", `askbadge ${cls}`, label));
  const cites = a.cites.filter((c) => httpUrl(c.url));
  cites.forEach((c, i) => {
    head.append(i ? ", " : " · ");
    const l = document.createElement("a"); l.href = c.url; l.target = "_blank"; l.rel = "noopener noreferrer"; l.textContent = c.title;
    head.append(l);
  });
  head.append(h("span", "askwhen", ` · ${a.model}, ${a.at}`));
  box.append(head);
  const line = (k: string, v: Node | string) => { const d = h("div", "askline"); d.append(h("span", "askkey", k), v); box.append(d); };
  if (a.shape === "formula") {
    if (a.latex) { const t = h("span"); t.innerHTML = tex(a.latex); line(a.via === "text" ? "The source writes" : "In LaTeX", t); }
    if (a.vars?.length) {
      const w = h("span");
      a.vars.forEach((v, i) => { w.append(i ? "; " : "", inlineMath(`$${v.name}$`), ` ${v.meaning}`); });
      line("Where", w);
    }
    if (!bound && a.params?.length) {
      const u = h("span");
      u.append(h("code", undefined, `let f = ?${a.question}`), h("span", "askmut", ` defines f(${a.params.join(", ")})`));
      line("To use it", u);
    }
  } else {
    if (a.columns.length > 1 || a.shape === "table") line("Columns", a.columns.join(" · "));
    else if (a.columns[0]) line(a.shape === "list" ? "Entries" : "Value", a.columns[0]);
    if (a.rowsAre) line("Rows", a.rowsAre);
    if (a.rowLabels?.length) line("Row names", a.rowLabels.length > 12 ? `${a.rowLabels.slice(0, 12).join(", ")}, … (${a.rowLabels.length})` : a.rowLabels.join(", "));
    if (a.flagged.length && a.via !== "memory") {
      const shown = a.flagged.slice(0, 6).map(([r, c]) => `row ${r + 1}, column ${c + 1} (${askEntry(a.source, r, c)})`);
      line("⚠ Not in the source", `${shown.join("; ")}${a.flagged.length > 6 ? `; … ${a.flagged.length - 6} more` : ""}`);
    }
  }
  for (const n of a.notes) box.append(h("div", `asknote${a.via === "memory" || a.flagged.length ? " warn" : ""}`, n));
  if (a.trail.length) box.append(askTrail(a.trail));
  return box;
}

/** Before a lookup's first search: what would be sent, and to where. A stop closes it (as a no). */
function confirmSearch(signal: AbortSignal): Promise<boolean> {
  return new Promise((resolve) => {
    const s = askSettings();
    const host = (u: string) => { try { return new URL(u.replace("{q}", "")).host; } catch { return u; } };
    const where = [s.wikipedia ? "Wikipedia" : "", s.searchUrl.trim() ? host(s.searchUrl.trim()) : ""].filter(Boolean).join(" and ");
    closeModal();
    const box = h("div", "modal");
    const card = h("div", "modalcard");
    card.setAttribute("role", "dialog"); card.setAttribute("aria-modal", "true"); card.setAttribute("aria-label", "Search for this?");
    card.append(h("h3", undefined, "Search for this?"),
      ...(s.backend === "openrouter" ? [
        h("p", undefined, `This question needs data the model should not answer from memory, so ChalkMath would ${s.openrouterWeb ? "have the model search the web through OpenRouter" : `search ${where} and send the pages it finds to the model`}.`),
        h("p", undefined, "What leaves this computer: your question (and the pages read) go to OpenRouter and the model's provider, on your OpenRouter account. Not your notebook."),
      ] : [
        h("p", undefined, `This question needs data the model should not answer from memory, so ChalkMath would search ${where} and read the pages it finds.`),
        h("p", undefined, "What leaves this computer: the search terms the model writes from your question. Not your notebook, and nothing else you typed. The model runs here."),
      ]),
      h("p", "muted", "Asked once. Sources and the model are in Run › Lookup settings."));
    const foot = h("div", "modalfoot");
    const no = h("button", undefined, "Don't search");
    const yes = h("button", "primary", "Search");
    foot.append(h("div", "spacer"), no, yes);
    card.append(foot);
    box.append(card);
    let answer = false;
    modalClosed = () => resolve(answer);
    no.addEventListener("click", () => closeModal());
    yes.addEventListener("click", () => { answer = true; closeModal(); });
    box.addEventListener("click", (ev) => { if (ev.target === box) closeModal(); });
    mountModal(box);
    signal.addEventListener("abort", () => { if (box.isConnected) closeModal(); }, { once: true });
    yes.focus();
  });
}

/** Run › Lookup settings: the model, the sources, and whether the model may answer itself. */
async function showAskSettings() {
  const s = askSettings();
  const st = await backendStatus();
  const form = h("div", "askform");
  /** A setting; `only` names the models it belongs to (it is hidden for the others). */
  const shown: [HTMLElement, string[]][] = [];
  const row = (label: string, input: HTMLElement, hint?: string, only?: string[]) => {
    const l = document.createElement("label"); l.className = "askrow";
    l.append(h("span", "asklab", label), input);
    if (hint) l.append(h("span", "askhint", hint));
    form.append(l);
    if (only) shown.push([l, only]);
  };
  const sel = (opts: [string, string][], v: string) => {
    const e = document.createElement("select");
    for (const [val, lab] of opts) { const o = document.createElement("option"); o.value = val; o.textContent = lab; o.selected = val === v; e.append(o); }
    return e;
  };
  const text = (v: string, ph: string) => { const e = document.createElement("input"); e.type = "text"; e.value = v; e.placeholder = ph; e.spellcheck = false; return e; };
  const check = (v: boolean) => { const e = document.createElement("input"); e.type = "checkbox"; e.checked = v; return e; };
  const backend = sel([["auto", "Automatic: Chrome's built-in model, else WebGPU"], ["chrome", "Chrome's built-in model (Gemini Nano)"],
    ["webllm", "A WebGPU model, downloaded once"], ["ollama", "Ollama, on this computer"], ["openrouter", "OpenRouter: a cloud model, on your account"]], s.backend);
  row("Model", backend, `This browser: ${st.chrome ? "has Chrome's built-in model" : "no built-in model"}; ${st.webgpu ? "WebGPU available" : "no WebGPU"}.`);
  const model = sel(WEBGPU_MODELS, s.model);
  row("WebGPU model", model, "Downloaded from Hugging Face the first time it is used, then kept by the browser. It has to fit in the graphics card's own memory.", ["auto", "webllm"]);
  const ollamaUrl = text(s.ollamaUrl, "http://localhost:11434");
  row("Ollama address", ollamaUrl, `Start Ollama so it lets this page call it: OLLAMA_ORIGINS=${location.origin} ollama serve. Chrome may ask to allow this page to reach devices on your network.`, ["ollama"]);
  const ollamaModel = text(s.ollamaModel, "gemma4:e2b");
  const known = document.createElement("datalist"); known.id = "ollamamodels";
  ollamaModel.setAttribute("list", known.id);
  row("Ollama model", ollamaModel, "A model Ollama has (ollama pull gemma4:e2b). Larger models read pages better and answer more slowly.", ["ollama"]);
  form.append(known);
  const fillModels = async () => {
    const names = await ollamaModels(ollamaUrl.value.trim() || "http://localhost:11434");
    known.replaceChildren(...(names ?? []).map((n) => { const o = document.createElement("option"); o.value = n; return o; }));
  };
  if (s.backend === "ollama") void fillModels();
  ollamaUrl.addEventListener("change", () => void fillModels());
  backend.addEventListener("change", () => { if (backend.value === "ollama") void fillModels(); });
  // OpenRouter: signing in fetches a key, kept in this browser; the model is any that takes a schema
  const orStatus = h("span");
  let orKey = s.openrouterKey, signedOut = false;
  const showKey = () => { orStatus.textContent = orKey ? `Signed in (key …${orKey.slice(-4)}). ` : "Not signed in. "; signOut.hidden = !orKey; signIn.textContent = orKey ? "Sign in again" : "Sign in with OpenRouter"; };
  const signIn = h("button", undefined, "Sign in with OpenRouter");
  const signOut = h("button", undefined, "Sign out");
  const orBox = h("span"); orBox.append(orStatus, signIn, " ", signOut);
  row("OpenRouter", orBox, "Pay-as-you-go on your own OpenRouter account. Your questions, and the pages read, go to OpenRouter and the model's provider. The key stays in this browser.", ["openrouter"]);
  showKey();
  signIn.addEventListener("click", () => { void signInOpenRouter().catch((e) => { orStatus.textContent = e instanceof Error ? `${e.message} ` : String(e); }); });
  signOut.addEventListener("click", () => { orKey = ""; signedOut = true; setAskSettings({ openrouterKey: "" }); showKey(); });
  // the sign-in window saves the key and closes: this page hears of it here
  const onStorage = (ev: StorageEvent) => {
    if (ev.key !== "chalkmath.ask") return;
    const k = askSettings().openrouterKey;
    if (k && k !== orKey) { orKey = k; signedOut = false; backend.value = "openrouter"; showKey(); notify("ok", "Signed in to OpenRouter."); }
  };
  window.addEventListener("storage", onStorage);
  const orModel = text(s.openrouterModel, "anthropic/claude-haiku-4.5");
  const orList = document.createElement("datalist"); orList.id = "openroutermodels";
  orModel.setAttribute("list", orList.id);
  row("OpenRouter model", orModel, "Any model OpenRouter offers that takes a schema for its reply (the list, cheapest first). A fast, inexpensive one is plenty; free ones (“:free”) are rate-limited to a few requests a minute and often busy.", ["openrouter"]);
  form.append(orList);
  const fillOr = async () => {
    const ms = await openrouterModels();
    orList.replaceChildren(...(ms ?? []).slice(0, 300).map((m) => { const o = document.createElement("option"); o.value = m.id; o.label = `${m.name}${m.price ? ` · $${m.price.toFixed(2)}/M tokens in` : " · free, rate-limited"}`; return o; }));
  };
  if (s.backend === "openrouter") void fillOr();
  backend.addEventListener("change", () => { if (backend.value === "openrouter") void fillOr(); });
  const orWeb = check(s.openrouterWeb);
  row("Let the model search the web", orWeb, "OpenRouter's web search finds pages for the model across the whole web (about half a cent to one and a half cents a lookup). Off, it reads what Wikipedia and your web search find.", ["openrouter"]);
  // a test of the chosen model: one small question, timed
  const testBtn = h("button", undefined, "Test the model");
  const result = h("span", "askhint", "Runs one small question on the model chosen above (a WebGPU model is downloaded first).");
  const tester = h("div", "askrow"); tester.append(h("span", "asklab", ""), testBtn, result);
  form.append(tester);
  const knowledge = check(s.knowledge);
  row("Answer from the model's knowledge", knowledge, "Standard formulas and constants are answered by the model without searching; when a search finds nothing, the model's memory is the last resort (marked unsourced).");
  const wiki = check(s.wikipedia);
  row("Search Wikipedia", wiki);
  const search = text(s.searchUrl, "https://searx.example (or a URL with {q})");
  row("Web search", search, "A SearXNG instance (or anything answering its JSON) searches Google, DuckDuckGo, Bing and Brave for you. It must allow this page's origin (CORS).");
  const reader = text(s.reader, "https://reader.example/?url={url}");
  row("Page reader", reader, "Most sites do not let another page read them; a reader fetches the page for you (scripts/ask-proxy/worker.js is one).");
  const consent = check(s.searchOk);
  row("Search without asking", consent);
  const save = () => setAskSettings({
    backend: backend.value as AskSettings["backend"], model: model.value, ollamaUrl: ollamaUrl.value.trim(), ollamaModel: ollamaModel.value.trim(),
    // a sign-in that finished while this dialog was open is kept even if its event was missed
    openrouterKey: signedOut ? "" : askSettings().openrouterKey || orKey, openrouterModel: orModel.value.trim(), openrouterWeb: orWeb.checked,
    knowledge: knowledge.checked, wikipedia: wiki.checked, searchUrl: search.value.trim(), reader: reader.value.trim(), searchOk: consent.checked,
  });
  testBtn.addEventListener("click", async () => {
    save();
    testBtn.setAttribute("disabled", "");
    result.textContent = "Loading the model…";
    try {
      const r = await testModel((d) => { result.textContent = `${d}…`; });
      const ok = /"volume"\s*:\s*24(\.0+)?\b/.test(r.reply);
      result.textContent = `${r.model}: answered in ${(r.ms / 1000).toFixed(1)} s${ok ? ", correctly" : `, wrongly (${r.reply.slice(0, 80)})`}. A lookup asks it 3 to 5 such questions, with longer prompts.`;
    } catch (e) {
      result.textContent = e instanceof Error ? e.message : String(e);
    } finally { testBtn.removeAttribute("disabled"); }
  });
  const showFor = () => { for (const [el, only] of shown) el.hidden = !only.includes(backend.value); };
  backend.addEventListener("change", showFor);
  showFor();
  showModal("Lookup settings", [h("p", "muted", "A cell that starts with ? is a question: ?volume of a cone, ?the first ten primes, let mlb = ?MLB runs and home runs per game for the last 20 years."), form], true);
  modalClosed = () => { window.removeEventListener("storage", onStorage); save(); };
}

/** The ⋮ button at the end of a cell's actions (replacing any there). */
// --- Exercises: a question the reader answers, checked by the engine -------------------------------
// The question is an engine source; its value is the answer and its work the solution, both held
// back until the reader asks. The engine compares answers (`engine.check`): two expressions are
// equivalent when they reduce to the same normal form, as two λ-terms are β-equivalent.

/** A small button for an exercise's row. */
function exBtn(label: string, title: string, act: () => void, cls = "xc-btn"): HTMLElement {
  const b = asButton(h("span", cls, label), title); b.title = title;
  b.addEventListener("mousedown", (e) => e.preventDefault());
  b.addEventListener("click", (ev) => { ev.stopPropagation(); act(); });
  return b;
}
/** An exercise's question, answer box, verdict, hints and solution switch; its editor while editing. */
function renderExercise(cell: Cell) {
  const box = cell.el?.querySelector<HTMLElement>(".xc-box"); if (!box) return;
  const i = S.cells.indexOf(cell);
  box.innerHTML = "";
  delete cell.input;
  if (cell.editing) { box.append(exerciseEditor(cell)); return; }
  if (cell.lean) return renderLeanExercise(cell, box);
  if (cell.prompt?.trim()) box.append(mdRender(cell.prompt));
  if (!cell.hideQuestion || !cell.prompt?.trim()) {
    const q = h("div", "xc-q");
    if (cell.echoLatex) q.innerHTML = tex(cell.echoLatex, true);
    else q.append(h("code", "xc-src", cell.src || "No question yet: ⋮ › Edit exercise"));
    box.append(q);
  }
  const row = h("div", "xc-row");
  const inp = document.createElement("input");
  inp.className = "xc-in"; inp.type = "text"; inp.spellcheck = false; inp.autocomplete = "off";
  inp.value = cell.attempt ?? ""; inp.placeholder = "Your answer, typed as in a cell";
  inp.setAttribute("aria-label", "Your answer");
  const check = () => {
    cell.attempt = inp.value;
    if (!inp.value.trim()) return;
    CHECK_NOW.add(cell); void runCell(cell);
  };
  inp.addEventListener("input", () => { cell.attempt = inp.value; box.querySelector(".xc-verdict")?.classList.add("old"); });
  inp.addEventListener("keydown", (ev) => {
    if (ev.key === "Enter") { ev.preventDefault(); check(); }
    if (ev.key === "ArrowDown" && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
    if (ev.key === "ArrowUp" && i > 0) { ev.preventDefault(); focusCell(i - 1); }
  });
  row.append(inp, exBtn("Check", "Check the answer (Enter)", check, "xc-btn primary"));
  box.append(row);
  const v = cell.verdict;
  if (v) {
    const out = h("div", `xc-verdict ${v.equivalent ? "right" : "wrong"}`);
    if (v.error) {
      out.append(h("span", "xc-mark", "✗"), document.createTextNode(` ${v.error.message[0]!.toUpperCase()}${v.error.message.slice(1)}.`));
      if (v.error.span && cell.attempt) out.append(h("span", "caret", `${cell.attempt}\n${" ".repeat(v.error.span.start)}${"^".repeat(Math.max(1, v.error.span.end - v.error.span.start))}`));
    } else {
      // how the answer was compared: by truth table, as a set, or by normal form
      const world = ORDER_CELL.test(cell.src.trim()) || SYSTEM_CELL.test(cell.src.trim()) || LAMBDA_CMD.test(cell.src.trim()) ? "order" : isLogicCell(cell.src.trim()) ? "logic" : "math";
      const m = h("span", "xc-math"); m.innerHTML = tex((v.equivalent || world !== "math" ? v.answerLatex : v.normalLatex) ?? "");
      const [before, after] = v.equivalent
        ? world === "logic" ? [" Correct: ", " agrees with the answer on every row of the truth table."]
        : world === "order" ? [" Correct: ", " is the answer."]
        : [" Correct: ", " reduces to the answer's normal form."]
        : world === "logic" ? [" Not yet: ", " does not agree with the answer on every row of the truth table."]
        : world === "order" ? [" Not yet: ", " is not the answer."]
        : [" Not yet: your answer reduces to ", ", which is not the answer's normal form."];
      out.append(h("span", "xc-mark", v.equivalent ? "✓" : "✗"), document.createTextNode(before), m, document.createTextNode(after));
    }
    box.append(out);
  }
  appendHints(cell, box);
  const tools = h("div", "xc-tools");
  appendHintButton(cell, tools);
  tools.append(exBtn(cell.solution ? "Hide the solution" : "Show the solution", cell.solution ? "Hide the worked solution" : "Step through the worked solution: the engine's own work on the question", () => {
    cell.solution = !cell.solution;
    if (cell.solution) { cell.showWork = true; if (cell.stepwise === undefined) cell.stepwise = 0; if (!cell.outLatex && !cell.error) void runCell(cell); }
    renderCellBody(cell); renderSidebar(); autosave();
  }));
  box.append(tools);
}
/** A Lean exercise: the prompt and the statement above the reader's proof (an editor of the notebook's
 *  Lean file), and below it what Lean says, the verdict, the hints and the author's proof. */
function renderLeanExercise(cell: Cell, box: HTMLElement) {
  if (cell.prompt?.trim()) box.append(mdRender(cell.prompt));
  if (!cell.src.trim()) { box.append(h("div", "xc-src", "No statement yet: ✎ Edit")); return; }
  const stmt = h("pre", "xc-leanstmt");
  stmt.append(h("code", undefined, cell.src));
  box.append(stmt);
  const below = cell.el?.querySelector<HTMLElement>(".xc-below"); if (!below) return;
  below.innerHTML = "";
  if (S.cells.find(isLeanCell) === cell) { const st = leanStatus(); if (st) below.append(st); }
  const state = leanState();
  if (state === "failed" || state === "isolating") below.append(h("div", `leanstate ${state}`, state === "failed" ? `Lean did not start: ${leanFailure()}` : "Preparing the page for Lean: it reloads once."));
  // what Lean says about the proof (its lines), and the statement's own errors (an unproved goal is reported at `by`)
  const ms = [...(cell.leanStmtMessages ?? []).filter((m) => m.severity === "error").map((m) => ({ ...m, where: "statement" })),
    ...(cell.leanMessages ?? []).map((m) => ({ ...m, where: `${m.line}:${m.column}` }))];
  for (const m of ms) {
    const row = h("div", `leanmsg ${m.severity}`);
    row.append(h("span", "where", m.where), h("span", "text", m.message));
    below.append(row);
  }
  const v = cell.verdict;
  const verdict = h("div", "xc-verdict");
  if (state !== "ready") verdict.append(h("span", "xc-pending", state === "failed" ? "" : "Waiting for Lean…"));
  else if (!leanChecked()) { verdict.classList.add("old"); verdict.append(h("span", "xc-pending", "Lean is checking…")); }
  else if (v?.equivalent) { verdict.classList.add("right"); verdict.append(h("span", "xc-mark", "✓"), document.createTextNode(" Proved: Lean accepts the proof, and nothing is left as sorry.")); }
  else if (v) { verdict.classList.add("wrong"); verdict.append(h("span", "xc-mark", "✗"), document.createTextNode(` Not yet: ${v.error?.message ?? "Lean does not accept the proof"}.`)); }
  below.append(verdict);
  appendHints(cell, below);
  const tools = h("div", "xc-tools");
  appendHintButton(cell, tools);
  if (cell.leanSolution?.trim()) tools.append(exBtn(cell.solution ? "Hide the proof" : "Show a proof", cell.solution ? "Hide the author's proof" : "The author's proof, to compare with yours", () => {
    cell.solution = !cell.solution; renderCellBody(cell); autosave();
  }));
  below.append(tools);
  if (cell.solution && cell.leanSolution?.trim()) {
    const sol = h("pre", "xc-leanstmt xc-leansol");
    sol.append(h("code", undefined, `${cell.src}\n${cell.leanSolution}`));
    below.append(sol);
  }
}
/** The hints opened so far. */
function appendHints(cell: Cell, into: HTMLElement) {
  const hints = cell.hints ?? [];
  hints.slice(0, Math.min(cell.hintsShown ?? 0, hints.length)).forEach((t, k) => {
    const hb = h("div", "xc-hint");
    hb.append(h("span", "xc-hintno", hints.length > 1 ? `Hint ${k + 1}` : "Hint"), mdRender(t));
    into.append(hb);
  });
}
/** The button that opens the next hint, while one is left. */
function appendHintButton(cell: Cell, tools: HTMLElement) {
  const hints = cell.hints ?? [], shown = Math.min(cell.hintsShown ?? 0, hints.length);
  if (shown < hints.length) tools.append(exBtn(shown ? `Another hint (${shown + 1} of ${hints.length})` : hints.length > 1 ? `Hint (1 of ${hints.length})` : "Hint",
    "Open the next hint", () => { cell.hintsShown = shown + 1; renderCellBody(cell); autosave(); }));
}
/** The author's side of an exercise: the prompt, the question, the hints. */
function exerciseEditor(cell: Cell): HTMLElement {
  const f = h("div", "xc-edit");
  const field = (label: string, input: HTMLElement, hint: string) => {
    const l = h("label", "xc-field");
    l.append(h("span", "xc-flabel", label), input, h("span", "xc-fhint", hint));
    f.append(l);
  };
  const grow = (ta: HTMLTextAreaElement) => { ta.style.height = "auto"; ta.style.height = `${ta.scrollHeight + 2}px`; };
  const prompt = document.createElement("textarea");
  prompt.rows = 2; prompt.value = cell.prompt ?? ""; prompt.placeholder = cell.lean ? "Prove that conjunction commutes." : "Differentiate, then simplify.";
  prompt.addEventListener("input", () => { cell.prompt = prompt.value; grow(prompt); });
  field("Prompt", prompt, "Markdown, with $math$: what the reader is asked to do.");
  if (cell.lean) return leanExerciseEditor(cell, f, field, grow, prompt);
  const q = document.createElement("input");
  q.type = "text"; q.className = "xc-qin"; q.spellcheck = false; q.value = cell.src; q.placeholder = "diff(x^2 * sin(x), x)";
  cell.input = q;   // what the cell's source is while it is edited (cellSrc)
  q.addEventListener("input", () => { cell.src = q.value; renderSidebar(); });
  field("Question", q, "An input for the engine. Its value is the answer the reader's is compared with, and its work is the solution.");
  const hints = document.createElement("textarea");
  hints.rows = 2; hints.value = (cell.hints ?? []).join("\n\n"); hints.placeholder = "Which rule applies to a product?\n\nThe product rule: (fg)′ = f′g + fg′.";
  hints.addEventListener("input", () => { cell.hints = hints.value.split(/\n\s*\n/).map((x) => x.trim()).filter(Boolean); grow(hints); });
  field("Hints", hints, "Opened one at a time, in order; a blank line between two hints.");
  const show = document.createElement("input");
  show.type = "checkbox"; show.checked = !cell.hideQuestion;
  show.addEventListener("change", () => { if (show.checked) delete cell.hideQuestion; else cell.hideQuestion = true; });
  const sl = h("label", "xc-check"); sl.append(show, document.createTextNode(" Show the question typeset under the prompt"));
  f.append(sl);
  for (const ta of [prompt, hints]) ta.addEventListener("keydown", (ev) => { if (ev.key === "Enter" && (ev.shiftKey || ev.metaKey || ev.ctrlKey)) { ev.preventDefault(); finishExerciseEdit(cell); } });
  q.addEventListener("keydown", (ev) => { if (ev.key === "Enter") { ev.preventDefault(); finishExerciseEdit(cell); } });
  queueMicrotask(() => { grow(prompt); grow(hints); });
  return f;
}
/** A Lean exercise's editor, after its prompt: the statement, the proof the reader starts from, the
 *  author's proof, the hints. */
function leanExerciseEditor(cell: Cell, f: HTMLElement, field: (label: string, input: HTMLElement, hint: string) => void,
  grow: (ta: HTMLTextAreaElement) => void, prompt: HTMLTextAreaElement): HTMLElement {
  const area = (value: string, placeholder: string, set: (v: string) => void, code = true) => {
    const ta = document.createElement("textarea");
    ta.rows = 2; ta.value = value; ta.placeholder = placeholder; ta.spellcheck = !code;
    if (code) ta.className = "xc-code";
    ta.addEventListener("input", () => { set(ta.value); grow(ta); });
    ta.addEventListener("keydown", (ev) => { if (ev.key === "Enter" && (ev.shiftKey || ev.metaKey || ev.ctrlKey)) { ev.preventDefault(); finishExerciseEdit(cell); } });
    return ta;
  };
  const stmt = area(cell.src, "theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := by", (v) => { cell.src = v; renderSidebar(); });
  field("Statement", stmt, "Lean, ending with := by. The reader cannot change it; their proof goes below it, and Lean checks the two together, with the notebook's Lean cells above in scope.");
  const start = area(cell.leanStart ?? "", LEAN_START, (v) => { if (v.trim()) cell.leanStart = v; else delete cell.leanStart; });
  field("Starting proof", start, "What the reader's proof starts as (indented): by default sorry, which Lean shows the goal of.");
  const sol = area(cell.leanSolution ?? "", "  obtain ⟨hp, hq⟩ := h\n  exact ⟨hq, hp⟩", (v) => { if (v.trim()) cell.leanSolution = v; else delete cell.leanSolution; });
  field("A proof", sol, "Yours, shown when the reader asks, and checked when the notebook is (scripts/notebooks/check-lean.mjs).");
  const hints = area((cell.hints ?? []).join("\n\n"), "Take the conjunction apart first.\n\nobtain ⟨hp, hq⟩ := h", (v) => { cell.hints = v.split(/\n\s*\n/).map((x) => x.trim()).filter(Boolean); }, false);
  field("Hints", hints, "Opened one at a time, in order; a blank line between two hints.");
  queueMicrotask(() => { for (const ta of [prompt, stmt, start, sol, hints]) grow(ta); });
  prompt.addEventListener("keydown", (ev) => { if (ev.key === "Enter" && (ev.shiftKey || ev.metaKey || ev.ctrlKey)) { ev.preventDefault(); finishExerciseEdit(cell); } });
  return f;
}
/** Leave an exercise's editor: a changed question makes the old verdict and solution the old question's. */
function finishExerciseEdit(cell: Cell) {
  if (cell.lean) {
    // the statement is part of the Lean file: the cells are rebuilt, and Lean checks it with the proof below
    cell.editing = false;
    delete cell.verdict;
    renderCells(); renderSidebar(); autosave();
    return;
  }
  const was = cell.src;
  cell.src = cellSrc(cell);
  cell.editing = false;
  if (cell.src !== was || !cell.echoLatex) { delete cell.verdict; delete cell.solution; }
  renderCellBody(cell); renderSidebar(); autosave();
  if (cell.src.trim()) void runCell(cell);
}
/** An exercise's actions: edit (or done), and the ⋮ menu. */
function exerciseActs(cell: Cell, acts: Element) {
  acts.innerHTML = "";
  acts.append(exBtn(cell.editing ? "✓ Done" : "✎ Edit", cell.editing ? "Finish editing the exercise (Shift+Enter)" : "Edit the prompt, the question and the hints",
    () => { if (cell.editing) finishExerciseEdit(cell); else { cell.editing = true; if (cell.lean) renderCells(); else renderCellBody(cell); focusCell(S.cells.indexOf(cell)); } }, ""));
  appendMore(cell, acts);
}

function appendMore(cell: Cell, acts: Element) {
  acts.querySelector(".more")?.remove();
  const more = asButton(h("span", "more", "⋮"), "Cell actions"); more.title = "Cell actions";
  more.setAttribute("aria-haspopup", "menu");
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
    ta.addEventListener("paste", (ev) => onPaste(ev, cell));
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
  const btn = asButton(h("span", undefined, cell.editing ? "▶ Render" : "✎ Edit"));
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
  const att = /^⟦([^⟧]+)⟧$/.exec(u.trim());
  if (att) return assetUrl(att[1]!) ?? "#";
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
    if (c === "⟦") {
      const m = /^⟦([^⟧]+)⟧/.exec(text.slice(i));
      const a = m && S.assets[m[1]!];
      if (m && a) {
        flush(); i += m[0].length;
        const f = assetFile(a), kind = kindOf(f);
        if (kind === "image") { const img = document.createElement("img"); img.src = dataUrl(f); img.alt = a.name; img.className = "mdimg"; host.append(img); }
        else if (kind === "table") { const t = tableOf(f); host.append(dataGrid({ rows: t.rows.length, cols: t.cols, header: t.header, cell: (r, c) => t.rows[r]![c]!, numeric: numericColumns(t), label: `${a.name}, a table` })); }
        else { const e = h("code", "mdcode", `⟦${a.name}⟧`); e.title = `${mimeLabel(a.mime)}, ${fmtSize(fileSize(f))}`; host.append(e); }
        continue;
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
/** The callouts a Markdown cell knows (`> [!kind] title`), by the name written, and how each is labelled. */
const CALLOUTS: Record<string, { cls: string; label: string }> = {
  definition: { cls: "definition", label: "Definition" },
  theorem: { cls: "theorem", label: "Theorem" }, lemma: { cls: "theorem", label: "Lemma" }, corollary: { cls: "theorem", label: "Corollary" },
  proposition: { cls: "theorem", label: "Proposition" },
  proof: { cls: "proof", label: "Proof" },
  example: { cls: "example", label: "Example" },
  try: { cls: "try", label: "Try it" }, "try-it": { cls: "try", label: "Try it" },
  mistake: { cls: "mistake", label: "Common mistake" }, warning: { cls: "mistake", label: "Careful" },
  note: { cls: "note", label: "Note" }, tip: { cls: "note", label: "Tip" },
  summary: { cls: "summary", label: "Summary" }, goal: { cls: "summary", label: "Goal" },
};
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
      // `> [!theorem] Title`: a callout, the blocks a lesson is made of; anything else is a quote
      const call = /^\[!([A-Za-z-]+)\]\s*(.*)$/.exec(buf[0] ?? "");
      const kind = call ? CALLOUTS[call[1]!.toLowerCase()] : undefined;
      if (call && kind) {
        const box = h("aside", `callout ${kind.cls}`);
        const head = h("div", "callhead", kind.label);
        if (call[2]!.trim()) { const t = h("span", "calltitle"); mdInline(t, call[2]!.trim()); head.append(t); }
        box.append(head, ...Array.from(mdRender(buf.slice(1).join("\n")).childNodes));
        if (kind.cls === "proof") box.append(h("span", "qed", "∎"));
        out.append(box); continue;
      }
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
    void navigator.clipboard?.writeText(text).then(() => notify("ok", `Copied ${what}`), () => notify("err", "The clipboard is not available"));
  };
  // Send to scene ▸ — every scene, then a new one
  const canSend = !!(cell.outLatex && cell.echoLatex);
  if (canSend) {
    const sub = h("div", "submenu");
    ST.scenes.forEach((sc, k) => {
      const it = h("div", "item", `${sc.name} · ${sc.shots.length} shots`);
      it.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); void sendToScene(cell, k); });
      sub.append(it);
    });
    if (ST.scenes.length) sub.append(h("div", "sep"));
    const nw = h("div", "item", "New scene");
    nw.addEventListener("click", (ev) => { ev.stopPropagation(); closeCellMenu(); void sendToScene(cell, "new"); });
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
  item("Run this and below", () => void runFrom(i));
  if (!cell.type && (cell.slider || SLIDER_SRC.test(cellSrc(cell)))) item(`${cell.slider ? "✓ " : ""}Show as a slider`, () => toggleSlider(cell));
  if ((!cell.type || (cell.type === "exercise" && cell.solution)) && workCount(cell)) {
    menu.append(h("div", "sep"));
    item(`${cell.stepwise !== undefined ? "✓ " : ""}Step through the work`, () => setStepwise(cell, cell.stepwise === undefined ? 0 : undefined));
    // the author's starting point: as many steps as show now, the rest left to the reader
    const k = cell.stepwise !== undefined ? revealedCount(cell) : 0;
    if (cell.stepwise !== undefined && k !== cell.stepwise && k < workCount(cell)) item(`Begin with ${k} step${k === 1 ? "" : "s"} shown`, () => setStepwise(cell, k));
  }
  menu.append(h("div", "sep"));
  item("Duplicate cell", () => duplicateCell(cell));
  item("Move up", i > 0 ? () => moveCell(cell, -1) : null);
  item("Move down", i < S.cells.length - 1 ? () => moveCell(cell, 1) : null);
  menu.append(h("div", "sep"));
  item("Copy input", copy(cellSrc(cell), "the input"));
  item("Copy output", cell.outText !== undefined ? copy(cell.outText, "the output") : null);
  item("Copy output as LaTeX", cell.outLatex ? copy(stripPaths(cell.outLatex), "the output as LaTeX") : null);
  menu.append(h("div", "sep"));
  item("Clear output", hasOutput(cell) ? () => clearCellOutput(cell) : null);
  item("Delete cell", () => deleteCell(cell), { danger: true });
  // on the body, fixed: the paper scrolls and clips, and a menu near its bottom must not grow a scrollbar
  document.body.append(menu);
  menuKeys(menu, () => { closeCellMenu(); anchor.focus(); });
  menu.querySelector<HTMLElement>(":scope > .item:not(.off)")?.focus({ preventScroll: true });
  const r = anchor.getBoundingClientRect(), mh = menu.offsetHeight;
  const below = r.bottom + 4 + mh <= window.innerHeight - 8;
  menu.style.top = `${below ? r.bottom + 4 : Math.max(8, r.top - 4 - mh)}px`;
  menu.style.right = `${window.innerWidth - r.right}px`;
}
function closeCellMenu() { document.querySelectorAll(".cellmenu").forEach((m) => m.remove()); }

// --- Help › Documentation (docs.ts, reference.ts): the contents beside the page shown ------------

/** Whether a page exists: a guide or reference page, or a function's page (`fn:name`). */
const docPageExists = (id: string) => DOC_PAGES.some((p) => p.id === id) || (id.startsWith("fn:") && FN_BY_NAME.has(id.slice(3)));

/** Open the documentation's tab on a page (the one last shown by default). */
function openDocs(page = S.guide.page) {
  S.guide.open = true;
  S.guide.page = docPageExists(page) ? page : "start";
  switchTab("docs");
}
function closeDocs() {
  S.guide.open = false;
  if (S.tab === "docs") switchTab("notebook"); else renderTabs();
}

/** Run an example: in the last cell when it is an empty math cell, else in a new one at the end. */
function tryInNotebook(src: string) {
  switchTab("notebook");
  const last = S.cells[S.cells.length - 1];
  let c: Cell;
  if (last && !last.type && !cellSrc(last).trim()) { c = last; c.src = src; delete c.tree; renderCells(); }
  else c = addCell(src);
  focusCell(S.cells.indexOf(c)); void runCell(c);
}

/** A function's examples as a notebook of their own, in a new tab, run. */
function openExamples(f: FnDoc, sections: ExampleSection[]) {
  const cells: Cell[] = [freshCell(`${f.title ?? f.name}: examples`, "section")];
  for (const sec of sections) {
    if (sections.length > 1) cells.push(freshCell(`## ${sec.title}`, "markdown"));
    for (const it of sec.items) cells.push(typeof it === "string" ? freshCell(it) : freshCell(it.note, "markdown"));
  }
  cells.push(freshCell());
  const d = makeDoc(`${f.name.replace(/[^\w-]/g, "") || "examples"}-examples.chalk`, cells);
  S.docs.push(d); loadDoc(S.docs.length - 1);
  switchTab("notebook");
  void runAll();
}

/** What a `#do:` link in the documentation does. */
const DOC_ACTIONS: Record<string, () => void> = {
  "ask-settings": () => void showAskSettings(),
  welcome: () => void openExample("welcome.chalk"),
};

/** A page's text, for the contents' search: its Markdown and the tables it shows. */
function docText(p: DocPage): string {
  return [p.title, ...p.parts.map((part) => typeof part === "string" ? part : "try" in part ? part.try.join(" ") : {
    functions: "",
    symbols: SYMBOLS.map((s) => `${s.abbr} ${s.aliases.join(" ")} ${s.what}`).join(" ") + Object.entries(TEMPLATES).map(([k, t]) => `${k} ${t.what}`).join(" "),
    shortcuts: SHORTCUTS.flat().join(" "),
    examples: EXAMPLES.map((e) => `${e.title} ${e.blurb}`).join(" "),
  }[part.insert])].join(" ").toLowerCase();
}
const fnText = (f: FnDoc) => [f.name, f.title ?? "", f.area, ...f.usage.flat(), ...(f.details ?? [])].join(" ").toLowerCase();
const queryWords = (q: string) => q.toLowerCase().split(/\s+/).filter(Boolean);
const docMatches = (text: string, q: string) => queryWords(q).every((w) => text.includes(w));
/** The functions a search finds: the name typed first, then names that start with it, then the rest. */
function fnMatches(q: string): FnDoc[] {
  const k = q.trim().toLowerCase();
  const rank = (f: FnDoc) => f.name.toLowerCase() === k ? 0 : f.name.toLowerCase().startsWith(k) ? 1 : 2;
  return FUNCTIONS.filter((f) => docMatches(fnText(f), q)).sort((a, b) => rank(a) - rank(b));
}

function renderDocs() {
  const host = $(".docs"); host.innerHTML = "";
  const nav = h("nav", "docnav"); nav.setAttribute("aria-label", "Documentation contents");
  const search = document.createElement("input");
  search.type = "search"; search.className = "docsearch"; search.placeholder = "Search the documentation"; search.value = S.guide.query;
  search.setAttribute("aria-label", "Search the documentation"); search.spellcheck = false;
  const list = h("div", "doclist");
  const row = (id: string, label: string, cls = "") => {
    const r = asButton(h("div", `docrow${cls}${id === S.guide.page ? " on" : ""}`, label));
    r.setAttribute("aria-current", String(id === S.guide.page));
    r.addEventListener("click", () => openDocs(id));
    return r;
  };
  const fillList = () => {
    list.innerHTML = "";
    const q = S.guide.query.trim();
    let group = "";
    const head = (g: string) => { if (g !== group) { group = g; list.append(h("div", "docgroup", g)); } };
    if (q) {
      const pages = DOC_PAGES.filter((p) => docMatches(docText(p), q));
      const fns = fnMatches(q);
      // a function named as typed comes first
      if (fns[0] && fns[0].name.toLowerCase() === q.toLowerCase()) { head("Functions"); for (const f of fns) list.append(row(fnPage(f.name), f.title ?? f.name, " fn")); }
      for (const p of pages) { head(p.group); list.append(row(p.id, p.title)); }
      if (group !== "Functions" && fns.length) { group = ""; head("Functions"); for (const f of fns) list.append(row(fnPage(f.name), f.title ?? f.name, " fn")); }
      if (!pages.length && !fns.length) list.append(h("div", "docnone", "Nothing matches."));
    } else {
      // the function pages unfold under the index while one of them (or the index) is shown
      const inFns = S.guide.page === "functions" || S.guide.page.startsWith("fn:");
      for (const p of DOC_PAGES) {
        head(p.group);
        list.append(row(p.id, p.title));
        if (p.id === "functions" && inFns) {
          for (const [area] of AREAS) {
            list.append(h("div", "docarea", area));
            for (const f of FUNCTIONS.filter((x) => x.area === area)) list.append(row(fnPage(f.name), f.title ?? f.name, " fn tree"));
          }
        }
      }
    }
    // the page shown stays in view (on a phone the contents are a strip)
    requestAnimationFrame(() => list.querySelector(".docrow.on")?.scrollIntoView({ block: "nearest", inline: "nearest" }));
  };
  search.addEventListener("input", () => { S.guide.query = search.value; fillList(); });
  search.addEventListener("keydown", (ev) => {
    if (ev.key !== "Enter") return;
    list.querySelector<HTMLElement>(".docrow")?.click();
  });
  fillList();
  nav.append(search, list);
  const main = h("div", "docmain");
  // links between pages, and to parts of the notebook, stay in the page
  main.addEventListener("click", (ev) => {
    const a = (ev.target as Element).closest?.("a");
    const m = /^#(doc|do|fn):(.+)$/.exec(a?.getAttribute("href") ?? "");
    if (!m) return;
    ev.preventDefault();
    if (m[1] === "do") DOC_ACTIONS[m[2]!]?.();
    else openDocs(m[1] === "fn" ? fnPage(m[2]!) : m[2]!);
  });
  host.append(nav, main);
  const art = h("article", "docpage");
  if (S.guide.page.startsWith("fn:")) renderFnPage(art, FN_BY_NAME.get(S.guide.page.slice(3))!);
  else renderGuidePage(art);
  main.append(art);
}

/** The pages before and after, by the contents' order. */
function docFoot(prev?: [string, string], next?: [string, string]): HTMLElement {
  const foot = h("div", "docfoot");
  for (const [p, dir] of [[prev, "prev"], [next, "next"]] as const) {
    if (!p) { foot.append(h("span", "docstep none")); continue; }
    const b = asButton(h("div", `docstep ${dir}`));
    b.append(h("span", "dir", dir === "prev" ? "← Previous" : "Next →"), h("span", "t", p[1]));
    b.addEventListener("click", () => openDocs(p[0]));
    foot.append(b);
  }
  return foot;
}

function renderGuidePage(art: HTMLElement) {
  const i = Math.max(0, DOC_PAGES.findIndex((p) => p.id === S.guide.page));
  const page = DOC_PAGES[i]!;
  for (const part of page.parts) art.append(docPart(part));
  const pg = (j: number): [string, string] | undefined => DOC_PAGES[j] ? [DOC_PAGES[j]!.id, DOC_PAGES[j]!.title] : undefined;
  art.append(docFoot(pg(i - 1), pg(i + 1)));
}

/** A function's page, as Mathematica lays one out: usage, details, examples with their outputs (the
 *  engine's, evaluated here), and related functions. */
function renderFnPage(art: HTMLElement, f: FnDoc) {
  art.classList.add("fnpage");
  const head = h("div", "fnhead");
  const area = asButton(h("span", "fnarea", f.area));
  area.addEventListener("click", () => openDocs("functions"));
  head.append(h("h1", "fnname", f.title ?? f.name), area);
  art.append(head);
  const usage = h("div", "fnusage");
  for (const [form, what] of f.usage) {
    const r = h("div", "urow");
    r.append(h("code", "uform", form));
    const w = h("div", "uwhat"); mdInline(w, what); r.append(w);
    usage.append(r);
  }
  art.append(usage);
  if (f.details?.length) {
    const d = document.createElement("details"); d.className = "fndetails"; d.open = true;
    d.append(h("summary", undefined, "Details"), mdRender(f.details.map((x) => `- ${x}`).join("\n")));
    art.append(d);
  }
  art.append(h("h2", "fnsec", "Examples"));
  const all = h("button", "smallbtn", "Open all in a notebook");
  all.title = "A new notebook with every example on this page, run";
  all.addEventListener("click", () => openExamples(f, f.examples));
  art.append(all);
  f.examples.forEach((sec, k) => art.append(exampleSection(f, sec, k)));
  if (f.see?.length) {
    art.append(h("h2", "fnsec", "See also"));
    const see = h("div", "fnsee");
    for (const n of f.see) {
      const g = FN_BY_NAME.get(n); if (!g) continue;
      const a = document.createElement("a"); a.href = `#fn:${g.name}`; a.textContent = g.title ?? g.name;
      see.append(a);
    }
    art.append(see);
  }
  if (f.ref) {
    const a = document.createElement("a"); a.href = f.ref; a.target = "_blank"; a.rel = "noreferrer"; a.className = "fnref"; a.textContent = "On MathWorld ↗";
    art.append(a);
  }
  const i = FUNCTIONS.indexOf(f);
  const pg = (j: number): [string, string] | undefined => FUNCTIONS[j] ? [fnPage(FUNCTIONS[j]!.name), FUNCTIONS[j]!.title ?? FUNCTIONS[j]!.name] : undefined;
  art.append(docFoot(pg(i - 1) ?? ["functions", "Functions and commands"], pg(i + 1)));
}

/** One section of a function's examples: its inputs and, as the engine answers, their outputs. */
function exampleSection(f: FnDoc, sec: ExampleSection, k: number): HTMLElement {
  const box = h("section", "exsec");
  const top = h("div", "exhead");
  top.append(h("h3", undefined, sec.title));
  const open = asButton(h("span", "link", "Open in a notebook"));
  open.addEventListener("click", () => openExamples(f, [sec]));
  top.append(open);
  box.append(top);
  const live = evaluable(sec);
  const outs: HTMLElement[] = [];
  let n = 0;
  for (const it of sec.items) {
    if (typeof it !== "string") { box.append(mdRender(it.note)); continue; }
    const pair = h("div", "expair");
    const inRow = h("div", "exrow");
    inRow.append(h("span", "exprompt", live ? `In[${++n}]:=` : ""), h("code", "exin", it));
    const outRow = h("div", "exrow exout");
    if (live) { outRow.append(h("span", "exprompt"), h("div", "exval pending", "…")); outs.push(outRow); }
    pair.append(inRow, ...(live ? [outRow] : []));
    box.append(pair);
  }
  if (!live) box.append(h("p", "exnote", "These read a file or ask a question, which a notebook does: open them in one to see what they give."));
  else void fillOutputs(`${f.name}#${k}`, sec, outs);
  return box;
}

/** The outputs of a section's inputs, evaluated once per page view in a session of their own. */
interface ExOut { label?: number; latex?: string; plot?: PlotData; hasse?: HasseData; summary?: string; visuals?: KnownVisual[]; error?: string }
const EXAMPLE_OUTS = new Map<string, Promise<ExOut[]>>();
async function fillOutputs(key: string, sec: ExampleSection, rows: HTMLElement[]) {
  const val = (r: HTMLElement) => r.querySelector(".exval") as HTMLElement;
  if (!client || S.kernel !== "ready") {
    // the engine is still loading (the page is drawn again when it is ready) or has stopped
    if (S.kernel === "failed") rows.forEach((r) => { val(r).textContent = "not evaluated: the engine is not running"; });
    return;
  }
  let p = EXAMPLE_OUTS.get(key);
  if (!p) { p = evaluateExamples(client, sec.items.filter((x): x is string => typeof x === "string")); EXAMPLE_OUTS.set(key, p); }
  let outs: ExOut[];
  try { outs = await p; } catch (e) {
    EXAMPLE_OUTS.delete(key);
    rows.forEach((r) => { const v = val(r); v.className = "exval err"; v.textContent = e instanceof Error ? e.message : String(e); });
    return;
  }
  rows.forEach((r, i) => {
    const o = outs[i]; if (!o) return;
    const prompt = r.querySelector(".exprompt")!, v = val(r);
    prompt.textContent = `Out[${o.label ?? i + 1}]=`;
    r.previousElementSibling?.querySelector(".exprompt")?.replaceChildren(`In[${o.label ?? i + 1}]:=`);
    v.className = "exval"; v.innerHTML = "";
    if (o.error) { v.classList.add("err"); v.textContent = o.error; return; }
    if (o.plot) {
      const epi = !!o.plot.terms?.length;
      const pb = epi ? epicycleBox(o.plot, 420, 260) : h("div", "plotbox");
      if (!epi) pb.append(plotSvg(o.plot, 420, o.plot.series.some((s) => s.parametric) ? 300 : 210));
      v.append(pb);
    } else if (o.hasse) {
      const pb = h("div", "plotbox"); pb.append(hasseSvg(o.hasse)); v.append(pb);
    } else v.innerHTML = tex(o.latex ?? "");
    if (o.summary) v.append(h("span", "exsummary", o.summary));
    for (const vis of o.visuals ?? []) v.append(visualBox(vis));
  });
}
async function evaluateExamples(c: EngineClient, inputs: string[]): Promise<ExOut[]> {
  const sid = `docs-${crypto.randomUUID()}`;
  const outs: ExOut[] = [];
  try {
    for (const [k, source] of inputs.entries()) {
      const params = { sessionId: sid, cellId: `ex${k}`, source, showWork: false, paths: false };
      const r = /^\s*(plot|epicycles|dft)\s*\(/.test(source) ? await c.call("engine.plot", params)
        : /^\s*manipulate\s*\(/.test(source) ? await c.call("engine.manipulate", params)
        : await c.call("engine.evaluate", params);
      if (!r.ok) { outs.push({ ...(r.label ? { label: r.label } : {}), error: r.error.message }); continue; }
      const o: ExOut = { latex: r.rendered.latex, ...(r.label ? { label: r.label } : {}) };
      if ("kind" in r && r.kind === "plot") o.plot = plotDataOf(r);
      if ("kind" in r && r.kind === "manipulate") {
        // the page shows the first frame; the slider is a notebook's
        const f = r.frames[0];
        const pl = f?.plot ?? f?.parts?.find((pt) => pt.plot)?.plot;
        if (pl) o.plot = plotDataOf(pl);
        o.summary = `the first of ${r.frames.length} frames, ${r.param} = ${f?.valueRendered.text ?? ""}: open it in a notebook to move ${r.param}`;
      }
      if ("kind" in r && r.kind === "poset" && r.hasse) { o.hasse = r.hasse; if (r.summary) o.summary = r.summary; }
      if ("kind" in r && r.kind === "lambda" && r.reading) o.summary = r.reading;
      if ("kind" in r && (r.kind === "logic" || r.kind === "system") && r.summary) o.summary = r.summary;
      const vs = knownVisuals("visuals" in r ? r.visuals : undefined);
      if (vs.length) o.visuals = vs;
      outs.push(o);
    }
  } finally { void c.call("engine.resetSession", { sessionId: sid }).catch(() => undefined); }
  return outs;
}

function docPart(part: DocPart): HTMLElement {
  if (typeof part === "string") return mdRender(part.replaceAll("{origin}", location.origin));
  if ("try" in part) {
    const row = h("div", "doctry");
    row.append(h("span", "lab", "Try"));
    for (const e of part.try) {
      const b = document.createElement("button"); b.textContent = e; b.title = "Run this in the notebook";
      b.addEventListener("click", () => tryInNotebook(e));
      row.append(b);
    }
    return row;
  }
  switch (part.insert) {
    case "functions": {
      // the index: every function, by area, with its first usage line
      const box = h("div", "fnindex");
      for (const [area, what] of AREAS) {
        box.append(h("h2", undefined, area), h("p", "fnareawhat", what));
        const grid = h("div", "fngrid");
        for (const f of FUNCTIONS.filter((x) => x.area === area)) {
          const r = h("div", "fnitem");
          const a = document.createElement("a"); a.href = `#fn:${f.name}`; a.textContent = f.title ?? f.name;
          const w = h("span", "fnwhat"); mdInline(w, f.usage[0]![1]);
          r.append(a, w); grid.append(r);
        }
        box.append(grid);
      }
      return box;
    }
    case "symbols": {
      const box = h("div");
      const t = h("table", "doctable");
      t.append(docRow(["Type", "For", ""], "th"));
      for (const s of SYMBOLS) t.append(docRow([[s.abbr, ...s.aliases].map((a) => `\\${a}`).join("  "), s.sym, s.what]));
      box.append(t, mdRender("## Templates\n\nIn a typeset cell these insert a shape with slots to fill (Tab goes to the next one); in a text cell, they turn the cell typeset."));
      const t2 = h("table", "doctable");
      t2.append(docRow(["Type", "For", ""], "th"));
      for (const [k, tpl] of Object.entries(TEMPLATES)) t2.append(docRow([`\\${k}`, tpl.glyph, tpl.what]));
      box.append(t2);
      return box;
    }
    case "shortcuts": {
      const t = h("table", "keys doctable");
      for (const [k, what] of SHORTCUTS) {
        const tr = h("tr"); const kd = h("td"); kd.append(h("kbd", undefined, k));
        tr.append(kd, h("td", undefined, what)); t.append(tr);
      }
      return t;
    }
    case "examples": {
      const list = h("div", "exlist");
      for (const p of PROJECTS) {
        const card = asButton(h("div", "excard"));
        card.append(h("div", "t", p.title), h("div", "b", `${p.kind === "course" ? `A course in ${p.lessons.length} lessons` : `${p.lessons.length} notebooks`}: ${p.blurb}`));
        card.addEventListener("click", () => openCourses(p.id));
        list.append(card);
      }
      return list;
    }
  }
}
function docRow(cells: string[], tag = "td"): HTMLElement {
  const tr = h("tr");
  cells.forEach((c, i) => tr.append(h(tag, i === 0 && tag === "td" ? "mono" : undefined, c)));
  return tr;
}

function renderPanelHead() {
  const panel = $(".panel");
  let head = panel.querySelector(".panelhead") as HTMLElement;
  if (!head) { head = h("div", "panelhead"); panel.prepend(head); }
  head.innerHTML = "";
  const hasLean = S.cells.some((c) => c.type === "lean") || leanState() !== "off";
  const tabs = [["explain", "Explanation", ""], ["lean", "Lean goals", ""], ["log", "Kernel log", String(S.log.length)]] as const;
  for (const [key, label, badge] of tabs.filter(([k]) => (S.dev || k !== "log") && (hasLean || k !== "lean"))) {
    const t = asButton(h("div", `ptab${S.panelTab === key ? " on" : ""}`));
    t.setAttribute("aria-pressed", String(S.panelTab === key));
    t.append(document.createTextNode(label));
    if (badge) t.append(h("span", "badge", badge));
    t.addEventListener("click", () => { S.panelTab = key; setPanelOpen(true); });
    head.append(t);
  }
  head.append(h("div", "spacer"));
  const toggle = asButton(h("div", "pbtn", S.panelOpen ? "▾ Collapse" : "▴ Expand"), S.panelOpen ? "Collapse the explanation panel" : "Expand the explanation panel");
  toggle.addEventListener("click", () => setPanelOpen(!S.panelOpen));
  head.append(toggle);
}

/** Fold or unfold the panel by the user's hand, and remember it for the next load. (Opening it to
 *  show an explanation is not a choice, so that does not change what is remembered.) */
function setPanelOpen(open: boolean) {
  S.panelOpen = open;
  setPref("chalkmath.panel", open);
  renderPanelHead(); renderPanel();
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
  const parent = label.split(".").slice(0, -1).join(".");
  c2.append(h("h3", undefined, `Inside step ${parent}`));
  const trail = h("div", "trail");
  const nums = stepNumbers(steps);
  steps.forEach((s, i) => {
    const row = h("div", `trailrow${i === index ? " on" : ""}`);
    const l = nums[i] !== undefined ? `${parent}.${nums[i]}` : `${parent}.·`;
    row.append(h("span", "n", l), h("span", "rule", s.rule));
    if (nums[i] === undefined) row.title = "Not in the work list: the term prints the same before and after.";
    row.style.cursor = "pointer";
    row.addEventListener("click", () => { if (cell) selectSubStep(cell, steps, i, l, top); });
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
  panel.style.flex = S.panelOpen ? (narrow() ? "0 0 45%" : "0 0 250px") : "0 0 38px";
  let body = panel.querySelector(".panelbody") as HTMLElement;
  if (!body) { body = h("div", "panelbody"); panel.append(body); }
  body.hidden = !S.panelOpen;
  body.innerHTML = "";
  // the infoview never moves (its iframe would reload): it is shown or hidden where it is
  const info = leanInfoview();
  if (info.parentElement !== panel) panel.append(info);
  info.hidden = !S.panelOpen || S.panelTab !== "lean";
  if (!S.panelOpen) return;
  if (S.panelTab === "lean") { body.hidden = true; return; }

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
  const nums = stepNumbers(steps);
  const where = sel.term.kind !== "step" ? (sel.term.kind === "input" ? "in the input" : "in the output")
    : nums[sel.term.index] !== undefined ? `after step ${nums[sel.term.index]}` : "after a step the work list folds (the term prints the same)";

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
  if (doc) {
    const links = h("div", "sellinks");
    const more = asButton(h("span", "link", "In the documentation"));
    more.addEventListener("click", () => openDocs(fnPage(doc.name)));
    links.append(more);
    if (doc.ref) {
      const a = document.createElement("a");
      a.href = doc.ref; a.target = "_blank"; a.rel = "noreferrer"; a.textContent = "Definition and identities ↗";
      links.append(" · ", a);
    }
    c1.append(links);
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
      row.append(h("span", "no", nums[i] !== undefined ? String(nums[i]) : "·"), h("span", "rule", st.rule));
      if (rel) row.append(h("span", "rel", rel));
      row.title = rel === "created" ? "This rule built the selected node." : rel === "copied" ? "This rule moved or copied the selected node." : rel === "contains" ? "This rule fired inside the selected node." : "This rule did not touch the selection.";
      if (nums[i] === undefined) row.title += " Not in the work list: the term prints the same before and after.";
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
  try { katex.render(texSrc, el, { throwOnError: false, displayMode: false, strict: false, trust: TRUST_PATHS }); } catch { return empty; }
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
async function sendToScene(cell: Cell, target?: number | "new") {
  if (!cell.outLatex || !cell.echoLatex) return;
  await loadWork(cell);
  const failed = WORK_FAILED.get(cell);
  if (failed) { notify("err", failed); return; }
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
  notify("ok", `${shots.length} shots sent to ${ST.scenes[ST.active]!.name}`);
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

function currentWord(input: HTMLInputElement | HTMLTextAreaElement): { word: string; start: number } {
  const caret = input.selectionStart ?? input.value.length;
  const before = input.value.slice(0, caret);
  // a word, or a backslash abbreviation (possibly still empty: a bare `\` lists every symbol)
  const m = /(\\[A-Za-z_]*|[A-Za-z_][A-Za-z0-9_]*)$/.exec(before);
  return { word: m?.[0] ?? "", start: m ? caret - m[0].length : caret };
}

function updateCompletions(cell: Cell) {
  const input = cell.input!;
  if (ASK_CELL.test(input.value)) return hideCompletions();   // a question is words, not names
  // inside `x[[…]]`: the column names or keys that can go there, and All
  const part = partAt(cell, input);
  if (part) {
    const { ctx, help } = part;
    const q = ctx.typed.text.toLowerCase();
    const items: CompItem[] = help.names.filter((n) => n.toLowerCase().startsWith(q))
      .map((n) => ({ kind: "part" as const, insert: `"${n}"`, label: `"${n}"`, hint: help.namesAre ?? "name", start: ctx.typed.start }));
    if (!ctx.typed.quoted && "all".startsWith(q)) items.unshift({ kind: "part", insert: "All", label: "All", hint: "every position", start: ctx.typed.start });
    // nothing typed yet and nothing to name: the signature line says what is in range
    if (!items.length || (!q && !ctx.typed.quoted && !help.names.length)) return hideCompletions();
    const r = input.getBoundingClientRect();
    S.comp = { cell, items: items.slice(0, 9), index: 0, picked: false, x: r.left + 8, y: r.bottom + 4 };
    return renderCompletions();
  }
  const { word } = currentWord(input);
  if (word.length < 1) return hideCompletions();
  let items: CompItem[];
  if (word.startsWith("\\")) {
    const q = word.slice(1).toLowerCase();
    items = SYMBOLS.filter((s) => [s.abbr, ...s.aliases].some((a) => a.startsWith(q))).map((sym) => ({ kind: "sym", sym }));
    // unless the cell is kept as text, a template (`\frac`, `\int`, …) turns it typeset
    if (cellMode(cell) !== "raw" && cell.kind !== "λ-term") {
      for (const [name, t] of Object.entries(TEMPLATES)) if (name.toLowerCase().startsWith(q)) items.push({ kind: "tpl", name, what: t.what, glyph: t.glyph });
    }
  } else {
    items = [
      ...sessionNames(docOf(cell)?.sessionId ?? sessionId, word).filter((n) => n.name !== word).map((n) => ({ kind: "name" as const, ...n })),
      ...DOCS.filter((d) => !d.notation && d.name.toLowerCase().startsWith(word.toLowerCase()) && d.name !== word).map((doc) => ({ kind: "doc" as const, doc })),
    ];
  }
  if (!items.length) return hideCompletions();
  const r = input.getBoundingClientRect();
  S.comp = { cell, items: items.slice(0, 9), index: 0, picked: false, x: r.left + 8, y: r.bottom + 4 };
  renderCompletions();
}

function hideCompletions() { S.comp = null; renderCompletions(); }

function acceptCompletion() {
  if (!S.comp) return false;
  const { cell, items, index } = S.comp;
  const input = cell.input!;
  const { word, start } = currentWord(input);
  const item = items[index]!;
  if (item.kind === "part") {
    // replace what was typed (a bare word, or a name from its opening quote) through the caret, and
    // a closing quote already there
    const caret = input.selectionStart ?? input.value.length;
    let rest = input.value.slice(caret);
    if (item.insert.startsWith('"') && rest.startsWith('"')) rest = rest.slice(1);
    input.value = input.value.slice(0, item.start) + item.insert + rest;
    const pos = item.start + item.insert.length;
    input.setSelectionRange(pos, pos);
    cell.src = input.value;
    hideCompletions(); syncHighlight(cell); updateSigHelp(cell); renderSidebar();
    return true;
  }
  const after = input.value.slice(start + word.length);
  if (item.kind === "tpl") {
    hideCompletions();
    if (openTemplate(cell, input.value.slice(0, start) + "\\" + item.name, after)) return true;
    // the text around it does not read yet: the command stays as typed, to finish by hand
    input.value = input.value.slice(0, start) + "\\" + item.name + after;
    input.setSelectionRange(start + item.name.length + 1, start + item.name.length + 1);
    cell.src = input.value; syncHighlight(cell); renderSidebar();
    return true;
  }
  // a symbol abbreviation becomes the symbol itself; a function name opens its parenthesis
  const insert = item.kind === "sym" ? item.sym.sym : item.kind === "name" ? item.name + (item.call && !after.startsWith("(") ? "(" : "")
    : item.doc.name + (after.startsWith("(") ? "" : "(");
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
    } else if (it.kind === "name") {
      row.append(h("span", "n", it.name), h("span", "h", it.what));
    } else if (it.kind === "part") {
      row.append(h("span", "n", it.label), h("span", "h", it.hint));
    } else if (it.kind === "tpl") {
      row.classList.add("symrow");
      row.append(h("span", "n", `\\${it.name}`), h("span", "h", it.what), h("span", "sym", it.glyph));
    } else {
      const d = it.doc;
      row.append(h("span", "n", d.sig), h("span", "h", d.blurb.split(".")[0]!));
    }
    row.addEventListener("mousedown", (e) => { e.preventDefault(); S.comp!.index = i; acceptCompletion(); });
    row.addEventListener("mouseenter", () => { S.comp!.index = i; renderCompletions(); });
    box.append(row);
  });
  box.append(h("div", "compfoot", S.comp.items[0]!.kind === "doc" ? "Tab to accept · ↑↓ then Enter · Esc to dismiss" : "Tab or Enter to accept · Esc to dismiss"));
  document.body.append(box);
}

// --- Syntax highlighting: tokens, and the variables a call binds ---------------------------------

/** Names bound in a session by `let` (values and functions), keyed `session:name`. */
const USER_NAMES = new Set<string>();

/** Commands whose argument at `arg` is a variable bound over the call: `diff(f, x)`, `plot(f, x, …)`. */
const BINDERS: Record<string, number> = { diff: 1, integrate: 1, plot: 1, epicycles: 1, sum: 1, subst: 1, manipulate: 1 };
const BUILTIN_FN = new Set(["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im", "sign", "det", "rref", "transpose", "dot", "norm", "solve",
  "total", "mean", "variance", "stdev", "min", "max", "median"]);
const COMMANDS = new Set(["diff", "integrate", "plot", "manipulate", "epicycles", "dft", "import", "samplePoints", "matrix", "dimensions", "sum", "exptotrig", "expand", "factor", "simplify", "N", "subst", "poset", "map", "monotone", "lfp", "gfp", "fixpoints", "hasse", "join", "meet", "sup", "inf", "upper", "lower", "top", "bottom", "maximal", "minimal", "lattice", "le", "divisors", "subsets", "chain"]);
const CONSTANTS = new Set(["pi", "π", "e", "ℯ", "i", "phi", "φ", "All"]);

type Tok = { kind: "id" | "num" | "op" | "ws" | "kw" | "asset" | "str"; text: string; start: number };
function tokenize(src: string): Tok[] {
  const out: Tok[] = [];
  const re = /(\s+)|(\d+(?:\.\d+)?)|([A-Za-z_\u0370-\u03FFℯ][A-Za-z0-9_\u0370-\u03FFℯ']*)|(⟦[^⟧]*⟧?)|("[^"]*"?|'[^']*'?)|(:=|->|[^\sA-Za-z0-9_])/gu;
  let m: RegExpExecArray | null;
  while ((m = re.exec(src))) {
    if (m[1] !== undefined) out.push({ kind: "ws", text: m[0], start: m.index });
    else if (m[2] !== undefined) out.push({ kind: "num", text: m[0], start: m.index });
    else if (m[3] !== undefined) out.push({ kind: m[0] === "let" ? "kw" : "id", text: m[0], start: m.index });
    else if (m[4] !== undefined) out.push({ kind: "asset", text: m[0], start: m.index });
    else if (m[5] !== undefined) out.push({ kind: "str", text: m[0], start: m.index });
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
  // a question: the binding (if any) as code, the `?`, then the words as they are
  const q = /^(\s*(?:let\s+[A-Za-z_][A-Za-z0-9_]*\s*=\s*)?)\?/.exec(src);
  if (q) return `${q[1] ? highlightHtml(q[1]) : ""}<span class="hq">?</span><span class="hask">${esc(src.slice(q[0].length))}</span>`;
  const toks = tokenize(src);
  const bound = boundTokens(src, toks);
  const lambdaCell = /[λ\\]|:=/.test(src) || LAMBDA_CMD.test(src.trim());
  let out = "";
  toks.forEach((t, k) => {
    let cls = "";
    if (t.kind === "num") cls = "hnum";
    else if (t.kind === "kw") cls = "hkw";
    else if (t.kind === "asset") cls = S.assets[t.text.slice(1, -1)] ? "hasset" : "hasset missing";
    else if (t.kind === "str") cls = "hstr";
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
function renderHighlights() { for (const c of S.cells) { if (c.hl) delete c.hl.dataset["src"]; syncHighlight(c); c.mi?.render(); } }

// --- Signature help: the call around the caret, its parameters, the current one in bold ---------

/** Session-defined functions (`let f(x, y) = e`), keyed by session and name, for signature help. */
const USER_FNS = new Map<string, string[]>();

/** The innermost call the caret is inside: its name, where its `(` is, and which argument the caret
 *  is in. Balanced groups before the caret are skipped; an unclosed `[`/`{` or a bare grouping `(` is
 *  part of an argument, so the walk continues outward. */
function callContext(input: HTMLInputElement | HTMLTextAreaElement): { name: string; open: number; arg: number; firstArg: string } | null {
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

/** The signature to show for a call: a session function first, else the reference's usage line for
 *  `name(` — the first with room for the argument the caret is in (`diff(f, x, n)` once a third is
 *  typed); `plot` picks its list form when the first argument starts with `[`. */
function sigFor(name: string, firstArg: string, arg = 0): { sig: string; blurb: string } | null {
  const user = USER_FNS.get(`${sessionId}:${name}`);
  if (user) return { sig: `${name}(${user.join(", ")})`, blurb: "Defined in this session with let." };
  for (const f of FUNCTIONS) {
    const alts = f.usage.filter(([form]) => form.startsWith(name + "("));
    if (!alts.length) continue;
    const fit = alts.filter(([form]) => sigPieces(form).filter((p) => p.param).length > arg);
    const pool = fit.length ? fit : alts;
    const [form, what] = (pool.length > 1 && firstArg.startsWith("[") ? pool.find(([a]) => a.startsWith(name + "([")) : undefined) ?? pool[0]!;
    const blurb = plainUsage(what);
    return { sig: form, blurb: blurb[0]!.toUpperCase() + blurb.slice(1) };
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

/** Inside `x[[…]]` at the caret: what `x` is (a file, a part of one, or a bound matrix) and what the
 *  index being typed can be. */
function partAt(cell: Cell, input: HTMLInputElement | HTMLTextAreaElement) {
  return partIn(cell, input.value.slice(0, input.selectionStart ?? input.value.length));
}
/** The same, given the cell's text up to the caret (a visual input writes it). */
function partIn(cell: Cell, before: string) {
  const ctx = partContext(before);
  if (!ctx) return null;
  const d = docOf(cell);
  const sid = d?.sessionId ?? sessionId;
  const value = fileExprValue(ctx.base, fileScope(sid, d?.assets ?? S.assets))
    ?? (() => { const sh = MATRIX_SHAPES.get(`${sid}:${ctx.base}`); return sh ? { kind: "numbers" as const, ...sh, single: false } : null; })();
  const help = value && partHelp(value, ctx.specs, ctx.arg);
  return help ? { ctx, help } : null;
}

/** The signature line inside a part: its indices, the one at the caret bold, and what is in range. */
function partSig(cell: Cell, key: string, { ctx, help }: NonNullable<ReturnType<typeof partIn>>) {
  const pieces: SigPiece[] = [{ text: `${ctx.base}[[`, param: false }];
  help.params.forEach((p, i) => { if (i) pieces.push({ text: ", ", param: false }); pieces.push({ text: p, param: true }); });
  pieces.push({ text: "]]", param: false });
  return { cell, key, sig: pieces.map((p) => p.text).join(""), blurb: help.blurb, arg: Math.min(ctx.arg, help.params.length - 1), pieces };
}

function updateSigHelp(cell: Cell) {
  const input = cell.input;
  if (!S.sigHelp || !input || document.activeElement !== input || ASK_CELL.test(input.value)) return hideSigHelp();
  const part = partAt(cell, input);
  if (part) {
    const key = `${cell.id}:[[${part.ctx.base}`;
    if (S.sigDismissed === key) return hideSigHelp();
    S.sig = partSig(cell, key, part);
    return renderSigHelp();
  }
  const ctx = callContext(input);
  const found = ctx && sigFor(ctx.name, ctx.firstArg, ctx.arg);
  if (!ctx || !found) { S.sigDismissed = null; return hideSigHelp(); }
  const key = `${cell.id}:${ctx.open}`;
  if (S.sigDismissed === key) return hideSigHelp();
  S.sigDismissed = null;
  S.sig = { cell, key, sig: found.sig, blurb: found.blurb, arg: ctx.arg };
  renderSigHelp();
}
/** Signature help for a visual input: the call around its caret that shows as `name(args)`. */
function updateVisualSigHelp(cell: Cell) {
  // in an index of a part: what can go there, as for the text input
  const pb = S.sigHelp && cell.mi ? cell.mi.edit.partBefore() : null;
  const part = pb && partIn(cell, pb.text);
  if (part) {
    const key = `${cell.id}:[[${part.ctx.base}`;
    if (S.sigDismissed === key) return hideSigHelp();
    S.sig = partSig(cell, key, part);
    return renderSigHelp();
  }
  const ctx = S.sigHelp && cell.mi ? cell.mi.edit.callContext() : null;
  const found = ctx && sigFor(ctx.name, ctx.firstArg, ctx.arg);
  if (!ctx || !found) { S.sigDismissed = null; return hideSigHelp(); }
  const key = `${cell.id}:${ctx.name}`;
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
  const anchor = g && (g.cell.input ?? g.cell.mi?.el);
  if (!g || !anchor) return;
  const box = h("div", "sighelp");
  const line = h("div", "ss");
  const pieces = g.pieces ?? sigPieces(g.sig), n = pieces.filter((p) => p.param).length;
  let k = 0;
  for (const p of pieces) {
    if (!p.param) { line.append(p.text); continue; }
    const on = k === g.arg || (g.arg >= n && k === n - 1 && p.text.endsWith("…"));
    line.append(on ? h("b", undefined, p.text) : document.createTextNode(p.text));
    k++;
  }
  box.append(line, h("div", "sb", g.blurb));
  const r = anchor.getBoundingClientRect();
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

// --- Usage on hover: a function's usage lines over its name in a cell, after a pause -----------------
// Mathematica shows a symbol's usage when the pointer rests on it. Here the name of a command or a
// function in a cell's input (text or typeset) shows its usage lines after a pause, with a link to
// its page; the tip stays while the pointer is on it, so the link can be followed.

const USAGE_DELAY = 650;
let usageTimer = 0;
let usageFor: { name: string; el: Element } | null = null;
/** The function name under the pointer in a cell's input, with the element it is drawn in. */
function nameAt(ev: MouseEvent): { name: string; rect: DOMRect; el: Element } | null {
  const t = ev.target as Element | null;
  if (!t) return null;
  // typeset input: the editor marks a call's name with its highlight class
  const typeset = t.closest?.('.mi [data-hl="hcmd"], .mi [data-hl="hfn"]');
  if (typeset) { const name = typeset.textContent?.trim() ?? ""; return FN_BY_NAME.has(name) ? { name, rect: typeset.getBoundingClientRect(), el: typeset } : null; }
  // text input: the highlight overlay under it has a span per token
  if (t instanceof HTMLInputElement && t.classList.contains("cellin")) {
    const hl = t.parentElement?.querySelector(".hl");
    for (const sp of hl?.querySelectorAll(".hcmd, .hfn") ?? []) {
      const r = sp.getBoundingClientRect();
      if (ev.clientX >= r.left && ev.clientX <= r.right && ev.clientY >= r.top && ev.clientY <= r.bottom) {
        const name = sp.textContent ?? "";
        return FN_BY_NAME.has(name) ? { name, rect: r, el: sp } : null;
      }
    }
  }
  return null;
}
function hideUsage() { clearTimeout(usageTimer); usageFor = null; document.querySelector(".usagetip")?.remove(); }
/** The usage tip for `name`, under `rect`. */
function showUsage(name: string, rect: DOMRect) {
  document.querySelector(".usagetip")?.remove();
  const f = FN_BY_NAME.get(name); if (!f) return;
  const tip = h("div", "usagetip");
  tip.setAttribute("role", "tooltip");
  for (const [form, what] of f.usage) {
    const row = h("div", "ur");
    row.append(h("code", "uf", plainUsage(form)), inlineMath(plainUsage(what), "uw"));
    tip.append(row);
  }
  const more = document.createElement("a");
  more.href = `#fn:${name}`; more.className = "umore"; more.textContent = `${f.title ?? name} — documentation ›`;
  more.addEventListener("click", (e) => { e.preventDefault(); hideUsage(); openDocs(`fn:${name}`); });
  tip.append(more);
  tip.addEventListener("mouseleave", hideUsage);
  document.body.append(tip);
  const w = tip.offsetWidth, hgt = tip.offsetHeight;
  tip.style.left = `${Math.max(8, Math.min(rect.left, window.innerWidth - w - 8))}px`;
  tip.style.top = `${rect.bottom + 6 + hgt > window.innerHeight ? Math.max(8, rect.top - hgt - 6) : rect.bottom + 6}px`;
}
let usageHide = 0;
document.addEventListener("mousemove", (ev) => {
  if ((ev.target as Element | null)?.closest?.(".usagetip")) { clearTimeout(usageHide); return; }
  const at = nameAt(ev);
  if (at && usageFor && usageFor.name === at.name && usageFor.el === at.el) { clearTimeout(usageHide); return; }
  // a tip on screen waits a moment, so the pointer can cross to it and follow its link
  if (!at && document.querySelector(".usagetip")) { clearTimeout(usageHide); usageHide = window.setTimeout(hideUsage, 300); return; }
  clearTimeout(usageHide);
  hideUsage();
  if (!at || S.comp) return;
  usageFor = { name: at.name, el: at.el };
  usageTimer = window.setTimeout(() => { if (usageFor?.el === at.el) showUsage(at.name, at.el.getBoundingClientRect()); }, USAGE_DELAY);
}, { passive: true });
document.addEventListener("keydown", hideUsage, true);
document.addEventListener("scroll", hideUsage, { capture: true, passive: true });

// ---------------------------------------------------------------------------
// Keyboard
// ---------------------------------------------------------------------------

function onKey(ev: KeyboardEvent, cell: Cell, i: number) {
  if (modeKey(ev, cell)) return;
  if (ev.key === "Enter" && ev.shiftKey && cell.input && !S.comp?.picked) {
    // a new line: the cell becomes (or stays) a textarea, and Enter still runs it
    ev.preventDefault(); hideCompletions();
    const input = cell.input, a = input.selectionStart ?? input.value.length, b = input.selectionEnd ?? a;
    const v = `${input.value.slice(0, a)}\n${input.value.slice(b)}`;
    cell.src = v;
    if (input instanceof HTMLTextAreaElement) { input.value = v; input.setSelectionRange(a + 1, a + 1); fitRows(input); syncHighlight(cell); }
    else { refreshInput(cell); cell.input?.focus(); cell.input?.setSelectionRange(a + 1, a + 1); }
    renderSidebar(); autosave();
    return;
  }
  if (ev.key === " " && cell.input) {
    // `\frac` then space in the text: the cell goes typeset with the template in place
    const input = cell.input, at = input.selectionStart ?? input.value.length;
    if (openTemplate(cell, input.value.slice(0, at), input.value.slice(input.selectionEnd ?? at))) { ev.preventDefault(); hideCompletions(); return; }
  }
  if (S.comp) {
    if (ev.key === "ArrowDown") { ev.preventDefault(); S.comp.picked = true; S.comp.index = (S.comp.index + 1) % S.comp.items.length; return renderCompletions(); }
    if (ev.key === "ArrowUp") { ev.preventDefault(); S.comp.picked = true; S.comp.index = (S.comp.index - 1 + S.comp.items.length) % S.comp.items.length; return renderCompletions(); }
    if (ev.key === "Tab") { ev.preventDefault(); acceptCompletion(); return; }
    // Enter takes a row only once one is picked (or for a `\` abbreviation, which cannot run as typed):
    // `d` then Enter runs `d`, not `diff(`
    if (ev.key === "Enter" && (S.comp.picked || currentWord(cell.input!).word.startsWith("\\"))) { ev.preventDefault(); acceptCompletion(); return; }
    if (ev.key === "Enter") hideCompletions();
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
  // in a cell of several lines the arrows move between lines, and leave the cell from its first or last
  const ta = cell.input instanceof HTMLTextAreaElement ? cell.input : null;
  const onFirst = !ta || !ta.value.slice(0, ta.selectionStart ?? 0).includes("\n");
  const onLast = !ta || !ta.value.slice(ta.selectionEnd ?? ta.value.length).includes("\n");
  if (ev.key === "ArrowDown" && onLast && i < S.cells.length - 1) { ev.preventDefault(); focusCell(i + 1); }
  if (ev.key === "ArrowUp" && onFirst && i > 0) { ev.preventDefault(); focusCell(i - 1); }
}

// ---------------------------------------------------------------------------
// Boot
// ---------------------------------------------------------------------------

initTheme();
initLeanIsolation();
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
trackViewSection();
document.addEventListener("keydown", (ev) => {
  if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === "s") { ev.preventDefault(); if (ev.shiftKey) saveNotebookAs(); else saveNotebook(); }
  if ((ev.metaKey || ev.ctrlKey) && !ev.shiftKey && ev.key.toLowerCase() === "b") { ev.preventDefault(); toggleSidebar(); }
  if (ev.key === "Escape") closeModal();
  if (ev.key === "Escape" && S.menu) { const m = S.menu; S.menu = null; renderChrome(); $<HTMLElement>(`.menus [data-menu="${m}"]`)?.focus(); }
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
      const d = makeDoc(file.name ?? "untitled.chalk", cellsFromFile(file), Array.isArray(file.scenes) ? file.scenes : [], assetsFromFile(file));
      if (!d.cells.length) d.cells.push(freshCell());
      d.hydrated = false;
      const pr = projectRefOf(file);
      if (pr) d.project = pr;
      if (typeof file.leanPrelude === "string" && file.leanPrelude) d.leanPrelude = file.leanPrelude;
      S.docs.push(d);
      // the saved text is what the tab compares against; a dirty document compares against nothing
      d.text = JSON.stringify({ chalk: 1, name: d.name, cells: file.cells, scenes: d.scenes, ...(Object.keys(d.assets).length ? { assets: d.assets } : {}), ...(pr ? { project: pr } : {}), ...(d.leanPrelude ? { leanPrelude: d.leanPrelude } : {}) }, null, 2);
      d.savedText = dirty ? "" : d.text;
    }
    restoredActive = "chalkmath" in parsed && typeof parsed.active === "number" ? parsed.active : 0;
  } catch { /* ignore a corrupt autosave */ }
}
// a first visit gets an empty notebook at once, replaced by the welcome notebook when it arrives
const firstVisit = !S.docs.length && !location.hash.startsWith("#nb");
if (!S.docs.length) S.docs.push(makeDoc("untitled.chalk", [freshCell()]));
S.doc = -1;
loadDoc(Math.min(restoredActive, S.docs.length - 1));
if (!saved) { const d = currentDoc(); if (d) d.savedText = serializeNotebook(); }
if (firstVisit) void openExample("welcome.chalk").then((ok) => {
  // served without examples/ (a bare dev server): a few cells to start from instead
  const d = currentDoc();
  if (ok || !d || !docPristine(d)) return;
  S.cells.splice(0, S.cells.length, ...SAMPLES.map((src) => freshCell(src)), freshCell());
  d.savedText = serializeNotebook(); renderCells(); renderSidebar(); renderChrome();
});
void loadProjects();
void connect().then(async () => {
  // a link with a notebook in its fragment opens that notebook (in its own tab unless the current one is untouched)
  if (location.hash.startsWith("#nb") && await openNotebookLink(location.hash)) return;
  const d = currentDoc(); if (d && !d.hydrated && S.kernel === "ready" && S.runOnOpen) hydrate(d);
});
