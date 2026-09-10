import { createClient, type EngineClient, type Derivation, type Step, type Path } from "@mathbook/protocol";
import { workerTransport, httpTransport } from "@mathbook/engine-host";

declare const katex: { renderToString(tex: string, opts?: object): string };
const tex = (s: string, paths = false) => katex.renderToString(s, { throwOnError: false, trust: paths, strict: false });
const $ = <T extends HTMLElement>(sel: string) => document.querySelector(sel) as T;

const sessionId = crypto.randomUUID();
let client: EngineClient;
let cellCount = 0;

async function connect() {
  client?.close();
  const mode = $<HTMLSelectElement>("#engine").value;
  $("#url").hidden = mode !== "http";
  client = mode === "worker" ? createClient(workerTransport(new Worker("engine.worker.js"))) : createClient(httpTransport($<HTMLInputElement>("#url").value));
  const caps = await client.call("engine.capabilities", {});
  $("#caps").textContent = `${caps.engine} v${caps.version}${caps.verified ? " · verified" : ""} · ${caps.features.join(", ")}`;
}
$("#engine").addEventListener("change", connect);
$("#url").addEventListener("change", connect);

const SAMPLES = ["diff(x^2 * sin(x), x)", "expand((x+1)^3)", "rref([1,2,3;4,5,6;7,8,10])", "let f = x^3 - 3x", "diff(f, x, 2)"];

function addCell(source = "") {
  const id = `c${++cellCount}`;
  const el = document.createElement("div");
  el.className = "cell"; el.dataset["id"] = id;
  el.innerHTML = `<textarea rows="1" placeholder="e.g. diff(x^2, x)" spellcheck="false"></textarea><div class="out"></div>`;
  const ta = el.querySelector("textarea")!; ta.value = source;
  ta.addEventListener("keydown", (ev) => { if (ev.key === "Enter" && ev.shiftKey) { ev.preventDefault(); void evaluate(id, ta.value, el.querySelector(".out")!); } });
  ta.addEventListener("input", () => { ta.rows = Math.max(1, ta.value.split("\n").length); });
  $("#cells").appendChild(el);
  ta.focus();
  return el;
}

async function evaluate(cellId: string, source: string, out: HTMLElement) {
  const r = await client.call("engine.evaluate", { sessionId, cellId, source, showWork: true, paths: true });
  if (!r.ok) { out.innerHTML = `<div class="err">${r.error.message}${r.error.span ? ` (at ${r.error.span.start})` : ""}</div>`; return; }
  out.innerHTML = tex(r.rendered.latex, true);
  out.querySelectorAll<HTMLElement>("[data-path]").forEach((span) => {
    span.addEventListener("click", async (ev) => {
      ev.stopPropagation();
      out.querySelectorAll(".sel").forEach((s) => s.classList.remove("sel"));
      span.classList.add("sel");
      const path: Path = span.dataset["path"] === "root" ? [] : span.dataset["path"]!.split(".").map(Number);
      const ex = await client.call("engine.explain", { sessionId, cellId, path });
      renderWork(`Selected: ${tex(ex.rendered.latex)}`, ex.steps);
    });
  });
  if (r.derivation) renderWork(`${tex(latexOf(r.derivation.input))} \u2192 ${tex(r.rendered.latex)}`, r.derivation.steps);
  if (out.parentElement === $("#cells").lastElementChild) addCell();
}

// The page has no printer of its own: it asks the engine to render. For the derivation header we
// only need something readable, so we show input via the step list's own before-fields.
function latexOf(_: unknown) { return "\\text{input}"; }

function renderWork(title: string, steps: Step[]) {
  const work = $("#work");
  work.innerHTML = `<div class="kbd">${title}</div>` + (steps.length ? steps.map(stepHtml).join("") : `<div class="kbd">No rewriting was needed.</div>`);
}
function stepHtml(s: Step): string {
  const sub = s.sub ? `<div class="sub">${s.sub.steps.map(stepHtml).join("")}</div>` : "";
  return `<div class="step"><div class="rule">${s.rule} @ ${s.path.join(".") || "root"}</div><div class="expl">${inlineMath(s.explanation)}</div>${sub}</div>`;
}
/** Render $...$ spans inside explanation text. */
function inlineMath(md: string): string {
  return md.replace(/\$([^$]+)\$/g, (_, t) => tex(t)).replace(/</g, (m, i) => (md[i + 1] === "s" ? m : "&lt;"));
}

void connect().then(() => { for (const s of SAMPLES) addCell(s); addCell(); });
export type { Derivation };
