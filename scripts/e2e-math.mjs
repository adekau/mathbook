// Math cells, end to end in Chromium: the bundled notebook (npm run bundle) against the native engine
// over HTTP (cd engine && lake build). Each case is typed into a cell and run the way a reader runs it.
// Checked: the engine's answer is the expected one (its text form, as in engine/Tests/golden.tsv), the
// page shows exactly that answer (its LaTeX, as the engine sends it to a client of its own), a session
// carries `let` bindings from one cell to the next, an error shows as the cell's error, and opening a
// cell's work shows the step that produced the answer, under the notebook's name for its rule.
//   node scripts/e2e-math.mjs [screenshot.png]
// Then the notebook's teaching features, in a notebook of their own: a cell out of date when a name it
// read changes, a slider driving the cells below it, work stepped through with the answer held back,
// an exercise written in its editor and answered (wrong, right, and with the work), a Markdown
// callout, a function's usage on hover, a truth table and a relation's graph, an operation table, a
// typing tree, a logic exercise, a system typed over several lines, manipulate (a plot played, a
// derivative and a column of a plot and a calculation dragged, against the engine's own frames), and a
// course's lesson opened from the Courses tab, answered, and followed to the next. Each is held to the
// engine's own answers through a client of the test's.
// Chromium: playwright-core's own, or the executable named by CHROMIUM. The engine: MATHENGINE, or
// engine/.lake/build/bin/mathengine.
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { readFileSync, statSync } from "node:fs";
import assert from "node:assert/strict";
import path from "node:path";
import { startServer } from "../packages/engine-host/dist/server.js";
import { httpTransport } from "../packages/engine-host/dist/index.js";
import { createClient } from "../packages/protocol/dist/index.js";

/** What to type, the engine's answer as text (or its error), and a step the cell's work must show. */
const CASES = [
  { src: "diff(sin(x)*exp(x), x)", text: "cos(x)*exp(x) + exp(x)*sin(x)", step: "Product rule" },
  { src: "let f = x^2 + 3x", text: "x^2 + 3*x" },
  { src: "diff(f, x)", text: "2*x + 3", step: "Sum rule" },
  { src: "[1,2;3,4] * [5,6;7,8]", text: "[19, 22; 43, 50]", step: "Matrix product" },
  { src: "[1, 2] ./ [3, 10]", text: "[1/3, 1/5]", step: "Entrywise division" },
  { src: "rref([1,2;2,4])", text: "[1, 2; 0, 0]", step: "Add a multiple of a row" },
  { src: "[1,2] * [1,2]", error: "inner dimensions must match" },
  // a law split at its assumption: the step that assumes says so
  { src: "exp(ln(w))", text: "w", step: "Function value, assuming a positive argument" },
  { src: "t*t^(-1)", text: "1", step: "Collect powers, assuming the base" },
  // the logic world, and relations in the order world
  { src: "cnf(p ∨ (q ∧ r))", text: "(p ∨ q) ∧ (p ∨ r)", step: "Distribute" },
  { src: "taut(p → q)", text: "⊥", step: "False when p = true, q = false" },
  { src: "∀ n ∈ 1..10, n^2 ≥ 2n", text: "⊥", step: "Check every element" },
  { src: "let R = rel({a, b, c}; a->b, b->c)", text: "{(a, b), (b, c)}" },
  { src: "closure(R, transitive)", text: "{(a, b), (b, c), (a, c)}", step: "Transitive closure" },
  { src: "cnf(p ∨)", error: "expected a formula" },
  // finite algebra
  { src: "let FA = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])", text: "[na, permit, deny; permit, permit, permit; deny, deny, deny]" },
  { src: "fold(FA; na, deny, permit)", text: "deny", step: "Combine" },
  { src: "let RPS = op({r, p, s}; [r, p, r; p, p, s; r, s, s])", text: "[r, p, r; p, p, s; r, s, s]" },
  { src: "associative(RPS)", text: "false", step: "Not associative" },
  { src: "lattice(product(chain(2), chain(3)))", text: "true", step: "Inner call" },
  { src: "replicas(gcounter; a, b; a: inc; m := a; a: inc; b <- m; a -> b)", text: "{a↦2, b↦2}", step: "b merges the message m" },
  // term rewriting, in the systems world
  { src: "let Add = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", text: "{add(0, y) → y, add(s(x), y) → s(add(x, y))}" },
  { src: "rewrite(Add, add(s(0), s(0)))", text: "s(s(0))", step: "Rewrite" },
  { src: "terminates(Add; add(x, y) = 2x + y, s(x) = x + 1)", text: "true", step: "Decreases" },
  { src: "rules(x -> a)", error: "the left side is a variable" },
  // transition systems
  { src: "let Ct = system(var x in 0..2; init x = 0; action inc when x < 2 do x := x + 1)", text: "system({x}, {inc})" },
  { src: "invariant(Ct, x ≤ 1)", text: "false", step: "inc (x < 2 holds)" },
  { src: "ctl(Ct, EF x = 2)", text: "true", step: "Round 1" },
  // the λ-calculus: a strategy, and the simply typed calculus
  { src: "cbv: (λx. x) ((λy. y) z)", text: "z", step: "Beta" },
  { src: "type: λf:A→B. λx:A. f x", text: "(A → B) → A → B", step: "→E (application)" },
  { src: "infer: S", text: "(α → β → γ) → (α → β) → α → γ", step: "Unify" },
  { src: "type: λx:A. x x", error: "not a function type" },
  // a Church name at the head is a λ-term only when the cell reads as one
  { src: "fst (pair a b)", text: "a" },
  { src: "S + 1", text: "S + 1" },
];

const root = path.resolve(import.meta.dirname, "..");
const dist = path.join(root, "apps/notebook/dist");
const exe = process.env.MATHENGINE ?? path.join(root, "engine/.lake/build/bin/mathengine");
const shot = process.argv[2];
const types = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".wasm": "application/wasm", ".json": "application/json", ".svg": "image/svg+xml", ".chalk": "application/json" };
const site = createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(new URL(req.url, "http://x").pathname).replace(/\/$/, "/index.html"));
  try { if (!statSync(file).isFile()) throw 0; } catch { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { "content-type": types[path.extname(file)] ?? "application/octet-stream" });
  res.end(readFileSync(file));
}).listen(0);
const engine = startServer(0, exe);
await new Promise((r) => engine.once("listening", r));
const base = `http://localhost:${site.address().port}`;
const engineUrl = `http://localhost:${engine.address().port}`;

// the same sources in a session of the test's own: what the engine answers, to hold the page to
const reference = createClient(httpTransport(engineUrl));
/** LaTeX as compared: no path annotations, braces or spaces (KaTeX's annotation keeps neither exactly). */
const flat = (tex) => tex.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "");

const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const page = await browser.newPage({ viewport: { width: 1180, height: 1400 } });
// errors before the engine is switched to HTTP are the wasm worker missing from a bundle without it
const pageErrors = [];
let connected = false;
page.on("pageerror", (e) => { if (connected) pageErrors.push(e.message); });

const cells = () => page.locator(".cell:not(.markdown):not(.section)");
async function run(i, src) {
  const input = cells().nth(i).locator("input.cellin");
  await input.click(); await input.fill(src); await input.press("Enter");
}
/** A cell's output (the engine's LaTeX, as KaTeX keeps it) or error, once it has finished. */
async function out(i) {
  await page.waitForFunction((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    return c && !c.classList.contains("running") && (c.querySelector(".outval") || c.querySelector(".cellerr"));
  }, i, { timeout: 30000 });
  return page.evaluate((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    return { tex: c.querySelector(".outval .katex-mathml annotation")?.textContent ?? null, err: c.querySelector(".cellerr")?.textContent ?? null };
  }, i);
}
/** Open a cell's work and read the names of its steps, nested ones included. */
async function work(i) {
  const cell = cells().nth(i);
  await cell.locator(".cellacts [aria-expanded]").click();
  await cell.locator(".work:not(.pending) .step").first().waitFor({ timeout: 30000 });
  return cell.locator(".work .step .rule").allTextContents();
}

const all = () => page.locator(".cell");
/** Wait until cell `i` (of every kind) shows `latex` as its output. */
async function outIs(i, latex, what) {
  await page.waitForFunction(([k, want]) => {
    const c = document.querySelectorAll(".cell")[k];
    const tex = c?.querySelector(".outval .katex-mathml annotation")?.textContent ?? "";
    const flat = (t) => t.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "");
    return !c?.classList.contains("running") && flat(tex) === want;
  }, [i, flat(latex)], { timeout: 30000 }).catch(async () => {
    const tex = await all().nth(i).locator(".outval .katex-mathml annotation").first().textContent().catch(() => null);
    assert.fail(`${what}: the cell shows ${JSON.stringify(tex)}, not ${JSON.stringify(latex)}`);
  });
}
/** A cell's ⋮ menu item. */
async function cellMenu(i, item) {
  await all().nth(i).hover();
  await all().nth(i).locator(".cellacts .more").click();
  await page.locator(".cellmenu .item", { hasText: item }).first().click();
}
const menu = async (m, item) => { await page.locator(".menus span", { hasText: m }).click(); await page.locator(".dropdown .item", { hasText: item }).first().click(); };
/** The engine's own answer, in a session of the test's that follows the notebook's. */
const ref = (source, k) => reference.call("engine.evaluate", { sessionId: "e2e-features", cellId: `f${k}`, source, paths: true });

/** manipulate, in a notebook of its own: a plot's slider played from the first frame to the last with
 *  its axes held still, and a derivative's slider dragged, each frame the engine's own. */
async function manipulate() {
  await menu("File", "New notebook");
  const src = "manipulate(plot([x^2, 1 + (2 + h)*(x - 1)], x, -0.5, 3), h, 2, 0.5, 4)";
  const want = await reference.call("engine.manipulate", { sessionId: "e2e-manip", cellId: "p", source: src });
  assert.equal(want.ok, true, `${src}: ${want.error?.message}`);
  assert.deepEqual(want.frames.map((f) => f.value), [2, 1.5, 1, 0.5], "the engine's values of h");
  await run(0, src);
  const box = all().nth(0).locator(".manip");
  await box.locator(".plotbox svg").waitFor({ timeout: 30000 });
  const svg = box.locator(".plotbox svg");
  const label = (f) => `Plot of ${f.plot.series.map((s) => s.rendered.text).join(" and ")}`;
  assert.ok((await svg.getAttribute("aria-label")).startsWith(label(want.frames[0])), "the first frame is not the engine's");
  assert.equal(await box.locator("input[type=range]").getAttribute("max"), "3", "one slider position per frame");
  const ticks = () => box.locator(".plotbox svg text.tl.r").allTextContents();
  const before = await ticks();
  const play = box.locator(".sliderplay");
  assert.equal((await play.textContent()).trim(), "▶ Play", "no ▶ Play");
  await play.click();
  await box.locator(".sliderplay.on").waitFor({ timeout: 5000 });
  await box.locator(".sliderplay:not(.on)").waitFor({ timeout: 15000 });
  assert.ok((await svg.getAttribute("aria-label")).startsWith(label(want.frames[3])), `the play did not end on the engine's last frame: ${await svg.getAttribute("aria-label")}`);
  assert.equal(await box.locator(".sliderval .katex-mathml annotation").textContent(), want.frames[3].valueRendered.latex, "the value shown at the end");
  assert.deepEqual(await ticks(), before, "the axes moved while h played");
  // any body: a derivative, its slider dragged to the last of its values, shown as its calculation
  const flatTex = (t) => t.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "");
  /** The text a part shows once its slider is at the last value: wait for it to end in `want`. */
  async function lastLine(i, part, want) {
    const box = all().nth(i).locator(".manip");
    await box.locator(".manipbody").first().waitFor({ timeout: 30000 });
    await box.locator("input[type=range]").focus();
    await page.keyboard.press("End");
    const line = () => box.locator(".manippart").nth(part).locator(".manipbody .katex-mathml annotation").textContent();
    await page.waitForFunction(([k, j, w]) => {
      const t = document.querySelectorAll(".cell")[k]?.querySelectorAll(".manippart")[j]?.querySelector(".manipbody .katex-mathml annotation")?.textContent ?? "";
      return t.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "").endsWith(w);
    }, [i, part, flatTex(want)], { timeout: 10000 }).catch(async () => assert.fail(`cell ${i}, part ${part} shows ${await line()}, which does not end in ${want}`));
    return flatTex(await line());
  }
  const src2 = "manipulate(diff(x^n, x), n, 1, 3, 3)";
  const want2 = await reference.call("engine.manipulate", { sessionId: "e2e-manip", cellId: "d", source: src2 });
  await run(1, src2);
  await lastLine(1, 0, want2.frames[2].rendered.latex);
  // a column: a plot and a calculation under one slider, the calculation from h put in to the value
  const src3 = "manipulate(column(plot([x, h*x], x, 0, 1), h^2 + 1), h, 1, 3, 3)";
  const want3 = await reference.call("engine.manipulate", { sessionId: "e2e-manip", cellId: "c", source: src3 });
  assert.equal(want3.frames[2].parts?.length, 2, "the engine's column has two parts");
  await run(2, src3);
  // wait for the output: the cell is evaluated after Enter, not by it
  await all().nth(2).locator(".manip .manippart").nth(1).waitFor({ timeout: 30000 }).catch(async () =>
    assert.fail(`the column's output did not appear: ${await all().nth(2).locator(".cellerr").textContent({ timeout: 1000 }).catch(() => "no error shown")}`));
  assert.equal(await all().nth(2).locator(".manip .manippart").count(), 2, "one place per part");
  const calc = want3.frames[2].parts[1];
  const shown = await lastLine(2, 1, calc.rendered.latex);
  assert.ok(!calc.work || shown.startsWith(flatTex(calc.work[0].latex)), `the calculation does not start from h put in: ${shown}`);
  assert.ok(await all().nth(2).locator(".manip .manippart").nth(0).locator(".plotbox svg").count(), "the column's plot is not drawn");
  console.log(`✓ manipulate: h played over ${want.frames.length} frames with the axes held; diff(x^n, x) at n = 3 is ${want2.frames[2].rendered.text}; a column's plot and calculation, h^2 + 1 = ${calc.rendered.text} at h = 3`);
}

/** The teaching features, in a fresh notebook, then a course. */
async function features() {
  await menu("File", "New notebook");
  // out of date: a cell that read a name whose value has changed says so, and runs again
  await run(0, "let a = 2"); await out(0);
  await run(1, "diff(sin(a*x), x)");
  await ref("let a = 2", 0);
  await outIs(1, (await ref("diff(sin(a*x), x)", 1)).rendered.latex, "diff with a = 2");
  await run(0, "let a = 3");
  await page.locator(".cell.stale .stalebar code", { hasText: "a" }).first().waitFor({ timeout: 30000 });
  await all().nth(1).locator(".stalebtn", { hasText: "Run again" }).click();
  await ref("let a = 3", 2);
  await outIs(1, (await ref("diff(sin(a*x), x)", 3)).rendered.latex, "diff with a = 3, run again");
  assert.equal(await page.locator(".cell.stale").count(), 0, "a cell is still out of date after running again");
  console.log("✓ out of date: a changed, the cell said so, and ran again");
  // a slider: one step right rewrites the number and runs the cell below
  await cellMenu(0, "Show as a slider");
  await all().nth(0).locator(".sliderrow input[type=range]").focus();
  await page.keyboard.press("ArrowRight");
  await ref("let a = 4", 4);
  await outIs(1, (await ref("diff(sin(a*x), x)", 5)).rendered.latex, "diff after the slider moved to 4");
  assert.equal(await all().nth(0).locator("input.cellin").inputValue(), "let a = 4", "the slider rewrites its cell");
  console.log("✓ slider: a = 4, and the cell below followed");
  // step through: the work comes one step at a time, the answer last
  await cellMenu(1, "Step through the work");
  const c1 = all().nth(1);
  await c1.locator(".stepnext [data-next]").waitFor({ timeout: 30000 });
  assert.equal(await c1.locator(".work .step").count(), 0, "steps shown before the first was asked for");
  assert.equal(await c1.locator(".outheld").count(), 1, "the answer is not held back");
  await c1.locator(".stepnext [data-next]").click();
  assert.equal(await c1.locator(".work .step:not(.sub)").count(), 1, "one step after ▸ First step");
  await c1.locator(".stepnext .stepbtn", { hasText: "Show all" }).click();
  assert.equal(await c1.locator(".outheld").count(), 0, "the answer is still held after Show all");
  await outIs(1, (await ref("diff(sin(a*x), x)", 6)).rendered.latex, "the answer after every step");
  console.log("✓ step through: no steps, then one, then all with the answer");
  // an exercise: written in its editor, answered wrong, right, and with the work itself
  const question = "diff(x^2 * sin(x), x)";
  await menu("Edit", "Add exercise");
  const exI = await all().count() - 1;
  const ex = all().nth(exI);
  await ex.locator(".xc-edit textarea").first().fill("Differentiate $x^2 \\sin x$.");
  await ex.locator(".xc-qin").fill(question);
  await ex.locator(".xc-edit textarea").nth(1).fill("A product.\n\nThe product rule.");
  await ex.locator(".xc-qin").press("Enter");
  await ex.locator(".xc-q .katex").waitFor({ timeout: 30000 });
  const answer = async (a) => {
    await ex.locator(".xc-in").fill(a); await ex.locator(".xc-in").press("Enter");
    await page.waitForFunction(([k, a]) => {
      const c = document.querySelectorAll(".cell")[k];
      return !c.classList.contains("running") && c.querySelector(".xc-verdict:not(.old)") && c.querySelector(".xc-in")?.value === a;
    }, [exI, a], { timeout: 30000 });
    const engine = await reference.call("engine.check", { sessionId: "e2e-features", cellId: "q", source: question, answer: a });
    return { shown: await ex.locator(".xc-verdict").getAttribute("class"), text: await ex.locator(".xc-verdict").textContent(), engine };
  };
  let v = await answer("2x sin(x)");
  assert.equal(v.engine.equivalent, false, "the engine accepted a wrong answer");
  assert.match(v.shown, /wrong/, "the page did not mark the wrong answer");
  v = await answer("x(2 sin(x) + x cos(x))");
  assert.equal(v.engine.equivalent, true, "the engine refused a factored right answer");
  assert.match(v.shown, /right/, `the page did not mark the right answer: ${v.text}`);
  v = await answer(question);
  assert.match(v.shown, /wrong/, "the question itself was accepted as its answer");
  assert.ok(v.text.toLowerCase().includes(v.engine.answer.error.message.toLowerCase()), `the page shows ${JSON.stringify(v.text)}, not the engine's refusal`);
  await ex.locator(".xc-btn", { hasText: "Hint" }).click();
  assert.equal(await ex.locator(".xc-hint").count(), 1, "one hint opened");
  await ex.locator(".xc-btn", { hasText: "Show the solution" }).click();
  await ex.locator(".stepnext [data-next]").waitFor({ timeout: 30000 });
  await ex.locator(".stepnext .stepbtn", { hasText: "Show all" }).click();
  const solution = await reference.call("engine.check", { sessionId: "e2e-features", cellId: "q", source: question, paths: true });
  await outIs(exI, solution.rendered.latex, "the exercise's solution");
  console.log("✓ exercise: wrong, right in another form, the question refused, a hint, the solution stepped through");
  // a Markdown callout
  await menu("Edit", "Add Markdown cell");
  const md = all().nth(await all().count() - 1);
  await md.locator("textarea.mdin").fill("> [!theorem] Product rule\n> $(fg)' = f'g + fg'$");
  await md.locator("textarea.mdin").press("Shift+Enter");
  await md.locator("aside.callout.theorem .calltitle", { hasText: "Product rule" }).waitFor({ timeout: 10000 });
  console.log("✓ callout: a theorem with its title");
  // usage on hover: the name of a command in a cell, after a pause
  const last = await all().count() - 1;
  await all().nth(last).locator("input.cellin").fill("subst(x^2, x, 3)");
  await all().nth(last).locator("input.cellin").press("Enter");
  await outIs(last, (await ref("subst(x^2, x, 3)", 7)).rendered.latex, "subst");
  const name = all().nth(last).locator('.hl .hcmd, .mi [data-hl="hcmd"]').filter({ hasText: "subst" }).first();
  const box = await name.boundingBox();
  await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
  await page.locator(".usagetip .umore", { hasText: "subst" }).waitFor({ timeout: 5000 });
  await page.mouse.move(5, 5);
  console.log("✓ usage on hover: subst");
  // explain: each clickable part of an answer explains that part, the engine's own explain of its path
  // (a negated product prints without its -1, and its factors keep their true paths)
  const negSrc = "cos(t) - sin(t)^2/sqrt(2)";
  const nI = await all().count() - 1;
  await all().nth(nI).locator("input.cellin").fill(negSrc);
  await all().nth(nI).locator("input.cellin").press("Enter");
  await outIs(nI, (await ref(negSrc, 8)).rendered.latex, "the negated product");
  const spans = all().nth(nI).locator(".outval .katex-html [data-path]");
  const paths = await spans.evaluateAll((els) => els.map((e) => e.getAttribute("data-path")));
  assert.ok(paths.includes("0.2.1"), `no clickable exponent among ${JSON.stringify(paths)}`);
  for (const p of paths) {
    const path = p === "root" ? [] : p.split(".").map(Number);
    const want = await reference.call("engine.explain", { sessionId: "e2e-features", cellId: "f8", path });
    await spans.and(page.locator(`[data-path="${p}"]`)).first().dispatchEvent("click");
    // the notebook marks the part it explains once the engine has answered for it
    await all().nth(nI).locator(`.outval [data-path="${p}"].sel`).waitFor({ timeout: 10000 })
      .catch(async () => assert.fail(`explain ${p}: not selected; ${await page.locator(".toast.err").allTextContents()}`));
    const shown = await page.locator(".panel .explain .sel .katex-mathml annotation").first().textContent();
    assert.equal(flat(shown ?? ""), flat(want.rendered.latex), `explain ${p}: the panel shows another subterm`);
  }
  assert.equal(await page.locator(".toast.err").count(), 0, "an explain failed");
  console.log(`✓ explain: ${paths.length} parts of ${negSrc}, each its own subterm`);
  // a truth table, and a relation's graph with the pairs that break a property marked
  const runLast = async (src) => {
    const k = await all().count() - 1;
    await all().nth(k).locator("input.cellin").fill(src); await all().nth(k).locator("input.cellin").press("Enter");
    await page.waitForFunction((k) => {
      const c = document.querySelectorAll(".cell")[k];
      return c && !c.classList.contains("running") && (c.querySelector(".outval") || c.querySelector(".cellerr"));
    }, k, { timeout: 30000 });
    return all().nth(k);
  };
  const tt = await runLast("truthtable(p → q)");
  const ttWant = (await ref("truthtable(p → q)", 8)).visuals.find((v) => v.kind === "logic.truthtable").data;
  assert.equal(await tt.locator("table.truthtable tbody tr").count(), ttWant.rows.length, "one row per assignment");
  assert.equal(await tt.locator("table.truthtable tbody tr.ttfalse").count(), ttWant.rows.filter((r) => !r.at(-1)).length, "the false rows are marked");
  assert.deepEqual(await tt.locator("table.truthtable tbody tr").evaluateAll((trs) => trs.map((tr) => [...tr.children].map((td) => td.textContent === "T"))), ttWant.rows, "the table is the engine's");
  await runLast("let S = rel({a, b, c}; a->b, b->c)");
  await ref("let S = rel({a, b, c}; a->b, b->c)", 9);
  const tr = await runLast("transitive(S)");
  const trWant = (await ref("transitive(S)", 10)).visuals.find((v) => v.kind === "relation.digraph").data;
  assert.equal(await tr.locator("svg path.redge").count(), trWant.edges.length, "an arrow per pair");
  assert.equal(await tr.locator("svg path.redge.bad").count(), trWant.bad.length, "the pairs that break transitivity are marked");
  const cl = await runLast("closure(S, transitive)");
  const clWant = (await ref("closure(S, transitive)", 11)).visuals.find((v) => v.kind === "relation.digraph").data;
  assert.equal(await cl.locator("svg path.redge.added").count(), clWant.added.length, "the closure's pairs are dashed");
  console.log(`✓ visuals: a truth table of ${ttWant.rows.length} rows, a relation with ${trWant.bad.length} marked and ${clWant.added.length} added`);
  // an operation's table, with the cells a failing law read marked
  await runLast("let G = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])");
  await ref("let G = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])", 12);
  const cm = await runLast("commutative(G)");
  const cmWant = (await ref("commutative(G)", 13)).visuals.find((v) => v.kind === "algebra.optable").data;
  assert.deepEqual(await cm.locator("table.optable tbody tr").evaluateAll((trs) => trs.map((tr) => [...tr.querySelectorAll("td")].map((td) => td.textContent))), cmWant.rows, "the table is the engine's");
  assert.equal(await cm.locator("table.optable td.opmark").count(), cmWant.marks.length, "the cells that differ are marked");
  console.log(`✓ operation table: ${cmWant.rows.length}×${cmWant.rows.length}, ${cmWant.marks.length} cells marked where commutativity fails`);
  // a typing derivation drawn as a proof tree: a judgment per node, its rule beside the bar
  const ty = await runLast("type: λf:A→B. λx:A. f x");
  const tyWant = (await ref("type: λf:A→B. λx:A. f x", 14)).visuals.find((v) => v.kind === "typing.tree").data;
  // in the page a judgment follows its premises, as they sit above it
  const nodesOf = (n) => [...n.premises.flatMap(nodesOf), n];
  assert.deepEqual(await ty.locator(".typingtree .ptrule").allTextContents(), nodesOf(tyWant.root).map((n) => n.rule), "a rule per judgment, as the engine derived it");
  assert.deepEqual(await ty.locator(".typingtree .ptconc").evaluateAll((els) => els.map((e) => e.title)), nodesOf(tyWant.root).map((n) => n.text), "the judgments are the engine's");
  console.log(`✓ typing tree: ${nodesOf(tyWant.root).length} judgments, rules ${nodesOf(tyWant.root).map((n) => n.rule).join(" ")}`);
  // a logic exercise: an equivalent answer not in CNF is refused, one in CNF is right
  const lq = "cnf(p → (q ∧ r))";
  await menu("Edit", "Add exercise");
  const lxI = await all().count() - 1;
  const lx = all().nth(lxI);
  await lx.locator(".xc-qin").fill(lq);
  await lx.locator(".xc-qin").press("Enter");
  await lx.locator(".xc-q .katex").waitFor({ timeout: 30000 });
  const lanswer = async (a) => {
    await lx.locator(".xc-in").fill(a); await lx.locator(".xc-in").press("Enter");
    await page.waitForFunction(([k, a]) => {
      const c = document.querySelectorAll(".cell")[k];
      return !c.classList.contains("running") && c.querySelector(".xc-verdict:not(.old)") && c.querySelector(".xc-in")?.value === a;
    }, [lxI, a], { timeout: 30000 });
    const engine = await reference.call("engine.check", { sessionId: "e2e-features", cellId: "lq", source: lq, answer: a });
    return { shown: await lx.locator(".xc-verdict").getAttribute("class"), text: await lx.locator(".xc-verdict").textContent(), engine };
  };
  let lv = await lanswer("¬p ∨ (q ∧ r)");
  assert.equal(lv.engine.equivalent, false, "the engine accepted an answer not in CNF");
  assert.ok(lv.text.toLowerCase().includes(lv.engine.answer.error.message.toLowerCase()), `the page shows ${JSON.stringify(lv.text)}, not the engine's refusal`);
  lv = await lanswer("(!p || r) && (!p || q)");
  assert.equal(lv.engine.equivalent, true, "the engine refused a CNF in another order");
  assert.match(lv.shown, /right/, `the page did not mark the right answer: ${lv.text}`);
  assert.match(lv.text, /truth table/, "the verdict does not say how it was decided");
  console.log("✓ logic exercise: not CNF refused, a CNF in another order accepted by truth table");
  // a cell of several lines: Shift+Enter starts a new line, Enter runs it; the counterexample's steps are marked on the graph
  const lines = ["let M = system(", "var p in {idle, crit}", "var lock in bool", "init p = idle ∧ lock = false", "action enter when p = idle do p := crit", "action leave when p = crit do p := idle, lock := false", ")"];
  await menu("Edit", "Add math cell");
  const mk = await all().count() - 1;
  const mcell = all().nth(mk);
  await mcell.locator(".cellin").click();
  for (const [k, l] of lines.entries()) {
    await page.keyboard.type(l);
    if (k < lines.length - 1) await page.keyboard.press("Shift+Enter");
  }
  assert.equal(await mcell.locator("textarea.cellin").inputValue(), lines.join("\n"), "Shift+Enter made a cell of several lines");
  await page.keyboard.press("Enter");
  await page.waitForFunction((k) => { const c = document.querySelectorAll(".cell")[k]; return c && !c.classList.contains("running") && (c.querySelector(".outval") || c.querySelector(".cellerr")); }, mk, { timeout: 30000 });
  const mWant = await ref(lines.join("\n"), 14);
  assert.equal(mWant.ok, true, `the system: ${mWant.error?.message}`);
  assert.equal(await mcell.locator(".cellerr").count(), 0, "the system cell shows an error");
  const inv = await runLast("invariant(M, p = crit → lock = true)");
  const invWant = (await ref("invariant(M, p = crit → lock = true)", 15)).visuals.find((v) => v.kind === "relation.digraph").data;
  assert.equal(await inv.locator("svg path.redge.bad").count(), invWant.bad.length, "the counterexample's transitions are marked");
  console.log(`✓ several lines: a system typed with Shift+Enter, ${invWant.nodes.length} states, a ${invWant.bad.length}-step counterexample marked`);
  // a step of the trace selected in the work: its transition is the current one on the graph
  if (await inv.locator(".work .step").count() === 0) await inv.locator(".cellacts [aria-expanded]").click();
  await inv.locator(".work:not(.pending) .step").first().waitFor({ timeout: 30000 });
  const stepK = invWant.steps.findIndex((m) => m?.edge);
  assert.ok(stepK >= 0, "the engine placed no step of the trace on the graph");
  await inv.locator(".work .step:not(.sub)").nth(stepK).click();
  await inv.locator("svg path.redge.cur").first().waitFor({ timeout: 10000 })
    .catch(() => assert.fail(`selecting step ${stepK + 1} marked no transition on the graph`));
  assert.equal(await inv.locator("svg path.redge.cur").first().getAttribute("data-edge"), JSON.stringify(invWant.steps[stepK].edge), "the marked transition is the step's");
  console.log(`✓ trace on the graph: step ${stepK + 1} selected, its transition ${invWant.steps[stepK].edge.join(" → ")} marked`);
  // a replica run drawn as a space-time diagram: a lane per replica, an arrow per message
  const repSrc = "replicas(gcounter; a, b, c; a: inc; m := a; b: inc; c <- m; a -> b; b -> c; c <- m)";
  const rep = await runLast(repSrc);
  const repWant = (await ref(repSrc, 16)).visuals.find((v) => v.kind === "replicas.spacetime").data;
  assert.equal(await rep.locator("svg.spacetime .stline").count(), repWant.lanes.length, "a lane per replica");
  assert.equal(await rep.locator("svg.spacetime [data-event]").count(), repWant.events.length, "a dot per event");
  assert.equal(await rep.locator("svg.spacetime .stmsg").count(), repWant.messages.length, "an arrow per message, a duplicate delivery too");
  console.log(`✓ replicas: ${repWant.lanes.length} lanes, ${repWant.events.length} events, ${repWant.messages.length} messages drawn`);
  await manipulate();
  // a course: the Courses tab, a lesson opened, answered, and followed to the next
  const manifest = JSON.parse(readFileSync(path.join(root, "notebooks/courses.json"), "utf8"));
  const course = manifest.projects.find((p) => p.kind === "course");
  await menu("File", "Courses and examples");
  await page.locator(".crscard").first().waitFor({ timeout: 10000 });
  assert.equal(await page.locator(".crscard").count(), manifest.projects.length, "one card per project");
  await page.locator(".crscard", { has: page.locator(".crstitle", { hasText: course.title }) }).click();
  assert.equal(await page.locator(".crslesson").count(), course.lessons.length, "one row per lesson");
  await page.locator(".crslesson").first().locator(".crsgo").click();
  await page.locator(".lessonbar .lbwhere", { hasText: `Lesson 1 of ${course.lessons.length}` }).waitFor({ timeout: 30000 });
  const lesson = JSON.parse(readFileSync(path.join(root, "notebooks", course.path, course.lessons[0].file), "utf8"));
  assert.equal(await page.locator(".sidebar .olrow.section").count(), lesson.cells.filter((c) => c.type === "section").length, "the outline lists the lesson's sections");
  const first = lesson.cells.find((c) => c.type === "exercise");
  const lex = page.locator(".cell.exercise").first();
  await lex.locator(".xc-q .katex").waitFor({ timeout: 60000 });
  const expected = await reference.call("engine.check", { sessionId: "e2e-lesson", cellId: "l", source: first.src });
  await lex.locator(".xc-in").fill(expected.rendered.text); await lex.locator(".xc-in").press("Enter");
  await lex.locator(".xc-verdict.right").waitFor({ timeout: 30000 });
  const total = lesson.cells.filter((c) => c.type === "exercise").length;
  await page.locator(".lessonbar .lbstate", { hasText: `1 of ${total} exercises` }).waitFor({ timeout: 10000 });
  await page.locator(".lessonbar .lbbtn", { hasText: "Next" }).click();
  await page.locator(".lessonbar .lbwhere", { hasText: `Lesson 2 of ${course.lessons.length}` }).waitFor({ timeout: 30000 });
  await page.locator(".lessonbar .lbcourse").click();
  await page.locator(".crslesson").first().locator(".crsstate", { hasText: `1 of ${total} exercises` }).waitFor({ timeout: 10000 });
  console.log(`✓ course: ${course.title}, lesson 1 answered (1 of ${total}), lesson 2 opened, progress remembered`);
}

let failed = false;
try {
  // the notebook, on the engine over HTTP (?dev shows the switch)
  await page.goto(`${base}/?dev`);
  await page.locator(".kernel select").selectOption("http");
  await page.locator("#kurl").fill(engineUrl);
  await page.locator("#kurl").dispatchEvent("change");
  await page.waitForFunction(() => /ready/.test(document.querySelector(".kernel")?.textContent ?? ""), null, { timeout: 30000 });
  connected = true;
  await page.locator(".menus span", { hasText: "File" }).click();
  await page.locator(".dropdown .item", { hasText: "New notebook" }).click();

  for (const [i, c] of CASES.entries()) {
    const want = await reference.call("engine.evaluate", { sessionId: "e2e-reference", cellId: `r${i}`, source: c.src, paths: true });
    await run(i, c.src);
    const got = await out(i);
    if (c.error) {
      assert.equal(want.ok, false, `${c.src}: the engine answered instead of failing`);
      assert.match(want.error.message, new RegExp(c.error), `${c.src}: the engine's error`);
      assert.ok(got.err?.includes(want.error.message), `${c.src}: the page shows ${JSON.stringify(got)}, not the error ${want.error.message}`);
      console.log(`✓ ${c.src}  ✗ ${want.error.message}`);
      continue;
    }
    assert.equal(want.ok, true, `${c.src}: ${want.error?.message}`);
    assert.equal(want.rendered.text, c.text, `${c.src}: the engine's answer`);
    assert.equal(got.err, null, `${c.src}: the page shows an error`);
    assert.equal(flat(got.tex ?? ""), flat(want.rendered.latex), `${c.src}: the page shows something other than the engine's answer`);
    if (c.step) {
      const steps = await work(i);
      assert.ok(steps.some((s) => s.includes(c.step)), `${c.src}: no "${c.step}" step in ${JSON.stringify(steps)}`);
    }
    console.log(`✓ ${c.src}  = ${c.text}${c.step ? `   (${c.step})` : ""}`);
  }
  console.log(`\n${CASES.length} cells, end to end\n`);
  await features();
  assert.deepEqual(pageErrors, [], "errors on the page");
  console.log("\nthe notebook's teaching features, end to end");
} catch (e) {
  failed = true;
  console.error(e);
} finally {
  if (shot) await page.screenshot({ path: shot, fullPage: true });
  reference.close?.();
  await browser.close();
  engine.close();
  site.close();
}
process.exit(failed ? 1 : 0);
