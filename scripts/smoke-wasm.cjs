// Smoke test + timing for the wasm engine:  node scripts/smoke-wasm.cjs apps/notebook/dist
// Loads engine-lean.js from a CommonJS-scoped temp dir (apps/notebook is "type": "module", so
// requiring the emcc output in place would treat it as ESM and drop its module.exports).
const fs = require("node:fs"), os = require("node:os"), path = require("node:path");
const src = path.resolve(process.argv[2] || "apps/notebook/dist");
const dir = fs.mkdtempSync(path.join(os.tmpdir(), "mathbook-wasm-"));
for (const f of ["engine-lean.js", "engine-lean.wasm"]) fs.copyFileSync(path.join(src, f), path.join(dir, f));
const t0 = performance.now();
const createMathEngine = require(path.join(dir, "engine-lean.js"));
createMathEngine().then((M) => {
  const t1 = performance.now();
  if (M.ccall("mathengine_init", "number", [], []) !== 0) throw new Error("mathengine_init failed");
  const t2 = performance.now();
  const call = M.cwrap("mathengine_call", "number", ["string"]);
  const free = M.cwrap("mathengine_free", null, ["number"]);
  const rpc = (method, params) => { const p = call(JSON.stringify({ jsonrpc: "2.0", id: 1, method, params })); const s = M.UTF8ToString(p); free(p); return JSON.parse(s); };
  const caps = rpc("engine.capabilities", {});
  const t3 = performance.now();
  const ev = rpc("engine.evaluate", { sessionId: "s", cellId: "1", source: "x + 0" });
  const t4 = performance.now();
  for (let i = 0; i < 2000; i++) rpc("engine.evaluate", { sessionId: "s", cellId: "1", source: "x + 0" });
  const t5 = performance.now();
  const ok = caps.result?.engine === "engine-lean" && ev.result?.ok === true && ev.result.rendered.text === "x";
  console.log(JSON.stringify({ ok, wasmBytes: fs.statSync(path.join(src, "engine-lean.wasm")).size, moduleLoad_ms: +(t1 - t0).toFixed(1), leanInit_ms: +(t2 - t1).toFixed(1), firstCaps_ms: +(t3 - t2).toFixed(1), totalToCaps_ms: +(t3 - t0).toFixed(1), firstEvaluate_ms: +(t4 - t3).toFixed(2), per_call_us: +((t5 - t4) / 2).toFixed(1), caps: caps.result, evaluate: ev.result?.rendered ?? ev }, null, 1));
  fs.rmSync(dir, { recursive: true, force: true });
  process.exitCode = ok ? 0 : 1;
});
