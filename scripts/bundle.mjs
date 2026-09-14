// Bundles the Lean/wasm worker glue and the notebook page into apps/notebook/dist (static, self-hostable).
import { build } from "esbuild";
import { cpSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
// A build stamp on every asset URL, so a browser never keeps yesterday's engine.
const BUILD = Date.now().toString(36);
const define = { __BUILD_ID__: JSON.stringify(BUILD) };
mkdirSync("apps/notebook/dist", { recursive: true });
await build({ entryPoints: ["apps/notebook/src/app.ts"], bundle: true, format: "esm", outfile: "apps/notebook/dist/app.js", target: "es2022", logLevel: "info", define });
cpSync("apps/notebook/assets", "apps/notebook/dist", { recursive: true });   // logo.svg and any other static asset
writeFileSync("apps/notebook/dist/index.html", readFileSync("apps/notebook/index.html", "utf8").replace(/src="app\.js"/, `src="app.js?v=${BUILD}"`));
console.log("→ serve apps/notebook/dist with any static server (e.g. `npx serve apps/notebook/dist`)");
await build({ entryPoints: ["packages/engine-host/src/worker-lean.ts"], bundle: true, format: "iife", outfile: "apps/notebook/dist/engine-lean.worker.js", target: "es2022", logLevel: "info", define });
