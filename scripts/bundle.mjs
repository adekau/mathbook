// Bundles the worker engine and the notebook page into apps/notebook/dist (static, self-hostable).
import { build } from "esbuild";
import { cpSync, mkdirSync } from "node:fs";
mkdirSync("apps/notebook/dist", { recursive: true });
await build({ entryPoints: ["packages/engine-host/src/worker.ts"], bundle: true, format: "iife", outfile: "apps/notebook/dist/engine.worker.js", target: "es2022", logLevel: "info" });
await build({ entryPoints: ["apps/notebook/src/app.ts"], bundle: true, format: "esm", outfile: "apps/notebook/dist/app.js", target: "es2022", logLevel: "info" });
cpSync("apps/notebook/index.html", "apps/notebook/dist/index.html");
console.log("→ serve apps/notebook/dist with any static server (e.g. `npx serve apps/notebook/dist`)");
await build({ entryPoints: ["packages/engine-host/src/worker-lean.ts"], bundle: true, format: "iife", outfile: "apps/notebook/dist/engine-lean.worker.js", target: "es2022", logLevel: "info" });
