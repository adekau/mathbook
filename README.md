# mathbook

A Mathematica-like learning notebook (linear algebra → Calc IV) with "show work" mode, plus
the zero-to-hero book written from building it. One math engine in Lean 4, verified, compiled
to native (server / CLI) and wasm (web worker). The TypeScript reference engine it was ported
from was deleted after M2; its answers live on in `engine/Tests/golden.tsv`.

```
packages/protocol       JSON-RPC contract + Transport abstraction (the seam everything hangs on)
packages/engine-host    transports (worker / HTTP / WebSocket / stdio), HTTP host over the native engine, wasm worker glue
engine/                 Lean engine: syntax, semantics, verified rewriter + rules, JSON, RPC, C shim, tests + golden
apps/notebook           minimal shell (real design comes from the Claude Design export)
book/                   SPIKE-RESULTS.md (milestone 0, done), M1-BRIEF.md (current), TRACKING.md
scripts/                bundle.mjs (esbuild), build-wasm.sh (Lean → C → emcc), build-lean-wasm-runtime.sh (leanrt + Init for wasm32, from source)
```

`npm install && npm run build && npm test` — TS. `cd engine && lake build` — Lean (toolchain
pinned in `engine/lean-toolchain`, currently v4.33.1; policy: latest stable). `npm run wasm` —
builds the Lean runtime + Init for wasm32 from source on first run (~10 min, cached under
`engine/toolchains/`), then links `apps/notebook/dist/engine-lean.{js,wasm}`; see `book/SPIKE-RESULTS.md`.
Needs emsdk (`emcc`), elan, git.
