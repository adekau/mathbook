# Milestone 0 — the wasm spike

**Question:** can one Lean engine serve every host (web worker, self-hosted server, CLI) by
compilation target alone? **Status: everything except the final `emcc` link is verified in
this repo. The link is the only step that needs your machine (emsdk).**

## What is already proven (run `npm test` and `lake build`)

| Step | Evidence |
|---|---|
| Lean engine speaks the protocol | `engine/Main.lean` + `packages/engine-host/test/lean-native.test.mjs`: TS client → stdio → native Lean exe, capabilities + evaluate round-trip |
| The C ABI the worker will call | `engine/c/shim.c` + `engine/c/test.c`: `mathengine_init` / `mathengine_call` / `mathengine_free`, 2 000 calls, refcounts balanced (the native build is `leanc ... c/shim.c c/test.c .lake/build/ir/MathEngine/*.c -lInit -lleanrt`) |
| No `libLean.a` dependency | `MathEngine/Json.lean` is hand-rolled; the engine links against `Init` + `leanrt` only (118 MB of `libLean.a` stays out of the wasm) |
| First verified rule | `MathEngine/Simp.lean`: `simpTop_sound : SemEq (simpTop e) e`, machine-checked |

## What you run locally (Road A, ~1 hour)

1. Install emsdk (`git clone https://github.com/emscripten-core/emsdk && ./emsdk install latest && ./emsdk activate latest && source emsdk_env.sh`).
2. **Pin `engine/lean-toolchain` to `leanprover/lean4:v4.15.0`.** That is the last release with a prebuilt `linux_wasm32` runtime (v4.16.0 through v4.30.0 have none — I checked the release asset lists on 2026-09-10). The engine code uses only `Init`, so it should build on 4.15 unchanged; if a tactic differs, that's the first thing to note.
3. `npm run wasm` — downloads the 200 MB runtime artifact, `lake build`, `emcc` link.
4. `npm run bundle && npx serve apps/notebook/dist`, pick "in-browser (Lean/wasm)" in the engine dropdown (add the `<option value="lean-worker">` in `index.html` pointing at `engine-lean.worker.js` — two lines in `app.ts`), evaluate `x + 0`.

### Record these numbers
- `engine-lean.wasm` size (expect single-digit MB; if it's 30+ MB something from `Lean` got linked).
- Time from `new Worker` to first `engine.capabilities` reply.
- Whether the link needed `-pthread`. If it did, the host page must send `Cross-Origin-Opener-Policy: same-origin` and `Cross-Origin-Embedder-Policy: require-corp`. That's a real deployment constraint for "self-hostable", so it goes in ARCHITECTURE.md either way.

### Known traps (from lean2wasm and the Lean wasm Zulip threads)
- `-sMODULARIZE` is required to instantiate the module more than once per page.
- Lean ≥ 4.16 runtimes reference libuv symbols (`uv_strerror`, `uv_fs_mkstemp`, …) that don't exist under Emscripten; upstream fix is PR #13298 (open, Apr 2026). Irrelevant on Road A (4.15), relevant on Road B.
- No filesystem, no `IO.Process`, no threads in the wasm engine. The engine must stay a pure `String → String` function, which it is by design.

## Road B — current Lean, build the runtime yourself (only if Road A works and you want Lean ≥ 4.16)
`git clone --recurse-submodules leanprover/lean4 && cd lean4 && git checkout v4.XX.0 && mkdir -p build/wasm && cd build/wasm && emcmake cmake ../.. -DUSE_GMP=OFF && emmake make -j8 leanrt Init` — expect to carry the #13298 patch and possibly a `unique_lock` guard. Budget a weekend. Decision rule: if Road A's wasm is < 10 MB and initializes in < 1 s, stay on 4.15 for the whole project and revisit Road B only when a Mathlib feature you need requires a newer toolchain.

## Decision after the spike
- **Works, numbers acceptable** → delete `packages/reference-ts` once the Lean engine reaches parity on its tests (port `engine.test.mjs` cases to `lake test` + a wire-level differential test in the meantime). Single engine, three hosts.
- **Fails on the link** → the fallback is still cheap: keep the TS engine in the worker and the Lean engine as the verified server-side reference. Nothing else in the architecture changes, because everything already talks through `@mathbook/protocol`.
