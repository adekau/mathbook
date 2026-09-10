# Milestone 0 — the wasm spike

**Question:** can one Lean engine serve every host (web worker, self-hosted server, CLI) by
compilation target alone? **Answer (2026-09-10): yes, on current Lean (v4.33.1), with a
runtime we build ourselves.** `npm run wasm` produces `engine-lean.wasm` (1.4 MB), the
notebook's "in-browser (Lean/wasm)" option evaluates `x + 0` to `x`, and no `-pthread`
(so no COOP/COEP headers) is needed.

## What is proven (run `npm test`, `lake build`, `npm run wasm`)

| Step | Evidence |
|---|---|
| Lean engine speaks the protocol | `engine/Main.lean` + `packages/engine-host/test/lean-native.test.mjs`: TS client → stdio → native Lean exe, capabilities + evaluate round-trip |
| The C ABI the worker calls | `engine/c/shim.c` + `engine/c/test.c`: `mathengine_init` / `mathengine_call` / `mathengine_free`, 2 000 calls, refcounts balanced. Native build: `clang -c -I $(lean --print-prefix)/include c/shim.c c/test.c` then `leanc -o t shim.o test.o .lake/build/ir/MathEngine/*.c .lake/build/ir/MathEngine.c -lInit -lleanrt` (leanc's bundled clang has no libc headers, so plain C goes through the system clang) |
| No `libLean.a` dependency | `MathEngine/Json.lean` is hand-rolled; the engine links against `Init` + `leanrt` only |
| First verified rule | `MathEngine/Simp.lean`: `simpTop_sound : SemEq (simpTop e) e`, machine-checked, unchanged from 4.22 to 4.33 |
| wasm link + run | `scripts/build-wasm.sh` → `apps/notebook/dist/engine-lean.{js,wasm}`; smoke-tested in Node and in the notebook page |

## Numbers (v4.33.1, emcc 5.0.6, -O2, MacBook x86_64)

| | |
|---|---|
| `engine-lean.wasm` | 1 410 652 bytes (1.4 MB); `engine-lean.js` 62 KB. Nothing from `Lean` is linked; `libInit.a` is 15 MB before dead-code elimination |
| Node: module load → `createMathEngine()` resolved | 14 ms |
| Node: `mathengine_init` (runtime + 631 Init module initializers) | 47 ms |
| Node: first `engine.capabilities` reply, from `require` | 64 ms total |
| Browser: `new Worker` → first `engine.capabilities` reply | 96 ms (worker fetch + compile + init; logged by `app.ts` as `[mathbook] lean-worker: …`) |
| `engine.evaluate "x + 0"` | 2.5 ms first call, then ~50 µs per call (2 000-call loop) |
| `-pthread` | not needed. The runtime is built single-threaded (`MULTI_THREAD=OFF`), so the host page needs no `Cross-Origin-Opener-Policy` / `Cross-Origin-Embedder-Policy` headers. "Self-hostable" stays a plain static directory |

Reproduce the Node numbers with `node scripts/smoke-wasm.cjs apps/notebook/dist` (`npm test` covers the
native path). First full `npm run wasm` on this machine: 9 min wall, of which ~5 min is elaborating Init;
the cache under `engine/toolchains/` is 63 MB plus a 774 MB lean4 checkout.

## How the wasm build works (Road B, what `npm run wasm` does)

Lean stopped shipping a prebuilt `linux_wasm32` runtime after v4.15.0, and the project wants
current Lean, so `scripts/build-lean-wasm-runtime.sh` builds the two libraries a Lean program
needs from source, for the toolchain pinned in `engine/lean-toolchain`:

1. **`libleanrt.a`** — `src/runtime/*.cpp` from the `leanprover/lean4` tag, compiled with `em++`
   using the flags `src/CMakeLists.txt` uses for Emscripten (`USE_GMP=OFF`, `USE_MIMALLOC=OFF`,
   `MMAP=OFF`, `MULTI_THREAD=OFF`, `-DLEAN_EMSCRIPTEN`, `-fwasm-exceptions`), minus `-pthread` and
   `-flto`. CMake is not used (the machine's cmake was broken, and the recipe is 34 files).
2. **`libInit.a`** — the C for all 631 `Init` modules, emitted by the *same* host `lean` that built
   the toolchain's `.olean`s (`lean -R . --c=… Init/Foo.lean` over the toolchain's `src/lean`),
   then compiled with `emcc`. The output matches the checked-in `stage0/stdlib/Init/*.c` for
   629 of 631 files, which is a nice cross-check. Elaborating all of Init takes ~5 min on 16 cores.
3. **The engine's own C** comes from `lake build` on the host — Lean's C output is target-independent
   (`sizeof(void*)` is only used symbolically).
4. **Link** — `emcc c/shim.c c/uv-stubs.c .lake/build/ir/**/*.c -lInit -lleanrt -sMODULARIZE …`.

Everything is cached under `engine/toolchains/lean-<ver>-wasm32/` (gitignored); delete it to rebuild.
The Lean compiler itself is never built.

### Upstream bugs hit, all patched in `engine/wasm/lean-runtime-emscripten.patch`

- **`string_to_list_core` builds `[]` with `lean_box_uint32(0)`** (`src/runtime/object.cpp`). On
  64-bit that is the scalar `lean_box(0)`, so nobody notices. On 32-bit `lean_box_uint32`
  allocates a heap object; Lean pattern matching still sees tag 0 (`nil`), but `lean_string_mk`
  tests `lean_is_scalar` and walks off the end of the list, growing a string until `bad_alloc`.
  Symptom: `String.ofList s.toList` hangs whenever the list *is* the original `toList` result
  (`takeWhile` returns its input when everything matches, so `x` failed but `(x)` worked). The
  v4.15.0 prebuilt wasm runtime has the same bug, which is why "Road A" died on its first
  evaluate. Fix: `lean_box(0)`. Not yet reported upstream.
- **libuv symbols referenced under `LEAN_EMSCRIPTEN`** (leanprover/lean4#6817, open PR #13298):
  `io.cpp` calls `uv_fs_stat/lstat/link/unlink/mkstemp/mkdtemp`, `uv_os_tmpdir`, `uv_strerror`,
  `uv_fs_req_cleanup` unconditionally. Instead of patching `io.cpp`, `engine/c/uv-stubs.c` defines
  them with the real prototypes from `uv.h` and returns `UV_ENOSYS`; the engine never reaches them.
- **Two Emscripten stubs don't match their declarations** (leanprover/lean4#14973, filed
  2026-09-08): `lean_uv_event_loop_alive` returns `uint8_t`, `lean_uv_os_get_group` takes a `gid`.
  Two-line patch.
- **Init's `IO.c` and the runtime disagree on the arity of `lean_io_create_tempfile/dir`** (Init
  emits `()` after the zero-cost `BaseIO` change #10625; `io.cpp` still takes a world). Native
  linkers don't care; `wasm-ld` warns and would trap if called. Harmless here, worth an upstream
  note.

### ABI changes between 4.22 (scaffold) and 4.33 that touched the shim
- Module initializers are prefixed with the Lake package and take no world token:
  `initialize_mathengine_MathEngine(uint8_t builtin)` (was `initialize_MathEngine(builtin, world)`).
- `String.Pos` became `s.Pos` (dependent) with `String.Pos.Raw` for byte offsets; `String.mk` →
  `String.ofList`; `trimRight` → `trimAsciiEnd` returning a `Slice`. Three-line port in `Json.lean`.

### Known traps (from lean2wasm and the Lean wasm Zulip threads, confirmed)
- `-sMODULARIZE` is required to instantiate the module more than once per page.
- No filesystem, no `IO.Process`, no threads in the wasm engine. The engine must stay a pure
  `String → String` function, which it is by design.
- `SAFE_HEAP=1` reports an unaligned 64-bit load in `Init.Data.ByteArray.Extra`'s initializer
  (`lean_ctor_get_uint64` on a 4-byte-aligned scalar area). wasm tolerates it; use `SAFE_HEAP=2`.

## Road A (v4.15.0 prebuilt runtime) — tried first, abandoned
It links after stubbing four libuv symbols (`uv_strerror`, `uv_os_tmpdir`, `uv_fs_mkstemp`,
`uv_fs_mkdtemp`), initializes, and then hits the `string_to_list_core` bug above on the first
evaluate. The Lean engine code itself built unchanged on 4.15 (proof included). Not worth
patching a frozen 2025 runtime when Road B costs one script.

## Decision after the spike
**Works, numbers acceptable** → delete `packages/reference-ts` once the Lean engine reaches parity
on its tests (port `engine.test.mjs` cases to `lake test` + a wire-level differential test in the
meantime). Single engine, three hosts. Toolchain policy: track the latest stable Lean release;
`npm run wasm` rebuilds the runtime for whatever `engine/lean-toolchain` says.
