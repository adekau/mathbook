#!/usr/bin/env bash
# Lean -> C -> wasm. Requires: emcc on PATH (emsdk), python3 with zstandard, curl.
# Output: apps/notebook/dist/engine-lean.{js,wasm}
#
# The last Lean release that shipped a prebuilt wasm32 runtime is v4.15.0 (checked 2026-09-10:
# v4.16.0+ have no linux_wasm32 asset). Two roads, pick with LEAN_WASM_TOOLCHAIN:
#   (A) prebuilt: pin engine/lean-toolchain to v4.15.0 and let this script download the artifact.
#   (B) build the runtime yourself for a current Lean: see book/SPIKE.md §"Road B".
set -euo pipefail
cd "$(dirname "$0")/../engine"
VER=$(sed -E 's/.*:v//' lean-toolchain)
TC=${LEAN_WASM_TOOLCHAIN:-toolchains/lean-$VER-linux_wasm32}
if [ ! -d "$TC" ]; then
  mkdir -p toolchains
  URL="https://github.com/leanprover/lean4/releases/download/v$VER/lean-$VER-linux_wasm32.tar.zst"
  echo "downloading $URL"
  curl -fL -o "toolchains/wasm32.tar.zst" "$URL" || { echo "no prebuilt wasm32 runtime for v$VER — use Road B (SPIKE.md)"; exit 1; }
  python3 -c "import zstandard,tarfile;
f=open('toolchains/wasm32.tar.zst','rb');t=tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(f),mode='r|');t.extractall('toolchains')"
fi
lake build                                     # produces .lake/build/ir/**/*.c
OUT=../apps/notebook/dist; mkdir -p "$OUT"
# NOTE: no -pthread. Lean's runtime can run single-threaded; -pthread would force COOP/COEP
# headers (SharedArrayBuffer) on the host page. If the link fails with atomics/pthread
# symbols, add -pthread and serve with cross-origin isolation — record that in SPIKE.md.
emcc -O2 -o "$OUT/engine-lean.js" \
  -I "$TC/include" -L "$TC/lib/lean" \
  c/shim.c $(find .lake/build/ir/MathEngine -name '*.c') .lake/build/ir/MathEngine.c \
  -lInit -lleanrt \
  -sMODULARIZE=1 -sEXPORT_NAME=createMathEngine -sENVIRONMENT=worker,node \
  -sEXPORTED_FUNCTIONS=_mathengine_init,_mathengine_call,_mathengine_free,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=ccall,cwrap,UTF8ToString,stringToUTF8,lengthBytesUTF8 \
  -sALLOW_MEMORY_GROWTH=1 -sEXIT_RUNTIME=0 -fwasm-exceptions
ls -la "$OUT"/engine-lean.*
