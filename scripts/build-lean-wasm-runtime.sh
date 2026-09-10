#!/usr/bin/env bash
# Build the Lean runtime + Init for wasm32 from source ("Road B" in book/SPIKE.md).
#
# Lean stopped shipping a prebuilt linux_wasm32 runtime after v4.15.0, so for a current toolchain
# we build the two static libraries a Lean program needs ourselves:
#   libleanrt.a  src/runtime/*.cpp from the leanprover/lean4 tag matching engine/lean-toolchain,
#                compiled with em++ using the flags src/CMakeLists.txt uses for Emscripten
#                (USE_GMP=OFF, USE_MIMALLOC=OFF, MMAP=OFF, MULTI_THREAD=OFF; no -pthread, no LTO)
#   libInit.a    C emitted for every Init module by the *same* host `lean` that built the toolchain's
#                .oleans (`lean --c`), compiled with emcc. The engine only imports Init.
# The Lean compiler itself is never built; the host toolchain from elan does all elaboration.
#
# Requires: elan toolchain from engine/lean-toolchain, emcc/em++/emar (emsdk), git, curl.
# Output:   engine/toolchains/lean-<ver>-wasm32/{include,lib/libleanrt.a,lib/libInit.a}
# Patch:    engine/wasm/lean-runtime-emscripten.patch (the two stub signatures from lean4#14973)
set -euo pipefail
cd "$(dirname "$0")/../engine"
VER=$(sed -E 's/.*:v//' lean-toolchain)
TAG="v$VER"
LEAN=$(elan which lean)   # elan resolves the pin in engine/lean-toolchain
PREFIX=$("$LEAN" --print-prefix)
GITHASH=$("$LEAN" -g)
TC=$PWD/toolchains/lean-$VER-wasm32
SRC=$PWD/toolchains/src/lean4-$TAG
UV=$PWD/toolchains/src/libuv
JOBS=${JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)}
mkdir -p toolchains/src "$TC/include/lean" "$TC/lib" "$TC/obj/runtime/uv" "$TC/obj/Init" "$TC/c"

# 1. Sources: lean4 at the pinned tag (runtime only is used) + libuv headers (io.cpp includes uv.h).
if [ ! -d "$SRC" ]; then
  git clone --depth 1 --branch "$TAG" https://github.com/leanprover/lean4 "$SRC"
  (cd "$SRC" && git apply "$OLDPWD/wasm/lean-runtime-emscripten.patch")
fi
if [ ! -d "$UV" ]; then
  git clone --depth 1 --branch v1.48.0 https://github.com/libuv/libuv "$UV"   # version pinned by lean4's own CMake
fi

# 2. Generated headers (what CMake's configure_file would produce), mimalloc off.
cp "$SRC/src/include/lean/"*.h "$TC/include/lean/"
cat > "$TC/include/lean/version.h" <<H
#pragma once
#define LEAN_VERSION_MAJOR $(cut -d. -f1 <<<"$VER")
#define LEAN_VERSION_MINOR $(cut -d. -f2 <<<"$VER")
#define LEAN_VERSION_PATCH $(cut -d. -f3 <<<"$VER")
#define LEAN_VERSION_IS_RELEASE 1
#define LEAN_SPECIAL_VERSION_DESC ""
#define LEAN_VERSION_STRING "$VER"
#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"
#define LEAN_MANUAL_ROOT "https://lean-lang.org/doc/reference/$TAG/"
H
cat > "$TC/include/lean/config.h" <<H
#pragma once
#include <lean/version.h>
/* no LEAN_MIMALLOC: the wasm build uses the libc allocator (USE_MIMALLOC=OFF) */
#define LEAN_IS_STAGE0 0
H
echo "#define LEAN_GITHASH \"$GITHASH\"" > "$TC/include/githash.h"

# 3. libleanrt.a
if [ ! -f "$TC/lib/libleanrt.a" ]; then
  echo "== compiling runtime ($SRC/src/runtime)"
  CXXFLAGS="-std=c++20 -Wall -Wextra -O3 -DNDEBUG -DLEAN_EXPORTING -D__CLANG__ -DLEAN_BUILD_TYPE=\"Release\" -ffp-contract=off -DLEAN_EMSCRIPTEN -fwasm-exceptions -I$TC/include -I$SRC/src -I$SRC/src/include -I$UV/include"
  RT="debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl"
  export CXXFLAGS SRC TC
  echo "$RT" | tr ' ' '\n' | xargs -P "$JOBS" -I{} bash -c 'em++ $CXXFLAGS -c "$SRC/src/runtime/{}.cpp" -o "$TC/obj/runtime/{}.o"'
  emar rcs "$TC/lib/libleanrt.a" $(for s in $RT; do echo "$TC/obj/runtime/$s.o"; done)
fi

# 4. libInit.a: emit C with the host lean, compile with emcc.
if [ ! -f "$TC/lib/libInit.a" ]; then
  echo "== emitting C for Init with $LEAN"
  export LEAN LEAN_PATH="$PREFIX/lib/lean" TC
  (cd "$PREFIX/src/lean" && { echo Init.lean; find Init -name '*.lean'; } | xargs -P "$JOBS" -I{} bash -c 'f={}; o="$TC/c/${f%.lean}.c"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || "$LEAN" -R . --c="$o" "$f"')
  echo "== compiling $(find "$TC/c" -name '*.c' | wc -l | tr -d ' ') Init modules"
  CFLAGS="-O3 -DNDEBUG -DLEAN_EXPORTING -ffp-contract=off -fwasm-exceptions -I$TC/include"
  export CFLAGS
  (cd "$TC/c" && find . -name '*.c' | xargs -P "$JOBS" -I{} bash -c 'c={}; o="$TC/obj/Init/${c%.c}.o"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || emcc $CFLAGS -c "$c" -o "$o"')
  find "$TC/obj/Init" -name '*.o' > "$TC/obj/init-objs.txt"
  emar rcs "$TC/lib/libInit.a" $(cat "$TC/obj/init-objs.txt")
fi
ls -la "$TC/lib"
