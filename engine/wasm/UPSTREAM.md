# Upstream notes for leanprover/lean4 (not yet reported)

Findings from building the Lean runtime for wasm32 on v4.33.1 (see `book/SPIKE-RESULTS.md`). Each item is
patched locally in `lean-runtime-emscripten.patch` or worked around in `../c/uv-stubs.c`. Nothing here
has been filed; review the project's contribution guidelines (`CONTRIBUTING.md`, RFC/issue templates,
`stage0` update rules) before opening anything.

## 1. Draft issue: `String.toList` builds `[]` with `lean_box_uint32(0)` (breaks 32-bit / wasm32)

**Title:** `string_to_list_core` builds the empty list with `lean_box_uint32(0)`, which is a heap object on 32-bit

**Description**

`src/runtime/object.cpp`, `string_to_list_core`:

```cpp
obj_res  r = lean_box_uint32(0);   // intended: the `List.nil` scalar
```

On 64-bit `lean_box_uint32(v)` is `lean_box(v)`, so this is the scalar `nil` and everything works.
On 32-bit (`sizeof(void*) == 4`, e.g. Emscripten wasm32) `lean_box_uint32` allocates a constructor
object (`lean_alloc_ctor(0, 0, 4)`). The resulting "nil" has tag 0, so compiled pattern matching
(`lean_obj_tag`) still treats it as `[]`, but runtime code that tests `lean_is_scalar` does not.
`lean_string_mk` is one such caller: it walks the list until `lean_is_scalar(o)`, reads the fake
cell's fields as `head`/`tail`, and never terminates (the `std::string` grows until `bad_alloc`).

Every `String.toList` result carries this bogus terminator, so any 32-bit program that passes a
`toList` result (or a suffix of it) back to `String.ofList` / `String.mk` hangs. Because
`List.takeWhile` returns its input unchanged when every element matches, this shows up in ordinary
lexer code: `String.ofList ((s.toList).takeWhile Char.isDigit)` hangs when the digits run to the
end of the string, but works when they don't (a fresh list from `Array.toList` is used then).

**Reproduction** (wasm32; a native 32-bit build should behave the same)

```lean
def main : IO Unit := do
  let s := "x"
  IO.println (String.ofList s.toList)   -- hangs, then std::bad_alloc
```

Observed with the v4.15.0 `linux_wasm32` release runtime and with v4.33.1 built from source with
Emscripten 5.0.6 (`USE_GMP=OFF USE_MIMALLOC=OFF MMAP=OFF MULTI_THREAD=OFF`). Heap dump from an
instrumented `lean_string_mk` on `"0".toList`:

```
cell 0 @0x5704c rc=1 tag=1 other=2 head=0x57064 tail=0x57424    -- cons '0'
cell 1 @0x57424 rc=3 tag=0 other=0 head=0 tail=0x18            -- "nil": a 0-field ctor object, not lean_box(0)
```

**Fix**

```cpp
obj_res  r = lean_box(0);
```

Same pattern worth checking elsewhere: any `lean_box_uint32(0)` / `box_uint32(0)` used as a
constructor-0 scalar. `grep -rn "box_uint32(0)" src/runtime` found only this site on v4.33.1.

**Versions:** Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6), Emscripten 5.0.6, macOS 14.6 host.

## 2. Related, already tracked upstream

- **#6817 / PR #13298** — `io.cpp` references libuv symbols under `LEAN_EMSCRIPTEN`. On v4.33.1 the
  set is larger than the PR covers: `uv_strerror`, `uv_os_tmpdir`, `uv_fs_mkstemp`, `uv_fs_mkdtemp`,
  `uv_fs_stat`, `uv_fs_lstat`, `uv_fs_link`, `uv_fs_unlink`, `uv_fs_req_cleanup` (metadata, hard
  links and unlink moved to libuv after the PR was written). Worth a comment on the PR if it is
  still open. Our workaround: `../c/uv-stubs.c` defines them with the `uv.h` prototypes and returns
  `UV_ENOSYS`.
- **#14973** (2026-09-08) — `lean_uv_event_loop_alive` and `lean_uv_os_get_group` Emscripten stubs
  don't match their declarations. Confirmed; the two-line fix is in our patch.

## 3. Possible follow-up: arity mismatch on `lean_io_create_tempfile` / `lean_io_create_tempdir`

After the zero-cost `BaseIO` change (#10625), `Init/System/IO.c` declares and calls
`lean_io_create_tempfile()` / `lean_io_create_tempdir()` with no arguments, while `io.cpp` defines
them as taking a `lean_object * w`. Native linkers don't check signatures; `wasm-ld` warns:

```
wasm-ld: warning: function signature mismatch: lean_io_create_tempfile
>>> defined as () -> i32 in libInit.a(IO.o)
>>> defined as (i32) -> i32 in libleanrt.a(io.o)
```

and inserts a trapping thunk, so calling `IO.FS.createTempFile` on wasm would trap. Not exercised
by us. Likely fix: drop the unused parameter in `io.cpp` (check other `IO` externs for the same drift).

## 4. Build notes that may help a future "wasm32 CI" discussion

- The runtime (34 files) compiles cleanly with `em++ -std=c++20 -DLEAN_EMSCRIPTEN` after the
  #14973 fix, without `-pthread`, with `MULTI_THREAD=OFF`.
- `Init` C emitted by the host `lean --c` matches the checked-in `stage0/stdlib/Init/*.c` for
  629 of 631 files at v4.33.1.
- `-sSAFE_HEAP=1` reports an unaligned 64-bit load in `Init.Data.ByteArray.Extra`'s initializer
  (`lean_ctor_get_uint64` at a 4-byte-aligned scalar offset); tolerated by wasm, but a
  `LEAN_CASSERT`-style alignment story for 32-bit scalar areas may be worth raising.
