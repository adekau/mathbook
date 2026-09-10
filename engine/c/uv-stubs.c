/*
 * libuv stubs for the wasm build.
 *
 * Lean's runtime (io.cpp) calls libuv for file metadata, hard links, unlink and temp files even
 * when built with LEAN_EMSCRIPTEN (leanprover/lean4#6817, open PR #13298). The engine is a pure
 * String → String function and never reaches these, but wasm-ld needs every referenced symbol
 * defined. Each stub fails with UV_ENOSYS, which the runtime turns into an IO error.
 * Prototypes come from uv.h so they match the runtime's calls exactly.
 * Only compiled into the emscripten link (scripts/build-wasm.sh), never into native builds.
 */
#include <uv.h>

const char* uv_strerror(int err) { (void)err; return "libuv is not available in the wasm engine"; }
int uv_os_tmpdir(char* buffer, size_t* size) { (void)buffer; (void)size; return UV_ENOSYS; }
int uv_fs_mkstemp(uv_loop_t* loop, uv_fs_t* req, const char* tpl, uv_fs_cb cb) { (void)loop; (void)req; (void)tpl; (void)cb; return UV_ENOSYS; }
int uv_fs_mkdtemp(uv_loop_t* loop, uv_fs_t* req, const char* tpl, uv_fs_cb cb) { (void)loop; (void)req; (void)tpl; (void)cb; return UV_ENOSYS; }
int uv_fs_stat(uv_loop_t* loop, uv_fs_t* req, const char* path, uv_fs_cb cb) { (void)loop; (void)req; (void)path; (void)cb; return UV_ENOSYS; }
int uv_fs_lstat(uv_loop_t* loop, uv_fs_t* req, const char* path, uv_fs_cb cb) { (void)loop; (void)req; (void)path; (void)cb; return UV_ENOSYS; }
int uv_fs_link(uv_loop_t* loop, uv_fs_t* req, const char* path, const char* new_path, uv_fs_cb cb) { (void)loop; (void)req; (void)path; (void)new_path; (void)cb; return UV_ENOSYS; }
int uv_fs_unlink(uv_loop_t* loop, uv_fs_t* req, const char* path, uv_fs_cb cb) { (void)loop; (void)req; (void)path; (void)cb; return UV_ENOSYS; }
void uv_fs_req_cleanup(uv_fs_t* req) { (void)req; }
