/// <reference lib="webworker" />
/**
 * Web-worker host for the Lean engine compiled to wasm (scripts/build-wasm.sh).
 * Mirrors worker.ts: same Transport, same protocol, different engine behind it.
 */
import { serve } from "@mathbook/protocol";
import { workerSelfTransport } from "./transports.js";

type Module = {
  ccall(name: string, ret: string, argTypes: string[], args: unknown[]): unknown;
  cwrap(name: string, ret: string | null, argTypes: string[]): (...a: unknown[]) => unknown;
  UTF8ToString(ptr: number): string;
};
declare const createMathEngine: (opts?: object) => Promise<Module>;

importScripts("engine-lean.js");

const ready = createMathEngine().then((M) => {
  if (M.ccall("mathengine_init", "number", [], []) !== 0) throw new Error("Lean runtime failed to initialize");
  const call = M.cwrap("mathengine_call", "number", ["string"]) as (s: string) => number;
  const free = M.cwrap("mathengine_free", null, ["number"]) as (p: number) => void;
  return (req: string): string => { const p = call(req); const out = M.UTF8ToString(p); free(p); return out; };
});

serve(workerSelfTransport(self as unknown as DedicatedWorkerGlobalScope), {
  async handle(method, params) {
    const call = await ready;
    const res = JSON.parse(call(JSON.stringify({ jsonrpc: "2.0", id: 1, method, params })));
    if (res.error) throw new Error(res.error.message);
    return res.result;
  },
});
