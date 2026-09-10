import { spawn } from "node:child_process";
import { createClient, type EngineClient } from "@mathbook/protocol";
import { stdioTransport } from "./transports.js";
/** Self-hosted / test path: the native Lean exe over stdio. */
export function leanNativeClient(exe = "engine/.lake/build/bin/mathengine"): EngineClient {
  const proc = spawn(exe, [], { stdio: ["pipe", "pipe", "inherit"] });
  return createClient(stdioTransport(proc));
}
