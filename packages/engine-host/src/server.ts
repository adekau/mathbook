import { createServer } from "node:http";
import type { RpcRequest, RpcResponse } from "@mathbook/protocol";
import { leanNativeClient } from "./lean-native.js";

/**
 * Self-hostable HTTP server: POST a JSON-RPC request, get a JSON-RPC response.
 *   node packages/engine-host/dist/server.js [port] [path/to/mathengine]
 * The engine is the native Lean executable, spoken to over stdio; its session store lives in that
 * process, keyed by sessionId in the protocol. Requests are serialized through the one stdio pipe.
 */
export function startServer(port = 8787, exe = "engine/.lake/build/bin/mathengine") {
  const client = leanNativeClient(exe);
  const server = createServer((req, res) => {
    res.setHeader("access-control-allow-origin", "*");
    res.setHeader("access-control-allow-headers", "content-type");
    if (req.method === "OPTIONS") { res.writeHead(204); res.end(); return; }
    if (req.method !== "POST") { res.writeHead(405); res.end(); return; }
    let body = "";
    req.on("data", (c) => (body += c));
    req.on("end", async () => {
      res.setHeader("content-type", "application/json");
      let rpc: RpcRequest;
      try { rpc = JSON.parse(body) as RpcRequest; }
      catch { res.end(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" } })); return; }
      let out: RpcResponse;
      try { out = { jsonrpc: "2.0", id: rpc.id, result: await client.call(rpc.method, rpc.params as never) }; }
      catch (e) { out = { jsonrpc: "2.0", id: rpc.id, error: { code: -32000, message: e instanceof Error ? e.message : String(e) } }; }
      res.end(JSON.stringify(out));
    });
  });
  server.on("close", () => client.close());
  server.listen(port, () => console.log(`mathbook engine-lean listening on http://localhost:${port}`));
  return server;
}

if (import.meta.url === `file://${process.argv[1]}`) startServer(Number(process.argv[2] ?? 8787), process.argv[3]);
