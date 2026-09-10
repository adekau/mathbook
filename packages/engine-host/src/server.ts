import { createServer } from "node:http";
import { serve } from "@mathbook/protocol";
import type { Transport } from "@mathbook/protocol";
import { Engine } from "@mathbook/reference-ts";

/**
 * Self-hostable HTTP server: POST a JSON-RPC request, get a JSON-RPC response.
 *   node packages/engine-host/dist/server.js [port]
 * One Engine instance serves all sessions; sessions are keyed by sessionId in the protocol.
 */
export function startServer(port = 8787, engine = new Engine()) {
  const server = createServer((req, res) => {
    res.setHeader("access-control-allow-origin", "*");
    res.setHeader("access-control-allow-headers", "content-type");
    if (req.method === "OPTIONS") { res.writeHead(204); res.end(); return; }
    if (req.method !== "POST") { res.writeHead(405); res.end(); return; }
    let body = "";
    req.on("data", (c) => (body += c));
    req.on("end", () => {
      const t: Transport = { send: (m) => { res.setHeader("content-type", "application/json"); res.end(m); }, onMessage: (h) => h(body) };
      serve(t, engine);
    });
  });
  server.listen(port, () => console.log(`mathbook engine-ts listening on http://localhost:${port}`));
  return server;
}

if (import.meta.url === `file://${process.argv[1]}`) startServer(Number(process.argv[2] ?? 8787));
