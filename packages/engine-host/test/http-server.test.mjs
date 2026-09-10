import { test } from "node:test";
import assert from "node:assert/strict";
import { startServer } from "../dist/server.js";
import { createClient } from "@mathbook/protocol";
import { httpTransport } from "../dist/index.js";

test("HTTP host: protocol client → HTTP → native Lean engine, sessions persist", async () => {
  const exe = new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname;
  const server = startServer(0, exe);
  await new Promise((r) => server.once("listening", r));
  const { port } = server.address();
  const c = createClient(httpTransport(`http://localhost:${port}`));
  const caps = await c.call("engine.capabilities", {});
  assert.equal(caps.engine, "engine-lean");
  const f = await c.call("engine.evaluate", { sessionId: "h", cellId: "1", source: "let f = x^2" });
  assert.deepEqual(f.bound, ["f"]);
  const d = await c.call("engine.evaluate", { sessionId: "h", cellId: "2", source: "diff(f, x)" });
  assert.equal(d.rendered.text, "2*x");
  const bad = await fetch(`http://localhost:${port}`, { method: "POST", body: "{" });
  assert.equal((await bad.json()).error.code, -32700);
  server.close();
});
