import { test } from "node:test";
import assert from "node:assert/strict";
import { leanNativeClient } from "../dist/lean-native.js";
test("protocol client ↔ native Lean engine over stdio", async () => {
  const c = leanNativeClient(new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname);
  const caps = await c.call("engine.capabilities", {});
  assert.equal(caps.engine, "engine-lean"); assert.equal(caps.verified, true);
  const r = await c.call("engine.evaluate", { sessionId: "s", cellId: "1", source: "x + 0" });
  assert.equal(r.ok, true); assert.equal(r.rendered.text, "x");
  c.close();
});
