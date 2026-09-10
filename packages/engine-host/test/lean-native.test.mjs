import { test } from "node:test";
import assert from "node:assert/strict";
import { leanNativeClient } from "../dist/lean-native.js";
test("protocol client ↔ native Lean engine over stdio", async () => {
  const c = leanNativeClient(new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname);
  const caps = await c.call("engine.capabilities", {});
  assert.equal(caps.engine, "engine-lean"); assert.equal(caps.verified, true);
  const r = await c.call("engine.evaluate", { sessionId: "s", cellId: "1", source: "x + 0" });
  assert.equal(r.ok, true); assert.equal(r.rendered.text, "x");
  // session state lives in the host loop: a `let` in one call is visible in the next
  const f = await c.call("engine.evaluate", { sessionId: "s", cellId: "2", source: "let f = x^2 + 3x" });
  assert.deepEqual(f.bound, ["f"]);
  const d = await c.call("engine.evaluate", { sessionId: "s", cellId: "3", source: "diff(f, x)", showWork: true });
  assert.equal(d.rendered.text, "2*x + 3");
  assert.ok(d.derivation.steps.some((s) => s.rule === "diff.power"));
  const ex = await c.call("engine.explain", { sessionId: "s", cellId: "3", path: [0] });
  assert.equal(ex.rendered.text, "2*x");
  c.close();
});
