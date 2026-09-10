import { test } from "node:test";
import assert from "node:assert/strict";
import { Engine, parse, toText, toLatex, simplify, differentiate, evalNumeric, Rational, equal } from "../dist/index.js";

const eng = new Engine();
const ev = (source, opts = {}) => {
  const r = eng.evaluate({ sessionId: "t", cellId: source, source, ...opts });
  if (!r.ok) throw new Error(r.error.message);
  return r;
};
const txt = (s) => ev(s).rendered.text;
const roundtrip = (s) => toText(parse(s).value);

test("rational arithmetic is exact and normalized", () => {
  assert.equal(Rational.of(6, -4).toString(), "-3/2");
  assert.equal(Rational.parse("0.125").toString(), "0.125"); // decimal literal ⇒ approximate ⇒ prints as decimal
  assert.equal(Rational.of(1, 8).toString(), "1/8");           // exact ⇒ fraction
  assert.equal(Rational.parse("2.5").toString(), "2.5");
  assert.equal(Rational.parse("0.125").add(Rational.parse("0.875")).toString(), "1");
  assert.equal(Rational.parse("1.5").mul(Rational.of(2)).toString(), "3");
  assert.equal(Rational.of(1, 3).add(Rational.of(1, 6)).toString(), "1/2");
});

test("parser: precedence and associativity", () => {
  assert.equal(txt("2 + 3*4"), "14");
  assert.equal(txt("-2^2"), "-4");          // unary minus binds looser than ^
  assert.equal(txt("(-2)^2"), "4");
  assert.equal(txt("2^3^2"), "512");        // right-assoc
  assert.equal(txt("8/2/2"), "2");          // left-assoc
  assert.equal(txt("a - b - c"), "a - b - c");
});

test("parser: implicit multiplication and calls", () => {
  assert.equal(txt("2x + 3x"), "5*x");
  assert.equal(txt("2(x+1)"), "2*(x + 1)");
  assert.equal(roundtrip("2x^2"), "2*x^2");
  assert.equal(txt("sin(0)"), "0");
  assert.throws(() => ev("3 4"), /unexpected '4'/);
  const bad = eng.evaluate({ sessionId: "t", cellId: "e", source: "x +" });
  assert.equal(bad.ok, false); assert.equal(bad.error.code, "syntax");
});

test("printer: recovers -, /, sqrt and parenthesizes correctly", () => {
  assert.equal(txt("x/(y*z)"), "x/(y*z)");
  assert.equal(txt("(x+1)/(x-1)"), "(x + 1)/(x - 1)");
  assert.equal(txt("1/x"), "1/x");
  assert.equal(txt("-(-x)"), "x");
  assert.equal(txt("sqrt(2)"), "sqrt(2)");
  assert.equal(toLatex(parse("x/2 + sqrt(y)").value), "\\frac{x}{2} + \\sqrt{y}");
});

test("simplify: identities, folding, like terms, powers", () => {
  assert.equal(txt("0*x + 1*y"), "y");
  assert.equal(txt("x - x"), "0");
  assert.equal(txt("x*x*x"), "x^3");
  assert.equal(txt("x^2 * x^3 / x"), "x^4");
  assert.equal(txt("(x^2)^3"), "x^6");
  assert.equal(txt("sqrt(16)"), "4");
  assert.equal(txt("ln(exp(x))"), "x");
  assert.equal(txt("1/2 + 1/3"), "5/6");
  assert.equal(txt("expand((x+1)^3)"), "x^3 + 3*x^2 + 3*x + 1");
});

test("simplify: canonical order makes structurally-equal terms identical", () => {
  const a = simplify(parse("x*2 + y").value), b = simplify(parse("y + 2*x").value);
  assert.ok(equal(a, b), `${toText(a)} vs ${toText(b)}`);
});

test("diff: standard rules", () => {
  assert.equal(txt("diff(x^3, x)"), "3*x^2");
  assert.equal(txt("diff(5, x)"), "0");
  assert.equal(txt("diff(sin(x^2), x)"), "2*x*cos(x^2)");
  assert.equal(txt("diff(x*sin(x), x)"), "x*cos(x) + sin(x)");
  assert.equal(txt("diff(2^x, x)"), "2^x*ln(2)");
  assert.equal(txt("diff(x^x, x)"), "x^x*(ln(x) + 1)");
  assert.equal(txt("diff(x^3, x, 2)"), "6*x");
  assert.equal(txt("diff(ln(x), x)"), "1/x");
});

test("diff: numerically agrees with a finite difference (differential test)", () => {
  for (const src of ["x^3 + 2x", "sin(x)*exp(x)", "ln(x^2 + 1)", "x^x", "1/(x+1)"]) {
    const f = parse(src).value, df = differentiate(f, "x");
    for (const x0 of [0.7, 1.3, 2.1]) {
      const h = 1e-6, env = (x) => new Map([["x", x]]);
      const fd = (evalNumeric(f, env(x0 + h)) - evalNumeric(f, env(x0 - h))) / (2 * h);
      assert.ok(Math.abs(fd - evalNumeric(df, env(x0))) < 1e-5, `${src} at ${x0}`);
    }
  }
});

test("linear algebra", () => {
  assert.equal(txt("[1,2;3,4] * [5,6;7,8]"), "[19, 22; 43, 50]");
  assert.equal(txt("det([1,2;3,4])"), "-2");
  assert.equal(txt("det([2,0,1;1,3,2;1,1,1])"), "0");
  assert.equal(txt("det([1,2,3;4,5,6;7,8,10])"), "-3");
  assert.equal(txt("transpose([1,2,3;4,5,6])"), "[1, 4; 2, 5; 3, 6]");
  assert.equal(txt("rref([1,2,3;4,5,6;7,8,10])"), "[1, 0, 0; 0, 1, 0; 0, 0, 1]");
  assert.equal(txt("rref([1,2;2,4])"), "[1, 2; 0, 0]");
  assert.equal(txt("det([a,b;c,d])"), "a*d - b*c");
  assert.throws(() => ev("[1,2] * [1,2]"), /inner dimensions/);
});

test("session: let-binding and substitution", () => {
  ev("let f = x^2 + 3x");
  assert.equal(txt("diff(f, x)"), "2*x + 3");
  assert.equal(txt("subst(f, x, 2)"), "10");
  assert.equal(txt("N(pi)"), "3.14159265358979");
});

test("show work: derivation steps carry rule names, paths and explanations", () => {
  const r = ev("diff(x^2 * sin(x), x)", { showWork: true });
  const rules = r.derivation.steps.map((s) => s.rule);
  assert.ok(rules.includes("diff.product") && rules.includes("diff.power") && rules.includes("diff.chain"), rules.join());
  for (const s of r.derivation.steps) { assert.ok(s.explanation.length > 0); assert.ok(Array.isArray(s.path)); }
  const rr = ev("rref([1,2;3,4])", { showWork: true });
  assert.equal(rr.derivation.steps[0].rule, "cmd.rref");
  assert.ok(rr.derivation.steps[0].sub.steps.some((s) => s.rule === "la.row-add"));
});

test("show work: LaTeX paths and explain()", () => {
  const r = ev("diff(x^3, x)", { showWork: true, paths: true });
  assert.match(r.rendered.latex, /\\htmlData\{path=1\.0\}\{x\}/);
  const ex = eng.explain({ sessionId: "t", cellId: "diff(x^3, x)", path: [1] });
  assert.equal(ex.rendered.text, "x^2");
  assert.ok(ex.steps.some((s) => s.rule === "diff.power"));
});

test("protocol: round trip through JSON-RPC serve/createClient", async () => {
  const { serve, createClient } = await import("@mathbook/protocol");
  const mk = () => { let h = () => {}; return { send: (m) => queueMicrotask(() => h(m)), onMessage: (f) => { h = f; } }; };
  const a = mk(), b = mk();
  serve({ send: b.send, onMessage: a.onMessage }, new Engine());
  const client = createClient({ send: a.send, onMessage: b.onMessage });
  const caps = await client.call("engine.capabilities", {});
  assert.equal(caps.engine, "reference-ts");
  const res = await client.call("engine.evaluate", { sessionId: "p", cellId: "1", source: "diff(x^2, x)" });
  assert.equal(res.rendered.text, "2*x");
  assert.equal(res.value.k, "mul");
});
