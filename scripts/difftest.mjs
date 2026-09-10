// M2: wire-level differential test, reference-ts (in-process) vs engine-lean (native, stdio).
//   node scripts/difftest.mjs            compare and list mismatches
//   node scripts/difftest.mjs --write    also write engine/Tests/golden.tsv from the reference's answers
// Both engines see the same corpus in the same session order, so `let` bindings carry over.
import { writeFileSync } from "node:fs";
import { Engine } from "@mathbook/reference-ts";
import { leanNativeClient } from "@mathbook/engine-host/lean-native";

export const CORPUS = [
  // numbers & parsing
  "2 + 3*4", "-2^2", "(-2)^2", "2^3^2", "8/2/2", "a - b - c", "2x + 3x", "2(x+1)", "x y", "3 4", "x +",
  "0.125 + 0.875", "1.5 * 2", "1/3 + 1/6", "2.5x + .5", "6/4", "pi", "[1,2;3,4]", "[1,2;3]",
  // printer
  "x/(y*z)", "(x+1)/(x-1)", "1/x", "-(-x)", "sqrt(2)", "x - 2y", "-x - 1", "x/2 + sqrt(y)", "1/x^2", "x^(1/2)",
  "-x", "x*(-1)", "(x+1)*(x-1)", "2*(x+y)", "x^-1", "x^(-2)*y", "a/b/c", "a/(b/c)", "(a/b)^2", "sin(x)^2",
  // simplify
  "0*x + 1*y", "x - x", "x*x*x", "x^2 * x^3 / x", "(x^2)^3", "sqrt(16)", "ln(exp(x))", "1/2 + 1/3",
  "1 + 3x + x^2", "x + 2x + y", "x*0.5*2", "x*2 + y", "y + 2*x", "sin(0)", "cos(0)", "exp(0)", "ln(1)",
  "exp(ln(x))", "ln(x^2)", "abs(-3)", "0^5", "1^x", "x^0", "x^1", "2^10", "8^(1/3)", "sqrt(8)", "(2x)^2",
  "(x^y)^2", "x*x^2", "x^2*x", "x^a * x^b", "3*x*2", "x + x", "2*x - 2*x", "a*b + b*a", "(x+1) + (x+1)",
  "x^2 + x^2", "1 + 1/2", "x/x", "2/4*x", "-3*x + 3*x", "x*y*x", "0.1 + 0.2", "1e3",
  // diff
  "diff(x^3, x)", "diff(5, x)", "diff(sin(x^2), x)", "diff(x*sin(x), x)", "diff(2^x, x)", "diff(x^x, x)",
  "diff(x^3, x, 2)", "diff(ln(x), x)", "diff(cos(x), x)", "diff(tan(x), x)", "diff(exp(2x), x)", "diff(x^2 + 2x + 1, x)",
  "diff(1/(x+1), x)", "diff(sqrt(x), x)", "diff(x*y, x)", "diff([x, x^2], x)", "diff(sin(x)*exp(x), x)", "diff(ln(x^2 + 1), x)",
  "diff(x^3 + 2x, x)", "diff(y, x)", "diff(x, x)", "diff(3x, x)",
  // linalg
  "[1,2;3,4] * [5,6;7,8]", "det([1,2;3,4])", "det([2,0,1;1,3,2;1,1,1])", "det([1,2,3;4,5,6;7,8,10])",
  "transpose([1,2,3;4,5,6])", "rref([1,2,3;4,5,6;7,8,10])", "rref([1,2;2,4])", "det([a,b;c,d])", "[1,2] * [1,2]",
  "[1,2;3,4] + [1,0;0,1]", "2*[1,2;3,4]", "[1,2;3,4]^2", "det([1])", "[1,2;3,4] + [1,2]", "rref([0,1;1,0])",
  "rref([2,4;1,3])", "[x, y] * [1; 2]",
  // session
  "let f = x^2 + 3x", "diff(f, x)", "subst(f, x, 2)", "N(pi)", "N(sqrt(2))", "N(1/3)", "N(f)", "let g = 2x",
  "f + g", "expand((x+1)^3)", "expand((x+y)^2)", "expand((x+1)*(x-1))", "expand(2*(x+y))", "simplify(x + x)",
  "N(exp(1))", "N(2^0.5)", "subst(g, x, y)", "expand((a+b)^4)",
  // matrix products must not be reordered (the two vectors sort on opposite sides of the matrix)
  "let m = [1,2,3;4,5,6;7,8,10]", "m * [1;2;3]", "m * [1;2;4]", "[1;2;3] * [1,2,3]", "[1,2,3] * [1;2;3]", "m * m",
];

const ref = new Engine();
const lean = leanNativeClient();
const write = process.argv.includes("--write");
const strip = (o) => JSON.stringify(o);
let mismatches = 0;
const golden = [];
for (const [i, source] of CORPUS.entries()) {
  const cellId = `c${i}`;
  const a = ref.evaluate({ sessionId: "d", cellId, source, paths: true });
  const b = await lean.call("engine.evaluate", { sessionId: "d", cellId, source, paths: true });
  const summary = (r) => r.ok ? { text: r.rendered.text, latex: r.rendered.latex, value: r.value, bound: r.bound ?? null } : { error: r.error.code, message: r.error.message, span: r.error.span ?? null };
  const sa = summary(a), sb = summary(b);
  golden.push(a.ok ? `${source}\t${a.rendered.text}` : `${source}\t<error: ${a.error.message}>`);
  const diffs = Object.keys(sa).filter((k) => strip(sa[k]) !== strip(sb[k]));
  if (diffs.length) {
    mismatches++;
    console.log(`✗ ${source}`);
    for (const k of diffs) console.log(`    ${k}:\n      ref : ${strip(sa[k])}\n      lean: ${strip(sb[k])}`);
  }
}
lean.close();
console.log(`${CORPUS.length} sources, ${mismatches} mismatches`);
if (write) { writeFileSync("engine/Tests/golden.tsv", golden.join("\n") + "\n"); console.log("wrote engine/Tests/golden.tsv"); }
process.exitCode = mismatches ? 1 : 0;
