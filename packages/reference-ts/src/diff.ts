import { Rational } from "./rational.js";
import { type Expr, num, add, mul, pow, fn, v, ZERO, ONE, MINUS_ONE, isNum, freeVars, equal, matrix, div, neg } from "./ast.js";
import { toText } from "./printer.js";
import { type Rule, Trace, normalize } from "./rewrite.js";
import { SIMPLIFY_RULES } from "./simplify.js";

/**
 * Differentiation is *not* a separate algorithm here: `diff(e, x)` is an ordinary node, and
 * the calculus rules are rewrite rules that push it inward. The rewriter's trace then reads
 * exactly like a textbook derivation, with pending d/dx's visible at each step:
 *
 *   d/dx(x^2 + sin x)  →  d/dx(x^2) + d/dx(sin x)  →  2x + d/dx(sin x)  →  2x + cos x
 *
 * The Lean side proves each rule against Mathlib's `HasDerivAt` (see book/TRACKING.md, M4).
 */

const D = (e: Expr, x: string): Expr => fn("diff", e, v(x));
const T = toText;

function target(e: Expr): { body: Expr; x: string } | null {
  if (e.k !== "fn" || e.name !== "diff" || e.args.length !== 2 || e.args[1]!.k !== "var") return null;
  return { body: e.args[0]!, x: (e.args[1] as Extract<Expr, { k: "var" }>).name };
}
const dependsOn = (e: Expr, x: string) => freeVars(e).has(x);

export const diffRules: Rule[] = [
  {
    name: "diff.higher-order",
    apply(e) {
      if (e.k !== "fn" || e.name !== "diff" || e.args.length !== 3 || e.args[1]!.k !== "var" || !isNum(e.args[2]!) || !e.args[2]!.v.isInteger() || e.args[2]!.v.num < 1n) return null;
      const n = Number(e.args[2]!.v.num);
      const x = (e.args[1] as Extract<Expr, { k: "var" }>).name;
      let r = e.args[0]!;
      for (let i = 0; i < n; i++) r = D(r, x);
      return { result: r, explanation: `The ${n}th derivative is ${n} successive derivatives.` };
    },
  },
  {
    name: "diff.constant",
    apply(e) {
      const t = target(e); if (!t || dependsOn(t.body, t.x)) return null;
      return { result: ZERO, explanation: `$${T(t.body)}$ does not depend on $${t.x}$, so its derivative is 0: constants have zero rate of change.` };
    },
  },
  {
    name: "diff.variable",
    apply(e) {
      const t = target(e); if (!t || !(t.body.k === "var" && t.body.name === t.x)) return null;
      return { result: ONE, explanation: `$\\frac{d}{d${t.x}} ${t.x} = 1$: the identity function has slope 1 everywhere.` };
    },
  },
  {
    name: "diff.sum",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "add") return null;
      return { result: add(...t.body.args.map((a) => D(a, t.x))), explanation: "Sum rule: the derivative of a sum is the sum of the derivatives (differentiation is linear)." };
    },
  },
  {
    name: "diff.constant-multiple",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "mul") return null;
      const consts = t.body.args.filter((a) => !dependsOn(a, t.x));
      const rest = t.body.args.filter((a) => dependsOn(a, t.x));
      if (consts.length === 0 || rest.length === 0) return null;
      return { result: mul(...consts, D(mul(...rest), t.x)), explanation: `Constant multiple rule: factors independent of $${t.x}$ (here $${T(mul(...consts))}$) pull out of the derivative.` };
    },
  },
  {
    name: "diff.product",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "mul") return null;
      const fs = t.body.args;
      const terms = fs.map((f, i) => mul(D(f, t.x), ...fs.filter((_, j) => j !== i)));
      const [f, g] = fs;
      return {
        result: add(...terms),
        explanation: fs.length === 2
          ? `Product rule: $(fg)' = f'g + fg'$ with $f = ${T(f!)}$ and $g = ${T(g!)}$.`
          : `Product rule for ${fs.length} factors: differentiate each factor in turn, holding the others fixed, and add.`,
      };
    },
  },
  {
    name: "diff.power",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "pow") return null;
      const { base, exp } = t.body;
      const baseDep = dependsOn(base, t.x), expDep = dependsOn(exp, t.x);
      if (baseDep && !expDep) {
        const n = exp, nMinus1 = add(exp, MINUS_ONE);
        if (base.k === "var" && base.name === t.x)
          return { result: mul(n, pow(base, nMinus1)), explanation: `Power rule: $\\frac{d}{d${t.x}} ${t.x}^n = n\\,${t.x}^{n-1}$ with $n = ${T(n)}$.` };
        return { result: mul(n, pow(base, nMinus1), D(base, t.x)), explanation: `Power rule with the chain rule: $(u^n)' = n u^{n-1} u'$ where $u = ${T(base)}$.` };
      }
      if (!baseDep && expDep) {
        return { result: mul(t.body, fn("ln", base), D(exp, t.x)), explanation: `Exponential rule with the chain rule: $(b^u)' = b^u \\ln b \\cdot u'$ where $u = ${T(exp)}$.` };
      }
      if (baseDep && expDep) {
        // f^g = exp(g ln f)
        return { result: mul(t.body, add(mul(D(exp, t.x), fn("ln", base)), mul(exp, div(D(base, t.x), base)))), explanation: `Both base and exponent depend on $${t.x}$: write $f^g = e^{g \\ln f}$ and differentiate, giving $f^g\\left(g' \\ln f + g \\frac{f'}{f}\\right)$.` };
      }
      return null;
    },
  },
  {
    name: "diff.chain",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "fn" || t.body.args.length !== 1) return null;
      const u = t.body.args[0]!;
      const outer: Record<string, [Expr, string]> = {
        sin: [fn("cos", u), "\\sin' = \\cos"],
        cos: [neg(fn("sin", u)), "\\cos' = -\\sin"],
        tan: [pow(fn("cos", u), num(-2)), "\\tan' = \\sec^2 = 1/\\cos^2"],
        exp: [fn("exp", u), "\\exp' = \\exp"],
        ln: [pow(u, MINUS_ONE), "\\ln' u = 1/u"],
      };
      const o = outer[t.body.name];
      if (!o) return null;
      const [fprime, law] = o;
      const inner = equal(u, v(t.x)) ? [] : [D(u, t.x)];
      return {
        result: mul(fprime, ...inner),
        explanation: inner.length ? `Chain rule: $(f(u))' = f'(u)\\,u'$ with $${law}$ and $u = ${T(u)}$.` : `$${law}$.`,
      };
    },
  },
  {
    name: "diff.matrix",
    apply(e) {
      const t = target(e); if (!t || t.body.k !== "matrix") return null;
      return { result: matrix(t.body.rows.map((r) => r.map((c) => D(c, t.x)))), explanation: "Differentiate a matrix entrywise." };
    },
  },
];

/** d^n/dx^n of `e`, with simplification interleaved so the trace reads naturally. */
export function differentiate(e: Expr, x: string, n = 1, trace = new Trace(false)): Expr {
  let cur = e;
  for (let i = 0; i < n; i++) cur = D(cur, x);
  return normalize(cur, [...diffRules, ...SIMPLIFY_RULES], trace);
}

export { Rational };
