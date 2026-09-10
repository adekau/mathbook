import { type Expr, children, withChildren, num } from "./ast.js";
import { Rational } from "./rational.js";

export const CONSTANTS: Record<string, number> = { "π": Math.PI, e: Math.E };

/** Replace free occurrences of variables per `bindings`. There are no binders, so this is plain. */
export function substitute(e: Expr, bindings: ReadonlyMap<string, Expr>): Expr {
  if (e.k === "var") return bindings.get(e.name) ?? e;
  const cs = children(e);
  if (cs.length === 0) return e;
  return withChildren(e, cs.map((c) => substitute(c, bindings)));
}

const FNS: Record<string, (x: number) => number> = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan, exp: Math.exp, ln: Math.log, log: Math.log10, sqrt: Math.sqrt, abs: Math.abs,
};

/** Floating-point value. Throws on unbound variables or unevaluated commands. */
export function evalNumeric(e: Expr, env: ReadonlyMap<string, number> = new Map()): number {
  switch (e.k) {
    case "num": return e.v.toNumber();
    case "var": {
      const x = env.get(e.name) ?? CONSTANTS[e.name];
      if (x === undefined) throw new Error(`cannot evaluate numerically: '${e.name}' is unbound`);
      return x;
    }
    case "add": return e.args.reduce((s, a) => s + evalNumeric(a, env), 0);
    case "mul": return e.args.reduce((s, a) => s * evalNumeric(a, env), 1);
    case "pow": return Math.pow(evalNumeric(e.base, env), evalNumeric(e.exp, env));
    case "fn": {
      const f = FNS[e.name];
      if (!f || e.args.length !== 1) throw new Error(`cannot evaluate '${e.name}' numerically`);
      return f(evalNumeric(e.args[0]!, env));
    }
    case "matrix": throw new Error("N() of a matrix: apply N to entries instead");
  }
}

/** A float as an exact rational from its shortest round-trip decimal (so 0.1 stays 1/10). */
export function floatToExpr(x: number): Expr {
  if (!Number.isFinite(x)) throw new Error(`non-finite result: ${x}`);
  const [mant, expPart] = x.toPrecision(15).split("e");
  let r = Rational.parse(mant!.replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, ""));
  if (expPart) r = r.mul(Rational.of(10).pow(BigInt(expPart)));
  return num(r.withApprox(true));
}
