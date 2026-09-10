import { Rational } from "./rational.js";
import type { WireExpr, Path } from "@mathbook/protocol";

/**
 * Internal expression tree. Deliberately small:
 *   - subtraction is add(a, mul(-1, b))
 *   - division is mul(a, pow(b, -1))
 *   - unary minus is mul(-1, a)
 * The *printer* recovers `-`, `/` and `−x` for humans. Fewer node kinds means fewer rewrite
 * rules and fewer proof cases in Lean (lean/MathEngine/Expr.lean mirrors this exactly).
 */
export type Expr =
  | { readonly k: "num"; readonly v: Rational }
  | { readonly k: "var"; readonly name: string }
  | { readonly k: "add"; readonly args: readonly Expr[] }
  | { readonly k: "mul"; readonly args: readonly Expr[] }
  | { readonly k: "pow"; readonly base: Expr; readonly exp: Expr }
  | { readonly k: "fn"; readonly name: string; readonly args: readonly Expr[] }
  | { readonly k: "matrix"; readonly rows: readonly (readonly Expr[])[] };

// --- constructors ----------------------------------------------------------
export const num = (v: Rational | number | bigint): Expr => ({ k: "num", v: v instanceof Rational ? v : Rational.of(v) });
export const ZERO = num(0), ONE = num(1), MINUS_ONE = num(-1);
export const v = (name: string): Expr => ({ k: "var", name });
export const add = (...args: Expr[]): Expr => args.length === 1 ? args[0]! : { k: "add", args };
export const mul = (...args: Expr[]): Expr => args.length === 1 ? args[0]! : { k: "mul", args };
export const pow = (base: Expr, exp: Expr): Expr => ({ k: "pow", base, exp });
export const fn = (name: string, ...args: Expr[]): Expr => ({ k: "fn", name, args });
export const matrix = (rows: Expr[][]): Expr => ({ k: "matrix", rows });
export const neg = (a: Expr): Expr => mul(MINUS_ONE, a);
export const sub = (a: Expr, b: Expr): Expr => add(a, neg(b));
export const div = (a: Expr, b: Expr): Expr => mul(a, pow(b, MINUS_ONE));

export type NumExpr = Extract<Expr, { k: "num" }>;
export const isNum = (e: Expr): e is NumExpr => e.k === "num";
export const isNumEq = (e: Expr, r: Rational): boolean => e.k === "num" && e.v.eq(r);
export const isZero = (e: Expr): boolean => isNumEq(e, Rational.ZERO);
export const isOne = (e: Expr): boolean => isNumEq(e, Rational.ONE);

// --- children / paths ------------------------------------------------------
export function children(e: Expr): readonly Expr[] {
  switch (e.k) {
    case "num": case "var": return [];
    case "add": case "mul": case "fn": return e.args;
    case "pow": return [e.base, e.exp];
    case "matrix": return e.rows.flat();
  }
}

export function withChildren(e: Expr, cs: readonly Expr[]): Expr {
  switch (e.k) {
    case "num": case "var": return e;
    case "add": return { k: "add", args: cs };
    case "mul": return { k: "mul", args: cs };
    case "fn": return { k: "fn", name: e.name, args: cs };
    case "pow": return { k: "pow", base: cs[0]!, exp: cs[1]! };
    case "matrix": {
      const w = e.rows[0]?.length ?? 0;
      const rows: Expr[][] = [];
      for (let i = 0; i < e.rows.length; i++) rows.push(cs.slice(i * w, (i + 1) * w));
      return { k: "matrix", rows };
    }
  }
}

export function at(e: Expr, path: Path): Expr {
  let cur = e;
  for (const i of path) {
    const c = children(cur)[i];
    if (!c) throw new Error(`bad path ${path.join(".")}`);
    cur = c;
  }
  return cur;
}

export function replaceAt(e: Expr, path: Path, replacement: Expr): Expr {
  if (path.length === 0) return replacement;
  const [i, ...rest] = path as [number, ...number[]];
  const cs = [...children(e)];
  cs[i] = replaceAt(cs[i]!, rest, replacement);
  return withChildren(e, cs);
}

// --- structural equality & total order -----------------------------------
export function equal(a: Expr, b: Expr): boolean { return compare(a, b) === 0; }

export const KIND_RANK: Record<Expr["k"], number> = { num: 0, var: 1, pow: 2, fn: 3, mul: 4, add: 5, matrix: 6 };

/**
 * A total order on expressions. Used to canonicalize argument order so that
 * `x*2` and `2*x` become the same tree, which is what makes like-term collection a
 * syntactic operation. Numbers first, then variables alphabetically, then compound terms.
 */
export function compare(a: Expr, b: Expr): number {
  if (a.k !== b.k) return KIND_RANK[a.k] - KIND_RANK[b.k];
  switch (a.k) {
    case "num": return a.v.cmp((b as typeof a).v);
    case "var": return a.name < (b as typeof a).name ? -1 : a.name > (b as typeof a).name ? 1 : 0;
    case "pow": { const bb = b as typeof a; return compare(a.base, bb.base) || compare(a.exp, bb.exp); }
    case "fn": { const bb = b as typeof a; return a.name < bb.name ? -1 : a.name > bb.name ? 1 : compareLists(a.args, bb.args); }
    case "add": case "mul": return compareLists(a.args, (b as typeof a).args);
    case "matrix": return compareLists(a.rows.flat(), (b as typeof a).rows.flat());
  }
}
function compareLists(xs: readonly Expr[], ys: readonly Expr[]): number {
  const n = Math.min(xs.length, ys.length);
  for (let i = 0; i < n; i++) { const c = compare(xs[i]!, ys[i]!); if (c) return c; }
  return xs.length - ys.length;
}

export function freeVars(e: Expr, acc = new Set<string>()): Set<string> {
  if (e.k === "var") acc.add(e.name);
  for (const c of children(e)) freeVars(c, acc);
  return acc;
}

/** Number of nodes. The termination measure for the rewriter (see rewrite.ts). */
export function size(e: Expr): number { return 1 + children(e).reduce((s, c) => s + size(c), 0); }

// --- wire conversion -------------------------------------------------------
export function toWire(e: Expr): WireExpr {
  switch (e.k) {
    case "num": return { k: "num", v: { num: e.v.num.toString(), den: e.v.den.toString() } };
    case "var": return e;
    case "add": return { k: "add", args: e.args.map(toWire) };
    case "mul": return { k: "mul", args: e.args.map(toWire) };
    case "pow": return { k: "pow", base: toWire(e.base), exp: toWire(e.exp) };
    case "fn": return { k: "fn", name: e.name, args: e.args.map(toWire) };
    case "matrix": return { k: "matrix", rows: e.rows.map((r) => r.map(toWire)) };
  }
}
export function fromWire(w: WireExpr): Expr {
  switch (w.k) {
    case "num": return num(Rational.of(BigInt(w.v.num), BigInt(w.v.den)));
    case "var": return w;
    case "add": return { k: "add", args: w.args.map(fromWire) };
    case "mul": return { k: "mul", args: w.args.map(fromWire) };
    case "pow": return { k: "pow", base: fromWire(w.base), exp: fromWire(w.exp) };
    case "fn": return { k: "fn", name: w.name, args: w.args.map(fromWire) };
    case "matrix": return { k: "matrix", rows: w.rows.map((r) => r.map(fromWire)) };
  }
}
