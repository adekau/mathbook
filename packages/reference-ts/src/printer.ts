import { type Expr, isNum, isNumEq } from "./ast.js";
import { Rational } from "./rational.js";
import type { Path, Rendered } from "@mathbook/protocol";

/**
 * Printing recovers human notation from the minimal AST:
 *   add(a, mul(-1, b))  →  a - b
 *   mul(a, pow(b, -1))  →  a / b    (LaTeX: \frac{a}{b})
 *   mul(-1, a)          →  -a
 *   pow(a, 1/2)         →  sqrt(a)
 *
 * Every printed subterm knows its Path, so with `paths: true` the LaTeX output wraps each
 * subterm in \htmlData{path=...}{...}. KaTeX renders that (with trust: true) as a <span
 * data-path="0.1">, which is how the UI turns a click/selection into a Path for engine.explain.
 */

interface Target {
  wrap(path: Path, s: string): string;
  num(r: Rational): string;
  variable(name: string): string;
  frac(n: string, d: string): string;
  pow(b: string, e: string): string;
  sqrt(s: string): string;
  fn(name: string, args: string[]): string;
  matrix(rows: string[][]): string;
  times: string;
  parens(s: string): string;
  /** Context precedence for a denominator: text needs parens around products (a/(b*c)); \frac does not. */
  denomPrec: number;
}

const textTarget = (paths: boolean): Target => ({
  wrap: (_p, s) => s,
  num: (r) => r.toString(),
  variable: (n) => n,
  frac: (n, d) => `${n}/${d}`,
  pow: (b, e) => `${b}^${e}`,
  sqrt: (s) => `sqrt(${s})`,
  fn: (n, a) => `${n}(${a.join(", ")})`,
  matrix: (rows) => `[${rows.map((r) => r.join(", ")).join("; ")}]`,
  times: "*",
  parens: (s) => `(${s})`,
  denomPrec: 3, // P_POW
});

const GREEK: Record<string, string> = { "π": "\\pi", alpha: "\\alpha", beta: "\\beta", theta: "\\theta", lambda: "\\lambda" };
const latexTarget = (paths: boolean): Target => ({
  wrap: (p, s) => (paths ? `\\htmlData{path=${p.join(".") || "root"}}{${s}}` : s),
  num: (r) => r.toLatex(),
  variable: (n) => GREEK[n] ?? (n.length > 1 ? `\\mathit{${n}}` : n),
  frac: (n, d) => `\\frac{${n}}{${d}}`,
  pow: (b, e) => `{${b}}^{${e}}`,
  sqrt: (s) => `\\sqrt{${s}}`,
  fn: (n, a) => `${["sin", "cos", "tan", "exp", "ln", "log"].includes(n) ? `\\${n}` : `\\operatorname{${n}}`}\\left(${a.join(", ")}\\right)`,
  matrix: (rows) => `\\begin{bmatrix}${rows.map((r) => r.join(" & ")).join(" \\\\ ")}\\end{bmatrix}`,
  times: " \\cdot ",
  parens: (s) => `\\left(${s}\\right)`,
  denomPrec: 2, // P_MUL
});

// precedence levels: what the *context* demands vs. what the term *provides*
const P_ADD = 1, P_MUL = 2, P_NEG = 2, P_POW = 3, P_ATOM = 4;

/** Split a term into (coefficient, rest) treating mul(c, ...) with numeric c. Rest keeps original child paths. */
function splitCoeff(e: Expr): { coeff: Rational; rest: Expr | null; restPathOffset: number } {
  if (isNum(e)) return { coeff: e.v, rest: null, restPathOffset: 0 };
  if (e.k === "mul" && e.args.length >= 2 && isNum(e.args[0]!)) {
    const rest = e.args.length === 2 ? e.args[1]! : { k: "mul" as const, args: e.args.slice(1) };
    return { coeff: e.args[0]!.v, rest, restPathOffset: 1 };
  }
  return { coeff: Rational.ONE, rest: e, restPathOffset: -1 };
}

function print(e: Expr, path: Path, T: Target, ctx: number): string {
  const out = printRaw(e, path, T);
  const s = out.prec < ctx ? T.parens(out.s) : out.s;
  return T.wrap(path, s);
}

/** Print a child at path index i, keeping path bookkeeping in one place. */
const child = (e: Expr, path: Path, i: number, T: Target, ctx: number) => print(e, [...path, i], T, ctx);

function printRaw(e: Expr, path: Path, T: Target): { s: string; prec: number } {
  switch (e.k) {
    case "num": return { s: T.num(e.v), prec: e.v.isNegative() ? P_NEG : P_ATOM };
    case "var": return { s: T.variable(e.name), prec: P_ATOM };
    case "matrix": {
      const rows = e.rows.map((row, r) => row.map((c, j) => print(c, [...path, r * row.length + j], T, P_ADD)));
      return { s: T.matrix(rows), prec: P_ATOM };
    }
    case "fn": {
      const args = e.args.map((a, i) => child(a, path, i, T, P_ADD));
      if (e.name === "sqrt" && args.length === 1) return { s: T.sqrt(args[0]!), prec: P_ATOM };
      if (e.name === "diff" && args.length === 2 && e.args[1]!.k === "var" && T.times !== "*")
        return { s: `\\frac{d}{d${args[1]!}}\\left(${args[0]!}\\right)`, prec: P_MUL };
      return { s: T.fn(e.name, args), prec: P_ATOM };
    }
    case "pow": {
      // x^(1/2) → sqrt(x); x^(-n) handled by mul printing when it is a factor; standalone prints as-is
      if (isNumEq(e.exp, Rational.of(1, 2))) return { s: T.sqrt(print(e.base, [...path, 0], T, P_ADD)), prec: P_ATOM };
      if (isNum(e.exp) && e.exp.v.isNegative()) {
        // standalone x^(-n) → 1/x^n
        const n = e.exp.v.neg();
        const base = print(e.base, [...path, 0], T, n.isOne() ? T.denomPrec : P_POW + 1);
        return { s: T.frac(T.num(Rational.ONE), n.isOne() ? base : T.pow(base, T.wrap([...path, 1], T.num(n)))), prec: P_MUL };
      }
      const b = print(e.base, [...path, 0], T, P_POW + 1); // left of ^ needs parens for anything non-atomic incl. -3 and 2^3
      const x = print(e.exp, [...path, 1], T, P_POW);      // right-assoc: 2^3^4 is 2^(3^4)
      return { s: T.pow(b, x), prec: P_POW };
    }
    case "add": {
      let s = "";
      e.args.forEach((a, i) => {
        const { coeff, rest, restPathOffset } = splitCoeff(a);
        const negative = coeff.isNegative();
        if (i === 0 && !negative) { s += child(a, path, i, T, P_ADD); return; }
        const sign = negative ? " - " : " + ";
        let termStr: string;
        if (negative) {
          // print |coeff| * rest, with paths still pointing into the original child
          const absC = coeff.neg();
          const p = [...path, i];
          if (rest === null) termStr = T.wrap(p, T.num(absC));
          else if (absC.isOne()) termStr = restPathOffset >= 0 ? print(rest, [...p, restPathOffset], T, P_MUL) : print(rest, p, T, P_MUL);
          else termStr = T.wrap(p, T.num(absC) + T.times + print(rest, [...p, restPathOffset], T, P_MUL));
        } else termStr = child(a, path, i, T, P_MUL);
        s += (i === 0 ? sign.trim() : sign) + termStr;
      });
      return { s, prec: P_ADD };
    }
    case "mul": {
      // Partition into numerator / denominator factors; a leading -1 becomes a unary minus.
      const numer: string[] = [], denom: string[] = [];
      let sign = "";
      e.args.forEach((a, i) => {
        const p = [...path, i];
        if (i === 0 && isNum(a) && a.v.isNegative()) {
          sign = "-";
          if (!a.v.neg().isOne()) numer.push(T.wrap(p, T.num(a.v.neg())));
          return;
        }
        if (a.k === "pow" && isNum(a.exp) && a.exp.v.isNegative()) {
          const n = a.exp.v.neg();
          const base = print(a.base, [...p, 0], T, n.isOne() ? T.denomPrec : P_POW + 1);
          denom.push(T.wrap(p, n.isOne() ? base : T.pow(base, T.wrap([...p, 1], T.num(n)))));
          return;
        }
        numer.push(print(a, p, T, P_MUL + (i > 0 && isNum(a) ? 1 : 0)));
      });
      const n = numer.length ? numer.join(T.times) : T.num(Rational.ONE);
      if (denom.length === 0) return { s: sign + n, prec: sign ? P_NEG : P_MUL };
      const d = denom.length > 1 && T.denomPrec > P_MUL ? T.parens(denom.join(T.times)) : denom.join(T.times);
      return { s: sign + T.frac(n, d), prec: sign ? P_NEG : P_MUL };
    }
  }
}

export function toText(e: Expr): string { return print(e, [], textTarget(false), P_ADD); }
export function toLatex(e: Expr, paths = false): string { return print(e, [], latexTarget(paths), P_ADD); }
export function render(e: Expr, paths = false): Rendered { return { text: toText(e), latex: toLatex(e, paths) }; }
