import { type Expr, num, add, mul, pow, fn, matrix, ZERO, ONE, MINUS_ONE, isNum, isZero, isOne, neg, div } from "./ast.js";
import { Rational } from "./rational.js";
import { toText } from "./printer.js";
import { type Rule, Trace, normalize } from "./rewrite.js";
import { SIMPLIFY_RULES, simplify } from "./simplify.js";

type Mat = Extract<Expr, { k: "matrix" }>;
const isMat = (e: Expr): e is Mat => e.k === "matrix";
const dims = (m: Mat) => [m.rows.length, m.rows[0]?.length ?? 0] as const;

/** Matrix arithmetic expressed as rewrite rules on add/mul/pow/fn nodes. */
export const matrixRules: Rule[] = [
  {
    name: "la.add",
    apply(e) {
      if (e.k !== "add" || !e.args.every(isMat)) return null;
      const [a, ...rest] = e.args as Mat[];
      const [r, c] = dims(a!);
      if (rest.some((m) => dims(m)[0] !== r || dims(m)[1] !== c)) throw new Error("matrix addition: dimension mismatch");
      const rows = a!.rows.map((row, i) => row.map((x, j) => add(x, ...rest.map((m) => m.rows[i]![j]!))));
      return { result: matrix(rows), explanation: "Matrices of the same shape add entrywise." };
    },
  },
  {
    name: "la.scalar-mul",
    apply(e) {
      if (e.k !== "mul") return null;
      const mats = e.args.filter(isMat), scalars = e.args.filter((a) => !isMat(a));
      if (mats.length !== 1 || scalars.length === 0) return null;
      const s = mul(...scalars), m = mats[0]!;
      return { result: matrix(m.rows.map((r) => r.map((x) => mul(s, x)))), explanation: `Scalar multiplication: multiply every entry by $${toText(s)}$.` };
    },
  },
  {
    name: "la.mul",
    apply(e) {
      if (e.k !== "mul" || e.args.length < 2 || !e.args.every(isMat)) return null;
      const [A, B] = e.args as Mat[];
      const [ar, ac] = dims(A!), [br, bc] = dims(B!);
      if (ac !== br) throw new Error(`matrix product: ${ar}×${ac} times ${br}×${bc} is undefined (inner dimensions must match)`);
      const rows = Array.from({ length: ar }, (_, i) => Array.from({ length: bc }, (_, j) => add(...Array.from({ length: ac }, (_, k) => mul(A!.rows[i]![k]!, B!.rows[k]![j]!)))));
      const rest = e.args.slice(2);
      return { result: mul(matrix(rows), ...rest), explanation: `Matrix product: entry $(i,j)$ is the dot product of row $i$ of the left factor with column $j$ of the right factor (${ar}×${ac} · ${br}×${bc} → ${ar}×${bc}).` };
    },
  },
  {
    name: "la.transpose",
    apply(e) {
      if (e.k !== "fn" || e.name !== "transpose" || !isMat(e.args[0]!)) return null;
      const m = e.args[0]!, [r, c] = dims(m);
      return { result: matrix(Array.from({ length: c }, (_, j) => Array.from({ length: r }, (_, i) => m.rows[i]![j]!))), explanation: "Transpose swaps rows and columns." };
    },
  },
  {
    name: "la.det",
    apply(e) {
      if (e.k !== "fn" || e.name !== "det" || !isMat(e.args[0]!)) return null;
      const m = e.args[0]!, [r, c] = dims(m);
      if (r !== c) throw new Error("determinant of a non-square matrix is undefined");
      if (r === 1) return { result: m.rows[0]![0]!, explanation: "The determinant of a 1×1 matrix is its entry." };
      if (r === 2) {
        const [[a, b], [c2, d]] = m.rows as [[Expr, Expr], [Expr, Expr]];
        return { result: add(mul(a, d), neg(mul(b, c2))), explanation: "$\\det\\begin{bmatrix}a&b\\\\c&d\\end{bmatrix} = ad - bc$." };
      }
      const terms = m.rows[0]!.map((a1j, j) => {
        const minor = matrix(m.rows.slice(1).map((row) => row.filter((_, k) => k !== j)));
        const sign = j % 2 === 0 ? ONE : MINUS_ONE;
        return mul(sign, a1j, fn("det", minor));
      });
      return { result: add(...terms), explanation: `Laplace expansion along the first row: $\\det M = \\sum_j (-1)^{1+j} a_{1j} \\det M_{1j}$, where $M_{1j}$ deletes row 1 and column $j$.` };
    },
  },
  {
    name: "la.pow",
    apply(e) {
      if (e.k !== "pow" || !isMat(e.base) || !isNum(e.exp) || !e.exp.v.isInteger() || e.exp.v.num < 1n) return null;
      const n = Number(e.exp.v.num);
      if (n === 1) return { result: e.base, explanation: "$M^1 = M$." };
      return { result: mul(...Array.from({ length: n }, () => e.base)), explanation: `$M^{${n}}$ is $M$ multiplied by itself ${n} times.` };
    },
  },
];

export const LINALG_RULES: readonly Rule[] = [...matrixRules, ...SIMPLIFY_RULES];

/**
 * Gauss–Jordan elimination. Recorded as row-operation Steps whose before/after are the whole
 * matrix. Works on symbolic entries as long as `simplify` can decide zero-ness of pivots.
 */
export function rref(m: Mat, trace = new Trace(false)): Mat {
  const rows: Expr[][] = m.rows.map((r) => [...r]);
  const [nr, nc] = dims(m);
  const snap = (): Mat => matrix(rows.map((r) => [...r])) as Mat;
  const rec = (rule: string, explanation: string, before: Mat) => trace.record({ rule, explanation, path: [], before, after: snap() });
  let pivotRow = 0;
  for (let col = 0; col < nc && pivotRow < nr; col++) {
    const p = rows.findIndex((r, i) => i >= pivotRow && !isZero(simplify(r[col]!)));
    if (p < 0) continue;
    if (p !== pivotRow) {
      const before = snap();
      [rows[p], rows[pivotRow]] = [rows[pivotRow]!, rows[p]!];
      rec("la.row-swap", `Swap $R_{${p + 1}}$ and $R_{${pivotRow + 1}}$ so the pivot for column ${col + 1} is nonzero. (Elementary row operations preserve the row space and the solution set.)`, before);
    }
    const pivot = rows[pivotRow]![col]!;
    if (!(isNum(pivot) && pivot.v.isOne())) {
      const before = snap();
      rows[pivotRow] = rows[pivotRow]!.map((x) => simplify(div(x, pivot)));
      rec("la.row-scale", `Scale $R_{${pivotRow + 1}}$ by $1/(${toText(pivot)})$ so the pivot becomes 1.`, before);
    }
    for (let i = 0; i < nr; i++) {
      if (i === pivotRow) continue;
      const factor = simplify(rows[i]![col]!);
      if (isZero(factor)) continue;
      const before = snap();
      rows[i] = rows[i]!.map((x, j) => simplify(add(x, neg(mul(factor, rows[pivotRow]![j]!)))));
      rec("la.row-add", `$R_{${i + 1}} \\leftarrow R_{${i + 1}} - (${toText(factor)}) R_{${pivotRow + 1}}$ to clear column ${col + 1}.`, before);
    }
    pivotRow++;
  }
  return snap();
}

export function evalLinalg(e: Expr, trace = new Trace(false)): Expr { return normalize(e, LINALG_RULES, trace); }
export { Rational, num, pow, ZERO };
