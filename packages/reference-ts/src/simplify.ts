import { Rational } from "./rational.js";
import { type Expr, num, add, mul, pow, ZERO, ONE, isNum, isZero, isOne, compare, equal, fn, KIND_RANK } from "./ast.js";
import { toText } from "./printer.js";
import { type Rule, Trace, normalize } from "./rewrite.js";

const T = toText; // for explanations

/** Split `c * rest` where c is numeric; rest is the product of remaining factors (or the term itself). */
function coeffRest(e: Expr): [Rational, Expr] {
  if (isNum(e)) return [e.v, ONE];
  if (e.k === "mul" && isNum(e.args[0]!)) return [e.args[0]!.v, mul(...e.args.slice(1))];
  return [Rational.ONE, e];
}
/** Split `base ^ exp`; a non-power is base^1. */
function baseExp(e: Expr): [Expr, Expr] { return e.k === "pow" ? [e.base, e.exp] : [e, ONE]; }

/** Integer n-th root if exact, else null. */
function exactRoot(r: Rational, n: bigint): Rational | null {
  if (r.isNegative() || n <= 0n) return null;
  const root = (x: bigint): bigint | null => {
    if (x < 2n) return x;
    let lo = 1n, hi = x;
    while (lo < hi) { const mid = (lo + hi) / 2n; if (mid ** n < x) lo = mid + 1n; else hi = mid; }
    return lo ** n === x ? lo : null;
  };
  const a = root(r.num), b = root(r.den);
  return a !== null && b !== null ? Rational.of(a, b) : null;
}

export const flatten: Rule = {
  name: "simp.flatten", silent: true,
  apply(e) {
    if ((e.k !== "add" && e.k !== "mul") || !e.args.some((a) => a.k === e.k)) return null;
    const args = e.args.flatMap((a) => (a.k === e.k ? a.args : [a]));
    return { result: { k: e.k, args }, explanation: "associativity" };
  },
};

/** Total degree in all variables, for ordering sums the way people write them (x^3 + 3x^2 + 3x + 1). */
export function degree(e: Expr): number {
  switch (e.k) {
    case "num": return 0;
    case "var": return 1;
    case "pow": return isNum(e.exp) ? degree(e.base) * e.exp.v.toNumber() : degree(e.base);
    case "mul": return e.args.reduce((d, a) => d + degree(a), 0);
    case "add": return Math.max(...e.args.map(degree));
    case "fn": case "matrix": return 0;
  }
}

export const sortArgs: Rule = {
  name: "simp.sort", silent: true,
  apply(e) {
    if (e.k !== "add" && e.k !== "mul") return null;
    // products: numbers first (2x); sums: highest degree first, constants last (x^2 + 3x + 1), otherwise alphabetical
    const sumKey = (t: Expr) => coeffRest(t)[1];
    const cmp = e.k === "mul" ? compare : (a: Expr, b: Expr) => {
      const ra = sumKey(a), rb = sumKey(b);
      return degree(rb) - degree(ra) || KIND_RANK[rb.k] - KIND_RANK[ra.k] || compare(ra, rb) || compare(a, b);
    };
    const sorted = [...e.args].sort(cmp);
    return sorted.every((a, i) => a === e.args[i]) ? null : { result: { k: e.k, args: sorted }, explanation: "commutativity" };
  },
};

export const foldConstants: Rule = {
  name: "simp.fold-constants",
  apply(e) {
    if (e.k !== "add" && e.k !== "mul") return null;
    const nums = e.args.filter(isNum);
    if (nums.length < 2) return null;
    const folded = e.k === "add" ? nums.reduce((s, n) => s.add(n.v), Rational.ZERO) : nums.reduce((s, n) => s.mul(n.v), Rational.ONE);
    const rest = e.args.filter((a) => !isNum(a));
    const op = e.k === "add" ? "+" : "×";
    return {
      result: { k: e.k, args: [num(folded), ...rest] },
      explanation: `Arithmetic on constants: ${nums.map((n) => n.v.toString()).join(` ${op} `)} = ${folded}.`,
    };
  },
};

export const identities: Rule = {
  name: "simp.identity",
  apply(e) {
    if (e.k === "add") {
      if (e.args.length === 0) return { result: ZERO, explanation: "An empty sum is 0." };
      if (e.args.length === 1) return { result: e.args[0]!, explanation: "A sum of one term is that term." };
      if (e.args.some(isZero)) return { result: add(...e.args.filter((a) => !isZero(a))), explanation: "$a + 0 = a$: zero is the additive identity." };
    }
    if (e.k === "mul") {
      if (e.args.length === 0) return { result: ONE, explanation: "An empty product is 1." };
      if (e.args.length === 1) return { result: e.args[0]!, explanation: "A product of one factor is that factor." };
      if (e.args.some(isZero)) return { result: ZERO, explanation: "$a \\cdot 0 = 0$: zero annihilates products." };
      if (e.args.some(isOne)) return { result: mul(...e.args.filter((a) => !isOne(a))), explanation: "$a \\cdot 1 = a$: one is the multiplicative identity." };
    }
    return null;
  },
};

export const collectTerms: Rule = {
  name: "simp.collect-like-terms",
  apply(e) {
    if (e.k !== "add") return null;
    const groups = new Map<string, { rest: Expr; coeff: Rational; count: number }>();
    for (const a of e.args) {
      const [c, rest] = coeffRest(a);
      const key = T(rest);
      const g = groups.get(key);
      if (g) { g.coeff = g.coeff.add(c); g.count++; } else groups.set(key, { rest, coeff: c, count: 1 });
    }
    const merged = [...groups.values()].filter((g) => g.count > 1);
    if (merged.length === 0) return null;
    const args = [...groups.values()].map((g) => (equal(g.rest, ONE) ? num(g.coeff) : mul(num(g.coeff), g.rest)));
    const g = merged[0]!;
    return {
      result: add(...args),
      explanation: `Like terms share the same variable part, here $${toText(g.rest)}$; add their coefficients (distributive law $ax + bx = (a+b)x$) to get ${g.coeff.toString()}.`,
    };
  },
};

export const collectPowers: Rule = {
  name: "simp.collect-powers",
  apply(e) {
    if (e.k !== "mul") return null;
    const groups = new Map<string, { base: Expr; exps: Expr[] }>();
    for (const a of e.args) {
      if (isNum(a)) { groups.set(`#${a.v}`, { base: a, exps: [ONE] }); continue; }
      const [b, x] = baseExp(a);
      const key = T(b);
      const g = groups.get(key);
      if (g) g.exps.push(x); else groups.set(key, { base: b, exps: [x] });
    }
    const merged = [...groups.values()].find((g) => g.exps.length > 1);
    if (!merged) return null;
    const args = [...groups.values()].map((g) => (isNum(g.base) ? g.base : g.exps.length === 1 ? (equal(g.exps[0]!, ONE) ? g.base : pow(g.base, g.exps[0]!)) : pow(g.base, add(...g.exps))));
    return {
      result: mul(...args),
      explanation: `Same base $${T(merged.base)}$: multiplying powers adds exponents, $b^m \\cdot b^n = b^{m+n}$.`,
    };
  },
};

export const powerRules: Rule = {
  name: "simp.power",
  apply(e) {
    if (e.k !== "pow") return null;
    const { base, exp } = e;
    if (isZero(exp)) return { result: ONE, explanation: "$b^0 = 1$ (for the domain we work in, $b \\neq 0$)." };
    if (isOne(exp)) return { result: base, explanation: "$b^1 = b$." };
    if (isOne(base)) return { result: ONE, explanation: "$1^n = 1$." };
    if (isZero(base) && isNum(exp) && !exp.v.isNegative() && !exp.v.isZero()) return { result: ZERO, explanation: "$0^n = 0$ for $n > 0$." };
    if (isNum(base) && isNum(exp)) {
      if (exp.v.isInteger()) return { result: num(base.v.pow(exp.v.num)), explanation: `Evaluate the numeric power: ${base.v}^${exp.v} = ${base.v.pow(exp.v.num)}.` };
      const root = exactRoot(base.v, exp.v.den);
      if (root) return { result: pow(num(root), num(Rational.of(exp.v.num))), explanation: `${base.v} is a perfect ${exp.v.den}th power: $${base.v}^{1/${exp.v.den}} = ${root}$.` };
    }
    if (base.k === "pow" && isNum(exp) && exp.v.isInteger()) {
      return { result: pow(base.base, mul(base.exp, exp)), explanation: "$(b^m)^n = b^{mn}$ for integer $n$." };
    }
    if (base.k === "mul" && isNum(exp) && exp.v.isInteger()) {
      return { result: mul(...base.args.map((a) => pow(a, exp))), explanation: "$(ab)^n = a^n b^n$: a power of a product is the product of the powers." };
    }
    return null;
  },
};

export const functionRules: Rule = {
  name: "simp.function",
  apply(e) {
    if (e.k !== "fn" || e.args.length !== 1) return null;
    const a = e.args[0]!;
    switch (e.name) {
      case "sqrt": return { result: pow(a, num(Rational.of(1, 2))), explanation: "$\\sqrt{a} = a^{1/2}$; we work with a single power form internally." };
      case "ln":
        if (isOne(a)) return { result: ZERO, explanation: "$\\ln 1 = 0$." };
        if (a.k === "fn" && a.name === "exp") return { result: a.args[0]!, explanation: "$\\ln(e^x) = x$: ln and exp are inverses." };
        if (a.k === "pow") return { result: mul(a.exp, fn("ln", a.base)), explanation: "$\\ln(b^p) = p \\ln b$." };
        return null;
      case "exp":
        if (isZero(a)) return { result: ONE, explanation: "$e^0 = 1$." };
        if (a.k === "fn" && a.name === "ln") return { result: a.args[0]!, explanation: "$e^{\\ln x} = x$: exp and ln are inverses." };
        return null;
      case "sin": if (isZero(a)) return { result: ZERO, explanation: "$\\sin 0 = 0$." }; return null;
      case "cos": if (isZero(a)) return { result: ONE, explanation: "$\\cos 0 = 1$." }; return null;
      case "abs": if (isNum(a)) return { result: num(a.v.isNegative() ? a.v.neg() : a.v), explanation: "Absolute value of a constant." }; return null;
      default: return null;
    }
  },
};

/** Distribute multiplication over addition; used by `expand`, not by `simplify`. */
export const distribute: Rule = {
  name: "expand.distribute",
  apply(e) {
    if (e.k !== "mul") return null;
    const i = e.args.findIndex((a) => a.k === "add");
    if (i < 0) return null;
    const sum = e.args[i]! as Extract<Expr, { k: "add" }>;
    const others = e.args.filter((_, j) => j !== i);
    return {
      result: add(...sum.args.map((t) => mul(...others, t))),
      explanation: `Distributive law: $a(b + c) = ab + ac$, applied to $${T(sum)}$.`,
    };
  },
};

/** (a+b)^n for small positive integer n → repeated product (then distribute). */
export const expandPower: Rule = {
  name: "expand.power",
  apply(e) {
    if (e.k !== "pow" || e.base.k !== "add" || !isNum(e.exp) || !e.exp.v.isInteger()) return null;
    const n = e.exp.v.num;
    if (n < 2n || n > 12n) return null;
    return { result: mul(...Array.from({ length: Number(n) }, () => e.base)), explanation: `$s^{${n}}$ is $s$ multiplied by itself ${n} times; expand by repeated distribution.` };
  },
};

export const SIMPLIFY_RULES: readonly Rule[] = [flatten, identities, foldConstants, functionRules, powerRules, collectPowers, collectTerms, sortArgs];
export const EXPAND_RULES: readonly Rule[] = [expandPower, distribute, ...SIMPLIFY_RULES];

export function simplify(e: Expr, trace = new Trace(false)): Expr { return normalize(e, SIMPLIFY_RULES, trace); }
export function expand(e: Expr, trace = new Trace(false)): Expr { return normalize(e, EXPAND_RULES, trace); }
