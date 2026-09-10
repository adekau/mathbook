import { Rational } from "./rational.js";
import { type Expr, num, v, add, mul, pow, fn, matrix, neg, sub, div } from "./ast.js";

/**
 * Input language (see book/OUTLINE.md, Part II):
 *
 *   stmt   := 'let' IDENT '=' expr | expr
 *   expr   := term (('+' | '-') term)*
 *   term   := unary (('*' | '/') unary | <implicit> unary)*
 *   unary  := '-' unary | power
 *   power  := atom ('^' unary)?                       -- right-assoc; -x^2 parses as -(x^2)
 *   atom   := NUMBER | IDENT | IDENT '(' expr,* ')' | '(' expr ')' | '[' row (';' row)* ']'
 *   row    := expr (',' expr)*
 *
 * Implicit multiplication (2x, 2(x+1), x y) is allowed when the previous token ends an atom
 * and the next token begins one. `IDENT (` is a call only if IDENT is a known function.
 * The Lean model of this grammar lives in lean/MathEngine/Syntax.lean.
 */

export interface ParseError { message: string; start: number; end: number }
export class SyntaxError extends Error {
  constructor(public readonly info: ParseError) { super(info.message); }
}

export type Stmt = { kind: "let"; name: string; value: Expr } | { kind: "expr"; value: Expr };

type Tok =
  | { t: "num"; s: string; start: number; end: number }
  | { t: "id"; s: string; start: number; end: number }
  | { t: "op"; s: string; start: number; end: number }
  | { t: "eof"; s: ""; start: number; end: number };

export function lex(src: string): Tok[] {
  const toks: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9]/.test(c) || (c === "." && /[0-9]/.test(src[i + 1] ?? ""))) {
      const m = /^[0-9]*\.?[0-9]+|^[0-9]+/.exec(src.slice(i))!;
      toks.push({ t: "num", s: m[0], start: i, end: i + m[0].length }); i += m[0].length; continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      const m = /^[A-Za-z_][A-Za-z0-9_']*/.exec(src.slice(i))!;
      toks.push({ t: "id", s: m[0], start: i, end: i + m[0].length }); i += m[0].length; continue;
    }
    if ("+-*/^()[],;=".includes(c)) { toks.push({ t: "op", s: c, start: i, end: i + 1 }); i++; continue; }
    throw new SyntaxError({ message: `unexpected character '${c}'`, start: i, end: i + 1 });
  }
  toks.push({ t: "eof", s: "", start: src.length, end: src.length });
  return toks;
}

export const BUILTIN_FUNCTIONS = new Set([
  "sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs",
  // commands
  "diff", "simplify", "expand", "N", "det", "rref", "transpose", "solve", "subst",
]);

export function parse(src: string, knownFunctions: ReadonlySet<string> = new Set()): Stmt {
  const toks = lex(src);
  let p = 0;
  const peek = () => toks[p]!;
  const next = () => toks[p++]!;
  const isFn = (name: string) => BUILTIN_FUNCTIONS.has(name) || knownFunctions.has(name);
  const fail = (msg: string, tok: Tok = peek()): never => { throw new SyntaxError({ message: msg, start: tok.start, end: tok.end }); };
  const expectOp = (s: string) => { const t = next(); if (t.t !== "op" || t.s !== s) fail(`expected '${s}'`, t); };

  const startsAtom = (t: Tok) => t.t === "num" || t.t === "id" || (t.t === "op" && (t.s === "(" || t.s === "["));

  function expr(): Expr {
    let lhs = term();
    for (;;) {
      const t = peek();
      if (t.t === "op" && t.s === "+") { next(); lhs = add(lhs, term()); }
      else if (t.t === "op" && t.s === "-") { next(); lhs = sub(lhs, term()); }
      else return lhs;
    }
  }
  function term(): Expr {
    let lhs = unary();
    for (;;) {
      const t = peek();
      if (t.t === "op" && t.s === "*") { next(); lhs = mul(lhs, unary()); }
      else if (t.t === "op" && t.s === "/") { next(); lhs = div(lhs, unary()); }
      else if (startsAtom(t) && !(t.t === "num" && toks[p - 1]?.t === "num")) { lhs = mul(lhs, unary()); } // implicit
      else return lhs;
    }
  }
  function unary(): Expr {
    const t = peek();
    if (t.t === "op" && t.s === "-") { next(); return neg(unary()); }
    return power();
  }
  function power(): Expr {
    const base = atom();
    const t = peek();
    if (t.t === "op" && t.s === "^") { next(); return pow(base, unary()); }
    return base;
  }
  function atom(): Expr {
    const t = next();
    if (t.t === "num") return num(Rational.parse(t.s));
    if (t.t === "id") {
      if (peek().t === "op" && peek().s === "(" && isFn(t.s)) {
        next();
        const args: Expr[] = [];
        if (!(peek().t === "op" && peek().s === ")")) {
          args.push(expr());
          while (peek().t === "op" && peek().s === ",") { next(); args.push(expr()); }
        }
        expectOp(")");
        return fn(t.s, ...args);
      }
      if (t.s === "pi") return v("π");
      return v(t.s);
    }
    if (t.t === "op" && t.s === "(") { const e = expr(); expectOp(")"); return e; }
    if (t.t === "op" && t.s === "[") {
      const rows: Expr[][] = [];
      do {
        const row = [expr()];
        while (peek().t === "op" && peek().s === ",") { next(); row.push(expr()); }
        rows.push(row);
      } while (peek().t === "op" && peek().s === ";" && next());
      expectOp("]");
      const w = rows[0]!.length;
      if (rows.some((r) => r.length !== w)) fail("ragged matrix rows", t);
      return matrix(rows);
    }
    return fail(t.t === "eof" ? "unexpected end of input" : `unexpected '${t.s}'`, t);
  }

  let stmt: Stmt;
  if (peek().t === "id" && peek().s === "let") {
    next();
    const name = next();
    if (name.t !== "id") fail("expected a name after 'let'", name);
    expectOp("=");
    stmt = { kind: "let", name: name.s, value: expr() };
  } else {
    stmt = { kind: "expr", value: expr() };
  }
  if (peek().t !== "eof") fail(`unexpected '${peek().s}'`);
  return stmt;
}
