import type { EngineHandler, EngineCapabilities, EvaluateParams, EvaluateResult, EvaluateError, ExplainParams, ExplainResult, Methods, MethodName, Path } from "@mathbook/protocol";
import { type Expr, at, toWire, isNum, children } from "./ast.js";
import { parse, SyntaxError } from "./parser.js";
import { render } from "./printer.js";
import { type Rule, type Step, type Derivation, Trace, normalize, derivationToWire, stepToWire } from "./rewrite.js";
import { SIMPLIFY_RULES, EXPAND_RULES } from "./simplify.js";
import { diffRules } from "./diff.js";
import { matrixRules, rref } from "./linalg.js";
import { substitute, evalNumeric, floatToExpr } from "./numeric.js";

export * from "./ast.js";
export * from "./rational.js";
export * from "./parser.js";
export * from "./printer.js";
export * from "./rewrite.js";
export * from "./simplify.js";
export * from "./diff.js";
export * from "./linalg.js";
export * from "./numeric.js";

/** Notebook commands are rules too: they fire on `fn` nodes with reserved names. */
function commandRules(trace: Trace): Rule[] {
  return [
    { name: "cmd.simplify", apply: (e) => (e.k === "fn" && e.name === "simplify" && e.args.length === 1 ? { result: e.args[0]!, explanation: "Arguments are already in simplified normal form." } : null) },
    {
      name: "cmd.expand",
      apply: (e) => e.k === "fn" && e.name === "expand" && e.args.length === 1
        ? { ...trace.nested(e.args[0]!, (t) => normalize(e.args[0]!, EXPAND_RULES, t)), explanation: "Expand products and powers of sums by repeated distribution." }
        : null,
    },
    {
      name: "cmd.rref",
      apply: (e) => e.k === "fn" && e.name === "rref" && e.args.length === 1 && e.args[0]!.k === "matrix"
        ? { ...trace.nested(e.args[0]!, (t) => rref(e.args[0] as Extract<Expr, { k: "matrix" }>, t)), explanation: "Gauss–Jordan elimination to reduced row echelon form." }
        : null,
    },
    {
      name: "cmd.N",
      apply: (e) => e.k === "fn" && e.name === "N" && e.args.length === 1 && !isNum(e.args[0]!)
        ? { result: floatToExpr(evalNumeric(e.args[0]!)), explanation: "Numerical approximation in IEEE-754 double precision." }
        : null,
    },
    {
      name: "cmd.subst",
      apply: (e) => e.k === "fn" && e.name === "subst" && e.args.length === 3 && e.args[1]!.k === "var"
        ? { result: substitute(e.args[0]!, new Map([[(e.args[1] as Extract<Expr, { k: "var" }>).name, e.args[2]!]])), explanation: `Substitute $${(e.args[1] as Extract<Expr, { k: "var" }>).name} := ${render(e.args[2]!).text}$.` }
        : null,
    },
  ];
}

interface Cell { output: Expr; derivation: Derivation }
interface Session { env: Map<string, Expr>; cells: Map<string, Cell> }

export class Engine implements EngineHandler {
  private sessions = new Map<string, Session>();

  capabilities(): EngineCapabilities {
    return { engine: "reference-ts", version: "0.1.0", verified: false, features: ["simplify", "expand", "diff", "linalg", "numeric"] };
  }

  private session(id: string): Session {
    let s = this.sessions.get(id);
    if (!s) { s = { env: new Map(), cells: new Map() }; this.sessions.set(id, s); }
    return s;
  }

  evaluate(p: EvaluateParams): EvaluateResult | EvaluateError {
    const s = this.session(p.sessionId);
    try {
      const stmt = parse(p.source);
      const input = substitute(stmt.value, s.env);
      const trace = new Trace(p.showWork ?? false);
      const rules = [...commandRules(trace), ...diffRules, ...matrixRules, ...SIMPLIFY_RULES];
      const output = normalize(input, rules, trace);
      const derivation: Derivation = { input, steps: trace.steps, output };
      s.cells.set(p.cellId, { output, derivation });
      const result: EvaluateResult = { ok: true, value: toWire(output), rendered: render(output, p.paths ?? false) };
      if (p.showWork) result.derivation = derivationToWire(derivation);
      if (stmt.kind === "let") { s.env.set(stmt.name, output); result.bound = [stmt.name]; }
      return result;
    } catch (e) {
      if (e instanceof SyntaxError) return { ok: false, error: { code: "syntax", message: e.message, span: { start: e.info.start, end: e.info.end } } };
      return { ok: false, error: { code: "eval", message: e instanceof Error ? e.message : String(e) } };
    }
  }

  /**
   * Which steps produced the subterm at `path` in the cell's output? Prototype heuristic:
   * every step that fired at, above, or below that path. Rewriting *moves* subterms, so this
   * over-approximates; proper origin tracking is milestone M6 in book/TRACKING.md.
   */
  explain(p: ExplainParams): ExplainResult {
    const cell = this.session(p.sessionId).cells.get(p.cellId);
    if (!cell) throw new Error(`unknown cell ${p.cellId}`);
    const subterm = at(cell.output, p.path);
    const related = (steps: Step[]): Step[] => steps.filter((st) => isPrefix(st.path, p.path) || isPrefix(p.path, st.path));
    return { subterm: toWire(subterm), rendered: render(subterm), steps: related(cell.derivation.steps).map(stepToWire) };
  }

  async handle<M extends MethodName>(method: M, params: Methods[M]["params"]): Promise<Methods[M]["result"]> {
    switch (method) {
      case "engine.capabilities": return this.capabilities() as Methods[M]["result"];
      case "engine.evaluate": return this.evaluate(params as EvaluateParams) as Methods[M]["result"];
      case "engine.explain": return this.explain(params as ExplainParams) as Methods[M]["result"];
      case "engine.resetSession": this.sessions.delete((params as { sessionId: string }).sessionId); return { ok: true } as Methods[M]["result"];
      default: throw new Error(`unknown method ${String(method)}`);
    }
  }
}

function isPrefix(a: Path, b: Path): boolean { return a.length <= b.length && a.every((x, i) => x === b[i]); }
export { children };
