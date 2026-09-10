import { type Expr, at, replaceAt, children, size } from "./ast.js";
import { toWire } from "./ast.js";
import type { Path, Step as WireStep, Derivation as WireDerivation } from "@mathbook/protocol";

/**
 * Provenance-carrying rewriting.
 *
 * A Rule looks at one node and either rewrites it (returning the new node and *why* the
 * rewrite is valid) or declines. The engine applies rules bottom-up to a fixed point,
 * recording every firing as a Step with the whole-term before/after and the Path where it fired.
 *
 * This is the whole trick behind "show work": we never compute an answer without also
 * computing the justification. The derivation is not reconstructed after the fact — it *is*
 * the computation, viewed as data. (Book: Part III, "Rewriting as a writer monad".)
 */

export interface Rule {
  name: string;
  /** Rules marked silent still fire but leave no Step (canonical reordering, flattening). */
  silent?: boolean;
  apply(e: Expr): RuleResult | null;
}
export interface RuleResult {
  result: Expr;
  explanation: string;
  /** Steps taken inside this rewrite (e.g. the row operations behind an rref command). */
  sub?: Derivation;
}

export interface Step {
  rule: string;
  explanation: string;
  path: Path;
  before: Expr;
  after: Expr;
  sub?: Derivation;
}
export interface Derivation { input: Expr; steps: Step[]; output: Expr }

export class Trace {
  readonly steps: Step[] = [];
  constructor(readonly enabled: boolean) {}
  record(step: Step): void { if (this.enabled) this.steps.push(step); }
  /** Run `f` with a fresh trace and package its steps as a sub-derivation for a RuleResult. */
  nested(input: Expr, f: (t: Trace) => Expr): { result: Expr; sub?: Derivation } {
    const t = new Trace(this.enabled);
    const result = f(t);
    return t.steps.length > 0 ? { result, sub: { input, steps: t.steps, output: result } } : { result };
  }
}

export const MAX_STEPS = 10_000;

/**
 * Rewrite `root` to a normal form under `rules`. Strategy: innermost (children first), then
 * apply the first applicable rule at the node, then re-normalize the result (its children may
 * have changed shape, e.g. after flattening). Terminates by the step budget; the book's
 * termination chapter replaces the budget with a proof that every rule decreases a measure.
 */
export function normalize(root: Expr, rules: readonly Rule[], trace: Trace): Expr {
  let budget = MAX_STEPS;
  const rewriteAt = (cur: Expr, path: Path): Expr => {
    // 1. children first
    const node = at(cur, path);
    const cs = children(node);
    for (let i = 0; i < cs.length; i++) cur = rewriteAt(cur, [...path, i]);
    // 2. rules at this node until quiescent
    for (;;) {
      const here = at(cur, path);
      let fired = false;
      for (const r of rules) {
        const out = r.apply(here);
        if (!out) continue;
        if (--budget < 0) throw new Error(`rewriting exceeded ${MAX_STEPS} steps (non-terminating rule set?)`);
        const next = replaceAt(cur, path, out.result);
        if (!r.silent) trace.record({ rule: r.name, explanation: out.explanation, path, before: cur, after: next, ...(out.sub ? { sub: out.sub } : {}) });
        cur = next;
        fired = true;
        break;
      }
      if (!fired) return cur;
      // the new node's children may need normalizing again
      const newCs = children(at(cur, path));
      for (let i = 0; i < newCs.length; i++) cur = rewriteAt(cur, [...path, i]);
    }
  };
  return rewriteAt(root, []);
}

// --- wire conversion of derivations -----------------------------------------
export function stepToWire(s: Step): WireStep {
  const w: WireStep = { rule: s.rule, explanation: s.explanation, path: s.path, before: toWire(s.before), after: toWire(s.after) };
  if (s.sub) w.sub = derivationToWire(s.sub);
  return w;
}
export function derivationToWire(d: Derivation): WireDerivation {
  return { input: toWire(d.input), steps: d.steps.map(stepToWire), output: toWire(d.output) };
}

export { size };
