// Dependency-free symbolic engine for the math notebook.
// AST: {t:'num',v} {t:'sym',name} {t:'add',args} {t:'mul',args} {t:'div',num,den}
//      {t:'pow',base,exp} {t:'neg',a} {t:'fn',name,args} {t:'deriv',a,v} {t:'int',a,v}
//      {t:'matrix',rows} {t:'eq',l,r} {t:'text',s}

const FNS = ['sin','cos','tan','sec','csc','cot','exp','ln','log','sqrt','abs',
  'asin','acos','atan','sinh','cosh','tanh'];
const GREEK = { pi:'π', lambda:'λ', theta:'θ', alpha:'α', beta:'β', mu:'μ' };

/* ---------------- tokenizer ---------------- */
function lex(s) {
  const out = []; let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(s[i + 1] || ''))) {
      let j = i; while (j < s.length && /[0-9.]/.test(s[j])) j++;
      out.push({ k: 'num', v: parseFloat(s.slice(i, j)) }); i = j; continue;
    }
    if (/[A-Za-z]/.test(c)) {
      let j = i; while (j < s.length && /[A-Za-z_]/.test(s[j])) j++;
      out.push({ k: 'id', v: s.slice(i, j) }); i = j; continue;
    }
    if ('+-*/^(),[]='.includes(c)) { out.push({ k: c }); i++; continue; }
    throw new Error('Unexpected character "' + c + '"');
  }
  return out;
}

/* ---------------- parser ---------------- */
function parse(src) {
  const ts = lex(src); let p = 0;
  const peek = () => ts[p];
  const eat = (k) => { if (ts[p] && ts[p].k === k) { p++; return true; } return false; };
  const expect = (k) => { if (!eat(k)) throw new Error('Expected "' + k + '"'); };

  function primary() {
    const t = peek();
    if (!t) throw new Error('Unexpected end of expression');
    if (t.k === 'num') { p++; return { t: 'num', v: t.v }; }
    if (t.k === 'id') {
      p++;
      const name = t.v;
      if (FNS.includes(name.toLowerCase()) && peek() && peek().k === '(') {
        p++; const args = [expr(0)];
        while (eat(',')) args.push(expr(0));
        expect(')');
        return { t: 'fn', name: name.toLowerCase(), args };
      }
      return { t: 'sym', name: GREEK[name] || name };
    }
    if (t.k === '(') { p++; const e = expr(0); expect(')'); return { t: 'group', a: e }; }
    if (t.k === '[') {
      p++;
      const items = [];
      if (!eat(']')) {
        items.push(expr(0));
        while (eat(',')) items.push(expr(0));
        expect(']');
      }
      return { t: 'row', items };
    }
    if (t.k === '-') { p++; return { t: 'neg', a: unary() }; }
    throw new Error('Unexpected token');
  }

  function unary() {
    if (eat('-')) return { t: 'neg', a: unary() };
    if (eat('+')) return unary();
    return postfix();
  }
  function postfix() {
    let base = primary();
    if (eat('^')) return { t: 'pow', base, exp: unary() };
    return base;
  }
  function startsPrimary() {
    const t = peek();
    if (!t) return false;
    return t.k === 'num' || t.k === 'id' || t.k === '(';
  }
  function expr(min) {
    let left = unary();
    for (;;) {
      const t = peek();
      if (t && (t.k === '+' || t.k === '-') && min <= 1) {
        p++; const right = expr(2);
        left = { t: 'add', args: [left, t.k === '-' ? { t: 'neg', a: right } : right] };
        continue;
      }
      if (t && (t.k === '*' || t.k === '/') && min <= 2) {
        p++; const right = expr(3);
        left = t.k === '*' ? { t: 'mul', args: [left, right] } : { t: 'div', num: left, den: right };
        continue;
      }
      if (min <= 2 && startsPrimary()) { // implicit multiplication: 2x, x y, 3sin(x)
        const right = expr(3);
        left = { t: 'mul', args: [left, right] };
        continue;
      }
      break;
    }
    return left;
  }

  let root = expr(0);
  if (p < ts.length) throw new Error('Could not parse the whole expression');
  return normalizeRows(strip(root));
}

function strip(n) {
  if (!n || typeof n !== 'object') return n;
  if (n.t === 'group') return strip(n.a);
  const o = { ...n };
  if (o.args) o.args = o.args.map(strip);
  if (o.items) o.items = o.items.map(strip);
  ['a', 'num', 'den', 'base', 'exp', 'l', 'r'].forEach(k => { if (o[k]) o[k] = strip(o[k]); });
  return o;
}
// [[1,2],[3,4]] -> matrix ; [1,2,3] -> single-row matrix (vector)
function normalizeRows(n) {
  if (!n || typeof n !== 'object') return n;
  if (n.t === 'row') {
    if (n.items.length && n.items.every(x => x.t === 'row'))
      return { t: 'matrix', rows: n.items.map(r => r.items.map(normalizeRows)) };
    return { t: 'matrix', rows: n.items.map(x => [normalizeRows(x)]) };
  }
  const o = { ...n };
  if (o.args) o.args = o.args.map(normalizeRows);
  ['a', 'num', 'den', 'base', 'exp'].forEach(k => { if (o[k]) o[k] = normalizeRows(o[k]); });
  return o;
}

/* ---------------- helpers ---------------- */
const num = v => ({ t: 'num', v });
const sym = name => ({ t: 'sym', name });
const add = (...args) => ({ t: 'add', args });
const mul = (...args) => ({ t: 'mul', args });
const div = (n, d) => ({ t: 'div', num: n, den: d });
const pow = (b, e) => ({ t: 'pow', base: b, exp: e });
const neg = a => ({ t: 'neg', a });
const fn = (name, ...args) => ({ t: 'fn', name, args });

export function hasVar(n, v) {
  if (!n || typeof n !== 'object') return false;
  if (n.t === 'sym') return n.name === v;
  return kids(n).some(k => hasVar(k, v));
}
function kids(n) {
  if (!n || typeof n !== 'object') return [];
  const out = [];
  if (n.args) out.push(...n.args);
  if (n.rows) n.rows.forEach(r => out.push(...r));
  ['a', 'num', 'den', 'base', 'exp', 'l', 'r'].forEach(k => { if (n[k]) out.push(n[k]); });
  return out;
}
export function evalAt(n, env) {
  switch (n.t) {
    case 'num': return n.v;
    case 'sym':
      if (n.name === 'π') return Math.PI;
      if (n.name === 'e') return Math.E;
      return env[n.name] !== undefined ? env[n.name] : NaN;
    case 'add': return n.args.reduce((s, a) => s + evalAt(a, env), 0);
    case 'mul': return n.args.reduce((s, a) => s * evalAt(a, env), 1);
    case 'div': return evalAt(n.num, env) / evalAt(n.den, env);
    case 'pow': return Math.pow(evalAt(n.base, env), evalAt(n.exp, env));
    case 'neg': return -evalAt(n.a, env);
    case 'fn': {
      const x = evalAt(n.args[0], env);
      const m = { sin: Math.sin, cos: Math.cos, tan: Math.tan, exp: Math.exp,
        ln: Math.log, log: Math.log, sqrt: Math.sqrt, abs: Math.abs,
        asin: Math.asin, acos: Math.acos, atan: Math.atan,
        sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
        sec: t => 1 / Math.cos(t), csc: t => 1 / Math.sin(t), cot: t => 1 / Math.tan(t) };
      return m[n.name] ? m[n.name](x) : NaN;
    }
    default: return NaN;
  }
}

/* ---------------- simplifier ---------------- */
function flat(n, t) {
  return n.t === t ? n.args.flatMap(a => flat(simp(a), t)) : [n];
}
export function simp(n) {
  if (!n || typeof n !== 'object') return n;
  switch (n.t) {
    case 'neg': {
      const a = simp(n.a);
      if (a.t === 'num') return num(-a.v);
      if (a.t === 'neg') return a.a;
      return neg(a);
    }
    case 'add': {
      let parts = n.args.flatMap(a => flat(simp(a), 'add'));
      let c = 0; const terms = [];
      for (const p of parts) {
        if (p.t === 'num') { c += p.v; continue; }
        if (p.t === 'neg' && p.a.t === 'num') { c -= p.a.v; continue; }
        const [coef, core] = split(p);
        const hit = terms.find(t => same(t.core, core));
        if (hit) hit.coef += coef; else terms.push({ coef, core });
      }
      const out = [];
      for (const t of terms) {
        if (Math.abs(t.coef) < 1e-12) continue;
        if (t.coef === 1) out.push(t.core);
        else if (t.coef === -1) out.push(neg(t.core));
        else if (t.coef < 0) out.push(neg(simp(mul(num(-t.coef), t.core))));
        else out.push(simp(mul(num(t.coef), t.core)));
      }
      out.sort((a, b) => deg(b) - deg(a));
      if (Math.abs(c) > 1e-12) out.push(c < 0 ? neg(num(round(-c))) : num(round(c)));
      if (!out.length) return num(0);
      if (out.length === 1) return out[0];
      return add(...out);
    }
    case 'mul': {
      const parts = n.args.flatMap(a => flat(simp(a), 'mul'));
      const expanded = [];
      let c = 1, cd = 1;
      const invert = (x) => {
        if (x.t === 'num') { cd *= x.v; return null; }
        if (x.t === 'neg') { cd *= -1; return invert(x.a); }
        if (x.t === 'pow') return pow(x.base, simp(neg(x.exp)));
        return pow(x, num(-1));
      };
      const push = (p) => {
        if (p.t === 'num') { c *= p.v; return; }
        if (p.t === 'neg') { c *= -1; push(p.a); return; }
        if (p.t === 'div') { push(p.num); const inv = invert(p.den); if (inv) expanded.push(inv); return; }
        expanded.push(p);
      };
      parts.forEach(push);
      if (Math.abs(c) < 1e-12) return num(0);
      const merged = [];
      expanded.forEach(p => {
        const b = p.t === 'pow' ? p.base : p;
        const e = p.t === 'pow' ? p.exp : num(1);
        const hit = merged.find(m => same(m.b, b) && m.e.t === 'num' && e.t === 'num');
        if (hit) hit.e = num(hit.e.v + e.v); else merged.push({ b, e });
      });
      const numF = [], denF = [];
      merged.forEach(({ b, e }) => {
        if (e.t !== 'num') { numF.push(pow(b, e)); return; }
        if (Math.abs(e.v) < 1e-12) return;
        if (e.v < 0) denF.push(e.v === -1 ? b : pow(b, num(-e.v)));
        else numF.push(e.v === 1 ? b : pow(b, num(e.v)));
      });
      let sign = 1;
      c = round(c); cd = round(cd);
      if (c < 0) { sign = -sign; c = -c; }
      if (cd < 0) { sign = -sign; cd = -cd; }
      if (Number.isInteger(c) && Number.isInteger(cd) && cd !== 0) {
        const g = (a, b) => b ? g(b, a % b) : a;
        const k = g(c, cd) || 1; c /= k; cd /= k;
      }
      const coefTimes = (k, list) => !list.length ? num(k)
        : k === 1 ? (list.length === 1 ? list[0] : mul(...list))
        : mul(num(k), ...list);
      let outNode = (cd === 1 && !denF.length)
        ? coefTimes(c, numF)
        : div(coefTimes(c, numF), coefTimes(cd, denF));
      if (outNode.t === 'div' && outNode.den.t === 'num' && outNode.den.v === 1) outNode = outNode.num;
      return sign < 0 ? neg(outNode) : outNode;
    }
    case 'div': {
      const a = simp(n.num), b = simp(n.den);
      if (b.t === 'num' && b.v === 1) return a;
      if (a.t === 'num' && b.t === 'num' && Number.isInteger(a.v / b.v)) return num(a.v / b.v);
      if (same(a, b)) return num(1);
      return div(a, b);
    }
    case 'pow': {
      const b = simp(n.base), e = simp(n.exp);
      if (e.t === 'num' && e.v === 1) return b;
      if (e.t === 'num' && e.v === 0) return num(1);
      if (b.t === 'num' && e.t === 'num' && Number.isInteger(e.v) && Math.abs(e.v) < 6)
        return num(round(Math.pow(b.v, e.v)));
      if (b.t === 'pow') return simp(pow(b.base, simp(mul(b.exp, e))));
      return pow(b, e);
    }
    case 'fn': return { ...n, args: n.args.map(simp) };
    case 'deriv': return { ...n, a: simp(n.a) };
    case 'int': return { ...n, a: simp(n.a) };
    case 'matrix': return { ...n, rows: n.rows.map(r => r.map(simp)) };
    default: return n;
  }
}
function split(p) { // numeric coefficient × core
  if (p.t === 'neg') { const [c, k] = split(p.a); return [-c, k]; }
  if (p.t === 'mul') {
    let c = 1; const rest = [];
    for (const a of p.args) { if (a.t === 'num') c *= a.v; else rest.push(a); }
    return [c, rest.length === 1 ? rest[0] : mul(...rest)];
  }
  return [1, p];
}
const round = v => Math.abs(v - Math.round(v)) < 1e-10 ? Math.round(v) : parseFloat(v.toFixed(6));
function deg(n) {
  if (!n || typeof n !== 'object') return 0;
  switch (n.t) {
    case 'num': return 0;
    case 'sym': return 1;
    case 'neg': return deg(n.a);
    case 'mul': return n.args.reduce((s, a) => s + deg(a), 0);
    case 'div': return deg(n.num) - deg(n.den);
    case 'pow': return n.exp.t === 'num' ? deg(n.base) * n.exp.v : 2;
    case 'add': return Math.max(...n.args.map(deg));
    default: return 1;
  }
}
export function same(a, b) { return key(a) === key(b); }
function key(n) {
  if (!n || typeof n !== 'object') return String(n);
  switch (n.t) {
    case 'num': return 'n' + round(n.v);
    case 'sym': return 's' + n.name;
    case 'add': case 'mul': return n.t + '(' + n.args.map(key).sort().join(',') + ')';
    case 'div': return 'd(' + key(n.num) + ',' + key(n.den) + ')';
    case 'pow': return 'p(' + key(n.base) + ',' + key(n.exp) + ')';
    case 'neg': return 'm(' + key(n.a) + ')';
    case 'fn': return 'f' + n.name + '(' + n.args.map(key).join(',') + ')';
    default: return n.t;
  }
}

/* ---------------- differentiation, one rule at a time ---------------- */
const DERIV_TABLE = {
  sin: u => fn('cos', u), cos: u => neg(fn('sin', u)),
  tan: u => pow(fn('sec', u), num(2)), exp: u => fn('exp', u),
  ln: u => div(num(1), u), log: u => div(num(1), u),
  sqrt: u => div(num(1), mul(num(2), fn('sqrt', u))),
  asin: u => div(num(1), fn('sqrt', add(num(1), neg(pow(u, num(2)))))),
  atan: u => div(num(1), add(num(1), pow(u, num(2)))),
  sinh: u => fn('cosh', u), cosh: u => fn('sinh', u),
};
function diffOnce(n, v) { // returns {node, rule, note}
  const a = n.a;
  switch (a.t) {
    case 'num': return { node: num(0), rule: 'Constant rule', note: 'The derivative of a constant is zero.' };
    case 'sym':
      return a.name === v
        ? { node: num(1), rule: 'Identity rule', note: 'd/d' + v + ' of ' + v + ' is 1.' }
        : { node: num(0), rule: 'Constant rule', note: a.name + ' does not depend on ' + v + ', so it is treated as a constant.' };
    case 'neg': return { node: neg({ t: 'deriv', a: a.a, v }), rule: 'Constant multiple rule', note: 'A factor of −1 passes through the derivative.' };
    case 'add': return { node: add(...a.args.map(x => ({ t: 'deriv', a: x, v }))), rule: 'Sum rule', note: 'Differentiate each term separately.' };
    case 'mul': {
      const consts = a.args.filter(x => !hasVar(x, v));
      const vars = a.args.filter(x => hasVar(x, v));
      if (consts.length && vars.length)
        return { node: mul(...consts, { t: 'deriv', a: vars.length === 1 ? vars[0] : mul(...vars), v }),
          rule: 'Constant multiple rule', note: 'Constant factors move outside the derivative.' };
      const f = a.args[0], g = a.args.length === 2 ? a.args[1] : mul(...a.args.slice(1));
      return { node: add(mul({ t: 'deriv', a: f, v }, g), mul(f, { t: 'deriv', a: g, v })),
        rule: 'Product rule', note: '(f·g)′ = f′g + f g′' };
    }
    case 'div': {
      if (!hasVar(a.den, v))
        return { node: div({ t: 'deriv', a: a.num, v }, a.den), rule: 'Constant multiple rule', note: 'The denominator is constant in ' + v + '.' };
      return { node: div(add(mul({ t: 'deriv', a: a.num, v }, a.den), neg(mul(a.num, { t: 'deriv', a: a.den, v }))), pow(a.den, num(2))),
        rule: 'Quotient rule', note: '(f/g)′ = (f′g − f g′)/g²' };
    }
    case 'pow': {
      if (!hasVar(a.exp, v)) {
        const e = a.exp;
        const outer = mul(e, pow(a.base, simp(add(e, num(-1)))));
        if (a.base.t === 'sym' && a.base.name === v)
          return { node: outer, rule: 'Power rule', note: 'd/d' + v + ' of ' + v + '^n = n·' + v + '^(n−1)' };
        return { node: mul(outer, { t: 'deriv', a: a.base, v }), rule: 'Power rule with chain rule', note: 'Differentiate the outer power, then multiply by the derivative of the inside.' };
      }
      if (!hasVar(a.base, v))
        return { node: mul(a, fn('ln', a.base), { t: 'deriv', a: a.exp, v }), rule: 'Exponential rule', note: 'd/d' + v + ' of a^u = a^u · ln a · u′' };
      return { node: { t: 'deriv', a: fn('exp', mul(a.exp, fn('ln', a.base))), v }, rule: 'Rewrite as exp/ln', note: 'Both base and exponent vary, so rewrite f^g = e^{g ln f}.' };
    }
    case 'fn': {
      const d = DERIV_TABLE[a.name];
      if (!d) return { node: num(NaN), rule: 'Not in rule set', note: 'No derivative rule is defined for ' + a.name + '.' };
      const u = a.args[0];
      const outer = d(u);
      if (u.t === 'sym' && u.name === v)
        return { node: outer, rule: 'Derivative of ' + a.name, note: 'Read directly from the table of standard derivatives.' };
      return { node: mul(outer, { t: 'deriv', a: u, v }), rule: 'Chain rule', note: 'Differentiate the outer function at the inner one, then multiply by the inner derivative.' };
    }
    default: return { node: num(NaN), rule: 'Not supported', note: '' };
  }
}

/* ---------------- integration, one rule at a time ---------------- */
function integOnce(n, v) {
  const a = n.a;
  const V = sym(v);
  if (!hasVar(a, v)) return { node: mul(a, V), rule: 'Constant rule', note: '∫ c d' + v + ' = c·' + v };
  switch (a.t) {
    case 'sym': return { node: div(pow(V, num(2)), num(2)), rule: 'Power rule', note: '∫ ' + v + ' d' + v + ' = ' + v + '²/2' };
    case 'neg': return { node: neg({ t: 'int', a: a.a, v }), rule: 'Linearity', note: 'A factor of −1 passes through the integral.' };
    case 'add': return { node: add(...a.args.map(x => ({ t: 'int', a: x, v }))), rule: 'Linearity (sum rule)', note: 'Integrate each term separately.' };
    case 'mul': {
      const consts = a.args.filter(x => !hasVar(x, v));
      const vars = a.args.filter(x => hasVar(x, v));
      if (consts.length && vars.length)
        return { node: mul(...consts, { t: 'int', a: vars.length === 1 ? vars[0] : mul(...vars), v }),
          rule: 'Constant multiple rule', note: 'Constant factors move outside the integral.' };
      const parts = byParts(a, v);
      if (parts) return parts;
      break;
    }
    case 'div': {
      if (!hasVar(a.den, v))
        return { node: div({ t: 'int', a: a.num, v }, a.den), rule: 'Constant multiple rule', note: 'The denominator is constant in ' + v + '.' };
      if (same(a.den, V) && !hasVar(a.num, v))
        return { node: mul(a.num, fn('ln', fn('abs', V))), rule: 'Reciprocal rule', note: '∫ d' + v + '/' + v + ' = ln|' + v + '|' };
      if (a.num.t === 'num' && a.den.t === 'add' && a.den.args.length === 2) {
        const [p, q] = a.den.args;
        if (p.t === 'num' && p.v === 1 && q.t === 'pow' && same(q.base, V) && q.exp.t === 'num' && q.exp.v === 2)
          return { node: mul(a.num, fn('atan', V)), rule: 'Standard form (arctangent)', note: '∫ d' + v + '/(1+' + v + '²) = arctan ' + v };
      }
      if (a.den.t === 'pow' && same(a.den.base, V))
        return { node: { t: 'int', a: simp(mul(a.num, pow(V, neg(a.den.exp)))), v }, rule: 'Rewrite as a power', note: '1/' + v + '^n = ' + v + '^(−n)' };
      break;
    }
    case 'pow': {
      if (same(a.base, V) && !hasVar(a.exp, v)) {
        if (a.exp.t === 'num' && a.exp.v === -1)
          return { node: fn('ln', fn('abs', V)), rule: 'Reciprocal rule', note: 'The power rule fails at n = −1; the antiderivative is ln|' + v + '|.' };
        const e1 = simp(add(a.exp, num(1)));
        return { node: div(pow(V, e1), e1), rule: 'Power rule', note: '∫ ' + v + '^n d' + v + ' = ' + v + '^(n+1)/(n+1), n ≠ −1' };
      }
      break;
    }
    case 'fn': {
      const u = a.args[0];
      const lin = linearIn(u, v); // {k, b} for u = k·v + b
      if (!lin) break;
      const T = { sin: x => neg(fn('cos', x)), cos: x => fn('sin', x), exp: x => fn('exp', x),
        sinh: x => fn('cosh', x), cosh: x => fn('sinh', x) }[a.name];
      if (!T) break;
      const anti = T(u);
      if (lin.k === 1) return { node: anti, rule: 'Standard antiderivative', note: 'Read directly from the table of standard integrals.' };
      return { node: div(anti, num(lin.k)), rule: 'Substitution u = ' + fmt(u),
        note: 'With u = ' + fmt(u) + ', du = ' + lin.k + ' d' + v + ', so the integral picks up a factor 1/' + lin.k + '.' };
    }
  }
  return { node: { t: 'text', s: 'no closed form in this rule set' }, rule: 'Outside the rule set',
    note: 'This integral needs a technique beyond the rules loaded here (partial fractions, trig substitution, or a special function).' };
}
function byParts(a, v) {
  const V = sym(v);
  const isX = x => same(x, V);
  const factors = a.args;
  if (factors.length !== 2) return null;
  for (const [u, dv] of [[factors[0], factors[1]], [factors[1], factors[0]]]) {
    const okU = isX(u) || (u.t === 'pow' && isX(u.base) && u.exp.t === 'num' && u.exp.v > 0);
    const okDv = dv.t === 'fn' && ['sin', 'cos', 'exp'].includes(dv.name) && linearIn(dv.args[0], v);
    if (okU && okDv) {
      const anti = integOnce({ t: 'int', a: dv, v }, v).node;
      const du = simp(diffOnce({ t: 'deriv', a: u, v }, v).node);
      return { node: add(mul(u, anti), neg({ t: 'int', a: simp(mul(anti, du)), v })),
        rule: 'Integration by parts', note: 'With u = ' + fmt(u) + ' and dv = ' + fmt(dv) + ' d' + v + ': ∫u dv = uv − ∫v du.' };
    }
    if (okU && dv.t === 'fn' && dv.name === 'ln' && isX(dv.args[0]))
      return { node: add(mul(dv, div(pow(V, num(2)), num(2))), neg({ t: 'int', a: div(V, num(2)), v })),
        rule: 'Integration by parts', note: 'With u = ln ' + v + ' and dv = ' + v + ' d' + v + '.' };
  }
  return null;
}
function linearIn(u, v) {
  if (u.t === 'sym' && u.name === v) return { k: 1, b: 0 };
  if (u.t === 'mul' && u.args.length === 2) {
    const [p, q] = u.args;
    if (p.t === 'num' && q.t === 'sym' && q.name === v) return { k: p.v, b: 0 };
    if (q.t === 'num' && p.t === 'sym' && p.name === v) return { k: q.v, b: 0 };
  }
  return null;
}

/* ---------------- step runner ---------------- */
function findPending(n, path = []) {
  if (!n || typeof n !== 'object') return null;
  if (n.t === 'deriv' || n.t === 'int') return { node: n, path };
  const slots = [];
  if (n.args) n.args.forEach((c, i) => slots.push(['args.' + i, c]));
  ['a', 'num', 'den', 'base', 'exp'].forEach(k => { if (n[k]) slots.push([k, n[k]]); });
  for (const [k, c] of slots) { const hit = findPending(c, path.concat(k)); if (hit) return hit; }
  return null;
}
function replaceAt(root, path, val) {
  if (!path.length) return val;
  const [head, ...rest] = path;
  const o = { ...root };
  if (head.startsWith('args.')) {
    const i = +head.slice(5);
    o.args = root.args.map((c, j) => j === i ? replaceAt(c, rest, val) : c);
  } else o[head] = replaceAt(root[head], rest, val);
  return o;
}
function runSteps(root, kind) {
  const steps = [];
  let cur = root, guard = 0;
  while (guard++ < 60) {
    const pend = findPending(cur);
    if (!pend) break;
    const r = kind === 'int' ? integOnce(pend.node, pend.node.v) : diffOnce(pend.node, pend.node.v);
    cur = replaceAt(cur, pend.path, r.node);
    steps.push({ expr: cur, rule: r.rule, note: r.note });
  }
  const final = simp(cur);
  if (key(final) !== key(cur))
    steps.push({ expr: final, rule: 'Simplify', note: 'Collect like terms and fold constants.' });
  return { steps, result: final };
}

/* ---------------- linear algebra ---------------- */
function toNums(m) {
  return m.rows.map(r => r.map(c => evalAt(c, {})));
}
function fmtNum(x) {
  const M = s => s.replace('-', '−');
  if (!isFinite(x)) return '—';
  const r = Math.round(x);
  if (Math.abs(x - r) < 1e-9) return M(String(r));
  for (let d = 2; d <= 12; d++) {
    const n = Math.round(x * d);
    if (Math.abs(x - n / d) < 1e-9) return M(n + '/' + d);
  }
  return M(x.toFixed(4).replace(/0+$/, '').replace(/\.$/, ''));
}
function matNode(a) {
  return { t: 'matrix', rows: a.map(r => r.map(x => ({ t: 'text', s: fmtNum(x) }))) };
}
function rrefSteps(m) {
  const a = toNums(m).map(r => r.slice());
  const rows = a.length, cols = a[0].length;
  const steps = [];
  let lead = 0, rank = 0;
  for (let r = 0; r < rows && lead < cols; lead++) {
    let piv = -1, best = 1e-9;
    for (let i = r; i < rows; i++) if (Math.abs(a[i][lead]) > best) { best = Math.abs(a[i][lead]); piv = i; }
    if (piv < 0) { steps.push({ expr: matNode(a), rule: 'Column ' + (lead + 1) + ' has no pivot', note: 'Every entry at or below row ' + (r + 1) + ' in this column is zero, so this column is free. Move to the next column.' }); continue; }
    if (piv !== r) { const t = a[piv]; a[piv] = a[r]; a[r] = t;
      steps.push({ expr: matNode(a), rule: 'R' + (r + 1) + ' ↔ R' + (piv + 1), note: 'Swap to bring the largest available entry into the pivot position.' }); }
    const pv = a[r][lead];
    if (Math.abs(pv - 1) > 1e-12) {
      a[r] = a[r].map(x => x / pv);
      steps.push({ expr: matNode(a), rule: 'R' + (r + 1) + ' ← ' + fmtNum(1 / pv) + '·R' + (r + 1), note: 'Scale the pivot row so the pivot is 1.' });
    }
    for (let i = 0; i < rows; i++) {
      if (i === r) continue;
      const f = a[i][lead];
      if (Math.abs(f) < 1e-12) continue;
      a[i] = a[i].map((x, j) => x - f * a[r][j]);
      steps.push({ expr: matNode(a), rule: 'R' + (i + 1) + ' ← R' + (i + 1) + ' − (' + fmtNum(f) + ')·R' + (r + 1),
        note: 'Clear the entry above/below the pivot in column ' + (lead + 1) + '.' });
    }
    r++; rank++;
  }
  return { steps, result: matNode(a), rank, cols };
}
function det(a) {
  const n = a.length; const m = a.map(r => r.slice());
  let d = 1;
  for (let i = 0; i < n; i++) {
    let piv = i;
    for (let k = i; k < n; k++) if (Math.abs(m[k][i]) > Math.abs(m[piv][i])) piv = k;
    if (Math.abs(m[piv][i]) < 1e-12) return 0;
    if (piv !== i) { const t = m[piv]; m[piv] = m[i]; m[i] = t; d = -d; }
    d *= m[i][i];
    for (let k = i + 1; k < n; k++) { const f = m[k][i] / m[i][i]; for (let j = i; j < n; j++) m[k][j] -= f * m[i][j]; }
  }
  return d;
}
function polyRoots(coeffs) { // monic, descending, degree 2 or 3
  const n = coeffs.length - 1;
  if (n === 2) {
    const [, b, c] = coeffs, disc = b * b - 4 * c;
    if (disc >= 0) { const s = Math.sqrt(disc); return [(-b + s) / 2, (-b - s) / 2]; }
    return null;
  }
  // Durand-Kerner-ish: sample + Newton on real roots
  const f = x => coeffs.reduce((s, c) => s * x + c, 0);
  const fp = x => { const d = coeffs.slice(0, -1).map((c, i) => c * (n - i)); return d.reduce((s, c) => s * x + c, 0); };
  const roots = [];
  for (let x0 = -12; x0 <= 12; x0 += 0.05) {
    let x = x0;
    for (let i = 0; i < 60; i++) { const d = fp(x); if (!d) break; const nx = x - f(x) / d; if (!isFinite(nx)) break; if (Math.abs(nx - x) < 1e-12) { x = nx; break; } x = nx; }
    if (isFinite(x) && Math.abs(f(x)) < 1e-7 && !roots.some(r => Math.abs(r - x) < 1e-6)) roots.push(x);
  }
  return roots.length ? roots.sort((a, b) => b - a) : null;
}
function nullVector(a, lam) { // solve (A - λI)x = 0 for one vector
  const n = a.length;
  const m = a.map((r, i) => r.map((x, j) => x - (i === j ? lam : 0)));
  const piv = [];
  let row = 0;
  for (let col = 0; col < n && row < n; col++) {
    let p = -1, best = 1e-7;
    for (let i = row; i < n; i++) if (Math.abs(m[i][col]) > best) { best = Math.abs(m[i][col]); p = i; }
    if (p < 0) continue;
    const t = m[p]; m[p] = m[row]; m[row] = t;
    const pv = m[row][col];
    m[row] = m[row].map(x => x / pv);
    for (let i = 0; i < n; i++) if (i !== row && Math.abs(m[i][col]) > 1e-12) {
      const f = m[i][col]; m[i] = m[i].map((x, j) => x - f * m[row][j]);
    }
    piv.push(col); row++;
  }
  const free = [];
  for (let c = 0; c < n; c++) if (!piv.includes(c)) free.push(c);
  if (!free.length) return null;
  const x = new Array(n).fill(0);
  x[free[0]] = 1;
  piv.forEach((c, i) => { x[c] = -m[i][free[0]]; });
  const mx = Math.max(...x.map(Math.abs));
  return x.map(v => Math.abs(v / mx) < 1e-12 ? 0 : v / mx);
}
function eigSteps(m) {
  const a = toNums(m); const n = a.length;
  if (n !== a[0].length) throw new Error('Eigenvalues need a square matrix');
  if (n > 3) throw new Error('This build handles 2×2 and 3×3 matrices');
  const L = sym('λ');
  const steps = [];
  const shifted = { t: 'matrix', rows: a.map((r, i) => r.map((x, j) =>
    i === j ? (x === 0 ? neg(L) : { t: 'text', s: fmtNum(x) + ' − λ' }) : { t: 'text', s: fmtNum(x) })) };
  steps.push({ expr: { t: 'eq', l: { t: 'text', s: 'A − λI' }, r: shifted }, rule: 'Shift by λI',
    note: 'Eigenvalues are the λ for which A − λI is singular.' });
  const tr = a.reduce((s, r, i) => s + r[i], 0);
  const dt = det(a);
  let coeffs, polyNode;
  if (n === 2) {
    coeffs = [1, -tr, dt];
    polyNode = add(pow(L, num(2)), mul(num(-tr), L), num(round(dt)));
  } else {
    let m2 = 0;
    for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++)
      m2 += a[i][i] * a[j][j] - a[i][j] * a[j][i];
    coeffs = [1, -tr, m2, -dt];
    polyNode = add(pow(L, num(3)), mul(num(-tr), pow(L, num(2))), mul(num(round(m2)), L), num(round(-dt)));
  }
  steps.push({ expr: { t: 'eq', l: { t: 'text', s: 'det(A − λI)' }, r: simp(polyNode) }, rule: 'Characteristic polynomial',
    note: n === 2 ? 'For a 2×2 matrix this is λ² − (trace)λ + det, with trace ' + fmtNum(tr) + ' and det ' + fmtNum(dt) + '.'
      : 'For a 3×3 matrix: λ³ − (trace)λ² + (sum of principal 2×2 minors)λ − det.' });
  const roots = polyRoots(coeffs);
  if (!roots) return { steps, result: { t: 'text', s: 'complex eigenvalues — outside this build' }, eig: null };
  steps.push({ expr: { t: 'text', s: 'λ = ' + roots.map(fmtNum).join(',  ') }, rule: 'Solve for the roots',
    note: 'The roots of the characteristic polynomial are the eigenvalues.' });
  const vecs = roots.map(l => nullVector(a, l));
  const pairs = roots.map((l, i) => ({ lam: l, vec: vecs[i] }));
  pairs.forEach(p => {
    if (!p.vec) return;
    steps.push({ expr: { t: 'eq', l: { t: 'text', s: 'λ = ' + fmtNum(p.lam) }, r: matNode(p.vec.map(x => [x])) },
      rule: 'Null space of A − λI', note: 'Row reduce A − ' + fmtNum(p.lam) + 'I and read off a basis vector for its null space.' });
  });
  return { steps, result: { t: 'matrix', rows: pairs.map(p => [{ t: 'text', s: 'λ = ' + fmtNum(p.lam) },
    { t: 'text', s: '[' + (p.vec ? p.vec.map(fmtNum).join(', ') : '—') + ']' }]) }, eig: pairs };
}

/* ---------------- plain-text formatter (for notes) ---------------- */
export function fmt(n) {
  if (!n || typeof n !== 'object') return '';
  switch (n.t) {
    case 'num': return fmtNum(n.v);
    case 'sym': return n.name;
    case 'text': return n.s;
    case 'add': return n.args.map((a, i) => (i && a.t !== 'neg' ? ' + ' : i ? ' ' : '') + fmt(a)).join('');
    case 'neg': return (n.a.t === 'add' ? '−(' + fmt(n.a) + ')' : '−' + fmt(n.a));
    case 'mul': return n.args.map(a => a.t === 'add' ? '(' + fmt(a) + ')' : fmt(a)).join('·');
    case 'div': return fmt(n.num) + '/' + (n.den.t === 'add' || n.den.t === 'mul' ? '(' + fmt(n.den) + ')' : fmt(n.den));
    case 'pow': return (n.base.t === 'sym' || n.base.t === 'num' ? fmt(n.base) : '(' + fmt(n.base) + ')') + '^' + fmt(n.exp);
    case 'fn': return n.name + '(' + n.args.map(fmt).join(', ') + ')';
    case 'deriv': return 'd/d' + n.v + ' ' + fmt(n.a);
    case 'int': return '∫ ' + fmt(n.a) + ' d' + n.v;
    case 'matrix': return '[' + n.rows.map(r => r.map(fmt).join(', ')).join('; ') + ']';
    case 'eq': return fmt(n.l) + ' = ' + fmt(n.r);
    default: return '';
  }
}

/* ---------------- input interpretation ---------------- */
const CMDS = [
  { re: /^(?:integrate|integral\s+of|antiderivative\s+of|int)\s+([\s\S]+?)(?:\s*d\s*([a-z]))?$/i,
    make: (m) => ({ kind: 'int', v: m[2] || null, body: m[1], fnName: 'Integrate' }) },
  { re: /^d\s*\/\s*d\s*([a-z])\s*(?:\[)?([\s\S]+?)\]?$/i,
    make: (m) => ({ kind: 'deriv', v: m[1], body: m[2], fnName: 'Derivative' }) },
  { re: /^(?:differentiate|derivative\s+of)\s+([\s\S]+?)(?:\s+(?:wrt|with\s+respect\s+to)\s+([a-z]))?$/i,
    make: (m) => ({ kind: 'deriv', v: m[2] || null, body: m[1], fnName: 'Derivative' }) },
  { re: /^(?:rref|row\s*reduce|reduce)\s+([\s\S]+)$/i, make: (m) => ({ kind: 'rref', body: m[1], fnName: 'RowReduce' }) },
  { re: /^(?:eigenvalues|eigenvectors|eigen|eig)\s+(?:of\s+)?([\s\S]+)$/i, make: (m) => ({ kind: 'eig', body: m[1], fnName: 'Eigensystem' }) },
  { re: /^(?:det|determinant\s+of)\s+([\s\S]+)$/i, make: (m) => ({ kind: 'det', body: m[1], fnName: 'Det' }) },
  { re: /^(?:rank|rank\s+of)\s+([\s\S]+)$/i, make: (m) => ({ kind: 'rank', body: m[1], fnName: 'MatrixRank' }) },
  { re: /^(?:grad|gradient\s+of)\s+([\s\S]+)$/i, make: (m) => ({ kind: 'grad', body: m[1], fnName: 'Grad' }) },
  { re: /^(?:partial|d)\s*\/\s*(?:partial|d)?\s*([a-z])\s+([\s\S]+)$/i, make: (m) => ({ kind: 'deriv', v: m[1], body: m[2], fnName: 'Derivative' }) },
];
function firstVar(n, fallback) {
  const found = [];
  (function walk(x) {
    if (!x || typeof x !== 'object') return;
    if (x.t === 'sym' && /^[a-z]$/.test(x.name)) found.push(x.name);
    kids(x).forEach(walk);
  })(n);
  const pref = ['x', 't', 'u', 'y', 'z'].find(p => found.includes(p));
  return pref || found[0] || fallback;
}

export function interpret(src) {
  const s = src.trim().replace(/\s+/g, ' ');
  if (!s) return null;
  for (const c of CMDS) {
    const m = s.match(c.re);
    if (m) {
      const spec = c.make(m);
      const body = parse(spec.body);
      const v = spec.v || firstVar(body, 'x');
      return { ...spec, v, body, input: { t: spec.kind === 'int' ? 'int' : spec.kind === 'deriv' ? 'deriv' : 'call', a: body, v } };
    }
  }
  const body = parse(s);
  return { kind: 'simplify', body, v: firstVar(body, 'x'), fnName: 'Simplify', input: body };
}

export function evaluate(src) {
  const spec = interpret(src);
  if (!spec) return null;
  const { kind, body, v } = spec;
  if (kind === 'deriv') {
    const r = runSteps({ t: 'deriv', a: body, v }, 'deriv');
    return { ...spec, ...r, input: { t: 'deriv', a: body, v }, check: checkDeriv(body, r.result, v) };
  }
  if (kind === 'int') {
    const r = runSteps({ t: 'int', a: body, v }, 'int');
    return { ...spec, ...r, input: { t: 'int', a: body, v }, check: checkInt(body, r.result, v) };
  }
  if (kind === 'rref') {
    const r = rrefSteps(body);
    return { ...spec, steps: r.steps, result: r.result, input: body,
      check: { label: 'Rank', text: 'The reduced form has ' + r.rank + ' pivot' + (r.rank === 1 ? '' : 's') + ', so rank A = ' + r.rank + ' and the null space has dimension ' + (r.cols - r.rank) + '.' } };
  }
  if (kind === 'eig') {
    const r = eigSteps(body);
    const tr = toNums(body).reduce((s, row, i) => s + row[i], 0);
    const sum = r.eig ? r.eig.reduce((s, p) => s + p.lam, 0) : NaN;
    return { ...spec, steps: r.steps, result: r.result, input: body,
      check: r.eig ? { label: 'Trace check', text: 'The eigenvalues sum to ' + fmtNum(sum) + ' and the trace of A is ' + fmtNum(tr) + '. They agree, as they must.' } : null };
  }
  if (kind === 'det' || kind === 'rank') {
    const a = toNums(body);
    if (kind === 'det') {
      const d = det(a);
      return { ...spec, steps: [{ expr: { t: 'text', s: fmtNum(d) }, rule: 'Gaussian elimination', note: 'Row reduce to triangular form; the determinant is the product of the pivots, with a sign flip per row swap.' }],
        result: { t: 'text', s: fmtNum(d) }, input: body,
        check: { label: 'Invertibility', text: Math.abs(d) < 1e-9 ? 'The determinant is zero, so A is singular and its columns are dependent.' : 'The determinant is nonzero, so A is invertible and its columns form a basis.' } };
    }
    const r = rrefSteps(body);
    return { ...spec, steps: r.steps, result: { t: 'text', s: String(r.rank) }, input: body,
      check: { label: 'Rank–nullity', text: 'rank A = ' + r.rank + ', so the null space has dimension ' + (r.cols - r.rank) + '.' } };
  }
  if (kind === 'grad') {
    const vars = [];
    (function walk(x) { if (!x || typeof x !== 'object') return; if (x.t === 'sym' && /^[a-z]$/.test(x.name) && !vars.includes(x.name)) vars.push(x.name); kids(x).forEach(walk); })(body);
    vars.sort();
    const steps = vars.map(vv => {
      const r = runSteps({ t: 'deriv', a: body, v: vv }, 'deriv');
      return { expr: { t: 'eq', l: { t: 'text', s: '∂f/∂' + vv }, r: r.result }, rule: 'Partial derivative in ' + vv,
        note: 'Hold ' + vars.filter(o => o !== vv).join(', ') + ' constant and differentiate in ' + vv + '.' };
    });
    return { ...spec, steps, result: { t: 'matrix', rows: steps.map(s => [s.expr.r]) }, input: body,
      check: { label: 'Reading it', text: 'The gradient points in the direction of steepest increase of f; its components are the partials in ' + vars.join(', ') + '.' } };
  }
  const r = simp(body);
  return { ...spec, steps: [{ expr: r, rule: 'Simplify', note: 'Fold constants, collect like terms and like powers.' }],
    result: r, input: body, check: numCheck(r, v) };
}

/* ---------------- sanity checks ---------------- */
function checkDeriv(f, fp, v) {
  const x0 = 1.3, h = 1e-5;
  const fd = (evalAt(f, { [v]: x0 + h }) - evalAt(f, { [v]: x0 - h })) / (2 * h);
  const sym = evalAt(fp, { [v]: x0 });
  if (!isFinite(fd) || !isFinite(sym)) return null;
  const ok = Math.abs(fd - sym) < 1e-4 * Math.max(1, Math.abs(sym));
  return { label: 'Numeric check at ' + v + ' = ' + x0,
    text: 'A central difference on f gives ' + fd.toFixed(6) + '; the symbolic derivative gives ' + sym.toFixed(6) + '. ' + (ok ? 'They agree.' : 'They disagree — the result is suspect.'),
    ok, plot: { f, fp, v } };
}
function checkInt(f, F, v) {
  if (F.t === 'text') return null;
  const a = 0.4, b = 1.7;
  const n = 2000, h = (b - a) / n;
  let s = 0;
  for (let i = 0; i < n; i++) { const m = a + h * (i + 0.5); const y = evalAt(f, { [v]: m }); if (!isFinite(y)) return null; s += y * h; }
  const exact = evalAt(F, { [v]: b }) - evalAt(F, { [v]: a });
  if (!isFinite(exact)) return null;
  const ok = Math.abs(exact - s) < 1e-4 * Math.max(1, Math.abs(exact));
  return { label: 'Numeric check on [' + a + ', ' + b + ']',
    text: 'Midpoint quadrature of the integrand gives ' + s.toFixed(6) + '; F(' + b + ') − F(' + a + ') gives ' + exact.toFixed(6) + '. ' + (ok ? 'They agree.' : 'They disagree — the result is suspect.'),
    ok, plot: { f, fp: F, v } };
}
function numCheck(r, v) {
  if (!hasVar(r, v)) {
    const val = evalAt(r, {});
    if (isFinite(val)) return { label: 'Value', text: 'The expression is constant in ' + v + ' and equals ' + fmtNum(val) + '.' };
    return null;
  }
  const at = evalAt(r, { [v]: 1 });
  return isFinite(at) ? { label: 'Spot value', text: 'At ' + v + ' = 1 the expression equals ' + fmtNum(at) + '.', plot: { f: r, v } } : null;
}
export function sample(node, v, a, b, n) {
  const pts = [];
  for (let i = 0; i <= n; i++) {
    const x = a + (b - a) * i / n;
    const y = evalAt(node, { [v]: x });
    pts.push([x, isFinite(y) ? y : null]);
  }
  return pts;
}

/* ---------------- node description, for the explanation drawer ---------------- */
const DOCS = {
  Integrate: { sig: 'integrate f dx', blurb: 'Finds an antiderivative of f with respect to the given variable, applying linearity, the power rule, the standard table, linear substitution and integration by parts.',
    also: ['integrate x^2 dx', 'integrate x sin(x) dx', 'integrate 1/(1+x^2) dx'], ref: 'https://mathworld.wolfram.com/Integral.html' },
  Derivative: { sig: 'd/dx f   ·   differentiate f wrt x', blurb: 'Differentiates f one rule at a time, naming each rule as it is applied: sum, product, quotient, power, chain and the standard table.',
    also: ['d/dx sin(x) x^2', 'differentiate ln(x)/x wrt x'], ref: 'https://mathworld.wolfram.com/Derivative.html' },
  RowReduce: { sig: 'rref M', blurb: 'Reduces a matrix to reduced row echelon form by Gauss–Jordan elimination, recording every row operation.',
    also: ['rref [[1,2,3],[4,5,6],[7,8,9]]'], ref: 'https://mathworld.wolfram.com/EchelonForm.html' },
  Eigensystem: { sig: 'eigen M', blurb: 'Builds the characteristic polynomial of a 2×2 or 3×3 matrix, solves for its real roots, and reads an eigenvector out of the null space of A − λI for each.',
    also: ['eigen [[2,1],[1,2]]'], ref: 'https://mathworld.wolfram.com/Eigenvalue.html' },
  Det: { sig: 'det M', blurb: 'Determinant by Gaussian elimination — the product of the pivots, signed by the number of row swaps.', also: ['det [[3,1],[2,4]]'], ref: 'https://mathworld.wolfram.com/Determinant.html' },
  MatrixRank: { sig: 'rank M', blurb: 'The number of pivots in the reduced row echelon form.', also: ['rank [[1,2],[2,4]]'], ref: 'https://mathworld.wolfram.com/MatrixRank.html' },
  Grad: { sig: 'grad f', blurb: 'The vector of first partial derivatives of f in every variable it contains, sorted alphabetically.', also: ['grad x^2 y + sin(y)'], ref: 'https://mathworld.wolfram.com/Gradient.html' },
  Simplify: { sig: 'expression', blurb: 'Parses the expression and simplifies it: folds constants, collects like terms, and combines like powers.', also: ['2x + 3x - 5', '(x^2)^3'], ref: 'https://mathworld.wolfram.com/Simplification.html' },
};
export function docFor(name) { return DOCS[name] ? { name, ...DOCS[name] } : null; }

const REFS = {
  sin: 'https://mathworld.wolfram.com/Sine.html', cos: 'https://mathworld.wolfram.com/Cosine.html',
  tan: 'https://mathworld.wolfram.com/Tangent.html', exp: 'https://mathworld.wolfram.com/ExponentialFunction.html',
  ln: 'https://mathworld.wolfram.com/NaturalLogarithm.html', sqrt: 'https://mathworld.wolfram.com/SquareRoot.html',
  atan: 'https://mathworld.wolfram.com/InverseTangent.html',
};
export function describe(n, v) {
  if (!n) return null;
  const base = { text: fmt(n) };
  switch (n.t) {
    case 'num': return { ...base, kind: 'Constant', note: 'A number. Its derivative in ' + v + ' is 0; as a factor it passes through both differentiation and integration.', ref: 'https://mathworld.wolfram.com/Constant.html' };
    case 'sym': return { ...base, kind: n.name === v ? 'The variable of differentiation' : 'Symbol',
      note: n.name === v ? 'Everything is differentiated and integrated with respect to ' + v + '.' : n.name + ' is held constant with respect to ' + v + '.',
      ref: 'https://mathworld.wolfram.com/Variable.html' };
    case 'add': return { ...base, kind: 'Sum of ' + n.args.length + ' terms', note: 'Differentiation and integration are both linear, so each term is handled separately.', ref: 'https://mathworld.wolfram.com/Sum.html' };
    case 'neg': return { ...base, kind: 'Negation', note: 'A factor of −1, which passes straight through the derivative and the integral.', ref: null };
    case 'mul': return { ...base, kind: 'Product of ' + n.args.length + ' factors',
      note: n.args.every(a => !hasVar(a, v)) ? 'No factor depends on ' + v + ', so this is a constant.' : 'Factors that depend on ' + v + ' need the product rule; the rest move outside.',
      ref: 'https://mathworld.wolfram.com/ProductRule.html' };
    case 'div': return { ...base, kind: 'Quotient', note: 'Differentiated by the quotient rule (f′g − f g′)/g²; watch for the point where the denominator vanishes.', ref: 'https://mathworld.wolfram.com/QuotientRule.html' };
    case 'pow': return { ...base, kind: 'Power', note: hasVar(n.exp, v) ? 'The exponent depends on ' + v + ', so the power rule does not apply — this needs the exponential rule.' : 'A fixed exponent, so the power rule applies: bring the exponent down and reduce it by one.',
      ref: 'https://mathworld.wolfram.com/PowerRule.html' };
    case 'fn': return { ...base, kind: 'Function application: ' + n.name, note: 'Its derivative comes from the standard table, composed with the chain rule when the argument is not just ' + v + '.', ref: REFS[n.name] || null };
    case 'deriv': return { ...base, kind: 'Unevaluated derivative', note: 'Still waiting for a rule to be applied.', ref: null };
    case 'int': return { ...base, kind: 'Unevaluated integral', note: 'Still waiting for a rule to be applied.', ref: null };
    case 'matrix': return { ...base, kind: 'Matrix ' + n.rows.length + '×' + (n.rows[0] || []).length, note: 'Rows are equations, columns are the coordinates of vectors — row reduction rewrites the equations without changing their solution set.', ref: 'https://mathworld.wolfram.com/Matrix.html' };
    default: return { ...base, kind: 'Expression', note: '', ref: null };
  }
}
