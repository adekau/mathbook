// AST -> React elements, with every subexpression individually selectable.
const DEFAULT_THEME = {
  op: 'color-mix(in srgb, var(--color-text) 72%, transparent)',
  rule: 'color-mix(in srgb, var(--color-text) 65%, transparent)',
  fnColor: 'var(--color-accent-300)',
  bracket: 'var(--color-neutral-500)',
  selBg: 'color-mix(in srgb, var(--color-accent) 26%, transparent)',
  selRing: 'var(--color-accent-400)',
  hoverBg: 'color-mix(in srgb, var(--color-accent) 12%, transparent)',
  plot: 'var(--color-accent)',
  axis: 'var(--color-neutral-700)',
  axis2: 'var(--color-neutral-800)',
};

export function makeRenderer(React, theme) {
  const h = React.createElement;
  const T = Object.assign({}, DEFAULT_THEME, theme || {});

  const MATH = "'Iowan Old Style','Palatino Linotype','Book Antiqua',Palatino,'STIX Two Math',Georgia,serif";

  function wrap(node, id, opts, children, extra) {
    const sel = opts.selected === id;
    const style = {
      display: 'inline-flex', alignItems: 'center', borderRadius: '3px',
      padding: '0 1px', margin: '0 -1px', cursor: 'pointer',
      transition: 'background 90ms linear, box-shadow 90ms linear',
      background: sel ? T.selBg : 'transparent',
      boxShadow: sel ? '0 0 0 1px ' + T.selRing : 'none',
      ...(extra || {}),
    };
    return h('span', {
      key: id, style,
      'data-mid': id,
      onClick: (e) => { e.stopPropagation(); opts.onSelect && opts.onSelect(id, node); },
      onMouseEnter: (e) => { if (!sel) e.currentTarget.style.background = T.hoverBg; },
      onMouseLeave: (e) => { if (!sel) e.currentTarget.style.background = 'transparent'; },
    }, children);
  }

  function op(s, tight) {
    return h('span', { style: { padding: tight ? '0 0.06em 0 0' : '0 0.22em', color: T.op } }, s);
  }

  function prec(n) {
    switch (n.t) {
      case 'add': return 1;
      case 'mul': case 'div': return 2;
      case 'neg': return 1.5;
      case 'pow': return 4;
      default: return 5;
    }
  }

  function paren(inner) {
    const bar = (c) => h('span', { style: { fontFamily: MATH, fontSize: '1.15em', lineHeight: 1, color: T.op } }, c);
    return h('span', { style: { display: 'inline-flex', alignItems: 'center' } }, bar('('), inner, bar(')'));
  }

  function render(n, opts, id) {
    id = id || 'r';
    if (!n || typeof n !== 'object') return null;
    const kids = (child, slot) => render(child, opts, id + '.' + slot);

    switch (n.t) {
      case 'num':
        return wrap(n, id, opts, String(n.v), { fontFamily: MATH });
      case 'text':
        return wrap(n, id, opts, n.s, { fontFamily: MATH });
      case 'sym':
        return wrap(n, id, opts, n.name, { fontFamily: MATH, fontStyle: n.name.length === 1 ? 'italic' : 'normal' });
      case 'neg':
        return wrap(n, id, opts, [op('−'), prec(n.a) <= 1.5 ? paren(kids(n.a, 'a')) : kids(n.a, 'a')]);
      case 'add': {
        const parts = [];
        n.args.forEach((a, i) => {
          if (i) parts.push(op(a.t === 'neg' ? '−' : '+'));
          else if (a.t === 'neg') parts.push(op('−', true));
          const body = a.t === 'neg' ? kids(a.a, i + '.a') : kids(a, i);
          parts.push(body);
        });
        return wrap(n, id, opts, parts);
      }
      case 'mul': {
        const parts = [];
        n.args.forEach((a, i) => {
          if (i) {
            const needDot = a.t === 'num' || (a.t === 'pow' && a.base.t === 'num');
            parts.push(op(needDot ? '·' : '\u2009'));
          }
          parts.push(prec(a) <= 1.5 ? paren(kids(a, i)) : kids(a, i));
        });
        return wrap(n, id, opts, parts);
      }
      case 'div':
        return wrap(n, id, opts, h('span', {
          style: { display: 'inline-flex', flexDirection: 'column', alignItems: 'center', verticalAlign: 'middle', margin: '0 0.15em', fontSize: '0.94em' },
        },
          h('span', { style: { padding: '0 0.3em 0.08em' } }, kids(n.num, 'num')),
          h('span', { style: { width: '100%', height: '1px', background: T.rule } }),
          h('span', { style: { padding: '0.08em 0.3em 0' } }, kids(n.den, 'den'))
        ));
      case 'pow':
        return wrap(n, id, opts, [
          prec(n.base) < 4 ? paren(kids(n.base, 'base')) : kids(n.base, 'base'),
          h('span', { key: 'e', style: { fontSize: '0.7em', alignSelf: 'flex-start', marginTop: '-0.25em', marginLeft: '0.08em' } }, kids(n.exp, 'exp')),
        ]);
      case 'fn': {
        const known = ['sin', 'cos', 'tan', 'ln', 'log', 'exp', 'sqrt', 'abs', 'sec', 'csc', 'cot', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh'].includes(n.name);
        if (n.name === 'sqrt')
          return wrap(n, id, opts, [
            h('span', { key: 's', style: { fontFamily: MATH, fontSize: '1.15em' } }, '√'),
            h('span', { key: 'b', style: { borderTop: '1px solid ' + T.rule, padding: '0.1em 0.15em 0' } }, kids(n.args[0], 0)),
          ]);
        if (n.name === 'abs')
          return wrap(n, id, opts, [h('span', { key: 'l', style: { padding: '0 0.1em' } }, '|'), kids(n.args[0], 0), h('span', { key: 'r', style: { padding: '0 0.1em' } }, '|')]);
        const nameSpan = h('span', {
          key: 'n',
          style: { fontFamily: MATH, color: known ? T.fnColor : 'inherit' },
          onMouseEnter: (e) => opts.onHoverFn && opts.onHoverFn(n.name, e.currentTarget),
          onMouseLeave: () => opts.onLeaveFn && opts.onLeaveFn(),
        }, n.name);
        const args = [];
        n.args.forEach((a, i) => { if (i) args.push(op(',')); args.push(kids(a, i)); });
        return wrap(n, id, opts, [nameSpan, paren(h('span', null, args))]);
      }
      case 'deriv':
        return wrap(n, id, opts, [
          h('span', { key: 'd', style: { display: 'inline-flex', flexDirection: 'column', alignItems: 'center', fontFamily: MATH, fontSize: '0.9em', marginRight: '0.2em' } },
            h('span', { style: { padding: '0 0.2em' } }, 'd'),
            h('span', { style: { width: '100%', height: '1px', background: T.rule } }),
            h('span', { style: { padding: '0 0.2em' } }, ['d', h('i', { key: 'v' }, n.v)])
          ),
          prec(n.a) <= 2 ? paren(kids(n.a, 'a')) : kids(n.a, 'a'),
        ]);
      case 'int':
        return wrap(n, id, opts, [
          h('span', { key: 'g', style: { fontFamily: MATH, fontSize: '1.7em', lineHeight: 0.7, marginRight: '0.12em', color: T.fnColor } }, '∫'),
          kids(n.a, 'a'),
          h('span', { key: 'dv', style: { fontFamily: MATH, marginLeft: '0.3em' } }, ['d', h('i', { key: 'v' }, n.v)]),
        ]);
      case 'eq':
        return wrap(n, id, opts, [kids(n.l, 'l'), op('='), kids(n.r, 'r')]);
      case 'matrix': {
        const bracket = (left) => h('span', {
          style: {
            width: '0.42em', alignSelf: 'stretch',
            borderTop: '1px solid ' + T.bracket, borderBottom: '1px solid ' + T.bracket,
            [left ? 'borderLeft' : 'borderRight']: '1px solid ' + T.bracket,
            borderRadius: left ? '2px 0 0 2px' : '0 2px 2px 0',
          },
        });
        const cols = Math.max(...n.rows.map(r => r.length));
        return wrap(n, id, opts, h('span', { style: { display: 'inline-flex', alignItems: 'stretch', verticalAlign: 'middle' } },
          bracket(true),
          h('span', {
            style: { display: 'grid', gridTemplateColumns: 'repeat(' + cols + ', auto)', columnGap: '1.1em', rowGap: '0.35em', padding: '0.3em 0.5em', justifyItems: 'end' },
          }, n.rows.flatMap((row, i) => row.map((c, j) => h('span', { key: i + '_' + j }, render(c, opts, id + '.r' + i + '_' + j))))),
          bracket(false)
        ), { verticalAlign: 'middle' });
      }
      default:
        return null;
    }
  }

  // find a node inside root by the id path the renderer assigned
  function nodeById(root, id) {
    const parts = id.split('.').slice(1);
    let cur = root;
    for (const p of parts) {
      if (!cur) return null;
      if (/^r\d+_\d+$/.test(p)) {
        const [i, j] = p.slice(1).split('_').map(Number);
        cur = cur.rows[i][j];
      } else if (/^\d+$/.test(p)) {
        cur = (cur.args || [])[+p];
      } else cur = cur[p];
    }
    return cur;
  }

  function plot(spec, w, hgt) {
    const { f, v } = spec;
    const a = -3, b = 3, n = 160;
    const pts = [];
    for (let i = 0; i <= n; i++) {
      const x = a + (b - a) * i / n;
      let y;
      try { y = evalIn(f, v, x); } catch (e) { y = NaN; }
      pts.push([x, y]);
    }
    const ys = pts.map(p => p[1]).filter(y => isFinite(y));
    if (!ys.length) return null;
    let lo = Math.min(...ys), hi = Math.max(...ys);
    if (hi - lo < 1e-9) { lo -= 1; hi += 1; }
    const clip = Math.max(Math.abs(lo), Math.abs(hi));
    if (clip > 40) { lo = Math.max(lo, -40); hi = Math.min(hi, 40); }
    const pad = (hi - lo) * 0.12;
    lo -= pad; hi += pad;
    const X = x => ((x - a) / (b - a)) * w;
    const Y = y => hgt - ((y - lo) / (hi - lo)) * hgt;
    const segs = [];
    let cur = [];
    pts.forEach(([x, y]) => {
      if (!isFinite(y) || y < lo - (hi - lo) || y > hi + (hi - lo)) { if (cur.length > 1) segs.push(cur); cur = []; return; }
      cur.push(X(x).toFixed(1) + ',' + Y(y).toFixed(1));
    });
    if (cur.length > 1) segs.push(cur);
    const zeroY = lo < 0 && hi > 0 ? Y(0) : null;
    return h('svg', { width: w, height: hgt, viewBox: '0 0 ' + w + ' ' + hgt, style: { display: 'block', overflow: 'visible' } },
      zeroY !== null ? h('line', { key: 'z', x1: 0, x2: w, y1: zeroY, y2: zeroY, stroke: T.axis, strokeWidth: 1 }) : null,
      h('line', { key: 'y', x1: X(0), x2: X(0), y1: 0, y2: hgt, stroke: T.axis2, strokeWidth: 1 }),
      segs.map((s, i) => h('polyline', { key: i, points: s.join(' '), fill: 'none', stroke: T.plot, strokeWidth: 1.6, strokeLinejoin: 'round' }))
    );
  }

  let evalFn = null;
  function evalIn(node, v, x) { return evalFn(node, { [v]: x }); }
  function setEval(fn) { evalFn = fn; }

  return { render, nodeById, plot, setEval, MATH };
}
