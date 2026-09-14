// KaTeX glyph-level morphing for Manim Studio preview.
// Renders TeX offscreen, measures every glyph box, matches glyphs between two
// expressions by LCS, and interpolates position/opacity — the browser-side
// approximation of Manim's TransformMatchingTex.

const cache = new Map();
let host = null;

function ensureHost() {
  if (host && host.isConnected) return host;
  host = document.createElement('div');
  host.setAttribute('data-morph-host', '');
  host.style.cssText = 'position:fixed; left:-99999px; top:0; visibility:hidden; pointer-events:none; z-index:-1';
  document.body.appendChild(host);
  return host;
}

export function katexReady() {
  return new Promise((resolve) => {
    const poll = () => { if (window.katex) resolve(window.katex); else setTimeout(poll, 40); };
    poll();
  });
}

export function measure(tex, fontSize) {
  const key = fontSize + '|' + tex;
  if (cache.has(key)) return cache.get(key);
  const empty = { glyphs: [], w: 0, h: 0 };
  if (!window.katex || !tex) return empty;

  const h = ensureHost();
  h.innerHTML = '';
  const el = document.createElement('div');
  el.style.cssText = 'font-size:' + fontSize + 'px; display:inline-block; white-space:nowrap';
  h.appendChild(el);
  try { window.katex.render(tex, el, { throwOnError: false, displayMode: false }); }
  catch (e) { return empty; }

  const root = el.querySelector('.katex-html');
  if (!root) return empty;
  // MathML duplicate would double-count every glyph
  const mml = el.querySelector('.katex-mathml');
  if (mml) mml.remove();

  const base = root.getBoundingClientRect();
  const glyphs = [];
  const range = document.createRange();

  const walk = (node) => {
    for (const child of node.childNodes) {
      if (child.nodeType === 3) {
        const txt = child.textContent;
        if (!txt || !txt.trim()) continue;
        const cs = getComputedStyle(child.parentElement);
        for (let i = 0; i < txt.length; i++) {
          if (!txt[i].trim()) continue;
          range.setStart(child, i); range.setEnd(child, i + 1);
          const r = range.getBoundingClientRect();
          if (r.width < 0.05 && r.height < 0.05) continue;
          glyphs.push({
            ch: txt[i], x: r.left - base.left, y: r.top - base.top, w: r.width, h: r.height,
            font: cs.fontFamily, size: cs.fontSize, style: cs.fontStyle, weight: cs.fontWeight,
          });
        }
      } else if (child.nodeType === 1) {
        const cs = getComputedStyle(child);
        const bw = parseFloat(cs.borderBottomWidth) || 0;
        if (bw > 0 && child.clientWidth > 0) {
          const r = child.getBoundingClientRect();
          glyphs.push({ ch: '\u2500', rule: true, x: r.left - base.left, y: r.bottom - base.top - bw,
            w: r.width, h: Math.max(1, bw) });
        }
        walk(child);
      }
    }
  };
  walk(root);

  const out = { glyphs, w: base.width, h: base.height };
  cache.set(key, out);
  return out;
}

function lcsPairs(A, B) {
  const n = A.length, m = B.length;
  if (!n || !m) return { pairs: [], usedA: new Set(), usedB: new Set() };
  const dp = Array.from({ length: n + 1 }, () => new Int32Array(m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = A[i].ch === B[j].ch ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const pairs = [], usedA = new Set(), usedB = new Set();
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (A[i].ch === B[j].ch) { pairs.push([i, j]); usedA.add(i); usedB.add(j); i++; j++; }
    else if (dp[i + 1][j] >= dp[i][j + 1]) i++;
    else j++;
  }
  return { pairs, usedA, usedB };
}

const clamp01 = (x) => x < 0 ? 0 : x > 1 ? 1 : x;
const easeIO = (p) => p < 0.5 ? 2 * p * p : 1 - Math.pow(-2 * p + 2, 2) / 2;

function glyphEl(React, g, key, style) {
  if (g.rule) {
    return React.createElement('div', { key, style: { position: 'absolute', ...style, width: g.w + 'px', height: Math.max(1, g.h) + 'px', background: style.color } });
  }
  return React.createElement('span', {
    key,
    style: {
      position: 'absolute', whiteSpace: 'pre', lineHeight: 'normal',
      fontFamily: g.font, fontSize: g.size, fontStyle: g.style, fontWeight: g.weight,
      ...style,
    },
  }, g.ch);
}

// p: 0..1 progress through the transition into `curTex`
export function frame(React, prevTex, curTex, p, fontSize, C) {
  const col = C || {};
  const ink = col.ink || '#e6edf3';
  const gone = col.gone || '#f85149';
  const added = col.added || '#3fb950';

  const B = measure(curTex, fontSize);
  if (!B.glyphs.length) return null;
  const A = prevTex ? measure(prevTex, fontSize) : { glyphs: [], w: 0, h: 0 };

  const e = easeIO(clamp01(p));
  const W = A.w ? A.w + (B.w - A.w) * e : B.w;
  const H = Math.max(A.h, B.h);
  const kids = [];

  // no previous expression: write the glyphs on, left to right
  if (!A.glyphs.length) {
    const n = B.glyphs.length, span = Math.max(1, n * 0.55);
    B.glyphs.forEach((g, i) => {
      const o = clamp01((clamp01(p) * (n + span) - i) / span);
      if (o <= 0.001) return;
      kids.push(glyphEl(React, g, 'w' + i, {
        left: (g.x + (B.w - W) / -2 - (B.w - W) / 2 + 0).toFixed(2) + 'px',
        top: g.y.toFixed(2) + 'px', opacity: o, color: ink,
      }));
    });
    return React.createElement('div', { style: { position: 'relative', width: W + 'px', height: H + 'px', margin: '0 auto' } }, kids);
  }

  const { pairs, usedA, usedB } = lcsPairs(A.glyphs, B.glyphs);
  const offA = (W - A.w) / 2, offB = (W - B.w) / 2;

  pairs.forEach(([ai, bi], k) => {
    const a = A.glyphs[ai], b = B.glyphs[bi];
    kids.push(glyphEl(React, b, 'm' + k, {
      left: ((a.x + offA) + ((b.x + offB) - (a.x + offA)) * e).toFixed(2) + 'px',
      top: (a.y + (b.y - a.y) * e).toFixed(2) + 'px',
      opacity: 1, color: ink,
      width: b.rule ? ((a.w + (b.w - a.w) * e)) + 'px' : undefined,
    }));
  });

  A.glyphs.forEach((g, i) => {
    if (usedA.has(i)) return;
    const o = clamp01(1 - p * 1.9);
    if (o <= 0.001) return;
    kids.push(glyphEl(React, g, 'g' + i, {
      left: (g.x + offA).toFixed(2) + 'px', top: g.y.toFixed(2) + 'px',
      opacity: o, color: gone,
      transform: 'scale(' + (1 - 0.25 * clamp01(p * 1.9)).toFixed(3) + ')',
    }));
  });

  B.glyphs.forEach((g, i) => {
    if (usedB.has(i)) return;
    const o = clamp01((p - 0.38) / 0.5);
    if (o <= 0.001) return;
    kids.push(glyphEl(React, g, 'a' + i, {
      left: (g.x + offB).toFixed(2) + 'px', top: g.y.toFixed(2) + 'px',
      opacity: o, color: o > 0.94 ? ink : added,
    }));
  });

  return React.createElement('div', { style: { position: 'relative', width: W + 'px', height: H + 'px', margin: '0 auto' } }, kids);
}

export function widthOf(tex, fontSize) { return measure(tex, fontSize).w; }
