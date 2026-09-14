// Glyph-level TeX morphing: measure KaTeX output, match glyphs between two
// expressions, and emit interpolated frames. This is what makes a step look
// like Manim's TransformMatchingTex instead of a crossfade.

export function ready() { return typeof window !== 'undefined' && !!window.katex; }

// Render `tex` into a hidden container and return every drawn leaf glyph with
// its position relative to the expression's own bounding box.
export function measure(tex, container) {
  if (!ready() || !container) return null;
  container.innerHTML = '';
  const box = document.createElement('div');
  box.style.cssText = 'display:inline-block; position:absolute; left:0; top:0; white-space:nowrap;';
  container.appendChild(box);
  try { window.katex.render(tex, box, { throwOnError: false, displayMode: true }); }
  catch (e) { return null; }

  const root = box.getBoundingClientRect();
  if (!root.width) return null;
  const glyphs = [];

  const walk = (el) => {
    const cl = el.classList;
    if (cl && (cl.contains('frac-line') || cl.contains('overline-line')
      || cl.contains('underline-line') || cl.contains('hline'))) {
      const r = el.getBoundingClientRect();
      glyphs.push({ text: '', rule: true, x: r.left - root.left, y: r.top - root.top,
        w: r.width, h: Math.max(1, r.height) });
      return;
    }
    if (!el.children.length) {
      const txt = (el.textContent || '').replace(/\u200b/g, '').trim();
      if (txt) {
        const r = el.getBoundingClientRect();
        if (r.width > 0.05 && r.height > 0.05) {
          const cs = getComputedStyle(el);
          glyphs.push({ text: txt, rule: false, x: r.left - root.left, y: r.top - root.top,
            w: r.width, h: r.height, fs: parseFloat(cs.fontSize) || 20,
            fst: cs.fontStyle, fw: cs.fontWeight, ff: cs.fontFamily });
        }
      }
      return;
    }
    for (let i = 0; i < el.children.length; i++) walk(el.children[i]);
  };
  walk(box);
  container.innerHTML = '';
  return glyphs.length ? { glyphs, w: root.width, h: root.height } : null;
}

// Longest-common-subsequence match on glyph text. Everything outside the
// subsequence is a term that genuinely left or entered the expression.
export function match(prev, next) {
  const A = prev.glyphs, B = next.glyphs;
  const n = A.length, m = B.length;
  const same = (a, b) => a.text === b.text && a.rule === b.rule;
  const dp = [];
  for (let i = 0; i <= n; i++) dp.push(new Int32Array(m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = same(A[i], B[j]) ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const pairs = [], goneIdx = [], addedIdx = [];
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (same(A[i], B[j])) { pairs.push([i, j]); i++; j++; }
    else if (dp[i + 1][j] >= dp[i][j + 1]) { goneIdx.push(i++); }
    else { addedIdx.push(j++); }
  }
  while (i < n) goneIdx.push(i++);
  while (j < m) addedIdx.push(j++);
  return { pairs, goneIdx, addedIdx };
}

const lerp = (a, b, t) => a + (b - a) * t;

// One frame of the morph at progress p, as absolutely-positioned glyph specs
// centred on (0,0) so the stage can drop them at its midpoint.
export function frame(prev, next, mt, p, colors) {
  const C = colors || { gone: '#ff7b72', added: '#3fb950', ink: '#e6edf3' };
  const out = [];
  const put = (key, g, x, y, opacity, color, w, h, fs) => out.push({
    key, text: g.text, rule: g.rule,
    left: x.toFixed(2) + 'px', top: y.toFixed(2) + 'px',
    w: g.rule ? (w || g.w).toFixed(2) + 'px' : 'auto',
    h: g.rule ? (h || g.h).toFixed(2) + 'px' : 'auto',
    bg: g.rule ? (color || C.ink) : 'transparent',
    fs: (fs || g.fs || 20).toFixed(2) + 'px',
    ff: g.ff || 'KaTeX_Main, serif', fst: g.fst || 'normal', fw: g.fw || '400',
    color: color || C.ink, opacity: Math.max(0, Math.min(1, opacity)).toFixed(3),
  });

  if (!next) return out;
  const ox = (L) => -L.w / 2, oy = (L) => -L.h / 2;

  if (!prev || !mt) {
    next.glyphs.forEach((g, k) => put('n' + k, g, g.x + ox(next), g.y + oy(next), p, null));
    return out;
  }

  mt.pairs.forEach(function (pr, k) {
    const A = prev.glyphs[pr[0]], B = next.glyphs[pr[1]];
    put('p' + k, B,
      lerp(A.x + ox(prev), B.x + ox(next), p),
      lerp(A.y + oy(prev), B.y + oy(next), p),
      1, null,
      lerp(A.w, B.w, p), lerp(A.h, B.h, p), lerp(A.fs || 20, B.fs || 20, p));
  });
  mt.goneIdx.forEach(function (ai, k) {
    const A = prev.glyphs[ai];
    put('g' + k, A, A.x + ox(prev), A.y + oy(prev), 1 - Math.min(1, p * 1.9), C.gone);
  });
  mt.addedIdx.forEach(function (bi, k) {
    const B = next.glyphs[bi];
    put('a' + k, B, B.x + ox(next), B.y + oy(next), Math.max(0, (p - 0.4) / 0.6), C.added);
  });
  return out;
}
