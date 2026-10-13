// Canvas plotting: line/scatter/bar charts, heat maps with vectors, animated profiles and
// particle motion, and a rotatable 3-D viewer for paths, point clouds and meshes.
import { fmt } from './units.js';

const PALETTE = ['#4cc9f0', '#f72585', '#ffd166', '#06d6a0', '#b388ff', '#ff8c42', '#90e0ef', '#ef476f'];
const css = (el, name, fallback) => (getComputedStyle(el).getPropertyValue(name).trim() || fallback);
const theme = el => ({ fg: css(el, '--fg', '#e8ecf4'), dim: css(el, '--fg-dim', '#93a0b8'), grid: css(el, '--line', '#2a3550'), bg: css(el, '--card', '#131a2b'), accent: css(el, '--accent', '#4cc9f0') });

function setup(canvas, h) {
  const dpr = Math.min(window.devicePixelRatio || 1, 2.5), w = Math.max(240, canvas.clientWidth || canvas.parentElement.clientWidth || 600);
  canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr); canvas.style.height = h + 'px';
  const ctx = canvas.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  return { ctx, w, h };
}
function niceTicks(lo, hi, n = 6) {
  // a span below the resolution of the numbers themselves is no span: ticks could not advance across it
  if (!(hi - lo > 1e-9 * Math.max(Math.abs(lo), Math.abs(hi)))) { const d = Math.abs(lo) || 1; lo -= d * 0.5; hi += d * 0.5; }
  const span = hi - lo, step0 = Math.pow(10, Math.floor(Math.log10(span / n))), err = span / n / step0;
  const step = step0 * (err >= 7.5 ? 10 : err >= 3.5 ? 5 : err >= 1.5 ? 2 : 1), t = [];
  for (let v = Math.ceil(lo / step) * step; v <= hi + step * 1e-9 && t.length < 60; v += step) t.push(Math.abs(v) < step * 1e-9 ? 0 : v);
  return t;
}
const logTicks = (lo, hi) => { const t = []; for (let e = Math.floor(lo); e <= Math.ceil(hi); e++) if (e >= lo - 1e-9 && e <= hi + 1e-9) t.push(e); return t.length >= 2 ? t : [lo, hi]; };
const tickLabel = v => { const a = Math.abs(v); if (v === 0) return '0'; if (a >= 1e5 || a < 1e-3) { const e = Math.floor(Math.log10(a)), m = v / Math.pow(10, e); return `${parseFloat(m.toFixed(2))}e${e}`; } return String(parseFloat(v.toPrecision(4))); };
const extent = arrs => { let lo = Infinity, hi = -Infinity; for (const a of arrs) for (const v of a) if (Number.isFinite(v)) { if (v < lo) lo = v; if (v > hi) hi = v; } return lo === Infinity ? [0, 1] : [lo, hi]; };

/**
 * Line / scatter chart.
 * spec: {x:{label,unit,data}, y:[{label,data,dash}], yLabel, yUnit, logx, logy, kind, overlay:[{label,x,y}], band:{lo,hi}, points:[{x,y,label}], vline}
 */
export function lineChart(canvas, spec, opts = {}) {
  const H = opts.height || 300, { ctx, w, h } = setup(canvas, H), th = theme(canvas);
  const m = { l: 58, r: 14, t: 12, b: 42 }, pw = w - m.l - m.r, ph = h - m.t - m.b;
  const tx = v => (spec.logx ? Math.log10(v) : v), ty = v => (spec.logy ? Math.log10(v) : v);
  const xs = [spec.x.data, ...(spec.overlay || []).map(o => o.x), ...(spec.points ? [spec.points.map(p => p.x)] : [])].map(a => a.map(tx));
  const ys = [...spec.y.map(s => s.data), ...(spec.overlay || []).map(o => o.y), ...(spec.band ? [spec.band.lo, spec.band.hi] : []), ...(spec.points ? [spec.points.map(p => p.y)] : [])].map(a => a.map(ty));
  let [x0, x1] = extent(xs), [y0, y1] = spec.yRange ? spec.yRange.map(ty) : extent(ys);
  if (!(y1 - y0 > 1e-9 * Math.max(Math.abs(y0), Math.abs(y1)))) { const d = Math.abs(y0) * 0.1 || 1; y0 -= d; y1 += d; } else if (!spec.yRange) { const p = (y1 - y0) * 0.06; y0 -= p; y1 += p; }
  if (x0 === x1) { x0 -= 1; x1 += 1; }
  const X = v => m.l + (tx(v) - x0) / (x1 - x0) * pw, Y = v => m.t + ph - (ty(v) - y0) / (y1 - y0) * ph;
  ctx.font = '11px system-ui, sans-serif'; ctx.lineWidth = 1;
  const xt = spec.logx ? logTicks(x0, x1) : niceTicks(x0, x1, Math.max(3, Math.floor(pw / 90))), yt = spec.logy ? logTicks(y0, y1) : niceTicks(y0, y1, 5);
  ctx.strokeStyle = th.grid; ctx.fillStyle = th.dim; ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  xt.forEach(v => { const px = m.l + (v - x0) / (x1 - x0) * pw; ctx.beginPath(); ctx.moveTo(px, m.t); ctx.lineTo(px, m.t + ph); ctx.stroke(); ctx.fillText(spec.logx ? `10^${v}` : tickLabel(v), px, m.t + ph + 5); });
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  yt.forEach(v => { const py = m.t + ph - (v - y0) / (y1 - y0) * ph; ctx.beginPath(); ctx.moveTo(m.l, py); ctx.lineTo(m.l + pw, py); ctx.stroke(); ctx.fillText(spec.logy ? `10^${v}` : tickLabel(v), m.l - 6, py); });
  ctx.fillStyle = th.fg; ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
  ctx.fillText(`${spec.x.label}${spec.x.unit && spec.x.unit !== '–' && spec.x.unit !== '1' ? ` (${spec.x.unit})` : ''}`, m.l + pw / 2, h - 4);
  { const un = spec.yUnit && spec.yUnit !== '–' && spec.yUnit !== '1' ? ` (${spec.yUnit})` : ''; let name = spec.yLabel || ''; while (name.length > 8 && ctx.measureText(name + '…' + un).width > h - 8) name = name.slice(0, -2); if (name !== (spec.yLabel || '')) name = name.trimEnd() + '…';
    ctx.save(); ctx.translate(12, m.t + ph / 2); ctx.rotate(-Math.PI / 2); ctx.textBaseline = 'top'; ctx.fillText(name + un, 0, 0); ctx.restore(); }
  ctx.save(); ctx.beginPath(); ctx.rect(m.l, m.t, pw, ph); ctx.clip();
  // intervals over which the plotted quantity has no value
  if (spec.shade) spec.shade.forEach(z => { const a = Math.max(m.l, X(z.x0)), b = Math.min(m.l + pw, X(z.x1)); ctx.fillStyle = th.dim; ctx.globalAlpha = 0.16; ctx.fillRect(a, m.t, Math.max(2, b - a), ph); ctx.globalAlpha = 0.7; ctx.strokeStyle = th.dim; ctx.lineWidth = 1; ctx.beginPath(); for (let u = a - ph; u < b; u += 9) { ctx.moveTo(Math.max(a, u), m.t + ph - Math.max(0, a - u)); ctx.lineTo(Math.min(b, u + ph), m.t + ph - Math.min(ph, b - u)); } ctx.stroke(); ctx.globalAlpha = 1; });
  if (spec.band) { ctx.fillStyle = PALETTE[0] + '33'; ctx.beginPath(); spec.x.data.forEach((v, i) => { const px = X(v), py = Y(spec.band.hi[i]); i ? ctx.lineTo(px, py) : ctx.moveTo(px, py); }); for (let i = spec.x.data.length - 1; i >= 0; i--) ctx.lineTo(X(spec.x.data[i]), Y(spec.band.lo[i])); ctx.closePath(); ctx.fill(); }
  const draw = (xd, yd, color, dash, scatter, fill) => {
    ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = 2; ctx.setLineDash(dash ? [6, 4] : []);
    if (scatter) { xd.forEach((v, i) => { if (Number.isFinite(yd[i])) { ctx.beginPath(); ctx.arc(X(v), Y(yd[i]), 3, 0, 7); ctx.fill(); } }); return; }
    ctx.beginPath(); let pen = false;
    xd.forEach((v, i) => { const yy = yd[i]; if (!Number.isFinite(yy) || !Number.isFinite(tx(v)) || !Number.isFinite(ty(yy))) { pen = false; return; } const px = X(v), py = Y(yy); pen ? ctx.lineTo(px, py) : ctx.moveTo(px, py); pen = true; });
    ctx.stroke(); ctx.setLineDash([]);
    if (fill) { ctx.lineTo(X(xd[xd.length - 1]), m.t + ph); ctx.lineTo(X(xd[0]), m.t + ph); ctx.closePath(); ctx.globalAlpha = 0.18; ctx.fill(); ctx.globalAlpha = 1; }
  };
  const legend = [];
  if (spec.kind === 'bar') { const n = spec.x.data.length, bw = pw / n * 0.7; spec.y.forEach((s, k) => { ctx.fillStyle = PALETTE[k % 8]; s.data.forEach((v, i) => { const px = m.l + (i + 0.5) / n * pw - bw / 2 + k * bw / spec.y.length, py = Y(v), base = Y(Math.max(y0, Math.min(0, y1))); ctx.fillRect(px, Math.min(py, base), bw / spec.y.length, Math.abs(base - py)); }); legend.push([s.label, PALETTE[k % 8]]); }); }
  else spec.y.forEach((s, k) => { draw(spec.x.data, s.data, s.color || PALETTE[k % 8], s.dash, spec.kind === 'scatter' || s.scatter, spec.fill && k === 0); legend.push([s.label, s.color || PALETTE[k % 8], s.dash]); });
  (spec.overlay || []).forEach((o, k) => { const col = PALETTE[(spec.y.length + k) % 8]; draw(o.x, o.y, col, o.dash, o.scatter); legend.push([o.label, col, o.dash]); });
  if (spec.points && spec.pointsRing) { ctx.strokeStyle = '#f59e0b'; ctx.lineWidth = 2; spec.points.forEach(p => { ctx.beginPath(); ctx.arc(X(p.x), Y(p.y), 6, 0, 7); ctx.stroke(); }); legend.push([spec.pointsLabel || 'Check failed', '#f59e0b', false, true]); }
  else if (spec.points) { ctx.fillStyle = th.fg; ctx.strokeStyle = th.bg; spec.points.forEach(p => { ctx.beginPath(); ctx.arc(X(p.x), Y(p.y), 4.5, 0, 7); ctx.fill(); ctx.stroke(); }); if (spec.pointsLabel) legend.push([spec.pointsLabel, th.fg, false, true]); }
  if (spec.vline != null) { ctx.strokeStyle = th.dim; ctx.setLineDash([3, 3]); ctx.beginPath(); ctx.moveTo(X(spec.vline), m.t); ctx.lineTo(X(spec.vline), m.t + ph); ctx.stroke(); ctx.setLineDash([]); }
  ctx.restore();
  ctx.strokeStyle = th.dim; ctx.lineWidth = 1; ctx.strokeRect(m.l, m.t, pw, ph);
  if (legend.length > 1 || opts.legend) { ctx.font = '11px system-ui, sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; let lx = m.l + 8, ly = m.t + 10; legend.forEach(([label, col, dash, dot]) => { const tw = ctx.measureText(label).width + 30; if (lx + tw > m.l + pw) { lx = m.l + 8; ly += 15; } ctx.strokeStyle = col; ctx.fillStyle = col; ctx.lineWidth = 2; if (dot) { ctx.beginPath(); ctx.arc(lx + 8, ly, 3.5, 0, 7); ctx.fill(); } else { ctx.setLineDash(dash ? [4, 3] : []); ctx.beginPath(); ctx.moveTo(lx, ly); ctx.lineTo(lx + 16, ly); ctx.stroke(); ctx.setLineDash([]); } ctx.fillStyle = th.fg; ctx.fillText(label, lx + 21, ly); lx += tw + 6; }); }
  // hover read-out
  canvas._plot = { X, Y, m, pw, ph, spec, x0, x1, tx };
  if (!canvas._hover && !opts.static) {
    canvas._hover = true;
    const tip = document.createElement('div'); tip.className = 'plot-tip'; canvas.parentElement.style.position = 'relative'; canvas.parentElement.appendChild(tip);
    const move = ev => {
      const P = canvas._plot, r = canvas.getBoundingClientRect(), px = (ev.touches ? ev.touches[0].clientX : ev.clientX) - r.left;
      if (px < P.m.l || px > P.m.l + P.pw || P.spec.kind === 'bar') { tip.style.display = 'none'; return; }
      const xv = P.x0 + (px - P.m.l) / P.pw * (P.x1 - P.x0), d = P.spec.x.data; let bi = 0, bd = Infinity;
      for (let i = 0; i < d.length; i++) { const dd = Math.abs(P.tx(d[i]) - xv); if (dd < bd) { bd = dd; bi = i; } }
      tip.innerHTML = `<b>${fmt(d[bi], 4)}</b> ${P.spec.x.unit || ''}<br>` + P.spec.y.map((s, k) => `<span style="color:${s.color || PALETTE[k % 8]}">●</span> ${s.label}: ${fmt(s.data[bi], 5)}`).join('<br>');
      tip.style.display = 'block'; tip.style.left = Math.min(px + 12, r.width - 170) + 'px'; tip.style.top = '8px';
    };
    canvas.addEventListener('mousemove', move); canvas.addEventListener('touchmove', move, { passive: true }); canvas.addEventListener('mouseleave', () => { tip.style.display = 'none'; });
  }
}

const VIRIDIS = [[68, 1, 84], [72, 40, 120], [62, 74, 137], [49, 104, 142], [38, 130, 142], [31, 158, 137], [53, 183, 121], [109, 205, 89], [180, 222, 44], [253, 231, 37]];
const DIVERGE = [[33, 102, 172], [103, 169, 207], [209, 229, 240], [247, 247, 247], [253, 219, 199], [239, 138, 98], [178, 24, 43]];
const ramp = (t, map) => { t = Math.min(1, Math.max(0, t)) * (map.length - 1); const i = Math.min(map.length - 2, Math.floor(t)), f = t - i; return map[i].map((c, k) => Math.round(c + (map[i + 1][k] - c) * f)); };
const CATS = [[76, 201, 240], [247, 37, 133], [255, 209, 102], [6, 214, 160], [179, 136, 255], [255, 140, 66]];

/** Heat map of a 2-D field. f: {data[ny][nx], extent, xLabel, yLabel, unit, vectors:{u,v}, categories, marker} */
export function heatmap(canvas, f, opts = {}) {
  const H = opts.height || 340, { ctx, w, h } = setup(canvas, H), th = theme(canvas);
  const ny = f.data.length, nx = f.data[0].length, cat = f.categories;
  const m = { l: 58, r: cat ? 14 : 74, t: 12, b: cat ? 62 : 42 }, pw = w - m.l - m.r, ph = h - m.t - m.b;
  let lo = Infinity, hi = -Infinity; for (const r of f.data) for (const v of r) if (Number.isFinite(v)) { if (v < lo) lo = v; if (v > hi) hi = v; }
  if (lo === hi) hi = lo + 1;
  const div = !cat && lo < 0 && hi > 0 && f.diverging !== false; if (div) { const a = Math.max(-lo, hi); lo = -a; hi = a; }
  const off = document.createElement('canvas'); off.width = nx; off.height = ny; const oc = off.getContext('2d'), img = oc.createImageData(nx, ny);
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) { const v = f.data[ny - 1 - j][i], c = cat ? CATS[Math.round(v) % CATS.length] : Number.isFinite(v) ? ramp((v - lo) / (hi - lo), div ? DIVERGE : VIRIDIS) : [40, 40, 40], o = 4 * (j * nx + i); img.data[o] = c[0]; img.data[o + 1] = c[1]; img.data[o + 2] = c[2]; img.data[o + 3] = 255; }
  oc.putImageData(img, 0, 0); ctx.imageSmoothingEnabled = !cat && nx * ny > 400; ctx.drawImage(off, m.l, m.t, pw, ph);
  const [x0, x1, y0, y1] = f.extent || [0, nx - 1, 0, ny - 1];
  if (f.vectors) { const { u, v } = f.vectors; let mx = 0; for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) mx = Math.max(mx, Math.hypot(u[j][i], v[j][i])); const sx = Math.max(1, Math.round(nx / 22)), sy = Math.max(1, Math.round(ny / 16)), L = Math.min(pw / nx * sx, ph / ny * sy) * 0.9; ctx.strokeStyle = 'rgba(255,255,255,.85)'; ctx.fillStyle = 'rgba(255,255,255,.85)'; ctx.lineWidth = 1; for (let j = Math.floor(sy / 2); j < ny; j += sy) for (let i = Math.floor(sx / 2); i < nx; i += sx) { const a = Math.hypot(u[j][i], v[j][i]) / (mx || 1); if (a < 0.02) continue; const px = m.l + (i + 0.5) / nx * pw, py = m.t + ph - (j + 0.5) / ny * ph, dx = u[j][i] / (mx || 1) * L, dy = -v[j][i] / (mx || 1) * L; ctx.beginPath(); ctx.moveTo(px - dx / 2, py - dy / 2); ctx.lineTo(px + dx / 2, py + dy / 2); ctx.stroke(); const an = Math.atan2(dy, dx); ctx.beginPath(); ctx.moveTo(px + dx / 2, py + dy / 2); ctx.lineTo(px + dx / 2 - 4 * Math.cos(an - 0.5), py + dy / 2 - 4 * Math.sin(an - 0.5)); ctx.lineTo(px + dx / 2 - 4 * Math.cos(an + 0.5), py + dy / 2 - 4 * Math.sin(an + 0.5)); ctx.fill(); } }
  if (f.marker) { const px = m.l + (f.marker[0] - x0) / (x1 - x0) * pw, py = m.t + ph - (f.marker[1] - y0) / (y1 - y0) * ph; ctx.strokeStyle = '#fff'; ctx.lineWidth = 2.5; ctx.beginPath(); ctx.arc(px, py, 7, 0, 7); ctx.stroke(); ctx.strokeStyle = '#000'; ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(px, py, 9, 0, 7); ctx.stroke(); }
  ctx.font = '11px system-ui, sans-serif'; ctx.fillStyle = th.dim; ctx.strokeStyle = th.dim; ctx.lineWidth = 1; ctx.strokeRect(m.l, m.t, pw, ph);
  ctx.textAlign = 'center'; ctx.textBaseline = 'top'; niceTicks(x0, x1, 5).forEach(v => ctx.fillText(tickLabel(v), m.l + (v - x0) / (x1 - x0) * pw, m.t + ph + 5));
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle'; niceTicks(y0, y1, 5).forEach(v => ctx.fillText(tickLabel(v), m.l - 6, m.t + ph - (v - y0) / (y1 - y0) * ph));
  ctx.fillStyle = th.fg; ctx.textAlign = 'center'; ctx.textBaseline = 'bottom'; ctx.fillText(f.xLabel || '', m.l + pw / 2, m.t + ph + 34);
  ctx.save(); ctx.translate(12, m.t + ph / 2); ctx.rotate(-Math.PI / 2); ctx.textBaseline = 'top'; ctx.fillText(f.yLabel || '', 0, 0); ctx.restore();
  if (cat) { ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; let lx = m.l; cat.forEach((c, k) => { ctx.fillStyle = `rgb(${CATS[k % CATS.length]})`; ctx.fillRect(lx, h - 14, 11, 11); ctx.fillStyle = th.fg; ctx.fillText(c, lx + 15, h - 8); lx += ctx.measureText(c).width + 30; }); }
  else { const bx = m.l + pw + 12; for (let k = 0; k < ph; k++) { const c = ramp(1 - k / ph, div ? DIVERGE : VIRIDIS); ctx.fillStyle = `rgb(${c})`; ctx.fillRect(bx, m.t + k, 12, 1.5); } ctx.fillStyle = th.dim; ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; niceTicks(lo, hi, 5).forEach(v => ctx.fillText(tickLabel(v), bx + 16, m.t + ph - (v - lo) / (hi - lo) * ph)); ctx.fillStyle = th.fg; ctx.textBaseline = 'top'; ctx.fillText(f.unit || '', bx - 2, m.t + ph + 8); }
}

/** Animation controller: returns {play, pause, toggle, seek, destroy}; calls onFrame(i). */
export function player(n, drawFrame, { fps = 20, onFrame } = {}) {
  let i = 0, raf = null, last = 0, playing = false;
  const step = t => { if (!playing) return; if (t - last >= 1000 / fps) { last = t; i = (i + 1) % n; drawFrame(i); onFrame && onFrame(i); } raf = requestAnimationFrame(step); };
  const api = { play() { if (!playing) { playing = true; raf = requestAnimationFrame(step); } }, pause() { playing = false; if (raf) cancelAnimationFrame(raf); }, toggle() { playing ? api.pause() : api.play(); return playing; }, seek(k) { i = Math.max(0, Math.min(n - 1, k)); drawFrame(i); onFrame && onFrame(i); }, get playing() { return playing; }, get frame() { return i; }, destroy() { api.pause(); } };
  drawFrame(0);
  return api;
}
/** Draw one frame of an animated profile. */
export function profileFrame(canvas, a, k, opts = {}) {
  const yr = a.yRange || extent(a.frames);
  lineChart(canvas, { x: a.x, y: [{ label: `t = ${fmt(a.times[k], 3)} ${a.tUnit || 's'}`, data: a.frames[k] }], yLabel: a.yLabel, yUnit: a.yUnit, yRange: yr[0] === yr[1] ? null : [yr[0] - 0.04 * (yr[1] - yr[0]), yr[1] + 0.04 * (yr[1] - yr[0])], fill: a.fill }, { ...opts, static: true, legend: true });
}
/** Draw one frame of planar particle motion with trails. */
export function motionFrame(canvas, a, k, opts = {}) {
  const H = opts.height || 340, { ctx, w, h } = setup(canvas, H), th = theme(canvas);
  let b = a.bounds; if (!b) { const xs = a.frames.flatMap(f => f.map(p => p[0])), ys = a.frames.flatMap(f => f.map(p => p[1])); b = [Math.min(...xs), Math.max(...xs), Math.min(...ys), Math.max(...ys)]; const px = (b[1] - b[0]) * 0.08 || 1, py = (b[3] - b[2]) * 0.08 || 1; b = [b[0] - px, b[1] + px, b[2] - py, b[3] + py]; a.bounds = b; }
  const s = Math.min((w - 30) / (b[1] - b[0]), (h - 30) / (b[3] - b[2])), cx = w / 2 - (b[0] + b[1]) / 2 * s, cy = h / 2 + (b[2] + b[3]) / 2 * s;
  const X = x => cx + x * s, Y = y => cy - y * s;
  ctx.strokeStyle = th.grid; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(0, Y(0)); ctx.lineTo(w, Y(0)); ctx.moveTo(X(0), 0); ctx.lineTo(X(0), h); ctx.stroke();
  (a.statics || []).forEach(o => { ctx.strokeStyle = th.dim; ctx.fillStyle = th.grid; ctx.beginPath(); if (o.circle) { ctx.arc(X(o.circle[0]), Y(o.circle[1]), Math.max(2, o.circle[2] * s), 0, 7); o.fill ? ctx.fill() : ctx.stroke(); } else if (o.line) { ctx.moveTo(X(o.line[0]), Y(o.line[1])); ctx.lineTo(X(o.line[2]), Y(o.line[3])); ctx.stroke(); } });
  const np = a.frames[0].length, trail = a.trails === false ? 0 : (a.trailLength || a.frames.length);
  for (let p = 0; p < np; p++) {
    const col = PALETTE[p % 8]; ctx.strokeStyle = col + '99'; ctx.lineWidth = 1.5; ctx.beginPath();
    for (let j = Math.max(0, k - trail); j <= k; j++) { const q = a.frames[j][p]; j === Math.max(0, k - trail) ? ctx.moveTo(X(q[0]), Y(q[1])) : ctx.lineTo(X(q[0]), Y(q[1])); }
    ctx.stroke();
  }
  if (a.links) { ctx.strokeStyle = th.fg; ctx.lineWidth = 2; a.links.forEach(([i, j]) => { const A = i < 0 ? (a.anchor || [0, 0]) : a.frames[k][i], B = a.frames[k][j]; ctx.beginPath(); ctx.moveTo(X(A[0]), Y(A[1])); ctx.lineTo(X(B[0]), Y(B[1])); ctx.stroke(); }); }
  a.frames[k].forEach((q, p) => { ctx.fillStyle = PALETTE[p % 8]; ctx.beginPath(); ctx.arc(X(q[0]), Y(q[1]), (a.radii && a.radii[p]) || 6, 0, 7); ctx.fill(); if (a.labels && a.labels[p]) { ctx.fillStyle = th.fg; ctx.font = '11px system-ui'; ctx.fillText(a.labels[p], X(q[0]) + 9, Y(q[1]) - 9); } });
  ctx.fillStyle = th.dim; ctx.font = '11px system-ui'; ctx.textAlign = 'left'; ctx.fillText(`t = ${fmt(a.times[k], 4)} ${a.tUnit || 's'}`, 10, 16);
}

/**
 * Rotatable 3-D view. content: {paths:[{label,x,y,z}], points: flat xyz[], tris:{idx, pts}}.
 * Drag to rotate, wheel or pinch to zoom.
 */
export function view3d(canvas, content, opts = {}) {
  const H = opts.height || 360; let az = opts.az ?? 0.7, el = opts.el ?? 0.45, zoom = 1;
  const all = []; (content.paths || []).forEach(p => p.x.forEach((_, i) => all.push(p.x[i], p.y[i], p.z[i])));
  const pts = content.points || []; for (let i = 0; i < pts.length; i++) all.push(pts[i]);
  const mesh = content.tris && content.tris.pts ? content.tris : null; if (mesh) for (let i = 0; i < mesh.pts.length; i++) all.push(mesh.pts[i]);
  const mn = [Infinity, Infinity, Infinity], mx = [-Infinity, -Infinity, -Infinity];
  for (let i = 0; i < all.length; i += 3) for (let k = 0; k < 3; k++) { const v = all[i + k]; if (v < mn[k]) mn[k] = v; if (v > mx[k]) mx[k] = v; }
  const c = mn.map((v, k) => (v + mx[k]) / 2), R = Math.max(...mx.map((v, k) => v - mn[k])) / 2 || 1;
  const draw = () => {
    const { ctx, w, h } = setup(canvas, H), th = theme(canvas), s = Math.min(w, h) * 0.42 / R * zoom;
    const ca = Math.cos(az), sa = Math.sin(az), ce = Math.cos(el), se = Math.sin(el);
    const P = (x, y, z) => { x -= c[0]; y -= c[1]; z -= c[2]; const x1 = x * ca - y * sa, y1 = x * sa + y * ca, y2 = y1 * se + z * ce, d = y1 * ce - z * se; return [w / 2 + x1 * s, h / 2 - y2 * s, d]; };
    // axes
    const o = P(mn[0], mn[1], mn[2]); [[mx[0], mn[1], mn[2], 'x'], [mn[0], mx[1], mn[2], 'y'], [mn[0], mn[1], mx[2], 'z']].forEach(([x, y, z, l]) => { const q = P(x, y, z); ctx.strokeStyle = th.dim; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(o[0], o[1]); ctx.lineTo(q[0], q[1]); ctx.stroke(); ctx.fillStyle = th.dim; ctx.font = '11px system-ui'; ctx.fillText(l, q[0] + 4, q[1]); });
    if (mesh) { const T = mesh.idx, V = mesh.pts, tris = []; for (let i = 0; i < T.length; i += 3) { const a = P(V[T[i] * 3], V[T[i] * 3 + 1], V[T[i] * 3 + 2]), b = P(V[T[i + 1] * 3], V[T[i + 1] * 3 + 1], V[T[i + 1] * 3 + 2]), d = P(V[T[i + 2] * 3], V[T[i + 2] * 3 + 1], V[T[i + 2] * 3 + 2]); const nz = (b[0] - a[0]) * (d[1] - a[1]) - (b[1] - a[1]) * (d[0] - a[0]); tris.push([a, b, d, (a[2] + b[2] + d[2]) / 3, Math.abs(nz)]); } tris.sort((p, q) => q[3] - p[3]); const mxA = Math.max(...tris.map(t => t[4])) || 1; tris.forEach(([a, b, d, , nz]) => { const sh = 0.35 + 0.65 * Math.min(1, nz / mxA * 3); ctx.fillStyle = `rgba(${Math.round(76 * sh)},${Math.round(201 * sh)},${Math.round(240 * sh)},0.9)`; ctx.strokeStyle = 'rgba(10,20,40,.35)'; ctx.lineWidth = 0.5; ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.lineTo(d[0], d[1]); ctx.closePath(); ctx.fill(); ctx.stroke(); }); }
    else if (pts.length) { ctx.fillStyle = th.accent; for (let i = 0; i < pts.length; i += 3) { const q = P(pts[i], pts[i + 1], pts[i + 2]); ctx.globalAlpha = 0.75; ctx.fillRect(q[0] - 1, q[1] - 1, 2, 2); } ctx.globalAlpha = 1; }
    (content.paths || []).forEach((p, k) => { ctx.strokeStyle = PALETTE[k % 8]; ctx.lineWidth = 1.8; ctx.beginPath(); p.x.forEach((_, i) => { const q = P(p.x[i], p.y[i], p.z[i]); i ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1]); }); ctx.stroke(); const e = P(p.x[p.x.length - 1], p.y[p.y.length - 1], p.z[p.z.length - 1]); ctx.fillStyle = PALETTE[k % 8]; ctx.beginPath(); ctx.arc(e[0], e[1], 3.5, 0, 7); ctx.fill(); if (p.label) { ctx.font = '11px system-ui'; ctx.fillText(p.label, e[0] + 6, e[1] - 6); } });
    (content.spheres || []).forEach(sp => { const q = P(sp.c[0], sp.c[1], sp.c[2]); ctx.fillStyle = sp.color || th.grid; ctx.strokeStyle = th.dim; ctx.beginPath(); ctx.arc(q[0], q[1], Math.max(2, sp.r * s), 0, 7); ctx.fill(); ctx.stroke(); });
  };
  let drag = null;
  const pos = e => (e.touches ? [e.touches[0].clientX, e.touches[0].clientY] : [e.clientX, e.clientY]);
  const down = e => { drag = pos(e); }, up = () => { drag = null; };
  const move = e => { if (!drag) return; const p = pos(e); az += (p[0] - drag[0]) * 0.01; el = Math.max(-1.5, Math.min(1.5, el + (p[1] - drag[1]) * 0.01)); drag = p; draw(); if (e.cancelable) e.preventDefault(); };
  canvas.addEventListener('mousedown', down); canvas.addEventListener('touchstart', down, { passive: true }); window.addEventListener('mouseup', up); window.addEventListener('touchend', up);
  canvas.addEventListener('mousemove', move); canvas.addEventListener('touchmove', move, { passive: false });
  canvas.addEventListener('wheel', e => { zoom *= e.deltaY < 0 ? 1.1 : 0.9; draw(); e.preventDefault(); }, { passive: false });
  canvas.style.cursor = 'grab'; canvas.style.touchAction = 'none';
  draw();
  return { redraw: draw };
}

/** Horizontal bars centred on zero (tornado chart) for sensitivities. rows: [{label, value}] */
export function tornado(canvas, rows, opts = {}) {
  const data = rows.filter(r => Number.isFinite(r.value)).sort((a, b) => Math.abs(b.value) - Math.abs(a.value)).slice(0, opts.max || 14);
  const H = Math.max(120, data.length * 24 + 40), { ctx, w, h } = setup(canvas, H), th = theme(canvas);
  const ml = Math.min(220, w * 0.42), pw = w - ml - 60, mx = Math.max(...data.map(r => Math.abs(r.value)), 1e-12), mid = ml + pw / 2;
  ctx.font = '11px system-ui, sans-serif'; ctx.strokeStyle = th.dim; ctx.beginPath(); ctx.moveTo(mid, 8); ctx.lineTo(mid, h - 22); ctx.stroke();
  data.forEach((r, i) => { const y = 12 + i * 24, len = r.value / mx * pw / 2; ctx.fillStyle = r.value >= 0 ? PALETTE[0] : PALETTE[1]; ctx.fillRect(Math.min(mid, mid + len), y, Math.abs(len), 16); ctx.fillStyle = th.fg; ctx.textAlign = 'right'; ctx.textBaseline = 'middle'; let t = r.label; while (ctx.measureText(t).width > ml - 12 && t.length > 6) t = t.slice(0, -2); ctx.fillText(t === r.label ? t : t + '…', ml - 6, y + 8); ctx.textAlign = len >= 0 ? 'left' : 'right'; ctx.fillStyle = th.dim; ctx.fillText(fmt(r.value, 3), mid + len + (len >= 0 ? 5 : -5), y + 8); });
  ctx.fillStyle = th.dim; ctx.textAlign = 'center'; ctx.fillText(opts.label || 'normalised sensitivity', mid, h - 8);
}

/** 2-D drawing preview (DXF polylines). */
export function drawing2d(canvas, d, opts = {}) {
  const H = opts.height || 340, { ctx, w, h } = setup(canvas, H), th = theme(canvas);
  if (!d || !d.bbox) return; const [mn, mx] = d.bbox, s = Math.min((w - 30) / ((mx[0] - mn[0]) || 1), (h - 30) / ((mx[1] - mn[1]) || 1));
  const X = x => 15 + (x - mn[0]) * s + (w - 30 - (mx[0] - mn[0]) * s) / 2, Y = y => h - 15 - (y - mn[1]) * s - (h - 30 - (mx[1] - mn[1]) * s) / 2;
  ctx.strokeStyle = th.accent; ctx.lineWidth = 1.2; d.segs.forEach(p => { ctx.beginPath(); p.forEach((q, i) => (i ? ctx.lineTo(X(q[0]), Y(q[1])) : ctx.moveTo(X(q[0]), Y(q[1])))); ctx.stroke(); });
}
export const canvasPng = canvas => new Promise(res => canvas.toBlob(b => (b ? b.arrayBuffer().then(a => res(new Uint8Array(a))) : res(null)), 'image/png'));
export { PALETTE };
