// Reusable result widgets: chart cards, field maps, animation players, 3-D views, equation cards.
import { html, raw, join, esc, chip, tex, on, $, $$, toast, showScalar } from './dom.js';
import { lineChart, heatmap, player, profileFrame, motionFrame, view3d, canvasPng } from '../core/plot.js';
import { seriesCsv, download, slug } from '../core/exporters.js';
import { fmt } from '../core/units.js';

const tools = (kind, id) => html`<span class="row" style="gap:.3rem"><button class="btn sm ghost" data-png="${kind}:${id}" title="Save this figure as an image">PNG</button>${kind === 'series' ? html`<button class="btn sm ghost" data-csv="${id}" title="Save the plotted numbers">CSV</button>` : ''}</span>`;
export const seriesCard = s => html`<div class="card"><div class="row spread"><h3>${s.title}${s.status === 'hypothetical' ? chip('conditional', 'hypo', 'Depends on a hypothetical closure') : ''}</h3>${tools('series', s.id)}</div><div class="plot"><canvas class="pl" data-series="${s.id}"></canvas></div>${s.note ? html`<p class="small dim">${s.note}</p>` : ''}</div>`;
export const fieldCard = f => html`<div class="card"><div class="row spread"><h3>${f.title}</h3>${tools('field', f.id)}</div><div class="plot"><canvas class="pl" data-field="${f.id}"></canvas></div>${f.note ? html`<p class="small dim">${f.note}</p>` : ''}</div>`;
export const animCard = a => html`<div class="card"><div class="row spread"><h3>${a.title}</h3><span class="row" style="gap:.3rem"><button class="btn sm ghost" data-video="${a.id}" title="Record the animation as a video file">Video</button>${tools('anim', a.id)}</span></div><div class="plot"><canvas class="pl" data-anim="${a.id}"></canvas></div>
  <div class="player"><button class="btn sm" data-play="${a.id}" aria-label="Play or pause">▶ Play</button><input type="range" min="0" max="${a.frames.length - 1}" value="0" data-seek="${a.id}" aria-label="Time"><span class="small dim" data-time="${a.id}" style="min-width:86px;text-align:right"></span></div></div>`;
export const pathCard = p => html`<div class="card"><div class="row spread"><h3>${p.title}</h3>${tools('path', p.id)}</div><div class="plot"><canvas class="pl" data-path="${p.id}"></canvas></div><p class="small dim">Drag to rotate; scroll or pinch to zoom.</p></div>`;

/** Draw every result canvas found under root and wire players and downloads. Returns a disposer. */
export function drawResults(root, result, extra = {}) {
  const players = {}, find = (arr, id) => (arr || []).find(x => x.id === id);
  $$('canvas[data-series]', root).forEach(cv => { const s = find(result.series, cv.dataset.series) || (extra.series || {})[cv.dataset.series]; if (s) lineChart(cv, s); });
  $$('canvas[data-field]', root).forEach(cv => { const f = find(result.fields, cv.dataset.field); if (f) heatmap(cv, f); });
  $$('canvas[data-path]', root).forEach(cv => { const p = find(result.paths, cv.dataset.path) || (extra.paths || {})[cv.dataset.path]; if (p) view3d(cv, p); });
  $$('canvas[data-anim]', root).forEach(cv => {
    const a = find(result.anims, cv.dataset.anim); if (!a) return;
    const draw = k => (a.kind === 'motion' ? motionFrame(cv, a, k) : profileFrame(cv, a, k));
    const seek = $(`[data-seek="${a.id}"]`, root), time = $(`[data-time="${a.id}"]`, root);
    players[a.id] = player(a.frames.length, draw, { fps: 18, onFrame: k => { if (seek) seek.value = k; if (time) time.textContent = `t = ${fmt(a.times[k], 3)} ${a.tUnit || 's'}`; } });
    if (time) time.textContent = `t = ${fmt(a.times[0], 3)} ${a.tUnit || 's'}`;
  });
  const click = async ev => {
    const pb = ev.target.closest('[data-play]'); if (pb && players[pb.dataset.play]) { const on_ = players[pb.dataset.play].toggle(); pb.textContent = on_ ? '❚❚ Pause' : '▶ Play'; return; }
    const png = ev.target.closest('[data-png]'); if (png) { const [kind, id] = png.dataset.png.split(':'); const cv = $(`canvas[data-${kind}="${id}"]`, root); if (cv) { const b = await canvasPng(cv); if (b) download(`${slug(id)}.png`, new Blob([b], { type: 'image/png' })); } return; }
    const csv = ev.target.closest('[data-csv]'); if (csv) { const s = find(result.series, csv.dataset.csv) || (extra.series || {})[csv.dataset.csv]; if (s) download(`${slug(s.id)}.csv`, seriesCsv(s), 'text/csv'); return; }
    const vid = ev.target.closest('[data-video]'); if (vid) { recordVideo($(`canvas[data-anim="${vid.dataset.video}"]`, root), players[vid.dataset.video], find(result.anims, vid.dataset.video)); }
  };
  const input = ev => { const s = ev.target.closest('[data-seek]'); if (s && players[s.dataset.seek]) { players[s.dataset.seek].pause(); const b = $(`[data-play="${s.dataset.seek}"]`, root); if (b) b.textContent = '▶ Play'; players[s.dataset.seek].seek(+s.value); } };
  root.addEventListener('click', click); root.addEventListener('input', input);
  const redraw = () => { $$('canvas[data-series]', root).forEach(cv => { const s = find(result.series, cv.dataset.series) || (extra.series || {})[cv.dataset.series]; if (s) lineChart(cv, s); }); $$('canvas[data-field]', root).forEach(cv => { const f = find(result.fields, cv.dataset.field); if (f) heatmap(cv, f); }); Object.values(players).forEach(p => p.seek(p.frame)); };
  let rt; const onResize = () => { clearTimeout(rt); rt = setTimeout(redraw, 200); };
  window.addEventListener('resize', onResize);
  return () => { Object.values(players).forEach(p => p.destroy()); root.removeEventListener('click', click); root.removeEventListener('input', input); window.removeEventListener('resize', onResize); };
}
function recordVideo(canvas, pl, a) {
  if (!canvas || !pl || !canvas.captureStream || typeof MediaRecorder === 'undefined') { toast('Video recording is not supported by this browser. Use the PNG button for a still frame.'); return; }
  const type = ['video/webm;codecs=vp9', 'video/webm', 'video/mp4'].find(t => MediaRecorder.isTypeSupported(t)); if (!type) { toast('No supported video format on this device.'); return; }
  const rec = new MediaRecorder(canvas.captureStream(18), { mimeType: type }), chunks = [];
  rec.ondataavailable = e => e.data.size && chunks.push(e.data);
  rec.onstop = () => { download(`${slug(a.id)}.${type.includes('mp4') ? 'mp4' : 'webm'}`, new Blob(chunks, { type })); toast('Video saved'); };
  pl.pause(); pl.seek(0); rec.start(); pl.play(); toast('Recording one full pass…');
  setTimeout(() => { pl.pause(); rec.stop(); }, a.frames.length / 18 * 1000 + 300);
}

const KIND = { law: ['Fundamental law', 'ok'], derived: ['Derived', 'live'], closure: ['Closure relation', 'soft'], empirical: ['Empirical correlation', 'warn'], definition: ['Definition', 'mute'], hypothesis: ['Hypothesis', 'hypo'], boundary: ['Boundary condition', 'mute'], initial: ['Initial condition', 'mute'] };
const VER = { verified: ['Verified', 'ok'], conditional: ['Verified with a domain condition', 'warn'], singular: ['Singular term found and regularised', 'warn'], inconsistent: ['Dimensionally inconsistent', 'bad'], incomplete: ['Units incomplete', 'warn'], rejected: ['Does not parse', 'bad'] };
/** Equation card with origin, verification steps and any regularised or repaired form. */
export function equationCard(rec, q = {}, asm = [], extraBtn = '') {
  const mark = s => (s.ok === true ? '<span class="m y">✓</span>' : s.ok === false ? '<span class="m n">✕</span>' : '<span class="m c">◐</span>');
  return html`<div class="eq" id="eq-${rec.id}">
    <div class="eqhead"><b>${rec.name}</b>${chip(...(KIND[q.kind || rec.kind] || KIND.derived))}${chip(...(VER[rec.status] || VER.verified))}${extraBtn && extraBtn.__raw != null ? extraBtn : ''}</div>
    ${rec.tex ? tex(rec.tex, true) : html`<code>${rec.lhs} = ${rec.rhs}</code>`}
    ${q.origin ? html`<div class="small dim">Origin: ${q.origin}${q.needs && q.needs.length ? html` · relies on: ${q.needs.map(id => (asm.find(a => a.id === id) || { text: id }).text).join('; ')}` : ''}</div>` : ''}
    ${q.note ? html`<div class="small dim">${q.note}</div>` : ''}
    <ul class="steps">${join(rec.steps, s => raw(`<li>${mark(s)}<span><b>${esc(s.check)}.</b> ${esc(s.text)}</span></li>`))}</ul>
    ${rec.regularised ? html`<div class="note ok"><b>Regularised form — finite and smooth on the whole declared domain</b>${tex(rec.regularised.tex, true)}<span class="small">${rec.regularised.text}${rec.regularised.finite ? ` With ε = 10⁻⁶ in the units of the softened term, the right-hand side is bounded between ${fmt(rec.regularised.bound[0], 3)} and ${fmt(rec.regularised.bound[1], 3)}.` : ''}</span></div>` : ''}
    ${rec.repair ? html`<div class="note warn"><b>Proposed correction.</b> ${rec.repair.text}${join(rec.repair.candidates, (k, i) => html`<div class="row" style="margin-top:.4rem">${tex(k.tex)}<button class="btn sm" data-repair="${rec.id}:${i}">Adopt this amendment</button></div>`)}</div>` : ''}
  </div>`;
}
export const scalarsTable = (scalars) => raw(`<div class="tw"><table><thead><tr><th>Quantity</th><th>Symbol</th><th class="num">Value</th></tr></thead><tbody>${scalars.map(s => `<tr><td>${esc(s.name)}${s.status === 'hypothetical' ? ' <span class="chip hypo">conditional</span>' : ''}${s.note ? ` <span class="dim small">(${esc(s.note)})</span>` : ''}</td><td>${tex(symTexSafe(s.sym)).__raw}</td><td class="num"><b>${esc(showScalar(s))}</b></td></tr>`).join('')}</tbody></table></div>`);
import { symTex } from '../core/expr.js';
export const symTexSafe = s => { try { return symTex(s); } catch { return s; } };
export const statGrid = (scalars, n = 6) => raw(`<div class="grid g4">${scalars.slice(0, n).map(s => `<div class="stat"><div class="v">${esc(showScalar(s, 4))}</div><div class="l">${esc(s.name)}</div></div>`).join('')}</div>`);
