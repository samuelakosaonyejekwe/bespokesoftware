// Typesets every piece of mathematics on the page with LaTeX. Views already render equations
// through the typesetter; this pass catches what remains in running text and tables: numbers in
// scientific notation, units, dimensions, Greek symbols with subscripts, roots, and short formulas
// written inline. It runs on whatever is added to the page, so no view has to remember to call it.
import { tryUnit } from '../core/units.js';
import * as E from '../core/expr.js';

const SUP = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9', '⁻': '-', '⁺': '+' };
const SUB = { '₀': '0', '₁': '1', '₂': '2', '₃': '3', '₄': '4', '₅': '5', '₆': '6', '₇': '7', '₈': '8', '₉': '9' };
const sup = s => [...s].map(c => SUP[c] ?? c).join(''), sub = s => [...s].map(c => SUB[c] ?? c).join('');
const GREEK = { α: '\\alpha', β: '\\beta', γ: '\\gamma', δ: '\\delta', ε: '\\varepsilon', ζ: '\\zeta', η: '\\eta', θ: '\\theta', κ: '\\kappa', λ: '\\lambda', μ: '\\mu', µ: '\\mu', ν: '\\nu', ξ: '\\xi', π: '\\pi', ρ: '\\rho', σ: '\\sigma', τ: '\\tau', φ: '\\varphi', χ: '\\chi', ψ: '\\psi', ω: '\\omega', Γ: '\\Gamma', Δ: '\\Delta', Θ: '\\Theta', Λ: '\\Lambda', Σ: '\\Sigma', Φ: '\\Phi', Ψ: '\\Psi', Ω: '\\Omega', ħ: '\\hbar', ℓ: '\\ell', '∞': '\\infty', '∇': '\\nabla', '∂': '\\partial' };

const UNIT_NAME = { ohm: '\\Omega', Ω: '\\Omega', '°C': '^{\\circ}\\mathrm{C}', '°F': '^{\\circ}\\mathrm{F}', '°': '^{\\circ}', deg: '^{\\circ}', '%': '\\%', um: '\\mu\\mathrm{m}', µm: '\\mu\\mathrm{m}', μm: '\\mu\\mathrm{m}', us: '\\mu\\mathrm{s}', uF: '\\mu\\mathrm{F}', uA: '\\mu\\mathrm{A}', uSv: '\\mu\\mathrm{Sv}', degC: '^{\\circ}\\mathrm{C}' };
/** LaTeX for a unit string such as "W/(m^2 K)". */
export function unitTex(u) {
  const s = String(u || '').trim(); if (!s || s === '1' || s === '–' || s === '-') return '';
  return s.replace(/[A-Za-zµμΩ°%]+/g, m => UNIT_NAME[m] || `\\mathrm{${m}}`).replace(/\^\(?(-?[\d/.]+)\)?/g, '^{$1}').replace(/[ ·*.](?=[\\(^])/g, '\\,').replace(/\//g, '/');
}
/** LaTeX for a number, using ×10ⁿ form when large or small. */
export function numTex(x, sig = 4) {
  if (x == null || Number.isNaN(x)) return '\\text{—}';
  if (!Number.isFinite(x)) return x > 0 ? '\\infty' : '-\\infty';
  if (x === 0) return '0';
  const a = Math.abs(x);
  if (a >= 1e5 || a < 1e-3) { const [m, e] = x.toExponential(sig - 1).split('e'); const mm = parseFloat(m); return `${mm === 1 ? '' : mm === -1 ? '-' : `${mm}\\times `}10^{${parseInt(e, 10)}}`; }
  return String(parseFloat(x.toPrecision(sig)));
}
const K = (tex, text) => { try { return window.katex.renderToString(tex, { throwOnError: true, strict: 'ignore', output: 'html' }); } catch { return null; } };
export const qtyHtml = (x, unit, sig) => K(`${numTex(x, sig)}${unitTex(unit) ? `\\,${unitTex(unit)}` : ''}`) || null;

const UNIT_CAND = /(?<![\w^.])((?:[A-Za-zµμΩ°]{1,6}(?:\^\(?-?[\d/]+\)?)?)(?:(?:[ ·]|\/\(?)(?:[A-Za-zµμΩ°]{1,6}(?:\^\(?-?[\d/]+\)?)?)\)?)*)(?![\w^])/g;
const RULES = [
  // 1.23×10⁻⁵ and 1.23×10^-5
  [/(-?\d+(?:\.\d+)?)\s?×\s?10(?:([⁻⁺⁰¹²³⁴-⁹]+)|\^\{?(-?\d+)\}?)/g, m => `${m[1]}\\times10^{${m[2] ? sup(m[2]) : m[3]}}`],
  [/(?<![\w.])10([⁻⁺⁰¹²³⁴-⁹]+)/g, m => `10^{${sup(m[1])}}`],
  // dimensions [M L^-1 T^-2]
  [/\[((?:[MLTIΘNJ](?:\^-?[\d/]+)?)(?: (?:[MLTIΘNJ](?:\^-?[\d/]+)?))*)\]/g, m => `[\\mathsf{${m[1].replace(/\^(-?[\d/]+)/g, '}^{$1}\\mathsf{').replace(/ /g, '\\,')}}]`.replace(/\\mathsf\{\}/g, '')],
  // roots √(…) and √x
  [/√\(([^()]{1,40})\)/g, m => `\\sqrt{${inline(m[1])}}`], [/√([A-Za-z0-9α-ωΑ-Ω]+)/g, m => `\\sqrt{${inline(m[1])}}`],
  // symbols with unicode sub/superscripts: T₀, m², s⁻¹, ρ₀, λ²
  [/([A-Za-zα-ωΑ-Ωµħℓ])([₀-₉]+)([⁻⁺⁰¹²³⁴-⁹]*)/g, m => `${GREEK[m[1]] || m[1]}_{${sub(m[2])}}${m[3] ? `^{${sup(m[3])}}` : ''}`],
  [/([A-Za-zα-ωΑ-Ωµ]{1,3})([⁻⁺⁰¹²³⁴-⁹]+)/g, m => `${[...m[1]].map(c => GREEK[c] || c).join('')}^{${sup(m[2])}}`.replace(/^([A-Za-z]{2,3})\^/, '\\mathrm{$1}^')],
  // isolated Greek letters and operators used as symbols
  [/(?<![A-Za-zα-ωΑ-Ω])([α-ωΓΔΘΛΣΦΨΩħℓ∇∂∞])(?![A-Za-zα-ωΑ-Ω])/g, m => GREEK[m[1]]],
  [/≤/g, () => '\\le'], [/≥/g, () => '\\ge'], [/≠/g, () => '\\ne'], [/≈/g, () => '\\approx'], [/∝/g, () => '\\propto'], [/±/g, () => '\\pm'],
];
function inline(s) { return [...s].map(c => GREEK[c] || (c === '·' ? '\\cdot ' : c === '×' ? '\\times ' : c === '−' ? '-' : c)).join('').replace(/([₀-₉]+)/g, (_, d) => `_{${sub(d)}}`).replace(/([⁻⁺⁰¹²³⁴-⁹]+)/g, (_, d) => `^{${sup(d)}}`); }

/** Convert one text string to HTML with typeset mathematics, or return null when nothing in it is mathematical. */
export function mathHtml(text) {
  if (!window.katex || !/[×√^₀-₉⁰¹²³⁴-⁹⁻α-ωΓΔΘΛΣΦΨΩµħℓ≤≥≠≈∝±∇∂∞/]/.test(text)) return null;
  const spans = [];
  const claim = (start, end, tex) => { if (spans.some(s => start < s.end && end > s.start)) return; const h = K(tex); if (h) spans.push({ start, end, h }); };
  for (const [re, f] of RULES) { re.lastIndex = 0; let m; while ((m = re.exec(text))) { claim(m.index, m.index + m[0].length, f(m)); if (m[0].length === 0) re.lastIndex++; } }
  UNIT_CAND.lastIndex = 0; let m;
  while ((m = UNIT_CAND.exec(text))) {
    let c = m[1]; if (!/[\^/]/.test(c) || c.length > 28) continue;
    const open = (c.match(/\(/g) || []).length, close = (c.match(/\)/g) || []).length; if (open > close) c += ')'.repeat(open - close);
    if (!tryUnit(c)) continue;
    // a number directly before the unit is typeset together with it
    const before = /(-?\d+(?:\.\d+)?)\s$/.exec(text.slice(0, m.index));
    if (before && !spans.some(s => m.index - before[0].length < s.end && m.index > s.start)) claim(m.index - before[0].length, m.index + m[1].length, `${before[1]}\\,${unitTex(c)}`); else claim(m.index, m.index + m[1].length, unitTex(c));
  }
  if (!spans.length) return null;
  spans.sort((a, b) => a.start - b.start);
  const esc = s => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  let out = '', pos = 0; for (const s of spans) { out += esc(text.slice(pos, s.start)) + `<span class="mx">${s.h}</span>`; pos = s.end; }
  return out + esc(text.slice(pos));
}

const SKIP = 'input,textarea,select,option,pre,script,style,canvas,svg,.katex,.mx,[contenteditable],.nomath,title';
function codeFormula(el) {
  const t = el.textContent.trim(); if (t.length < 3 || t.length > 180 || !/[=+*/^(]/.test(t) || /^[0-9a-f]{16,}$/i.test(t) || /[<>{}\[\];:"'\\|&#@$?!]|->|\s{2,}/.test(t) || /^\.|^[a-z]+\.[a-z]+$/i.test(t)) return;
  const parts = t.split('=').map(s => s.trim()); if (parts.length > 2 || parts.some(p => !p)) return;
  try { const tex = parts.map(p => E.toTex(E.parse(p))).join(' = '); const h = K(tex); if (h) { el.innerHTML = h; el.classList.add('mx'); el.style.background = 'none'; } } catch { /* not a formula: leave it as code */ }
}
/** Diagram labels: symbols in italics with true subscripts and superscripts (SVG text cannot hold the typesetter's markup). */
function diagramLabels(root) {
  const list = root.matches && root.matches('svg.dgm text') ? [root] : root.querySelectorAll ? root.querySelectorAll('svg.dgm text:not([data-mx])') : [];
  list.forEach(t => {
    t.setAttribute('data-mx', '1'); const txt = t.textContent; if (!/[_^₀-₉⁰¹²³⁴-⁹⁻]|[A-Za-z]\s?=/.test(txt)) return;
    const escx = x => x.replace(/&/g, '&amp;').replace(/</g, '&lt;');
    t.innerHTML = escx(txt)
      .replace(/([A-Za-zα-ωΑ-Ωµ]+)_([A-Za-z0-9]+)/g, '<tspan font-style="italic">$1</tspan><tspan baseline-shift="sub" font-size="72%">$2</tspan>')
      .replace(/([A-Za-zα-ωΑ-Ωµ])([₀-₉]+)/g, (_, a, d) => `<tspan font-style="italic">${a}</tspan><tspan baseline-shift="sub" font-size="72%">${sub(d)}</tspan>`)
      .replace(/\^(-?\d+)/g, '<tspan baseline-shift="super" font-size="72%">$1</tspan>').replace(/([⁻⁺⁰¹²³⁴-⁹]+)/g, (_, d) => `<tspan baseline-shift="super" font-size="72%">${sup(d)}</tspan>`)
      .replace(/(^|[\s(,])([A-Za-zα-ωΑ-Ω])(?=\s?=)/g, '$1<tspan font-style="italic">$2</tspan>');
  });
}
function walk(root) {
  if (root.nodeType === 3) { visit(root); return; }
  if (root.nodeType === 1) diagramLabels(root);
  if (root.nodeType !== 1 || root.closest(SKIP)) return;
  root.querySelectorAll('code').forEach(c => { if (!c.closest('pre,.katex,.mx,.nomath')) codeFormula(c); });
  const tw = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, { acceptNode: n => (n.parentElement && !n.parentElement.closest(SKIP) && n.nodeValue.length > 1 ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT) });
  const nodes = []; while (tw.nextNode()) nodes.push(tw.currentNode);
  nodes.forEach(visit);
}
function visit(node) {
  if (!node.parentElement || node.parentElement.closest(SKIP)) return;
  const h = mathHtml(node.nodeValue); if (!h) return;
  const span = document.createElement('span'); span.innerHTML = h; node.replaceWith(...span.childNodes);
}
/** Typeset everything under root now, and everything added to it later. */
export function watch(root) {
  let queue = new Set(), pending = false;
  const flush = () => { pending = false; const q = [...queue]; queue = new Set(); q.forEach(n => { if (n.isConnected) walk(n); }); };
  new MutationObserver(list => { for (const r of list) { r.addedNodes.forEach(n => { if (n.nodeType === 1 ? !n.closest('.katex,.mx') : n.nodeType === 3) queue.add(n); }); if (r.type === 'characterData' && r.target.parentElement && !r.target.parentElement.closest(SKIP)) queue.add(r.target); } if (queue.size && !pending) { pending = true; requestAnimationFrame(flush); } }).observe(root, { childList: true, subtree: true, characterData: true });
  walk(root);
}
