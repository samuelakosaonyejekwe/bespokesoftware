// Authoring kit and contract for simulation models.
//
// A MODEL is a plain object. Everything is optional except id, title, module, klass, domains,
// keywords, inputs, equations and solve. The engine supplies generic behaviour for the rest.
//
//   id          unique kebab-case string
//   title       short human title
//   module      1 (thought experiments), 2 (engineering) or [1, 2]
//   klass       'I' scientifically computable | 'II' logically analysable | 'III' speculative / counterfactual
//               (an array such as ['I','II'] marks a hybrid)
//   domains     array of DOMAIN keys (see js/data/domains.js)
//   keywords    array of lower-case words / phrases used to match a prompt; put the most specific first
//   summary     one-sentence description
//   background  paragraph(s) of established scientific context (string or array of strings)
//   phenomena   array of physical mechanisms involved
//   laws        array of LAW keys (see js/data/domains.js) the model rests on
//   refs        array of literature citations (strings); never invent a DOI
//   inputs      array built with inp(...)
//   assumptions array built with asm(...); each can be switched off by the user
//   symbols     { sym: [name, unit] } for every non-input symbol that appears in the equations
//   equations   (a, v) => array built with eq(...). `a` = { assumptionId: boolean }, `v` = SI input values
//   derivation  (a, v) => array of { text, tex? } steps from first principles
//   solve       (v, a) => result object built with the helpers below. v is in SI. MUST be deterministic,
//               must not throw for inputs inside their declared ranges, and should take well under 50 ms
//               (set heavy: true on the model when a single solve is slower than ~150 ms).
//   benchmarks  (v, a) => array built with bench(...): comparisons against exact / analytical results
//   validation  array of { name, ref, note?, cases: [{ inputs: {sym: SI value}, observable: 'scalar sym', observed, sigma? }] }
//               — published measurements used ONLY for comparison, never for tuning
//   diagram     (v, a) => SVG markup string (viewBox "0 0 640 360"), drawn with currentColor-friendly strokes
//   experiment  { objective, apparatus[], instruments[{name, measures, range, resolution}], procedure[],
//                 controls[], signatures[], safety[] }
//   falsify     array of statements: observations that would refute the model
//   alternatives array of { name, text } competing explanations / formulations
//   hazards     array of { hazard, cause, mitigation }
//   standards   array of strings naming codes that typically apply (identify, never claim compliance)
//   limits      string describing the validity envelope
//   numerics    { method, order?, stability?, resolution?: 'input sym controlling grid/time step' }
//   optimise    { objective: 'scalar sym', sense: 'min'|'max', vars: ['input syms'], note? }
//   inverse     { series: 'series id', curve?: index, fit: ['input syms'] } default reverse-engineering set-up
//   extensions  array of strings: natural next steps
//   hypothetical true when the model's central law is invented (class III); results are then labelled conditional
//
// RESULT object returned by solve():
//   { scalars: [scalar(...)], series: [line(...)], fields: [field(...)], anims: [anim(...)],
//     paths: [path3d(...)], checks: [check(...)], warnings: [strings], notes: [strings] }

import * as N from '../core/num.js';
import * as R from '../data/reference.js';
export { N, R };
export const C = Object.fromEntries(Object.entries(R.CONSTANTS).map(([k, v]) => [k, v.value]));

/** Input declaration. `value` is given in the display `unit`; the engine converts to SI for solve(). */
export const inp = (sym, name, unit, value, o = {}) => ({ sym, name, unit, value, kind: 'operating', ...o });
/** Constant of nature exposed as an input so that counterfactual worlds may change it. */
export const konst = (sym, o = {}) => {
  const c = R.CONSTANTS[sym];
  return { sym, name: c.name, unit: c.unit, value: c.value, kind: 'constant', src: c.src, min: c.value * 1e-3, max: c.value * 1e3, ...o };
};
/** Assumption: id, statement, {on, why, alt, affects} — `alt` says what replaces it when switched off. */
export const asm = (id, text, o = {}) => ({ id, text, on: true, ...o });
/**
 * Equation: id, name, lhs, rhs (strings in the expression grammar), then
 * { kind: 'law'|'derived'|'closure'|'empirical'|'definition'|'hypothesis'|'boundary'|'initial',
 *   origin: 'the principle or source it comes from', needs: ['assumption ids'], note }.
 * Grammar: + - * / ^, functions sqrt exp ln log10 sin cos tan tanh sinh cosh atan asin acos abs min max erf,
 * derivative operators d(y,t) d2(y,t) pd(u,x) pd2(u,x) lap(u) grad(u) div(u) int(f,x). Greek names
 * (rho, mu, sigma, omega, ...) and subscripts with underscore (T_in) render automatically.
 */
export const eq = (id, name, lhs, rhs, o = {}) => ({ id, name, lhs, rhs, kind: 'derived', ...o });

export const scalar = (sym, name, value, unit, o = {}) => ({ sym, name, value, unit, ...o });
/** Line/scatter chart. ys: [{label, data, dash?}]  opts: {logx, logy, kind:'scatter'|'bar', note, xUnit display} */
export const line = (id, title, xLabel, xUnit, xData, ys, yLabel, yUnit, o = {}) => ({ id, title, x: { label: xLabel, unit: xUnit, data: xData }, y: ys, yLabel, yUnit, kind: 'line', ...o });
/** 2-D scalar field on a regular grid. data: array of ny rows each of nx values. extent [x0,x1,y0,y1]. Optional vectors {u,v} (same shape). */
export const field = (id, title, data, extent, xLabel, yLabel, unit, o = {}) => ({ id, title, data, extent, xLabel, yLabel, unit, ...o });
/** Animated 1-D profile: frames[k] is the y-array at times[k] over the common x. */
export const anim = (id, title, xLabel, xUnit, xData, frames, times, yLabel, yUnit, o = {}) => ({ id, title, x: { label: xLabel, unit: xUnit, data: xData }, frames, times, yLabel, yUnit, kind: 'profile', ...o });
/** Animated particles / bodies in a plane: frames[k] = [[x,y], ...]; opts {trails, labels, bounds:[x0,x1,y0,y1]} */
export const motion = (id, title, frames, times, o = {}) => ({ id, title, frames, times, kind: 'motion', ...o });
/** 3-D trajectories: paths [{label, x:[], y:[], z:[]}] */
export const path3d = (id, title, paths, o = {}) => ({ id, title, paths, ...o });
/** Conservation / consistency check: |value| must be ≤ tol to pass. */
export const check = (name, value, tol, note = '') => ({ name, value, tol, pass: Math.abs(value) <= tol, note });
/** Analytical benchmark: computed vs exact. */
export const bench = (name, got, expected, ref = '', tol = 1e-3) => {
  const rel = expected !== 0 ? Math.abs(got - expected) / Math.abs(expected) : Math.abs(got);
  return { name, got, expected, rel, tol, pass: rel <= tol, ref };
};

// ---- small shared physics helpers -------------------------------------------------
/** Darcy friction factor: laminar 64/Re, Colebrook–White (solved iteratively) when turbulent, blended across transition. */
export function frictionFactor(Re, relRough = 0) {
  if (!(Re > 0)) return 0;
  const lam = 64 / Re;
  if (Re < 2000) return lam;
  let f = 0.25 / Math.log10(relRough / 3.7 + 5.74 / Math.pow(Re, 0.9)) ** 2;
  for (let i = 0; i < 30; i++) { const fn = 1 / (-2 * Math.log10(relRough / 3.7 + 2.51 / (Re * Math.sqrt(f)))) ** 2; if (Math.abs(fn - f) < 1e-12) { f = fn; break; } f = fn; }
  if (Re < 4000) { const w = (Re - 2000) / 2000; return lam * (1 - w) + f * w; }
  return f;
}
/** SVG helpers for diagrams. Use class names so the theme controls colour. */
export const svg = (body, w = 640, h = 360) => `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" class="dgm" role="img">${ARROW}${body}</svg>`;
const ARROW = '<defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" class="d-fill"/></marker></defs>';
export const S = {
  rect: (x, y, w, h, cls = 'd-body', rx = 4) => `<rect x="${x}" y="${y}" width="${w}" height="${h}" rx="${rx}" class="${cls}"/>`,
  line: (x1, y1, x2, y2, cls = 'd-line') => `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" class="${cls}"/>`,
  arrow: (x1, y1, x2, y2, cls = 'd-arrow') => `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" class="${cls}" marker-end="url(#ah)"/>`,
  circle: (cx, cy, r, cls = 'd-body') => `<circle cx="${cx}" cy="${cy}" r="${r}" class="${cls}"/>`,
  path: (d, cls = 'd-line') => `<path d="${d}" class="${cls}"/>`,
  text: (x, y, t, cls = 'd-text', anchor = 'middle') => `<text x="${x}" y="${y}" class="${cls}" text-anchor="${anchor}">${String(t).replace(/&/g, '&amp;').replace(/</g, '&lt;')}</text>`,
  dim: (x1, y1, x2, y2, label) => `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" class="d-dim" marker-start="url(#ah)" marker-end="url(#ah)"/>${S.text((x1 + x2) / 2, (y1 + y2) / 2 - 6, label, 'd-text d-small')}`,
  poly: (pts, cls = 'd-line') => `<polyline points="${pts.map(p => p.join(',')).join(' ')}" class="${cls}"/>`,
};
/** Number to tidy string for diagram labels. */
export const lab = (x, unit = '', sig = 3) => `${Number.isFinite(x) ? parseFloat(x.toPrecision(sig)) : '—'}${unit ? ' ' + unit : ''}`;
