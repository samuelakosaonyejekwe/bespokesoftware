// Equation discovery: dimensional analysis (Buckingham Π), symbolic regression over
// interpretable families, sparse identification of dynamics from time series, and
// information-criterion ranking with held-out testing.
import * as N from './num.js';
import { dimToString, isDimless, BASE } from './units.js';

// ---------------------------------------------------------------- Buckingham Π
const gcd = (a, b) => (b ? gcd(b, a % b) : Math.abs(a));
/** Rational null space of the dimension matrix. quantities: [{sym, dim}]. Returns Π groups as exponent maps. */
export function buckinghamPi(quantities) {
  const n = quantities.length;
  const rows = BASE.map((_, r) => quantities.map(q => q.dim[r])).filter(row => row.some(x => Math.abs(x) > 1e-12));
  const M = rows.map(r => r.slice());
  const pivots = []; let r = 0;
  for (let c = 0; c < n && r < M.length; c++) {
    let p = r; for (let i = r + 1; i < M.length; i++) if (Math.abs(M[i][c]) > Math.abs(M[p][c])) p = i;
    if (Math.abs(M[p][c]) < 1e-10) continue;
    [M[r], M[p]] = [M[p], M[r]];
    const d = M[r][c]; for (let k = 0; k < n; k++) M[r][k] /= d;
    for (let i = 0; i < M.length; i++) if (i !== r) { const f = M[i][c]; if (Math.abs(f) > 1e-12) for (let k = 0; k < n; k++) M[i][k] -= f * M[r][k]; }
    pivots.push(c); r++;
  }
  const free = quantities.map((_, i) => i).filter(i => !pivots.includes(i));
  const groups = free.map(fc => {
    const e = new Array(n).fill(0); e[fc] = 1;
    pivots.forEach((pc, i) => { e[pc] = -M[i][fc]; });
    // scale to small integers where possible
    let scale = 1;
    for (const q of [1, 2, 3, 4, 6]) if (e.every(x => Math.abs(x * q - Math.round(x * q)) < 1e-9)) { scale = q; break; }
    let ints = e.map(x => Math.round(x * scale * 1e9) / 1e9);
    if (ints.every(Number.isInteger)) { const g = ints.reduce((a, b) => gcd(a, b), 0) || 1; ints = ints.map(x => x / g); }
    return Object.fromEntries(quantities.map((q, i) => [q.sym, ints[i]]).filter(([, x]) => Math.abs(x) > 1e-12));
  });
  return { rank: pivots.length, nGroups: free.length, groups, repeating: pivots.map(i => quantities[i].sym), text: `${n} quantities span ${pivots.length} independent dimensions, so the relation among them reduces to one among ${free.length} dimensionless group${free.length === 1 ? '' : 's'}.` };
}
export function piToExpr(group) {
  const num = [], den = [];
  Object.entries(group).forEach(([k, e]) => { const a = Math.abs(e), s = a === 1 ? k : `${k}^${Number.isInteger(a) ? a : `(${a})`}`; (e > 0 ? num : den).push(s); });
  return (num.join('*') || '1') + (den.length ? `/(${den.join('*')})` : '');
}
/**
 * Candidate law for a target quantity: target = C · Π(other^a) when dimensions alone fix the exponents,
 * otherwise target = scale · f(Π₁, Π₂, …).
 */
export function dimensionalLaw(target, others) {
  const all = [target, ...others], pi = buckinghamPi(all);
  const withTarget = pi.groups.filter(g => g[target.sym]);
  if (!withTarget.length) return { ok: false, text: `${target.sym} cannot be formed from the other quantities on dimensional grounds: at least one further dimensional quantity is missing from the problem.`, pi };
  const g = withTarget[0], et = g[target.sym];
  const rhs = Object.fromEntries(Object.entries(g).filter(([k]) => k !== target.sym).map(([k, e]) => [k, -e / et]));
  const rest = pi.groups.filter(x => x !== g);
  return {
    ok: true, pi, exponents: rhs, unique: rest.length === 0,
    rhs: `C_0*${piToExpr(rhs)}`,
    text: rest.length === 0
      ? `Dimensional analysis fixes the form completely up to a pure number C₀, which must come from theory or experiment.`
      : `Dimensional analysis gives the scale; the remaining ${rest.length} dimensionless group(s) ${rest.map(piToExpr).join(', ')} enter through an undetermined function to be found from data or theory.`,
    remaining: rest,
  };
}

// ---------------------------------------------------------------- model families for regression
const ic = (n, k, sse) => { const s2 = Math.max(sse / n, 1e-300); return { aic: n * Math.log(s2) + 2 * k, bic: n * Math.log(s2) + k * Math.log(n) }; };
const split = n => { const tr = [], te = []; for (let i = 0; i < n; i++) ((i * 7 + 3) % 4 === 0 ? te : tr).push(i); return { tr, te }; };
const pick = (a, idx) => idx.map(i => a[i]);

const FAMILIES = [
  { id: 'linear', name: 'Linear', k: 2, expr: p => `${g(p[0])} + ${g(p[1])}*x`, f: (x, p) => p[0] + p[1] * x, init: (x, y) => { const r = N.linearRegression(x.map(v => [1, v]), y); return r.beta; } },
  { id: 'quadratic', name: 'Quadratic', k: 3, expr: p => `${g(p[0])} + ${g(p[1])}*x + ${g(p[2])}*x^2`, f: (x, p) => p[0] + p[1] * x + p[2] * x * x, init: (x, y) => N.linearRegression(x.map(v => [1, v, v * v]), y).beta },
  { id: 'cubic', name: 'Cubic', k: 4, expr: p => `${g(p[0])} + ${g(p[1])}*x + ${g(p[2])}*x^2 + ${g(p[3])}*x^3`, f: (x, p) => p[0] + p[1] * x + p[2] * x * x + p[3] * x ** 3, init: (x, y) => N.linearRegression(x.map(v => [1, v, v * v, v ** 3]), y).beta },
  { id: 'power', name: 'Power law', k: 2, need: 'pos', expr: p => `${g(p[0])}*x^${g(p[1])}`, f: (x, p) => p[0] * Math.pow(x, p[1]), init: (x, y) => { const ok = y.every(v => v > 0); if (!ok) return [N.mean(y), 1]; const r = N.linearRegression(x.map(v => [1, Math.log(v)]), y.map(Math.log)); return [Math.exp(r.beta[0]), r.beta[1]]; } },
  { id: 'power-offset', name: 'Power law with offset', k: 3, need: 'pos', expr: p => `${g(p[0])} + ${g(p[1])}*x^${g(p[2])}`, f: (x, p) => p[0] + p[1] * Math.pow(x, p[2]), init: (x, y) => [N.minOf(y) * 0.9, (N.maxOf(y) - N.minOf(y)) / Math.max(N.maxOf(x), 1e-12), 1] },
  { id: 'exponential', name: 'Exponential', k: 2, expr: p => `${g(p[0])}*exp(${g(p[1])}*x)`, f: (x, p) => p[0] * Math.exp(p[1] * x), init: (x, y) => { if (!y.every(v => v > 0)) return [y[0] || 1, -1 / (N.maxOf(x) - N.minOf(x) || 1)]; const r = N.linearRegression(x.map(v => [1, v]), y.map(Math.log)); return [Math.exp(r.beta[0]), r.beta[1]]; } },
  { id: 'exp-offset', name: 'Exponential approach to a limit', k: 3, expr: p => `${g(p[0])} + ${g(p[1])}*exp(-x/${g(p[2])})`, f: (x, p) => p[0] + p[1] * Math.exp(-x / p[2]), init: (x, y) => [y[y.length - 1], y[0] - y[y.length - 1], (N.maxOf(x) - N.minOf(x)) / 3 || 1] },
  { id: 'logarithmic', name: 'Logarithmic', k: 2, need: 'pos', expr: p => `${g(p[0])} + ${g(p[1])}*ln(x)`, f: (x, p) => p[0] + p[1] * Math.log(x), init: (x, y) => N.linearRegression(x.map(v => [1, Math.log(v)]), y).beta },
  { id: 'inverse', name: 'Inverse', k: 2, need: 'nonzero', expr: p => `${g(p[0])} + ${g(p[1])}/x`, f: (x, p) => p[0] + p[1] / x, init: (x, y) => N.linearRegression(x.map(v => [1, 1 / v]), y).beta },
  { id: 'inverse-square', name: 'Inverse square', k: 2, need: 'nonzero', expr: p => `${g(p[0])} + ${g(p[1])}/x^2`, f: (x, p) => p[0] + p[1] / (x * x), init: (x, y) => N.linearRegression(x.map(v => [1, 1 / (v * v)]), y).beta },
  { id: 'saturation', name: 'Saturation (Langmuir / Michaelis–Menten)', k: 2, need: 'pos', expr: p => `${g(p[0])}*x/(${g(p[1])} + x)`, f: (x, p) => p[0] * x / (p[1] + x), init: (x, y) => [N.maxOf(y) * 1.2, N.mean(x)] },
  { id: 'logistic', name: 'Logistic', k: 3, expr: p => `${g(p[0])}/(1 + exp(-(x - ${g(p[1])})/${g(p[2])}))`, f: (x, p) => p[0] / (1 + Math.exp(-(x - p[1]) / p[2])), init: (x, y) => [N.maxOf(y), N.mean(x), (N.maxOf(x) - N.minOf(x)) / 8 || 1] },
  { id: 'sinusoid', name: 'Sinusoid', k: 4, expr: p => `${g(p[0])} + ${g(p[1])}*sin(${g(p[2])}*x + ${g(p[3])})`, f: (x, p) => p[0] + p[1] * Math.sin(p[2] * x + p[3]), init: (x, y) => { const dt = (x[x.length - 1] - x[0]) / (x.length - 1) || 1; const sp = N.spectrum(y, dt); return [N.mean(y), (N.maxOf(y) - N.minOf(y)) / 2, 2 * Math.PI * (sp.peakFreq || 1 / (x[x.length - 1] - x[0] || 1)), 0]; } },
  { id: 'damped', name: 'Damped oscillation', k: 5, expr: p => `${g(p[0])} + ${g(p[1])}*exp(-x/${g(p[2])})*cos(${g(p[3])}*x + ${g(p[4])})`, f: (x, p) => p[0] + p[1] * Math.exp(-x / p[2]) * Math.cos(p[3] * x + p[4]), init: (x, y) => { const dt = (x[x.length - 1] - x[0]) / (x.length - 1) || 1; const sp = N.spectrum(y, dt); return [N.mean(y), (N.maxOf(y) - N.minOf(y)) / 2, (x[x.length - 1] - x[0]) / 2 || 1, 2 * Math.PI * (sp.peakFreq || 1), 0]; } },
  { id: 'gaussian', name: 'Gaussian peak', k: 3, expr: p => `${g(p[0])}*exp(-(x - ${g(p[1])})^2/(2*${g(p[2])}^2))`, f: (x, p) => p[0] * Math.exp(-((x - p[1]) ** 2) / (2 * p[2] * p[2])), init: (x, y) => { const i = y.indexOf(N.maxOf(y)); return [y[i], x[i], (N.maxOf(x) - N.minOf(x)) / 6 || 1]; } },
  { id: 'screened', name: 'Screened power law (Yukawa-type)', k: 4, need: 'pos', expr: p => `${g(p[0])}/x^${g(p[1])}*(1 + ${g(p[2])}*exp(-x/${g(p[3])}))`, f: (x, p) => p[0] / Math.pow(x, p[1]) * (1 + p[2] * Math.exp(-x / p[3])), init: (x, y) => { const r = N.linearRegression(x.map(v => [1, Math.log(v)]), y.map(v => Math.log(Math.abs(v) + 1e-300))); return [Math.exp(r.beta[0]), -r.beta[1], 0.1, N.mean(x)]; } },
  { id: 'stretched', name: 'Stretched exponential (memory relaxation)', k: 3, need: 'nonneg', expr: p => `${g(p[0])}*exp(-(x/${g(p[1])})^${g(p[2])})`, f: (x, p) => p[0] * Math.exp(-Math.pow(Math.max(x, 0) / p[1], p[2])), init: (x, y) => [y[0] || 1, (N.maxOf(x) - N.minOf(x)) / 3 || 1, 0.8] },
];
function g(v) { const s = Number.isFinite(v) ? parseFloat(v.toPrecision(6)) : 0; return s < 0 ? `(${s})` : String(s); }

/**
 * Fit every admissible family to (x, y), rank by BIC, and test each on held-out points.
 * Returns candidates sorted best-first with parameters, standard errors, fit and holdout metrics.
 */
export function symbolicRegression(x, y, opts = {}) {
  const n = x.length;
  if (n < 5) return { candidates: [], text: 'At least five data points are needed to compare candidate equations.' };
  const { tr, te } = split(n), xtr = pick(x, tr), ytr = pick(y, tr), xte = pick(x, te), yte = pick(y, te);
  const allPos = x.every(v => v > 0), nonZero = x.every(v => v !== 0), nonNeg = x.every(v => v >= 0);
  const out = [];
  for (const F of FAMILIES) {
    if (F.need === 'pos' && !allPos) continue;
    if (F.need === 'nonzero' && !nonZero) continue;
    if (F.need === 'nonneg' && !nonNeg) continue;
    if (F.k >= tr.length - 1) continue;
    try {
      let p0 = F.init(xtr, ytr);
      if (!p0 || p0.some(v => !Number.isFinite(v))) continue;
      const fit = N.leastSquares(p => xtr.map((v, i) => F.f(v, p) - ytr[i]), p0, { maxIt: 120 });
      const p = fit.p; if (p.some(v => !Number.isFinite(v))) continue;
      const predTr = xtr.map(v => F.f(v, p)), predTe = xte.map(v => F.f(v, p));
      if (predTr.concat(predTe).some(v => !Number.isFinite(v))) continue;
      const mTr = N.metrics(ytr, predTr), mTe = N.metrics(yte, predTe), crit = ic(tr.length, F.k, mTr.rmse ** 2 * tr.length);
      const se = fit.cov ? fit.cov.map((r, i) => Math.sqrt(Math.max(r[i], 0))) : p.map(() => NaN);
      out.push({ id: F.id, name: F.name, k: F.k, params: p, se, expr: F.expr(p), f: v => F.f(v, p), train: mTr, test: mTe, ...crit, identifiable: se.every((s, i) => Number.isFinite(s) && s < Math.abs(p[i]) * 2 + 1e-12) });
    } catch { /* family not applicable to these data */ }
  }
  out.sort((a, b) => a.bic - b.bic);
  if (out.length) { const b0 = out[0].bic; out.forEach(c => { c.dBic = c.bic - b0; c.weight = Math.exp(-0.5 * c.dBic); }); const s = N.sum(out.map(c => c.weight)); out.forEach(c => { c.weight /= s; }); }
  return { candidates: out, nTrain: tr.length, nTest: te.length, split: { tr, te }, xVar: opts.xVar || 'x', yVar: opts.yVar || 'y', text: out.length ? `${out.length} candidate forms were fitted on ${tr.length} points and tested on ${te.length} held-out points. Ranking uses the Bayesian information criterion, which penalises extra parameters.` : 'No candidate family could be fitted to these data.' };
}

/** Multivariate power law y = C·Π xᵢ^aᵢ by log-linear regression, with held-out testing. */
export function powerLawFit(cols, y) {
  const names = Object.keys(cols), n = y.length;
  if (!y.every(v => v > 0) || names.some(k => !cols[k].every(v => v > 0))) return null;
  const { tr, te } = split(n);
  const X = i => [1, ...names.map(k => Math.log(cols[k][i]))];
  const r = N.linearRegression(tr.map(X), tr.map(i => Math.log(y[i])));
  const f = i => Math.exp(N.sum(X(i).map((v, j) => v * r.beta[j])));
  const snap = e => { for (const q of [1, 2, 3, 4]) { const v = Math.round(e * q) / q; if (Math.abs(v - e) < 0.04) return v; } return e; };
  return {
    C: Math.exp(r.beta[0]), exponents: Object.fromEntries(names.map((k, j) => [k, r.beta[j + 1]])), snapped: Object.fromEntries(names.map((k, j) => [k, snap(r.beta[j + 1])])),
    expr: `${g(Math.exp(r.beta[0]))}*${names.map((k, j) => `${k}^${g(r.beta[j + 1])}`).join('*')}`,
    train: N.metrics(tr.map(i => y[i]), tr.map(f)), test: te.length ? N.metrics(te.map(i => y[i]), te.map(f)) : null,
  };
}

/**
 * Sparse identification of nonlinear dynamics. states: {name: [values]}, t: times.
 * Library: polynomials up to `degree`. Sequential thresholded least squares.
 * Returns one differential equation per state, then re-simulates to check reproduction.
 */
export function sindy(t, states, opts = {}) {
  const { degree = 3, threshold = 0.05 } = opts;
  const names = Object.keys(states), n = t.length, m = names.length;
  if (n < 12) return { ok: false, text: 'At least twelve samples are needed to estimate derivatives reliably.' };
  const dX = names.map(k => N.gradient(t, states[k]));
  // library terms as exponent tuples
  const terms = [];
  const rec = (i, left, cur) => { if (i === m) { terms.push(cur.slice()); return; } for (let e = 0; e <= left; e++) { cur.push(e); rec(i + 1, left - e, cur); cur.pop(); } };
  rec(0, degree, []);
  terms.sort((a, b) => N.sum(a) - N.sum(b));
  const val = (ex, i) => ex.reduce((p, e, j) => p * Math.pow(states[names[j]][i], e), 1);
  const idx = Array.from({ length: n - 4 }, (_, i) => i + 2); // drop end points with poor derivatives
  const Theta = idx.map(i => terms.map(ex => val(ex, i)));
  const scale = terms.map((_, j) => Math.sqrt(N.mean(Theta.map(r => r[j] ** 2))) || 1);
  const Tn = Theta.map(r => r.map((v, j) => v / scale[j]));
  const label = ex => ex.map((e, j) => (e === 0 ? '' : e === 1 ? names[j] : `${names[j]}^${e}`)).filter(Boolean).join('*') || '1';
  const eqs = names.map((k, s) => {
    const yv = idx.map(i => dX[s][i]);
    let active = terms.map((_, j) => j), beta = [];
    for (let it = 0; it < 10; it++) {
      const r = N.linearRegression(Tn.map(row => active.map(j => row[j])), yv); beta = r.beta;
      const mx = N.maxOf(beta.map(Math.abs)) || 1;
      const keep = active.filter((_, q) => Math.abs(beta[q]) >= threshold * mx);
      if (keep.length === active.length || !keep.length) break;
      active = keep;
    }
    const coef = active.map((j, q) => ({ term: label(terms[j]), ex: terms[j], c: beta[q] / scale[j] }));
    const rhs = coef.map(c => `${g(c.c)}${c.term === '1' ? '' : '*' + c.term}`).join(' + ') || '0';
    return { state: k, lhs: `d(${k},t)`, rhs, coef };
  });
  const f = (_, yv) => eqs.map(q => q.coef.reduce((a, c) => a + c.c * c.ex.reduce((p, e, j) => p * Math.pow(yv[j], e), 1), 0));
  let sim = null, score = null;
  try {
    sim = N.rk45(f, names.map(k => states[k][0]), t[0], t[n - 1], n, { rtol: 1e-6 });
    if (!sim.blewUp && sim.t.length === n) score = names.map((k, s) => N.metrics(states[k], sim.y[s]));
  } catch { sim = null; }
  return { ok: true, equations: eqs, sim, score, names, text: `Derivatives were estimated by central differences and regressed on a polynomial library of degree ${degree}; terms smaller than ${threshold * 100}% of the largest were removed. The identified system was then integrated from the first sample and compared with the data.` };
}

/** Human-readable novelty statement: what can and cannot be claimed about a discovered relation. */
export const NOVELTY_NOTE = 'A candidate equation can be described as apparently new relative to the sources actually searched. It cannot be certified as absent from all scientific literature, and mathematical consistency alone does not make it physically true: that requires independent experimental evidence.';
export { FAMILIES, dimToString, isDimless };
