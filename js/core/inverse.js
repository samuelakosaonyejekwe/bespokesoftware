// Shared inverse-modelling engine for reverse engineering:
// reconstruct → simulate → compare → refine → validate.
// Parameter estimation with bounds, identifiability from the sensitivity matrix, held-out
// validation, competing explanations, and recommendations for the next measurement.
import * as N from './num.js';
import { symbolicRegression } from './discover.js';

/**
 * @param predict  (paramsSI[]) => function x -> y   (forward model as a curve), or null on failure
 * @param data     {x:[], y:[], sigma?:[]}
 * @param params   [{sym, name, unit, value, lo, hi}]
 */
export function fitCurve(predict, data, params, opts = {}) {
  const n = data.x.length;
  if (n < params.length + 2) return { ok: false, text: `Only ${n} observations for ${params.length} unknowns: the problem is underdetermined. Supply more measurements or fix some parameters.` };
  const hold = [], train = [];
  for (let i = 0; i < n; i++) ((opts.holdout !== false && n >= 8 && (i * 5 + 2) % 4 === 0) ? hold : train).push(i);
  const sig = i => (data.sigma && data.sigma[i] > 0 ? data.sigma[i] : 1);
  const scale = params.map(p => Math.abs(p.value) > 0 ? Math.abs(p.value) : (p.hi - p.lo) || 1);
  const toP = q => q.map((v, k) => v * scale[k]);
  const res = (q, idx) => { const f = predict(toP(q)); if (!f) return idx.map(() => 1e6); return idx.map(i => { const y = f(data.x[i]); return Number.isFinite(y) ? (y - data.y[i]) / sig(i) : 1e6; }); };
  const fit = N.leastSquares(q => res(q, train), params.map((p, k) => p.value / scale[k]), { lo: params.map((p, k) => p.lo / scale[k]), hi: params.map((p, k) => p.hi / scale[k]), maxIt: opts.maxIt || 60 });
  const p = toP(fit.p), f = predict(p);
  if (!f) return { ok: false, text: 'The forward model failed at the fitted parameters.' };
  const pred = data.x.map(f);
  const mAll = N.metrics(data.y, pred), mTr = N.metrics(train.map(i => data.y[i]), train.map(i => pred[i])), mHo = hold.length ? N.metrics(hold.map(i => data.y[i]), hold.map(i => pred[i])) : null;
  // identifiability from the scaled Jacobian
  const J = fit.J, sv = J && J.length ? N.singularValues(J) : [];
  const cond = sv.length && sv[sv.length - 1] > 0 ? sv[0] / sv[sv.length - 1] : Infinity;
  const rank = sv.filter(s => s > sv[0] * 1e-8).length;
  let se = params.map(() => NaN), corr = null;
  if (fit.cov) {
    se = fit.cov.map((r, i) => Math.sqrt(Math.max(r[i], 0)) * scale[i]);
    corr = fit.cov.map((r, i) => r.map((v, j) => v / Math.sqrt(Math.max(fit.cov[i][i] * fit.cov[j][j], 1e-300))));
  }
  const est = params.map((q, k) => ({ ...q, estimate: p[k], se: se[k], rel: Math.abs(se[k] / (p[k] || 1)), lo95: p[k] - 1.96 * se[k], hi95: p[k] + 1.96 * se[k], atBound: Math.abs(p[k] - q.lo) < 1e-6 * (q.hi - q.lo) || Math.abs(p[k] - q.hi) < 1e-6 * (q.hi - q.lo), identifiable: Number.isFinite(se[k]) && se[k] < Math.abs(p[k]) }));
  const pairs = [];
  if (corr) for (let i = 0; i < params.length; i++) for (let j = i + 1; j < params.length; j++) if (Math.abs(corr[i][j]) > 0.9) pairs.push({ a: params[i].name, b: params[j].name, r: corr[i][j] });
  // sensitivity of the curve to each parameter along x: where a new measurement would help most
  const xs = N.linspace(N.minOf(data.x) - 0.25 * (N.maxOf(data.x) - N.minOf(data.x)), N.maxOf(data.x) + 0.25 * (N.maxOf(data.x) - N.minOf(data.x)), 60);
  const sens = params.map((q, k) => { const pp = p.slice(); pp[k] = p[k] * 1.02 + (p[k] === 0 ? 1e-6 * scale[k] : 0); const g = predict(pp); return xs.map(x => (g && f ? (g(x) - f(x)) / 0.02 : 0)); });
  const recommend = params.map((q, k) => { const a = sens[k].map(Math.abs); const others = sens.filter((_, j) => j !== k); const score = a.map((v, i) => v / (1e-12 + N.maxOf(a)) - 0.6 * Math.max(0, ...others.map(o => Math.abs(o[i]) / (1e-12 + N.maxOf(o.map(Math.abs)))))); const i = score.indexOf(N.maxOf(score)); return { param: q.name, x: xs[i], inside: xs[i] >= N.minOf(data.x) && xs[i] <= N.maxOf(data.x) }; });
  const unique = rank === params.length && cond < 1e6 && est.every(e => e.identifiable) && !pairs.length;
  return {
    ok: true, estimates: est, corr, pairs, singular: sv, cond, rank, unique,
    pred, residuals: data.y.map((y, i) => pred[i] - y), metrics: mAll, train: mTr, holdout: mHo, trainIdx: train, holdIdx: hold,
    history: fit.history, iterations: fit.iterations, converged: fit.converged, curve: f, sensX: xs, sens, recommend,
    verdict: unique
      ? 'The observations determine these parameters uniquely within the stated uncertainty.'
      : rank < params.length ? `Only ${rank} of ${params.length} parameter combinations are constrained by the data. Several different parameter sets reproduce the observations equally well.`
        : pairs.length ? `The fit converged, but ${pairs.map(q => `${q.a} and ${q.b}`).join('; ')} are strongly correlated: the data constrain their combination better than either alone.`
          : 'The fit converged, but at least one parameter has an uncertainty comparable to its value and should be treated as weakly identified.',
  };
}

/** Compare the mechanistic fit against generic empirical families fitted to the same observations. */
export function competingExplanations(data, mechanistic) {
  const sr = symbolicRegression(data.x, data.y);
  const out = sr.candidates.slice(0, 5).map(c => ({ name: c.name, expr: c.expr, k: c.k, rmse: c.train.rmse, holdout: c.test.rmse, bic: c.bic, kind: 'empirical' }));
  if (mechanistic && mechanistic.ok) {
    const n = mechanistic.trainIdx.length, k = mechanistic.estimates.length, s2 = Math.max(mechanistic.train.rmse ** 2, 1e-300);
    out.push({ name: 'Mechanistic model (fitted)', expr: 'forward simulation', k, rmse: mechanistic.train.rmse, holdout: mechanistic.holdout ? mechanistic.holdout.rmse : NaN, bic: n * Math.log(s2) + k * Math.log(n), kind: 'mechanistic' });
  }
  out.sort((a, b) => a.bic - b.bic);
  const b0 = out.length ? out[0].bic : 0; out.forEach(o => { o.dBic = o.bic - b0; });
  return out;
}

/** Geometry reconstruction summary from a triangle mesh or point cloud: extents, principal axes, primitive fits. */
export function reconstructGeometry(geo) {
  if (!geo || !geo.points || geo.points.length < 9) return null;
  const P = geo.points, n = P.length / 3;
  const c = [0, 0, 0]; for (let i = 0; i < n; i++) { c[0] += P[3 * i]; c[1] += P[3 * i + 1]; c[2] += P[3 * i + 2]; } c[0] /= n; c[1] /= n; c[2] /= n;
  const C = [[0, 0, 0], [0, 0, 0], [0, 0, 0]];
  for (let i = 0; i < n; i++) { const d = [P[3 * i] - c[0], P[3 * i + 1] - c[1], P[3 * i + 2] - c[2]]; for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) C[a][b] += d[a] * d[b] / n; }
  const eg = N.eigSym(C), ext = eg.values.map(v => 2 * Math.sqrt(Math.max(v, 0) * 3)); // uniform-distribution equivalent extents
  // candidate primitives judged by radial statistics about the principal axes
  const axis = eg.vectors[2]; let rs = [], hs = [];
  for (let i = 0; i < n; i++) { const d = [P[3 * i] - c[0], P[3 * i + 1] - c[1], P[3 * i + 2] - c[2]]; const h = d[0] * axis[0] + d[1] * axis[1] + d[2] * axis[2]; const r = Math.hypot(d[0] - h * axis[0], d[1] - h * axis[1], d[2] - h * axis[2]); rs.push(r); hs.push(h); }
  const rSph = []; for (let i = 0; i < n; i++) rSph.push(Math.hypot(P[3 * i] - c[0], P[3 * i + 1] - c[1], P[3 * i + 2] - c[2]));
  const cv = a => N.std(a) / (N.mean(a) || 1);
  const cands = [
    { shape: 'Sphere (surface points)', score: cv(rSph), params: { radius: N.mean(rSph) } },
    { shape: 'Cylinder shell about the longest axis', score: cv(rs), params: { radius: N.mean(rs), length: N.maxOf(hs) - N.minOf(hs) } },
    { shape: 'Rectangular box', score: 0.35, params: { a: ext[2], b: ext[1], c: ext[0] } },
  ].sort((a, b) => a.score - b.score);
  return { centroid: c, principalExtents: ext.slice().reverse(), axis, candidates: cands, nPoints: n, text: 'Primitive fits are ranked by the scatter of the points about each ideal surface. A low score means the points are consistent with that shape; it does not prove the object is that shape, and internal features are not recoverable from surface data.' };
}
