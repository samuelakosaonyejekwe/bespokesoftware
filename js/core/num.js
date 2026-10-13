// Numerical methods shared by every model: ODE/PDE integrators, linear algebra,
// root finding, optimisation, statistics, spectral analysis and sampling.

export const linspace = (a, b, n) => Array.from({ length: n }, (_, i) => (n === 1 ? a : a + (b - a) * i / (n - 1)));
export const logspace = (a, b, n) => linspace(Math.log10(a), Math.log10(b), n).map(x => Math.pow(10, x));
export const clamp = (x, lo, hi) => Math.min(hi, Math.max(lo, x));
export const sum = a => { let s = 0; for (let i = 0; i < a.length; i++) s += a[i]; return s; };
export const mean = a => sum(a) / a.length;
export const variance = a => { const m = mean(a); return sum(a.map(x => (x - m) ** 2)) / Math.max(1, a.length - 1); };
export const std = a => Math.sqrt(variance(a));
export const minOf = a => a.reduce((m, x) => (x < m ? x : m), Infinity);
export const maxOf = a => a.reduce((m, x) => (x > m ? x : m), -Infinity);
/**
 * Largest value of a sampled curve, read between the samples: a parabola through the highest sample and its two
 * neighbours gives the peak value and its position as a fractional index. Reading the highest sample alone makes the
 * result jump by a grid step when an input changes slightly. `interp(arr)` reads any other sampled quantity at the peak.
 */
export function peak(ys) {
  let i = 0; for (let k = 1; k < ys.length; k++) if (ys[k] > ys[i]) i = k;
  let o = 0, y = ys[i];
  if (i > 0 && i < ys.length - 1) { const a = ys[i - 1], b = ys[i], c = ys[i + 1], den = a - 2 * b + c; if (den < 0) { o = clamp(0.5 * (a - c) / den, -0.5, 0.5); y = b - 0.25 * (a - c) * o; } }
  const interp = arr => { const j = clamp(i + (o > 0 ? 1 : -1), 0, arr.length - 1); return arr[i] + (arr[j] - arr[i]) * Math.abs(o); };
  return { i, offset: o, value: y, interp };
}
export function quantile(a, q) {
  const s = [...a].sort((x, y) => x - y); const p = (s.length - 1) * q; const i = Math.floor(p);
  return s[i] + (s[Math.min(i + 1, s.length - 1)] - s[i]) * (p - i);
}
export function interp1(xs, ys, x) {
  const n = xs.length;
  if (x <= xs[0]) return ys[0];
  if (x >= xs[n - 1]) return ys[n - 1];
  let lo = 0, hi = n - 1;
  while (hi - lo > 1) { const m = (lo + hi) >> 1; if (xs[m] <= x) lo = m; else hi = m; }
  return ys[lo] + (ys[hi] - ys[lo]) * (x - xs[lo]) / (xs[hi] - xs[lo]);
}
export function trapz(xs, ys) { let s = 0; for (let i = 1; i < xs.length; i++) s += 0.5 * (ys[i] + ys[i - 1]) * (xs[i] - xs[i - 1]); return s; }
export function gradient(xs, ys) {
  const n = xs.length, g = new Array(n);
  for (let i = 0; i < n; i++) { const a = Math.max(0, i - 1), b = Math.min(n - 1, i + 1); g[i] = (ys[b] - ys[a]) / (xs[b] - xs[a]); }
  return g;
}

/** Deterministic pseudo-random generator (mulberry32) so every run is reproducible from its seed. */
export function rng(seed = 12345) {
  let a = seed >>> 0;
  const u = () => { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  u.normal = () => { let x = 0, y = 0; while (x === 0) x = u(); y = u(); return Math.sqrt(-2 * Math.log(x)) * Math.cos(2 * Math.PI * y); };
  u.range = (lo, hi) => lo + (hi - lo) * u();
  return u;
}

// ------------------------------------------------------------------ ordinary differential equations
/** Classical fixed-step RK4. f(t, y) -> dy/dt (arrays). Returns {t:[], y:[[...]]} with y[k] = component k over time. */
export function rk4(f, y0, t0, t1, n) {
  const m = y0.length, h = (t1 - t0) / n;
  const t = new Array(n + 1), Y = Array.from({ length: m }, () => new Array(n + 1));
  let y = y0.slice();
  const add = (a, b, s) => a.map((x, i) => x + s * b[i]);
  for (let k = 0; k <= n; k++) {
    const tk = t0 + k * h; t[k] = tk;
    for (let j = 0; j < m; j++) Y[j][k] = y[j];
    if (k === n) break;
    const k1 = f(tk, y), k2 = f(tk + h / 2, add(y, k1, h / 2)), k3 = f(tk + h / 2, add(y, k2, h / 2)), k4 = f(tk + h, add(y, k3, h));
    y = y.map((x, i) => x + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]));
  }
  return { t, y: Y };
}

/** Adaptive Dormand–Prince RK45 with dense sampling at nOut equally spaced times. Options: rtol, atol, maxSteps, event(t,y)->stop, h0 (upper bound on the first trial step). */
export function rk45(f, y0, t0, t1, nOut = 400, opts = {}) {
  const { rtol = 1e-7, atol = 1e-10, maxSteps = 200000, event, h0 } = opts;
  const m = y0.length;
  const tOut = linspace(t0, t1, nOut), Y = Array.from({ length: m }, () => new Array(nOut).fill(NaN));
  let t = t0, y = y0.slice(), h = h0 > 0 ? Math.min(h0, (t1 - t0) / 200) : (t1 - t0) / 200, steps = 0, rejected = 0, io = 0, stopped = false, stopT = null;
  const rec = () => { while (io < nOut && tOut[io] <= t + 1e-14 * Math.abs(t1 - t0)) { for (let j = 0; j < m; j++) Y[j][io] = y[j]; io++; } };
  rec();
  const A = [[1 / 5], [3 / 40, 9 / 40], [44 / 45, -56 / 15, 32 / 9], [19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729], [9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656], [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84]];
  const C = [1 / 5, 3 / 10, 4 / 5, 8 / 9, 1, 1];
  const B5 = [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84, 0], B4 = [5179 / 57600, 0, 7571 / 16695, 393 / 640, -92097 / 339200, 187 / 2100, 1 / 40];
  while (t < t1 && steps < maxSteps) {
    if (io < nOut) h = Math.min(h, tOut[io] - t > 0 ? tOut[io] - t : h);
    h = Math.min(h, t1 - t);
    const k = [f(t, y)];
    for (let s = 0; s < 6; s++) {
      const ys = y.map((x, i) => { let a = x; for (let q = 0; q <= s; q++) a += h * A[s][q] * k[q][i]; return a; });
      k.push(f(t + C[s] * h, ys));
    }
    let err = 0; const yn = new Array(m);
    for (let i = 0; i < m; i++) {
      let a5 = 0, a4 = 0;
      for (let q = 0; q < 7; q++) { a5 += B5[q] * k[q][i]; a4 += B4[q] * k[q][i]; }
      yn[i] = y[i] + h * a5;
      const sc = atol + rtol * Math.max(Math.abs(y[i]), Math.abs(yn[i]));
      err = Math.max(err, Math.abs(h * (a5 - a4)) / sc);
    }
    steps++;
    if (!isFinite(err)) { return { t: tOut.slice(0, io), y: Y.map(r => r.slice(0, io)), steps, rejected, blewUp: true, blowUpTime: t }; }
    if (err <= 1) {
      t += h; y = yn; rec();
      if (event && event(t, y)) { stopped = true; stopT = t; break; }
    } else rejected++;
    h *= clamp(0.9 * Math.pow(Math.max(err, 1e-12), -0.2), 0.2, 5);
    if (h < 1e-14 * Math.max(1, Math.abs(t))) return { t: tOut.slice(0, io), y: Y.map(r => r.slice(0, io)), steps, rejected, blewUp: true, blowUpTime: t };
  }
  return { t: tOut.slice(0, io), y: Y.map(r => r.slice(0, io)), steps, rejected, stopped, stopT, final: y, blewUp: false };
}

/** Velocity-Verlet (symplectic) for q'' = a(q). Good long-time energy behaviour for conservative mechanics. */
export function verlet(acc, q0, v0, t0, t1, n) {
  const m = q0.length, h = (t1 - t0) / n;
  const t = new Array(n + 1), Q = Array.from({ length: m }, () => new Array(n + 1)), V = Array.from({ length: m }, () => new Array(n + 1));
  let q = q0.slice(), v = v0.slice(), a = acc(q, t0);
  for (let k = 0; k <= n; k++) {
    t[k] = t0 + k * h;
    for (let j = 0; j < m; j++) { Q[j][k] = q[j]; V[j][k] = v[j]; }
    if (k === n) break;
    const vh = v.map((x, i) => x + 0.5 * h * a[i]);
    q = q.map((x, i) => x + h * vh[i]);
    a = acc(q, t[k] + h);
    v = vh.map((x, i) => x + 0.5 * h * a[i]);
  }
  return { t, q: Q, v: V };
}

// ------------------------------------------------------------------ linear algebra
export function solveLinear(Ain, bin) {
  const n = bin.length, A = Ain.map(r => r.slice()), b = bin.slice();
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
    if (Math.abs(A[p][c]) < 1e-300) throw new Error('Singular matrix: the system of equations is not uniquely solvable');
    [A[c], A[p]] = [A[p], A[c]]; [b[c], b[p]] = [b[p], b[c]];
    for (let r = c + 1; r < n; r++) {
      const f = A[r][c] / A[c][c];
      if (f === 0) continue;
      for (let k = c; k < n; k++) A[r][k] -= f * A[c][k];
      b[r] -= f * b[c];
    }
  }
  const x = new Array(n);
  for (let r = n - 1; r >= 0; r--) { let s = b[r]; for (let k = r + 1; k < n; k++) s -= A[r][k] * x[k]; x[r] = s / A[r][r]; }
  return x;
}
/** Thomas algorithm for tridiagonal systems (a: sub, b: diag, c: super, d: rhs). */
export function tridiag(a, b, c, d) {
  const n = d.length, cp = new Array(n), dp = new Array(n), x = new Array(n);
  cp[0] = c[0] / b[0]; dp[0] = d[0] / b[0];
  for (let i = 1; i < n; i++) { const m = b[i] - a[i] * cp[i - 1]; cp[i] = c[i] / m; dp[i] = (d[i] - a[i] * dp[i - 1]) / m; }
  x[n - 1] = dp[n - 1];
  for (let i = n - 2; i >= 0; i--) x[i] = dp[i] - cp[i] * x[i + 1];
  return x;
}
export const matMul = (A, B) => A.map(r => B[0].map((_, j) => r.reduce((s, v, k) => s + v * B[k][j], 0)));
export const matVec = (A, x) => A.map(r => r.reduce((s, v, k) => s + v * x[k], 0));
export const transpose = A => A[0].map((_, j) => A.map(r => r[j]));
export const identity = n => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)));
export function invert(A) { const n = A.length; const I = identity(n); return transpose(I.map((_, j) => solveLinear(A, I.map(r => r[j])))); }

/** Jacobi eigenvalue iteration for a real symmetric matrix. Returns {values[], vectors[][]} sorted ascending. */
export function eigSym(Ain) {
  const n = Ain.length, A = Ain.map(r => r.slice()), V = identity(n);
  for (let sweep = 0; sweep < 100; sweep++) {
    let off = 0;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) off += A[i][j] ** 2;
    if (off < 1e-22) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      if (Math.abs(A[p][q]) < 1e-300) continue;
      const th = (A[q][q] - A[p][p]) / (2 * A[p][q]);
      const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < n; k++) { const akp = A[k][p], akq = A[k][q]; A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq; }
      for (let k = 0; k < n; k++) { const apk = A[p][k], aqk = A[q][k]; A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk; }
      for (let k = 0; k < n; k++) { const vkp = V[k][p], vkq = V[k][q]; V[k][p] = c * vkp - s * vkq; V[k][q] = s * vkp + c * vkq; }
    }
  }
  const idx = A.map((_, i) => i).sort((a, b) => A[a][a] - A[b][b]);
  return { values: idx.map(i => A[i][i]), vectors: idx.map(i => V.map(r => r[i])) };
}
/** Generalised symmetric eigenproblem K x = λ M x with M symmetric positive definite (via Cholesky reduction). */
export function eigGen(K, M) {
  const n = K.length, L = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 0; i < n; i++) for (let j = 0; j <= i; j++) {
    let s = M[i][j]; for (let k = 0; k < j; k++) s -= L[i][k] * L[j][k];
    if (i === j) { if (s <= 0) throw new Error('Mass matrix is not positive definite'); L[i][i] = Math.sqrt(s); } else L[i][j] = s / L[j][j];
  }
  const Li = invert(L), A = matMul(matMul(Li, K), transpose(Li));
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) A[i][j] = A[j][i] = 0.5 * (A[i][j] + A[j][i]);
  const { values, vectors } = eigSym(A), LiT = transpose(Li);
  return { values, vectors: vectors.map(v => matVec(LiT, v)) };
}
/** Singular values of a (small) matrix via eigenvalues of AᵀA; used for identifiability and conditioning. */
export function singularValues(A) {
  const At = transpose(A), G = matMul(At, A);
  return eigSym(G).values.map(v => Math.sqrt(Math.max(v, 0))).sort((a, b) => b - a);
}

// ------------------------------------------------------------------ roots and optimisation
export function bisect(f, a, b, tol = 1e-12, maxIt = 200) {
  let fa = f(a), fb = f(b);
  if (!(fa * fb <= 0)) throw new Error('Root is not bracketed on the given interval');
  for (let i = 0; i < maxIt; i++) {
    const m = 0.5 * (a + b), fm = f(m);
    if (fa * fm <= 0) { b = m; fb = fm; } else { a = m; fa = fm; }
    if (Math.abs(b - a) < tol * Math.max(1, Math.abs(m))) break;
  }
  return 0.5 * (a + b);
}
/** Brent-style safeguarded secant. Falls back to bisection when the secant step leaves the bracket. */
export function findRoot(f, a, b, tol = 1e-12) {
  let fa = f(a), fb = f(b);
  if (fa === 0) return a; if (fb === 0) return b;
  if (!(fa * fb < 0)) throw new Error('Root is not bracketed on the given interval');
  for (let i = 0; i < 200; i++) {
    let c = b - fb * (b - a) / (fb - fa);
    if (!(c > Math.min(a, b) && c < Math.max(a, b)) || i % 3 === 2) c = 0.5 * (a + b);
    const fc = f(c);
    if (fa * fc < 0) { b = c; fb = fc; } else { a = c; fa = fc; }
    if (Math.abs(b - a) < tol * Math.max(1, Math.abs(c)) || fc === 0) return c;
  }
  return 0.5 * (a + b);
}
export function newton(f, x0, tol = 1e-12, maxIt = 60) {
  let x = x0;
  for (let i = 0; i < maxIt; i++) {
    const h = 1e-6 * Math.max(1, Math.abs(x)), fx = f(x), d = (f(x + h) - f(x - h)) / (2 * h);
    if (d === 0 || !isFinite(d)) break;
    const xn = x - fx / d;
    if (Math.abs(xn - x) < tol * Math.max(1, Math.abs(xn))) return xn;
    x = xn;
  }
  return x;
}
/** Nelder–Mead simplex minimiser with optional box bounds. Returns {x, f, iterations, history}. */
export function nelderMead(f, x0, opts = {}) {
  const { lo, hi, maxIt = 400, tol = 1e-9, scale } = opts;
  const n = x0.length;
  const proj = x => (lo ? x.map((v, i) => clamp(v, lo[i], hi[i])) : x);
  const F = x => { const v = f(proj(x)); return Number.isFinite(v) ? v : 1e300; };
  let S = [proj(x0)];
  for (let i = 0; i < n; i++) { const p = x0.slice(); const s = scale ? scale[i] : (Math.abs(p[i]) > 1e-12 ? 0.1 * Math.abs(p[i]) : 0.1); p[i] += s; if (lo && p[i] > hi[i]) p[i] = x0[i] - s; S.push(proj(p)); }
  let fv = S.map(F); const history = [];
  let it = 0;
  for (; it < maxIt; it++) {
    const idx = fv.map((_, i) => i).sort((a, b) => fv[a] - fv[b]);
    S = idx.map(i => S[i]); fv = idx.map(i => fv[i]);
    history.push(fv[0]);
    if (Math.abs(fv[n] - fv[0]) <= tol * (Math.abs(fv[0]) + tol)) break;
    const c = new Array(n).fill(0);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) c[j] += S[i][j] / n;
    const at = s => proj(c.map((v, j) => v + s * (S[n][j] - v)));
    const xr = at(-1), fr = F(xr);
    if (fr < fv[0]) { const xe = at(-2), fe = F(xe); if (fe < fr) { S[n] = xe; fv[n] = fe; } else { S[n] = xr; fv[n] = fr; } }
    else if (fr < fv[n - 1]) { S[n] = xr; fv[n] = fr; }
    else {
      const xc = at(fr < fv[n] ? -0.5 : 0.5), fc = F(xc);
      if (fc < Math.min(fr, fv[n])) { S[n] = xc; fv[n] = fc; }
      else { for (let i = 1; i <= n; i++) { S[i] = proj(S[i].map((v, j) => S[0][j] + 0.5 * (v - S[0][j]))); fv[i] = F(S[i]); } }
    }
  }
  return { x: proj(S[0]), f: fv[0], iterations: it, history };
}
/** Golden-section minimiser for one variable. */
export function golden(f, a, b, tol = 1e-8) {
  const g = (Math.sqrt(5) - 1) / 2; let c = b - g * (b - a), d = a + g * (b - a), fc = f(c), fd = f(d);
  for (let i = 0; i < 200 && Math.abs(b - a) > tol * (Math.abs(c) + Math.abs(d) + 1e-30); i++) {
    if (fc < fd) { b = d; d = c; fd = fc; c = b - g * (b - a); fc = f(c); } else { a = c; c = d; fc = fd; d = a + g * (b - a); fd = f(d); }
  }
  return 0.5 * (a + b);
}

/**
 * Levenberg–Marquardt least squares. residual(p) -> array.
 * Returns {p, cost, iterations, cov, J, converged, history}.
 */
export function leastSquares(residual, p0, opts = {}) {
  const { lo, hi, maxIt = 100, tol = 1e-10 } = opts;
  const n = p0.length;
  const proj = p => (lo ? p.map((v, i) => clamp(v, lo[i], hi[i])) : p);
  let p = proj(p0.slice()), r = residual(p), cost = sum(r.map(x => x * x)), lam = 1e-3;
  const history = [cost];
  const jac = (q, r0) => {
    const J = r0.map(() => new Array(n));
    for (let j = 0; j < n; j++) {
      const h = 1e-6 * Math.max(Math.abs(q[j]), 1e-8), qq = q.slice(); qq[j] += h;
      const rr = residual(qq);
      for (let i = 0; i < r0.length; i++) J[i][j] = (rr[i] - r0[i]) / h;
    }
    return J;
  };
  let J = jac(p, r), it = 0, converged = false;
  for (; it < maxIt; it++) {
    const Jt = transpose(J), H = matMul(Jt, J), g = matVec(Jt, r);
    let improved = false;
    for (let tries = 0; tries < 12; tries++) {
      const A = H.map((row, i) => row.map((v, j) => (i === j ? v * (1 + lam) + 1e-300 : v)));
      let dp;
      try { dp = solveLinear(A, g.map(x => -x)); } catch { lam *= 10; continue; }
      const pn = proj(p.map((v, i) => v + dp[i])), rn = residual(pn), cn = sum(rn.map(x => x * x));
      if (Number.isFinite(cn) && cn < cost) {
        const rel = (cost - cn) / Math.max(cost, 1e-300);
        p = pn; r = rn; cost = cn; lam = Math.max(lam / 5, 1e-12); improved = true;
        if (rel < tol) converged = true;
        break;
      }
      lam *= 5;
    }
    history.push(cost);
    if (!improved) { converged = true; break; }
    if (converged) break;
    J = jac(p, r);
  }
  J = jac(p, r);
  let cov = null;
  try {
    const H = matMul(transpose(J), J), dof = Math.max(1, r.length - n), s2 = cost / dof;
    cov = invert(H).map(row => row.map(v => v * s2));
  } catch { cov = null; }
  return { p, cost, iterations: it, cov, J, converged, history, residuals: r };
}
export function linearRegression(X, y) {
  const Xt = transpose(X), beta = solveLinear(matMul(Xt, X).map((r, i) => r.map((v, j) => (i === j ? v + 1e-12 : v))), matVec(Xt, y));
  const pred = matVec(X, beta), ybar = mean(y);
  const ssr = sum(y.map((v, i) => (v - pred[i]) ** 2)), sst = sum(y.map(v => (v - ybar) ** 2));
  return { beta, r2: sst > 0 ? 1 - ssr / sst : 1, rmse: Math.sqrt(ssr / y.length), pred };
}
export function metrics(obs, pred) {
  const n = obs.length, e = obs.map((o, i) => pred[i] - o), ybar = mean(obs);
  const sse = sum(e.map(x => x * x)), sst = sum(obs.map(o => (o - ybar) ** 2));
  return {
    n, rmse: Math.sqrt(sse / n), mae: sum(e.map(Math.abs)) / n, bias: mean(e), r2: sst > 0 ? 1 - sse / sst : NaN,
    mape: 100 * mean(obs.map((o, i) => (o !== 0 ? Math.abs(e[i] / o) : 0))), maxAbs: maxOf(e.map(Math.abs)),
  };
}

// ------------------------------------------------------------------ partial differential equations
/** 1-D diffusion u_t = D u_xx + S(x,t,u) with Dirichlet/Neumann ends, Crank–Nicolson in time. */
export function diffusion1D({ D, L, nx = 101, tEnd, nt = 400, u0, left = { type: 'dirichlet', value: 0 }, right = { type: 'dirichlet', value: 0 }, source, frames = 60 }) {
  const dx = L / (nx - 1), dt = tEnd / nt, r = D * dt / (dx * dx);
  const x = linspace(0, L, nx);
  let u = x.map((xx, i) => (typeof u0 === 'function' ? u0(xx, i) : u0));
  const snaps = [], times = [], every = Math.max(1, Math.floor(nt / frames));
  const a = new Array(nx).fill(-r / 2), b = new Array(nx).fill(1 + r), c = new Array(nx).fill(-r / 2);
  const bcRow = (i, bc, inner) => {
    if (bc.type === 'dirichlet') { a[i] = 0; b[i] = 1; c[i] = 0; }
    else { a[i] = inner < i ? -r : 0; c[i] = inner > i ? -r : 0; b[i] = 1 + r; }
  };
  bcRow(0, left, 1); bcRow(nx - 1, right, nx - 2);
  for (let n = 0; n <= nt; n++) {
    if (n % every === 0 || n === nt) { snaps.push(u.slice()); times.push(n * dt); }
    if (n === nt) break;
    const t = n * dt, d = new Array(nx);
    for (let i = 1; i < nx - 1; i++) d[i] = u[i] + r / 2 * (u[i + 1] - 2 * u[i] + u[i - 1]) + (source ? dt * source(x[i], t, u[i]) : 0);
    const lv = typeof left.value === 'function' ? left.value(t + dt) : left.value, rv = typeof right.value === 'function' ? right.value(t + dt) : right.value;
    if (left.type === 'dirichlet') d[0] = lv; else d[0] = u[0] + r * (u[1] - u[0]) - 2 * r * dx * lv / 1 + (source ? dt * source(x[0], t, u[0]) : 0);
    if (right.type === 'dirichlet') d[nx - 1] = rv; else d[nx - 1] = u[nx - 1] + r * (u[nx - 2] - u[nx - 1]) + 2 * r * dx * rv + (source ? dt * source(x[nx - 1], t, u[nx - 1]) : 0);
    u = tridiag(a, b, c, d);
  }
  return { x, times, snaps, final: u, dx, dt, r };
}
/** 1-D wave equation u_tt = c² u_xx, explicit leapfrog (stable for CFL ≤ 1), fixed or free ends. */
export function wave1D({ c, L, nx = 201, tEnd, cfl = 0.9, u0, v0 = () => 0, ends = 'fixed', frames = 80, damping = 0 }) {
  const dx = L / (nx - 1), dt = cfl * dx / c, nt = Math.max(1, Math.ceil(tEnd / dt)), C2 = (c * dt / dx) ** 2;
  const x = linspace(0, L, nx);
  let up = x.map(u0), u = new Array(nx);
  for (let i = 1; i < nx - 1; i++) u[i] = up[i] + dt * v0(x[i]) + 0.5 * C2 * (up[i + 1] - 2 * up[i] + up[i - 1]);
  const edge = arr => { if (ends === 'fixed') { arr[0] = 0; arr[nx - 1] = 0; } else { arr[0] = arr[1]; arr[nx - 1] = arr[nx - 2]; } };
  edge(u);
  const snaps = [up.slice()], times = [0], every = Math.max(1, Math.floor(nt / frames));
  for (let n = 1; n <= nt; n++) {
    if (n % every === 0) { snaps.push(u.slice()); times.push(n * dt); }
    const un = new Array(nx);
    for (let i = 1; i < nx - 1; i++) un[i] = (2 * u[i] - (1 - damping * dt / 2) * up[i] + C2 * (u[i + 1] - 2 * u[i] + u[i - 1])) / (1 + damping * dt / 2);
    edge(un); up = u; u = un;
  }
  return { x, times, snaps, final: u, dx, dt, cfl: c * dt / dx };
}
/** 2-D Poisson ∇²φ = -f on a rectangle by successive over-relaxation. fixed(i,j) -> value or undefined. */
export function poisson2D({ nx, ny, dx, dy = dx, f, fixed, tol = 1e-6, maxIt = 6000, omega }) {
  const phi = Array.from({ length: ny }, () => new Float64Array(nx));
  const mask = Array.from({ length: ny }, () => new Uint8Array(nx));
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) { const v = fixed(i, j); if (v !== undefined) { phi[j][i] = v; mask[j][i] = 1; } }
  const w = omega || 2 / (1 + Math.sin(Math.PI / Math.max(nx, ny)));
  const ax = 1 / (dx * dx), ay = 1 / (dy * dy), den = 2 * (ax + ay);
  let it = 0, res = Infinity; const hist = [];
  for (; it < maxIt; it++) {
    res = 0;
    for (let j = 1; j < ny - 1; j++) for (let i = 1; i < nx - 1; i++) {
      if (mask[j][i]) continue;
      const g = (ax * (phi[j][i - 1] + phi[j][i + 1]) + ay * (phi[j - 1][i] + phi[j + 1][i]) + (f ? f(i, j) : 0)) / den;
      const dlt = g - phi[j][i]; phi[j][i] += w * dlt; res = Math.max(res, Math.abs(dlt));
    }
    // zero-gradient on any unfixed outer edge
    for (let i = 0; i < nx; i++) { if (!mask[0][i]) phi[0][i] = phi[1][i]; if (!mask[ny - 1][i]) phi[ny - 1][i] = phi[ny - 2][i]; }
    for (let j = 0; j < ny; j++) { if (!mask[j][0]) phi[j][0] = phi[j][1]; if (!mask[j][nx - 1]) phi[j][nx - 1] = phi[j][nx - 2]; }
    if (it % 20 === 0) hist.push(res);
    if (res < tol) break;
  }
  return { phi, iterations: it, residual: res, history: hist, converged: res < tol };
}
/** 1-D linear advection–diffusion c_t + u c_x = D c_xx, first-order upwind + explicit diffusion (monotone). */
export function advectDiffuse1D({ u, D, L, nx = 201, tEnd, c0, inlet = 0, frames = 60 }) {
  const dx = L / (nx - 1), dtAdv = Math.abs(u) > 0 ? dx / Math.abs(u) : Infinity, dtDif = D > 0 ? dx * dx / (2 * D) : Infinity;
  const dt = 0.4 * Math.min(dtAdv, dtDif, tEnd), nt = Math.max(1, Math.ceil(tEnd / dt));
  const x = linspace(0, L, nx); let c = x.map(c0);
  const snaps = [], times = [], every = Math.max(1, Math.floor(nt / frames));
  for (let n = 0; n <= nt; n++) {
    if (n % every === 0 || n === nt) { snaps.push(c.slice()); times.push(n * dt); }
    if (n === nt) break;
    const cn = c.slice();
    for (let i = 1; i < nx - 1; i++) {
      const adv = u >= 0 ? u * (c[i] - c[i - 1]) / dx : u * (c[i + 1] - c[i]) / dx;
      cn[i] = c[i] + dt * (-adv + D * (c[i + 1] - 2 * c[i] + c[i - 1]) / (dx * dx));
    }
    cn[0] = typeof inlet === 'function' ? inlet(n * dt) : inlet; cn[nx - 1] = cn[nx - 2];
    c = cn;
  }
  return { x, times, snaps, final: c, dx, dt };
}

// ------------------------------------------------------------------ spectral analysis
/** Radix-2 FFT of a real signal (zero-padded). Returns one-sided {freq, amp, power}. */
export function spectrum(signal, dt) {
  let n = 1; while (n < signal.length) n <<= 1;
  const re = new Float64Array(n), im = new Float64Array(n), m = mean(signal);
  for (let i = 0; i < signal.length; i++) re[i] = (signal[i] - m) * (0.5 - 0.5 * Math.cos(2 * Math.PI * i / (signal.length - 1)));
  for (let i = 1, j = 0; i < n; i++) { let bit = n >> 1; for (; j & bit; bit >>= 1) j ^= bit; j ^= bit; if (i < j) { [re[i], re[j]] = [re[j], re[i]]; [im[i], im[j]] = [im[j], im[i]]; } }
  for (let len = 2; len <= n; len <<= 1) {
    const ang = -2 * Math.PI / len, wr = Math.cos(ang), wi = Math.sin(ang);
    for (let i = 0; i < n; i += len) {
      let cr = 1, ci = 0;
      for (let k = 0; k < len / 2; k++) {
        const a = i + k, b = a + len / 2, xr = re[b] * cr - im[b] * ci, xi = re[b] * ci + im[b] * cr;
        re[b] = re[a] - xr; im[b] = im[a] - xi; re[a] += xr; im[a] += xi;
        const t = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = t;
      }
    }
  }
  const half = n / 2, freq = new Array(half), amp = new Array(half);
  for (let k = 0; k < half; k++) { freq[k] = k / (n * dt); amp[k] = 4 * Math.hypot(re[k], im[k]) / signal.length; }
  let kp = 1; for (let k = 2; k < half; k++) if (amp[k] > amp[kp]) kp = k;
  return { freq, amp, peakFreq: freq[kp], peakAmp: amp[kp] };
}

// ------------------------------------------------------------------ sampling & sensitivity
/** Latin hypercube sample of n points in a box [[lo,hi],...]. */
export function latinHypercube(n, box, seed = 7) {
  const r = rng(seed), dimn = box.length, cols = [];
  for (let d = 0; d < dimn; d++) {
    const perm = Array.from({ length: n }, (_, i) => i);
    for (let i = n - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [perm[i], perm[j]] = [perm[j], perm[i]]; }
    cols.push(perm.map(k => box[d][0] + (box[d][1] - box[d][0]) * (k + r()) / n));
  }
  return Array.from({ length: n }, (_, i) => cols.map(c => c[i]));
}
export function histogram(data, bins = 24) {
  const lo = minOf(data), hi = maxOf(data), w = (hi - lo) / bins || 1, counts = new Array(bins).fill(0);
  data.forEach(v => { counts[Math.min(bins - 1, Math.floor((v - lo) / w))]++; });
  return { centres: counts.map((_, i) => lo + (i + 0.5) * w), counts, width: w };
}
/** Observed order of accuracy from three results on grids refined by a constant ratio r (Richardson). */
export function observedOrder(coarse, medium, fine, r = 2) {
  const p = Math.log(Math.abs((coarse - medium) / (medium - fine))) / Math.log(r);
  const extrap = fine + (fine - medium) / (Math.pow(r, p) - 1);
  const gci = 1.25 * Math.abs((fine - medium) / fine) / (Math.pow(r, p) - 1);
  return { order: p, extrapolated: extrap, gci };
}
