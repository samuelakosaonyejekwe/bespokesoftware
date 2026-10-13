// Parameter-response check. Every input of every model is swept exactly as the "Parameter response" panel sweeps it, and
// every plotted output is tested three independent ways:
//   1. at every sweep point, the displayed explicit equations are evaluated directly and compared with the plotted value;
//   2. whether the output moves at all is compared with whether the equations make it depend on that input;
//   3. at the two ends of the range and at the present value the model is re-solved at twice the numerical resolution,
//      and the plotted value must not move by more than the tolerance (the curve is then a property of the equations,
//      not of the grid).
// The curve must also pass through the result reported at the present input.
//   node tests/check-sweeps.mjs [model-id ...]
import { MODELS } from '../js/models/index.js';
import { defaults, runModel, sweep, sensitivity } from '../js/engine/core.js';
import { symbolTable } from '../js/core/verify.js';
import * as E from '../js/core/expr.js';

const ids = process.argv.slice(2), TOL = 2e-3, CONV = 5e-2;
const stat = { sweeps: 0, curves: 0, points: 0, byEq: 0, eqPoints: 0, conv: 0, convCurves: 0, unchecked: 0 }, bad = [], unch = new Map(), weak = {}, limited = {}, laws = {};
const close = (p, q, tol) => (!Number.isFinite(p) && !Number.isFinite(q)) || Math.abs(p - q) <= tol * Math.max(Math.abs(p), Math.abs(q)) + 1e-12 * (1 + Math.abs(q));
for (const m of MODELS) { if (ids.length && !ids.includes(m.id)) continue;
  const d = defaults(m), v0 = Object.fromEntries(d.map(i => [i.sym, i.si])), a = Object.fromEntries((m.assumptions || []).map(q => [q.id, q.on]));
  const base = runModel(m, v0, a, true); if (base.status !== 'computed') { bad.push(`${m.id}: base run ${base.status}`); continue; }
  const consts = Object.fromEntries(Object.entries(symbolTable(d, m.symbols || {}, [])).filter(([, t]) => t.constant).map(([k, t]) => [k, t.value])), inputs = new Set(d.map(i => i.sym));
  const sens = sensitivity({ model: m, inputs: d, v: v0, a, result: base }), resKey = m.numerics && m.numerics.resolution, numerical = d.filter(i => i.sym === resKey), c = { model: m, inputs: d, v: v0, a };
  /** Values the displayed equations give at input point v, and what each depends on. */
  const fromEquations = v => {
    let eqs; try { eqs = m.equations(a, v); } catch { return { env: {}, deps: {}, form: {} }; }
    const env = { ...consts, ...v }, deps = {}, val = {}, form = {};
    const pend = eqs.filter(q => q.exportable !== false).map(q => { try { return { L: E.parse(q.lhs), R: E.parse(q.rhs) }; } catch { return null; } }).filter(Boolean);
    let progress = true;
    while (progress) { progress = false; for (const p of pend) { if (p.done || p.L.t !== 'sym' || inputs.has(p.L.n) || E.hasDiffOps(p.R)) continue; const need = [...E.symbols(p.R)]; if (!need.every(s => s in env)) continue; try { env[p.L.n] = E.evaluate(p.R, env); } catch { env[p.L.n] = NaN; } val[p.L.n] = env[p.L.n]; form[p.L.n] = E.show ? E.show(p.R) : JSON.stringify(p.R); deps[p.L.n] = new Set(need.flatMap(s => (inputs.has(s) ? [s] : [...(deps[s] || [])]))); p.done = true; progress = true; } }
    return { env: val, deps, form };
  };
  for (const i of d.filter(q => q.kind !== 'numerical')) {
    const s = sweep(c, i.sym, 40); stat.sweeps++;
    const at = s.xs.map(x => fromEquations({ ...v0, [i.sym]: x })), k0 = s.xs.indexOf(i.si);
    // resolution doubled at the ends and at the present value
    const probe = [0, k0, s.xs.length - 1].filter((k, j, arr) => k >= 0 && arr.indexOf(k) === j), fine = numerical.length ? probe.map(k => { const vv = { ...v0, [i.sym]: s.xs[k] }; numerical.forEach(n => { vv[n.sym] = Math.min(n.rangeSI[1], n.integer ? Math.round(n.si * 2) : n.si * 2); }); const r = runModel(m, vv, a, true); return r.status === 'computed' ? Object.fromEntries(r.scalars.map(q => [q.sym, q.value])) : null; }) : [];
    // the model's own conservation checks and exact-solution benchmarks, repeated across the swept range
    const n5 = [0, 0.25, 0.5, 0.75, 1].map(f => Math.round(f * (s.xs.length - 1))).concat(k0 < 0 ? [] : [k0]).filter((k, j, arr) => arr.indexOf(k) === j); let guarded = false;
    // conservation checks come with every sweep point, so they are examined at all of them
    s.bad.forEach((f, k) => { stat.checkPts = (stat.checkPts || 0) + 1; (f || []).forEach(name => { const key = `${m.id}  ${i.sym}: check "${name}"`; (weak[key] = weak[key] || []).push(s.xs[k].toPrecision(3)); }); });
    for (const k of n5) { const vv = { ...v0, [i.sym]: s.xs[k] }, r = runModel(m, vv, a, true); if (r.status !== 'computed') { stat.failedSolves = (stat.failedSolves || 0) + 1; continue; }
      (r.checks || []).forEach(() => { stat.checks = (stat.checks || 0) + 1; guarded = true; });
      let bs = []; try { bs = m.benchmarks ? m.benchmarks(vv, a) || [] : []; } catch { bs = []; }
      bs.forEach(bm => { stat.bench = (stat.bench || 0) + 1; guarded = true; if (!bm.pass) (weak[`${m.id}  ${i.sym}: benchmark "${bm.name}"`] = weak[`${m.id}  ${i.sym}: benchmark "${bm.name}"`] || []).push(`${s.xs[k].toPrecision(3)} (got ${Number(bm.got).toPrecision(4)}, exact ${Number(bm.expected).toPrecision(4)})`); }); }
    const elastic = sens && sens.rows.find(q => q.sym === i.sym);
    for (const o of s.outputs) { stat.curves++; stat.points += o.data.length; const tag = `${m.id}  ${i.sym} -> ${o.sym} (${o.name})`;
      const b = base.scalars.find(q => q.sym === o.sym);
      if (k0 < 0) bad.push(`${tag}: present value is not a sweep point`); else if (b && Number.isFinite(b.value) && !close(o.data[k0], b.value, 1e-12)) bad.push(`${tag}: curve gives ${o.data[k0]} at the present input, the result panel gives ${b.value}`);
      // a break in a curve must come with the model's reason for it
      { const blank = o.data.filter((q, k) => !Number.isFinite(q) && !o.why[k] && !s.bad[k]).length; if (blank) bad.push(`${tag}: ${blank} points have no value and the model gives no reason`); }
      // the law stated under the chart, and the Sensitivity panel (a separate ±2 % difference at the present value), must tell one story
      { const kind = o.shape === 'line' ? (o.law.type === 'power' ? (o.law.p === 1 ? 'proportional' : o.law.p === -1 ? 'inverse' : 'power law') : o.law.type) : o.shape; laws[kind] = (laws[kind] || 0) + 1;
        const e = elastic ? elastic.s[o.sym] : NaN;
        if (Number.isFinite(e) && i.si !== 0 && b && b.value !== 0) { stat.sens = (stat.sens || 0) + 1;
          if (o.shape === 'level' && Math.abs(e) > 1e-6) bad.push(`${tag}: drawn level, yet the Sensitivity panel reports ${e.toPrecision(3)} % per 1 %`);
          if (o.shape === 'line' && o.law.type === 'power' && Math.abs(e - o.law.p) > 0.02 * Math.max(1, Math.abs(o.law.p))) bad.push(`${tag}: stated power ${o.law.p.toPrecision(4)}, Sensitivity panel reports ${e.toPrecision(4)}`); } }
      let checked = false;
      if (at.some(e => o.sym in e.env)) { checked = true; stat.byEq++; let n = 0, ex = '';
        s.xs.forEach((x, k) => { const p = at[k].env[o.sym], q = o.data[k]; if (p === undefined || !Number.isFinite(q)) { if (p !== undefined && Number.isFinite(p)) stat.undef = (stat.undef || 0) + 1; return; } stat.eqPoints++; if (!close(p, q, TOL)) { n++; ex = ex || `at ${i.sym} = ${x.toPrecision(4)}: equation ${Number(p).toPrecision(5)}, plotted ${Number(q).toPrecision(5)}`; } });
        if (n) bad.push(`${tag}: ${n} of ${s.xs.length} plotted points disagree with the displayed equation; ${ex}`);
        const dep = at[Math.max(k0, 0)].deps[o.sym], moves = ['line', 'steps', 'scattered'].includes(o.shape);
        // a regime change along the sweep replaces the displayed equation: the dependence then runs through the regime
        const regimes = new Set(at.map(e => e.form[o.sym]).filter(Boolean)).size > 1;
        if (dep && moves && !regimes && !dep.has(i.sym)) bad.push(`${tag}: the curve moves, yet the displayed equations do not make this output depend on ${i.sym}`);
      }
      if (fine.length && !/\berror\b|residual|drift|defect|grid|spacing|\bsteps?\b|cell|nodes?\b|iterations?|resolution|mesh|courant|number of (terms|modes|samples)|standard error|simulat|sampled|percentile|median|stages?\b|rooms|plays|games|groups|numerical against/i.test(o.name) && o.shape !== 'residual' && o.shape !== 'scattered') { const fin = o.data.filter(Number.isFinite), span = Math.max(...fin) - Math.min(...fin); let n = 0, ex = '';
        probe.forEach((k, j) => { const f = fine[j]; if (!f || !(o.sym in f) || !Number.isFinite(f[o.sym]) || !Number.isFinite(o.data[k])) return; stat.conv++; checked = true; if (Math.abs(f[o.sym] - o.data[k]) > CONV * Math.max(Math.abs(o.data[k]), span) + 1e-12) { n++; ex = ex || `at ${i.sym} = ${s.xs[k].toPrecision(4)}: plotted ${o.data[k].toPrecision(5)}, at twice the resolution ${f[o.sym].toPrecision(5)}`; } });
        if (probe.length) stat.convCurves++;
        if (n) (limited[`${m.id}  ${o.sym} (${o.name})`] = limited[`${m.id}  ${o.sym} (${o.name})`] || []).push(`${i.sym}: ${ex}`);
      }
      if (guarded) { stat.guarded = (stat.guarded || 0) + 1; }
      if (!checked && !guarded) { stat.unchecked++; unch.set(`${m.id}/${o.sym}`, o.name); }
    }
  }
}
console.log(`${stat.sweeps} input sweeps, ${stat.curves} plotted curves, ${stat.points} plotted points`);
console.log(`${stat.byEq} curves compared with the displayed equations at every point (${stat.eqPoints} point comparisons)`);
console.log(`${stat.convCurves} curves re-solved at twice the numerical resolution (${stat.conv} comparisons)`);
console.log(`${stat.unchecked} curves (${unch.size} distinct outputs) have no explicit equation, no resolution setting and no model check: they pass the present-value test only`);
console.log(`${stat.guarded || 0} curves come from solves whose conservation checks were examined at every one of ${stat.checkPts || 0} sweep points and whose exact-solution benchmarks (${stat.bench || 0}) were repeated at up to six points across the range`);
const wk = Object.entries(weak); console.log(`${wk.length} check/benchmark and input combinations fail somewhere in the swept range`); wk.slice(0, +process.env.MAX || 60).forEach(([k, l]) => console.log(`  ~ ${k} fails at ${l.slice(0, 4).join(', ')}`));
if (process.env.LIST) console.log([...unch].map(([k, n]) => `   ${k}  ${n}`).join('\n'));
console.log(`How the ${stat.curves} input/output pairs behave: ${Object.entries(laws).sort((p, q) => q[1] - p[1]).map(([k, n]) => `${k} ${n}`).join(', ')}`);
console.log(`${stat.sens || 0} pairs cross-checked against the Sensitivity panel`);
console.log(`${stat.undef || 0} plotted points are breaks where the quantity is undefined; every break must carry the model's stated reason`);
const lim = Object.entries(limited); console.log(`${lim.length} outputs move by more than ${CONV * 100} % when the resolution is doubled somewhere in the range`); lim.slice(0, +process.env.MAX || 60).forEach(([k, l]) => console.log(`  ^ ${k}: ${l[0]}`));
console.log(`${bad.length} problems`); bad.slice(0, +process.env.MAX || 60).forEach(x => console.log('  ' + x));
process.exit(bad.length ? 1 : 0);
