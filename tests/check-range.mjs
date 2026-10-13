// Whole-range check. tests/check-sweeps.mjs follows the Parameter response panel, which sweeps an input from a quarter to
// four times its present value. This goes further, to everything the application lets a user enter:
//   1. every input in turn is taken across its ENTIRE declared range (nine points, spaced logarithmically when the range
//      spans more than a factor of fifty), and the model's own conservation checks and exact-solution benchmarks must
//      hold at each point, and the solve must complete;
//   2. every assumption is switched in turn, and with each the result at the default inputs must not move by more than
//      5 % when the numerical resolution is doubled — so the alternative numerical schemes are held to the same standard
//      as the default one.
//   node tests/check-range.mjs [model-id ...]
import { MODELS } from '../js/models/index.js';
import { defaults, runModel } from '../js/engine/core.js';
import * as N from '../js/core/num.js';

const ids = process.argv.slice(2), CONV = 5e-2, PTS = 9;
const fail = {}, stat = { models: 0, points: 0, checks: 0, bench: 0, flips: 0, conv: 0 }, add = (k, x) => { (fail[k] = fail[k] || []).push(x); };
const GRID = /\berror\b|residual|drift|defect|grid|spacing|\bsteps?\b|cell|nodes?\b|iterations?|resolution|mesh|courant|number of (terms|modes|samples)|standard error|simulat|sampled|percentile|median|stages?\b|rooms|plays|games|groups|numerical against/i;
for (const m of MODELS) { if (ids.length && !ids.includes(m.id)) continue; stat.models++;
  const d = defaults(m), v0 = Object.fromEntries(d.map(i => [i.sym, i.si])), a0 = Object.fromEntries((m.assumptions || []).map(q => [q.id, q.on]));
  for (const i of d.filter(q => q.kind !== 'numerical' && q.kind !== 'constant')) {
    const [lo, hi] = i.rangeSI; if (!(hi > lo)) continue;
    let xs = lo > 0 && hi / lo > 50 ? N.logspace(lo, hi, PTS) : N.linspace(lo, hi, PTS); if (i.integer) xs = [...new Set(xs.map(Math.round))];
    for (const x of xs) { stat.points++; const v = { ...v0, [i.sym]: x }, r = runModel(m, v, a0, true), at = `${i.sym} = ${x.toPrecision(3)}`;
      if (r.status !== 'computed') { add(`${m.id}: the solve fails (${String(r.error).slice(0, 70)})`, at); continue; }
      r.checks.forEach(c => { stat.checks++; if (c.pass === false) add(`${m.id}: check "${c.name}"`, `${at} (${Number(c.value).toExponential(1)})`); });
      let bs = []; try { bs = m.benchmarks ? m.benchmarks(v, a0) || [] : []; } catch (e) { add(`${m.id}: benchmarks throw (${String(e.message).slice(0, 60)})`, at); }
      bs.forEach(b => { stat.bench++; if (!b.pass) add(`${m.id}: benchmark "${b.name}"`, `${at} (got ${Number(b.got).toPrecision(4)}, exact ${Number(b.expected).toPrecision(4)})`); });
    }
  }
  const key = m.numerics && m.numerics.resolution, ri = key && d.find(q => q.sym === key);
  for (const flip of [null, ...(m.assumptions || []).map(q => q.id)]) {
    const a = { ...a0 }; if (flip) a[flip] = !a[flip]; const tag = flip ? ` [${flip} ${a[flip] ? 'on' : 'off'}]` : '';
    const r = runModel(m, v0, a, true); stat.flips++;
    if (r.status !== 'computed') { add(`${m.id}${tag}: the solve fails (${String(r.error).slice(0, 70)})`, 'defaults'); continue; }
    r.checks.forEach(c => { if (c.pass === false) add(`${m.id}${tag}: check "${c.name}"`, `defaults (${Number(c.value).toExponential(1)})`); });
    let bs = []; try { bs = m.benchmarks ? m.benchmarks(v0, a) || [] : []; } catch (e) { add(`${m.id}${tag}: benchmarks throw (${String(e.message).slice(0, 60)})`, 'defaults'); }
    bs.forEach(b => { if (!b.pass) add(`${m.id}${tag}: benchmark "${b.name}"`, `defaults (got ${Number(b.got).toPrecision(4)}, exact ${Number(b.expected).toPrecision(4)})`); });
    if (!ri) continue;
    const f = runModel(m, { ...v0, [key]: Math.min(ri.rangeSI[1], ri.integer ? Math.round(ri.si * 2) : ri.si * 2) }, a, true); if (f.status !== 'computed') { add(`${m.id}${tag}: the solve fails at twice the resolution`, 'defaults'); continue; }
    for (const s of r.scalars) { if (typeof s.value !== 'number' || !Number.isFinite(s.value) || GRID.test(s.name)) continue; const q = f.scalars.find(x => x.sym === s.sym); if (!q || !Number.isFinite(q.value)) continue; stat.conv++;
      if (Math.abs(q.value - s.value) > CONV * Math.max(Math.abs(s.value), Math.abs(q.value)) + 1e-9 * (1 + Math.abs(s.value))) add(`${m.id}${tag}: moves by more than ${CONV * 100} % when the resolution is doubled`, `${s.sym} (${s.name.slice(0, 40)}): ${s.value.toPrecision(4)} -> ${q.value.toPrecision(4)}`); }
  }
}
const list = Object.entries(fail);
console.log(`${stat.models} models; ${stat.points} points across whole declared ranges with ${stat.checks} checks and ${stat.bench} benchmarks; ${stat.flips} assumption settings with ${stat.conv} resolution comparisons`);
console.log(`${list.length} problems`); list.slice(0, +process.env.MAX || 200).forEach(([k, l]) => console.log(`  ${k}: ${l.length} — ${l.slice(0, 3).join('; ')}`));
process.exit(list.length ? 1 : 0);
