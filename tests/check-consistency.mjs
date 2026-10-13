// Equation-versus-solver consistency. For every model, with default assumptions and with each
// assumption flipped in turn, the displayed explicit equations are evaluated directly at the default
// inputs and at random points across the declared input ranges (so that clamps and regime changes are
// exercised), and every quantity they define is compared with the value the solver reports.
//   node tests/check-consistency.mjs [js/models/<pack>.js]
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { defaults, runModel } from '../js/engine/core.js';
import { symbolTable } from '../js/core/verify.js';
import * as E from '../js/core/expr.js';
import { rng } from '../js/core/num.js';

const file = process.argv[2];
const models = file ? (await import(pathToFileURL(path.resolve(file)).href)).default : (await import('../js/models/index.js')).MODELS;
const POINTS = 10, TOL = 2e-3;
let bad = 0, compared = 0, modelsBad = 0;
for (const m of models) {
  const d = defaults(m), a0 = Object.fromEntries((m.assumptions || []).map(a => [a.id, a.on])), R = rng(4321), seen = new Map();
  const points = [Object.fromEntries(d.map(i => [i.sym, i.si]))];
  for (let k = 0; k < POINTS; k++) points.push(Object.fromEntries(d.map(i => [i.sym, i.kind === 'numerical' || i.kind === 'constant' ? i.si : (i.rangeSI[0] > 0 && i.rangeSI[1] / i.rangeSI[0] > 50 ? Math.exp(R.range(Math.log(i.rangeSI[0]), Math.log(i.rangeSI[1]))) : R.range(i.rangeSI[0], i.rangeSI[1]))])));
  for (const flip of [null, ...(m.assumptions || []).map(a => a.id)]) {
    const a = { ...a0 }; if (flip) a[flip] = !a[flip];
    points.forEach((v0, pi) => {
      // integer-valued inputs are rounded exactly as the application rounds them
      const v = { ...v0 }; d.forEach(i => { if (i.integer) v[i.sym] = Math.round(v[i.sym]); });
      const r = runModel(m, v, a, true); if (r.status !== 'computed') return;
      let eqs; try { eqs = m.equations(a, v); } catch { return; }
      const consts = Object.fromEntries(Object.entries(symbolTable(d, m.symbols || {}, [])).filter(([, t]) => t.constant).map(([k, t]) => [k, t.value]));
      const env = { ...consts, ...v }, inputs = new Set(d.map(i => i.sym));
      let progress = true; const pend = eqs.filter(q => q.exportable !== false).map(q => { try { return { q, L: E.parse(q.lhs), R: E.parse(q.rhs) }; } catch { return null; } }).filter(Boolean);
      while (progress) { progress = false; for (const p of pend) { if (p.done || p.L.t !== 'sym' || inputs.has(p.L.n) || E.hasDiffOps(p.R)) continue; if (![...E.symbols(p.R)].every(s => s in env)) continue; try { env[p.L.n] = E.evaluate(p.R, env); } catch { env[p.L.n] = NaN; } p.done = true; p.val = env[p.L.n]; progress = true; } }
      for (const p of pend) {
        if (!p.done) continue; const s = r.scalars.find(x => x.sym === p.L.n); if (!s || typeof s.value !== 'number') continue;
        if (!Number.isFinite(s.value) && !Number.isFinite(p.val)) continue;
        // the solver reports no value where the quantity is undefined; a displayed equation that yields no value where the solver has one is a fault
        if (!Number.isFinite(s.value)) continue;
        compared++;
        if (!Number.isFinite(p.val) || Math.abs(p.val - s.value) > TOL * Math.abs(s.value) + 1e-12 * (1 + Math.abs(s.value))) {
          const key = `${p.q.id}|${flip || ''}`; const e = seen.get(key) || { n: 0, eq: p.q, flip, ex: null, def: false }; e.n++; if (pi === 0) e.def = true; if (!e.ex) e.ex = `equation ${Number(p.val).toPrecision(5)} vs solver ${s.value.toPrecision(5)}`; seen.set(key, e);
        }
      }
    });
  }
  if (seen.size) { modelsBad++; console.log(m.id); for (const e of seen.values()) { bad++; console.log(`   ${e.eq.lhs} = ${e.eq.rhs.slice(0, 90)}${e.flip ? `   [${e.flip} flipped]` : ''}: ${e.n} of ${POINTS + 1} points${e.def ? ' incl. defaults' : ''}; e.g. ${e.ex}`); } }
}
console.log(`\n${models.length} models, ${compared} comparisons, ${bad} equation/assumption combinations disagree with the solver in ${modelsBad} models`);
process.exit(bad ? 1 : 0);
