// Contract and physics checks for model packs.
//   node tests/check-models.mjs                 all registered models
//   node tests/check-models.mjs js/models/x.js  one pack file
import { pathToFileURL } from 'node:url';
import path from 'node:path';
import { defaults, runModel } from '../js/engine/core.js';
import { verifySystem, symbolTable } from '../js/core/verify.js';
import { DOMAINS, LAWS } from '../js/data/domains.js';
import { rng } from '../js/core/num.js';
import { tryUnit } from '../js/core/units.js';
import { parseFormula } from '../js/core/logic.js';

const file = process.argv[2];
const models = file ? (await import(pathToFileURL(path.resolve(file)).href)).default : (await import('../js/models/index.js')).MODELS;
let fails = 0, warns = 0;
const fail = (m, msg) => { fails++; console.log(`  FAIL  ${m.id}: ${msg}`); };
const warn = (m, msg) => { warns++; console.log(`  warn  ${m.id}: ${msg}`); };
const ids = new Set();
for (const m of models) {
  const t0 = performance.now();
  for (const k of ['id', 'title', 'module', 'klass', 'domains', 'keywords', 'inputs', 'equations', 'solve', 'summary', 'background', 'laws', 'refs', 'limits']) if (m[k] == null) fail(m, `missing "${k}"`);
  if (ids.has(m.id)) fail(m, 'duplicate id'); ids.add(m.id);
  (m.domains || []).forEach(d => { if (!DOMAINS[d]) fail(m, `unknown domain "${d}"`); });
  (m.laws || []).forEach(l => { if (!LAWS[l]) fail(m, `unknown law "${l}"`); });
  (m.inputs || []).forEach(i => { if (!tryUnit(i.unit)) fail(m, `input ${i.sym}: unit "${i.unit}" does not parse`); if (i.min != null && i.max != null && !(i.min <= i.value && i.value <= i.max)) fail(m, `input ${i.sym}: default outside [min,max]`); if (i.kind !== 'constant' && (i.min == null || i.max == null)) warn(m, `input ${i.sym}: no min/max`); });
  Object.entries(m.symbols || {}).forEach(([s, v]) => { if (!tryUnit(v[1])) fail(m, `symbol ${s}: unit "${v[1]}" does not parse`); });
  const d = defaults(m), v0 = Object.fromEntries(d.map(i => [i.sym, i.si])), a0 = Object.fromEntries((m.assumptions || []).map(a => [a.id, a.on]));
  const r0 = runModel(m, v0, a0);
  if (r0.status !== 'computed') { fail(m, `solve failed at defaults: ${r0.error}`); continue; }
  if (!r0.scalars.length) fail(m, 'no scalars returned');
  if (!r0.series.length && !r0.fields.length && !r0.anims.length && !r0.paths.length) warn(m, 'no series/fields/anims: nothing to plot');
  r0.scalars.forEach(s => { if (typeof s.value !== 'number' || (!Number.isFinite(s.value) && !s.text)) fail(m, `scalar ${s.sym} not finite at defaults (${s.value})`); if (!tryUnit(s.unit)) fail(m, `scalar ${s.sym}: unit "${s.unit}" does not parse`); if (s.show && !tryUnit(s.show)) fail(m, `scalar ${s.sym}: show unit "${s.show}" does not parse`); });
  r0.series.forEach(s => { if (!s.x || !s.y || !s.y.length) fail(m, `series ${s.id} malformed`); else s.y.forEach(y => { if (y.data.length !== s.x.data.length && !s.kind?.match(/bar/)) fail(m, `series ${s.id}/${y.label}: length mismatch`); if (y.data.some(q => typeof q !== 'number')) fail(m, `series ${s.id}/${y.label}: non-numeric`); if (!y.data.some(Number.isFinite)) fail(m, `series ${s.id}/${y.label}: no finite values`); }); });
  r0.fields.forEach(f => { if (!Array.isArray(f.data) || !f.data.length || !f.data[0].length) fail(m, `field ${f.id} malformed`); });
  r0.checks.forEach(c => { if (!c.pass) fail(m, `check "${c.name}" fails at defaults (${c.value})`); });
  // equations + verification
  for (const flip of [null, ...(m.assumptions || []).map(a => a.id)]) {
    const a = { ...a0 }; if (flip) a[flip] = !a[flip];
    let eqs;
    try { eqs = m.equations(a, v0); } catch (e) { fail(m, `equations() threw${flip ? ` with ${flip} flipped` : ''}: ${e.message}`); continue; }
    const r = flip ? runModel(m, v0, a) : r0;
    if (r.status !== 'computed') { fail(m, `solve failed with assumption ${flip} flipped: ${r.error}`); continue; }
    r.scalars.forEach(s => { if (!Number.isFinite(s.value) && !s.text) fail(m, `scalar ${s.sym} not finite with ${flip} flipped`); });
    const inputs = d.map(i => ({ ...i }));
    const table = symbolTable(inputs, m.symbols || {}, r.scalars);
    const ver = verifySystem(eqs, table, inputs.map(i => i.sym));
    ver.records.forEach(q => { const bad = q.steps.find(s => s.ok === false && (s.check === 'Syntax' || s.check === 'Dimensions')); if (bad) fail(m, `equation "${q.id}"${flip ? ` [${flip} flipped]` : ''}: ${bad.text}`); if (q.status === 'incomplete') fail(m, `equation "${q.id}": ${q.steps.find(s => s.ok === null && s.check === 'Dimensions')?.text}`); });
    if (!flip && !eqs.length) fail(m, 'no equations');
  }
  // random sampling inside declared ranges
  const R = rng(99); let bad = 0, firstErr = '';
  for (let k = 0; k < 25; k++) {
    const v = {}; d.forEach(i => { v[i.sym] = i.kind === 'numerical' || i.kind === 'constant' ? i.si : (i.rangeSI[0] > 0 && i.rangeSI[1] / i.rangeSI[0] > 50 ? Math.exp(R.range(Math.log(i.rangeSI[0]), Math.log(i.rangeSI[1]))) : R.range(i.rangeSI[0], i.rangeSI[1])); });
    const r = runModel(m, v, a0);
    if (r.status !== 'computed') { bad++; firstErr = firstErr || r.error; }
  }
  if (bad) fail(m, `solve threw for ${bad}/25 random points inside declared ranges: ${firstErr}`);
  try { (m.benchmarks ? m.benchmarks(v0, a0) : []).forEach(b => { if (!b.pass) fail(m, `benchmark "${b.name}" off by ${(b.rel * 100).toPrecision(3)}% (got ${b.got}, expected ${b.expected})`); }); if (!m.benchmarks) warn(m, 'no benchmarks'); } catch (e) { fail(m, `benchmarks threw: ${e.message}`); }
  for (const set of m.validation || []) for (const c of set.cases) {
    const r = runModel(m, { ...v0, ...c.inputs }, { ...a0, ...(c.assumptions || {}) }), s = r.scalars.find(q => q.sym === c.observable);
    if (!s) { fail(m, `validation "${set.name}": observable ${c.observable} not returned`); continue; }
    const z = c.sigma ? Math.abs(s.value - c.observed) / c.sigma : Math.abs(s.value - c.observed) / Math.abs(c.observed) * 40;
    if (z > 3) warn(m, `validation "${set.name}" ${c.label || ''}: predicted ${s.value} vs observed ${c.observed} (${z.toFixed(1)}σ)`);
  }
  if (m.diagram) { try { const s = m.diagram(v0, a0); if (!/^<svg/.test(s)) fail(m, 'diagram() must return <svg…>'); } catch (e) { fail(m, `diagram threw: ${e.message}`); } } else warn(m, 'no diagram');
  if (m.logicPreset) { try { m.logicPreset.premises.forEach(parseFormula); if (m.logicPreset.conclusion) parseFormula(m.logicPreset.conclusion); } catch (e) { fail(m, `logicPreset: ${e.message}`); } }
  if (!m.experiment) warn(m, 'no experiment plan');
  const ms = r0.ms;
  if (ms > 150 && !m.heavy) warn(m, `solve took ${ms.toFixed(0)} ms; mark heavy: true or speed up`);
  console.log(`ok    ${m.id}  (${r0.scalars.length} scalars, ${r0.series.length} series, solve ${ms.toFixed(1)} ms, total ${(performance.now() - t0).toFixed(0)} ms)`);
}
console.log(`\n${models.length} models, ${fails} failures, ${warns} warnings`);
process.exit(fails ? 1 : 0);
