// Combinations check. tests/check-range.mjs moves one input at a time. Faults that need two things at once are looked
// for here:
//   1. every PAIR of inputs is taken to the four corners of its declared ranges (both low, both high, one of each);
//   2. every assumption is switched in turn and, with it switched, every input is taken to each end of its range.
// At each such point the solve must complete and the model's own conservation checks and exact-solution benchmarks must
// hold. A corner that cannot physically occur must be refused by the model with a stated reason (the solve reporting
// failure with a message, or the affected outputs carrying a text reason), never answered with numbers that fail a check.
//   node tests/check-pairs.mjs [model-id ...]        FRAC=0.02 pulls the corners in by that fraction of the (log) range
import { MODELS } from '../js/models/index.js';
import { defaults, runModel } from '../js/engine/core.js';

const ids = process.argv.slice(2), FRAC = +process.env.FRAC || 0, fail = {}, stat = { models: 0, corners: 0, flips: 0, checks: 0, bench: 0, refused: 0 }, add = (k, x) => { (fail[k] = fail[k] || []).push(x); };
const end = (i, hi) => { const [lo, up] = i.rangeSI; if (!(up > lo)) return i.si; const log = lo > 0 && up / lo > 50, f = hi ? 1 - FRAC : FRAC; let x = log ? Math.exp(Math.log(lo) + f * Math.log(up / lo)) : lo + f * (up - lo); return i.integer ? Math.round(x) : x; };
function probe(m, v, a, where) {
  const r = runModel(m, v, a, true);
  if (r.status !== 'computed') { if (r.error && /[a-z]{4}/i.test(r.error) && !/undefined|null|NaN|not a function|Cannot read|is not defined|Maximum call|Invalid array/i.test(r.error)) { stat.refused++; return; } add(`${m.id}: the solve fails without a stated reason (${String(r.error).slice(0, 60)})`, where); return; }
  r.checks.forEach(c => { stat.checks++; if (c.pass === false) add(`${m.id}: check "${c.name}"`, `${where} (${Number(c.value).toExponential(1)})`); });
  let bs = []; try { bs = m.benchmarks ? m.benchmarks(v, a) || [] : []; } catch (e) { add(`${m.id}: benchmarks throw (${String(e.message).slice(0, 60)})`, where); }
  bs.forEach(b => { stat.bench++; if (!b.pass) add(`${m.id}: benchmark "${b.name}"`, `${where} (got ${Number(b.got).toPrecision(4)}, exact ${Number(b.expected).toPrecision(4)})`); });
}
for (const m of MODELS) { if (ids.length && !ids.includes(m.id)) continue; stat.models++;
  const d = defaults(m), v0 = Object.fromEntries(d.map(i => [i.sym, i.si])), a0 = Object.fromEntries((m.assumptions || []).map(q => [q.id, q.on]));
  const vary = d.filter(q => q.kind !== 'numerical' && q.kind !== 'constant' && q.rangeSI[1] > q.rangeSI[0]);
  for (let p = 0; p < vary.length; p++) for (let q = p + 1; q < vary.length; q++) for (const [hp, hq] of [[0, 0], [0, 1], [1, 0], [1, 1]]) { stat.corners++; const xp = end(vary[p], hp), xq = end(vary[q], hq); probe(m, { ...v0, [vary[p].sym]: xp, [vary[q].sym]: xq }, a0, `${vary[p].sym} = ${xp.toPrecision(3)}, ${vary[q].sym} = ${xq.toPrecision(3)}`); }
  for (const as of m.assumptions || []) { const a = { ...a0, [as.id]: !a0[as.id] }; for (const i of vary) for (const h of [0, 1]) { stat.flips++; const x = end(i, h); probe(m, { ...v0, [i.sym]: x }, a, `[${as.id} ${a[as.id] ? 'on' : 'off'}] ${i.sym} = ${x.toPrecision(3)}`); } }
}
const list = Object.entries(fail);
console.log(`${stat.models} models; ${stat.corners} corners of input pairs and ${stat.flips} assumption-with-extreme-input points; ${stat.checks} checks and ${stat.bench} benchmarks evaluated; ${stat.refused} points refused by the model with a stated reason`);
console.log(`${list.length} problems`); list.slice(0, +process.env.MAX || 400).forEach(([k, l]) => console.log(`  ${k}: ${l.length} — ${l.slice(0, 2).join('; ')}`));
process.exit(list.length ? 1 : 0);
