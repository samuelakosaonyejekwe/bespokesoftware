// Every atlas entry must parse, be dimensionally homogeneous, compute finite results, and be
// reachable from at least one of its own keywords.   node tests/check-atlas.mjs
import { ATLAS } from '../js/data/atlas.js';
import { createInvestigation, compute } from '../js/engine/core.js';
let fails = 0;
for (const a of ATLAS) {
  const inv = createInvestigation({ module: 1, prompt: `${a.kw[0]}: ${a.title}` }), c = compute(inv), errs = [];
  if (inv.atlas !== a.id) errs.push(`its own title and first keyword select "${inv.atlas || inv.modelId || 'nothing'}" instead`);
  else {
    if (c.result.status !== 'computed') errs.push(`not computed: ${c.result.error}`);
    c.verification.records.forEach(r => { const bad = r.steps.find(s => s.ok === false && (s.check === 'Syntax' || s.check === 'Dimensions')); if (bad) errs.push(`${r.lhs}: ${bad.text}`); if (r.status === 'incomplete') errs.push(`${r.lhs}: a symbol has no unit`); });
    c.result.scalars.forEach(s => { if (!Number.isFinite(s.value)) errs.push(`${s.sym} is not finite`); });
    if (!c.result.series.length) errs.push('nothing to plot');
  }
  if (errs.length) { fails++; console.log(`FAIL ${a.id}: ${errs.slice(0, 3).join(' | ')}`); }
}
console.log(`${ATLAS.length} atlas entries, ${fails} failing`);
process.exit(fails ? 1 : 0);
