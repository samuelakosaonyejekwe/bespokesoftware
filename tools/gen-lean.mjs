// Writes a Lean 4 verification file for every model in the library (default inputs and assumptions)
// into lean/generated/.   node tools/gen-lean.mjs [model-id ...]
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { MODELS } from '../js/models/index.js';
import { createInvestigation, compute, leanSource } from '../js/engine/core.js';

const out = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../lean/generated');
fs.mkdirSync(out, { recursive: true });
const only = process.argv.slice(2);
let n = 0; const totals = { dim: 0, reg: 0, hyp: 0, soft: 0 };
for (const m of MODELS) {
  if (only.length && !only.includes(m.id)) continue;
  const mod = [].concat(m.module);
  const inv = createInvestigation({ module: mod.includes(2) ? 2 : 1, prompt: m.summary, modelId: m.id });
  inv.title = m.title; inv.id = m.id;
  const { source, stats } = leanSource(inv, compute(inv));
  fs.writeFileSync(path.join(out, `${m.id.replace(/[^A-Za-z0-9]/g, '_')}.lean`), source);
  Object.keys(totals).forEach(k => { totals[k] += stats[k] || 0; }); n++;
}
console.log(`${n} files written to lean/generated: ${totals.dim} dimensional theorems, ${totals.reg} positivity theorems, ${totals.hyp} stated domain conditions, ${totals.soft} regularised bounds`);
