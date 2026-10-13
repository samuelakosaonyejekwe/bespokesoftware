// End-to-end check of the Parameter response panel for EVERY model in the library and every standard relation: for every
// input and every plottable result, what the page drew is read back and compared with fresh solves made here, outside the
// page, at the same input values; and the page's own accuracy verdict for the curve is collected.
//   node wiring-all.mjs [model-id ...]      (needs the app served on localhost:47391 and the playwright package)
import { chromium } from 'playwright';
import { MODELS } from '../js/models/index.js';
import { ATLAS } from '../js/data/atlas.js';
import { createInvestigation, compute, runModel, useAtlas } from '../js/engine/core.js';
import { fromSI, toSI, tryUnit } from '../js/core/units.js';
const only = process.argv.slice(2), b = await chromium.launch(); let ctx = await b.newContext({ serviceWorkers: 'block', viewport: { width: 1100, height: 900 } }), p = await ctx.newPage(); const errs = []; p.setDefaultTimeout(180000); p.on('pageerror', e => errs.push(e.message));
const items = [...MODELS.map(m => ({ kind: 'model', id: m.id, module: [].concat(m.module || 1)[0], prompt: m.summary })), ...ATLAS.map(a => ({ kind: 'atlas', id: a.id, module: 1, prompt: a.title }))].filter(x => !only.length || only.includes(x.id));
let charts = 0, points = 0, bad = 0, unverified = 0, refined = 0; const t0 = Date.now();
for (const it of items) {
  let inv = createInvestigation({ module: it.module, prompt: it.prompt, modelId: it.kind === 'model' ? it.id : null });
  if (it.kind === 'atlas') { inv.modelId = null; inv.estimate = false; inv.worlds.forEach(w => { w.inputs = {}; }); useAtlas(inv, ATLAS.find(a => a.id === it.id), ''); delete inv.match; }
  const c = compute(inv), model = c.model;
  await p.goto('http://localhost:47391/#/help'); await p.waitForSelector('#main h1, #main h2');
  const id = await p.evaluate(async json => { const Store = await import('/js/core/store.js'); const inv = JSON.parse(json); await Store.saveInvestigation(inv); return inv.id; }, JSON.stringify(inv));
  await p.goto(`http://localhost:47391/#/i/${id}/compute`); await p.waitForSelector('.tabs'); await p.waitForTimeout(500);
  if (!(await p.$('#sw-go')) || !(await p.$$eval('#sw-out option', e => e.length))) { console.log(`${it.id.padEnd(34)} no sweep panel (${c.result.status})`); continue; }
  const ins = await p.$$eval('#sw-in option', e => e.map(o => o.value)); let mC = 0, mBad = 0, mUn = 0;
  for (const iv of ins) { await p.selectOption('#sw-in', iv); await p.waitForTimeout(150);
    for (const ov of await p.$$eval('#sw-out option', e => e.filter(o => !o.disabled).map(o => o.value))) {
      await p.selectOption('#sw-out', ov);
      let d = null, ver = null; for (let k = 0; k < 400; k++) { [d, ver] = await p.$eval('#sw-plot', cv => [cv.plotted, cv.verified]); if (d && d.input === iv && d.output === ov && ver && ver.input === iv && ver.output === ov) break; await p.waitForTimeout(50); }
      if (!d || d.input !== iv || d.output !== ov) { bad++; mBad++; console.log(`  WIRING ${it.id}: chose ${iv} -> ${ov}, chart holds ${d && d.input} -> ${d && d.output}`); continue; }
      charts++; mC++; if (!ver || !ver.ok) { unverified++; mUn++; if (mUn <= 3) console.log(`  UNVERIFIED ${it.id} ${iv} -> ${ov}: ${(await p.$eval('#sw-check', e => e.textContent)).replace(/\s+/g, ' ').slice(0, 230)}`); } if (ver && ver.refined) { refined++; continue; }
      const idx = [...new Set([0, Math.floor(d.x.length / 2), d.x.length - 1, d.x.indexOf(d.present)].filter(k => k >= 0))];
      for (const k of idx) { const xSI = toSI(d.x[k], d.xUnit); let got;
        if (model) { const r = runModel(model, { ...c.v, [iv]: xSI }, c.a, true), s = r.scalars.find(q => q.sym === ov); got = s && Number.isFinite(s.value) ? s.value : NaN; }
        else { const inv2 = JSON.parse(JSON.stringify(inv)); inv2.id = 'x' + k + iv + ov + Math.random(); const sy = inv2.custom.symbols[iv]; if (!sy) continue; sy.value = fromSI(xSI, sy.unit); const s = compute(inv2).result.scalars.find(q => q.sym === ov); got = s && Number.isFinite(s.value) ? s.value : NaN; }
        if (d.shape === 'steps' || d.shape === 'residual') continue; points++;
        const shown = d.y[k], want = Number.isFinite(got) && tryUnit(d.yUnit) ? fromSI(got, d.yUnit) : got, same = (!Number.isFinite(shown) && !Number.isFinite(want)) || Math.abs(shown - want) <= 1e-9 * Math.max(Math.abs(shown), Math.abs(want)) + 1e-300;
        if (!same) { bad++; mBad++; if (mBad <= 3) console.log(`  DIFF ${it.id} ${iv} -> ${ov} at ${d.x[k]} ${d.xUnit}: chart ${shown}, independent ${want} ${d.yUnit}`); } } } }
  console.log(`${it.id.padEnd(34)} ${String(ins.length).padStart(2)} inputs ${String(mC).padStart(4)} charts  ${mBad} disagreements  ${mUn} not verified   [${Math.round((Date.now() - t0) / 1000)} s]`);
  await p.evaluate(async id => { const Store = await import('/js/core/store.js'); await Store.deleteInvestigation(id); }, id).catch(() => {});
}
console.log(`\n${items.length} models and relations; ${charts} charts read back; ${points} plotted points compared with independent solves; ${bad} disagreements; ${unverified} curves the page itself marked not fully verified; ${refined} curves the page recomputed at twice the resolution`);
console.log(errs.length ? `page errors: ${[...new Set(errs)].slice(0, 5).join(' | ')}` : 'no page errors'); await b.close(); process.exit(bad || errs.length ? 1 : 0);
