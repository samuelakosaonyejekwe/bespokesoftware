// Investigation frame: header, workspace tabs, forward/back workspace arrows, the output
// catalogue for each workspace with an honest execution state per output, and persistence.
import { html, raw, join, esc, chip, stateChip, toast, on, $, $$, debounce } from './dom.js';
import { go } from '../app.js';
import * as Store from '../core/store.js';
import { compute, clearCache, READINESS, modelClass } from '../engine/core.js';
import { modelById } from '../models/index.js';
import { workspaces, catalogue } from '../data/catalogue.js';
import { CLASS_NAME } from '../engine/prompt.js';
import * as A from './ws-a.js';
import * as B from './ws-b.js';

const W = { ...A.views, ...B.views };
let current = null;   // { inv }

const REVERSE_TAB = { key: 'reverse', title: 'Reverse Engineering', blurb: 'Work back from results to inputs and equations' };
export const tabsFor = inv => [...workspaces(inv.module), REVERSE_TAB];

/** Execution state of every catalogue output for this investigation. */
export function outputStates(inv, c) {
  const m = c.model, r = c.result, done = r.status === 'computed';
  const f = {
    model: !!m, done, eqs: c.equations.length > 0, logic: !!c.logic, up: inv.uploads.length > 0, tab: inv.uploads.some(u => (u.tables || []).length), geo: inv.uploads.some(u => u.geometry || u.drawing),
    loc: !!inv.location, live: Object.keys(inv.env || {}).length > 0, val: (c.validation || []).length > 0, ben: (c.benchmarks || []).length > 0, exp: !!(m && m.experiment), hypo: !!(m && (m.hypothetical || modelClass(m)[0] === 'III')) || inv.klass.tags.includes('III'),
    opt: !!(m && m.optimise), res: !!(m && m.numerics && m.numerics.resolution), anim: r.anims.length > 0, field: r.fields.length > 0, vec: r.fields.some(x => x.vectors), path: r.paths.length > 0 || r.anims.some(a => a.kind === 'motion'), ser: r.series.length > 0, haz: !!(m && m.hazards), dgm: !!(m && m.diagram),
    worlds: inv.worlds.length > 1, bodies: (inv.bodies || []).length > 0, dom: k => inv.domains.some(d => d.key === k) || (m && m.domains.includes(k)), custom: inv.custom.equations.length > 0, multi: m ? m.domains.length > 1 : false,
  };
  const g = 'generated', co = 'computed', de = 'derived', ve = 'verified', na = 'na', nd = 'needs', od = 'ondemand', ia = 'interactive', pa = 'partial', un = 'unavailable', cd = 'conditional', va = 'validated';
  const M = x => (f.model ? x : pa), D = x => (f.done ? x : un), E = x => (f.eqs ? x : f.custom ? pa : nd), L = x => (f.logic ? x : na);
  const rules = inv.module === 1 ? [
    [1, 16, () => M(g)], [1, 1, () => g], [3, 3, () => g], [12, 13, () => od], [17, 32, () => M(g)], [21, 21, () => (f.dgm ? g : f.geo ? g : na)], [32, 32, () => (f.dgm ? g : na)],
    [33, 48, () => g], [35, 35, () => (f.up ? g : nd)], [40, 40, () => (f.model ? ia : na)], [41, 41, () => od], [42, 42, () => (f.live ? co : f.loc ? g : na)], [43, 43, () => (f.bodies || f.dom('space') ? g : na)], [45, 45, () => (f.live ? co : g)],
    [49, 64, () => g], [54, 54, () => (f.hypo ? cd : na)], [60, 60, () => M(ia)],
    [65, 70, () => E(de)], [71, 73, () => (f.hypo ? cd : od)], [74, 74, () => (f.multi ? E(de) : na)], [75, 75, () => L(co)], [76, 85, () => E(de)], [85, 85, () => na], [86, 89, () => (f.logic ? ve : E(g))], [90, 93, () => E(ve)], [94, 96, () => E(g)],
    [97, 108, () => od], [102, 106, () => (f.hypo ? cd : od)], [109, 109, () => od], [110, 111, () => M(g)], [112, 112, () => co], [113, 113, () => g],
    [114, 128, () => L(co)], [126, 126, () => (m && m.philosophy ? g : L(pa))],
    [129, 152, () => (f.exp ? g : na)], [145, 145, () => nd], [151, 151, () => (f.exp ? g : na)],
    [153, 167, () => M(g)], [156, 156, () => (f.res ? g : na)], [160, 160, () => E(g)], [161, 161, () => L(g)], [162, 162, () => M(od)],
    [168, 171, () => D(co)], [172, 172, () => (f.path ? D(co) : na)], [173, 173, () => (f.field || f.ser ? D(co) : na)], [174, 174, () => (f.vec ? D(co) : na)], [175, 175, () => (f.dom('waves') ? D(co) : na)], [176, 177, () => D(co)],
    [178, 178, () => (f.dom('relativity') ? D(co) : na)], [179, 179, () => (f.dom('quantum') ? D(co) : na)], [180, 181, () => D(pa)], [182, 182, () => M(od)], [183, 183, () => (f.hypo ? D(cd) : na)], [184, 184, () => (f.worlds ? D(co) : M(ia))], [185, 185, () => L(co)],
    [186, 189, () => D(co)], [189, 189, () => M(od)], [190, 193, () => D(co)], [191, 191, () => M(od)],
    [194, 194, () => (f.ser ? D(co) : na)], [195, 195, () => (f.path || f.geo ? co : na)], [196, 196, () => (f.field ? D(co) : na)], [197, 197, () => (f.vec ? D(co) : na)], [198, 198, () => (f.anim ? D(co) : na)], [199, 199, () => (f.dom('relativity') && f.ser ? D(co) : na)], [200, 200, () => (f.dom('quantum') && f.ser ? D(co) : na)],
    [201, 201, () => (f.worlds && f.ser ? co : M(ia))], [202, 202, () => L(co)], [203, 203, () => (f.dgm ? g : na)], [204, 205, () => na], [206, 206, () => (f.loc ? g : na)], [207, 207, () => (f.worlds ? co : M(ia))], [208, 208, () => (f.anim ? ia : na)], [209, 210, () => D(co)], [211, 211, () => (f.hypo && f.dgm ? cd : na)], [212, 212, () => (f.anim ? ia : na)],
    [213, 230, () => M(ia)], [224, 224, () => L(ia)],
    [231, 232, () => E(ve)], [233, 233, () => (f.eqs || f.logic ? g : na)], [234, 234, () => (f.ben ? ve : M(pa))], [235, 235, () => (f.res ? od : na)], [236, 236, () => (f.ben ? ve : na)], [237, 237, () => M(g)], [238, 238, () => nd], [239, 239, () => (f.val ? va : nd)],
    [240, 241, () => M(g)], [242, 243, () => M(od)], [244, 244, () => nd], [245, 245, () => D(co)], [246, 246, () => L(co)], [247, 250, () => M(g)], [249, 249, () => co],
    [251, 275, () => M(g)], [257, 257, () => (f.val ? va : nd)], [260, 260, () => (m && m.philosophy ? g : L(pa))],
    [276, 285, () => (f.exp ? g : na)], [280, 281, () => na], [278, 279, () => (f.exp ? D(co) : na)],
    [286, 309, () => g], [288, 288, () => (f.eqs || f.logic ? g : na)], [291, 291, () => na], [292, 292, () => D(g)], [306, 306, () => M(od)], [307, 307, () => na],
  ] : [
    [1, 12, () => M(g)], [1, 1, () => g],
    [13, 16, () => g], [17, 17, () => od], [18, 19, () => g], [20, 20, () => M(g)], [21, 21, () => (f.live ? co : f.loc ? g : na)], [22, 23, () => (f.geo ? g : nd)], [24, 26, () => M(g)], [27, 27, () => (f.tab ? od : nd)],
    [28, 49, () => E(de)], [28, 33, () => M(g)], [37, 37, () => (f.multi ? E(de) : na)], [43, 44, () => E(ve)], [46, 46, () => E(ve)], [47, 47, () => E(g)], [48, 48, () => E(g)], [49, 49, () => M(g)],
    [50, 63, () => od], [51, 51, () => od], [57, 57, () => M(g)], [62, 62, () => M(g)], [63, 63, () => co],
    [64, 80, () => (f.exp ? g : na)], [80, 80, () => (f.tab ? od : nd)],
    [81, 93, () => M(g)], [81, 84, () => (f.res || f.field ? g : na)], [82, 82, () => (f.geo ? g : na)], [90, 90, () => (f.res ? od : na)], [93, 93, () => M(g)],
    [94, 110, () => D(co)], [95, 96, () => D(co)], [97, 98, () => (f.field || f.ser ? D(co) : na)], [103, 103, () => (f.multi ? D(co) : na)], [104, 104, () => D(pa)], [105, 105, () => M(od)], [106, 106, () => na], [107, 107, () => M(ia)], [108, 108, () => M(od)],
    [111, 111, () => (f.ser ? D(co) : na)], [112, 112, () => (f.path || f.geo ? co : na)], [113, 113, () => (f.field ? D(co) : na)], [114, 114, () => (f.path ? D(co) : na)], [115, 115, () => (f.vec ? D(co) : na)], [116, 117, () => (f.anim ? ia : na)], [118, 118, () => D(co)],
    [119, 119, () => (f.dgm ? g : na)], [120, 122, () => (f.dgm ? pa : na)], [123, 123, () => (f.loc ? g : na)], [124, 125, () => M(ia)], [126, 126, () => D(co)],
    [127, 128, () => nd], [129, 129, () => (f.ben ? ve : M(pa))], [130, 130, () => (f.res ? od : na)], [131, 131, () => (f.ben ? ve : na)], [132, 132, () => na], [133, 133, () => (f.val ? va : nd)], [134, 134, () => nd], [135, 135, () => M(pa)], [136, 136, () => (f.val ? va : nd)],
    [137, 137, () => D(co)], [138, 138, () => M(od)], [139, 140, () => M(od)], [141, 144, () => M(g)], [143, 143, () => co],
    [145, 146, () => (f.opt ? g : M(ia))], [147, 148, () => M(od)], [149, 149, () => na], [150, 152, () => M(od)], [153, 156, () => na], [157, 157, () => M(ia)], [158, 158, () => na], [159, 159, () => M(g)],
    [160, 161, () => (f.haz ? g : na)], [162, 164, () => D(pa)], [163, 163, () => na], [165, 165, () => M(ia)], [166, 168, () => (f.haz ? g : na)], [168, 168, () => na], [169, 169, () => na], [170, 170, () => g],
    [171, 182, () => (f.exp ? pa : na)], [176, 180, () => na], [181, 182, () => (f.exp ? g : na)],
    [183, 195, () => M(ia)], [185, 185, () => (f.worlds ? co : M(ia))],
    [196, 210, () => M(g)], [199, 199, () => (f.val ? va : M(g))], [210, 210, () => od],
    [211, 228, () => g], [215, 215, () => na], [219, 219, () => (f.anim ? ia : D(g))], [223, 223, () => M(od)], [224, 224, () => na], [226, 226, () => g], [227, 227, () => D(co)],
  ];
  const out = {};
  for (const item of catalogue(inv.module)) { let s = na; for (const [a, b, fn] of rules) if (item.id >= a && item.id <= b) s = fn(); out[item.id] = s; }
  return out;
}
const REASON = {
  na: 'Not relevant to this scenario, so it is not populated rather than filled with invented content.', needs: 'Needs measurements or files that have not been supplied.', ondemand: 'Produced when you ask for it in this workspace.',
  interactive: 'Produced as you interact: change something and it updates.', partial: 'Available in part; the missing part needs a model or more information.', unavailable: 'Depends on a computation that has not completed.', conditional: 'Produced, and valid only under the stated hypothetical assumptions.',
};

function frame(inv, c, wsKey) {
  const tabs = tabsFor(inv), i = Math.max(0, tabs.findIndex(t => t.key === wsKey)), ws = tabs[i], prev = tabs[i - 1], next = tabs[i + 1];
  const m = c.model, states = outputStates(inv, c);
  const items = ws.from ? catalogue(inv.module).filter(x => x.id >= ws.from && x.id <= ws.to) : [];
  const count = k => items.filter(x => states[x.id] === k).length;
  const active = items.filter(x => !['na', 'needs', 'unavailable'].includes(states[x.id])).length;
  const allActive = Object.values(states).filter(s => !['na', 'needs', 'unavailable'].includes(s)).length;
  return html`
    <div class="invhead">
      <div class="grow">
        <div class="row" style="margin-bottom:.3rem"><span class="klass">Module ${inv.module}</span>${join(inv.klass.tags, k => html`<span class="chip ${k === 'III' ? 'hypo' : k === 'II' ? 'soft' : 'ok'}" title="${CLASS_NAME[k]}">Class ${k} · ${CLASS_NAME[k]}</span>`)}
          ${inv.mode === 'B' ? chip('Option B · equation discovery', 'live') : inv.mode.startsWith('re') ? chip('Reverse engineering', 'live') : inv.module === 2 ? chip('Option A · first principles', 'mute') : ''}
          <span class="chip ${['bad', 'warn', 'live', 'ok', 'ok'][c.readiness.level]}" title="${c.readiness.why.join(' ')}">Readiness ${c.readiness.level + 1}/5 · ${c.readiness.label}</span></div>
        <h1 id="inv-title" contenteditable="true" spellcheck="false" title="Click to rename">${inv.title}</h1>
        <div class="small dim">${m ? html`Model: <b>${m.title}</b>` : 'No computable model selected'} · World: <b>${(inv.worlds.find(w => w.id === inv.activeWorld) || inv.worlds[0]).name}</b> · ${allActive} of ${Object.keys(states).length} outputs active</div>
      </div>
      ${inv.worlds.length > 1 ? html`<div><label class="f" for="world-sel">Active world</label><select id="world-sel">${join(inv.worlds, w => html`<option value="${w.id}" ${w.id === inv.activeWorld ? raw('selected') : ''}>${w.name}</option>`)}</select></div>` : ''}
    </div>
    <div class="tabs" role="tablist" aria-label="Workspaces">${join(tabs, (t, k) => html`<button class="tab" role="tab" aria-selected="${t.key === ws.key}" data-ws="${t.key}" title="${t.blurb}"><span class="n">${k + 1}</span>${t.title}</button>`)}</div>
    <div class="row spread" style="margin:.2rem 0 .8rem"><div><h2 style="margin:0">${ws.title}</h2><span class="small dim">${ws.blurb}${ws.from ? ` · catalogue outputs ${ws.from}–${ws.to}` : ''}</span></div></div>
    <div id="ws" class="stack"></div>
    ${ws.from ? html`<details style="margin-top:1.2rem"><summary>Output catalogue for this workspace <span class="chip ok">${active} active</span> <span class="chip mute">${items.length - active} not activated</span></summary><div class="body">
      <p class="small dim">Every output the architecture can produce is listed with its present state. Outputs are activated by the scenario; nothing is invented to fill a slot.</p>
      <ul class="cat">${join(items, x => html`<li><span class="id">${x.id}</span>${stateChip(states[x.id])}<span><b>${x.t}.</b> <span class="dim">${x.d}</span>${REASON[states[x.id]] ? html`<br><small>${REASON[states[x.id]]}</small>` : ''}</span></li>`)}</ul></div></details>` : ''}
    <div class="wsnav">
      ${prev ? html`<button data-ws="${prev.key}" class="prev" aria-label="Previous workspace: ${prev.title}"><span class="navarrow back"><svg viewBox="0 0 24 24"><path d="M15 5l-7 7 7 7"/></svg></span><span><small class="dim">Previous</small><b>${prev.title}</b></span></button>` : ''}
      ${next ? html`<button data-ws="${next.key}" class="next" aria-label="Next workspace: ${next.title}"><span class="navarrow fwd"><svg viewBox="0 0 24 24"><path d="M9 5l7 7-7 7"/></svg></span><span><small class="dim">Next</small><b>${next.title}</b></span></button>` : ''}
    </div>`;
}

export async function investigationView([id, wsKey = 'concept']) {
  if (!current || current.inv.id !== id) {
    const inv = await Store.loadInvestigation(id);
    if (!inv) return { title: 'Not found', crumb: 'Not found', html: html`<div class="card"><h2>This investigation is not on this device</h2><p class="dim">It may have been deleted, or created on another device. Investigations are stored locally.</p><a class="btn primary" href="#/saved">Saved investigations</a></div>` };
    inv.custom = inv.custom || { equations: [], symbols: {} }; inv.challenges = inv.challenges || []; inv.versions = inv.versions || []; inv.env = inv.env || {};
    current = { inv }; clearCache();
  }
  const inv = current.inv;
  if (!tabsFor(inv).some(t => t.key === wsKey)) wsKey = 'concept';
  const c = compute(inv);
  const tab = tabsFor(inv).find(t => t.key === wsKey);
  return {
    title: `${tab.title} · ${inv.title}`, crumb: `${inv.title} › ${tab.title}`, html: frame(inv, c, wsKey),
    async after(root) {
      const save = debounce(() => Store.saveInvestigation(inv).catch(e => toast(`Could not save: ${e.message}`)), 400);
      let disposers = [];
      const X = {
        inv, get c() { return compute(inv); }, get model() { return modelById(inv.modelId); }, root, save,
        /** Re-render the whole investigation view, keeping the scroll position. */
        refresh() { const y = window.scrollY; save(); disposers.forEach(d => { try { d(); } catch { /* gone */ } }); disposers = []; const cc = compute(inv); root.innerHTML = `<div>${frame(inv, cc, wsKey).__raw}</div>`; bind(); paint().then(() => window.scrollTo(0, y)); },
        onDispose(fn) { disposers.push(fn); }, go: k => go(`#/i/${inv.id}/${k}`),
      };
      const paint = async () => {
        const view = W[wsKey] || W.concept, v = await view(X), host = $('#ws', root);
        host.innerHTML = v.html && v.html.__raw != null ? v.html.__raw : v.html;
        if (v.after) await v.after(host, X);
      };
      const bind = () => {
        const t = $('#inv-title', root);
        t.addEventListener('blur', () => { const s = t.textContent.trim(); if (s && s !== inv.title) { inv.title = s.slice(0, 140); save(); } });
        t.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); t.blur(); } });
        $('#world-sel', root)?.addEventListener('change', e => { inv.activeWorld = e.target.value; X.refresh(); });
        $('.tab[aria-selected="true"]', root)?.scrollIntoView({ block: 'nearest', inline: 'center' });
      };
      on(root, 'click', '[data-ws]', (_, el) => go(`#/i/${inv.id}/${el.dataset.ws}`));
      bind(); await paint();
      return () => { disposers.forEach(d => { try { d(); } catch { /* gone */ } }); Store.saveInvestigation(inv).catch(() => {}); };
    },
  };
}
export const currentInvestigation = () => (current ? current.inv : null);
export { READINESS };
