// Top-level pages: home, the two prompt interfaces, the reverse-engineering studio,
// saved work, the model library, the field taxonomy, live data sources, settings and help.
import { html, raw, join, esc, chip, toast, on, $, $$, debounce, table, num, when, bytes, tex, section } from './dom.js';
import { go, install, canPromptInstall, isStandalone } from '../app.js';
import { MODELS, modelById } from '../models/index.js';
import * as P from '../engine/prompt.js';
import { createInvestigation, log } from '../engine/core.js';
import * as Store from '../core/store.js';
import { importFile, ACCEPT, FORMATS } from '../core/importers.js';
import * as Conn from '../core/connectors.js';
import { DOMAINS } from '../data/domains.js';
import { PHYSICS_FIELDS, ENGINEERING_FIELDS, SUITES, M1_PHASES, M2_PHASES } from '../data/catalogue.js';
import { fmt } from '../core/units.js';
import { lineChart } from '../core/plot.js';

const EXAMPLES = {
  1: [
    'A twin travels to a star 8 light-years away at 0.8c and returns. How much younger is the travelling twin, and why is the situation not symmetric?',
    'Suppose gravity fell off as 1/r^3 instead of 1/r^2. Would planets still have stable orbits?',
    'Schrödinger\'s cat: if the atom has decayed then the cat is dead. The atom is in a superposition. Is the cat both alive and dead?',
    'A fluid remembers its past electric charge. How would its charge relaxation differ from an ordinary conducting liquid, and how could the difference be measured?',
    'A car runs only on compressed air and recompresses its own air while driving, so it never needs refuelling. Is this possible?',
    'In the Monty Hall game with 3 doors, should I switch?',
    'What if the speed of light were ten times smaller? How would atoms and stars change?',
    'Imagine a traversable wormhole with a 100 m throat. What would a traveller experience and what kind of matter would be needed?',
  ],
  2: [
    'A 20 km subsea gas tieback, 10 inch diameter, in the Gulf of Guinea. Wellhead at 150 bar and 60 °C. Will hydrates form, and how much methanol is needed?',
    'Hydrodynamic slugging in an 8 inch flowline 5 km long with superficial liquid velocity 0.8 m/s and superficial gas velocity 3 m/s. Find the slug frequency, slug length and the load on a bend.',
    'Pressure drop and arrival temperature for a 12 km, 8 inch crude oil pipeline at 250 m3/h, inlet 120 bar and 70 °C, seabed at 4 °C.',
    'Seawater reverse osmosis plant in the Arabian Gulf at 60 bar feed pressure and 45 % recovery. What is the specific energy consumption and brine salinity?',
    'Brine discharge from a desalination outfall through a 60 degree inclined jet into the Red Sea. How far does the dense plume spread and what dilution is reached?',
    'Vortex-induced vibration of a 500 m tensioned riser of 0.3 m diameter in a 1.2 m/s current.',
    'Wave load on a 2 m diameter monopile in 30 m water depth in the North Sea.',
    'Lift, drag and stall speed for a wing with aspect ratio 8 and area 16 m2 at 3000 m altitude.',
    'Perihelion precession of Mercury from the Schwarzschild solution compared with observation.',
    'Thrust and thrust-to-power of an ionic wind thruster with a 30 mm gap at 25 kV. Could it lift its own power supply?',
  ],
  re: [
    'Reverse engineer the wall roughness and viscosity of a pipeline from a measured pressure profile.',
    'Two electrically neutral particles show an unexpected attraction that changes with separation. Determine candidate governing equations and possible mechanisms.',
    'Reverse engineer an unknown metamaterial from its measured acoustic transmission spectrum.',
    'From a measured decay curve of charge against time, decide whether the relaxation is exponential or shows memory.',
  ],
};

let pending = [];   // files attached on a prompt page before the investigation exists

const hero = () => html`
  <section class="hero">
    <h1>From an idea to a <span class="hl">checked scientific investigation</span></h1>
    <p>Describe a thought experiment, a hypothesis or a real engineering problem in your own words. The studio classifies it, completes the missing data and labels where every value came from, derives and verifies the governing equations, runs the simulation on your device, and lets you change assumptions and compare alternative worlds side by side.</p>
    <div class="row">
      <a class="btn primary" href="#/m1">Start a thought experiment</a>
      <a class="btn primary" href="#/m2">Start an engineering simulation</a>
      <a class="btn" href="#/re">Reverse engineer from results</a>
    </div>
  </section>`;

export async function home() {
  const saved = await Store.listInvestigations();
  const nI = MODELS.filter(m => [].concat(m.klass)[0] === 'I').length, nII = MODELS.filter(m => [].concat(m.klass).includes('II')).length, nIII = MODELS.filter(m => [].concat(m.klass).includes('III')).length;
  return {
    title: 'Home', crumb: 'Home',
    html: html`<div class="stack">
      ${hero()}
      <div class="grid g3">
        <a class="card modcard" href="#/m1"><span class="big">1</span><h2>Thought and imaginative experiments</h2><p class="dim">Hypotheses, conjectures, paradoxes and counterfactual worlds. Three classes are handled, alone or mixed: scientifically computable, logically analysable, and speculative.</p><span class="go">Open Module 1 →</span></a>
        <a class="card modcard" href="#/m2"><span class="big">2</span><h2>Scientific, engineering and industrial simulation</h2><p class="dim">Aerospace, marine, offshore and subsea, pipelines, slugging, hydrates, desalination and brine, structures, fluids, relativity and more. Generate a first-principles model or discover a new candidate equation.</p><span class="go">Open Module 2 →</span></a>
        <a class="card modcard" href="#/re"><span class="big">↺</span><h2>Reverse engineering studio</h2><p class="dim">Start from results: measurements, signals, geometry or equations. Reconstruct the inputs and governing model, test whether the answer is unique, and validate on data held back.</p><span class="go">Open the studio →</span></a>
      </div>
      <div class="grid g4">
        <div class="stat"><div class="v">${MODELS.length}</div><div class="l">computable models in the library</div></div>
        <div class="stat"><div class="v">${Object.keys(DOMAINS).length}</div><div class="l">scientific and engineering domains</div></div>
        <div class="stat"><div class="v">${M1_PHASES.reduce((a, p) => a + p.items.length, 0)} + ${M2_PHASES.reduce((a, p) => a + p.items.length, 0)}</div><div class="l">output categories across the two modules</div></div>
        <div class="stat"><div class="v">${Conn.SOURCES.length}</div><div class="l">live scientific data sources</div></div>
      </div>
      ${saved.length ? html`<div class="card"><div class="row spread"><h2>Continue where you left off</h2><a class="btn sm" href="#/saved">All saved work (${saved.length})</a></div>
        <div class="grid g3">${join(saved.slice(0, 6), s => html`<a class="card flat tight modcard" href="#/i/${s.id}/concept"><div class="row"><span class="klass">${s.module === 1 ? 'Module 1' : 'Module 2'}</span>${join(s.klass.tags, k => chip('Class ' + k, 'mute'))}</div><b>${s.title}</b><small>${when(s.updated)}</small></a>`)}</div></div>` : ''}
      <div class="grid g2">
        <div class="card"><h2>What makes a result trustworthy here</h2>
          <ul class="clean">
            <li><b>Every input says where it came from.</b> Yours, a live source with its retrieval time, or supplied by the software and marked as such.</li>
            <li><b>Every equation is checked.</b> Dimensions, closure, and whether any term can diverge on the stated domain. Singular terms get a bounded, smooth replacement, and a Lean 4 proof file is generated.</li>
            <li><b>Mathematics is not mistaken for physics.</b> Results are also compared with exact solutions and with published measurements, and the readiness level says how far the evidence goes.</li>
            <li><b>"Not computable with the present information"</b> is reported plainly, with what is missing.</li>
          </ul></div>
        <div class="card"><h2>Explore</h2>
          <div class="grid g2">
            <a class="btn" href="#/library">Model library</a><a class="btn" href="#/fields">Fields covered</a>
            <a class="btn" href="#/sources">Live data sources</a><a class="btn" href="#/saved">Saved investigations</a>
            <a class="btn" href="#/settings">Install and offline use</a><a class="btn" href="#/help">How it works</a>
          </div>
          <p class="small dim" style="margin-top:.8rem">Library coverage: ${nI} primarily computable, ${nII} with a formal logical structure, ${nIII} speculative or counterfactual.</p></div>
      </div></div>`,
  };
}

function reading(prompt, module) {
  if (prompt.trim().length < 8) return raw('<p class="dim small">Start typing and this panel will show how your prompt is being read: its class, the fields involved, the quantities you gave and the closest models.</p>');
  const ranked = P.rankModels(prompt, MODELS, module), model = P.strongMatch(ranked[0]) ? modelById(ranked[0].id) : null;
  const k = P.classifyClass(prompt, model), doms = P.rankDomains(prompt).slice(0, 5), q = P.extractQuantities(prompt).items, loc = P.locate(prompt);
  return html`
    <div class="row">${join(k.tags, c => html`<span class="klass">Class ${c}</span> <span class="small">${P.CLASS_NAME[c]}</span>`)}${k.hybrid ? chip('hybrid', 'warn') : ''}</div>
    <p class="small dim">${P.CLASS_BLURB[k.primary]}</p>
    ${doms.length ? html`<div>${join(doms, d => html`<span class="tag">${d.name}</span>`)}</div>` : ''}
    ${model ? html`<p class="small" style="margin-top:.5rem"><b>Closest model:</b> ${model.title}${ranked.length > 1 ? html` <span class="dim">(also: ${ranked.slice(1, 3).map(r => r.title).join('; ')})</span>` : ''}</p>` : html`<p class="small note warn">No library model matches closely yet.${ranked[0] ? html` The nearest is <b>${ranked[0].title}</b>; it will be run and marked as a low-confidence match.` : ''} Equations written in your prompt (for example <code>d(x,t) = -k*x</code> with <code>k = 0.3</code>) are simulated directly.</p>`}
    ${q.length ? html`<p class="small"><b>Quantities read from your text:</b> ${join(q.slice(0, 10), x => html`<span class="tag">${x.raw}${x.bare ? '' : ` · ${x.quantity}`}</span>`)}</p>` : html`<p class="small dim">No numbers yet: reference values will be supplied and marked as software-supplied.</p>`}
    ${loc ? html`<p class="small"><b>Location:</b> ${loc.name} — environmental data will be attached.</p>` : ''}`;
}

const uploadZone = (id = 'up') => html`
  <label class="drop" id="${id}-drop" for="${id}-file"><b>Add files</b> — drop them here or tap to choose<br><small>Data, documents, drawings, CAD, meshes, point clouds, images, maps and more. Files stay on this device.</small></label>
  <input type="file" id="${id}-file" multiple hidden accept="${ACCEPT}">
  <div id="${id}-list" class="small"></div>`;
function bindUpload(root, id, onFiles) {
  const drop = $(`#${id}-drop`, root), input = $(`#${id}-file`, root);
  ['dragover', 'dragenter'].forEach(t => drop.addEventListener(t, e => { e.preventDefault(); drop.classList.add('over'); }));
  ['dragleave', 'drop'].forEach(t => drop.addEventListener(t, e => { e.preventDefault(); drop.classList.remove('over'); }));
  drop.addEventListener('drop', e => onFiles([...e.dataTransfer.files]));
  input.addEventListener('change', () => { onFiles([...input.files]); input.value = ''; });
}
export { uploadZone, bindUpload };
const pendingList = () => (pending.length ? `<ul class="clean">${pending.map(p => `<li>${esc(p.rec.name)} <span class="dim">(${bytes(p.rec.size)})</span> — ${p.rec.rejected ? `<span style="color:var(--bad)">${esc(p.rec.summary)}</span>` : esc(p.rec.summary)}</li>`).join('')}</ul>` : '');
async function takeFiles(files, listEl) {
  for (const f of files) { listEl.innerHTML = `${pendingList()}<p><span class="busy"></span> Reading ${esc(f.name)}…</p>`; const rec = await importFile(f); pending.push({ rec, file: f }); }
  listEl.innerHTML = pendingList();
}
async function start(module, mode, prompt, modelId) {
  if (prompt.trim().length < 3 && !modelId) { toast('Describe your idea or problem first.'); return; }
  const inv = createInvestigation({ module, mode, prompt: prompt.trim() || modelById(modelId).summary, modelId });
  for (const p of pending.filter(x => !x.rec.rejected)) { inv.uploads.push(p.rec); await Store.saveUpload(p.rec, p.file); log(inv, `File added: ${p.rec.name} (SHA-256 ${p.rec.sha256.slice(0, 12)}…)`); }
  pending = [];
  await Store.saveInvestigation(inv);
  if (inv.location && inv.location.lat != null) { const locs = Store.prefs.get('locations', []); if (!locs.some(l => l.name === inv.location.name)) { locs.unshift({ name: inv.location.name, lat: inv.location.lat, lon: inv.location.lon }); Store.prefs.set('locations', locs.slice(0, 8)); } }
  go(`#/i/${inv.id}/${mode.startsWith('re') ? 'reverse' : 'concept'}`);
}

export function promptPage(module) {
  pending = [];
  const title = module === 1 ? 'Module 1 — Thought and imaginative experiments' : 'Module 2 — Scientific, engineering and industrial simulation';
  return {
    title: module === 1 ? 'Thought experiments' : 'Engineering simulation', crumb: module === 1 ? 'Module 1' : 'Module 2',
    html: html`<div class="stack">
      <div><h1>${title}</h1><p class="dim">${module === 1 ? 'Type a hypothesis, conjecture, paradox or imagined scenario. It may be established physics, a logical argument, or something that contradicts known laws: each is handled according to its class.' : 'Describe the system, what you know and what you want to find. Give any numbers you have; anything missing is completed for you and clearly marked as software-supplied.'}</p></div>
      <div class="grid g2" style="grid-template-columns:minmax(0,1.5fr) minmax(0,1fr)">
        <div class="card stack">
          ${module === 2 ? html`<div><label class="f">What should the software do?</label>
            <div class="seg" id="opt" role="group" aria-label="Operating option">
              <button aria-pressed="true" data-opt="A" title="Identify the established laws that apply and derive the governing equations">Option A · Generate a first-principles model</button>
              <button aria-pressed="false" data-opt="B" title="Propose candidate new relationships by dimensional analysis, symbolic regression and constrained search">Option B · Discover a new model equation</button>
            </div><p class="small dim" id="opt-help">Governing equations are generated from conservation of mass, momentum, energy, charge and chemical species, closed by stated constitutive relations.</p></div>` : ''}
          <div><label class="f" for="prompt">Your ${module === 1 ? 'idea, hypothesis or thought experiment' : 'scenario'}</label>
            <textarea id="prompt" class="prompt" placeholder="${module === 1 ? 'For example: Suppose a twin travels to a nearby star at 80 % of the speed of light and comes back…' : 'For example: A 20 km subsea gas tieback, 10 inch diameter, wellhead at 150 bar and 60 °C…'}" autofocus spellcheck="true"></textarea></div>
          <div><label class="f">Or begin from an example</label><div class="examples">${join(EXAMPLES[module], e => html`<button type="button" data-ex="${e}">${e.length > 78 ? e.slice(0, 76) + '…' : e}</button>`)}</div></div>
          ${uploadZone()}
          <div class="row"><button class="btn primary" id="go">Create the investigation</button><a class="btn ghost" href="#/library">Browse the model library instead</a></div>
        </div>
        <div class="card"><h3>How your prompt is being read</h3><div id="reading">${reading('', module)}</div></div>
      </div></div>`,
    after(root) {
      const ta = $('#prompt', root), rd = $('#reading', root); let mode = 'A';
      const upd = debounce(() => { rd.innerHTML = reading(ta.value, module).__raw; }, 180);
      ta.addEventListener('input', upd);
      on(root, 'click', '[data-ex]', (_, el) => { ta.value = el.dataset.ex; upd(); ta.focus(); });
      on(root, 'click', '[data-opt]', (_, el) => { mode = el.dataset.opt; $$('[data-opt]', root).forEach(b => b.setAttribute('aria-pressed', String(b === el))); $('#opt-help', root).textContent = mode === 'A' ? 'Governing equations are generated from conservation of mass, momentum, energy, charge and chemical species, closed by stated constitutive relations.' : 'Candidate relationships are proposed by dimensional analysis, symbolic regression on your data and constrained search, then ranked and tested on held-out points. A candidate is a hypothesis: novelty is assessed against the literature searched, never certified.'; });
      bindUpload(root, 'up', f => takeFiles(f, $('#up-list', root)));
      $('#go', root).addEventListener('click', () => start(module, module === 2 ? mode : 'A', ta.value));
      ta.addEventListener('keydown', e => { if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') start(module, module === 2 ? mode : 'A', ta.value); });
    },
  };
}

export function reversePage() {
  pending = [];
  return {
    title: 'Reverse engineering studio', crumb: 'Reverse engineering',
    html: html`<div class="stack">
      <div><h1>Reverse engineering studio</h1><p class="dim">Begin with the outputs — measurements, a response curve, a geometry, a set of equations — and work back to the inputs and the model. The loop is always the same: reconstruct, simulate, compare, refine, then validate on data that was held back.</p></div>
      <div class="grid g2" style="grid-template-columns:minmax(0,1.5fr) minmax(0,1fr)">
        <div class="card stack">
          <div><label class="f">Operating mode</label><div class="seg" id="mode" role="group">
            <button aria-pressed="true" data-mode="re1">Theories and equations</button><button aria-pressed="false" data-mode="re2">Physical systems</button><button aria-pressed="false" data-mode="re12">Combined reconstruction</button></div>
            <p class="small dim" id="mode-help">Infer governing equations, mechanisms and candidate laws from observed or hypothesised behaviour.</p></div>
          <div><label class="f" for="prompt">Describe what you want to reverse engineer</label><textarea id="prompt" class="prompt" placeholder="For example: Reverse engineer the wall roughness and viscosity of a pipeline from its measured pressure profile."></textarea></div>
          <div class="examples">${join(EXAMPLES.re, e => html`<button type="button" data-ex="${e}">${e}</button>`)}</div>
          <div><label class="f" for="pasted">Paste output data (optional) — two or more columns: x, y, and optionally the uncertainty of y</label><textarea id="pasted" style="min-height:90px;font-family:var(--mono);font-size:.85rem" placeholder="distance_km, pressure_bar&#10;0, 120&#10;2, 114.1&#10;4, 108.3"></textarea></div>
          ${uploadZone()}
          <button class="btn primary" id="go">Prepare the reverse-engineering investigation</button>
        </div>
        <div class="card"><h3>What you will get</h3>
          <ul class="clean small"><li>Register of unknowns and a map of which observation constrains which unknown</li><li>Estimated parameters with confidence intervals and correlations</li><li>Identifiability verdict: is the reconstruction unique?</li><li>Measured against simulated response, with residuals</li><li>Competing explanations fitted to the same data</li><li>The next measurement that would separate the candidates</li><li>Validation on points not used for fitting</li><li>Every reconstructed equation verified and exported</li></ul>
          <div class="note">A reconstruction that fits the data used to build it is a candidate, not a finding. Different structures can produce the same response; when they do, the studio says so.</div>
          <h3 style="margin-top:1rem">Accepted formats</h3><div class="small">${join(FORMATS, f => html`<div><b>${f.family}:</b> <span class="dim">${f.exts.map(e => '.' + e).join(' ')}</span></div>`)}</div></div>
      </div></div>`,
    after(root) {
      let mode = 're1'; const ta = $('#prompt', root);
      const HELP = { re1: 'Infer governing equations, mechanisms and candidate laws from observed or hypothesised behaviour.', re2: 'Reconstruct geometry, material and operating parameters of a physical system from measurements, scans and records.', re12: 'Reconstruct the system and its governing model together, simulate, compare and refine.' };
      on(root, 'click', '[data-mode]', (_, el) => { mode = el.dataset.mode; $$('[data-mode]', root).forEach(b => b.setAttribute('aria-pressed', String(b === el))); $('#mode-help', root).textContent = HELP[mode]; });
      on(root, 'click', '[data-ex]', (_, el) => { ta.value = el.dataset.ex; ta.focus(); });
      bindUpload(root, 'up', f => takeFiles(f, $('#up-list', root)));
      $('#go', root).addEventListener('click', async () => {
        const pasted = $('#pasted', root).value.trim();
        if (pasted) { const file = new File([pasted], 'pasted-data.csv', { type: 'text/csv' }); const rec = await importFile(file); if (rec.tables.length) pending.push({ rec, file }); else toast('The pasted text could not be read as a table.'); }
        start(mode === 're1' ? 1 : 2, mode, ta.value);
      });
    },
  };
}

export async function savedPage() {
  const saved = await Store.listInvestigations(), est = await Store.storageEstimate();
  return {
    title: 'Saved investigations', crumb: 'Saved work',
    html: html`<div class="stack"><div class="row spread"><h1>Saved investigations</h1>${est ? html`<span class="pill">${bytes(est.used)} used on this device</span>` : ''}</div>
      ${saved.length ? html`<div class="grid g2">${join(saved, s => html`<div class="card"><div class="row"><span class="klass">Module ${s.module}</span>${join(s.klass.tags, k => chip('Class ' + k, 'mute'))}${s.mode && s.mode.startsWith('re') ? chip('Reverse engineering', 'live') : ''}</div>
        <h3 style="margin-top:.5rem">${s.title}</h3><p class="small dim">${s.prompt.slice(0, 160)}${s.prompt.length > 160 ? '…' : ''}</p>
        <div class="row spread"><small>${when(s.updated)} · ${s.worlds} world${s.worlds > 1 ? 's' : ''}</small><span class="row"><a class="btn sm primary" href="#/i/${s.id}/concept">Open</a><button class="btn sm danger" data-del="${s.id}">Delete</button></span></div></div>`)}</div>`
        : html`<div class="card"><p>Nothing saved yet. Investigations are stored on this device as you work.</p><div class="row"><a class="btn primary" href="#/m1">Start a thought experiment</a><a class="btn primary" href="#/m2">Start an engineering simulation</a></div></div>`}</div>`,
    after(root) { on(root, 'click', '[data-del]', async (_, el) => { if (!confirm('Delete this investigation and its uploaded files from this device? This cannot be undone.')) return; await Store.deleteInvestigation(el.dataset.del); toast('Deleted'); go('#/saved'); }); },
  };
}

export function libraryPage(_, q) {
  const byDom = {};
  MODELS.forEach(m => { (byDom[m.domains[0]] = byDom[m.domains[0]] || []).push(m); });
  return {
    title: 'Model library', crumb: 'Model library',
    html: html`<div class="stack"><div><h1>Model library</h1><p class="dim">${MODELS.length} computable models. Each carries its equations with origins, assumptions you can switch off, solvers, exact benchmarks, and an experiment plan. Open one directly or let a prompt select it.</p></div>
      <input type="search" id="q" placeholder="Search models, fields and keywords…" value="${q.q || ''}" aria-label="Search the model library">
      <div id="lib">${join(Object.keys(DOMAINS).filter(d => byDom[d]), d => html`<div class="card" data-group style="margin-bottom:.9rem"><h2>${DOMAINS[d].name}</h2><div class="grid g3">${join(byDom[d], m => html`
        <button class="card flat tight modcard" data-model="${m.id}" data-text="${(m.title + ' ' + m.summary + ' ' + m.keywords.join(' ') + ' ' + DOMAINS[d].name).toLowerCase()}">
          <div class="row">${join([].concat(m.klass), k => chip('Class ' + k, k === 'III' ? 'hypo' : k === 'II' ? 'soft' : 'ok'))}${m.hypothetical ? chip('hypothetical law', 'hypo') : ''}<span class="chip mute">Module ${[].concat(m.module).join(' + ')}</span></div>
          <b>${m.title}</b><small>${m.summary}</small></button>`)}</div></div>`)}</div></div>`,
    after(root) {
      const f = () => { const s = $('#q', root).value.toLowerCase().trim(); $$('[data-model]', root).forEach(b => { b.style.display = !s || s.split(/\s+/).every(w => b.dataset.text.includes(w)) ? '' : 'none'; }); $$('[data-group]', root).forEach(g => { g.style.display = $$('[data-model]', g).some(b => b.style.display !== 'none') ? '' : 'none'; }); };
      $('#q', root).addEventListener('input', f); f();
      on(root, 'click', '[data-model]', (_, el) => { const m = modelById(el.dataset.model); const mod = [].concat(m.module); start(mod.includes(2) && !mod.includes(1) ? 2 : mod[0], 'A', '', m.id); });
    },
  };
}

export function fieldsPage() {
  const grp = (g, n0) => html`<div class="card"><h3>${g.group}</h3>${table(['#', 'Field', 'Aspects covered'], g.items.map(i => [i.id, i.t, i.d]))}</div>`;
  return {
    title: 'Fields covered', crumb: 'Fields covered',
    html: html`<div class="stack"><div><h1>Fields and aspects covered</h1><p class="dim">The classification behind the studio: ${PHYSICS_FIELDS.reduce((a, g) => a + g.items.length, 0)} physics and mathematical-physics fields, ${ENGINEERING_FIELDS.reduce((a, g) => a + g.items.length, 0)} engineering disciplines and ${SUITES.length} integrated suites. Categories overlap, and several are enabling methods rather than separate branches.</p></div>
      <div class="card"><h2>Integrated suites</h2>${table(['#', 'Suite', 'Primary coverage'], SUITES.map(s => [s.id, s.t, s.d]))}<p class="small dim" style="margin-top:.5rem">The last suite exists so that experimental hypotheses can be investigated without their predictions being classed as established fact.</p></div>
      <div class="card"><h2>Application domains with specialised outputs</h2>${table(['Domain', 'Typical outputs', 'Models'], Object.entries(DOMAINS).map(([k, d]) => [d.name, d.outputs, MODELS.filter(m => m.domains.includes(k)).length]))}</div>
      <h2>Physics</h2>${join(PHYSICS_FIELDS, g => grp(g))}<h2>Engineering</h2>${join(ENGINEERING_FIELDS, g => grp(g))}</div>`,
  };
}

export function sourcesPage() {
  return {
    title: 'Live data sources', crumb: 'Live data',
    html: html`<div class="stack"><div><h1>Live data sources</h1><p class="dim">Requests go straight from your browser to public scientific services, so freshness does not depend on any single computer or server. Each answer is stored on this device with its retrieval time and is used, marked as cached, when you are offline. Some sources are themselves updated only periodically: polling more often cannot make their observations newer.</p></div>
      <div class="card"><div class="row spread"><h2>Conditions at a place</h2><span class="small dim" id="loc-status"></span></div>
        <div class="row"><input type="search" id="place" placeholder="Place name or “latitude, longitude” — e.g. Aberdeen, or 57.0, 2.5" class="grow" style="flex:1;min-width:200px"><button class="btn primary" id="find">Fetch conditions</button><button class="btn" id="here" title="Use this device's location">Use my location</button></div>
        <div id="env" style="margin-top:.8rem"></div></div>
      <div class="grid g2">
        <div class="card"><div class="row spread"><h2>Space environment</h2><button class="btn sm" data-refresh="space">Refresh</button></div><div id="space"><span class="busy"></span></div></div>
        <div class="card"><div class="row spread"><h2>Near-Earth objects today</h2><button class="btn sm" data-refresh="neo">Refresh</button></div><div id="neo"><span class="busy"></span></div></div>
        <div class="card"><div class="row spread"><h2>Earthquakes, past day (M ≥ 4.5)</h2><button class="btn sm" data-refresh="quakes">Refresh</button></div><div id="quakes"><span class="busy"></span></div></div>
        <div class="card"><div class="row spread"><h2>Open natural events</h2><button class="btn sm" data-refresh="events">Refresh</button></div><div id="events"><span class="busy"></span></div></div>
      </div>
      <div class="card"><h2>Scientific literature</h2><div class="row"><input type="search" id="lit" placeholder="Search published work — e.g. hydrate plug formation subsea tieback" style="flex:1;min-width:200px"><button class="btn primary" id="litgo">Search</button></div><div id="litout" style="margin-top:.8rem"></div></div>
      <div class="card"><h2>All connected sources</h2>${table(['Source', 'Provides', 'Operated by', 'How often the source itself updates', 'Licence', 'Last contact'], Conn.SOURCES.map(s => [raw(`<a href="${s.home}" target="_blank" rel="noopener noreferrer">${esc(s.name)}</a>`), s.gives, s.provider, s.cadence, s.licence, raw(`<span data-src="${s.id}" class="small dim">—</span>`)]))}</div></div>`,
    after(root) {
      const stale = r => (r.stale ? ' <span class="chip warn">cached copy</span>' : '');
      const stamp = r => `<p class="small dim">Retrieved ${esc(Conn.age(r.ts))}${stale(r)}</p>`;
      const paintStatus = () => { const st = Conn.sourceStatus(); $$('[data-src]', root).forEach(el => { const s = st[el.dataset.src]; el.innerHTML = s ? (s.ok ? `<span style="color:var(--ok)">●</span> ${esc(Conn.age(s.at))}` : `<span style="color:var(--warn)">●</span> ${esc(s.error || 'unreachable')}`) : '—'; }); };
      const off = Conn.onStatus(paintStatus);
      const fail = (el, e) => { el.innerHTML = `<p class="note warn">Not available right now: ${esc(e.message)}. Nothing is shown rather than an invented value.</p>`; };
      const loaders = {
        async space(force) { const el = $('#space', root); try { const s = await Conn.spaceWeather(force); el.innerHTML = `<div class="grid g3"><div class="stat"><div class="v">${s.kp ? fmt(s.kp.value, 3) : '—'}</div><div class="l">Planetary K index${s.kp ? ' · ' + esc(String(s.kp.time).replace('T', ' ').slice(0, 16)) : ''}</div></div><div class="stat"><div class="v">${s.wind ? fmt(s.wind.value / 1000, 3) + ' km/s' : '—'}</div><div class="l">Solar-wind speed</div></div><div class="stat"><div class="v">${s.imf ? fmt(s.imf.bz * 1e9, 3) + ' nT' : '—'}</div><div class="l">Interplanetary field B<sub>z</sub></div></div></div><div class="plot" style="margin-top:.6rem"><canvas class="pl" id="kpc"></canvas></div>${s.kp ? stamp(s.kp) : ''}${s.errors.length ? `<p class="small dim">${esc(s.errors.join('; '))}</p>` : ''}`; if (s.kp && s.kp.series.length > 2) lineChart($('#kpc', root), { x: { label: 'Three-hour interval', unit: '', data: s.kp.series.map((_, i) => i - s.kp.series.length + 1) }, y: [{ label: 'Kp', data: s.kp.series.map(p => p.v) }], yLabel: 'Kp', yUnit: '', kind: 'bar' }, { height: 170 }); } catch (e) { fail(el, e); } },
        async neo(force) { const el = $('#neo', root); try { const n = await Conn.nearEarthObjects(force); el.innerHTML = table(['Object', 'Diameter (m)', 'Speed (km/s)', 'Miss distance (lunar distances)'], n.list.slice(0, 8).map(o => [o.name + (o.hazardous ? ' ⚠' : ''), num(`${fmt(o.dMin, 2)}–${fmt(o.dMax, 2)}`), num(fmt(o.speed / 1000, 3)), num(fmt(o.miss / 3.844e8, 3))])).__raw + stamp(n); } catch (e) { fail(el, e); } },
        async quakes(force) { const el = $('#quakes', root); try { const q = await Conn.earthquakes(force); el.innerHTML = table(['Magnitude', 'Region', 'Depth (km)', 'Time'], q.list.slice(0, 8).map(x => [num(fmt(x.mag, 2)), x.place, num(fmt(x.depth / 1000, 3)), when(x.time)])).__raw + stamp(q); } catch (e) { fail(el, e); } },
        async events(force) { const el = $('#events', root); try { const q = await Conn.naturalEvents(force); el.innerHTML = table(['Event', 'Category', 'Latest report'], q.list.map(x => [x.title, x.category || '', x.date ? when(x.date) : ''])).__raw + stamp(q); } catch (e) { fail(el, e); } },
      };
      Object.values(loaders).forEach(f => f(false));
      on(root, 'click', '[data-refresh]', (_, el) => { $('#' + el.dataset.refresh, root).innerHTML = '<span class="busy"></span>'; loaders[el.dataset.refresh](true); });
      const showEnv = async (lat, lon, name) => {
        const el = $('#env', root); el.innerHTML = '<span class="busy"></span> Contacting sources…';
        const { env, errors } = await Conn.environment(lat, lon, { force: true });
        const L = { air_temp: ['Air temperature', v => `${fmt(v - 273.15, 3)} °C`], air_pressure: ['Surface pressure', v => `${fmt(v / 100, 5)} hPa`], wind_speed: ['Wind at 10 m', v => `${fmt(v, 3)} m/s`], humidity: ['Relative humidity', v => `${fmt(v * 100, 3)} %`], air_density: ['Air density', v => `${fmt(v, 4)} kg/m³`], wave_height: ['Significant wave height', v => `${fmt(v, 3)} m`], wave_period: ['Wave period', v => `${fmt(v, 3)} s`], sea_surface_temp: ['Sea-surface temperature', v => `${fmt(v - 273.15, 3)} °C`], current_speed: ['Surface current', v => `${fmt(v, 3)} m/s`], water_depth: ['Water depth', v => `${fmt(v, 4)} m`], seabed_temp: ['Seabed temperature', v => `${fmt(v - 273.15, 3)} °C`], salinity: ['Salinity near the seabed', v => `${fmt(v, 4)} g/kg`], elevation: ['Ground elevation', v => `${fmt(v, 4)} m`] };
        const rows = Object.entries(L).filter(([k]) => env[k]).map(([k, [n, f]]) => [n, raw(`<b>${esc(f(env[k].value))}</b>`), env[k].source, raw(esc(Conn.age(env[k].ts)) + (env[k].stale ? ' <span class="chip warn">cached</span>' : ''))]);
        el.innerHTML = `<p><b>${esc(name)}</b> <span class="dim">(${lat.toFixed(3)}°, ${lon.toFixed(3)}°)</span></p>` + (rows.length ? table(['Quantity', 'Value', 'Source', 'Retrieved'], rows).__raw : '<p class="note warn">No source answered for this point.</p>') + (errors.length ? `<p class="small dim">${esc(errors.join('; '))}</p>` : '') + '<p class="small dim">Seabed temperature and salinity come from a climatology of ship-borne measurements (1972–2013) at the depth returned by the bathymetry source. They are long-term means at one-degree resolution, not today\'s reading; no open service broadcasts live seabed temperature.</p>';
        paintStatus();
      };
      const find = async () => {
        const s = $('#place', root).value.trim(); if (!s) return; const m = /^\s*(-?\d+(?:\.\d+)?)\s*[, ]\s*(-?\d+(?:\.\d+)?)\s*$/.exec(s);
        if (m) return showEnv(+m[1], +m[2], 'Coordinates');
        try { const g = await Conn.geocode(s); if (!g.length) { const loc = P.locate(s); if (loc) return showEnv(loc.lat, loc.lon, loc.name); toast('No place of that name was found.'); return; } showEnv(g[0].lat, g[0].lon, g[0].name); }
        catch (e) { const loc = P.locate(s); if (loc) showEnv(loc.lat, loc.lon, loc.name); else toast(`Place lookup failed: ${e.message}`); }
      };
      $('#find', root).addEventListener('click', find); $('#place', root).addEventListener('keydown', e => { if (e.key === 'Enter') find(); });
      $('#here', root).addEventListener('click', () => { if (!navigator.geolocation) { toast('This device does not offer a location.'); return; } navigator.geolocation.getCurrentPosition(p => showEnv(p.coords.latitude, p.coords.longitude, 'Your location'), () => toast('Location permission was not given.')); });
      const lit = async () => { const q = $('#lit', root).value.trim(), el = $('#litout', root); if (!q) return; el.innerHTML = '<span class="busy"></span>'; try { const r = await Conn.literature(q, 8); el.innerHTML = r.results.length ? table(['Title', 'Authors', 'Year', 'Venue', 'Cited by', 'Index'], r.results.slice(0, 12).map(w => [w.doi ? raw(`<a href="https://doi.org/${esc(w.doi)}" target="_blank" rel="noopener noreferrer">${esc(w.title)}</a>`) : w.title, w.authors, w.year || '', w.venue, num(w.cited ?? ''), w.via])).__raw : '<p class="dim">No results.</p>'; if (r.errors.length) el.innerHTML += `<p class="small dim">${esc(r.errors.join('; '))}</p>`; paintStatus(); } catch (e) { fail(el, e); } };
      $('#litgo', root).addEventListener('click', lit); $('#lit', root).addEventListener('keydown', e => { if (e.key === 'Enter') lit(); });
      paintStatus();
      return off;
    },
  };
}

export async function settingsPage() {
  const est = await Store.storageEstimate(); let cfg = { mirrors: [] };
  try { cfg = await (await fetch('config.json', { cache: 'no-cache' })).json(); } catch { /* offline or opened from a file */ }
  const ua = navigator.userAgent, ios = /iPad|iPhone|iPod/.test(ua) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1), android = /Android/.test(ua);
  return {
    title: 'Install and offline use', crumb: 'Settings',
    html: html`<div class="stack"><h1>Install, offline use and resilience</h1>
      <div class="card" id="install-help"><h2>Install on this device</h2>
        ${isStandalone() ? html`<p class="note ok">Installed and running as an application.</p>` : html`
        <div class="row"><button class="btn primary" id="do-install" ${canPromptInstall() ? '' : 'disabled'}>Install now</button><span class="small dim">${canPromptInstall() ? 'One tap: no store, no account.' : 'If the button is inactive, use the steps for your device below.'}</span></div>`}
        <div class="grid g3" style="margin-top:.8rem">
          <div class="stat" ${ios ? 'style="border-color:var(--accent)"' : ''}><b>iPhone and iPad</b><ol class="clean small"><li>Open this page in Safari.</li><li>Tap the Share button.</li><li>Choose <b>Add to Home Screen</b>, then <b>Add</b>.</li></ol></div>
          <div class="stat" ${android ? 'style="border-color:var(--accent)"' : ''}><b>Android</b><ol class="clean small"><li>Open this page in Chrome, Edge, Samsung Internet or Firefox.</li><li>Tap the browser menu (⋮).</li><li>Choose <b>Install app</b> or <b>Add to Home screen</b>.</li></ol></div>
          <div class="stat" ${!ios && !android ? 'style="border-color:var(--accent)"' : ''}><b>Windows, macOS, Linux, ChromeOS</b><ol class="clean small"><li>In Chrome or Edge, use the install icon in the address bar, or the menu → <b>Install Bespoke</b>.</li><li>In Safari on macOS: File → <b>Add to Dock</b>.</li></ol></div>
        </div></div>
      <div class="grid g2">
        <div class="card"><h2>Offline and aeroplane mode</h2><p>After the first visit the whole application — solvers, model library, verification, plotting, exports — is stored on the device and runs with no connection. Investigations and uploaded files are kept in on-device storage.</p>
          <dl class="kv"><dt>Offline shell</dt><dd id="sw-state">checking…</dd><dt>Storage used</dt><dd>${est ? `${bytes(est.used)} of about ${bytes(est.quota)} available` : 'not reported by this browser'}</dd><dt>Protected from eviction</dt><dd id="persist">—</dd></dl>
          <div class="row" style="margin-top:.6rem"><button class="btn" id="persist-btn">Ask the browser to keep my data</button><button class="btn" id="update">Check for an update</button></div>
          <p class="small dim">Offline, live sources cannot be contacted; the last saved values are used and marked as cached.</p><p class="small"><a class="btn sm" href="#/refresh">Refresh all live data now</a> — and on iPhone or iPad, see that page for a way to have the device do it on a timetable.</p></div>
        <div class="card"><h2>Resilience</h2><p>The application is plain static files, so it can be served from any number of independent hosts at once, and it keeps working from an installed copy even if every host is down.</p>
          <dl class="kv"><dt>This copy is served from</dt><dd>${location.origin}${location.pathname.replace(/index\.html$/, '')}</dd><dt>File mirrors used when this host is unreachable</dt><dd>${cfg.mirrors && cfg.mirrors.length ? join(cfg.mirrors, m => html`<div><a href="${m}" rel="noopener noreferrer">${m}</a></div>`) : 'none listed yet'}</dd></dl>
          <div class="row" style="margin-top:.6rem"><a class="btn" href="bespoke-offline.zip" download>Download the complete offline copy (ZIP)</a></div>
          <p class="small dim">The ZIP contains the whole application. Unpack it on any computer or web server and open <code>index.html</code> through a local web server to run it with no outside dependency.</p></div>
      </div>
      <div class="card"><h2>Data source key</h2><p class="small dim">Asteroid data uses NASA's open interface with a shared demonstration key that is rate-limited. If you have your own free key from api.nasa.gov, enter it here; it is stored only on this device.</p>
        <div class="row"><input type="text" id="nasa" placeholder="NASA API key (optional)" style="max-width:360px" autocomplete="off"><button class="btn" id="nasa-save">Save</button></div></div>
      <div class="card"><h2>Privacy and security</h2><ul class="clean small"><li>Your prompts, inputs, files and results stay on this device. There is no account and no analytics.</li><li>Outgoing requests go only to the scientific data sources listed under Live data, and carry only the query (for example a latitude and longitude).</li><li>Uploaded files are hashed, checked against their claimed type and size limits, and parsed as data. Nothing in an upload is ever executed; macros and scripts are ignored.</li><li>Archives are guarded against decompression bombs and path traversal.</li></ul></div></div>`,
    after(root) {
      $('#do-install', root)?.addEventListener('click', install);
      const st = $('#sw-state', root);
      if (!('serviceWorker' in navigator)) st.textContent = 'not supported by this browser'; else navigator.serviceWorker.getRegistration().then(r => { st.innerHTML = r && r.active ? '<span style="color:var(--ok)">●</span> stored on this device and ready' : location.protocol === 'file:' ? 'not available when opened directly from a file; use a local web server' : 'being prepared…'; });
      const p = $('#persist', root); if (navigator.storage && navigator.storage.persisted) navigator.storage.persisted().then(v => { p.textContent = v ? 'yes' : 'not yet'; });
      $('#persist-btn', root).addEventListener('click', async () => { const ok = await Store.persist(); p.textContent = ok ? 'yes' : 'not granted'; toast(ok ? 'The browser will keep this application\'s data.' : 'The browser declined for now; installing the application usually grants this.'); });
      $('#update', root).addEventListener('click', async () => { try { const r = await navigator.serviceWorker.getRegistration(); if (r) { await r.update(); toast('Checked. Any newer version is installed in the background.'); } else toast('Updates are checked automatically when a connection is available.'); } catch { toast('Could not reach the server.'); } });
      const k = $('#nasa', root); try { k.value = localStorage.getItem('bespoke.nasaKey') || ''; } catch { /* ignore */ }
      $('#nasa-save', root).addEventListener('click', () => { try { k.value.trim() ? localStorage.setItem('bespoke.nasaKey', k.value.trim()) : localStorage.removeItem('bespoke.nasaKey'); toast('Saved'); } catch { toast('Storage is not available.'); } });
    },
  };
}

export function helpPage() {
  return {
    title: 'How it works', crumb: 'Help',
    html: html`<div class="stack"><h1>How the studio works</h1>
      <div class="card"><h2>The workflow</h2><ol class="deriv">
        <li><b>Your prompt</b> is preserved exactly and read for its class, fields, quantities and any place it names. It is matched against the full text of every model in the library; if it contains equations of its own, those are assembled into a computable model directly.</li>
        <li><b>Inputs are completed.</b> What you gave is used; what a live source can provide is fetched; the rest is supplied from references. Every value carries its origin, and you can overwrite any of them.</li>
        <li><b>Equations are derived</b> from conservation laws and stated closures, each with its origin and the assumptions it needs.</li>
        <li><b>Mathematics is verified.</b> Dimensions, closure and finiteness are checked on the device; a Lean 4 file is generated for independent machine checking; singular terms are regularised.</li>
        <li><b>The model is solved</b> on your device, with conservation residuals reported.</li>
        <li><b>Physical credibility is assessed</b> separately: exact benchmarks, published measurements, your own data, uncertainty and sensitivity.</li>
        <li><b>You challenge it.</b> Switch assumptions off, branch alternative worlds, compare them side by side and see which conclusions depend on which assumptions.</li>
        <li><b>Everything exports</b>: report, LaTeX, Lean, Python, MATLAB, C++, data, figures and a reproducible package.</li></ol></div>
      <div class="grid g3">${join(['I', 'II', 'III'], k => html`<div class="card"><span class="klass">Class ${k}</span><h3 style="margin-top:.5rem">${P.CLASS_NAME[k]}</h3><p class="small">${P.CLASS_BLURB[k]}</p></div>`)}</div>
      <div class="card"><h2>What "verified" does and does not mean</h2>
        <p>A proof assistant can establish that a statement follows from its hypotheses. It cannot establish that the hypotheses describe nature. The studio therefore keeps five separate levels and never skips one:</p>
        <ol class="clean"><li>Untested hypothesis</li><li>Internally consistent formulation — dimensions, closure and finiteness established</li><li>Numerically verified model — reproduces exact solutions</li><li>Empirically supported model — agrees with published measurements within their uncertainty</li><li>Independently validated model — agrees with your own data that was not used to fit anything</li></ol>
        <p class="small dim">On finiteness: every algebraic relation is tested for terms that can diverge on the declared ranges, and a bounded, smooth replacement is generated when one is found. Time-dependent equations that you supply are integrated through a smooth cap on every rate of change; a proved lemma then guarantees that no variable can reach infinity in finite time, and the run reports whether the cap was ever active — if it was, the equations as written would have blown up. For the partial differential equations inside library models, boundedness is checked for the specific run and reported with its conservation residuals; a general guarantee does not exist for all such equations.</p></div>
      <div class="card"><h2>Understanding the labels on inputs</h2>${table(['Label', 'Meaning'], [['User-supplied', 'You typed it, or it was read from your prompt.'], ['Uploaded', 'Read from a file you provided.'], ['Software-retrieved', 'Fetched from a named external source; the retrieval time is shown.'], ['Software-derived', 'Calculated from other inputs.'], ['Software-estimated', 'From bundled climatology or correlations, with stated uncertainty.'], ['Software-supplied', 'A reference value adopted because none was given. Not a measurement of your system.'], ['Hypothetical', 'Invented or altered for a counterfactual world.'], ['Unresolved', 'Cannot be determined from what is available.']])}</div>
      <div class="card"><h2>Keyboard</h2><p class="small"><code>Alt</code> + <code>←</code> / <code>→</code> go back and forward. <code>Ctrl</code> + <code>Enter</code> in a prompt box creates the investigation.</p></div></div>`,
  };
}
/** Refresh every live feed and every saved location in one go. Opened by hand, or on a schedule by the device. */
export function refreshPage() {
  return {
    title: 'Refresh live data', crumb: 'Refresh',
    html: html`<div class="stack"><h1>Refreshing live data</h1><div class="card"><div id="rf"><span class="busy"></span> Contacting sources…</div></div>
      <div class="card"><h3>Keep data fresh on a schedule</h3><p class="small">Opening this page refreshes everything and stores it for offline use. On an iPhone or iPad, which does not let web applications refresh in the background, the system's own Shortcuts app can open it for you on a timetable:</p>
        <ol class="clean small"><li>Open <b>Shortcuts</b> → <b>Automation</b> → <b>New Automation</b> → <b>Time of Day</b>; choose the times and <b>Run Immediately</b>.</li><li>Add the action <b>Open URLs</b> and paste the address below.</li><li>Save. The device now opens this page at those times and the data is refreshed.</li></ol>
        <div class="row"><input type="text" readonly id="rf-url" value="${location.origin + location.pathname}#/refresh" style="flex:1"><button class="btn" id="rf-copy">Copy</button></div>
        <p class="small dim">On Android and on desktop Chrome or Edge, the installed application refreshes in the background by itself.</p></div></div>`,
    async after(root) {
      $('#rf-copy', root).addEventListener('click', () => { navigator.clipboard.writeText($('#rf-url', root).value).then(() => toast('Address copied')).catch(() => toast('Select the address and copy it')); });
      const locs = Store.prefs.get('locations', []), out = $('#rf', root), t0 = Date.now();
      try {
        await Conn.refreshAll(locs);
        const st = Conn.sourceStatus(), ok = Object.values(st).filter(s => s.ok).length, bad = Object.entries(st).filter(([, s]) => !s.ok);
        out.innerHTML = `<p class="note ok"><b>Done in ${((Date.now() - t0) / 1000).toFixed(1)} s.</b> ${ok} source(s) answered${locs.length ? `, including conditions at ${locs.length} saved location(s): ${locs.map(l => esc(l.name)).join('; ')}` : ''}. Everything is stored on this device for offline use.</p>${bad.length ? `<p class="small dim">Not reachable just now: ${bad.map(([k, s]) => `${esc(k)} (${esc(s.error || 'no answer')})`).join('; ')}. Their last saved values remain in use.</p>` : ''}<p class="small dim">${when(Date.now())}</p>`;
      } catch (e) { out.innerHTML = `<p class="note warn">Refresh could not complete: ${esc(e.message)}. Saved values remain in use.</p>`; }
    },
  };
}
export const notFound = () => ({ title: 'Not found', crumb: 'Not found', html: html`<div class="card"><h2>That page does not exist</h2><a class="btn primary" href="#/">Return home</a></div>` });
