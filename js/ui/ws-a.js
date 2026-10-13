// Workspaces: concept, system design, inputs and sources, foundational principles,
// equations, equation discovery, and logic.
import { html, raw, join, esc, chip, provChip, tex, toast, on, $, $$, table, num, section, unitChoices, showScalar, when, bytes, copy, debounce } from './dom.js';
import { equationCard, scalarsTable, statGrid, symTexSafe, drawResults, seriesCard } from './widgets.js';
import { uploadZone, bindUpload } from './pages.js';
import * as Eng from '../engine/core.js';
import * as P from '../engine/prompt.js';
import { MODELS, modelById } from '../models/index.js';
import { DOMAINS, LAWS } from '../data/domains.js';
import { CONSTANTS, ENV_KEYS, BODIES } from '../data/reference.js';
import { fmt, fromSI, toSI, tryUnit, dimToString, dimToSI, quantityName, dimEq } from '../core/units.js';
import * as E from '../core/expr.js';
import * as Logic from '../core/logic.js';
import { buckinghamPi, piToExpr, dimensionalLaw, symbolicRegression, powerLawFit, sindy, NOVELTY_NOTE } from '../core/discover.js';
import { importFile, findEquations } from '../core/importers.js';
import * as Store from '../core/store.js';
import * as Conn from '../core/connectors.js';
import { lineChart, view3d, drawing2d } from '../core/plot.js';
import { leanLiveUrl } from '../core/lean.js';
import { checkLean, cached as leanCached, sourceHash } from '../core/leancheck.js';
import { download, slug } from '../core/exporters.js';

const para = t => join([].concat(t || []), p => html`<p>${p}</p>`);
const list = a => (a && a.length ? html`<ul class="clean">${join(a, x => html`<li>${x}</li>`)}</ul>` : raw('<p class="dim small">None recorded.</p>'));

/** Literature search box shared by several workspaces. */
export const litBox = (q, id = 'lit') => html`<div class="row"><input type="search" id="${id}-q" value="${q}" style="flex:1;min-width:180px" aria-label="Literature query"><button class="btn" id="${id}-go">Search the literature</button></div><div id="${id}-out" class="small" style="margin-top:.5rem"></div>`;
export function bindLit(root, id = 'lit') {
  const run = async () => {
    const q = $(`#${id}-q`, root).value.trim(), out = $(`#${id}-out`, root); if (!q) return; out.innerHTML = '<span class="busy"></span> Asking two independent indexes…';
    try { const r = await Conn.literature(q, 8); out.innerHTML = (r.results.length ? table(['Title', 'Authors', 'Year', 'Venue', 'Cited by'], r.results.slice(0, 10).map(w => [w.doi ? raw(`<a href="https://doi.org/${esc(w.doi)}" target="_blank" rel="noopener noreferrer">${esc(w.title)}</a>`) : w.title, w.authors, w.year || '', w.venue, num(w.cited ?? '')])).__raw : '<p>No matching records.</p>') + `<p class="dim">Searched Crossref and OpenAlex ${esc(Conn.age(r.results[0] ? r.results[0].ts : Date.now()))}. ${esc(NOVELTY_NOTE)}</p>`; }
    catch (e) { out.innerHTML = `<p class="note warn">The literature indexes could not be reached (${esc(e.message)}). No prior-art statement is made.</p>`; }
  };
  $(`#${id}-go`, root).addEventListener('click', run); $(`#${id}-q`, root).addEventListener('keydown', e => { if (e.key === 'Enter') run(); });
}

// =================================================================== concept
function concept(X) {
  const { inv } = X, c = X.c, m = c.model, k = inv.klass, r = c.result;
  const software = c.inputs.filter(i => ['SUPPLIED', 'ESTIMATED'].includes(i.prov)).length, user = c.inputs.filter(i => i.prov === 'USER' || i.prov === 'UPLOAD').length, hyp = c.inputs.filter(i => i.prov === 'HYPOTHETICAL').length;
  const feas = !m ? ['Not computable with the present information', 'warn', 'No computable model is attached. This is a finding, not a failure: the sections below say what is missing.']
    : r.status !== 'computed' ? ['Model selected but the computation failed', 'bad', r.error || '']
      : m.hypothetical || k.primary === 'III' ? ['Mathematically computable; physically speculative', 'hypo', 'The simulation follows its stated rules. Whether those rules occur in nature is a separate, empirical question.']
        : c.logic && k.primary === 'II' ? ['Logically decidable and numerically computable', 'ok', 'The argument has a formal structure that can be checked, and its quantities can be computed.']
          : ['Scientifically computable', 'ok', 'Described by explicit equations with justified inputs.'];
  return {
    html: html`
      ${r.status === 'computed' ? html`<div class="card"><div class="row spread"><h3>Headline results</h3><button class="btn sm" data-ws="${inv.module === 1 ? 'compute' : 'visuals'}">See all results →</button></div>${statGrid(r.scalars, 8)}${join(r.warnings, w => html`<div class="note warn">${w}</div>`)}</div>` : ''}
      <div class="grid g2">
        <div class="card"><h3>Original prompt record</h3><div class="note" id="prompt-view" style="white-space:pre-wrap">${inv.prompt}</div>
          <div class="row"><button class="btn sm" id="edit-prompt">Edit the prompt</button><span class="small dim">Preserved verbatim. Created ${when(inv.created)}.</span></div>
          <div id="prompt-edit" hidden><textarea id="prompt-ta">${inv.prompt}</textarea><div class="row" style="margin-top:.4rem"><button class="btn primary sm" id="prompt-save">Re-read the prompt</button><button class="btn sm" id="prompt-cancel">Cancel</button></div><p class="small dim">Re-reading re-classifies the experiment and re-extracts the quantities you stated. Values you typed into the input table are reset.</p></div></div>
        <div class="card"><h3>Classification</h3>
          ${join(['I', 'II', 'III'], q => html`<div class="row" style="margin:.25rem 0"><span class="chip ${k.tags.includes(q) ? (q === 'III' ? 'hypo' : q === 'II' ? 'soft' : 'ok') : 'mute'}">Class ${q}</span><span class="small grow"><b>${P.CLASS_NAME[q]}</b>${k.cues[q].length ? html` — signalled by: ${k.cues[q].slice(0, 6).join(', ')}` : html` — <span class="dim">no signals</span>`}</span></div>`)}
          <p class="small">${k.hybrid ? 'This is a hybrid investigation: each part is treated according to its own class.' : P.CLASS_BLURB[k.primary]}</p>
          <div class="note ${feas[1] === 'ok' ? 'ok' : feas[1] === 'hypo' ? 'hypo' : feas[1]}"><b>Feasibility: ${feas[0]}.</b> ${feas[2]}</div></div>
      </div>
      ${inv.reading ? html`<div class="note"><b>Read with a language model.</b> ${inv.reading.why || ''} ${inv.reading.choice === 'library' ? html`It pointed to the model <b>${inv.reading.title}</b>.` : inv.reading.choice === 'atlas' ? html`It pointed to the standard relation <b>${inv.reading.title}</b>.` : 'Nothing in the library fitted, so it proposed the equations shown under Equations; they are a hypothesis until the checks there pass and you confirm they describe your system.'}
        ${inv.reading.values && inv.reading.values.length ? html`<br><span class="small">Numbers it took from your words: ${inv.reading.values.map(v => `${v.name} = ${v.value} ${v.unit === '1' ? '' : v.unit} (“${v.quote}”)`).join('; ')}.</span>` : ''}
        ${inv.reading.dropped && inv.reading.dropped.length ? html`<br><span class="small dim">Discarded because it could not be checked: ${inv.reading.dropped.slice(0, 4).join(' ')}</span>` : ''}
        <br><span class="small dim">Source: ${inv.reading.provider}; its own confidence ${Math.round((inv.reading.confidence || 0) * 100)} %. The language model only read the prompt. All results come from the equations and the solver, and are verified in the same way as any other investigation. If the reading is wrong, pick another model below or enter your own equations.</span></div>` : ''}
      ${inv.match && inv.match.confidence === 'low' && !inv.modelId ? html`<div class="note warn"><b>${inv.reading && inv.reading.choice === 'equations' ? 'Equations proposed by a language model.' : inv.estimate ? 'Order-of-magnitude estimate.' : 'Nearest standard relation, low confidence.'}</b> ${inv.match.note} <button class="btn sm" data-ws="equations">See or replace the equation</button></div>` : ''}
      ${inv.match && inv.match.confidence === 'low' && inv.modelId ? html`<div class="note warn"><b>Nearest available model, low confidence.</b> ${inv.match.note} <button class="btn sm" data-ws="equations">Enter my own equations</button> <a class="btn sm" href="#/library">Browse the library</a></div>` : ''}
      <div class="card"><h3>Consolidated scenario</h3>
        ${m ? html`<p>${m.custom ? 'No library model was needed: the equations found in your prompt or entered by you have been assembled into a computable model.' : html`The prompt is read as a question about <b>${m.title.toLowerCase()}</b>.`} ${m.summary}</p>${para(m.background)}${m.diagram && inv.module === 2 ? raw(`<div style="max-width:720px">${m.diagram(c.v, c.a)}</div>`) : ''}`
          : html`<p>The prompt has been recorded and analysed, but it does not correspond closely enough to a model in the library for equations to be solved automatically. You can choose a model below, enter your own equations in the Equations workspace, or continue with the logical and dimensional analysis that needs no model.</p>`}
        ${m && m.phenomena ? html`<p class="small"><b>Mechanisms involved:</b> ${m.phenomena.join(' · ')}</p>` : ''}
        ${m && m.limits ? html`<p class="small"><b>Scope and boundaries:</b> ${m.limits}</p>` : ''}</div>
      <div class="grid g2">
        <div class="card"><h3>Model selection</h3>
          <p class="small dim">Models ranked against your wording. Choosing another re-derives everything.</p>
          <div class="tw"><table><thead><tr><th>Model</th><th>Matched on</th><th></th></tr></thead><tbody>
            ${join(inv.candidates.slice(0, 7), q => html`<tr><td><b>${q.title}</b></td><td class="small dim">${(q.hits || []).slice(0, 4).join(', ') || 'field overlap'}</td><td>${q.id === inv.modelId ? chip('in use', 'ok') : html`<button class="btn sm" data-model="${q.id}">Use</button>`}</td></tr>`)}
            ${!inv.candidates.length ? raw('<tr><td colspan="3" class="dim">No close matches. Browse the library to pick one.</td></tr>') : ''}
          </tbody></table></div>
          <div class="row" style="margin-top:.5rem"><select id="any-model" style="max-width:320px"><option value="">Choose any model from the library…</option>${join(MODELS.slice().sort((a, b) => a.title.localeCompare(b.title)), q => html`<option value="${q.id}">${q.title}</option>`)}</select>${inv.modelId ? html`<button class="btn sm ghost" data-model="">Remove the model</button>` : ''}</div></div>
        <div class="card"><h3>Fields involved</h3>
          ${inv.domains.length ? join(inv.domains, d => html`<div style="margin:.3rem 0"><b>${d.name}</b>${d.hits && d.hits.length ? html` <span class="small dim">— ${d.hits.slice(0, 5).join(', ')}</span>` : ''}<div class="small dim">${DOMAINS[d.key].outputs}</div></div>`) : html`<p class="dim">No specific field was recognised from the wording.</p>`}
          ${inv.domains.length > 1 ? html`<p class="small"><b>Interdisciplinary links:</b> ${inv.domains.slice(0, 3).map(d => d.name).join(' ↔ ')}.</p>` : ''}</div>
      </div>
      <div class="grid g2">
        <div class="card"><h3>Research question and objectives</h3>
          <p><b>Central question.</b> ${inv.title}</p>
          <ul class="clean small">${m ? html`<li>Derive the governing relations from ${(m.laws || []).slice(0, 3).map(l => LAWS[l].name.toLowerCase()).join(', ') || 'first principles'}.</li><li>Compute ${r.scalars.slice(0, 4).map(s => s.name.toLowerCase()).join('; ') || 'the model outputs'}.</li><li>Establish which conclusions survive when each assumption is removed.</li><li>State what evidence would support or refute the result.</li>` : html`<li>Formalise the scenario and identify the quantities and laws involved.</li><li>Determine what further information would make it computable.</li>`}${c.logic ? html`<li>Decide whether the stated conclusion follows from the stated premises.</li>` : ''}</ul>
          <h4 style="margin-top:.8rem">Hypothesis register</h4>
          ${m ? html`<ul class="clean small">${join(c.equations.filter(q => q.kind === 'hypothesis'), q => html`<li>${chip('hypothesis', 'hypo')} ${q.name}: ${q.origin || 'proposed relation'}</li>`)}${join(m.falsify || [], q => html`<li><b>Would be refuted by:</b> ${q}</li>`)}</ul>` : html`<p class="small dim">Add propositions in the Logic workspace or equations in the Equations workspace to register hypotheses.</p>`}</div>
        <div class="card"><h3>What is known, and what is not</h3>
          <dl class="kv"><dt>Inputs you gave</dt><dd>${user}</dd><dt>Supplied by the software</dt><dd>${software}${software ? ' — reference values, not measurements' : ''}</dd><dt>Hypothetical</dt><dd>${hyp}</dd><dt>Stated but not placed</dt><dd>${(inv.unmapped || []).filter(q => !q.bare).length} quantit${(inv.unmapped || []).filter(q => !q.bare).length === 1 ? 'y' : 'ies'}</dd><dt>Evidence files</dt><dd>${inv.uploads.length}</dd></dl>
          ${m && m.refs ? html`<h4 style="margin-top:.8rem">Established sources</h4><ul class="clean small">${join(m.refs, q => html`<li>${q}</li>`)}</ul>` : ''}
          ${m && m.alternatives ? html`<h4>Disputed or alternative views</h4><ul class="clean small">${join(m.alternatives, q => html`<li><b>${q.name}.</b> ${q.text}</li>`)}</ul>` : ''}</div>
      </div>
      <div class="card"><h3>Prior work and novelty</h3><p class="small dim">Search published literature for this scenario. Results come from live indexes and carry their retrieval time.</p>${litBox((m ? m.keywords.slice(0, 3).join(' ') : inv.title).slice(0, 120))}</div>`,
    after(root) {
      bindLit(root);
      $('#edit-prompt', root).addEventListener('click', () => { $('#prompt-edit', root).hidden = false; $('#prompt-ta', root).focus(); });
      $('#prompt-cancel', root).addEventListener('click', () => { $('#prompt-edit', root).hidden = true; });
      $('#prompt-save', root).addEventListener('click', () => {
        const t = $('#prompt-ta', root).value.trim(); if (t.length < 3) return;
        inv.prompt = t; inv.candidates = P.rankModels(t, MODELS, inv.module).slice(0, 8); inv.domains = P.rankDomains(t).slice(0, 6); inv.location = P.locate(t) || inv.location; inv.bodies = P.celestial(t).map(b => b.key);
        const best = P.strongMatch(inv.candidates[0]) ? inv.candidates[0].id : inv.modelId;
        Eng.selectModel(inv, best); const f = Logic.fromText(t); if (f.premises.length) inv.logic = f; Eng.log(inv, 'Prompt edited and re-read'); X.refresh();
      });
      const pick = id => { delete inv.match; Eng.selectModel(inv, id || null); const mm = modelById(id); if (mm && mm.logicPreset && (!inv.logic || inv.logic.premises.length < 2)) inv.logic = JSON.parse(JSON.stringify(mm.logicPreset)); X.refresh(); toast(id ? 'Model changed: equations and results re-derived.' : 'Model removed.'); };
      on(root, 'click', '[data-model]', (_, el) => pick(el.dataset.model));
      $('#any-model', root).addEventListener('change', e => { if (e.target.value) pick(e.target.value); });
    },
  };
}

// =================================================================== system design (Module 1)
function system(X) {
  const c = X.c, m = c.model, inv = X.inv;
  if (!m) return { html: html`<div class="card"><p>System design needs a model. Choose one in <b>Concept &amp; Scenario</b>, or continue with Logic for a purely propositional experiment.</p></div>` };
  const cl = c.verification.closure, ind = cl.independents;
  const dimension = !ind.length ? 'Zero-dimensional: algebraic relations between state quantities' : ind.length === 1 ? `One independent variable (${ind[0]}): the system evolves along it` : `${ind.length} independent variables (${ind.join(', ')}): a field problem`;
  const groups = {}; c.inputs.forEach(i => { (groups[i.kind] = groups[i.kind] || []).push(i); });
  const KN = { geometry: 'Geometry and configuration', fluid: 'Material and fluid properties', operating: 'Operating and initial conditions', environment: 'Environment', numerical: 'Numerical settings', constant: 'Constants of nature', hypothetical: 'Hypothetical parameters' };
  return {
    html: html`
      <div class="grid g2">
        <div class="card"><h3>Conceptual system</h3>${m.diagram ? raw(m.diagram(c.v, c.a)) : html`<p class="dim">No schematic is defined for this model.</p>`}${m.hypothetical ? html`<p class="note hypo small">Illustrative schematic of a hypothetical system. It is a visual aid, not an observation.</p>` : ''}</div>
        <div class="card"><h3>System overview</h3><p>${m.summary}</p>
          <dl class="kv"><dt>Idealisation</dt><dd>${m.numerics ? m.numerics.method : 'Closed-form relations'}</dd><dt>Dimensionality</dt><dd>${dimension}</dd><dt>Degrees of freedom</dt><dd>${cl.nUnknowns} unknown${cl.nUnknowns === 1 ? '' : 's'} determined by ${cl.nEquations} relation${cl.nEquations === 1 ? '' : 's'}</dd><dt>Independent variables</dt><dd>${ind.length ? ind.map(s => (c.table[s] ? `${s} — ${c.table[s].name}` : s)).join('; ') : 'none'}</dd><dt>Reference frame</dt><dd>${m.domains.includes('relativity') ? 'Stated per equation; inertial unless an acceleration is specified' : 'Inertial laboratory frame; SI units'}</dd><dt>Environment</dt><dd>${inv.location ? inv.location.name : inv.bodies && inv.bodies.length ? inv.bodies.map(b => BODIES[b].name).join(', ') : 'Not location-dependent'}</dd></dl>
          ${m.phenomena ? html`<h4 style="margin-top:.7rem">Interactions</h4>${list(m.phenomena)}` : ''}</div>
      </div>
      <div class="card"><h3>Entities, state variables and observables</h3>
        ${join(Object.keys(KN).filter(k => groups[k]), k => html`<h4 style="margin-top:.6rem">${KN[k]}</h4><div>${join(groups[k], i => html`<span class="tag">${tex(symTexSafe(i.sym))} ${i.name}</span>`)}</div>`)}
        <h4 style="margin-top:.6rem">Unknowns and observables</h4>
        ${table(['Symbol', 'Quantity', 'Unit', 'Role'], cl.unknowns.map(s => [tex(symTexSafe(s)), (c.table[s] || {}).name || '—', (c.table[s] || {}).unit || '—', c.result.scalars.some(q => q.sym === s) ? 'computed observable' : 'internal state']))}</div>
      ${m.experiment ? html`<div class="card"><h3>Preparation and external influences</h3><p class="small">${m.experiment.objective}</p><h4>Controls against confounding effects</h4>${list(m.experiment.controls)}</div>` : ''}`,
  };
}

// =================================================================== inputs and sources
const ENV_LABEL = { air_temp: v => `${fmt(v - 273.15, 3)} °C`, seabed_temp: v => `${fmt(v - 273.15, 3)} °C`, sea_surface_temp: v => `${fmt(v - 273.15, 3)} °C`, air_pressure: v => `${fmt(v / 100, 5)} hPa`, humidity: v => `${fmt(v * 100, 3)} %` };
function uploadCard(u) {
  return html`<details ${u.geometry || u.drawing || u.image ? raw('open') : ''}><summary>${u.name} <span class="chip ${u.rejected ? 'bad' : u.tier === 'parsed' ? 'ok' : u.tier === 'summarised' ? 'live' : 'mute'}">${u.rejected ? 'rejected' : u.tier === 'parsed' ? 'read in full' : u.tier === 'summarised' ? 'summary read' : 'registered'}</span> <span class="small dim">${u.family} · ${bytes(u.size)}</span></summary><div class="body">
    <p class="small">${u.summary}</p>${join(u.warnings || [], w => html`<p class="note warn small">${w}</p>`)}
    <dl class="kv small"><dt>SHA-256</dt><dd><code>${u.sha256 || '—'}</code></dd><dt>Content signature</dt><dd>${u.signature || '—'}</dd>${join(Object.entries(u.meta || {}).filter(([, v]) => v !== '' && v != null), ([k, v]) => html`<dt>${k}</dt><dd>${String(v).slice(0, 400)}</dd>`)}</dl>
    ${u.geometry && u.geometry.points && u.geometry.points.length ? html`<div class="plot"><canvas class="pl" data-geo="${u.id}"></canvas></div><p class="small dim">Drag to rotate. ${u.geometry.nVertices.toLocaleString()} points${u.geometry.nFaces ? `, ${u.geometry.nFaces.toLocaleString()} triangles` : ''}; extents ${u.geometry.size.map(v => fmt(v, 4)).join(' × ')} in file units.</p>` : ''}
    ${u.drawing && u.drawing.segs ? html`<div class="plot"><canvas class="pl" data-dwg="${u.id}"></canvas></div>` : ''}
    ${u.image ? html`<img class="imgprev" data-img="${u.id}" alt="${u.name}">` : ''}
    ${join(u.tables || [], (t, ti) => html`<h4>${t.name} — ${t.rows} rows</h4>${table(t.columns.map(col => col.name + (col.unit ? ` (${col.unit})` : '')), Array.from({ length: Math.min(6, t.rows) }, (_, r) => t.columns.map(col => (col.numeric && col.data ? num(fmt(col.data[r], 5)) : (col.text ? col.text[r] : '')))))}<div class="row" style="margin-top:.3rem"><button class="btn sm" data-ws="reverse">Use for reverse engineering</button><button class="btn sm" data-ws="${'evaluation'}">Compare with the model</button></div>`)}
    ${u.text ? html`<pre style="max-height:160px;white-space:pre-wrap">${u.text.slice(0, 1500)}${u.text.length > 1500 ? '…' : ''}</pre><button class="btn sm" data-scan="${u.id}">Look for equations in this text</button>` : ''}
    <div class="row" style="margin-top:.5rem"><button class="btn sm danger" data-rm="${u.id}">Remove this file</button></div></div></details>`;
}
function inputs(X) {
  const { inv } = X, c = X.c, m = c.model, world = inv.worlds.find(w => w.id === inv.activeWorld) || inv.worlds[0];
  const counts = c.inputs.reduce((a, i) => { a[i.prov] = (a[i.prov] || 0) + 1; return a; }, {});
  const suff = !m ? ['No model: nothing to compute yet', 'warn'] : c.result.status === 'computed' ? [`Sufficient: all ${c.inputs.length} inputs are resolved, ${(counts.SUPPLIED || 0) + (counts.ESTIMATED || 0)} of them by the software`, 'ok'] : ['Insufficient: the computation did not complete', 'bad'];
  const loc = inv.location, envKeys = [...new Set(c.inputs.filter(i => i.env).map(i => i.env))];
  return {
    html: html`
      <div class="card"><div class="row spread"><h3>Input data register</h3><div class="row">${join(Object.entries(counts), ([k, n]) => html`<span>${provChip(k)} <b>${n}</b></span>`)}</div></div>
        <div class="note ${suff[1]}"><b>${suff[0]}.</b> Type over any value to make it yours; clear a field to return it to the software. Values supplied by the software are reference values, not measurements of your system.</div>
        ${m ? html`<div class="tw"><table><thead><tr><th>Symbol</th><th>Quantity</th><th>Value</th><th>Unit</th><th>Origin</th><th>Basis</th><th></th></tr></thead><tbody>
          ${join(c.inputs, i => html`<tr><td>${tex(symTexSafe(i.sym))}</td><td>${i.name}${i.env ? html` <span class="tag" title="Can be filled from a live environmental source">${ENV_KEYS[i.env].name}</span>` : ''}</td>
            <td><input type="number" step="any" data-in="${i.sym}" value="${+parseFloat(i.value.toPrecision(10))}" aria-label="${i.name}" ${i.prov === 'HYPOTHETICAL' ? raw('style="border-color:var(--hot)"') : i.overridden ? raw('style="border-color:var(--ok)"') : ''}></td>
            <td><select data-unit="${i.sym}" aria-label="Unit of ${i.name}">${join(unitChoices(i.unit), u => html`<option ${u === i.unit ? raw('selected') : ''}>${u}</option>`)}</select></td>
            <td>${provChip(i.prov)}</td><td class="small dim">${i.note || ''}${i.unc ? html`<br>± ${fmt(i.unc * 100, 2)} %` : ''}</td>
            <td>${i.inWorld ? html`<button class="btn sm ghost" data-reset="${i.sym}" title="Return to the software-supplied value">Reset</button>` : ''}</td></tr>`)}
        </tbody></table></div>
        <p class="small dim">Permitted ranges are enforced in solvers: ${c.inputs.filter(i => i.kind !== 'constant').slice(0, 4).map(i => `${i.sym} ∈ [${fmt(fromSI(i.rangeSI[0], i.unit), 3)}, ${fmt(fromSI(i.rangeSI[1], i.unit), 3)}] ${i.unit}`).join('; ')}…</p>` : html`<p class="dim">Choose a model to see its inputs.</p>`}
      </div>
      ${(inv.extracted || []).length ? html`<div class="card"><h3>Quantities read from your prompt</h3>${table(['As written', 'Kind of quantity', 'In SI', 'Used as'], inv.extracted.map(q => { const used = Object.entries(inv.worlds[0].inputs).find(([, v]) => v.note && v.note.includes(q.raw)); return [q.raw, q.quantity, q.bare ? fmt(q.si) : `${fmt(q.si, 5)} ${dimToSI(q.dim)}`, used ? raw(`<span class="chip user">${esc((c.inputs.find(i => i.sym === used[0]) || {}).name || used[0])}</span>`) : m && !q.bare ? raw(`<select data-assign="${esc(q.raw)}" data-si="${q.si}" data-unit="${esc(q.unit)}"><option value="">not placed — assign to…</option>${c.inputs.filter(i => tryUnit(i.unit) && dimEq(tryUnit(i.unit).dim, q.dim)).map(i => `<option value="${esc(i.sym)}">${esc(i.name)}</option>`).join('')}</select>`) : raw('<span class="dim">not placed</span>')]; }))}</div>` : ''}
      <div class="card"><h3>Location and environment</h3>
        ${loc ? html`<p><b>${loc.name}</b> ${loc.lat != null ? html`<span class="dim">(${loc.lat.toFixed(2)}°, ${loc.lon.toFixed(2)}°)</span>` : ''} — ${loc.source}.</p>` : html`<p class="dim">No place was named. Set one if the experiment depends on where it happens.</p>`}
        <div class="row"><input type="search" id="place" placeholder="Place, sea or “lat, lon”" style="flex:1;min-width:180px"><button class="btn" id="set-place">Set location</button>${loc && loc.lat != null ? html`<button class="btn primary" id="fetch-env">Fetch live conditions</button>` : ''}</div>
        <div id="env-out" style="margin-top:.6rem">${Object.keys(inv.env || {}).length ? table(['Quantity', 'Value', 'Source', 'Retrieved', 'Feeds input'], Object.entries(inv.env).filter(([k]) => ENV_KEYS[k]).map(([k, v]) => [ENV_KEYS[k].name, (ENV_LABEL[k] || (x => `${fmt(x, 4)} ${ENV_KEYS[k].unit}`))(v.value), v.source, raw(esc(Conn.age(v.ts)) + (v.stale ? ' <span class="chip warn">cached</span>' : '')), c.inputs.filter(i => i.env === k).map(i => i.name).join(', ') || '—'])) : ''}</div>
        ${envKeys.length ? html`<p class="small dim">This model can take from the environment: ${envKeys.map(k => ENV_KEYS[k].name.toLowerCase()).join(', ')}. Live values replace climatological estimates when fetched; anything you typed yourself is never overwritten.</p>` : ''}
        ${inv.bodies && inv.bodies.length ? html`<h4 style="margin-top:.7rem">Astronomical data</h4>${table(['Body', 'GM (m³/s²)', 'Mean radius (m)', 'Surface gravity (m/s²)', 'Source'], inv.bodies.map(b => [BODIES[b].name, num(fmt(BODIES[b].GM, 6)), num(fmt(BODIES[b].radius, 5)), num(BODIES[b].g != null ? fmt(BODIES[b].g, 4) : '—'), BODIES[b].src]))}` : ''}</div>
      <div class="card"><h3>Evidence files</h3>${uploadZone('ev')}
        <div style="margin-top:.7rem">${inv.uploads.length ? join(inv.uploads, uploadCard) : html`<p class="small dim">No files yet. Tables become data for calibration and reverse engineering; meshes, point clouds and drawings are previewed and measured; documents are searched for equations.</p>`}</div></div>
      <div class="card"><h3>Reference literature for missing data</h3>${litBox(m ? `${m.title} properties data` : inv.title)}</div>`,
    after(root) {
      bindLit(root);
      const set = (sym, v, unit) => { try { Eng.setInput(inv, world.id, sym, v, unit); X.refresh(); } catch (e) { toast(e.message); } };
      on(root, 'change', '[data-in]', (_, el) => { const i = c.inputs.find(q => q.sym === el.dataset.in), unit = $(`[data-unit="${i.sym}"]`, root).value, v = el.value === '' ? null : parseFloat(el.value); if (v != null) { const si = toSI(v, unit); if (si < i.rangeSI[0] || si > i.rangeSI[1]) toast(`${i.name} is outside the range this model was built for (${fmt(fromSI(i.rangeSI[0], unit), 3)}–${fmt(fromSI(i.rangeSI[1], unit), 3)} ${unit}). Results there are an extrapolation.`, 5000); } set(i.sym, v, unit); });
      on(root, 'change', '[data-unit]', (_, el) => { const i = c.inputs.find(q => q.sym === el.dataset.unit); const v = fromSI(i.si, el.value); world.inputs[i.sym] = { ...(world.inputs[i.sym] || { si: i.si, prov: i.prov, note: i.note }), unit: el.value }; if (!i.overridden) world.inputs[i.sym].prov = i.prov; $(`[data-in="${i.sym}"]`, root).value = +parseFloat(v.toPrecision(10)); X.refresh(); });
      on(root, 'click', '[data-reset]', (_, el) => set(el.dataset.reset, null));
      on(root, 'change', '[data-assign]', (_, el) => { if (!el.value) return; const i = c.inputs.find(q => q.sym === el.value); inv.worlds[0].inputs[i.sym] = { si: +el.dataset.si, prov: 'USER', note: `From your prompt: “${el.dataset.assign}”`, unit: tryUnit(el.dataset.unit) && el.dataset.unit !== 'c' ? el.dataset.unit : i.unit }; Eng.log(inv, `“${el.dataset.assign}” assigned to ${i.name}`); X.refresh(); });
      const setPlace = async () => {
        const s = $('#place', root).value.trim(); if (!s) return; const mm = /^\s*(-?\d+(?:\.\d+)?)\s*[, ]\s*(-?\d+(?:\.\d+)?)\s*$/.exec(s);
        let L = mm ? { name: `${(+mm[1]).toFixed(3)}°, ${(+mm[2]).toFixed(3)}°`, lat: +mm[1], lon: +mm[2], source: 'Coordinates entered by you', marine: true } : P.locate(s);
        if (!L) { try { const g = await Conn.geocode(s); if (g.length) L = g[0]; } catch { /* offline */ } }
        if (!L) { toast('That place was not recognised. Try coordinates such as 57.0, 2.5.'); return; }
        inv.location = L; inv.env = {}; Eng.log(inv, `Location set to ${L.name}`); X.refresh();
      };
      $('#set-place', root).addEventListener('click', setPlace); $('#place', root).addEventListener('keydown', e => { if (e.key === 'Enter') setPlace(); });
      $('#fetch-env', root)?.addEventListener('click', async () => { const out = $('#env-out', root); out.innerHTML = '<span class="busy"></span> Contacting weather, sea-state and bathymetry sources…'; try { const { env, errors } = await Conn.environment(loc.lat, loc.lon, { force: true }); inv.env = env; Eng.log(inv, `Environmental data retrieved for ${loc.name}: ${Object.keys(env).length} quantities`); if (errors.length) toast(errors.join('; '), 5000); X.refresh(); } catch (e) { out.innerHTML = `<p class="note warn">Live sources could not be reached: ${esc(e.message)}. Climatological estimates remain in use.</p>`; } });
      bindUpload(root, 'ev', async files => { const l = $('#ev-list', root); for (const f of files) { l.innerHTML = `<p><span class="busy"></span> Reading ${esc(f.name)}…</p>`; const rec = await importFile(f); if (rec.rejected) { toast(rec.summary, 5000); continue; } inv.uploads.push(rec); await Store.saveUpload(rec, f); Eng.log(inv, `File added: ${rec.name} (SHA-256 ${rec.sha256.slice(0, 12)}…)`); } X.refresh(); });
      on(root, 'click', '[data-rm]', (_, el) => { const u = inv.uploads.find(q => q.id === el.dataset.rm); inv.uploads = inv.uploads.filter(q => q.id !== el.dataset.rm); Eng.log(inv, `File removed: ${u ? u.name : ''}`); X.refresh(); });
      on(root, 'click', '[data-scan]', (_, el) => { const u = inv.uploads.find(q => q.id === el.dataset.scan), found = findEquations(u.text, E.parse); if (!found.length) { toast('No equations in a recognisable form were found in this text.'); return; } found.slice(0, 12).forEach(q => inv.custom.equations.push({ lhs: q.lhs, rhs: q.rhs, name: `From ${u.name}` })); Eng.log(inv, `${Math.min(found.length, 12)} equation(s) read from ${u.name}`); toast(`${Math.min(found.length, 12)} equation(s) added to the equation laboratory for checking.`); X.go('equations'); });
      inv.uploads.forEach(u => { const g = $(`canvas[data-geo="${u.id}"]`, root); if (g && u.geometry) view3d(g, { points: u.geometry.points, tris: u.geometry.tris }, { height: 300 }); const d = $(`canvas[data-dwg="${u.id}"]`, root); if (d && u.drawing) drawing2d(d, u.drawing); const im = $(`img[data-img="${u.id}"]`, root); if (im) Store.loadUploadFile(u.id).then(f => { if (f) { const url = URL.createObjectURL(f); im.src = url; X.onDispose(() => URL.revokeObjectURL(url)); } }); });
    },
  };
}

// =================================================================== foundational principles (Module 1)
function foundations(X) {
  const c = X.c, m = c.model, inv = X.inv, hyp = c.equations.filter(q => q.kind === 'hypothesis');
  const changed = c.inputs.filter(i => i.kind === 'constant' && i.prov === 'HYPOTHETICAL');
  return {
    html: html`
      <div class="card"><h3>Foundational laws and principles</h3><p class="small dim">Laws this investigation rests on, and whether the scenario keeps or alters them.</p>
        ${join(c.generic.laws, k => html`<div class="eq"><div class="eqhead"><b>${LAWS[k].name}</b>${chip(m && (m.laws || []).includes(k) ? 'used by the model' : 'applies to the field', m && (m.laws || []).includes(k) ? 'ok' : 'mute')}${hyp.length && ['energy', 'second', 'gravitation', 'causality'].includes(k) && m && m.hypothetical ? html`<button class="btn sm" data-ws="evaluation" title="Open the conservation and consistency checks computed for this investigation">Hypothetical law in force — see the conservation checks →</button>` : ''}</div>${tex(LAWS[k].tex, true)}<div class="small dim">${LAWS[k].text}</div></div>`)}</div>
      <div class="grid g2">
        <div class="card"><h3>Postulates and hypothetical laws</h3>
          ${hyp.length || changed.length ? html`${join(hyp, q => html`<div class="note hypo"><b>${q.name}.</b> ${q.origin || ''} <code>${q.lhs} = ${q.rhs}</code></div>`)}${join(changed, i => html`<div class="note hypo"><b>${i.name}</b> altered to ${fmt(i.value, 5)} ${i.unit} (accepted value ${fmt(CONSTANTS[i.sym].value, 6)}).</div>`)}<p class="small">Conclusions below are conditional on these. A proof from invented postulates is a conditional mathematical statement, not a fact about the universe.</p>` : html`<p class="small">No hypothetical law or altered constant is in force in this world: the investigation rests on established principles and stated closures.</p>`}
          <h4 style="margin-top:.8rem">Formal premise</h4><p class="small">${m ? `Given ${(m.laws || []).map(l => LAWS[l].name.toLowerCase()).join(', ') || 'the stated relations'}, the assumptions in force, and the inputs registered with their origins, determine ${c.result.scalars.slice(0, 3).map(s => s.name.toLowerCase()).join(', ') || 'the model outputs'}.` : 'No formal premise can be stated until a model or a set of propositions is supplied.'}</p></div>
        <div class="card"><h3>Consistency assessment</h3>
          ${join(c.gates.filter(g => ['B', 'C', 'D'].includes(g.id)), g => html`<div class="gate"><span class="g ${g.status}">${g.id}</span><div><b>${g.name}</b><div class="small dim">${g.text}</div></div></div>`)}
          ${c.logic ? html`<div class="gate"><span class="g ${c.logic.consistent ? 'pass' : 'fail'}">L</span><div><b>Logical consistency of the premises</b><div class="small dim">${c.logic.lines[0]}</div></div></div>` : ''}
          ${(c.result.checks || []).length ? table(['Physical check', 'Residual', 'Tolerance', ''], c.result.checks.map(k => [k.name + (k.note ? ` — ${k.note}` : ''), num(fmt(k.value, 3)), num(fmt(k.tol, 3)), k.pass ? chip('pass', 'ok') : chip('fail', 'bad')])) : ''}</div>
      </div>
      ${m ? html`<div class="card"><div class="row spread"><h3>Assumption register and what depends on each</h3><button class="btn sm primary" data-ws="worlds">Change assumptions →</button></div>
        ${table(['Assumption', 'In force', 'Why it is made', 'Equations that rely on it', 'If removed'], (m.assumptions || []).map(a => [a.text, c.a[a.id] ? chip('yes', 'ok') : chip('removed', 'warn'), a.why || '', c.equations.filter(q => (q.needs || []).includes(a.id)).map(q => q.name).join('; ') || '—', a.alt || '']))}</div>
      <div class="card"><h3>Alternative frameworks</h3>${m.alternatives ? join(m.alternatives, q => html`<p><b>${q.name}.</b> ${q.text}</p>`) : html`<p class="dim small">No competing formulation is recorded for this model.</p>`}</div>` : ''}`,
  };
}

// =================================================================== equations
function leanPanel(X) {
  return html`<div class="card"><div class="row spread"><h3>Machine check by Lean 4</h3><span class="row"><button class="btn sm primary" id="lean-run">Check with Lean now</button><button class="btn sm" id="lean-copy">Copy</button><button class="btn sm" id="lean-dl">Download .lean</button><a class="btn sm" id="lean-open" target="_blank" rel="noopener noreferrer">Open in the Lean editor ↗</a></span></div>
    <div id="lean-result" class="note">Preparing…</div>
    <p class="small dim" id="lean-stats"></p>
    <details><summary>Proof file</summary><div class="body"><pre id="lean-src" style="max-height:340px"></pre></div></details>
    <p class="small dim">Every equation here is translated into Lean theorems and checked by the Lean kernel with the Mathlib library, on the Lean community's public server, as soon as this workspace opens and again whenever an equation or assumption changes. What Lean establishes: each equation is dimensionally homogeneous; denominators and logarithm arguments stay away from their singular sets when the quantities are positive; each regularised term and each capped rate is bounded, so nothing can reach infinity. What Lean cannot establish: that the equations describe nature. That is the job of the benchmarks, measurements and your own data in the evaluation workspace.</p></div>`;
}
function bindLean(root, X) {
  const { source, stats } = Eng.leanSource(X.inv, X.c), out = $('#lean-result', root);
  $('#lean-src', root).textContent = source;
  $('#lean-stats', root).textContent = `${stats.dim} dimensional theorems, ${stats.reg} regularity theorems proved by positivity, ${stats.hyp} domain conditions carried as hypotheses, ${stats.soft} regularised bounds${stats.capped ? `, ${stats.capped} capped-rate guarantees` : ''}${stats.logic ? ', 1 logical theorem' : ''}.`;
  $('#lean-copy', root).addEventListener('click', () => copy(source));
  $('#lean-dl', root).addEventListener('click', () => download(`${slug(X.inv.title)}.lean`, source));
  const url = leanLiveUrl(source); const a = $('#lean-open', root); if (url.length < 60000) a.href = url; else { a.removeAttribute('href'); a.addEventListener('click', () => { copy(source); window.open('https://live.lean-lang.org/', '_blank', 'noopener'); toast('The file is long: it has been copied. Paste it into the editor that just opened.'); }); }
  let alive = true; X.onDispose(() => { alive = false; });
  const show = r => {
    if (!alive) return;
    out.className = `note ${r.ok ? 'ok' : 'bad'}`;
    out.innerHTML = r.ok
      ? `<b>✓ Checked by Lean 4: all ${r.theorems} theorems accepted, no errors.</b> <span class="small">Lean kernel with Mathlib, ${r.cached ? `result of ${esc(when(r.at))}` : `${(r.ms / 1000).toFixed(1)} s`}${r.warnings ? `; ${r.warnings} style warning(s)` : ''}.</span>`
      : `<b>✕ Lean rejected ${r.errors.length} statement(s).</b> The equations concerned are not verified and should be corrected in the equation laboratory.<ul class="clean small">${r.errors.slice(0, 8).map(e => `<li><code>${esc(e.theorem)}</code> (line ${e.line}): ${esc(e.message.split('\n').slice(0, 3).join(' '))}</li>`).join('')}</ul>`;
    if (X.inv.audit[X.inv.audit.length - 1].action.indexOf(r.hash) < 0 && !r.cached) { Eng.log(X.inv, `Lean 4 check ${r.ok ? 'passed' : 'FAILED'}: ${r.theorems} theorems, ${r.errors.length} errors (file ${r.hash})`); X.save(); }
  };
  const run = force => {
    out.className = 'note'; out.innerHTML = '<span class="busy"></span> Connecting to Lean…';
    checkLean(source, { force, onStatus: s => { if (alive) out.innerHTML = `<span class="busy"></span> ${esc(s)}`; } }).then(show).catch(e => { if (!alive) return; out.className = 'note warn'; out.innerHTML = `<b>Lean has not checked this file yet.</b> ${esc(e.message)} The on-device checks above (dimensions, closure, finiteness) are complete and do not depend on a connection.`; });
  };
  $('#lean-run', root).addEventListener('click', () => run(true));
  run(false);
}
function equationLab(X) {
  const { inv } = X, c = X.c, cv = c.customVerification;
  return html`<div class="card"><h3>Equation laboratory</h3><p class="small dim">Enter or paste any equation. It is parsed, checked for dimensional consistency against the units you declare, tested for terms that can diverge, and corrected where a correction can be justified.</p>
    <div class="grid g2"><div><label class="f" for="cl">Left-hand side</label><input type="text" id="cl" placeholder="F" autocomplete="off" spellcheck="false"></div><div><label class="f" for="cr">Right-hand side</label><input type="text" id="cr" placeholder="A/r^n*(1 + alpha*exp(-r/ell))" autocomplete="off" spellcheck="false"></div></div>
    <div class="row" style="margin-top:.5rem"><input type="text" id="cn" placeholder="Name (optional)" style="max-width:260px"><button class="btn primary" id="cadd">Check this equation</button><span class="small dim">Operators + − * / ^, functions sqrt exp ln sin cos tanh…, derivatives d(y,t), pd(u,x).</span></div>
    ${inv.custom.equations.length ? html`
      <h4 style="margin-top:1rem">Symbols in your equations</h4><p class="small dim">Give each symbol a unit and, where you know it, a value and range. Symbols already defined by the model are filled in.</p>
      <div class="tw"><table><thead><tr><th>Symbol</th><th>Meaning</th><th>Unit</th><th>Value</th><th>Minimum</th><th>Maximum</th></tr></thead><tbody>
        ${join([...new Set(cv.records.flatMap(r => r.symbols || []))].filter(s => !c.table[s] || inv.custom.symbols[s]), s => { const d = inv.custom.symbols[s] || {}; return html`<tr><td>${tex(symTexSafe(s))}</td><td><input type="text" data-cs="${s}" data-k="name" value="${d.name || ''}"></td><td><input type="text" data-cs="${s}" data-k="unit" value="${d.unit || ''}" placeholder="e.g. N, m/s, 1"></td><td><input type="number" step="any" data-cs="${s}" data-k="value" value="${d.value ?? ''}"></td><td><input type="number" step="any" data-cs="${s}" data-k="min" value="${d.min ?? ''}"></td><td><input type="number" step="any" data-cs="${s}" data-k="max" value="${d.max ?? ''}"></td></tr>`; })}
      </tbody></table></div>
      <h4 style="margin-top:1rem">Verification of your equations</h4>
      ${join(cv.records, (r, i) => equationCard(r, { kind: 'hypothesis', origin: 'Entered by you' }, [], html`<button class="btn sm ghost danger" data-cdel="${i}">Remove</button>${r.regularised ? html`<button class="btn sm" data-creg="${i}">Replace with the regularised form</button>` : ''}`))}` : ''}</div>`;
}
function bindLab(root, X) {
  const { inv } = X;
  $('#cadd', root).addEventListener('click', () => { const l = $('#cl', root).value.trim(), r = $('#cr', root).value.trim(); if (!l || !r) { toast('Enter both sides of the equation.'); return; } try { E.parse(l); E.parse(r); } catch (e) { toast(`This does not parse: ${e.message}`, 5000); return; } inv.custom.equations.push({ lhs: l, rhs: r, name: $('#cn', root).value.trim() }); Eng.log(inv, `Equation entered: ${l} = ${r}`); X.refresh(); });
  on(root, 'change', '[data-cs]', (_, el) => { const s = el.dataset.cs, d = inv.custom.symbols[s] = inv.custom.symbols[s] || {}; const k = el.dataset.k; if (k === 'unit') { if (el.value && !tryUnit(el.value)) { toast(`“${el.value}” is not a recognised unit.`); return; } d.unit = el.value || '1'; } else if (k === 'name') d.name = el.value; else d[k] = el.value === '' ? undefined : parseFloat(el.value); if (!d.unit) d.unit = '1'; X.refresh(); });
  on(root, 'click', '[data-cdel]', (_, el) => { inv.custom.equations.splice(+el.dataset.cdel, 1); X.refresh(); });
  on(root, 'click', '[data-creg]', (_, el) => { const r = X.c.customVerification.records[+el.dataset.creg], q = inv.custom.equations[+el.dataset.creg]; q.lhs = r.regularised.lhs; q.rhs = r.regularised.rhs; q.name = `${q.name || 'Equation'} (regularised)`; inv.custom.symbols.eps_reg = inv.custom.symbols.eps_reg || { name: 'Regularisation scale', unit: '1', value: 1e-6, min: 1e-9, max: 1e-3 }; Eng.log(inv, 'Equation replaced by its regularised form'); X.refresh(); toast('Replaced. Set the unit of eps_reg to match the softened term.'); });
  on(root, 'click', '[data-repair]', (_, el) => { const [id, k] = el.dataset.repair.split(':'), recs = X.c.customVerification ? X.c.customVerification.records : [], i = recs.findIndex(r => r.id === id); if (i < 0) { toast('Amendments can be adopted for equations in the laboratory.'); return; } const cand = recs[i].repair.candidates[+k]; inv.custom.equations[i].rhs = cand.rhs; inv.custom.equations[i].name = `${inv.custom.equations[i].name || 'Equation'} (amended)`; Eng.log(inv, `Equation amended for dimensional consistency: ${cand.lhs} = ${cand.rhs}`); X.refresh(); });
}
function equations(X) {
  const { inv } = X, c = X.c, m = c.model, ver = c.verification;
  let pi = null; if (m) { try { const qs = c.inputs.filter(i => i.kind !== 'numerical' && i.kind !== 'constant').slice(0, 12).map(i => ({ sym: i.sym, dim: i.dim })); if (qs.length >= 2) pi = buckinghamPi(qs); } catch { pi = null; } }
  return {
    html: html`
      ${m ? html`
      <div class="card"><h3>Verification summary</h3>
        <div class="grid g4"><div class="stat"><div class="v">${ver.summary.total}</div><div class="l">equations</div></div><div class="stat"><div class="v" style="color:var(--ok)">${ver.summary.verified}</div><div class="l">verified outright</div></div><div class="stat"><div class="v" style="color:var(--warn)">${ver.summary.conditional + ver.summary.singular}</div><div class="l">with a domain condition or regularised</div></div><div class="stat"><div class="v" style="color:${ver.summary.inconsistent + ver.summary.rejected ? 'var(--bad)' : 'inherit'}">${ver.summary.inconsistent + ver.summary.rejected + ver.summary.incomplete}</div><div class="l">inconsistent or incomplete</div></div></div>
        <div class="note ${ver.closure.closed ? 'ok' : 'warn'}"><b>Mathematical closure.</b> ${ver.closure.text}${ver.closure.unknowns.length ? ` Unknowns: ${ver.closure.unknowns.join(', ')}.` : ''}</div></div>
      ${c.derivation.length ? html`<div class="card"><h3>Derivation from first principles</h3><ol class="deriv">${join(c.derivation, d => html`<li>${d.text}${d.tex ? tex(d.tex, true) : ''}</li>`)}</ol></div>` : ''}
      <div class="card"><h3>Governing equations</h3><p class="small dim">Regenerated whenever an assumption changes. Each shows where it comes from and the outcome of every check.</p>
        ${m.custom ? html`<p class="small">These are your own equations; each is shown with its checks in the equation laboratory below, where it can also be amended or removed.</p>` : join(ver.records, r => equationCard(r, c.equations.find(q => q.id === r.id) || {}, m.assumptions || []))}</div>
      <div class="grid g2">
        <div class="card"><h3>Symbol register</h3>${table(['Symbol', 'Quantity', 'Unit', 'Dimension'], Object.entries(c.table).filter(([s]) => ver.records.some(r => (r.symbols || []).includes(s))).map(([s, v]) => [tex(symTexSafe(s)), v.name || '', v.unit || '', dimToString(v.dim)]))}</div>
        <div class="card"><h3>Dimensional analysis</h3>${pi ? html`<p class="small">${pi.text}</p>${join(pi.groups.slice(0, 8), (g, i) => html`<div class="eq">${tex(`\\Pi_{${i + 1}} = ${E.toTex(piToExpr(g))}`, true)}</div>`)}` : html`<p class="dim small">Needs at least two dimensional inputs.</p>`}
          <h4 style="margin-top:.8rem">Provenance and dependencies</h4>${table(['Equation', 'Kind', 'Depends on assumptions', 'Uses inputs'], c.equations.map(q => { const r = ver.records.find(x => x.id === q.id) || {}; return [q.name, q.kind, (q.needs || []).map(id => ((m.assumptions || []).find(a => a.id === id) || {}).text || id).join('; ') || '—', (r.symbols || []).filter(s => c.inputs.some(i => i.sym === s)).join(', ') || '—']; }))}</div>
      </div>` : html`<div class="card"><p>No model is attached, so there are no governing equations yet. Enter your own below, or choose a model in <b>Concept &amp; Scenario</b>.</p>${c.generic.pi ? html`<h4>Dimensional analysis of the quantities in your prompt</h4><p class="small">${c.generic.pi.text}</p>${join(c.generic.pi.groups.slice(0, 6), (g, i) => html`<div class="eq">${tex(`\\Pi_{${i + 1}} = ${E.toTex(piToExpr(g))}`, true)}<div class="small dim">${Object.keys(g).map(k => { const q = c.generic.pi.quantities.find(x => x.sym === k); return `${k} = ${q.raw}`; }).join('; ')}</div></div>`)}` : ''}</div>`}
      ${equationLab(X)}
      ${(m && ver.records.length) || inv.custom.equations.length || c.logic ? leanPanel(X) : ''}
      ${inv.module === 1 ? discoveryBody(X) : html`<div class="card"><div class="row spread"><h3>Looking for a new relationship?</h3><button class="btn primary sm" data-ws="discovery">Open equation discovery →</button></div></div>`}`,
    after(root) { bindLab(root, X); if ($('#lean-src', root)) bindLean(root, X); if (inv.module === 1) bindDiscovery(root, X); },
  };
}

// =================================================================== discovery
function numericColumns(inv) { const out = []; inv.uploads.forEach(u => (u.tables || []).forEach((t, ti) => t.columns.forEach((col, ci) => { if (col.numeric && col.data) out.push({ key: `${u.id}|${ti}|${ci}`, label: `${u.name} › ${col.name}${col.unit ? ` (${col.unit})` : ''}`, data: col.data, name: col.name, unit: col.unit }); }))); return out; }
export { numericColumns };
function discoveryBody(X) {
  const { inv } = X, c = X.c, m = c.model, cols = numericColumns(inv);
  const syms = Object.entries(c.table).filter(([, v]) => !v.constant).map(([s, v]) => ({ s, name: v.name }));
  return html`
    <div class="card"><h3>1 · Candidate law from dimensional analysis</h3><p class="small dim">Choose the quantity to be explained and the quantities it may depend on. The form allowed by dimensions alone is derived; what dimensions cannot fix is stated.</p>
      ${syms.length >= 3 ? html`<div class="grid g2"><div><label class="f" for="da-t">Quantity to explain</label><select id="da-t">${join(syms, q => html`<option value="${q.s}">${q.s} — ${q.name || ''}</option>`)}</select></div><div><label class="f" for="da-o">May depend on (hold Ctrl or ⌘ to select several)</label><select id="da-o" multiple size="6">${join(syms, q => html`<option value="${q.s}">${q.s} — ${q.name || ''}</option>`)}</select></div></div><button class="btn primary" id="da-go" style="margin-top:.5rem">Derive the candidate form</button><div id="da-out"></div>` : html`<p class="dim small">Needs a model, or symbols with units declared in the equation laboratory.</p>`}</div>
    <div class="card"><h3>2 · Candidate equations from data</h3><p class="small dim">Interpretable families are fitted to your data on three-quarters of the points and tested on the remaining quarter. Ranking penalises extra parameters.</p>
      ${cols.length >= 2 ? html`<div class="grid g3"><div><label class="f" for="sr-x">Independent variable</label><select id="sr-x">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 0 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div><label class="f" for="sr-y">Quantity to explain</label><select id="sr-y">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 1 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div style="align-self:end" class="row"><button class="btn primary" id="sr-go">Search for equations</button>${cols.length >= 3 ? html`<button class="btn" id="pl-go" title="y as a product of powers of all other columns">Multivariable power law</button>` : ''}<button class="btn" id="sd-go" title="Treat the first column as time and identify differential equations for the others">Identify dynamics</button></div></div><div id="sr-out"></div>` : html`<p class="note warn small">Upload a table with at least two numeric columns in <b>Inputs</b> to activate data-driven discovery.</p>`}</div>
    <div class="card"><h3>3 · Hypothesis catalogue and competing mechanisms</h3>
      ${m && m.alternatives ? table(['Candidate', 'Idea', 'Status'], [[m.title, m.summary, raw(m.hypothetical ? '<span class="chip hypo">hypothetical</span>' : '<span class="chip ok">baseline</span>')], ...m.alternatives.map(q => [q.name, q.text, raw('<span class="chip mute">alternative</span>')])]) : html`<p class="dim small">No alternatives are recorded.</p>`}
      ${m && m.falsify ? html`<h4 style="margin-top:.7rem">Predictions that would discriminate</h4>${list(m.falsify)}` : ''}
      <div class="note"><b>Scientific readiness of any candidate:</b> ${Eng.READINESS.map((q, i) => `${i + 1} ${q.toLowerCase()}`).join(' → ')}. A candidate found here starts at level 1 and moves only with evidence.</div></div>
    <div class="card"><h3>4 · Novelty and prior art</h3><p class="small dim">${NOVELTY_NOTE}</p>${litBox(m ? m.keywords.slice(0, 2).join(' ') + ' equation model' : inv.title, 'nov')}</div>`;
}
function bindDiscovery(root, X) {
  const { inv } = X, c = X.c, cols = numericColumns(inv);
  if ($('#nov-go', root)) bindLit(root, 'nov');
  const adopt = (lhs, rhs, name) => { inv.custom.equations.push({ lhs, rhs, name }); Eng.log(inv, `Candidate adopted: ${lhs} = ${rhs}`); toast('Added to the equation laboratory for verification.'); X.refresh(); };
  $('#da-go', root)?.addEventListener('click', () => {
    const t = $('#da-t', root).value, others = [...$('#da-o', root).selectedOptions].map(o => o.value).filter(s => s !== t), out = $('#da-out', root);
    if (!others.length) { toast('Select at least one quantity it may depend on.'); return; }
    const law = dimensionalLaw({ sym: t, dim: c.table[t].dim }, others.map(s => ({ sym: s, dim: c.table[s].dim })));
    out.innerHTML = law.ok ? `<div class="eq">${tex(`${E.symTex(t)} = ${E.toTex(law.rhs)}${law.unique ? '' : `\\; f\\!\\left(${law.remaining.map(g => E.toTex(piToExpr(g))).join(',\\,')}\\right)`}`, true).__raw}<p class="small">${esc(law.text)}</p><button class="btn sm" id="da-adopt">Adopt as a candidate equation</button></div>` : `<div class="note warn">${esc(law.text)}</div>`;
    $('#da-adopt', root)?.addEventListener('click', () => { inv.custom.symbols.C_0 = inv.custom.symbols.C_0 || { name: 'Dimensionless constant, from theory or experiment', unit: '1', value: 1 }; adopt(t, law.rhs, 'Dimensional-analysis candidate'); });
  });
  const col = k => cols.find(q => q.key === k);
  $('#sr-go', root)?.addEventListener('click', () => {
    const cx = col($('#sr-x', root).value), cy = col($('#sr-y', root).value), out = $('#sr-out', root), n = Math.min(cx.data.length, cy.data.length);
    const idx = Array.from({ length: n }, (_, i) => i).filter(i => Number.isFinite(cx.data[i]) && Number.isFinite(cy.data[i])).sort((a, b) => cx.data[a] - cx.data[b]), x = idx.map(i => cx.data[i]), y = idx.map(i => cy.data[i]);
    const r = symbolicRegression(x, y); if (!r.candidates.length) { out.innerHTML = `<p class="note warn">${esc(r.text)}</p>`; return; }
    const best = r.candidates.slice(0, 4), xs = Array.from({ length: 160 }, (_, i) => x[0] + (x[x.length - 1] - x[0]) * i / 159);
    out.innerHTML = `<p class="small">${esc(r.text)}</p><div class="plot"><canvas class="pl" id="sr-plot"></canvas></div>` + table(['Rank', 'Family', 'Equation (x → y)', 'Parameters', 'RMSE (fit)', 'RMSE (held out)', 'ΔBIC', 'Weight', ''], r.candidates.slice(0, 8).map((k, i) => [i + 1, k.name, raw(`<code>${esc(k.expr)}</code>`), k.k, num(fmt(k.train.rmse, 3)), num(fmt(k.test.rmse, 3)), num(fmt(k.dBic, 3)), num(fmt(k.weight, 2)), raw(`<button class="btn sm" data-adopt="${i}">Adopt</button>`)])).__raw + `<p class="small dim">A held-out error much larger than the fit error signals over-fitting. Several candidates within ΔBIC of about 2 cannot be told apart by these data: more measurements are needed, ideally where their predictions differ most.</p>`;
    lineChart($('#sr-plot', root), { x: { label: cx.name, unit: cx.unit, data: xs }, y: best.map(k => ({ label: k.name, data: xs.map(k.f) })), yLabel: cy.name, yUnit: cy.unit, points: x.map((v, i) => ({ x: v, y: y[i] })), pointsLabel: 'your data' }, { height: 320, legend: true });
    on(out, 'click', '[data-adopt]', (_, el) => { const k = r.candidates[+el.dataset.adopt]; const xn = cx.name.replace(/[^A-Za-z0-9_]/g, '_') || 'x', yn = cy.name.replace(/[^A-Za-z0-9_]/g, '_') || 'y'; let rhs = k.expr.replace(/\bx\b/g, xn); inv.custom.symbols[xn] = inv.custom.symbols[xn] || { name: cx.name, unit: cx.unit || '1', min: x[0], max: x[x.length - 1] }; inv.custom.symbols[yn] = inv.custom.symbols[yn] || { name: cy.name, unit: cy.unit || '1' }; adopt(yn, rhs, `${k.name} fitted to ${cy.name}`); });
  });
  $('#pl-go', root)?.addEventListener('click', () => {
    const cy = col($('#sr-y', root).value), [uid, ti] = cy.key.split('|'), others = cols.filter(q => q.key.startsWith(`${uid}|${ti}|`) && q.key !== cy.key), out = $('#sr-out', root);
    const r = powerLawFit(Object.fromEntries(others.map(q => [q.name.replace(/[^A-Za-z0-9_]/g, '_'), q.data])), cy.data);
    out.innerHTML = r ? `<div class="eq"><code>${esc(cy.name)} = ${esc(r.expr)}</code><p class="small">Fit RMSE ${fmt(r.train.rmse, 3)} (R² ${fmt(r.train.r2, 4)})${r.test ? `; held-out RMSE ${fmt(r.test.rmse, 3)}` : ''}. Exponents close to simple fractions: ${Object.entries(r.snapped).map(([k, v]) => `${esc(k)} → ${fmt(v, 3)}`).join(', ')}.</p></div>` : '<p class="note warn">A power law needs every value to be positive.</p>';
  });
  $('#sd-go', root)?.addEventListener('click', () => {
    const cx = col($('#sr-x', root).value), [uid, ti] = cx.key.split('|'), others = cols.filter(q => q.key.startsWith(`${uid}|${ti}|`) && q.key !== cx.key).slice(0, 3), out = $('#sr-out', root);
    if (!others.length) { toast('The table needs a time column and at least one state column.'); return; }
    const r = sindy(cx.data, Object.fromEntries(others.map(q => [q.name.replace(/[^A-Za-z0-9_]/g, '_') || 'x', q.data])), { degree: 3 });
    if (!r.ok) { out.innerHTML = `<p class="note warn">${esc(r.text)}</p>`; return; }
    out.innerHTML = `<p class="small">${esc(r.text)}</p>` + r.equations.map(q => `<div class="eq">${tex(`${E.toTex(q.lhs)} = ${E.toTex(q.rhs)}`, true).__raw}</div>`).join('') + (r.score ? table(['State', 'RMSE of re-simulation', 'R²'], r.names.map((n, i) => [n, num(fmt(r.score[i].rmse, 3)), num(fmt(r.score[i].r2, 4))])).__raw : '<p class="note warn">The identified system could not be integrated over the whole record (it diverged), so it does not reproduce the data and should be rejected.</p>') + '<button class="btn sm" id="sd-adopt" style="margin-top:.4rem">Adopt these equations</button>';
    $('#sd-adopt', root).addEventListener('click', () => { r.equations.forEach(q => inv.custom.equations.push({ lhs: q.lhs, rhs: q.rhs, name: `Identified dynamics of ${q.state}` })); inv.custom.symbols.t = inv.custom.symbols.t || { name: 'Time', unit: cx.unit || 's' }; X.refresh(); toast('Added to the equation laboratory.'); });
  });
}
function discovery(X) {
  return { html: html`<div class="note"><b>Option B — novel equation discovery.</b> Candidates are generated by dimensional reasoning, by symbolic regression on data and by identifying dynamics from time series. Each is a hypothesis: it is verified mathematically here, and earns physical credibility only through the comparisons in <b>Calibration &amp; Validation</b>.</div>${discoveryBody(X)}`, after(root) { bindDiscovery(root, X); } };
}

// =================================================================== logic
function logic(X) {
  const { inv } = X, c = X.c, L = inv.logic || { atoms: [], premises: [], conclusion: null, notes: [] }, r = c.logic, m = c.model;
  const ST = { valid: ['Valid: the conclusion follows necessarily', 'ok'], invalid: ['Invalid: the conclusion does not follow', 'bad'], contradicted: ['The premises entail the opposite of the conclusion', 'bad'], 'inconsistent-premises': ['The premises contradict one another', 'warn'], consistent: ['The premises are jointly consistent', 'ok'] };
  const cellv = v => raw(`<td class="${v ? 'T' : 'F'}">${v ? 'T' : 'F'}</td>`), cap = t => t.charAt(0).toUpperCase() + t.slice(1);
  const atomText = Object.fromEntries(L.atoms.map(a => [a.k, a.text])), tally = r ? { all: r.rows.filter(x => x.all).length, counter: r.rows.filter(x => x.all && x.conclusion === false).length } : null;
  return {
    html: html`
      <div class="card"><h3>Formal proposition set</h3><p class="small dim">Each atomic statement gets a letter; premises and conclusion are formulas over those letters. Edit anything — the analysis updates at once. Connectives: <code>~</code> not, <code>&amp;</code> and, <code>|</code> or, <code>-&gt;</code> implies, <code>&lt;-&gt;</code> if and only if.</p>
        <div class="tw"><table><thead><tr><th style="width:5rem">Symbol</th><th>Proposition</th><th></th></tr></thead><tbody>${join(L.atoms, (a, i) => html`<tr><td><input type="text" data-ak="${i}" value="${a.k}" style="min-width:3rem"></td><td><input type="text" data-at="${i}" value="${a.text}"></td><td><button class="btn sm ghost" data-adel="${i}">✕</button></td></tr>`)}</tbody></table></div>
        <button class="btn sm" id="atom-add" style="margin-top:.4rem">Add a proposition</button>
        <h4 style="margin-top:1rem">Premises</h4>
        ${join(L.premises, (p, i) => html`<div class="row" style="margin:.25rem 0"><span class="chip mute">P${i + 1}</span><input type="text" data-prem="${i}" value="${p}" style="flex:1" spellcheck="false"><button class="btn sm ghost" data-pdel="${i}">✕</button></div>`)}
        <div class="row" style="margin:.25rem 0"><button class="btn sm" id="prem-add">Add a premise</button><button class="btn sm ghost" id="reread">Re-read from the prompt</button>${m && m.logicPreset ? html`<button class="btn sm ghost" id="preset">Load the formal structure for this thought experiment</button>` : ''}</div>
        <h4 style="margin-top:.8rem">Conclusion</h4><div class="row"><span class="chip mute">∴</span><input type="text" id="concl" value="${L.conclusion || ''}" placeholder="leave empty to test consistency only" style="flex:1" spellcheck="false"></div>
        ${join(L.notes || [], n => html`<p class="small dim">${n}</p>`)}${c.logicError ? html`<p class="note bad">${c.logicError}</p>` : ''}</div>
      ${r ? html`
      <div class="card"><h3>Result</h3><div class="note ${ST[r.status][1] === 'ok' ? 'ok' : ST[r.status][1]}"><b>${ST[r.status][0]}.</b></div>${join(r.lines, l => html`<p>${l}</p>`)}
        <div class="eq">${tex(`${r.premises.map(Logic.showTex).join(',\\;') || '\\varnothing'} \\;${r.status === 'valid' ? '\\vDash' : '\\nvDash'}\\; ${r.conclusion ? Logic.showTex(r.conclusion) : '\\bot'}`, true)}</div>
        ${r.needed.length || r.redundant.length ? html`<p class="small"><b>Premises the conclusion really needs:</b> ${r.needed.map(i => `P${i + 1}`).join(', ') || 'none individually'}. <b>Not needed:</b> ${r.redundant.map(i => `P${i + 1}`).join(', ') || 'none'}.</p>` : ''}
        ${r.conflicts.length ? html`<p class="small"><b>Smallest conflicting sets:</b> ${r.conflicts.map(k => `{${k.map(i => `P${i + 1}`).join(', ')}}`).join(' ; ')}. Removing one premise from each set restores consistency.</p>` : ''}</div>
      <div class="card"><h3>The argument in plain words</h3><p class="small dim">Every letter stands for one statement that is either true or false. The premises are what the argument takes for granted; the conclusion is what it claims must follow.</p>
        ${table(['Letter', 'Stands for'], r.names.map(n => [raw(`<b class="mono">${esc(n)}</b>`), atomText[n] || raw('<span class="dim">no wording given — type it in the table above</span>')]))}
        ${table(['', 'In symbols', 'Read as'], [...r.premises.map((p, i) => [`Premise P${i + 1}`, tex(Logic.showTex(p)), cap(Logic.words(p, atomText)) + '.']), ...(r.conclusion ? [['Conclusion ∴', tex(Logic.showTex(r.conclusion)), cap(Logic.words(r.conclusion, atomText)) + '.']] : [])])}
        <p class="small dim">Symbols: ${tex('\\lnot')} not · ${tex('\\land')} and · ${tex('\\lor')} or · ${tex('\\rightarrow')} if … then · ${tex('\\leftrightarrow')} exactly when · ${tex('\\vDash')} “forces to be true”.</p></div>
      <div class="grid g2">
        <div class="card"><h3>Truth table and possible worlds</h3>
          <p class="small">A <b>possible world</b> is one way of making each letter true (T) or false (F). With ${r.names.length} letter${r.names.length === 1 ? '' : 's'} there are ${r.rows.length} worlds, one per row. The columns <b>P1…P${r.premises.length}</b> show whether each premise is true in that world${r.conclusion ? html`; the last column <b>∴</b> shows whether the conclusion is` : ''}.</p>
          <ul class="key small"><li><span class="sw model"></span><b>Green row</b> — every premise is true here${r.conclusion ? ' and so is the conclusion' : ''}. These are the worlds the premises allow.</li>${r.conclusion ? raw('<li><span class="sw counter"></span><b>Red row</b> — every premise is true but the conclusion is false: a counterexample. One red row is enough to make the argument invalid.</li>') : ''}<li><span class="sw"></span><b>Plain row</b> — at least one premise is false, so this world is ruled out and cannot count for or against the argument.</li></ul>
          <div class="note ${tally.counter ? 'bad' : 'ok'}"><b>How to read the verdict off the table.</b> The premises are all true in ${tally.all} of the ${r.rows.length} worlds. ${r.conclusion ? (tally.all === 0 ? 'No world satisfies them together, so they contradict one another and anything would “follow”.' : tally.counter ? `In ${tally.counter} of those the conclusion is false, so the conclusion does not follow.` : `The conclusion is true in every one of them, so it follows necessarily.`) : (tally.all ? 'At least one world satisfies them together, so they are consistent.' : 'No world satisfies them together, so they contradict one another.')}</div>
          <div class="tw" style="max-height:420px;overflow:auto"><table class="truth"><thead><tr>${join(r.names, n => html`<th title="${atomText[n] || n}">${n}</th>`)}${join(r.premises, (p, i) => html`<th title="Premise ${i + 1}: ${Logic.show(p)}">P${i + 1}</th>`)}${r.conclusion ? raw(`<th title="Conclusion: ${esc(Logic.show(r.conclusion))}">∴</th>`) : ''}<th style="text-align:left">Meaning of the row</th></tr></thead><tbody>
            ${join(r.rows.slice(0, 256), row => raw(`<tr class="${row.all ? (row.conclusion === false ? 'counter' : 'model') : ''}">${r.names.map(n => cellv(row.w[n]).__raw).join('')}${row.premises.map(v => cellv(v).__raw).join('')}${r.conclusion ? cellv(row.conclusion).__raw : ''}<td class="why">${row.all ? (row.conclusion === false ? 'counterexample' : r.conclusion ? 'premises hold, conclusion holds' : 'premises hold together') : `ruled out by ${row.premises.map((v, i) => (v ? '' : `P${i + 1}`)).filter(Boolean).join(', ')}`}</td></tr>`))}</tbody></table></div>
          ${r.rows.length > 256 ? raw('<p class="small dim">Only the first 256 worlds are listed; the verdict uses all of them.</p>') : ''}</div>
        <div class="card"><h3>Argument structure</h3><p class="small">Each box on the top row is a premise; the box underneath is the conclusion. A line shows how much the conclusion leans on that premise.</p>${raw(argTree(r))}
          <h4 style="margin-top:.8rem">Counterfactual analysis</h4><p class="small">Each row removes one premise and re-tests the argument with the rest. If the conclusion still follows, that premise was not needed; if it stops following, the argument depends on it.</p>
          ${table(['Remove', 'Which says', 'Remaining premises', 'Conclusion then'], r.premises.map((p, i) => { const rest = inv.logic.premises.filter((__, j) => j !== i); let s; try { s = Logic.analyse(rest, inv.logic.conclusion); } catch { s = null; } return [`P${i + 1}`, cap(Logic.words(p, atomText)) + '.', s ? (s.consistent ? 'consistent' : 'still inconsistent') : '—', s ? (ST[s.status] || ['—'])[0] : '—']; }))}</div>
      </div>` : html`<div class="card"><p class="dim">Add at least one premise to analyse an argument. For a physical experiment with no propositional content this workspace stays empty by design.</p></div>`}
      ${m && m.philosophy ? html`<div class="card"><h3>Philosophical and conceptual interpretation</h3>${para(m.philosophy)}</div>` : ''}
      <div class="card"><h3>Limits of this analysis</h3><ul class="clean small"><li>The engine is classical and propositional: every statement is true or false, and quantifiers such as "all" and "some" are not analysed.</li><li>Validity concerns form only. A valid argument with a false premise proves nothing about the world.</li><li>Translating natural language into symbols involves judgement; the formalisation above is yours to correct.</li></ul></div>`,
    after(root) {
      const ensure = () => { if (!inv.logic) inv.logic = { atoms: [], premises: [], conclusion: null, notes: [] }; return inv.logic; };
      const okF = f => { try { Logic.parseFormula(f); return true; } catch (e) { toast(`Formula not understood: ${e.message}`, 4500); return false; } };
      $('#atom-add', root).addEventListener('click', () => { const g = ensure(), used = new Set(g.atoms.map(a => a.k)); const k = 'PQRSTUVWXYZABCDEFGH'.split('').find(x => !used.has(x)) || `X${g.atoms.length}`; g.atoms.push({ k, text: '' }); X.refresh(); });
      on(root, 'change', '[data-at]', (_, el) => { ensure().atoms[+el.dataset.at].text = el.value; X.save(); });
      on(root, 'change', '[data-ak]', (_, el) => { const g = ensure(), old = g.atoms[+el.dataset.ak].k, nw = el.value.trim().replace(/[^A-Za-z0-9_]/g, ''); if (!nw || /^(true|false|and|or|not|implies|iff|xor|then)$/i.test(nw)) { toast('Choose a different symbol.'); el.value = old; return; } const re = new RegExp(`\\b${old}\\b`, 'g'); g.premises = g.premises.map(p => p.replace(re, nw)); if (g.conclusion) g.conclusion = g.conclusion.replace(re, nw); g.atoms[+el.dataset.ak].k = nw; X.refresh(); });
      on(root, 'click', '[data-adel]', (_, el) => { ensure().atoms.splice(+el.dataset.adel, 1); X.refresh(); });
      $('#prem-add', root).addEventListener('click', () => { const g = ensure(); g.premises.push(g.atoms[0] ? g.atoms[0].k : 'P'); X.refresh(); });
      on(root, 'change', '[data-prem]', (_, el) => { if (!okF(el.value)) return; ensure().premises[+el.dataset.prem] = el.value.trim(); Eng.log(inv, `Premise P${+el.dataset.prem + 1} set to ${el.value.trim()}`); X.refresh(); });
      on(root, 'click', '[data-pdel]', (_, el) => { ensure().premises.splice(+el.dataset.pdel, 1); X.refresh(); });
      $('#concl', root).addEventListener('change', e => { const v = e.target.value.trim(); if (v && !okF(v)) return; ensure().conclusion = v || null; X.refresh(); });
      $('#reread', root).addEventListener('click', () => { const f = Logic.fromText(inv.prompt); if (!f.premises.length && !f.conclusion) { toast('No "if … then", "therefore" or similar structure was found in the prompt.'); return; } inv.logic = f; X.refresh(); });
      $('#preset', root)?.addEventListener('click', () => { inv.logic = JSON.parse(JSON.stringify(X.model.logicPreset)); X.refresh(); });
    },
  };
}
function argTree(r) {
  const n = r.premises.length, w = 600, bw = Math.min(150, (w - 20) / Math.max(n, 1) - 10), h = 190;
  const col = r.status === 'valid' ? 'var(--ok)' : r.status === 'consistent' ? 'var(--accent)' : 'var(--bad)';
  let s = `<svg viewBox="0 0 ${w} ${h}" class="dgm" role="img" aria-label="Argument structure">`;
  r.premises.forEach((p, i) => { const x = 10 + (w - 20) * (i + 0.5) / n - bw / 2, need = r.needed.includes(i), bad = r.conflicts.some(c => c.includes(i)); const t = Logic.show(p); s += `<rect x="${x}" y="14" width="${bw}" height="46" rx="8" fill="none" stroke="${bad ? 'var(--bad)' : need ? 'var(--ok)' : 'var(--line)'}" stroke-width="${need || bad ? 2 : 1.2}"/><text x="${x + bw / 2}" y="32" class="d-text d-small" text-anchor="middle">P${i + 1}</text><text x="${x + bw / 2}" y="50" class="d-text" text-anchor="middle" style="font-size:12px">${esc(t.length > 18 ? t.slice(0, 17) + '…' : t)}</text><line x1="${x + bw / 2}" y1="60" x2="${w / 2}" y2="124" stroke="${need ? 'var(--ok)' : 'var(--fg-dim)'}" stroke-width="${need ? 2 : 1}" ${need ? '' : 'stroke-dasharray="4 3"'}/>`; });
  const ct = r.conclusion ? Logic.show(r.conclusion) : (r.consistent ? 'consistent' : '⊥ contradiction');
  s += `<rect x="${w / 2 - 110}" y="124" width="220" height="48" rx="10" fill="none" stroke="${col}" stroke-width="2.5"/><text x="${w / 2}" y="144" class="d-text d-small" text-anchor="middle">${r.status === 'valid' ? 'follows necessarily' : r.status === 'invalid' ? 'does not follow' : r.status === 'contradicted' ? 'refuted by the premises' : r.status === 'consistent' ? 'no conclusion stated' : 'premises conflict'}</text><text x="${w / 2}" y="162" class="d-text" text-anchor="middle">${esc(ct.length > 30 ? ct.slice(0, 29) + '…' : ct)}</text></svg>`;
  return s + '<ul class="key small"><li><span class="ln need"></span><b>Solid green line and border</b> — the conclusion cannot be reached without this premise.</li><li><span class="ln"></span><b>Dashed grey line</b> — the conclusion still follows if this premise is removed.</li><li><span class="ln bad"></span><b>Red border</b> — this premise is part of a contradiction with other premises.</li></ul>';
}

export const views = { concept, system, inputs, foundations, equations, discovery, logic };
