// Workspaces: experimental design, numerical computation, visualisation, alternative worlds,
// scientific evaluation, optimisation, engineering and safety, export, and reverse engineering.
import { html, raw, join, esc, chip, provChip, tex, toast, on, $, $$, table, num, showScalar, pct, when, copy } from './dom.js';
import { equationCard, scalarsTable, statGrid, symTexSafe, drawResults, seriesCard, fieldCard, animCard, pathCard } from './widgets.js';
import { numericColumns, litBox, bindLit } from './ws-a.js';
import * as Eng from '../engine/core.js';
import { modelById } from '../models/index.js';
import { fmt, fromSI, toSI, tryUnit, dimEq } from '../core/units.js';
import * as N from '../core/num.js';
import { lineChart, tornado, heatmap, canvasPng, view3d } from '../core/plot.js';
import * as Ex from '../core/exporters.js';
import { fitCurve, competingExplanations, reconstructGeometry } from '../core/inverse.js';
import { symbolicRegression } from '../core/discover.js';
import { catalogue } from '../data/catalogue.js';
import { outputStates } from './investigation.js';
import { LAWS } from '../data/domains.js';

const list = a => (a && a.length ? html`<ul class="clean">${join(a, x => html`<li>${x}</li>`)}</ul>` : raw('<p class="dim small">None recorded.</p>'));
const need = what => ({ html: html`<div class="card"><p>${what}</p><button class="btn primary sm" data-ws="concept">Choose a model</button></div>` });
const worldOf = X => X.inv.worlds.find(w => w.id === X.inv.activeWorld) || X.inv.worlds[0];

// =================================================================== experimental design
function experiment(X) {
  const c = X.c, m = c.model; if (!m) return need('An experimental design is generated from a model.');
  const ex = m.experiment;
  const sens = c.result.status === 'computed' ? Eng.sensitivity(c) : null;
  let doe = null;
  if (sens && sens.outputs.length) {
    const o = sens.outputs[0].sym, top = sens.rows.filter(r => Number.isFinite(r.s[o]) && c.inputs.find(i => i.sym === r.sym).kind !== 'constant').sort((a, b) => Math.abs(b.s[o]) - Math.abs(a.s[o])).slice(0, 3).map(r => c.inputs.find(i => i.sym === r.sym));
    if (top.length) { const lv = i => [0.75, 1, 1.25].map(f => N.clamp(i.si * f || i.rangeSI[0] + (i.rangeSI[1] - i.rangeSI[0]) * (f - 0.5), i.rangeSI[0], i.rangeSI[1])); const runs = []; const rec = (k, cur) => { if (k === top.length) { const v = { ...c.v }; top.forEach((i, j) => { v[i.sym] = cur[j]; }); const r = Eng.runModel(m, v, c.a), s = r.scalars.find(q => q.sym === o); runs.push([...cur, s ? s.value : NaN]); return; } lv(top[k]).forEach(x => rec(k + 1, [...cur, x])); }; rec(0, []); doe = { top, runs, out: sens.outputs[0] }; }
  }
  return {
    html: html`
      ${m.hypothetical ? html`<div class="note hypo">This experiment tests a hypothetical law. The plan below is what would be needed to detect or exclude the predicted effect; nothing here reports a measurement.</div>` : ''}
      ${ex ? html`
      <div class="card"><h3>Objective and testability</h3><p>${ex.objective}</p>
        <div class="grid g2"><div><h4>Expected signatures</h4>${list(ex.signatures)}</div><div><h4>What would refute the model</h4>${list(m.falsify)}</div></div></div>
      <div class="grid g2">
        <div class="card"><h3>Apparatus and configuration</h3>${list(ex.apparatus)}${m.diagram ? raw(m.diagram(c.v, c.a)) : ''}</div>
        <div class="card"><h3>Procedure</h3><ol class="deriv">${join(ex.procedure || [], p => html`<li>${p}</li>`)}</ol><h4>Controls and baseline cases</h4>${list(ex.controls)}</div>
      </div>
      <div class="card"><h3>Measurement system and uncertainty budget</h3>
        ${(ex.instruments || []).length ? table(['Instrument', 'Measures', 'Range', 'Resolution / accuracy'], ex.instruments.map(i => [i.name, i.measures, i.range, i.resolution])) : html`<p class="dim small">No instruments are specified.</p>`}
        <p class="small dim" style="margin-top:.5rem">Combine instrument accuracy (systematic) with repeatability (random) in quadrature for each measured quantity; calibration results can be reported only once real calibration measurements exist.</p></div>
      ${(ex.safety || []).length ? html`<div class="card"><h3>Safety and precautions</h3>${list(ex.safety)}</div>` : ''}` : html`<div class="card"><p class="dim">No experimental plan is attached to this model.</p></div>`}
      ${doe ? html`<div class="card"><h3>Test matrix</h3><p class="small dim">A three-level full factorial over the ${doe.top.length} inputs to which <b>${doe.out.name.toLowerCase()}</b> is most sensitive, with the model's prediction for each run. Use it to choose test points that discriminate best.</p>
        ${table(['Run', ...doe.top.map(i => `${i.name} (${i.unit})`), `Predicted ${doe.out.name}`], doe.runs.map((r, k) => [k + 1, ...doe.top.map((i, j) => num(fmt(fromSI(r[j], i.unit), 4))), num(showScalar({ ...doe.out, value: r[r.length - 1] }))]))}</div>` : ''}
      ${sens ? html`<div class="card"><h3>Detectability</h3><p class="small dim">Change in each predicted quantity for a 1 % change in its most influential input. An effect is detectable only if this exceeds the resolution of the instrument that measures it.</p>
        ${table(['Predicted quantity', 'Value', 'Most influential input', 'Change per 1 % change in that input'], sens.outputs.slice(0, 10).map(o => { const top = sens.rows.filter(r => Number.isFinite(r.s[o.sym])).sort((a, b) => Math.abs(b.s[o.sym]) - Math.abs(a.s[o.sym]))[0]; return [o.name, num(showScalar(o)), top ? top.name : '—', num(top ? `${fmt(top.s[o.sym], 3)} %` : '—')]; }))}</div>` : ''}`,
  };
}

// =================================================================== numerical computation
function compute(X) {
  const { inv } = X, c = X.c, m = c.model, r = c.result; if (!m) return need('Numerical computation needs a model, or your own equations entered in the equation laboratory.');
  const conv = Eng.convergence(c);
  return {
    html: html`
      <div class="card"><div class="row spread"><h3>Simulation status</h3>${r.status === 'computed' ? chip('actually computed on this device', 'ok') : chip(r.status === 'failed' ? 'failed' : 'not computed', 'bad')}</div>
        <dl class="kv"><dt>Formulation</dt><dd>${c.verification.closure.nDifferential ? `${c.verification.closure.nDifferential} differential and ${c.verification.closure.nEquations - c.verification.closure.nDifferential} algebraic relations` : `${c.verification.closure.nEquations} algebraic relations`}</dd><dt>Method</dt><dd>${m.numerics ? m.numerics.method : 'Direct evaluation of closed-form relations'}</dd>${m.numerics && m.numerics.order ? html`<dt>Formal order</dt><dd>${m.numerics.order}</dd>` : ''}${m.numerics && m.numerics.stability ? html`<dt>Stability</dt><dd>${m.numerics.stability}</dd>` : ''}<dt>Solve time</dt><dd>${fmt(r.ms, 3)} ms</dd><dt>Reproducibility</dt><dd>Deterministic: the same inputs give the same numbers; random sampling uses fixed seeds.</dd></dl>
        ${r.status !== 'computed' ? html`<div class="note bad"><b>Not computed.</b> ${r.error}</div>` : ''}${join(r.warnings, w => html`<div class="note warn">${w}</div>`)}${join(r.notes, w => html`<div class="note">${w}</div>`)}</div>
      ${r.status === 'computed' ? html`
      <div class="card"><h3>Computed results</h3>${scalarsTable(r.scalars)}</div>
      ${r.checks.length ? html`<div class="card"><h3>Conservation and consistency diagnostics</h3>${table(['Check', 'Residual', 'Tolerance', 'Outcome'], r.checks.map(k => [raw(`${esc(k.name)}${k.note ? `<br><span class="small dim">${esc(k.note)}</span>` : ''}`), num(fmt(k.value, 3)), num(fmt(k.tol, 3)), k.pass ? chip('pass', 'ok') : chip('fail', 'bad')]))}</div>` : ''}
      <div class="card"><h3>Parameter response</h3><p class="small dim">Vary one input across its range and watch any output respond. Pick an input, then a result. Most results depend on only a few of the inputs, so the list is sorted into results that change with the input you picked, results that stay the same, and results that have no value to plot.</p>
        <div class="grid g3"><div><label class="f" for="sw-in">Input to vary</label><select id="sw-in">${join(c.inputs.filter(i => i.kind !== 'numerical'), i => html`<option value="${i.sym}">${i.name}</option>`)}</select></div><div><label class="f" for="sw-out">Output to plot</label><select id="sw-out">${join(r.scalars.filter(s => Number.isFinite(s.value)), s => html`<option value="${s.sym}">${s.name}</option>`)}</select></div><div style="align-self:end"><button class="btn primary" id="sw-go">Run the sweep</button></div></div>
        <div class="plot" style="margin-top:.6rem"><canvas class="pl" id="sw-plot"></canvas></div><div id="sw-note" class="small dim"></div></div>
      ${conv ? html`<div class="card"><h3>Solution verification: refinement study</h3><p class="small dim">The model is run at three resolutions of “${conv.name}” (${conv.levels.join(', ')}). The observed order of accuracy and the grid-convergence index follow Richardson's method.</p>
        ${table(['Quantity', 'Coarse', 'Medium', 'Fine', 'Observed order', 'Extrapolated', 'Discretisation uncertainty'], conv.rows.slice(0, 10).map(q => [q.name, num(fmt(q.vals[0], 6)), num(fmt(q.vals[1], 6)), num(fmt(q.vals[2], 6)), num(q.order == null ? 'converged' : fmt(q.order, 3)), num(fmt(q.extrap, 6)), num(q.order == null ? '< 10⁻¹⁴' : Number.isFinite(q.gci) ? `${fmt(q.gci * 100, 2)} %` : 'not monotone')]))}</div>` : ''}` : ''}
      <div class="card"><div class="row spread"><h3>Generated source code</h3><div class="seg" id="lang"><button aria-pressed="true" data-lang="python">Python</button><button aria-pressed="false" data-lang="matlab">MATLAB / Octave</button><button aria-pressed="false" data-lang="cpp">C++</button></div></div>
        <p class="small dim">Python for scientific computing and automation, MATLAB for matrix and engineering analysis, C++ for high-performance simulation. Each file implements the explicit relations of this model with your inputs, lists implicit ones with their origin, and embeds the results above so the two can be compared.</p>
        <pre id="code"></pre><div class="row"><button class="btn sm" id="code-copy">Copy</button><button class="btn sm" id="code-dl">Download</button><button class="btn sm primary" id="py-run" title="Runs the Python file in this browser using a WebAssembly Python runtime">Run the Python file here</button></div>
        <pre id="py-out" hidden></pre></div>`,
    after(root) {
      const gen = { python: () => Ex.toPython(inv, c), matlab: () => Ex.toMatlab(inv, c), cpp: () => Ex.toCpp(inv, c) }, extn = { python: 'py', matlab: 'm', cpp: 'cpp' }; let lang = 'python';
      const show = () => { $('#code', root).textContent = gen[lang](); $('#py-run', root).hidden = lang !== 'python'; };
      show();
      on(root, 'click', '[data-lang]', (_, el) => { lang = el.dataset.lang; $$('[data-lang]', root).forEach(b => b.setAttribute('aria-pressed', String(b === el))); show(); });
      $('#code-copy', root).addEventListener('click', () => copy(gen[lang]()));
      $('#code-dl', root).addEventListener('click', () => Ex.download(`${Ex.slug(inv.title)}.${extn[lang]}`, gen[lang]()));
      $('#py-run', root).addEventListener('click', () => runPython(gen.python(), $('#py-out', root)));
      const swCache = {};
      const sweepNow = () => {
        if (r.status !== 'computed') return; const key = $('#sw-in', root).value, s = swCache[key] || (swCache[key] = Eng.sweep(c, key, 40)), o = s.outputs.find(q => q.sym === $('#sw-out', root).value) || s.outputs[0]; if (!o) return;
        const i = s.input, same = o.show && tryUnit(o.show) && dimEq(tryUnit(o.show).dim, tryUnit(o.unit).dim), conv2 = same ? v => fromSI(v, o.show) : v => v, unit = same ? o.show : o.unit;
        const x = s.xs.map(v => fromSI(v, i.unit)), y = o.data.map(conv2), spec = { x: { label: i.name, unit: i.unit, data: x }, y: [{ label: o.name, data: y }], yLabel: o.name, yUnit: unit, vline: fromSI(i.si, i.unit) };
        const fin = y.filter(Number.isFinite), gaps = y.length - fin.length, lower = o.name.charAt(0).toLowerCase() + o.name.slice(1); let how = '';
        // each result is drawn as what it is: a line only where neighbouring points really belong to one curve
        if (o.shape === 'level') how = `${o.name} stays the same whatever the value of ${i.name.charAt(0).toLowerCase() + i.name.slice(1)}, so the line is flat. That is correct: it does not depend on this input.`;
        else if (o.shape === 'steady') { const mid = (Math.max(...fin) + Math.min(...fin)) / 2, pad = Math.abs(mid) * 0.01; spec.yRange = [mid - pad, mid + pad]; how = `${o.name} changes by only ${fmt(o.rel * 100, 2)} % over the whole range, which is within the numerical resolution of the solve. The axis spans ±1 % so that this is not magnified into apparent structure.`; }
        else if (o.shape === 'steps') { const sx = [], sy = []; x.forEach((v, k) => { if (k) { sx.push(v); sy.push(y[k - 1]); } sx.push(v); sy.push(y[k]); }); spec.x.data = sx; spec.y[0].data = sy; how = `${o.name} is a count or a category: it takes separate values and jumps from one to the next, so it is drawn as steps.`; }
        else if (o.shape === 'residual') { spec.y = [{ label: `|${o.name}|`, data: y.map(v => (v === 0 ? NaN : Math.abs(v))), scatter: true }]; spec.logy = true; { const nz = y.map(Math.abs).filter(v => v > 0); if (nz.length) spec.yRange = [Math.pow(10, Math.floor(Math.log10(Math.min(...nz)) - 1e-9)), Math.pow(10, Math.ceil(Math.log10(Math.max(...nz)) + 1e-9))]; } how = `Every value of ${lower} is at rounding level (largest ${fmt(conv2(o.peak), 2)}${unit && unit !== '1' ? ' ' + unit : ''}): it is zero, or a numerical error measure, to within the precision of the arithmetic. The scatter therefore carries no physical meaning; what matters is that the values stay this small. Shown as separate points on a logarithmic axis; exact zeros are not drawn.`; }
        else if (o.shape === 'scattered') { spec.y = [{ label: o.name, data: y, scatter: true }, { label: 'Typical level (running median)', data: o.trend.map(conv2), dash: true }]; how = o.sampled ? `${o.name} comes from random sampling, so each point carries sampling error. The points are the individual results; the dashed line is their running median, which is the trend to read.` : `${o.name} responds irregularly to this input: neighbouring values give unrelated results, as happens with sensitive (chaotic) dynamics or when the response switches between distinct states.${o.switches ? ` Here “${o.switches.name}” changes ${o.switches.n} times across the range, and the result jumps each time it does.` : ''} Joining the points would draw a curve that is not there, so they are shown separately; the dashed line is the running median. Half of the results lie between ${fmt(conv2(o.q1), 3)} and ${fmt(conv2(o.q3), 3)}${unit && unit !== '1' ? ' ' + unit : ''}.`; }
        else if (o.shape === 'line' && o.law) { const L = o.law, X = i.name.charAt(0).toLowerCase() + i.name.slice(1), frac = q => { const a = Math.abs(q); for (const dn of [1, 2, 3, 4, 6]) if (Math.abs(a * dn - Math.round(a * dn)) < 1e-9) return dn === 1 ? String(Math.round(a)) : `${Math.round(a * dn)}/${dn}`; return fmt(a, 3); };
          const times = f => (f >= 1 ? `${fmt(f, 3)} times as large` : `${fmt(f, 3)} times its size (${fmt(1 / f, 3)} times smaller)`);
          if (L.type === 'power') how = L.p === 1 ? `${o.name} goes up in step with ${X}: double one and the other doubles. A straight line is the correct shape here.` : L.p === -1 ? `${o.name} goes down as ${X} goes up: double the input and it halves.` : `Double ${X} and ${lower} becomes ${times(Math.pow(2, L.p))}. (It varies as the input to the power ${L.p < 0 ? '−' : ''}${frac(L.p)}${L.exact ? '' : ', fitted'}.)`;
          else if (L.type === 'linear') how = `${o.name} changes by the same amount for each equal step in ${X}. A straight line is the correct shape here.`;
          else if (L.type === 'exponential') how = `Each equal step in ${X} multiplies ${lower} by the same factor.`;
          else how = { rises: `${o.name} rises as ${X} increases, along a curve.`, falls: `${o.name} falls as ${X} increases, along a curve.`, peak: `${o.name} rises, reaches its largest value near ${fmt(fromSI(L.at, i.unit), 3)} ${i.unit === '1' ? '' : i.unit}, then falls.`, dip: `${o.name} falls, reaches its smallest value near ${fmt(fromSI(L.at, i.unit), 3)} ${i.unit === '1' ? '' : i.unit}, then rises.`, mixed: `${o.name} goes up and down more than once over the range.` }[L.trend]; }
        // stretches of the range over which the quantity has no value are shaded, with the reason the model gives
        const zones = []; y.forEach((v, k) => { if (Number.isFinite(v)) return; const z = zones[zones.length - 1]; if (z && z.k1 === k - 1) { z.k1 = k; if (o.why[k]) z.why.add(o.why[k]); } else zones.push({ k0: k, k1: k, why: new Set(o.why[k] ? [o.why[k]] : []) }); });
        const mid = (p, q) => (p < 0 ? x[0] : q >= x.length ? x[x.length - 1] : (x[p] + x[q]) / 2);
        if (zones.length) spec.shade = zones.map(z => ({ x0: mid(z.k0 - 1, z.k0), x1: mid(z.k1, z.k1 + 1) }));
        const reasons = [...new Set(zones.flatMap(z => [...z.why]))];
        // points at which one of the model's own checks failed are marked: the value there is not to be relied on
        const nBad = s.bad.filter(Boolean).length;
        if (nBad) { spec.pointsRing = true; spec.pointsLabel = 'A model check failed here'; } if (nBad) spec.points = s.bad.map((f, k) => (f && Number.isFinite(y[k]) && (!spec.logy || y[k] !== 0) ? { x: x[k], y: spec.logy ? Math.abs(y[k]) : y[k] } : null)).filter(Boolean);
        lineChart($('#sw-plot', root), spec, { height: 280 });
        // what was drawn, kept on the canvas so that the end-to-end test can compare it with an independent solve
        $('#sw-plot', root).plotted = { input: i.sym, output: o.sym, shape: o.shape, xUnit: i.unit, yUnit: unit, x, y, present: fromSI(i.si, i.unit) };
        // the list of outputs is regrouped for this input: those that respond to it first, each tagged with how
        const dirOf = q => { const f = q.data.filter(Number.isFinite); return f[f.length - 1] > f[0] ? 'rises' : 'falls'; };
        const tag = q => (q.shape === 'line' ? (q.law.type === 'curved' ? { rises: 'rises', falls: 'falls', peak: 'rises then falls', dip: 'falls then rises', mixed: 'goes up and down' }[q.law.trend] : dirOf(q)) : { steps: 'changes in steps', scattered: 'scattered', steady: '', residual: '', level: '' }[q.shape] || '');
        const rank = q => (q.shape === 'line' ? (q.law.type === 'curved' ? 0 : 1) : q.shape === 'steps' ? 2 : 3);
        const moving = s.outputs.filter(q => ['line', 'steps', 'scattered'].includes(q.shape)).sort((p, q) => rank(p) - rank(q)), still = s.outputs.filter(q => !moving.includes(q));
        const none = r.scalars.filter(q => typeof q.value === 'number' && !s.outputs.some(x => x.sym === q.sym));
        const count = (n, one, many) => `${n} result${n === 1 ? ' ' + one : 's ' + many}`;
        const sel = $('#sw-out', root), opt = q => `<option value="${esc(q.sym)}"${q.sym === o.sym ? ' selected' : ''}>${esc(q.name)}${tag(q) ? ` — ${tag(q)}` : ''}</option>`;
        sel.innerHTML = `${moving.length ? `<optgroup label="${count(moving.length, 'changes', 'change')} when this input changes">${moving.map(opt).join('')}</optgroup>` : ''}${still.length ? `<optgroup label="${count(still.length, 'stays', 'stay')} the same">${still.map(opt).join('')}</optgroup>` : ''}${none.length ? `<optgroup label="${count(none.length, 'has', 'have')} no value to plot" disabled>${none.map(q => `<option value="${esc(q.sym)}" disabled>${esc(q.name)}${q.text ? ` — ${esc(q.text)}` : ''}</option>`).join('')}</optgroup>` : ''}`;
        const hint = !moving.includes(o) && moving.length ? ` ${count(moving.length, 'does change', 'do change')} with this input; pick one from the top of the “Output to plot” list.` : !moving.length ? ' No result changes with this input.' : '';
        const trust = nBad ? ` At ${nBad} of the ${s.xs.length} points a check built into the model failed (${s.failedChecks.slice(0, 3).map(n => `“${n}”`).join(', ')}): those points are ringed, and the values there should not be relied on.` : s.nChecks ? ` The model's built-in check${s.nChecks === 1 ? '' : 's'} passed at every point.` : '';
        const res = s.resolution && !['level', 'residual'].includes(o.shape) ? ` Values depend slightly on “${s.resolution}”; the refinement study below measures by how much.` : '';
        $('#sw-note', root).textContent = `${how ? how + ' ' : ''}The dashed line marks the present value of ${i.name.charAt(0).toLowerCase() + i.name.slice(1)}.`.trim() + `${zones.length ? ` In the shaded part of the range (${zones.map(z => `${fmt(spec.shade[zones.indexOf(z)].x0, 3)} to ${fmt(spec.shade[zones.indexOf(z)].x1, 3)}`).slice(0, 3).join('; ')}${i.unit === '1' ? '' : ' ' + i.unit}) ${lower} has no value${reasons.length ? `: ${reasons.slice(0, 2).map(t => t.charAt(0).toLowerCase() + t.slice(1)).join('; ')}` : ' (the solve gives none there)'}.` : ''}${hint}${trust}${res} (${s.xs.length} solves${i.integer ? ', whole numbers only' : s.xs.length > 41 ? ', more of them where the curve bends' : ''}.)`;
      };
      $('#sw-go', root)?.addEventListener('click', sweepNow); $('#sw-out', root)?.addEventListener('change', sweepNow); $('#sw-in', root)?.addEventListener('change', () => { sweepNow(); const top = $('#sw-out optgroup option', root), cur = $('#sw-out', root).selectedOptions[0]; if (top && cur && / the same$/.test(cur.parentElement.label) && / change/.test(top.parentElement.label)) { $('#sw-out', root).value = top.value; sweepNow(); toast('Switched to an output that responds to this input'); } }); if ($('#sw-go', root)) { const first = c.inputs.find(i => i.kind !== 'numerical' && i.kind !== 'constant'); if (first) $('#sw-in', root).value = first.sym; sweepNow(); const top = $('#sw-out optgroup option', root); if (top && $('#sw-out', root).value !== top.value && / change/.test(top.parentElement.label)) { $('#sw-out', root).value = top.value; sweepNow(); } }
    },
  };
}
let pyodide = null;
async function runPython(code, out) {
  out.hidden = false; out.textContent = 'Preparing the Python runtime (about 10 MB the first time; it is then kept on this device)…';
  try {
    if (!pyodide) {
      if (!window.loadPyodide) await new Promise((res, rej) => { const s = document.createElement('script'); s.src = 'https://cdn.jsdelivr.net/pyodide/v0.26.4/full/pyodide.js'; s.onload = res; s.onerror = () => rej(new Error('the runtime could not be downloaded; a connection is needed the first time')); document.head.appendChild(s); });
      pyodide = await window.loadPyodide({ indexURL: 'https://cdn.jsdelivr.net/pyodide/v0.26.4/full/' });
    }
    out.textContent = 'Loading numerical libraries…';
    await pyodide.loadPackage(/scipy/.test(code) ? ['numpy', 'scipy'] : ['numpy']);
    let buf = ''; pyodide.setStdout({ batched: s => { buf += s + '\n'; } }); pyodide.setStderr({ batched: s => { buf += s + '\n'; } });
    await pyodide.runPythonAsync(code.replace('if __name__ == "__main__":', 'if True:'));
    out.textContent = buf || '(the script produced no output)';
  } catch (e) { out.textContent = `Python could not be run here: ${e.message}\n\nThe file can still be downloaded and run with any Python 3 installation.`; }
}

// =================================================================== visualisation
function visuals(X) {
  const { inv } = X, c = X.c, m = c.model, r = c.result;
  if (!m) return need('Visualisations are drawn from computed results.');
  const geos = inv.uploads.filter(u => u.geometry && u.geometry.points && u.geometry.points.length);
  return {
    html: html`
      ${inv.module === 2 && r.status === 'computed' ? html`<div class="card"><h3>Results</h3>${statGrid(r.scalars, 8)}${join(r.warnings, w => html`<div class="note warn">${w}</div>`)}<details style="margin-top:.6rem"><summary>Full table of computed quantities</summary><div class="body">${scalarsTable(r.scalars)}</div></details></div>` : ''}
      ${r.status !== 'computed' ? html`<div class="note bad"><b>Nothing to plot.</b> ${r.error}</div>` : ''}
      ${m.hypothetical ? html`<div class="note hypo">Figures below show the consequences of a hypothetical law. They are solutions of the stated equations, not observations.</div>` : ''}
      ${m.diagram ? html`<div class="card"><div class="row spread"><h3>Schematic</h3><button class="btn sm ghost" id="svg-dl">SVG</button></div><div id="dgm">${raw(m.diagram(c.v, c.a))}</div><p class="small dim">Generated from the current inputs. A schematic, not a manufacturing drawing.</p></div>` : ''}
      <div class="grid g2">${join(r.anims, animCard)}${join(r.fields, fieldCard)}${join(r.paths, pathCard)}${join(r.series, seriesCard)}</div>
      ${geos.length ? html`<div class="card"><h3>Uploaded geometry</h3><div class="grid g2">${join(geos, u => html`<div><b class="small">${u.name}</b><div class="plot"><canvas class="pl" data-geo="${u.id}"></canvas></div></div>`)}</div></div>` : ''}
      ${r.series.length ? html`<div class="card"><h3>Data tables</h3>${join(r.series.slice(0, 6), s => html`<details><summary>${s.title} <span class="small dim">${s.x.data.length} points</span></summary><div class="body">${table([`${s.x.label} (${s.x.unit})`, ...s.y.map(y => `${y.label} (${s.yUnit})`)], Array.from({ length: Math.min(12, s.x.data.length) }, (_, k) => { const i = Math.round(k * (s.x.data.length - 1) / Math.max(1, Math.min(12, s.x.data.length) - 1)); return [num(fmt(s.x.data[i], 5)), ...s.y.map(y => num(fmt(y.data[i], 5)))]; }))}<p class="small dim">Evenly spaced sample of the series; the CSV button on each chart saves every point.</p></div></details>`)}</div>` : ''}`,
    after(root) {
      X.onDispose(drawResults(root, r));
      geos.forEach(u => { const g = $(`canvas[data-geo="${u.id}"]`, root); if (g) view3d(g, { points: u.geometry.points, tris: u.geometry.tris }, { height: 300 }); });
      $('#svg-dl', root)?.addEventListener('click', () => { const svg = $('#dgm svg', root); if (!svg) return; const cs = getComputedStyle(document.documentElement); const style = `<style>.d-line{stroke:#222;stroke-width:1.6;fill:none}.d-body{fill:#d7eef8;stroke:#0b7ea8;stroke-width:1.5}.d-pipe{stroke:#0b7ea8;stroke-width:9;fill:none;stroke-linecap:round}.d-pipe-fill{fill:#eee;stroke:#666;stroke-width:2}.d-liquid{fill:#7cc7e6}.d-liquid-line{stroke:#0b7ea8;stroke-dasharray:6 4;fill:none}.d-ground{stroke:#666;stroke-width:2;fill:#f6efdc}.d-hazard{fill:#f8c9dc;stroke:#c2136b;stroke-dasharray:4 3}.d-arrow{stroke:#222;stroke-width:1.8;fill:none}.d-heat{stroke:#c2136b}.d-fill{fill:#222}.d-dim{stroke:#666;fill:none}.d-text{fill:#111;font:13px sans-serif}.d-small{font-size:11px;fill:#555}</style>`; Ex.download(`${Ex.slug(inv.title)}-schematic.svg`, svg.outerHTML.replace(/<defs>/, style + '<defs>'), 'image/svg+xml'); void cs; });
    },
  };
}

// =================================================================== alternative worlds
function respond(X, target, text) {
  const c = X.c, m = c.model, [kind, id] = target.split(':'), out = [];
  if (kind === 'asm') {
    const am = Eng.assumptionMap(c), row = am && am.rows.find(r => r.id === id), a = (m.assumptions || []).find(q => q.id === id);
    out.push(`The assumption is: “${a.text}” It is made because: ${a.why || 'no rationale is recorded'}.`);
    if (row) { out.push(row.status !== 'computed' ? `With it removed the model could not be solved (${row.error}).` : row.maxRel < 1e-6 ? 'Removing it changes none of the computed results, so no conclusion here depends on it.' : `Removing it changes the results by up to ${fmt(row.maxRel * 100, 3)} %. Most affected: ${row.dependents.slice(0, 4).join('; ')}.`); if (row.changedEq.length) out.push(`Equations that are regenerated: ${row.changedEq.join('; ')}.`); }
    if (a.alt) out.push(`What replaces it: ${a.alt}`);
  } else if (kind === 'in') {
    const i = c.inputs.find(q => q.sym === id), s = Eng.sensitivity(c), row = s && s.rows.find(r => r.sym === id);
    out.push(`${i.name} is ${fmt(i.value, 5)} ${i.unit}. Origin: ${Eng.PROV[i.prov].label.toLowerCase()}. ${i.note || ''}`);
    if (i.prov === 'SUPPLIED' || i.prov === 'ESTIMATED') out.push('It was not measured for your system. Replace it with your own value in the Inputs workspace if you have one.');
    if (row && s.outputs.length) { const top = s.outputs.map(o => ({ o, v: row.s[o.sym] })).filter(q => Number.isFinite(q.v)).sort((a, b) => Math.abs(b.v) - Math.abs(a.v)).slice(0, 3); out.push(top.length && Math.abs(top[0].v) > 1e-9 ? `A 1 % change in it changes ${top.map(q => `${q.o.name.toLowerCase()} by ${fmt(q.v, 3)} %`).join('; ')}.` : 'The results are insensitive to it at this operating point.'); }
  } else if (kind === 'eq') {
    const q = c.equations.find(e => e.id === id), r = c.verification.records.find(e => e.id === id);
    out.push(`“${q.name}” is a ${q.kind} relation. Origin: ${q.origin || 'stated by the model'}.`);
    out.push(`Verification: ${r.steps.map(s => `${s.check.toLowerCase()} — ${s.ok === true ? 'established' : s.ok === false ? 'failed' : 'conditional'}`).join('; ')}.`);
    if (q.needs && q.needs.length) out.push(`It holds only under: ${q.needs.map(n => ((m.assumptions || []).find(a => a.id === n) || {}).text || n).join(' ')}`);
    if (q.kind === 'empirical' || q.kind === 'closure' || q.kind === 'hypothesis') out.push(q.kind === 'hypothesis' ? 'It is a hypothesis: it has no standing beyond the evidence gathered for it.' : 'It is not a law of nature but a fitted or modelled relation with a limited range of validity. See the limits and the alternatives listed for this model.');
  } else if (kind === 'res') {
    const s = c.result.scalars.find(q => q.sym === id), uq = Eng.uncertainty(c, 120), u = uq && uq.stats.find(q => q.sym === id), am = Eng.assumptionMap(c);
    out.push(`${s.name} = ${showScalar(s)}.`);
    if (u) out.push(`Propagating the stated input uncertainties gives a 90 % interval of ${showScalar({ ...s, value: u.p05 })} to ${showScalar({ ...s, value: u.p95 })}.`);
    if (am) { const dep = am.rows.filter(r => Math.abs(r.delta[id]) > 1e-6).sort((a, b) => Math.abs(b.delta[id]) - Math.abs(a.delta[id])); out.push(dep.length ? `It depends on ${dep.length} assumption(s); the strongest is “${dep[0].text}” (${pct(dep[0].delta[id])} if removed).` : 'It does not change when any single assumption is removed.'); }
    out.push(`Evidence level: ${c.readiness.label.toLowerCase()}.`);
  }
  if (m && m.alternatives && /alternativ|other|instead|rival|different/i.test(text)) out.push(`Competing explanations on record: ${m.alternatives.map(a => a.name).join('; ')}.`);
  if (m && m.limits && /valid|range|limit|applic|extrapol/i.test(text)) out.push(`Validity envelope: ${m.limits}`);
  return out.join(' ');
}
function worlds(X) {
  const { inv } = X, c = X.c, m = c.model; if (!m) return need('Alternative worlds are built by changing the assumptions and inputs of a model.');
  const w = worldOf(X), base = inv.worlds[0], am = Eng.assumptionMap(c), cmp = inv.worlds.length > 1 ? Eng.compareWorlds(inv) : null;
  const KIND = { baseline: ['baseline', 'ok'], alternative: ['physically supported alternative', 'live'], counterfactual: ['counterfactual', 'hypo'] };
  const heatCell = v => { if (!Number.isFinite(v)) return raw('<td class="dim">—</td>'); const a = Math.min(1, Math.abs(v) / 0.5); return raw(`<td style="background:color-mix(in srgb, ${v >= 0 ? 'var(--accent)' : 'var(--hot)'} ${Math.round(a * 60)}%, transparent)">${Math.abs(v) < 1e-6 ? '·' : esc(pct(v, 2))}</td>`); };
  return {
    html: html`
      <div class="card"><div class="row spread"><h3>Worlds</h3><span class="row"><button class="btn sm" data-new="alternative" title="Same laws, different assumptions or inputs">+ Alternative world</button><button class="btn sm" data-new="counterfactual" title="Different laws or constants">+ Counterfactual world</button></span></div>
        <div class="worldtabs">${join(inv.worlds, q => html`<button aria-pressed="${q.id === w.id}" data-world="${q.id}">${q.name} ${chip(...KIND[q.kind])}</button>`)}</div>
        <div class="row" style="margin-top:.6rem"><input type="text" id="w-name" value="${w.name}" style="max-width:260px" aria-label="World name" ${w === base ? raw('disabled') : ''}>${w !== base ? html`<button class="btn sm danger" id="w-del">Delete this world</button>` : html`<span class="small dim">The baseline cannot be deleted; branch from it to explore.</span>`}</div>
        <p class="small dim">Worlds are kept apart by kind so that an explicitly counterfactual scenario is never read as an equally valid description of reality.</p></div>
      <div class="card"><h3>Editable assumption catalogue — ${w.name}</h3><p class="small dim">Switch an assumption off and the affected equations are regenerated and the model re-solved at once.</p>
        ${(m.assumptions || []).length ? html`<div class="tw"><table><thead><tr><th>In force</th><th>Assumption</th><th>Rationale</th><th>If removed</th><th>Largest effect</th></tr></thead><tbody>${join(m.assumptions, a => { const row = am && am.rows.find(r => r.id === a.id); return html`<tr><td><label class="switch"><input type="checkbox" data-asm="${a.id}" ${c.a[a.id] ? raw('checked') : ''} aria-label="${a.text}"><span></span></label></td><td>${a.text}${c.a[a.id] !== (base.assumptions[a.id] ?? a.on) && w !== base ? chip('differs from baseline', 'warn') : ''}</td><td class="small dim">${a.why || ''}</td><td class="small dim">${a.alt || ''}</td><td class="num">${row ? (row.status !== 'computed' ? chip('unsolvable', 'bad') : fmt(row.maxRel * 100, 3) + ' %') : '—'}</td></tr>`; })}</tbody></table></div>` : html`<p class="dim">This model declares no switchable assumptions.</p>`}
        ${c.inputs.some(i => i.kind === 'constant' || i.kind === 'hypothetical') ? html`<h4 style="margin-top:.9rem">Laws and constants of this world</h4><div class="tw"><table><thead><tr><th>Quantity</th><th>Value in this world</th><th>Unit</th><th>Status</th><th></th></tr></thead><tbody>${join(c.inputs.filter(i => i.kind === 'constant' || i.kind === 'hypothetical'), i => html`<tr><td>${i.name}</td><td><input type="number" step="any" data-const="${i.sym}" value="${+parseFloat(i.value.toPrecision(10))}"></td><td>${i.unit}</td><td>${provChip(i.prov)}</td><td>${i.inWorld ? html`<button class="btn sm ghost" data-creset="${i.sym}">Restore</button>` : ''}</td></tr>`)}</tbody></table></div>` : ''}</div>
      ${am ? html`<div class="card"><h3>Which conclusions depend on which assumptions</h3><p class="small dim">Each cell is the change in a result when that one assumption is removed, everything else held fixed. Computed, not asserted.</p>
        <div class="tw"><table class="heat"><thead><tr><th style="text-align:left">Assumption removed</th>${join(am.outputs.slice(0, 9), o => html`<th title="${o.name}">${o.sym}</th>`)}</tr></thead><tbody>${join(am.rows, r => raw(`<tr><td style="text-align:left">${esc(r.text.length > 70 ? r.text.slice(0, 68) + '…' : r.text)}</td>${am.outputs.slice(0, 9).map(o => heatCell(r.delta[o.sym]).__raw).join('')}</tr>`))}</tbody></table></div>
        <div class="grid g2" style="margin-top:.7rem"><div class="note ok"><b>Robust conclusions</b> (change under 1 % whichever assumption is removed): ${am.robust.join('; ') || 'none'}.</div><div class="note warn"><b>Assumption-dependent conclusions</b> (change over 10 % for at least one): ${am.fragile.join('; ') || 'none'}.</div></div>
        <p class="small"><b>Critical-assumption ranking:</b> ${am.rows.map((r, i) => `${i + 1}. ${r.text.split(/[.;:]/)[0]} (${fmt(r.maxRel * 100, 2)} %)`).join(' · ')}</p></div>` : ''}
      ${cmp ? html`<div class="card"><h3>Side-by-side comparison</h3>
        ${cmp.inDiff.length || cmp.asDiff.length ? html`<h4>What differs</h4>${table(['', ...cmp.worlds.map(q => q.name)], [...cmp.asDiff.map(a => [a.text, ...a.vals.map(v => (v ? 'in force' : raw('<b>removed</b>')))]), ...cmp.inDiff.map(i => [`${i.name} (${i.unit})`, ...i.vals.map(v => (v ? fmt(v.value, 5) : '—'))])])}` : html`<p class="small dim">The worlds are currently identical. Change an assumption, an input or a constant in one of them.</p>`}
        ${cmp.eqDiff.some(e => e.length) ? html`<h4 style="margin-top:.7rem">Equations that differ from the baseline</h4>${join(cmp.worlds.slice(1), (q, i) => (cmp.eqDiff[i + 1].length ? html`<p class="small"><b>${q.name}:</b></p>${join(cmp.eqDiff[i + 1], e => html`<div class="eq">${tex(`${safeTex(e.lhs)} = ${safeTex(e.rhs)}`, true)}<span class="small dim">${e.name}</span></div>`)}` : ''))}` : ''}
        <h4 style="margin-top:.7rem">Results</h4>${table(['Quantity', ...cmp.worlds.flatMap((q, i) => (i ? [q.name, 'vs baseline'] : [q.name]))], cmp.rows.map(r => [r.name, ...r.cells.flatMap((x, i) => (i ? [num(x ? showScalar(x) : '—'), num(r.rel[i] == null ? '—' : pct(r.rel[i]))] : [num(x ? showScalar(x) : '—')]))]))}
        ${cmp.comps[0].result.series.length ? html`<div class="plot" style="margin-top:.7rem"><canvas class="pl" id="cmp-plot"></canvas></div><div class="row"><label class="f" for="cmp-series" style="margin:0">Overlay</label><select id="cmp-series" style="max-width:340px">${join(cmp.comps[0].result.series, s => html`<option value="${s.id}">${s.title}</option>`)}</select></div>` : ''}
        <div class="grid g2" style="margin-top:.7rem"><div class="note ok"><b>Shared by all worlds:</b> ${cmp.shared.slice(0, 8).join('; ') || 'nothing'}.</div><div class="note warn"><b>Depends on the world chosen:</b> ${cmp.divergent.slice(0, 8).join('; ') || 'nothing'}.</div></div></div>` : ''}
      <div class="card"><h3>Challenge the explanation</h3><p class="small dim">Pick anything in the investigation and question it. The reply is assembled from the model's own records and fresh computations — where a value came from, what it rests on, and how much the answer moves without it.</p>
        <div class="grid g2"><div><label class="f" for="ch-t">What are you challenging?</label><select id="ch-t"><optgroup label="Assumptions">${join(m.assumptions || [], a => html`<option value="asm:${a.id}">${a.text.slice(0, 80)}</option>`)}</optgroup><optgroup label="Equations">${join(c.equations, q => html`<option value="eq:${q.id}">${q.name}</option>`)}</optgroup><optgroup label="Inputs">${join(c.inputs, i => html`<option value="in:${i.sym}">${i.name}</option>`)}</optgroup><optgroup label="Results">${join(c.result.scalars.filter(s => Number.isFinite(s.value)), s => html`<option value="res:${s.sym}">${s.name}</option>`)}</optgroup></select></div>
          <div><label class="f" for="ch-q">Your challenge</label><input type="text" id="ch-q" placeholder="Why should I believe this? Is there an alternative? Over what range is it valid?"></div></div>
        <button class="btn primary" id="ch-go" style="margin-top:.5rem">Challenge</button>
        <div id="ch-log" style="margin-top:.7rem">${join(inv.challenges.slice().reverse().slice(0, 8), q => html`<div class="note"><b>You:</b> ${q.text} <span class="dim small">— on ${q.label}</span><br><b>Response:</b> ${q.response}</div>`)}</div></div>
      <div class="card"><div class="row spread"><h3>Versions</h3><span class="row"><input type="text" id="v-note" placeholder="Note for this version" style="max-width:220px"><button class="btn sm" id="v-save">Save a version</button></span></div>
        ${inv.versions.length ? table(['Saved', 'Note', ''], inv.versions.slice().reverse().map(v => [when(v.ts), v.note, raw(`<button class="btn sm" data-restore="${v.id}">Restore</button>`)])) : html`<p class="small dim">Save a version before a major change so you can return to it.</p>`}</div>`,
    after(root) {
      on(root, 'click', '[data-world]', (_, el) => { inv.activeWorld = el.dataset.world; X.refresh(); });
      on(root, 'click', '[data-new]', (_, el) => { const k = el.dataset.new; Eng.addWorld(inv, k === 'counterfactual' ? `Counterfactual ${inv.worlds.filter(q => q.kind === k).length + 1}` : `Alternative ${inv.worlds.filter(q => q.kind === k).length + 1}`, k); X.refresh(); toast(k === 'counterfactual' ? 'Counterfactual world created. Change its laws and constants below; they will be marked hypothetical.' : 'Alternative world created. Change its assumptions or inputs and compare.'); });
      $('#w-name', root).addEventListener('change', e => { if (w !== base && e.target.value.trim()) { w.name = e.target.value.trim().slice(0, 60); X.refresh(); } });
      $('#w-del', root)?.addEventListener('click', () => { if (!confirm(`Delete the world “${w.name}”?`)) return; inv.worlds = inv.worlds.filter(q => q !== w); inv.activeWorld = base.id; Eng.log(inv, `World “${w.name}” deleted`); X.refresh(); });
      on(root, 'change', '[data-asm]', (_, el) => { Eng.setAssumption(inv, w.id, el.dataset.asm, el.checked); X.refresh(); });
      on(root, 'change', '[data-const]', (_, el) => { const i = c.inputs.find(q => q.sym === el.dataset.const); try { Eng.setInput(inv, w.id, i.sym, parseFloat(el.value), i.unit, i.kind === 'constant' ? undefined : 'HYPOTHETICAL'); if (w === base && i.kind === 'constant') toast('You changed a constant of nature in the baseline. It is now marked hypothetical; consider doing this in a counterfactual world instead.', 6000); X.refresh(); } catch (e) { toast(e.message); } });
      on(root, 'click', '[data-creset]', (_, el) => { Eng.setInput(inv, w.id, el.dataset.creset, null); X.refresh(); });
      const overlay = () => { const sel = $('#cmp-series', root); if (!sel || !cmp) return; const ss = cmp.comps.map(q => q.result.series.find(s => s.id === sel.value)).filter(Boolean); if (!ss.length) return; const s0 = ss[0]; lineChart($('#cmp-plot', root), { ...s0, y: [], overlay: cmp.comps.flatMap((q, i) => { const s = q.result.series.find(z => z.id === sel.value); return s ? [{ label: `${cmp.worlds[i].name}: ${s.y[0].label}`, x: s.x.data, y: s.y[0].data, dash: i > 0 }] : []; }) }, { height: 320, legend: true }); };
      $('#cmp-series', root)?.addEventListener('change', overlay); overlay();
      $('#ch-go', root).addEventListener('click', () => { const sel = $('#ch-t', root), t = sel.value, text = $('#ch-q', root).value.trim() || 'Why should I accept this?'; const response = respond(X, t, text); inv.challenges.push({ ts: Date.now(), target: t, label: sel.options[sel.selectedIndex].text, text, response }); Eng.log(inv, `Challenge raised on ${sel.options[sel.selectedIndex].text}`); X.refresh(); });
      $('#v-save', root).addEventListener('click', () => { Eng.snapshot(inv, $('#v-note', root).value.trim()); X.refresh(); toast('Version saved'); });
      on(root, 'click', '[data-restore]', (_, el) => { Eng.restore(inv, el.dataset.restore); Eng.clearCache(); X.refresh(); toast('Version restored'); });
    },
  };
}
import * as Expr from '../core/expr.js';
const safeTex = s => { try { return Expr.toTex(s); } catch { return `\\text{${String(s).replace(/[\\{}_^]/g, ' ')}}`; } };

// =================================================================== scientific evaluation
function evaluation(X) {
  const { inv } = X, c = X.c, m = c.model, r = c.result, cols = numericColumns(inv);
  const sens = r.status === 'computed' ? Eng.sensitivity(c) : null;
  const lvl = c.readiness.level;
  const vc = (c.validation || []).flatMap(s => s.cases), bOk = c.benchmarks.filter(b => b.pass).length;
  const top = sens && sens.outputs.length ? sens.rows.map(q => ({ name: q.name, v: q.s[sens.outputs[0].sym] })).filter(q => Number.isFinite(q.v)).sort((a, b) => Math.abs(b.v) - Math.abs(a.v)).slice(0, 3) : [];
  return {
    html: html`
      <div class="card"><h3>Scientific readiness</h3><div class="ladder">${join(Eng.READINESS, (q, i) => html`<div class="${i === lvl ? 'on' : i < lvl ? 'done' : ''}"><b>${i + 1}</b> ${q}</div>`)}</div>
        <ul class="clean small" style="margin-top:.6rem">${join(c.readiness.why, q => html`<li>${q}</li>`)}</ul></div>
      <div class="card"><h3>Scientific gates</h3>${join(c.gates, g => html`<div class="gate"><span class="g ${g.status}" title="${g.status}">${g.id}</span><div><b>${g.name}</b> ${chip({ pass: 'passed', fail: 'failed', conditional: 'conditional', open: 'open' }[g.status], { pass: 'ok', fail: 'bad', conditional: 'warn', open: 'mute' }[g.status])}<div class="small dim">${g.text}</div></div></div>`)}</div>
      ${m ? html`
      <div class="grid g2">
        <div class="card"><h3>Numerical verification against exact solutions</h3>${c.benchmarks.length ? html`${table(['Benchmark', 'Computed', 'Exact', 'Difference', ''], c.benchmarks.map(b => [raw(`${esc(b.name)}<br><span class="small dim">${esc(b.ref)}</span>`), num(fmt(b.got, 6)), num(fmt(b.expected, 6)), num(fmt(b.rel * 100, 2) + ' %'), b.pass ? chip('pass', 'ok') : chip('fail', 'bad')]))}<p class="small dim">${bOk} of ${c.benchmarks.length} within tolerance. This shows the solver solves its equations correctly; it says nothing yet about whether the equations describe the real system.</p>` : html`<p class="dim small">No analytical benchmark is attached to this model.</p>`}</div>
        <div class="card"><h3>Comparison with published measurements</h3>${c.validation.length ? join(c.validation, v => html`<p class="small"><b>${v.name}.</b> ${v.ref}${v.note ? html` <span class="dim">${v.note}</span>` : ''}</p>${table(['Case', 'Observed', 'Predicted', 'Difference', ''], v.cases.map(k => [k.label, num(`${showScalar({ value: k.observed, unit: k.unit, show: k.show })}${k.sigma ? ` ± ${fmt(k.show && tryUnit(k.show) && tryUnit(k.show).o === 0 ? fromSI(k.sigma, k.show) : k.sigma, 2)}` : ''}`), num(showScalar({ value: k.predicted, unit: k.unit, show: k.show })), num(k.z != null ? `${fmt(k.z, 2)} σ` : pct(k.rel)), k.pass ? chip('agrees', 'ok') : chip('disagrees', 'bad')]))}`) : html`<p class="dim small">No published measurement is attached. The model is unvalidated until compared with data: use the panel below with your own.</p>`}
          <p class="small dim">These data were not used to tune anything. Agreement supports the model only inside the range the measurements cover.</p></div>
      </div>
      <div class="card"><h3>Validate against your own data</h3><p class="small dim">Compare a computed curve with measurements you have uploaded. Nothing is fitted: the model is run as it stands and the differences are reported.</p>
        ${cols.length >= 2 && r.series.length ? html`<div class="grid g4"><div><label class="f" for="va-s">Model curve</label><select id="va-s">${join(r.series.flatMap(s => s.y.map((y, k) => ({ v: `${s.id}|${k}`, t: `${s.title} — ${y.label}` }))), o => html`<option value="${o.v}">${o.t}</option>`)}</select></div><div><label class="f" for="va-x">Your x column</label><select id="va-x">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 0 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div><label class="f" for="va-y">Your y column</label><select id="va-y">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 1 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div style="align-self:end"><button class="btn primary" id="va-go">Compare</button></div></div><div id="va-out" style="margin-top:.6rem"></div>` : html`<p class="note warn small">Upload a table of measurements in <b>Inputs</b> (same units as the plotted axes) to activate this comparison.</p>`}</div>
      ${sens ? html`<div class="grid g2">
        <div class="card"><div class="row spread"><h3>Sensitivity</h3><select id="se-out" style="max-width:260px" aria-label="Output">${join(sens.outputs, o => html`<option value="${o.sym}">${o.name}</option>`)}</select></div><p class="small dim">Percentage change in the output for a 1 % change in each input.</p><div class="plot"><canvas class="pl" id="se-plot"></canvas></div></div>
        <div class="card"><div class="row spread"><h3>Uncertainty</h3><button class="btn sm primary" id="uq-go">Propagate input uncertainty</button></div><p class="small dim">Inputs are sampled within their stated uncertainty (larger for software-supplied values than for yours) and the model re-solved for each sample.</p><div id="uq-out"></div></div>
      </div>` : ''}
      <div class="card"><h3>Interpretation</h3>
        ${r.status === 'computed' ? html`<p>${m.hypothetical ? 'Within the hypothetical framework stated, ' : ''}the model gives ${r.scalars.slice(0, 3).map(s => `${s.name.toLowerCase()} of ${showScalar(s)}`).join(', ')}.${top.length ? ` The result is governed mainly by ${top.map(q => q.name.toLowerCase()).join(', ')}.` : ''}</p>` : html`<p class="note warn">No numerical conclusion: ${r.error}</p>`}
        ${join(r.warnings, q => html`<p class="note warn small">${q}</p>`)}
        <dl class="kv"><dt>What is established</dt><dd>${lvl >= 1 ? 'The formulation is dimensionally consistent and mathematically closed.' : 'Not yet the mathematical consistency of the formulation.'} ${lvl >= 2 ? 'The numerical solution reproduces exact results.' : ''} ${lvl >= 3 ? 'Predictions agree with published measurements within their uncertainty.' : ''}</dd>
          <dt>What remains conjectural</dt><dd>${m.hypothetical ? 'The governing law itself. ' : ''}${c.inputs.filter(i => ['SUPPLIED', 'ESTIMATED'].includes(i.prov)).length} input(s) are reference values rather than measurements of your system. ${vc.length ? '' : 'There is no independent experimental comparison. '}${c.equations.filter(q => q.kind === 'empirical' || q.kind === 'closure').length} relation(s) are closures or correlations with limited range.</dd>
          <dt>Validity envelope</dt><dd>${m.limits || 'Not stated.'}</dd>
          <dt>Conclusion criteria</dt><dd>Accept a deduction when it is proved; support a hypothesis when independent data agree within uncertainty; reject a model when a falsifying observation below is made; otherwise report the question as open.</dd></dl>
        ${m.falsify ? html`<h4 style="margin-top:.7rem">Falsification tests</h4>${list(m.falsify)}` : ''}</div>
      <div class="grid g2">
        <div class="card"><h3>Further evidence required</h3><ul class="clean small">${!c.benchmarks.length ? raw('<li>An analytical or manufactured benchmark for the solver.</li>') : ''}${!vc.length ? raw('<li>Independent measurements covering the operating range.</li>') : ''}${join(c.inputs.filter(i => ['SUPPLIED', 'ESTIMATED'].includes(i.prov)).slice(0, 5), i => html`<li>A measured value of ${i.name.toLowerCase()} for your system.</li>`)}${m.experiment ? html`<li>The experiment described in the Experimental Design workspace.</li>` : ''}</ul></div>
        <div class="card"><h3>Extensions</h3>${list(m.extensions)}</div>
      </div>` : html`<div class="card"><p class="dim">Evaluation of numerical results needs a model. Logical results are evaluated in the Logic workspace.</p></div>`}`,
    after(root) {
      if (sens) { const draw = () => { const o = $('#se-out', root).value; tornado($('#se-plot', root), sens.rows.map(q => ({ label: q.name, value: q.s[o] })), { label: '% change in output per 1 % change in input' }); }; $('#se-out', root).addEventListener('change', draw); draw(); }
      $('#uq-go', root)?.addEventListener('click', () => { const out = $('#uq-out', root); out.innerHTML = '<span class="busy"></span> Sampling…'; setTimeout(() => { const u = Eng.uncertainty(c, 240); if (!u) { out.innerHTML = '<p class="dim small">No uncertain inputs.</p>'; return; } out.innerHTML = table(['Quantity', 'Median', '5th percentile', '95th percentile', 'Spread'], u.stats.slice(0, 10).map(s => [s.name, num(showScalar({ ...s, value: s.p50 })), num(showScalar({ ...s, value: s.p05 })), num(showScalar({ ...s, value: s.p95 })), num(s.p50 ? `± ${fmt((s.p95 - s.p05) / 2 / Math.abs(s.p50) * 100, 3)} %` : '—')])).__raw + (u.band ? '<div class="plot" style="margin-top:.5rem"><canvas class="pl" id="uq-plot"></canvas></div>' : '') + `<p class="small dim">${u.n - u.failed} of ${u.n} samples solved. Shaded band: 5th to 95th percentile. This is uncertainty from inputs only; it does not include error in the form of the model.</p>`; if (u.band) lineChart($('#uq-plot', root), { ...u.band.series, y: [u.band.series.y[0]], band: { lo: u.band.lo, hi: u.band.hi } }, { height: 260 }); }, 30); });
      $('#va-go', root)?.addEventListener('click', () => { const [sid, k] = $('#va-s', root).value.split('|'), s = r.series.find(q => q.id === sid), cx = cols.find(q => q.key === $('#va-x', root).value), cy = cols.find(q => q.key === $('#va-y', root).value), n = Math.min(cx.data.length, cy.data.length); const xs = [], ys = [], ps = []; for (let i = 0; i < n; i++) { const x = cx.data[i], y = cy.data[i]; if (!Number.isFinite(x) || !Number.isFinite(y) || x < N.minOf(s.x.data) || x > N.maxOf(s.x.data)) continue; xs.push(x); ys.push(y); ps.push(N.interp1(s.x.data, s.y[+k].data, x)); } const out = $('#va-out', root); if (xs.length < 2) { out.innerHTML = '<p class="note warn">Your data do not overlap the range of this curve. Check that the units match the plotted axes.</p>'; return; } const mt = N.metrics(ys, ps); out.innerHTML = `<div class="grid g4"><div class="stat"><div class="v">${fmt(mt.rmse, 4)}</div><div class="l">root-mean-square error (${esc(s.yUnit)})</div></div><div class="stat"><div class="v">${fmt(mt.bias, 3)}</div><div class="l">mean bias</div></div><div class="stat"><div class="v">${fmt(mt.mape, 3)} %</div><div class="l">mean absolute percentage error</div></div><div class="stat"><div class="v">${fmt(mt.r2, 4)}</div><div class="l">coefficient of determination</div></div></div><div class="plot" style="margin-top:.5rem"><canvas class="pl" id="va-plot"></canvas></div><p class="small dim">${xs.length} of your points lie within the model's range. Because nothing was fitted to them, this is an independent comparison. Whether the agreement is good enough depends on your measurement uncertainty and what the result will be used for.</p>`; lineChart($('#va-plot', root), { x: s.x, y: [s.y[+k]], yLabel: s.yLabel, yUnit: s.yUnit, points: xs.map((x, i) => ({ x, y: ys[i] })), pointsLabel: 'your measurements', logx: s.logx, logy: s.logy }, { height: 300, legend: true }); Eng.log(inv, `Model compared with user data (${cy.name}): RMSE ${fmt(mt.rmse, 4)}, bias ${fmt(mt.bias, 3)}, n = ${xs.length}`); X.save(); });
    },
  };
}

// =================================================================== optimisation and controls (Module 2)
function optimise(X) {
  const c = X.c, m = c.model, r = c.result; if (!m || r.status !== 'computed') return need('Optimisation works on a computed model.');
  const vars = c.inputs.filter(i => i.kind !== 'numerical' && i.kind !== 'constant'), outs = r.scalars.filter(s => Number.isFinite(s.value)), d = m.optimise || {};
  return {
    html: html`
      <div class="card"><h3>Optimisation</h3><p class="small dim">Choose what to minimise or maximise, which inputs may change, and any limit a result must respect. The search stays inside each input's permitted range.${d.note ? ` ${d.note}` : ''}</p>
        <div class="grid g3"><div><label class="f" for="op-obj">Objective</label><select id="op-obj">${join(outs, s => html`<option value="${s.sym}" ${s.sym === d.objective ? raw('selected') : ''}>${s.name}</option>`)}</select></div>
          <div><label class="f">Direction</label><div class="seg" id="op-sense"><button aria-pressed="${d.sense !== 'max'}" data-sense="min">Minimise</button><button aria-pressed="${d.sense === 'max'}" data-sense="max">Maximise</button></div></div>
          <div><label class="f" for="op-con">Constraint (optional)</label><div class="row" style="flex-wrap:nowrap"><select id="op-con"><option value="">none</option>${join(outs, s => html`<option value="${s.sym}">${s.sym}</option>`)}</select><select id="op-rel" style="max-width:64px"><option value="max">≤</option><option value="min">≥</option></select><input type="number" step="any" id="op-lim" placeholder="SI value"></div></div></div>
        <label class="f" style="margin-top:.6rem">Design variables</label><div class="row">${join(vars, i => html`<label class="row" style="gap:.3rem"><input type="checkbox" data-var="${i.sym}" ${(d.vars || []).includes(i.sym) ? raw('checked') : ''}> <span class="small">${i.name}</span></label>`)}</div>
        <div class="row" style="margin-top:.7rem"><button class="btn primary" id="op-go">Optimise</button><button class="btn" id="op-rs">Build a response surface</button></div><div id="op-out" style="margin-top:.7rem"></div></div>
      <div class="card"><h3>Operational recommendations</h3><p class="small dim">Drawn from the sensitivity of the present design.</p><div id="op-rec"></div></div>
      <div class="card"><h3>Not activated for this scenario</h3><p class="small dim">Controller tuning, real-time monitoring and digital-twin updating need a dynamic plant model and a live, authorised data connection. Neither is present, so no such results are shown.</p></div>`,
    after(root) {
      let sense = d.sense === 'max' ? 'max' : 'min';
      on(root, 'click', '[data-sense]', (_, el) => { sense = el.dataset.sense; $$('[data-sense]', root).forEach(b => b.setAttribute('aria-pressed', String(b === el))); });
      const chosen = () => $$('[data-var]', root).filter(x => x.checked).map(x => x.dataset.var);
      const s = Eng.sensitivity(c), rec = $('#op-rec', root);
      if (s && s.outputs.length) { const o = s.outputs.find(q => q.sym === d.objective) || s.outputs[0]; const rows = s.rows.filter(q => Number.isFinite(q.s[o.sym]) && Math.abs(q.s[o.sym]) > 0.02).sort((a, b) => Math.abs(b.s[o.sym]) - Math.abs(a.s[o.sym])).slice(0, 5); rec.innerHTML = rows.length ? `<ul class="clean">${rows.map(q => `<li><b>${esc(q.name)}</b>: raising it by 1 % ${q.s[o.sym] > 0 ? 'raises' : 'lowers'} ${esc(o.name.toLowerCase())} by ${fmt(Math.abs(q.s[o.sym]), 3)} %.${q.prov === 'SUPPLIED' ? ' It is currently a software-supplied reference value: measure it before acting on this.' : ''}</li>`).join('')}</ul>` : '<p class="dim small">No input has a notable influence at this operating point.</p>'; }
      $('#op-go', root).addEventListener('click', () => {
        const v = chosen(); if (!v.length) { toast('Select at least one design variable.'); return; } const out = $('#op-out', root); out.innerHTML = '<span class="busy"></span> Searching…';
        setTimeout(() => { const con = $('#op-con', root).value, lim = parseFloat($('#op-lim', root).value); const res = Eng.optimise(c, { objective: $('#op-obj', root).value, sense, vars: v, constraints: con && Number.isFinite(lim) ? [{ sym: con, [$('#op-rel', root).value]: lim }] : [] }); if (!res) { out.innerHTML = '<p class="note warn">The search could not start.</p>'; return; }
          const gain = res.before ? (res.after - res.before) / Math.abs(res.before) : 0;
          out.innerHTML = `<div class="grid g3"><div class="stat"><div class="v">${esc(showScalar({ ...res.objective, value: res.before }))}</div><div class="l">${esc(res.objective.name)} — present design</div></div><div class="stat"><div class="v" style="color:var(--ok)">${esc(showScalar({ ...res.objective, value: res.after }))}</div><div class="l">after optimisation (${esc(pct(gain))})</div></div><div class="stat"><div class="v">${res.iterations}</div><div class="l">iterations</div></div></div>` + table(['Design variable', 'Present', 'Optimised', 'Note'], res.vars.map(q => [q.name, num(`${fmt(fromSI(q.from, q.unit), 5)} ${q.unit}`), num(`${fmt(fromSI(q.to, q.unit), 5)} ${q.unit}`), q.atBound ? raw('<span class="chip warn">at the edge of its permitted range</span>') : ''])).__raw + '<div class="plot" style="margin-top:.5rem"><canvas class="pl" id="op-hist"></canvas></div>' + `<div class="row" style="margin-top:.5rem"><button class="btn sm primary" id="op-apply">Create a world with the optimised design</button></div><p class="small dim">An optimum on a boundary usually means the true optimum lies outside the range the model was built for, or that a constraint is missing. An optimised number is no more validated than the model that produced it.</p>`;
          lineChart($('#op-hist', root), { x: { label: 'Iteration', unit: '', data: res.history.map((_, i) => i) }, y: [{ label: 'Best objective so far', data: res.history }], yLabel: res.objective.name, yUnit: res.objective.unit }, { height: 220 });
          $('#op-apply', root).addEventListener('click', () => { const w = Eng.addWorld(X.inv, 'Optimised design', 'alternative'); res.vars.forEach(q => { w.inputs[q.sym] = { si: q.to, unit: q.unit, prov: 'DERIVED', note: `Optimised for ${sense === 'max' ? 'maximum' : 'minimum'} ${res.objective.name.toLowerCase()}` }; }); Eng.log(X.inv, 'Optimised design saved as a world'); X.refresh(); toast('Saved as the world “Optimised design”. Compare it with the baseline under Alternative Scenarios.'); });
        }, 30);
      });
      $('#op-rs', root).addEventListener('click', () => {
        const v = chosen().slice(0, 3); if (!v.length) { toast('Select one to three design variables.'); return; } const out = $('#op-out', root), obj = $('#op-obj', root).value, ins = v.map(sy => c.inputs.find(i => i.sym === sy));
        const box = ins.map(i => [Math.max(i.rangeSI[0], i.si * 0.6), Math.min(i.rangeSI[1], i.si * 1.4 || i.rangeSI[1])]), pts = N.latinHypercube(m.heavy ? 20 : 60, box, 11), ys = [], Xm = [];
        const feats = p => { const z = p.map((x, k) => (x - (box[k][0] + box[k][1]) / 2) / ((box[k][1] - box[k][0]) / 2 || 1)); const f = [1, ...z]; for (let a = 0; a < z.length; a++) for (let b = a; b < z.length; b++) f.push(z[a] * z[b]); return f; };
        pts.forEach(p => { const vv = { ...c.v }; ins.forEach((i, k) => { vv[i.sym] = p[k]; }); const rr = Eng.runModel(m, vv, c.a), s2 = rr.scalars.find(q => q.sym === obj); if (s2 && Number.isFinite(s2.value)) { ys.push(s2.value); Xm.push(feats(p)); } });
        if (ys.length < Xm[0].length + 2) { out.innerHTML = '<p class="note warn">Too few successful runs to fit a surface.</p>'; return; }
        const tr = ys.map((_, i) => i).filter(i => i % 5 !== 0), te = ys.map((_, i) => i).filter(i => i % 5 === 0), fit = N.linearRegression(tr.map(i => Xm[i]), tr.map(i => ys[i])), pred = te.map(i => N.sum(Xm[i].map((f, k) => f * fit.beta[k]))), mt = N.metrics(te.map(i => ys[i]), pred);
        const names = ['constant', ...ins.map(i => i.name)]; for (let a = 0; a < ins.length; a++) for (let b = a; b < ins.length; b++) names.push(a === b ? `${ins[a].name}²` : `${ins[a].name} × ${ins[b].name}`);
        out.innerHTML = `<p class="small">Quadratic response surface fitted to ${tr.length} solves and tested on ${te.length} held back. Inputs are scaled to ±1 over 60–140 % of their present values.</p><div class="grid g3"><div class="stat"><div class="v">${fmt(fit.r2, 4)}</div><div class="l">R² on the fitting runs</div></div><div class="stat"><div class="v">${fmt(mt.rmse, 3)}</div><div class="l">RMSE on held-back runs</div></div><div class="stat"><div class="v">${fmt(mt.mape, 3)} %</div><div class="l">mean error on held-back runs</div></div></div>` + table(['Term', 'Coefficient'], names.map((nm, k) => [nm, num(fmt(fit.beta[k], 4))])).__raw + '<p class="small dim">A surrogate is a fast approximation valid only inside the sampled box; its error is the held-back figure above.</p>';
      });
    },
  };
}

// =================================================================== engineering and safety (Module 2)
function safety(X) {
  const c = X.c, m = c.model, r = c.result; if (!m) return need('Engineering and safety assessments are generated from a model.');
  const g = c.gates.find(q => q.id === 'G');
  return {
    html: html`
      <div class="note warn"><b>Gate G — engineering release — is never granted by software.</b> ${g.text} Generated drawings and results are not manufacturing-certified or construction-approved documents.</div>
      <div class="card"><h3>Hazard identification and mitigation</h3>${m.hazards ? table(['Hazard', 'Cause', 'Consequence check', 'Mitigation'], m.hazards.map(h => [h.hazard, h.cause, 'To be assessed by the responsible engineer', h.mitigation])) : html`<p class="dim small">No hazards are recorded for this model.</p>`}
        ${m.experiment && (m.experiment.safety || []).length ? html`<h4 style="margin-top:.7rem">Precautions for testing</h4>${list(m.experiment.safety)}` : ''}</div>
      <div class="grid g2">
        <div class="card"><h3>Standards that typically apply</h3>${m.standards ? html`${list(m.standards)}<p class="small dim">Identified for orientation only. Editions and jurisdiction must be confirmed, and no compliance is claimed or implied.</p>` : html`<p class="dim small">None recorded.</p>`}</div>
        <div class="card"><h3>Margins in the present results</h3>${r.status === 'computed' ? scalarsTable(r.scalars.filter(s => /margin|factor|safety|utilis|ratio|limit|allow|critical|burst|risk/i.test(s.name)).slice(0, 10)) : ''}${r.status === 'computed' && !r.scalars.some(s => /margin|factor|safety|utilis|ratio|limit|allow|critical|burst|risk/i.test(s.name)) ? html`<p class="dim small">This model reports no explicit margin or safety factor.</p>` : ''}${join(r.warnings, w => html`<div class="note warn small">${w}</div>`)}</div>
      </div>
      <div class="card"><h3>Qualification path</h3><ol class="deriv">${join([['Parsed model and units', 'Geometry and data load; every value has an origin.', c.inputs.length > 0], ['Conservation and feasibility', 'Energy, mass, momentum and power budgets close before detailed claims.', (r.checks || []).length > 0 && r.checks.every(k => k.pass)], ['Verified numerics', 'Analytical tests, refinement studies, monitored residuals.', c.benchmarks.length > 0 && c.benchmarks.every(b => b.pass)], ['Independent component tests', 'Each mechanism reproduced under controlled conditions.', false], ['Integrated prototype', 'Controls, fallbacks, safety systems and uncertainty demonstrated together.', false], ['Field and industrial qualification', 'Independent measurements in realistic conditions, within regulation.', false]], ([t, d, ok]) => html`<li><b>${t}</b> ${ok ? chip('evidence present', 'ok') : chip('open', 'mute')}<br><span class="small dim">${d}</span></li>`)}</ol></div>
      <div class="card"><h3>Prototype and manufacture</h3>${m.experiment ? html`<p class="small">A demonstrator for the measurable part of this model is described under Experiments &amp; Measurements: ${m.experiment.objective}</p>` : ''}<p class="small dim">Bills of materials, fabrication sequences, tolerances and manufacturing drawings require a defined detailed geometry and a selected production process. They are not generated from a physics model alone, and are not shown here rather than being invented.</p></div>
      <div class="card"><h3>Integrity of this computation</h3><ul class="clean small"><li>All calculation runs on this device; no result is fetched from a server.</li><li>${X.inv.uploads.length} uploaded file(s) hashed with SHA-256 and parsed as data only.</li><li>${X.inv.audit.length} actions recorded in the audit trail, exportable with the report.</li></ul></div>`,
  };
}

// =================================================================== export
function exportView(X) {
  const { inv } = X, c = X.c, m = c.model, states = outputStates(inv, c), cat = catalogue(inv.module);
  const tally = {}; Object.values(states).forEach(s => { tally[s] = (tally[s] || 0) + 1; });
  const D = inv.module === 1 ? [['Thought experiment and conceptual framework', 'Scenario, hypotheses, system, assumptions, foundations and feasibility'], ['Mathematical equations, derivations and theory', 'Equations with origins, LaTeX derivations, proofs and provenance'], ['Logical and philosophical analysis', 'Propositions, deductions, truth tables and conditional conclusions'], ['Experimental design and measurement', 'Apparatus, instruments, procedure, controls and safety'], ['Simulation, visualisation and animation', 'Computed results, figures, data and animations'], ['Alternative worlds and assumption challenges', 'Worlds compared, dependencies, challenges and responses'], ['Verification, validation and interpretation', 'Checks, benchmarks, measurements, uncertainty and conclusions'], ['Reproducible research and source code', 'Reports, code, data, figures, history and references']]
    : [['Scientific and engineering model', 'Scenario, system, assumptions, data and environment'], ['Mathematical equations and derivations', 'Equations, closures, conditions and consistency evidence'], ['Numerical simulation and visualisation', 'Solver set-up, datasets, figures and animations'], ['Calibration, verification, validation and uncertainty', 'Benchmarks, comparisons, sensitivity and readiness'], ['Engineering design, optimisation and experiments', 'Optimised designs, apparatus, hazards and qualification path'], ['Alternative scenarios and scientific challenge', 'Changed assumptions, regenerated equations and dependencies'], ['Complete reproducible research and export', 'Reports, code, data, history and provenance']];
  return {
    html: html`
      <div class="card"><h3>Complete package</h3><p>Everything applicable in one archive: the report in three formats, the machine-readable model, the equation dossier, the Lean proof file, source code in Python, MATLAB and C++, every data series and every figure.</p>
        <div class="row"><button class="btn primary" data-x="zip">Download the reproducible package (ZIP)</button><span class="small dim" id="x-busy"></span></div>
        <h4 style="margin-top:.9rem">The ${D.length} deliverables it contains</h4><ol class="clean small">${join(D, ([t, d]) => html`<li><b>${t}.</b> <span class="dim">${d}</span></li>`)}</ol></div>
      <div class="grid g3">
        <div class="card"><h3>Reports</h3><div class="stack" style="--g:.4rem"><button class="btn" data-x="docx">Word document (.docx)</button><button class="btn" data-x="html">Web page (.html)</button><button class="btn" data-x="pdf">PDF — via Print</button><button class="btn" data-x="md">Markdown (.md)</button><button class="btn" data-x="tex">LaTeX (.tex)</button></div></div>
        <div class="card"><h3>Mathematics and code</h3><div class="stack"><button class="btn" data-x="eqtex">Equation dossier (LaTeX)</button><button class="btn" data-x="lean">Proof file (Lean 4)</button><button class="btn" data-x="py">Python</button><button class="btn" data-x="m">MATLAB / Octave</button><button class="btn" data-x="cpp">C++</button></div></div>
        <div class="card"><h3>Data</h3><div class="stack"><button class="btn" data-x="json">Model definition (JSON)</button><button class="btn" data-x="inputs">Input register (CSV)</button><button class="btn" data-x="results">Results (CSV)</button><button class="btn" data-x="series">All plotted series (ZIP of CSV)</button><button class="btn" data-x="inv">Whole investigation, to move to another device</button></div></div>
      </div>
      <div class="card"><h3>Coverage of the output catalogue</h3><div class="row">${join(Object.entries(tally).sort((a, b) => b[1] - a[1]), ([k, n]) => html`<span class="stat" style="padding:.4rem .7rem"><b>${n}</b> <span class="small dim">${{ generated: 'generated', computed: 'computed', derived: 'derived', verified: 'verified', validated: 'compared with data', interactive: 'interactive', ondemand: 'on request', partial: 'partly supported', needs: 'need your data', na: 'not applicable here', unavailable: 'unavailable', conditional: 'conditional' }[k] || k}</span></span>`)}</div>
        <p class="small dim" style="margin-top:.5rem">${cat.length} output categories exist for this module. Those not relevant to this scenario are left unpopulated on purpose.</p></div>
      <div class="card"><h3>Data sources used</h3>${Object.keys(inv.env || {}).length ? table(['Quantity', 'Source', 'Retrieved'], Object.entries(inv.env).map(([k, v]) => [k, v.source, when(v.ts) + (v.stale ? ' (cached copy)' : '')])) : html`<p class="small dim">No live source was used; all values are yours or bundled references.</p>`}${m && m.refs ? html`<h4 style="margin-top:.7rem">References</h4>${list(m.refs)}` : ''}</div>
      <div class="card"><h3>Audit trail</h3><div class="tw" style="max-height:320px;overflow:auto">${table(['Time', 'Action'], inv.audit.slice().reverse().slice(0, 150).map(a => [when(a.ts), a.action]))}</div></div>`,
    after(root) {
      const extras = () => ({ sensitivity: c.result.status === 'computed' ? Eng.sensitivity(c) : null, uncertainty: c.result.status === 'computed' && m && !m.heavy ? Eng.uncertainty(c, 120) : null, assumptionMap: Eng.assumptionMap(c), worlds: inv.worlds.length > 1 ? Eng.compareWorlds(inv) : null });
      const report = () => Ex.buildReport(inv, c, extras()), base = Ex.slug(inv.title), texR = s => { try { return window.katex.renderToString(s, { displayMode: true, throwOnError: false, output: 'mathml' }); } catch { return `<code>${esc(s)}</code>`; } };
      const figures = async () => { const out = [], host = document.createElement('div'); host.style.cssText = 'position:fixed;left:-9999px;top:0;width:820px'; host.className = 'card'; document.body.appendChild(host); try { for (const s of c.result.series.slice(0, 12)) { const cv = document.createElement('canvas'); cv.className = 'pl'; host.appendChild(cv); lineChart(cv, s, { height: 340, static: true, legend: true }); out.push({ name: s.id, caption: s.title, bytes: await canvasPng(cv), src: cv.toDataURL('image/png') }); } for (const f of c.result.fields.slice(0, 4)) { const cv = document.createElement('canvas'); cv.className = 'pl'; host.appendChild(cv); heatmap(cv, f, { height: 360 }); out.push({ name: f.id, caption: f.title, bytes: await canvasPng(cv), src: cv.toDataURL('image/png') }); } } finally { host.remove(); } return out; };
      on(root, 'click', '[data-x]', async (_, el) => {
        const k = el.dataset.x, busy = $('#x-busy', root);
        try {
          if (k === 'md') Ex.download(`${base}.md`, Ex.toMarkdown(report()));
          else if (k === 'tex') Ex.download(`${base}.tex`, Ex.toLatex(report()));
          else if (k === 'docx') Ex.download(`${base}.docx`, Ex.toDocx(report()));
          else if (k === 'html') Ex.download(`${base}.html`, Ex.toHtml(report(), texR, await figures()), 'text/html');
          else if (k === 'pdf') { const w = window.open('', '_blank'); if (!w) { toast('Allow pop-ups to print, or use the web-page export and print it.'); return; } w.document.write(Ex.toHtml(report(), texR, await figures())); w.document.close(); setTimeout(() => w.print(), 500); }
          else if (k === 'eqtex') Ex.download(`${base}-equations.tex`, Ex.equationsTex(inv, c));
          else if (k === 'lean') Ex.download(`${base}.lean`, Eng.leanSource(inv, c).source);
          else if (k === 'py') Ex.download(`${base}.py`, Ex.toPython(inv, c));
          else if (k === 'm') Ex.download(`${base.replace(/-/g, '_')}.m`, Ex.toMatlab(inv, c));
          else if (k === 'cpp') Ex.download(`${base}.cpp`, Ex.toCpp(inv, c));
          else if (k === 'json') Ex.download(`${base}-model.json`, Ex.modelJson(inv, c), 'application/json');
          else if (k === 'inputs') Ex.download(`${base}-inputs.csv`, Ex.inputsCsv(c), 'text/csv');
          else if (k === 'results') Ex.download(`${base}-results.csv`, Ex.scalarsCsv(c), 'text/csv');
          else if (k === 'series') { const { writeZip } = await import('../core/zip.js'); Ex.download(`${base}-series.zip`, writeZip(c.result.series.map(s => ({ name: `${Ex.slug(s.id)}.csv`, data: Ex.seriesCsv(s) })))); }
          else if (k === 'inv') Ex.download(`${base}.bespoke.json`, JSON.stringify({ format: 'bespoke-investigation/1', investigation: { ...inv, uploads: inv.uploads.map(u => ({ ...u, geometry: u.geometry ? { ...u.geometry, points: [], tris: null } : null })) } }), 'application/json');
          else if (k === 'zip') { busy.innerHTML = '<span class="busy"></span> Assembling…'; const figs = await figures(); Ex.download(`${base}-package.zip`, Ex.buildPackage(inv, c, { report: report(), lean: Eng.leanSource(inv, c).source, renderTex: texR, figures: figs, pngs: figs })); busy.textContent = ''; }
          Eng.log(inv, `Exported: ${el.textContent.trim()}`); X.save();
        } catch (e) { busy.textContent = ''; toast(`Export failed: ${e.message}`, 5000); console.error(e); }
      });
    },
  };
}

// =================================================================== reverse engineering
function reverse(X) {
  const { inv } = X, c = X.c, m = c.model, cols = numericColumns(inv), r = c.result;
  const geos = inv.uploads.filter(u => u.geometry && u.geometry.points && u.geometry.points.length >= 9);
  const fitDefault = (m && m.inverse) || {}, candidates = c.inputs.filter(i => i.kind !== 'numerical' && i.kind !== 'constant');
  const mode = inv.mode.startsWith('re') ? inv.mode : inv.module === 1 ? 're1' : 're2';
  return {
    html: html`
      <div class="card"><h3>Reverse engineering — ${mode === 're1' ? 'theories and equations' : mode === 're2' ? 'physical systems' : 'combined reconstruction'}</h3>
        <ol class="clean small" style="columns:2;column-gap:2rem"><li>Evidence in: outputs, measurements, geometry</li><li>Classify and choose a forward model</li><li>Register the unknowns</li><li>Test identifiability</li><li>Solve the inverse problem</li><li>Simulate forward and compare</li><li>Refine</li><li>Validate on held-back data</li><li>Export what is justified</li></ol>
        <p class="small dim">Each step below reports what it found, including when the answer is not unique.</p></div>
      ${!cols.length && !geos.length ? html`<div class="card"><div class="note warn"><b>No output data yet.</b> Reverse engineering starts from results. Add a table of measurements, a scan or a mesh in the <b>Inputs</b> workspace, or paste data on the Reverse Engineering page.</div><div class="row"><button class="btn primary" data-ws="inputs">Add evidence</button></div>
        ${m ? html`<p class="small" style="margin-top:.7rem">To try the workflow, synthetic “measurements” can be generated from the present model with noise added, so that the method can be seen recovering known values. They are labelled as synthetic.</p><button class="btn" id="synth">Generate a synthetic test dataset</button>` : ''}</div>` : ''}
      ${cols.length >= 2 ? html`
      <div class="card"><h3>A · Reconstruct equations from the data</h3><p class="small dim">Which mathematical form explains the observations? Candidate families are fitted, ranked, and tested on points held back.</p>
        <div class="grid g3"><div><label class="f" for="re-x">Independent variable (x)</label><select id="re-x">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 0 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div><label class="f" for="re-y">Observed response (y)</label><select id="re-y">${join(cols, (q, i) => html`<option value="${q.key}" ${i === 1 ? raw('selected') : ''}>${q.label}</option>`)}</select></div><div><label class="f" for="re-s">Uncertainty of y (optional)</label><select id="re-s"><option value="">not given</option>${join(cols, q => html`<option value="${q.key}">${q.label}</option>`)}</select></div></div>
        <button class="btn primary" id="re-eq" style="margin-top:.6rem">Reconstruct candidate equations</button><div id="re-eq-out" style="margin-top:.7rem"></div></div>
      ${m && r.status === 'computed' && r.series.length ? html`<div class="card"><h3>B · Reconstruct the inputs of the physical model</h3><p class="small dim">Which parameter values make <b>${m.title.toLowerCase()}</b> reproduce the observations? Choose the computed curve that corresponds to your data and the inputs that are unknown.</p>
        <div class="grid g2"><div><label class="f" for="re-curve">Model curve that your data correspond to</label><select id="re-curve">${join(r.series.flatMap(s => s.y.map((y, k) => ({ v: `${s.id}|${k}`, t: `${s.title} — ${y.label} [${s.yUnit}] against ${s.x.label} [${s.x.unit}]` }))), o => html`<option value="${o.v}" ${o.v.startsWith(`${fitDefault.series}|`) ? raw('selected') : ''}>${o.t}</option>`)}</select></div>
          <div><label class="f">Unknowns to reconstruct</label><div class="row">${join(candidates, i => html`<label class="row" style="gap:.3rem"><input type="checkbox" data-fit="${i.sym}" ${(fitDefault.fit || []).includes(i.sym) ? raw('checked') : ''}><span class="small">${i.name}</span></label>`)}</div></div></div>
        <p class="small dim">Your data must be in the units of the plotted axes. Three-quarters of the points are used to fit; one quarter is held back for validation.</p>
        <button class="btn primary" id="re-fit">Solve the inverse problem</button><div id="re-fit-out" style="margin-top:.7rem"></div></div>` : html`<div class="card"><h3>B · Reconstruct the inputs of a physical model</h3><p class="small dim">Choose a model in <b>Concept</b> whose computed curve corresponds to your data; its unknown inputs can then be estimated.</p></div>`}` : ''}
      ${geos.length ? html`<div class="card"><h3>C · Reconstruct geometry</h3>${join(geos, u => { const g = reconstructGeometry(u.geometry); return g ? html`<h4>${u.name}</h4><div class="grid g2"><div><div class="plot"><canvas class="pl" data-geo="${u.id}"></canvas></div></div><div><dl class="kv small"><dt>Points analysed</dt><dd>${g.nPoints.toLocaleString()}</dd><dt>Centroid</dt><dd>${g.centroid.map(v => fmt(v, 4)).join(', ')}</dd><dt>Principal extents</dt><dd>${g.principalExtents.map(v => fmt(v, 4)).join(' × ')} (file units)</dd>${u.geometry.volume ? html`<dt>Enclosed volume</dt><dd>${fmt(u.geometry.volume, 5)}</dd>` : ''}${u.geometry.area ? html`<dt>Surface area</dt><dd>${fmt(u.geometry.area, 5)}</dd>` : ''}</dl>
        ${table(['Candidate primitive', 'Scatter about the ideal surface', 'Fitted dimensions'], g.candidates.map(k => [k.shape, num(fmt(k.score, 3)), Object.entries(k.params).map(([a, b]) => `${a} = ${fmt(b, 4)}`).join(', ')]))}<p class="small dim">${g.text}</p></div></div>` : ''; })}</div>` : ''}
      <div class="card"><h3>Classification of what has been reconstructed</h3>${table(['Label', 'Meaning'], [['User-supplied', 'Directly provided by you'], ['Software-retrieved', 'Obtained from an identified external source'], ['Software-derived', 'Calculated from the evidence — reconstructed parameters carry this label'], ['Software-estimated', 'Estimated, with uncertainty and a documented method'], ['Software-assumed', 'Reference value adopted for the scenario'], ['Unresolved', 'Not reliably identifiable from what is available']])}
        <p class="small dim" style="margin-top:.5rem">A photograph may support approximate outer geometry but cannot reveal composition or internal structure. Where the evidence cannot decide, the result is a set of labelled candidates, not a single answer.</p></div>`,
    after(root) {
      geos.forEach(u => { const g = $(`canvas[data-geo="${u.id}"]`, root); if (g) view3d(g, { points: u.geometry.points, tris: u.geometry.tris }, { height: 280 }); });
      $('#synth', root)?.addEventListener('click', async () => {
        const s = r.series.find(q => q.id === fitDefault.series) || r.series[0]; if (!s) { toast('This model has no curve to sample.'); return; }
        const rnd = N.rng(4242), n = 24, idx = Array.from({ length: n }, (_, i) => Math.round(i * (s.x.data.length - 1) / (n - 1))), span = N.maxOf(s.y[0].data) - N.minOf(s.y[0].data) || Math.abs(s.y[0].data[0]) || 1;
        const csv = `${s.x.label} (${s.x.unit}),${s.y[0].label} (${s.yUnit})\n` + idx.map(i => `${s.x.data[i]},${s.y[0].data[i] + rnd.normal() * 0.01 * span}`).join('\n');
        const { importFile } = await import('../core/importers.js'), Store = await import('../core/store.js'), file = new File([csv], 'synthetic-test-data.csv', { type: 'text/csv' }), rec = await importFile(file);
        rec.summary = `SYNTHETIC test data generated from the model with 1 % noise. Not a measurement. ${rec.summary}`; inv.uploads.push(rec); await Store.saveUpload(rec, file); Eng.log(inv, 'Synthetic test dataset generated for the reverse-engineering demonstration'); X.refresh();
      });
      const col = k => cols.find(q => q.key === k);
      const data = () => { const cx = col($('#re-x', root).value), cy = col($('#re-y', root).value), cs = col($('#re-s', root).value), n = Math.min(cx.data.length, cy.data.length); const idx = Array.from({ length: n }, (_, i) => i).filter(i => Number.isFinite(cx.data[i]) && Number.isFinite(cy.data[i])).sort((a, b) => cx.data[a] - cx.data[b]); return { x: idx.map(i => cx.data[i]), y: idx.map(i => cy.data[i]), sigma: cs ? idx.map(i => cs.data[i]) : null, cx, cy }; };
      $('#re-eq', root)?.addEventListener('click', () => {
        const d = data(), out = $('#re-eq-out', root), sr = symbolicRegression(d.x, d.y); if (!sr.candidates.length) { out.innerHTML = `<p class="note warn">${esc(sr.text)}</p>`; return; }
        const best = sr.candidates[0], close = sr.candidates.filter(k => k.dBic < 2), xs = N.linspace(d.x[0], d.x[d.x.length - 1], 160);
        out.innerHTML = `<div class="note ${close.length === 1 ? 'ok' : 'warn'}"><b>${close.length === 1 ? 'One form is clearly preferred.' : `${close.length} forms explain the data about equally well.`}</b> ${close.length === 1 ? `The ${esc(best.name.toLowerCase())} form has the best penalised fit by a clear margin.` : `They cannot be told apart with these observations: ${esc(close.map(k => k.name).join('; '))}. The reconstruction is not unique.`}</div><div class="plot"><canvas class="pl" id="re-eq-plot"></canvas></div>` + table(['Rank', 'Candidate', 'Reconstructed equation', 'Parameters ± standard error', 'RMSE fit', 'RMSE held back', 'ΔBIC', ''], sr.candidates.slice(0, 7).map((k, i) => [i + 1, k.name, raw(`<code>${esc(k.expr)}</code>`), k.params.map((p, j) => `${fmt(p, 4)} ± ${fmt(k.se[j], 2)}`).join('; '), num(fmt(k.train.rmse, 3)), num(fmt(k.test.rmse, 3)), num(fmt(k.dBic, 3)), raw(`<button class="btn sm" data-adopt="${i}">Verify</button>`)])).__raw + `<p class="small dim">${esc(sr.text)} “Verify” sends a candidate to the equation laboratory, where it is checked for dimensions and singular terms and written to the Lean proof file.</p>` + (close.length > 1 ? `<div class="note"><b>Measurement that would separate them:</b> the candidates differ most at x ≈ ${fmt(xs[(() => { let bi = 0, bd = -1; xs.forEach((x, i) => { const v = close.map(k => k.f(x)).filter(Number.isFinite), dd = Math.max(...v) - Math.min(...v); if (dd > bd) { bd = dd; bi = i; } }); return bi; })()], 4)} within the measured range; extending the range of x usually separates them further.</div>` : '');
        lineChart($('#re-eq-plot', root), { x: { label: d.cx.name, unit: d.cx.unit, data: xs }, y: sr.candidates.slice(0, 4).map(k => ({ label: k.name, data: xs.map(k.f) })), yLabel: d.cy.name, yUnit: d.cy.unit, points: d.x.map((x, i) => ({ x, y: d.y[i] })), pointsLabel: 'observations' }, { height: 320, legend: true });
        on(out, 'click', '[data-adopt]', (_, el) => { const k = sr.candidates[+el.dataset.adopt], xn = d.cx.name.replace(/[^A-Za-z0-9_]/g, '_') || 'x', yn = d.cy.name.replace(/[^A-Za-z0-9_]/g, '_') || 'y'; inv.custom.equations.push({ lhs: yn, rhs: k.expr.replace(/\bx\b/g, xn), name: `Reconstructed: ${k.name}` }); inv.custom.symbols[xn] = inv.custom.symbols[xn] || { name: d.cx.name, unit: d.cx.unit || '1', min: d.x[0], max: d.x[d.x.length - 1] }; inv.custom.symbols[yn] = inv.custom.symbols[yn] || { name: d.cy.name, unit: d.cy.unit || '1' }; Eng.log(inv, `Reconstructed equation sent for verification: ${yn} = ${k.expr}`); X.save(); X.go('equations'); });
        Eng.log(inv, `Equation reconstruction: best candidate ${best.name}, ${close.length} within ΔBIC 2`); X.save();
      });
      $('#re-fit', root)?.addEventListener('click', () => {
        const syms = $$('[data-fit]', root).filter(x => x.checked).map(x => x.dataset.fit), out = $('#re-fit-out', root); if (!syms.length) { toast('Select at least one unknown.'); return; }
        const [sid, k] = $('#re-curve', root).value.split('|'), d = data(), params = syms.map(s => { const i = c.inputs.find(q => q.sym === s); return { sym: s, name: i.name, unit: i.unit, value: i.si, lo: i.rangeSI[0], hi: i.rangeSI[1] }; });
        out.innerHTML = '<span class="busy"></span> Fitting…';
        setTimeout(() => {
          const predict = p => { const v = { ...c.v }; syms.forEach((s, j) => { v[s] = p[j]; }); const rr = Eng.runModel(m, v, c.a), s = rr.series.find(q => q.id === sid); if (rr.status !== 'computed' || !s) return null; const xd = s.x.data, yd = s.y[+k].data; return x => N.interp1(xd, yd, x); };
          const s0 = r.series.find(q => q.id === sid), inside = d.x.filter(x => x >= N.minOf(s0.x.data) && x <= N.maxOf(s0.x.data)).length;
          if (inside < d.x.length * 0.5) { out.innerHTML = `<div class="note warn"><b>The data do not overlap this curve.</b> Only ${inside} of ${d.x.length} points fall inside the model's x-range (${fmt(N.minOf(s0.x.data), 3)}–${fmt(N.maxOf(s0.x.data), 3)} ${esc(s0.x.unit)}). Check the units and the choice of curve.</div>`; return; }
          const f = fitCurve(predict, d, params, { maxIt: m.heavy ? 15 : 50 }); if (!f.ok) { out.innerHTML = `<div class="note warn">${esc(f.text)}</div>`; return; }
          const comp2 = competingExplanations(d, f);
          out.innerHTML = `<div class="note ${f.unique ? 'ok' : 'warn'}"><b>Identifiability: ${f.unique ? 'unique' : 'not unique'}.</b> ${esc(f.verdict)}</div>` +
            table(['Unknown', 'Starting value', 'Reconstructed', '95 % interval', 'Relative uncertainty', 'Note'], f.estimates.map(e => [e.name, num(`${fmt(fromSI(e.value, e.unit), 4)} ${e.unit}`), raw(`<b>${esc(fmt(fromSI(e.estimate, e.unit), 5))} ${esc(e.unit)}</b>`), num(Number.isFinite(e.se) ? `${fmt(fromSI(e.lo95, e.unit), 4)} – ${fmt(fromSI(e.hi95, e.unit), 4)}` : 'not determined'), num(Number.isFinite(e.rel) ? fmt(e.rel * 100, 3) + ' %' : '—'), raw([e.atBound ? '<span class="chip warn">at range limit</span>' : '', e.identifiable ? '' : '<span class="chip bad">weakly identified</span>'].join(' '))])).__raw +
            `<div class="grid g2" style="margin-top:.6rem"><div><div class="plot"><canvas class="pl" id="re-fit-plot"></canvas></div></div><div><div class="plot"><canvas class="pl" id="re-res-plot"></canvas></div></div></div>` +
            `<div class="grid g4" style="margin-top:.6rem"><div class="stat"><div class="v">${fmt(f.train.rmse, 4)}</div><div class="l">RMSE on fitted points (${f.trainIdx.length})</div></div><div class="stat"><div class="v">${f.holdout ? fmt(f.holdout.rmse, 4) : '—'}</div><div class="l">RMSE on held-back points (${f.holdIdx.length})</div></div><div class="stat"><div class="v">${fmt(f.cond, 3)}</div><div class="l">condition number of the sensitivity matrix</div></div><div class="stat"><div class="v">${f.rank} / ${f.estimates.length}</div><div class="l">parameter combinations constrained</div></div></div>` +
            (f.corr && f.estimates.length > 1 ? `<h4 style="margin-top:.8rem">Parameter correlations</h4>${table(['', ...f.estimates.map(e => e.sym)], f.estimates.map((e, i) => [e.name, ...f.corr[i].map(v => num(fmt(v, 2)))])).__raw}` : '') +
            `<h4 style="margin-top:.8rem">Observable-to-unknown map and next measurement</h4>${table(['Unknown', 'Where the response is most informative about it'], f.recommend.map(q => [q.param, `x ≈ ${fmt(q.x, 4)} ${s0.x.unit}${q.inside ? '' : ' — outside your present data: a measurement here would add the most'}`])).__raw}` +
            `<h4 style="margin-top:.8rem">Competing explanations of the same data</h4>${table(['Explanation', 'Kind', 'Parameters', 'RMSE fit', 'RMSE held back', 'ΔBIC'], comp2.map(q => [q.kind === 'mechanistic' ? raw(`<b>${esc(q.name)}</b>`) : q.name, q.kind, q.k, num(fmt(q.rmse, 3)), num(fmt(q.holdout, 3)), num(fmt(q.dBic, 3))])).__raw}<p class="small dim">If a generic curve with no physics fits as well as the mechanistic model, the data alone do not support the mechanism; they are merely consistent with it.</p>` +
            `<div class="row" style="margin-top:.6rem"><button class="btn primary" id="re-apply">Adopt the reconstructed values as inputs</button><span class="small dim">They will be labelled software-derived, with this fit recorded as their basis.</span></div>`;
          const xs = N.linspace(N.minOf(d.x), N.maxOf(d.x), 160);
          lineChart($('#re-fit-plot', root), { x: { label: s0.x.label, unit: s0.x.unit, data: xs }, y: [{ label: 'Reconstructed model', data: xs.map(f.curve) }], yLabel: s0.yLabel, yUnit: s0.yUnit, overlay: [{ label: 'Before fitting', x: s0.x.data, y: s0.y[+k].data, dash: true }], points: d.x.map((x, i) => ({ x, y: d.y[i] })), pointsLabel: 'observations' }, { height: 280, legend: true });
          lineChart($('#re-res-plot', root), { x: { label: s0.x.label, unit: s0.x.unit, data: d.x }, y: [{ label: 'Residual (model − observed)', data: f.residuals, scatter: true }, { label: 'zero', data: d.x.map(() => 0), dash: true }], yLabel: 'Residual', yUnit: s0.yUnit }, { height: 280, legend: true });
          $('#re-apply', root).addEventListener('click', () => { const w = inv.worlds.find(q => q.id === inv.activeWorld); f.estimates.forEach(e => { w.inputs[e.sym] = { si: e.estimate, unit: e.unit, prov: 'DERIVED', note: `Reconstructed from ${d.cy.name} (${f.trainIdx.length} points; held-back RMSE ${f.holdout ? fmt(f.holdout.rmse, 3) : 'n/a'})${f.unique ? '' : '; NOT uniquely identified'}` }; }); Eng.log(inv, `Reconstructed inputs adopted: ${f.estimates.map(e => `${e.sym} = ${fmt(fromSI(e.estimate, e.unit), 5)} ${e.unit}`).join(', ')}`); X.refresh(); toast('Adopted. The model has been re-solved with the reconstructed inputs.'); });
          Eng.log(inv, `Inverse problem solved for ${syms.join(', ')}: ${f.unique ? 'unique' : 'non-unique'}, condition number ${fmt(f.cond, 3)}`); X.save();
        }, 30);
      });
    },
  };
}

export const views = { experiment, compute, visuals, worlds, evaluation, optimise, safety, export: exportView, reverse };
