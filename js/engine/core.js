// The investigation engine: turns a prompt into a structured, computed, verified investigation,
// and re-derives everything whenever an input, assumption or world changes.
import { MODELS, modelById } from '../models/index.js';
import * as P from './prompt.js';
import * as N from '../core/num.js';
import * as E from '../core/expr.js';
import { tryUnit, toSI, fromSI, dimEq, fmt, D0 } from '../core/units.js';
import { verifySystem, symbolTable } from '../core/verify.js';
import { generateLean } from '../core/lean.js';
import * as Logic from '../core/logic.js';
import { buckinghamPi, piToExpr } from '../core/discover.js';
import { CONSTANTS, ENV_KEYS, atmosphere, localGravity } from '../data/reference.js';
import { DOMAINS, LAWS } from '../data/domains.js';

export const PROV = {
  USER: { key: 'USER', label: 'User-supplied', tone: 'user', text: 'Entered by you or stated in your prompt.' },
  UPLOAD: { key: 'UPLOAD', label: 'Uploaded', tone: 'user', text: 'Read from a file you uploaded.' },
  RETRIEVED: { key: 'RETRIEVED', label: 'Software-retrieved', tone: 'live', text: 'Fetched from an identified external source, with its retrieval time.' },
  DERIVED: { key: 'DERIVED', label: 'Software-derived', tone: 'soft', text: 'Calculated from other inputs.' },
  ESTIMATED: { key: 'ESTIMATED', label: 'Software-estimated', tone: 'soft', text: 'Estimated from bundled climatology or correlations, with stated uncertainty.' },
  SUPPLIED: { key: 'SUPPLIED', label: 'Software-supplied', tone: 'soft', text: 'Reference value supplied by the software because none was given.' },
  HYPOTHETICAL: { key: 'HYPOTHETICAL', label: 'Hypothetical', tone: 'hypo', text: 'Invented or altered for a counterfactual scenario. Not a measured fact.' },
  UNRESOLVED: { key: 'UNRESOLVED', label: 'Unresolved', tone: 'bad', text: 'Not reliably identifiable from the available information.' },
};

const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const modelClass = m => (Array.isArray(m.klass) ? m.klass : [m.klass]);

/** Create a new investigation from a prompt. */
export function createInvestigation({ module, mode = 'A', prompt, modelId = null }) {
  const ranked = P.rankModels(prompt, MODELS, module);
  const chosen = modelId || (ranked[0] && ranked[0].score >= 4 ? ranked[0].id : null);
  const model = chosen ? modelById(chosen) : null;
  const inv = {
    id: uid(), v: 1, module, mode, prompt, title: P.titleFrom(prompt), created: Date.now(), updated: Date.now(),
    modelId: chosen, candidates: ranked.slice(0, 8),
    klass: P.classifyClass(prompt, model), domains: P.rankDomains(prompt).slice(0, 6),
    location: P.locate(prompt), bodies: P.celestial(prompt).map(b => b.key),
    env: {}, uploads: [], custom: { equations: [], symbols: {} },
    worlds: [{ id: 'w0', name: 'Baseline', kind: 'baseline', inputs: {}, assumptions: {}, note: '' }], activeWorld: 'w0',
    logic: null, challenges: [], versions: [], audit: [{ ts: Date.now(), action: 'Investigation created from prompt' }],
  };
  if (!inv.domains.length && model) inv.domains = model.domains.map(k => ({ key: k, name: DOMAINS[k].name, score: 1, hits: [] }));
  applyPrompt(inv);
  if (inv.klass.tags.includes('II') || !model) {
    const f = Logic.fromText(prompt);
    if (f.premises.length || f.conclusion) inv.logic = f;
  }
  // thought experiments in the library carry a vetted formal structure; prefer it to a thin reading of the prompt
  if (model && model.logicPreset && (!inv.logic || inv.logic.premises.length < 2 || !inv.logic.conclusion)) inv.logic = { ...JSON.parse(JSON.stringify(model.logicPreset)), notes: ['Formal structure taken from the model library. Edit it freely.'] };
  return inv;
}

/** Re-read quantities from the prompt and write them into the baseline world as user-supplied values. */
export function applyPrompt(inv) {
  const model = modelById(inv.modelId);
  const ex = P.extractQuantities(inv.prompt);
  inv.extracted = ex.items;
  if (!model) { inv.unmapped = ex.items; return; }
  const base = defaults(model);
  const { mapped, unmapped } = P.mapQuantities(ex, base);
  const w = inv.worlds[0];
  mapped.forEach(({ q, sym }) => {
    const i = base.find(b => b.sym === sym);
    w.inputs[sym] = { si: q.si, prov: 'USER', note: `From your prompt: “${q.raw}”`, unit: q.unit && tryUnit(q.unit) && dimEq(tryUnit(q.unit).dim, tryUnit(i.unit).dim) && q.unit !== 'c' ? q.unit : i.unit };
  });
  inv.unmapped = unmapped;
}

/** Model inputs with SI values and SI ranges. */
export function defaults(model) {
  return model.inputs.map(i => {
    const u = tryUnit(i.unit) || { f: 1, o: 0, dim: D0 };
    const si = i.value * u.f + u.o;
    const rangeSI = [i.min != null ? i.min * u.f + u.o : (si > 0 ? si / 100 : si < 0 ? si * 100 : -1), i.max != null ? i.max * u.f + u.o : (si > 0 ? si * 100 : si < 0 ? si / 100 : 1)];
    return { ...i, si, rangeSI, dim: u.dim };
  });
}

const ENV_FROM_GAZ = { water_depth: g => g.depth, seabed_temp: g => g.seabedT + 273.15, sea_surface_temp: g => g.sst + 273.15, wave_height: g => g.Hs, wave_period: g => g.Tp, current_speed: g => g.current, salinity: g => g.salinity ?? 35, latitude: g => g.lat };
/** Value for an environmental binding: live connector first, then gazetteer climatology. */
function envValue(inv, key) {
  const live = inv.env && inv.env[key];
  if (live && Number.isFinite(live.value)) return { si: live.value, prov: 'RETRIEVED', note: `${live.source}; retrieved ${new Date(live.ts).toISOString().replace('T', ' ').slice(0, 16)} UTC${live.stale ? ' (cached copy)' : ''}`, ts: live.ts };
  const loc = inv.location;
  if (!loc) return null;
  if (loc.marine && ENV_FROM_GAZ[key] && loc.depth != null) { const v = ENV_FROM_GAZ[key](loc); if (v != null) return { si: v, prov: 'ESTIMATED', note: `Climatological value for ${loc.name} (built-in gazetteer); connect to refine` }; }
  if (key === 'gravity' && loc.lat != null) return { si: localGravity(loc.lat, loc.alt || 0), prov: 'DERIVED', note: `WGS-84 normal gravity at latitude ${loc.lat.toFixed(1)}°` };
  if (loc.alt != null) {
    const a = atmosphere(loc.alt);
    const m = { air_temp: a.T, air_pressure: a.p, air_density: a.rho, elevation: loc.alt }[key];
    if (m != null) return { si: m, prov: 'ESTIMATED', note: `Standard atmosphere at ${loc.alt} m (${loc.name})` };
  }
  return null;
}

/** Resolve every input of the model for one world, with provenance. */
export function resolveInputs(inv, model, world) {
  const base = inv.worlds[0];
  return defaults(model).map(d => {
    const ov = world.inputs[d.sym] || (world !== base ? base.inputs[d.sym] : null);
    let r;
    if (ov) r = { si: ov.si, prov: ov.prov || 'USER', note: ov.note || '', unit: ov.unit || d.unit };
    else {
      const ev = d.env ? envValue(inv, d.env) : null;
      if (ev) r = { ...ev, unit: d.unit };
      else r = { si: d.si, prov: d.kind === 'hypothetical' ? 'HYPOTHETICAL' : 'SUPPLIED', note: d.src || (d.kind === 'constant' ? CONSTANTS[d.sym]?.src : 'Representative reference value'), unit: d.unit };
    }
    if (d.kind === 'constant' && CONSTANTS[d.sym] && Math.abs(r.si - CONSTANTS[d.sym].value) > Math.abs(CONSTANTS[d.sym].value) * 1e-9) { r.prov = 'HYPOTHETICAL'; r.note = `Altered from the accepted value ${fmt(CONSTANTS[d.sym].value, 6)} ${d.unit}`; }
    const unc = d.unc != null ? d.unc : r.prov === 'USER' || r.prov === 'UPLOAD' ? 0.02 : r.prov === 'RETRIEVED' ? 0.05 : d.kind === 'constant' ? (CONSTANTS[d.sym]?.rel || 0) : d.kind === 'numerical' ? 0 : 0.10;
    return { ...d, ...r, value: fromSI(r.si, r.unit), unc, default: d.si, overridden: !!ov, inWorld: !!world.inputs[d.sym] };
  });
}
export const assumptionState = (model, world, base) => Object.fromEntries((model.assumptions || []).map(a => [a.id, world.assumptions[a.id] ?? (base && base !== world ? base.assumptions[a.id] : undefined) ?? a.on]));

const cache = new Map();
const keyOf = (inv, world) => JSON.stringify([inv.id, inv.modelId, world.inputs, world.assumptions, inv.worlds[0].inputs, inv.worlds[0].assumptions, inv.env, inv.location && inv.location.name, inv.custom, inv.logic]);

/** Run one model evaluation with explicit SI values; never throws. */
export function runModel(model, v, a, light = false) {
  const t0 = (typeof performance !== 'undefined' ? performance : Date).now();
  try {
    const r = model.solve(v, a, { light }) || {};
    const res = { scalars: r.scalars || [], series: r.series || [], fields: r.fields || [], anims: r.anims || [], paths: r.paths || [], checks: r.checks || [], warnings: r.warnings || [], notes: r.notes || [], status: 'computed' };
    const bad = res.scalars.filter(s => typeof s.value === 'number' && !Number.isFinite(s.value) && !s.text);
    if (bad.length) res.warnings.push(`Non-finite value returned for ${bad.map(s => s.name).join(', ')}.`);
    res.ms = (typeof performance !== 'undefined' ? performance : Date).now() - t0;
    return res;
  } catch (err) {
    return { scalars: [], series: [], fields: [], anims: [], paths: [], checks: [], warnings: [], notes: [], status: 'failed', error: err.message, ms: 0 };
  }
}

/** Full computation for one world of an investigation. */
export function compute(inv, worldId = inv.activeWorld) {
  const world = inv.worlds.find(w => w.id === worldId) || inv.worlds[0];
  const k = keyOf(inv, world);
  if (cache.has(k)) return cache.get(k);
  const model = modelById(inv.modelId);
  const out = { worldId: world.id, model, ts: Date.now() };
  // logic is independent of any physical model
  if (inv.logic && inv.logic.premises && (inv.logic.premises.length || inv.logic.conclusion)) {
    try { out.logic = Logic.analyse(inv.logic.premises, inv.logic.conclusion); out.logic.lines = Logic.explain(out.logic); }
    catch (err) { out.logicError = err.message; }
  }
  if (model) {
    out.inputs = resolveInputs(inv, model, world);
    out.a = assumptionState(model, world, inv.worlds[0]);
    out.v = Object.fromEntries(out.inputs.map(i => [i.sym, i.si]));
    out.result = runModel(model, out.v, out.a);
    try { out.equations = model.equations(out.a, out.v) || []; } catch (err) { out.equations = []; out.eqError = err.message; }
    try { out.derivation = model.derivation ? model.derivation(out.a, out.v) : []; } catch { out.derivation = []; }
    out.table = symbolTable(out.inputs, model.symbols || {}, out.result.scalars);
    out.verification = verifySystem(out.equations, out.table, out.inputs.map(i => i.sym).concat(Object.keys(out.table).filter(s => out.table[s].constant)));
    try { out.benchmarks = model.benchmarks ? model.benchmarks(out.v, out.a) : []; } catch (err) { out.benchmarks = []; out.benchError = err.message; }
    out.validation = runValidation(model, out);
  } else {
    out.inputs = []; out.a = {}; out.v = {}; out.equations = []; out.derivation = [];
    out.result = { scalars: [], series: [], fields: [], anims: [], paths: [], checks: [], warnings: [], notes: [], status: 'not-computable', error: 'No computable model has been selected for this prompt.' };
    out.table = symbolTable([], {}, []); out.benchmarks = []; out.validation = [];
  }
  // user-entered equations are verified alongside
  if (inv.custom && inv.custom.equations.length) {
    const ct = { ...out.table };
    Object.entries(inv.custom.symbols || {}).forEach(([s, m]) => { const u = tryUnit(m.unit); ct[s] = { dim: u ? u.dim : D0, name: m.name || s, unit: m.unit, range: m.min != null && m.max != null ? [toSI(m.min, m.unit), toSI(m.max, m.unit)] : (m.value != null ? [toSI(m.value, m.unit), toSI(m.value, m.unit)] : undefined), value: m.value != null ? toSI(m.value, m.unit) : undefined }; });
    out.customTable = ct;
    out.customVerification = verifySystem(inv.custom.equations.map((q, i) => ({ id: `user${i + 1}`, name: q.name || `Your equation ${i + 1}`, lhs: q.lhs, rhs: q.rhs, kind: 'hypothesis' })), ct, Object.keys(ct).filter(s => ct[s].value != null));
  }
  out.generic = genericAnalysis(inv, model);
  out.gates = gates(inv, out);
  out.readiness = readiness(inv, out);
  if (cache.size > 40) cache.delete(cache.keys().next().value);
  cache.set(k, out);
  return out;
}
export const clearCache = () => cache.clear();

function runValidation(model, comp) {
  return (model.validation || []).map(set => ({
    name: set.name, ref: set.ref, note: set.note,
    cases: set.cases.map(c => {
      const v = { ...comp.v, ...c.inputs }, a = { ...comp.a, ...(c.assumptions || {}) };
      const r = runModel(model, v, a), s = r.scalars.find(q => q.sym === c.observable);
      const predicted = s ? s.value : NaN, err = predicted - c.observed;
      const z = c.sigma ? err / c.sigma : null;
      return { label: c.label || '', observed: c.observed, sigma: c.sigma, predicted, unit: s ? s.unit : '', show: s && s.show, rel: c.observed !== 0 ? err / c.observed : err, z, pass: z != null ? Math.abs(z) <= 2 : Math.abs(err) <= 0.05 * Math.abs(c.observed), name: s ? s.name : c.observable };
    }),
  }));
}

/** Analysis that needs no model: laws for the detected domains, dimensional analysis of prompt quantities, what is missing. */
function genericAnalysis(inv, model) {
  const domKeys = inv.domains.map(d => d.key);
  const lawKeys = new Set(model ? model.laws || [] : []);
  const DOM_LAWS = { pipeline: ['mass', 'momentum', 'energy', 'darcy'], multiphase: ['mass', 'momentum'], hydrates: ['mass', 'energy', 'species'], cfd: ['mass', 'momentum', 'energy'], fsi: ['momentum', 'newton2', 'hooke'], thermal: ['energy', 'second', 'fourier', 'stefan'], electromagnetic: ['maxwell', 'charge', 'lorentz', 'ohm'], classical: ['newton2', 'newton3', 'energy', 'momentum', 'angular', 'gravitation', 'action'], relativity: ['sr', 'equivalence', 'efe', 'causality'], quantum: ['schrodinger', 'born', 'uncertainty', 'pauli'], logic: ['logic_nc', 'logic_em', 'kolmogorov'], aerospace: ['mass', 'momentum', 'energy', 'bernoulli', 'ideal_gas'], marine: ['archimedes', 'momentum', 'mass'], offshore: ['momentum', 'archimedes', 'hooke'], mechanical: ['newton2', 'hooke', 'energy'], structural: ['newton2', 'hooke'], desalination: ['mass', 'species', 'energy', 'fick'], chemical: ['mass', 'species', 'energy', 'second'], nuclear: ['mass', 'energy'], materials: ['hooke', 'maxwell', 'energy'], geotechnical: ['newton2', 'mass'], space: ['gravitation', 'newton2', 'angular', 'energy', 'stefan'], waves: ['momentum', 'mass', 'energy'] };
  domKeys.forEach(k => (DOM_LAWS[k] || []).forEach(l => lawKeys.add(l)));
  if (!lawKeys.size) ['energy', 'momentum', 'mass', 'causality'].forEach(l => lawKeys.add(l));
  const dimQ = (inv.extracted || []).filter(q => !q.bare).map((q, i) => ({ sym: `q${i + 1}`, dim: q.dim, raw: q.raw, quantity: q.quantity }));
  let pi = null;
  if (dimQ.length >= 2) { try { pi = buckinghamPi(dimQ); pi.exprs = pi.groups.map(piToExpr); pi.quantities = dimQ; } catch { pi = null; } }
  return { laws: [...lawKeys].filter(k => LAWS[k]), pi, quantities: dimQ };
}

/** The seven scientific gates. Each has a status and the evidence behind it. */
function gates(inv, c) {
  const g = [];
  const r = c.result, ver = c.verification;
  const prov = c.inputs.reduce((m, i) => { m[i.prov] = (m[i.prov] || 0) + 1; return m; }, {});
  g.push({ id: 'A', name: 'Evidence intake', status: c.inputs.length ? 'pass' : 'open', text: c.inputs.length ? `${c.inputs.length} inputs registered with provenance: ${Object.entries(prov).map(([k, n]) => `${n} ${PROV[k].label.toLowerCase()}`).join(', ')}. ${inv.uploads.length} uploaded file(s) hashed and logged.` : 'No model inputs yet. The prompt record and any uploads are preserved with their hashes.' });
  const cons = r.checks || [];
  const hypo = c.model && (c.model.hypothetical || modelClass(c.model)[0] === 'III');
  g.push({ id: 'B', name: 'Physical plausibility', status: !c.model ? 'open' : cons.some(x => !x.pass) ? 'fail' : hypo ? 'conditional' : cons.length ? 'pass' : 'open', text: !c.model ? 'Awaiting a model.' : cons.length ? `${cons.filter(x => x.pass).length} of ${cons.length} conservation and consistency checks pass.${hypo ? ' The central law is hypothetical, so plausibility is conditional on the stated postulates.' : ''}` : 'This model declares no automatic conservation checks.' });
  const kinds = (c.equations || []).reduce((m, q) => { m[q.kind] = (m[q.kind] || 0) + 1; return m; }, {});
  g.push({ id: 'C', name: 'Equation traceability', status: c.equations.length ? 'pass' : 'open', text: c.equations.length ? `Every equation carries its origin: ${Object.entries(kinds).map(([k, n]) => `${n} ${k}`).join(', ')}. Laws, closures, empirical relations and hypotheses are kept apart.` : 'No equations yet.' });
  g.push({ id: 'D', name: 'Mathematical closure', status: !ver ? 'open' : ver.summary.inconsistent || ver.summary.rejected ? 'fail' : !ver.closure.closed ? 'conditional' : ver.summary.singular ? 'conditional' : 'pass', text: !ver ? 'Awaiting equations.' : `${ver.closure.text} ${ver.summary.verified + ver.summary.conditional} of ${ver.summary.total} equations are dimensionally homogeneous and finite on the declared domain${ver.summary.singular ? `; ${ver.summary.singular} had a singular term and received a regularised form` : ''}.` });
  const b = c.benchmarks || [];
  g.push({ id: 'E', name: 'Numerical verification', status: r.status !== 'computed' ? 'open' : !b.length ? 'conditional' : b.every(x => x.pass) ? 'pass' : 'fail', text: r.status !== 'computed' ? (r.error || 'Not computed.') : b.length ? `${b.filter(x => x.pass).length} of ${b.length} comparisons with exact solutions are within tolerance.` : 'Computed, but no analytical benchmark is attached to this model; treat the numbers as unverified.' });
  const vc = (c.validation || []).flatMap(s => s.cases);
  g.push({ id: 'F', name: 'Experimental validation', status: !vc.length ? 'open' : vc.every(x => x.pass) ? 'pass' : 'conditional', text: vc.length ? `${vc.filter(x => x.pass).length} of ${vc.length} comparisons with published measurements agree within two standard uncertainties. This supports the model inside that range only.` : 'No independent measurements are attached. Upload your own data to test the model; until then it is unvalidated.' });
  g.push({ id: 'G', name: 'Safety and engineering release', status: 'open', text: 'Never granted by software. Release for construction or operation needs recognised standards, competent review and measured qualification.' });
  return g;
}

export const READINESS = ['Untested hypothesis', 'Internally consistent formulation', 'Numerically verified model', 'Empirically supported model', 'Independently validated model'];
function readiness(inv, c) {
  let level = 0; const why = [];
  const ver = c.verification;
  if (ver && ver.summary.total && !ver.summary.inconsistent && !ver.summary.rejected) { level = 1; why.push('All equations parse, are dimensionally homogeneous, and are finite on the declared domain or carry an explicit domain condition.'); }
  else why.push('Mathematical consistency has not been established.');
  if (level === 1 && c.result.status === 'computed' && c.benchmarks.length && c.benchmarks.every(b => b.pass) && (c.result.checks || []).every(x => x.pass)) { level = 2; why.push('Numerical results reproduce exact solutions and satisfy the conservation checks.'); }
  const vc = (c.validation || []).flatMap(s => s.cases);
  if (level === 2 && vc.length && vc.every(x => x.pass)) { level = 3; why.push('Predictions agree with published measurements within their uncertainty.'); }
  const hypo = c.model && (c.model.hypothetical || modelClass(c.model)[0] === 'III');
  if (hypo && level > 2) level = 2;
  if (hypo) why.push('The governing law is hypothetical: no amount of internal testing validates it as a description of nature.');
  why.push('Level 5 is reserved for agreement with independent data that you supply and that was not used to fit anything.');
  return { level, label: READINESS[level], why };
}

// ---------------------------------------------------------------- analyses built on compute()
const scalarMap = r => Object.fromEntries(r.scalars.filter(s => Number.isFinite(s.value)).map(s => [s.sym, s.value]));
const variable = c => c.inputs.filter(i => i.kind !== 'numerical');

/** Local sensitivity: normalised derivative d ln(output) / d ln(input) by central differences. */
export function sensitivity(c, step = 0.02) {
  const model = c.model; if (!model || c.result.status !== 'computed') return null;
  const base = scalarMap(c.result), outs = Object.keys(base), rows = [];
  for (const i of variable(c)) {
    const h = Math.abs(i.si) > 0 ? Math.abs(i.si) * step : (i.rangeSI[1] - i.rangeSI[0]) * step || step;
    const up = scalarMap(runModel(model, { ...c.v, [i.sym]: N.clamp(i.si + h, i.rangeSI[0], i.rangeSI[1]) }, c.a, true));
    const dn = scalarMap(runModel(model, { ...c.v, [i.sym]: N.clamp(i.si - h, i.rangeSI[0], i.rangeSI[1]) }, c.a, true));
    const dx = N.clamp(i.si + h, i.rangeSI[0], i.rangeSI[1]) - N.clamp(i.si - h, i.rangeSI[0], i.rangeSI[1]);
    const s = {};
    outs.forEach(o => { if (up[o] == null || dn[o] == null || dx === 0) { s[o] = NaN; return; } const d = (up[o] - dn[o]) / dx; s[o] = base[o] !== 0 && i.si !== 0 ? d * i.si / base[o] : d; });
    rows.push({ sym: i.sym, name: i.name, prov: i.prov, s });
  }
  return { outputs: c.result.scalars.filter(s => outs.includes(s.sym)), rows };
}

/** Monte-Carlo propagation of input uncertainty (Latin hypercube, deterministic seed). */
export function uncertainty(c, n = 200) {
  const model = c.model; if (!model || c.result.status !== 'computed') return null;
  const vars = variable(c).filter(i => i.unc > 0);
  if (!vars.length) return null;
  if (model.heavy) n = Math.min(n, 40);
  const pts = N.latinHypercube(n, vars.map(() => [0, 1]), 2024);
  const inv = p => { const q = N.clamp(p, 1e-6, 1 - 1e-6); const t = Math.sqrt(-2 * Math.log(q < 0.5 ? q : 1 - q)); const z = t - (2.515517 + 0.802853 * t + 0.010328 * t * t) / (1 + 1.432788 * t + 0.189269 * t * t + 0.001308 * t ** 3); return q < 0.5 ? -z : z; };
  const samples = {}; let failed = 0; const firstSeries = c.result.series[0]; const bands = firstSeries ? firstSeries.y.map(() => []) : [];
  for (const p of pts) {
    const v = { ...c.v };
    vars.forEach((i, k) => { const sd = Math.abs(i.si) > 0 ? Math.abs(i.si) * i.unc : (i.rangeSI[1] - i.rangeSI[0]) * i.unc; v[i.sym] = N.clamp(i.si + inv(p[k]) * sd, i.rangeSI[0], i.rangeSI[1]); });
    const r = runModel(model, v, c.a);
    if (r.status !== 'computed') { failed++; continue; }
    r.scalars.forEach(s => { if (Number.isFinite(s.value)) (samples[s.sym] = samples[s.sym] || []).push(s.value); });
    if (firstSeries && r.series[0] && r.series[0].x.data.length === firstSeries.x.data.length) r.series[0].y.forEach((y, k) => bands[k] && bands[k].push(y.data));
  }
  const stats = c.result.scalars.filter(s => samples[s.sym] && samples[s.sym].length > 5).map(s => { const a = samples[s.sym]; return { ...s, mean: N.mean(a), sd: N.std(a), p05: N.quantile(a, 0.05), p50: N.quantile(a, 0.5), p95: N.quantile(a, 0.95), hist: N.histogram(a, 20) }; });
  let band = null;
  if (firstSeries && bands[0] && bands[0].length > 5) { const m = firstSeries.x.data.length; band = { series: firstSeries, lo: Array.from({ length: m }, (_, j) => N.quantile(bands[0].map(a => a[j]), 0.05)), hi: Array.from({ length: m }, (_, j) => N.quantile(bands[0].map(a => a[j]), 0.95)) }; }
  return { n, failed, vars: vars.map(i => ({ sym: i.sym, name: i.name, unc: i.unc, prov: i.prov })), stats, band };
}

/** One-at-a-time parameter sweep of an input over its range (or a custom range). */
export function sweep(c, sym, nPts = 30, lo, hi) {
  const model = c.model, i = c.inputs.find(q => q.sym === sym); if (!model || !i) return null;
  const a = lo ?? Math.max(i.rangeSI[0], i.si > 0 ? i.si / 4 : i.rangeSI[0]), b = hi ?? Math.min(i.rangeSI[1], i.si > 0 ? i.si * 4 : i.rangeSI[1]);
  if (model.heavy) nPts = Math.min(nPts, 12);
  const xs = N.linspace(a, b, nPts), out = {};
  xs.forEach((x, k) => { const r = runModel(model, { ...c.v, [sym]: x }, c.a, true); r.scalars.forEach(s => { (out[s.sym] = out[s.sym] || { ...s, data: new Array(nPts).fill(NaN) }).data[k] = Number.isFinite(s.value) ? s.value : NaN; }); });
  return { input: i, xs, outputs: Object.values(out).filter(o => o.data.some(Number.isFinite)) };
}

/** Which conclusions depend on which assumptions: flip each assumption alone and measure the change in every output. */
export function assumptionMap(c) {
  const model = c.model; if (!model || !(model.assumptions || []).length || c.result.status !== 'computed') return null;
  const base = scalarMap(c.result), outs = c.result.scalars.filter(s => s.sym in base);
  const eqBase = new Map(c.equations.map(q => [q.id, `${q.lhs}=${q.rhs}`]));
  const rows = model.assumptions.map(a => {
    const flipped = { ...c.a, [a.id]: !c.a[a.id] };
    const r = runModel(model, c.v, flipped, true), m = scalarMap(r);
    let eqs = []; try { eqs = model.equations(flipped, c.v) || []; } catch { eqs = []; }
    const changedEq = [...new Set([...eqs.filter(q => eqBase.get(q.id) !== `${q.lhs}=${q.rhs}`).map(q => q.name), ...c.equations.filter(q => !eqs.some(x => x.id === q.id)).map(q => q.name)])];
    const delta = {}; let maxRel = 0;
    outs.forEach(o => { if (m[o.sym] == null) { delta[o.sym] = NaN; return; } const d = base[o.sym] !== 0 ? (m[o.sym] - base[o.sym]) / Math.abs(base[o.sym]) : m[o.sym] - base[o.sym]; delta[o.sym] = d; if (Number.isFinite(d)) maxRel = Math.max(maxRel, Math.abs(d)); });
    return { id: a.id, text: a.text, alt: a.alt, on: c.a[a.id], status: r.status, error: r.error, delta, maxRel, changedEq, dependents: outs.filter(o => Math.abs(delta[o.sym]) > 1e-6).map(o => o.name) };
  });
  rows.sort((x, y) => y.maxRel - x.maxRel);
  const robust = outs.filter(o => rows.every(r => !(Math.abs(r.delta[o.sym]) > 0.01))).map(o => o.name);
  const fragile = outs.filter(o => rows.some(r => Math.abs(r.delta[o.sym]) > 0.10)).map(o => o.name);
  return { outputs: outs, rows, robust, fragile };
}

/** Side-by-side comparison of worlds. */
export function compareWorlds(inv, ids = inv.worlds.map(w => w.id)) {
  const comps = ids.map(id => compute(inv, id)), base = comps[0];
  const syms = [...new Set(comps.flatMap(c => c.result.scalars.map(s => s.sym)))];
  const rows = syms.map(sym => {
    const cells = comps.map(c => c.result.scalars.find(s => s.sym === sym) || null), b = cells[0];
    return { sym, name: (cells.find(Boolean) || {}).name, unit: (cells.find(Boolean) || {}).unit, show: (cells.find(Boolean) || {}).show, cells, rel: cells.map(x => (x && b && Number.isFinite(x.value) && Number.isFinite(b.value) && b.value !== 0 ? (x.value - b.value) / Math.abs(b.value) : null)) };
  });
  const inDiff = base.inputs.map(i => ({ sym: i.sym, name: i.name, unit: i.unit, vals: comps.map(c => c.inputs.find(q => q.sym === i.sym)) })).filter(r => r.vals.some(v => v && Math.abs(v.si - r.vals[0].si) > 1e-12 * Math.max(1, Math.abs(r.vals[0].si))));
  const asDiff = (base.model?.assumptions || []).map(a => ({ id: a.id, text: a.text, vals: comps.map(c => c.a[a.id]) })).filter(r => r.vals.some(v => v !== r.vals[0]));
  const eqDiff = comps.map(c => c.equations.filter(q => { const b0 = base.equations.find(x => x.id === q.id); return !b0 || b0.rhs !== q.rhs || b0.lhs !== q.lhs; }));
  return { worlds: ids.map(id => inv.worlds.find(w => w.id === id)), comps, rows, inDiff, asDiff, eqDiff, shared: rows.filter(r => r.rel.every(x => x == null || Math.abs(x) < 0.01)).map(r => r.name), divergent: rows.filter(r => r.rel.some(x => x != null && Math.abs(x) >= 0.10)).map(r => r.name) };
}

/** Grid/time-step convergence: run at three resolutions and report the observed order (Richardson). */
export function convergence(c) {
  const model = c.model, key = model && model.numerics && model.numerics.resolution; if (!key) return null;
  const i = c.inputs.find(q => q.sym === key); if (!i) return null;
  const n0 = Math.max(4, Math.round(i.si / 2)), levels = [n0, n0 * 2, n0 * 4].map(n => Math.min(n, i.rangeSI[1]));
  if (levels[2] <= levels[1]) return null;
  const runs = levels.map(n => scalarMap(runModel(model, { ...c.v, [key]: n }, c.a, true)));
  const rows = c.result.scalars.filter(s => runs.every(r => Number.isFinite(r[s.sym]))).map(s => {
    const [a, b, d] = runs.map(r => r[s.sym]);
    if (Math.abs(b - d) < 1e-14 * Math.max(1, Math.abs(d))) return { ...s, vals: [a, b, d], order: null, converged: true, gci: 0, extrap: d };
    const o = N.observedOrder(a, b, d, 2);
    return { ...s, vals: [a, b, d], order: o.order, gci: o.gci, extrap: o.extrapolated, converged: Number.isFinite(o.order) && o.order > 0.3 };
  });
  return { key, levels, rows, name: i.name };
}

/** Constrained optimisation of a scalar output over chosen inputs (Nelder–Mead inside the declared ranges). */
export function optimise(c, spec) {
  const model = c.model; const o = spec || (model && model.optimise); if (!model || !o) return null;
  const vars = o.vars.map(s => c.inputs.find(i => i.sym === s)).filter(Boolean); if (!vars.length) return null;
  const sgn = o.sense === 'max' ? -1 : 1;
  const f = x => { const v = { ...c.v }; vars.forEach((i, k) => { v[i.sym] = x[k]; }); const r = runModel(model, v, c.a, true); const s = r.scalars.find(q => q.sym === o.objective); if (!s || !Number.isFinite(s.value)) return 1e300; let pen = 0; (o.constraints || []).forEach(k => { const cs = r.scalars.find(q => q.sym === k.sym); if (cs) { const g = k.max != null ? cs.value - k.max : k.min - cs.value; if (g > 0) pen += 1e6 * (g / (Math.abs(k.max ?? k.min) || 1)) ** 2 * Math.abs(s.value || 1); } }); return sgn * s.value + pen; };
  const x0 = vars.map(i => i.si), lo = vars.map(i => i.rangeSI[0]), hi = vars.map(i => i.rangeSI[1]);
  const res = N.nelderMead(f, x0, { lo, hi, maxIt: model.heavy ? 60 : 250, scale: vars.map(i => (i.rangeSI[1] - i.rangeSI[0]) * 0.08) });
  const vOpt = { ...c.v }; vars.forEach((i, k) => { vOpt[i.sym] = res.x[k]; });
  const rOpt = runModel(model, vOpt, c.a), sBase = c.result.scalars.find(q => q.sym === o.objective), sOpt = rOpt.scalars.find(q => q.sym === o.objective);
  return { spec: o, vars: vars.map((i, k) => ({ sym: i.sym, name: i.name, unit: i.unit, from: i.si, to: res.x[k], atBound: Math.abs(res.x[k] - lo[k]) < 1e-9 * Math.abs(hi[k] - lo[k]) || Math.abs(res.x[k] - hi[k]) < 1e-9 * Math.abs(hi[k] - lo[k]) })), objective: sBase, before: sBase?.value, after: sOpt?.value, history: res.history.map(h => sgn * h), iterations: res.iterations, result: rOpt };
}

/** Lean source for the active world. */
export function leanSource(inv, c) {
  const logic = c.logic ? { premises: inv.logic.premises, conclusion: inv.logic.conclusion, status: c.logic.status, counter: c.logic.counter } : null;
  const ver = c.verification ? { records: [...c.verification.records, ...(c.customVerification ? c.customVerification.records : [])] } : (c.customVerification || null);
  return generateLean(inv.title, ver, c.customTable || c.table, logic, { id: inv.id });
}

// ---------------------------------------------------------------- world and history management
export function addWorld(inv, name, kind = 'alternative', from = inv.activeWorld) {
  const src = inv.worlds.find(w => w.id === from) || inv.worlds[0];
  const w = { id: 'w' + uid(), name: name || `World ${inv.worlds.length + 1}`, kind, inputs: JSON.parse(JSON.stringify(src === inv.worlds[0] ? {} : src.inputs)), assumptions: { ...(src === inv.worlds[0] ? {} : src.assumptions) }, note: '', parent: src.id };
  inv.worlds.push(w); inv.activeWorld = w.id; log(inv, `World “${w.name}” branched from “${src.name}”`);
  return w;
}
export function setInput(inv, worldId, sym, value, unit, prov) {
  const w = inv.worlds.find(x => x.id === worldId), model = modelById(inv.modelId), d = defaults(model).find(i => i.sym === sym);
  if (value === null || value === '' || Number.isNaN(value)) { delete w.inputs[sym]; log(inv, `${d.name} reset to its software-supplied value in “${w.name}”`); touch(inv); return; }
  const si = toSI(value, unit || d.unit);
  w.inputs[sym] = { si, unit: unit || d.unit, prov: prov || (d.kind === 'hypothetical' || (w.kind === 'counterfactual' && d.kind === 'constant') ? 'HYPOTHETICAL' : 'USER'), note: prov === 'UPLOAD' ? 'From an uploaded file' : 'Entered by you' };
  log(inv, `${d.name} set to ${fmt(value)} ${unit || d.unit} in “${w.name}”`); touch(inv);
}
export function setAssumption(inv, worldId, id, on) {
  const w = inv.worlds.find(x => x.id === worldId); w.assumptions[id] = on;
  const a = (modelById(inv.modelId).assumptions || []).find(x => x.id === id);
  log(inv, `Assumption ${on ? 'restored' : 'removed'} in “${w.name}”: ${a ? a.text : id}`); touch(inv);
}
export function snapshot(inv, note) {
  inv.versions.push({ id: uid(), ts: Date.now(), note: note || `Version ${inv.versions.length + 1}`, state: JSON.stringify({ worlds: inv.worlds, activeWorld: inv.activeWorld, modelId: inv.modelId, logic: inv.logic, custom: inv.custom, prompt: inv.prompt }) });
  log(inv, `Version saved: ${note || inv.versions.length}`);
}
export function restore(inv, versionId) {
  const v = inv.versions.find(x => x.id === versionId); if (!v) return;
  Object.assign(inv, JSON.parse(v.state)); log(inv, `Restored version “${v.note}”`); touch(inv);
}
export const log = (inv, action) => { inv.audit.push({ ts: Date.now(), action }); if (inv.audit.length > 400) inv.audit.splice(0, inv.audit.length - 400); };
export const touch = inv => { inv.updated = Date.now(); };
export function selectModel(inv, modelId) {
  inv.modelId = modelId; inv.worlds.forEach(w => { w.inputs = {}; w.assumptions = {}; });
  const model = modelById(modelId);
  inv.klass = P.classifyClass(inv.prompt, model); applyPrompt(inv);
  log(inv, model ? `Model selected: ${model.title}` : 'Model cleared'); touch(inv); clearCache();
}
export { ENV_KEYS, modelClass };
