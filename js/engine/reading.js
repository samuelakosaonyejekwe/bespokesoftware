// Optional reading of a prompt by a language model. The model only proposes: which catalogue entry fits, which stated
// numbers belong to which inputs, or which equations describe the system. Everything it returns is checked here before
// use — identifiers against the catalogue, numbers against the wording of the prompt, units against the inputs they are
// meant for, equations against the expression grammar — and whatever survives is labelled as a language-model reading
// and then verified by the same dimensional, numerical and proof checks as anything else.
import { MODELS, modelById } from '../models/index.js';
import { ATLAS } from '../data/atlas.js';
import * as P from './prompt.js';
import * as E from '../core/expr.js';
import { tryUnit, dimEq, fromSI } from '../core/units.js';
import { defaults, selectModel, useAtlas, clearCache } from './core.js';
import { SYSTEM } from './reading-prompt.js';

export const ENDPOINT = 'https://bespokesoftware.pages.dev/api/read';
const ATLAS_INDEX = ATLAS.map(a => ({ id: a.id, title: a.title, keywords: a.kw, summary: a.summary, background: '', phenomena: [], inputs: Object.values(a.sym).map(v => ({ name: v[0] })), module: [1, 2], klass: 'I', domains: [] }));
const clip = (t, n) => { t = String(t || '').replace(/\s+/g, ' ').trim(); return t.length > n ? t.slice(0, n - 1) + '…' : t; };

/** The catalogue entries most likely to be relevant, described compactly for the language model. */
export function candidates(prompt, module) {
  const lib = P.rankModels(prompt, MODELS, module).slice(0, 10).map(r => modelById(r.id)).filter(Boolean);
  const atl = P.rankModels(prompt, ATLAS_INDEX, 1).slice(0, 5).map(r => ATLAS.find(a => a.id === r.id)).filter(Boolean);
  return [
    ...lib.map(m => ({ kind: 'library', id: m.id, title: m.title, about: clip(m.summary, 160), inputs: m.inputs.filter(i => i.kind !== 'numerical' && i.kind !== 'constant').slice(0, 14).map(i => [i.sym, clip(i.name, 48), i.unit]) })),
    ...atl.map(a => ({ kind: 'atlas', id: a.id, title: a.title, about: clip(a.summary, 200), inputs: Object.entries(a.sym).filter(([, v]) => v.length > 2 && v[3] !== v[4]).map(([k, v]) => [k, clip(v[0], 60), v[1]]) })),
  ];
}

/** Ask a language model to read the prompt. opts.key (the user's own key) goes straight to the provider from this device; otherwise the project's server function is used. */
export async function askModel(prompt, module, opts = {}) {
  const cat = candidates(prompt, module);
  const once = async feedback => {
    const ctl = new AbortController(), timer = setTimeout(() => ctl.abort(), opts.timeout || 45000), note = feedback ? `\n\nYour previous answer was rejected for these reasons; correct them:\n${feedback}` : '';
    try {
      if (opts.key) {
        const model = opts.model || 'claude-sonnet-5-5';
        const r = await fetch('https://api.anthropic.com/v1/messages', { method: 'POST', signal: ctl.signal, headers: { 'content-type': 'application/json', 'x-api-key': opts.key, 'anthropic-version': '2023-06-01', 'anthropic-dangerous-direct-browser-access': 'true' }, body: JSON.stringify({ model, max_tokens: 1400, system: SYSTEM, messages: [{ role: 'user', content: `CATALOGUE:\n${JSON.stringify(cat)}\n\nQUESTION:\n${prompt}${note}` }] }) });
        const j = await r.json().catch(() => ({})); if (!r.ok) throw new Error((j.error && j.error.message) || `The provider answered ${r.status}`);
        return { text: (j.content || []).filter(b => b.type === 'text').map(b => b.text).join(''), provider: `your own key (${model})` };
      }
      const r = await fetch(opts.endpoint || ENDPOINT, { method: 'POST', signal: ctl.signal, headers: { 'content-type': 'application/json' }, body: JSON.stringify({ prompt, candidates: cat, feedback }) });
      const j = await r.json().catch(() => ({})); if (!r.ok || j.error) throw new Error(j.error || `The reading service answered ${r.status}`);
      return { text: j.text, provider: `the project's reading service (${String(j.model || '').split('/').pop()})` };
    } finally { clearTimeout(timer); }
  };
  const read = async feedback => { const a = await once(feedback); try { return validate(parseJson(a.text), prompt, cat, a.provider); } catch (e) { return { choice: 'none', values: [], equations: [], symbols: {}, dropped: [e.message], provider: a.provider, unreadable: true }; } };
  let rd = await read('');
  // an answer that was attempted but could not be checked gets one chance to be corrected, with the reasons
  if (rd.choice === 'none' && rd.dropped.length) { const second = await read(rd.dropped.slice(0, 5).join('\n')); if (second.choice !== 'none' || !second.unreadable) rd = second; }
  if (rd.unreadable) throw new Error(rd.dropped[0]);
  return rd;
}
function parseJson(text) {
  const t = String(text || ''), a = t.indexOf('{'), b = t.lastIndexOf('}'); if (a < 0 || b <= a) throw new Error('The language model did not return a structured answer');
  try { return JSON.parse(t.slice(a, b + 1)); } catch { throw new Error('The language model returned an answer that could not be parsed'); }
}
const digits = s => String(s).replace(/[,\s]/g, '');
/** True when the number is written in the prompt: the quoted words occur there and contain it. */
function stated(prompt, value, quote) {
  const q = String(quote || '').trim(); if (!q || !Number.isFinite(value)) return false;
  if (!prompt.toLowerCase().includes(q.toLowerCase())) return false;
  const nums = (digits(q).match(/-?\d+\.?\d*(?:[eE][-+]?\d+)?/g) || []).map(Number);
  // the number itself, or the same number after a change of unit prefix (2 kW given as 2000 W)
  return nums.some(n => n !== 0 && [0, 3, -3, 6, -6, 9, -9, 2, -2].some(k => Math.abs(Math.abs(n) * 10 ** k - Math.abs(value)) <= 1e-9 * Math.abs(value))) || (value === 0 && nums.includes(0));
}

/** Keep only what can be checked. Returns { choice, id, title, why, confidence, klass, values, equations, symbols, dropped, provider }. */
export function validate(raw, prompt, cat, provider = '') {
  const out = { choice: 'none', id: null, title: '', why: clip(raw.why, 260), confidence: Math.min(1, Math.max(0, Number(raw.confidence) || 0)), klass: ['I', 'II', 'III'].includes(raw.klass) ? raw.klass : null, values: [], equations: [], symbols: {}, dropped: [], provider };
  const choice = String(raw.choice || '').toLowerCase(), entry = cat.find(c => c.id === raw.id && c.kind === choice);
  if ((choice === 'library' || choice === 'atlas') && !entry) { out.dropped.push(`It named a catalogue entry that does not exist (“${clip(raw.id, 40)}”).`); return out; }
  if (choice === 'library' || choice === 'atlas') {
    out.choice = choice; out.id = entry.id; out.title = entry.title;
    for (const v of Array.isArray(raw.values) ? raw.values.slice(0, 24) : []) {
      const inp = entry.inputs.find(i => i[0] === v.sym), val = Number(v.value), u = tryUnit(String(v.unit || '1')), ui = inp && tryUnit(inp[2]);
      if (!inp) { out.dropped.push(`A value for “${clip(v.sym, 20)}”, which is not an input of this model.`); continue; }
      if (!stated(prompt, val, v.quote)) { out.dropped.push(`${inp[1]} = ${v.value} ${v.unit || ''}: that number is not written in your prompt.`); continue; }
      // a volume of water given for a mass of water: one kilogram per litre
      const vol = tryUnit('m^3'), mass = tryUnit('kg');
      if (u && ui && dimEq(u.dim, vol.dim) && dimEq(ui.dim, mass.dim) && /water/i.test(`${v.quote} ${inp[1]}`)) { out.values.push({ sym: inp[0], name: inp[1], value: val, unit: String(v.unit), si: val * u.f * 1000, quote: `${clip(v.quote, 100)} (taken as 1 kg per litre)` }); continue; }
      if (!u || !ui || !dimEq(u.dim, ui.dim)) { out.dropped.push(`${inp[1]} = ${v.value} ${v.unit || ''}: the unit does not suit this input (${inp[2]}).`); continue; }
      out.values.push({ sym: inp[0], name: inp[1], value: val, unit: String(v.unit || '1'), si: val * u.f + (u.o || 0), quote: clip(v.quote, 120) });
    }
    return out;
  }
  if (choice !== 'equations') return out;
  const units = {};
  for (const s of Array.isArray(raw.symbols) ? raw.symbols.slice(0, 40) : []) { const k = String(s.sym || ''); if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(k) || k === 't' || k === 'pi') continue; const u = tryUnit(String(s.unit || '1')); if (!u) { out.dropped.push(`Symbol ${k}: the unit “${clip(s.unit, 16)}” is not understood.`); continue; } units[k] = { name: clip(s.name || k, 70), unit: String(s.unit || '1'), value: Number.isFinite(Number(s.value)) ? Number(s.value) : undefined }; }
  for (const q of Array.isArray(raw.equations) ? raw.equations.slice(0, 6) : []) {
    if (out.equations.some(x => x.lhs.replace(/\s/g, '') === String(q.lhs).replace(/\s/g, ''))) { out.dropped.push(`“${clip(q.name || q.lhs, 50)}”: a second equation for ${clip(q.lhs, 20)}, which already has one.`); continue; }
    try { const L = E.parse(String(q.lhs)), R = E.parse(String(q.rhs)); const need = [...E.symbols(L), ...E.symbols(R)].filter(k => k !== 'pi' && k !== 't' && !(k in units)); if (need.length) { out.dropped.push(`“${clip(q.name || q.lhs, 50)}”: no unit was given for ${need.slice(0, 4).join(', ')}.`); continue; } out.equations.push({ lhs: String(q.lhs), rhs: String(q.rhs), name: clip(q.name || 'Proposed relation', 80) }); }
    catch (e) { out.dropped.push(`“${clip(q.name || q.lhs, 50)}”: the expression could not be read (${clip(e.message, 60)}).`); }
  }
  if (!out.equations.length) { out.dropped.push('None of the proposed equations could be read.'); return out; }
  const used = new Set(out.equations.flatMap(q => [...E.symbols(E.parse(q.lhs)), ...E.symbols(E.parse(q.rhs))]));
  out.symbols = Object.fromEntries(Object.entries(units).filter(([k]) => used.has(k)));
  // stated values override the typical ones, on the same test as above
  for (const v of Array.isArray(raw.values) ? raw.values.slice(0, 24) : []) { const d = out.symbols[v.sym], val = Number(v.value), u = tryUnit(String(v.unit || '1')), ud = d && tryUnit(d.unit); if (!d) continue; if (!stated(prompt, val, v.quote) || !u || !dimEq(u.dim, ud.dim)) { if (!(d.value !== undefined && Math.abs(val - d.value) <= 1e-9 * Math.abs(val))) out.dropped.push(`${d.name} = ${v.value} ${v.unit || ''}: not written in your prompt in a matching unit.`); continue; } d.value = fromSI(val * u.f + (u.o || 0), d.unit); d.stated = clip(v.quote, 120); }
  out.choice = 'equations';
  return out;
}

/** Apply a validated reading to an investigation created from the same prompt. Returns a one-line account of what changed. */
export function applyReading(inv, rd) {
  if (!rd || rd.choice === 'none') return null;
  const note = t => `Read from your prompt by a language model: “${t}”`;
  let did;
  if (rd.choice === 'library') {
    const model = modelById(rd.id); if (!model) return null;
    const changed = inv.modelId !== rd.id;
    if (changed) { inv.atlas = null; inv.estimate = false; inv.custom = { equations: [], symbols: {} }; selectModel(inv, rd.id); if (model.logicPreset) inv.logic = { ...JSON.parse(JSON.stringify(model.logicPreset)), notes: ['Formal structure taken from the model library. Edit it freely.'] }; }
    delete inv.match;
    const dfl = defaults(model), base = inv.worlds[0];
    rd.values.forEach(v => { const d = dfl.find(i => i.sym === v.sym); if (!d || base.inputs[v.sym]) return; base.inputs[v.sym] = { si: d.integer ? Math.round(v.si) : v.si, unit: d.unit, prov: 'LLM', note: note(v.quote) }; });
    did = changed ? `Model chosen by the language-model reading: ${model.title}` : `Language-model reading agreed with the model already chosen: ${model.title}`;
  } else if (rd.choice === 'atlas') {
    const at = ATLAS.find(a => a.id === rd.id); if (!at) return null;
    inv.modelId = null; inv.estimate = false; inv.worlds.forEach(w => { w.inputs = {}; w.assumptions = {}; }); useAtlas(inv, at, inv.prompt); delete inv.match;
    rd.values.forEach(v => { const d = inv.custom.symbols[v.sym]; if (!d || d.prov === 'USER') return; d.value = fromSI(v.si, d.unit); if (d.min != null) d.min = Math.min(d.min, d.value); if (d.max != null) d.max = Math.max(d.max, d.value); d.src = note(v.quote); d.prov = 'LLM'; });
    did = `Standard relation chosen by the language-model reading: ${at.title}`;
  } else {
    inv.modelId = null; inv.atlas = null; inv.estimate = false; inv.worlds.forEach(w => { w.inputs = {}; w.assumptions = {}; });
    inv.custom = { equations: rd.equations.map(q => ({ lhs: q.lhs, rhs: q.rhs, name: q.name, origin: 'Proposed by a language model from your prompt', kind: rd.klass === 'III' ? 'hypothesis' : 'derived' })), symbols: Object.fromEntries(Object.entries(rd.symbols).map(([k, d]) => [k, { name: d.name, unit: d.unit, ...(d.value !== undefined ? { value: d.value } : {}), src: d.stated ? note(d.stated) : 'Typical value suggested by the language model — replace it with yours', prov: d.stated ? 'LLM' : 'SUPPLIED' }])) };
    inv.match = { confidence: 'low', note: 'These equations were proposed by a language model from your prompt. Treat them as a hypothesis: each is checked below for dimensional consistency and by the proof checker, but nothing yet confirms that they describe the system you meant.' };
    did = `${rd.equations.length} equation(s) proposed by the language-model reading`;
  }
  if (rd.klass && rd.choice !== 'library') inv.klass = P.classifyClass(inv.prompt, { klass: rd.klass, title: rd.title || inv.title });
  inv.reading = { choice: rd.choice, id: rd.id, title: rd.title, why: rd.why, confidence: rd.confidence, provider: rd.provider, values: rd.values.map(v => ({ name: v.name, value: v.value, unit: v.unit, quote: v.quote })), dropped: rd.dropped, at: Date.now() };
  inv.audit.push({ ts: Date.now(), action: did }); clearCache();
  return did;
}
