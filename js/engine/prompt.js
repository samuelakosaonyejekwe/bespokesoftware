// Prompt understanding: experiment class, scientific domains, candidate models,
// quantities with units, and named locations. Entirely rule- and ontology-based so that it
// runs on-device with no network and gives the same reading of the same prompt every time.
import { DOMAINS, CLASS_CUES } from '../data/domains.js';
import { GAZETTEER, SITES, BODIES, CONSTANTS } from '../data/reference.js';
import { tryUnit, dimEq, isDimless, quantityName, D0 } from '../core/units.js';

const lc = s => String(s || '').toLowerCase();
const count = (text, phrase) => { let n = 0, i = 0; while ((i = text.indexOf(phrase, i)) !== -1) { const b = text[i - 1], a = text[i + phrase.length]; if (!(b && /[a-z0-9]/.test(b)) && !(a && /[a-z0-9]/.test(a) && phrase.length < 5)) n++; i += phrase.length; } return n; };

/** Experiment class scores and the cues that produced them. */
export function classifyClass(prompt, model) {
  const t = lc(prompt), score = { I: 0, II: 0, III: 0 }, cues = { I: [], II: [], III: [] };
  for (const k of ['I', 'II', 'III']) for (const cue of CLASS_CUES[k]) { const n = count(t, cue); if (n) { score[k] += n * (cue.includes(' ') ? 2 : 1); cues[k].push(cue); } }
  if (/\d/.test(t)) { score.I += 1; cues.I.push('numerical values present'); }
  if (model) (Array.isArray(model.klass) ? model.klass : [model.klass]).forEach((k, i) => { score[k] += i === 0 ? 4 : 2; cues[k].push(`matched model "${model.title}"`); });
  const order = Object.keys(score).sort((a, b) => score[b] - score[a]);
  const top = score[order[0]] || 0;
  const tags = order.filter(k => score[k] > 0 && score[k] >= Math.max(1, 0.45 * top));
  if (!tags.length) tags.push(model ? (Array.isArray(model.klass) ? model.klass[0] : model.klass) : 'I');
  return { primary: tags[0], tags, hybrid: tags.length > 1, score, cues };
}
export const CLASS_NAME = { I: 'Scientifically computable', II: 'Logically analysable', III: 'Speculative / counterfactual' };
export const CLASS_BLURB = {
  I: 'Described by explicit equations with justified inputs; produces numerical predictions that are only as reliable as the equations, data and validation behind them.',
  II: 'Built from propositions, definitions and inference; produces deductions, proofs, countermodels and conditional conclusions.',
  III: 'Explores invented or modified laws; produces conditional consequences that do not establish that those laws occur in nature.',
};

export function rankDomains(prompt) {
  const t = lc(prompt);
  return Object.entries(DOMAINS).map(([key, d]) => {
    let s = 0; const hits = [];
    d.kw.forEach(k => { const n = count(t, k); if (n) { s += n * (k.includes(' ') ? 3 : 1.5); hits.push(k); } });
    return { key, name: d.name, score: s, hits };
  }).filter(d => d.score > 0).sort((a, b) => b.score - a.score);
}

export function rankModels(prompt, models, module) {
  const t = lc(prompt), doms = rankDomains(prompt), domScore = Object.fromEntries(doms.map(d => [d.key, d.score]));
  return models.filter(m => module === 1 || (Array.isArray(m.module) ? m.module.includes(2) : m.module === 2)).map(m => {
    let s = 0; const hits = [];
    m.keywords.forEach((k, i) => { const n = count(t, k); if (n) { const words = k.split(' ').length; s += (words * words * 3 + 1) * (1 + 0.5 / (i + 1)); hits.push(k); } });
    const ds = m.domains.reduce((a, d, i) => a + (domScore[d] || 0) * (i === 0 ? 0.5 : 0.2), 0);
    const title = lc(m.title).split(/\W+/).filter(w => w.length > 3 && t.includes(w)).length;
    const modBonus = module === 1 && (m.module === 1 || (Array.isArray(m.module) && m.module[0] === 1)) ? 1.15 : 1;
    return { id: m.id, title: m.title, score: (s + ds + title) * modBonus, kw: s, hits };
  }).filter(m => m.kw > 0 || m.score > 2).sort((a, b) => b.score - a.score);
}

// ---------------------------------------------------------------- quantities
const WORD_UNITS = [
  [/\bdegrees?\s*(celsius|centigrade|c)\b/gi, '°C'], [/\bdegrees?\s*(fahrenheit|f)\b/gi, '°F'], [/\bdeg\s*c\b/gi, '°C'], [/\bkelvins?\b/gi, 'K'],
  [/\b(metres|meters|metre|meter)\s+per\s+second\s+squared\b/gi, 'm/s^2'], [/\b(metres|meters|metre|meter)\s+per\s+second\b/gi, 'm/s'],
  [/\b(kilometres|kilometers|kilometre|kilometer)\s+per\s+hour\b/gi, 'kph'], [/\bmiles\s+per\s+hour\b/gi, 'mph'],
  [/\bcubic\s+(metres|meters|metre|meter)\s+per\s+(hour|hr)\b/gi, 'm^3/h'], [/\bcubic\s+(metres|meters|metre|meter)\s+per\s+(second|sec)\b/gi, 'm^3/s'], [/\bcubic\s+(metres|meters|metre|meter)\s+per\s+day\b/gi, 'm^3/d'],
  [/\b(kilograms?|kg)\s+per\s+cubic\s+(metre|meter)\b/gi, 'kg/m^3'], [/\b(kilograms?|kg)\s+per\s+(second|sec)\b/gi, 'kg/s'],
  [/\bbarrels?\s+per\s+day\b/gi, 'bbl/d'], [/\bbpd\b/gi, 'bbl/d'], [/\bcubic\s+(metres|meters|metre|meter)\b/gi, 'm^3'], [/\bsquare\s+(metres|meters|metre|meter)\b/gi, 'm^2'],
  [/\b(kilometres|kilometers|kilometre|kilometer)\b/gi, 'km'], [/\b(millimetres|millimeters|millimetre|millimeter)\b/gi, 'mm'], [/\b(centimetres|centimeters|centimetre|centimeter)\b/gi, 'cm'],
  [/\b(micrometres|micrometers|micrometre|micrometer|microns?)\b/gi, 'um'], [/\b(nanometres|nanometers|nanometre|nanometer)\b/gi, 'nm'], [/\b(metres|meters|metre|meter)\b/gi, 'm'],
  [/\b(inches|inch)\b/gi, 'in'], [/\b(feet|foot)\b/gi, 'ft'], [/\bmiles?\b/gi, 'mi'], [/\blight[- ]years?\b/gi, 'ly'], [/\bastronomical units?\b/gi, 'AU'],
  [/\b(kilograms|kilogram|kilos)\b/gi, 'kg'], [/\b(grams|gram)\b/gi, 'g'], [/\b(tonnes|tonne|metric tons?)\b/gi, 't'], [/\bsolar mass(es)?\b/gi, 'Msun'], [/\bearth mass(es)?\b/gi, 'Mearth'],
  [/\b(seconds|second|secs)\b/gi, 's'], [/\b(milliseconds|millisecond)\b/gi, 'ms'], [/\b(microseconds|microsecond)\b/gi, 'us'], [/\b(nanoseconds|nanosecond)\b/gi, 'ns'],
  [/\b(minutes|minute|mins)\b/gi, 'min'], [/\b(hours|hour|hrs)\b/gi, 'h'], [/\b(days|day)\b/gi, 'd'], [/\b(years|year|yrs)\b/gi, 'yr'],
  [/\b(newtons|newton)\b/gi, 'N'], [/\b(kilonewtons|kilonewton)\b/gi, 'kN'], [/\b(pascals|pascal)\b/gi, 'Pa'], [/\b(megapascals|megapascal)\b/gi, 'MPa'], [/\b(kilopascals|kilopascal)\b/gi, 'kPa'], [/\b(gigapascals|gigapascal)\b/gi, 'GPa'],
  [/\bbars\b/gi, 'bar'], [/\batmospheres?\b/gi, 'atm'], [/\b(joules|joule)\b/gi, 'J'], [/\b(kilojoules|kilojoule)\b/gi, 'kJ'], [/\b(megajoules|megajoule)\b/gi, 'MJ'], [/\belectron[- ]?volts?\b/gi, 'eV'],
  [/\b(watts|watt)\b/gi, 'W'], [/\b(kilowatts|kilowatt)\b/gi, 'kW'], [/\b(megawatts|megawatt)\b/gi, 'MW'], [/\bhorsepower\b/gi, 'hp'],
  [/\b(volts|volt)\b/gi, 'V'], [/\b(kilovolts|kilovolt)\b/gi, 'kV'], [/\b(amperes|ampere|amps|amp)\b/gi, 'A'], [/\b(milliamps?|milliamperes?)\b/gi, 'mA'], [/\b(ohms)\b/gi, 'ohm'], [/\b(farads|farad)\b/gi, 'F'], [/\b(microfarads?)\b/gi, 'uF'],
  [/\b(henries|henry|henrys)\b/gi, 'H'], [/\b(teslas|tesla)\b/gi, 'T'], [/\b(coulombs|coulomb)\b/gi, 'C'],
  [/\b(hertz)\b/gi, 'Hz'], [/\b(kilohertz)\b/gi, 'kHz'], [/\b(megahertz)\b/gi, 'MHz'], [/\b(gigahertz)\b/gi, 'GHz'], [/\b(terahertz)\b/gi, 'THz'],
  [/\b(litres|liters|litre|liter)\b/gi, 'L'], [/\bpercent\b/gi, '%'], [/\b(degrees|degree)\b/gi, 'deg'], [/\bradians?\b/gi, 'rad'], [/\bknots\b/gi, 'kn'], [/\bcentipoise\b/gi, 'cP'],
  [/\bpsi[ag]?\b/gi, m => m.toLowerCase()], [/\bbarg\b/gi, 'barg'], [/\bbara\b/gi, 'bara'], [/\bmoles?\b/gi, 'mol'],
];
const SKIP_AFTER_IN = new Set(['the', 'a', 'an', 'this', 'that', 'each', 'every', 'order', 'total', 'which', 'both', 'all', 'its', 'their', 'our', 'my', 'one', 'two', 'such', 'any', 'some', 'water', 'air', 'vacuum', 'space', 'series', 'parallel', 'steady', 'deep']);
const BAD_UNITS = new Set(['a', 'at', 'as', 'is', 'd', 'h', 't', 'u', 'G', 'P', 'R', 'S', 'F', 'H', 'T', 'D_perm', 'l', 'rev', 'M_conc', 'g0', 'te', 'ha', 'oz', 'sec', 'cal', 'barn', 'kat', 'St', 'Np', 'lx', 'lm', 'sr', 'cd', 'Da', 'pc', 'au', 'Wb', 'ft', 'yd', 'mi', 'R', 'C', 'A', 'J', 'N', 'V', 'W', 'K', 'L', 'g', 's', 'm']);
const SAFE_SINGLE = new Set(['m', 's', 'g', 'K', 'N', 'V', 'W', 'J', 'A', 'L', 'C', 'T', 'F', 'H', 'h', 'd', 't', 'ft', 'mi']); // accepted only when directly attached to a number or clearly a unit context
const MULT = { thousand: 1e3, million: 1e6, billion: 1e9, trillion: 1e12, hundred: 100, dozen: 12 };

/** Find numbers with (optional) units. Returns [{value, unit, si, dim, quantity, start, end, raw}]. */
export function extractQuantities(prompt) {
  let text = String(prompt);
  WORD_UNITS.forEach(([re, rep]) => { text = text.replace(re, m0 => (typeof rep === 'function' ? rep(m0) : rep)); });
  const out = [];
  const reNum = /(?<![A-Za-z_\d.])([-−–]?\d{1,3}(?:,\d{3})+(?:\.\d+)?|[-−–]?\d+\.?\d*(?:[eE][-+]?\d+)?|[-−–]?\.\d+)(?:\s*(?:×|x|\*)\s*10\s*\^?\s*([-−]?\d+))?/g;
  let m;
  while ((m = reNum.exec(text))) {
    let value = parseFloat(m[1].replace(/,/g, '').replace(/[−–]/g, '-'));
    // a leading dash right after a word is a hyphen or range, not a minus sign
    if (/^[-−–]/.test(m[1]) && /[A-Za-z0-9]$/.test(text.slice(0, m.index).trimEnd()) && !/[=(,:]\s*$/.test(text.slice(0, m.index))) value = Math.abs(value);
    if (m[2]) value *= Math.pow(10, parseInt(m[2].replace('−', '-'), 10));
    let end = m.index + m[0].length;
    let rest = text.slice(end);
    const mm = /^\s*(thousand|million|billion|trillion|hundred|dozen)\b/i.exec(rest);
    if (mm) { value *= MULT[mm[1].toLowerCase()]; end += mm[0].length; rest = text.slice(end); }
    // fraction of light speed: "0.8c", "0.8 c", "80% of the speed of light"
    const mc = /^\s?c\b(?!\w)/.exec(rest), mcp = /^\s*%\s*(?:of\s+)?(?:the\s+)?speed of light/i.exec(rest), mct = /^\s*(?:times\s+)?(?:the\s+)?speed of light/i.exec(rest);
    if ((mc && value < 10 && !/^\s?c\w/.test(rest)) || mcp || mct) {
      const frac = mcp ? value / 100 : value, len = (mc || mcp || mct)[0].length;
      out.push({ value: frac, unit: 'c', si: frac * CONSTANTS.c.value, dim: [0, 1, -1, 0, 0, 0, 0], quantity: 'velocity (fraction of light speed)', start: m.index, end: end + len, raw: text.slice(m.index, end + len), lightFraction: frac });
      reNum.lastIndex = end + len; continue;
    }
    const attached = !/^\s/.test(rest);
    const mu = /^\s{0,2}([A-Za-zµμΩ°%"][A-Za-z0-9µμΩ°%"^/.·*()\-]{0,14})/.exec(rest);
    let unit = '', u = null, ulen = 0;
    if (mu) {
      let cand = mu[1].replace(/[.,;:)]+$/, '');
      while (cand.length) {
        const tu = tryUnit(cand);
        if (tu && !/^\d/.test(cand)) {
          const single = !/[/^*·]/.test(cand);
          const after = lc(text.slice(end + mu[0].indexOf(cand) + cand.length).trim().split(/[\s,.;]/)[0]);
          let ok = true;
          if (single && BAD_UNITS.has(cand) && !(SAFE_SINGLE.has(cand) && (attached || /^[\s]*$/.test(after) || !/^[a-z]{3,}$/.test(after) || ['long', 'wide', 'high', 'deep', 'thick', 'pipe', 'pipeline', 'diameter', 'tall', 'apart', 'away', 'above', 'below', 'per', 'of', 'and', 'at', 'in', 'to', 'for', 'from', 'with', 'by', 'is', 'on'].includes(after)))) ok = false;
          if (cand === 'in' && SKIP_AFTER_IN.has(after)) ok = false;
          if (cand === 'm' && /^(?:illion|ore|any)/.test(after)) ok = false;
          if (ok) { unit = cand; u = tu; ulen = mu[0].indexOf(cand) + cand.length; }
          break;
        }
        cand = cand.slice(0, -1);
      }
    }
    const si = u ? value * u.f + u.o : value;
    out.push({ value, unit, si, dim: u ? u.dim : D0, quantity: u ? quantityName(u.dim) : 'number', start: m.index, end: end + ulen, raw: text.slice(m.index, end + ulen).trim(), bare: !u });
    reNum.lastIndex = end + ulen;
  }
  return { text, items: out };
}

/** Assign extracted quantities to a model's inputs by dimension, nearby wording and plausibility of magnitude. */
export function mapQuantities(extracted, inputs) {
  const { text, items } = extracted, t = lc(text), used = new Set(), mapped = [];
  const cands = items.map((q, qi) => {
    const before = t.slice(Math.max(0, q.start - 70), q.start), after = t.slice(q.end, q.end + 45);
    const scores = inputs.map(inp => {
      const u = tryUnit(inp.unit);
      if (!u) return -Infinity;
      if (q.bare) { if (!isDimless(u.dim)) return -Infinity; }
      else if (!dimEq(u.dim, q.dim)) return -Infinity;
      if (inp.kind === 'numerical' || inp.kind === 'constant') return -Infinity;
      let s = 0, hit = false;
      const names = [...(inp.aliases || []), lc(inp.name)];
      for (const a of names) {
        const ib = before.lastIndexOf(a), ia = after.indexOf(a);
        if (ib !== -1) { s = Math.max(s, 6 - (before.length - ib - a.length) / 14 + a.length / 8); hit = true; }
        if (ia !== -1) { s = Math.max(s, 5 - ia / 10 + a.length / 8); hit = true; }
      }
      // plausibility: closeness of magnitude to the reference value and inside the declared range
      const ref = Math.abs(inp.si), val = Math.abs(q.si);
      if (ref > 0 && val > 0) s += Math.max(0, 2 - Math.abs(Math.log10(val / ref)));
      if (inp.rangeSI && (q.si < inp.rangeSI[0] * 0.5 || q.si > inp.rangeSI[1] * 2)) s -= 4;
      if (q.bare && !hit) return -Infinity; // bare numbers need wording to anchor them
      return s;
    });
    return { qi, scores };
  });
  // greedy assignment, best score first
  const pairs = [];
  cands.forEach(c => c.scores.forEach((s, ii) => { if (s > -Infinity) pairs.push({ qi: c.qi, ii, s }); }));
  pairs.sort((a, b) => b.s - a.s);
  const qUsed = new Set();
  for (const p of pairs) {
    if (qUsed.has(p.qi) || used.has(p.ii) || p.s < 0.6) continue;
    const sameDim = inputs.filter(i => { const u = tryUnit(i.unit); return u && dimEq(u.dim, items[p.qi].dim) && i.kind !== 'numerical' && i.kind !== 'constant'; }).length;
    if (sameDim > 1 && p.s < 1.2) continue;
    qUsed.add(p.qi); used.add(p.ii);
    mapped.push({ q: items[p.qi], sym: inputs[p.ii].sym, confidence: Math.min(1, p.s / 6) });
  }
  return { mapped, unmapped: items.filter((_, i) => !qUsed.has(i)) };
}

// ---------------------------------------------------------------- places and bodies
export function locate(prompt) {
  const t = lc(prompt);
  const mll = /(-?\d{1,2}(?:\.\d+)?)\s*°?\s*([ns])\b[\s,]+(-?\d{1,3}(?:\.\d+)?)\s*°?\s*([ew])\b/i.exec(prompt) || /lat(?:itude)?\s*[:=]?\s*(-?\d{1,2}(?:\.\d+)?)()[\s,;]+lon(?:gitude)?\s*[:=]?\s*(-?\d{1,3}(?:\.\d+)?)()/i.exec(prompt);
  if (mll) {
    const lat = parseFloat(mll[1]) * (lc(mll[2]) === 's' ? -1 : 1), lon = parseFloat(mll[3]) * (lc(mll[4]) === 'w' ? -1 : 1);
    return { name: `${lat.toFixed(3)}°, ${lon.toFixed(3)}°`, lat, lon, source: 'Coordinates given in the prompt', marine: true };
  }
  let best = null;
  for (const g of GAZETTEER) for (const k of g.kw) { const i = t.indexOf(k); if (i !== -1 && (!best || k.length > best.k.length)) best = { g, k }; }
  if (best) return { ...best.g, source: 'Built-in gazetteer', marine: true, matched: best.k };
  for (const s of SITES) { const k = lc(s.name.split(',')[0].split('(')[0]).trim(); if (k.length > 3 && t.includes(k)) return { ...s, source: 'Built-in gazetteer', marine: false, matched: k }; }
  return null;
}
export function celestial(prompt) {
  const t = lc(prompt);
  return Object.entries(BODIES).filter(([k, b]) => new RegExp(`\\b${k}\\b`).test(t) || t.includes(lc(b.name) + "'s")).map(([k, b]) => ({ key: k, ...b }));
}

/** Short title for an investigation from the first clause of its prompt. */
export function titleFrom(prompt) {
  const s = String(prompt).trim().replace(/\s+/g, ' ');
  const first = s.split(/(?<=[.?!])\s/)[0];
  return (first.length > 72 ? first.slice(0, 69).replace(/\s+\S*$/, '') + '…' : first) || 'Untitled investigation';
}
