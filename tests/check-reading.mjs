// The language-model reading is only ever a proposal. This checks, with canned replies and no network, that whatever a
// model might return is cut down to what can be verified before it touches an investigation.
//   node tests/check-reading.mjs
import { candidates, validate, applyReading } from '../js/engine/reading.js';
import { createInvestigation, compute } from '../js/engine/core.js';

let fails = 0; const ok = (name, cond, extra = '') => { if (!cond) { fails++; console.log(`FAIL  ${name} ${extra}`); } else console.log(`ok    ${name}`); };
const P1 = 'Natural gas at 120 bar flows through a 30 km subsea pipeline 0.25 m in diameter; seabed at 4 °C. Will hydrates form?', cat1 = candidates(P1, 2);
ok('the right model is among the candidates offered', cat1.some(c => c.id === 'hydrate-formation-risk'));
let r = validate({ choice: 'library', id: 'made-up-model', why: 'x', confidence: 1 }, P1, cat1);
ok('an invented catalogue id is refused', r.choice === 'none' && r.dropped.length === 1);
r = validate({ choice: 'library', id: 'hydrate-formation-risk', confidence: 0.9, klass: 'I', values: [{ sym: 'p_in', value: 120, unit: 'bar', quote: '120 bar' }, { sym: 'L', value: 30, unit: 'km', quote: '30 km' }, { sym: 'T_in', value: 80, unit: '°C', quote: 'inlet at 80 °C' }, { sym: 'D', value: 0.25, unit: 'bar', quote: '0.25 m' }, { sym: 'zzz', value: 1, unit: 'm', quote: '30 km' }, { sym: 'T_amb', value: 4, unit: '°C', quote: 'seabed at 4 °C' }] }, P1, cat1);
ok('stated numbers are kept', r.values.map(v => v.sym).join() === 'p_in,L,T_amb', r.values.map(v => v.sym).join());
ok('a number that is not in the prompt is discarded', r.dropped.some(d => /not written in your prompt/.test(d)));
ok('a unit of the wrong kind is discarded', r.dropped.some(d => /unit does not suit/.test(d)));
ok('a symbol that is not an input is discarded', r.dropped.some(d => /not an input/.test(d)));
ok('values are converted to SI', Math.abs(r.values[0].si - 120e5) < 1 && Math.abs(r.values[2].si - 277.15) < 1e-6);
let inv = createInvestigation({ module: 2, prompt: P1 }); const did = applyReading(inv, r), c = compute(inv);
ok('the reading selects the model and the investigation computes', inv.modelId === 'hydrate-formation-risk' && c.result.status === 'computed' && !!did, `${inv.modelId} ${c.result.status}`);
ok('the reading is recorded in the audit trail', inv.audit.some(a => /language-model reading/i.test(a.action)) && inv.reading && inv.reading.choice === 'library');

const P2 = 'A steel ball of mass 0.5 kg falls through glycerine. Drag is proportional to speed with coefficient 2 N s/m. What terminal speed does it reach?', cat2 = candidates(P2, 2);
r = validate({ choice: 'equations', id: null, confidence: 0.8, klass: 'I', equations: [{ name: 'Terminal speed', lhs: 'v_term', rhs: 'm*g/k' }, { name: 'Duplicate', lhs: 'v_term', rhs: 'm*g' }, { name: 'Broken', lhs: 'F', rhs: 'm*(g' }, { name: 'Undeclared', lhs: 'W', rhs: 'm*g*h' }], symbols: [{ sym: 'm', name: 'Mass', unit: 'kg', value: 1 }, { sym: 'g', name: 'Gravity', unit: 'm/s^2', value: 9.81 }, { sym: 'k', name: 'Drag coefficient', unit: 'N s/m', value: 1 }, { sym: 'v_term', name: 'Terminal speed', unit: 'm/s' }, { sym: 'bad', name: 'x', unit: 'flurbs' }], values: [{ sym: 'm', value: 0.5, unit: 'kg', quote: 'mass 0.5 kg' }, { sym: 'k', value: 2, unit: 'N s/m', quote: 'coefficient 2 N s/m' }, { sym: 'g', value: 3.7, unit: 'm/s^2', quote: 'on Mars' }] }, P2, cat2);
ok('only readable, single, fully declared equations survive', r.choice === 'equations' && r.equations.length === 1 && r.equations[0].rhs === 'm*g/k', JSON.stringify(r.equations));
ok('stated values replace typical ones, unstated ones do not', r.symbols.m.value === 0.5 && r.symbols.k.value === 2 && r.symbols.g.value === 9.81);
inv = createInvestigation({ module: 2, prompt: P2 }); applyReading(inv, r); const c2 = compute(inv), vt = c2.result.scalars.find(s => s.sym === 'v_term');
ok('the proposed equation is solved by the engine: v = m g / k', c2.result.status === 'computed' && vt && Math.abs(vt.value - 0.5 * 9.81 / 2) < 1e-9, vt && vt.value);
ok('proposed equations are flagged as a hypothesis to confirm', inv.match && inv.match.confidence === 'low' && /language model/.test(inv.match.note));
ok('each proposed equation goes through dimensional verification', c2.customVerification.records.length === 1 && ['verified', 'conditional'].includes(c2.customVerification.records[0].status), c2.customVerification.records.map(q => q.status).join());
r = validate({ choice: 'equations', equations: [{ name: 'Nonsense', lhs: 'v_term', rhs: 'm + g' }], symbols: [{ sym: 'm', name: 'Mass', unit: 'kg', value: 1 }, { sym: 'g', name: 'Gravity', unit: 'm/s^2', value: 9.81 }, { sym: 'v_term', name: 'Speed', unit: 'm/s' }] }, P2, cat2);
inv = createInvestigation({ module: 2, prompt: P2 }); applyReading(inv, r); const c3 = compute(inv);
ok('a dimensionally inconsistent proposal is caught by the verifier, not trusted', c3.customVerification.records[0] && c3.customVerification.records[0].status === 'inconsistent', c3.customVerification.records.map(q => q.status).join());
r = validate({ choice: 'none', why: 'A logical argument', confidence: 1, klass: 'II' }, 'If A then B. A. Therefore B.', []);
inv = createInvestigation({ module: 1, prompt: 'If A then B. A. Therefore B.' }); ok('"none" changes nothing', applyReading(inv, r) === null && !inv.reading);
let threw = false; try { validate(JSON.parse('{"choice":"atlas","id":5,"values":"x","equations":{}}'), P1, cat1); } catch { threw = true; } ok('malformed fields do not throw', !threw);
console.log(`\n${fails} failing`); process.exit(fails ? 1 : 0);
