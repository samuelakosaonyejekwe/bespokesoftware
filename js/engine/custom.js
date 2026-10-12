// Builds a computable model from the user's own equations (typed, pasted, discovered, or read
// from the prompt). Explicit relations are evaluated in dependency order; equations of the form
// d(x,t) = f are integrated in time. Rates of change pass through a smooth cap, so that no
// solution can reach infinity in finite time.
import * as E from '../core/expr.js';
import * as N from '../core/num.js';
import { tryUnit, fmt } from '../core/units.js';
import { DOMAINS } from '../data/domains.js';
import { ATLAS } from '../data/atlas.js';

const K = {}; // no symbol is assumed to be a constant of nature: in a user's equation, c or g may mean anything

export function customModel(inv) {
  const eqs = (inv.custom && inv.custom.equations) || []; if (!eqs.length) return null;
  const parsed = eqs.map((q, i) => { try { return { q, i, L: E.parse(q.lhs), R: E.parse(q.rhs) }; } catch { return null; } }).filter(Boolean);
  const odes = parsed.filter(p => p.L.t === 'fn' && p.L.n === 'd' && p.L.args[0].t === 'sym' && p.L.args[1] && p.L.args[1].t === 'sym' && !E.hasDiffOps(p.R));
  const alg = parsed.filter(p => p.L.t === 'sym' && !E.hasDiffOps(p.R));
  if (!odes.length && !alg.length) return null;
  const states = odes.map(o => o.L.args[0].n), tVar = odes.length ? odes[0].L.args[1].n : null, defined = new Set(alg.map(p => p.L.n));
  const free = new Set(); [...odes, ...alg].forEach(p => E.symbols(p.R).forEach(s => { if (!defined.has(s) && s !== tVar && !states.includes(s)) free.add(s); }));
  const S = inv.custom.symbols || {};
  const unitOf = s => ((S[s] && S[s].unit && tryUnit(S[s].unit)) ? S[s].unit : '1');
  const mk = (sym, name) => {
    const d = S[sym] || {}, known = K[sym] != null && !d.unit, value = d.value != null ? d.value : known ? K[sym] : 1;
    if (d.src) return { sym, name: d.name || name, unit: unitOf(sym), value, min: d.min != null ? d.min : value, max: d.max != null ? d.max : value, kind: d.min != null && d.min === d.max ? 'constant' : 'operating', unc: d.min != null && d.min === d.max ? 0 : 0.05, placeholder: false, src: d.src, prov: d.prov, aliases: d.aliases };
    return { sym, name: d.name || name, unit: unitOf(sym), value, min: d.min != null ? d.min : value > 0 ? value / 10 : value < 0 ? value * 10 : -1, max: d.max != null ? d.max : value > 0 ? value * 10 : value < 0 ? value / 10 : 1, kind: 'operating', unc: 0.05, placeholder: d.value == null && !known, src: d.value != null ? 'Value you declared for your equation' : known ? 'Accepted constant' : 'Placeholder of 1: set the real value' };
  };
  const inputs = [...free].map(s => mk(s, `Symbol ${s}`)).concat(states.map(s => mk(s, `Initial value of ${s}`)));
  if (odes.length) {
    inputs.push({ sym: 't_end', name: 'Duration of the simulation', unit: unitOf(tVar), value: (S[tVar] && S[tVar].max) || 10, min: 1e-9, max: 1e12, kind: 'numerical', src: 'Simulation horizon' });
    inputs.push({ sym: 'rate_cap', name: 'Cap on any rate of change', unit: '1', value: 1e9, min: 1, max: 1e30, kind: 'numerical', src: 'Smooth saturation that rules out finite-time blow-up' });
  }
  const order = [];
  { const known = new Set([...free, ...states, tVar].filter(Boolean)); let prog = true; while (prog) { prog = false; for (const p of alg) if (!p.done && [...E.symbols(p.R)].every(s => known.has(s))) { order.push(p); known.add(p.L.n); p.done = true; prog = true; } } }
  const evalAlg = env => { for (const p of order) { try { env[p.L.n] = E.evaluate(p.R, env); } catch { env[p.L.n] = NaN; } } return env; };
  const domains = (inv.domains || []).map(d => d.key).filter(k => DOMAINS[k]).slice(0, 2);
  const at = inv.atlas ? ATLAS.find(x => x.id === inv.atlas) : null;
  return {
    id: at ? `atlas:${at.id}` : 'custom', custom: true, atlas: !!at, title: at ? at.title : inv.estimate ? 'Order-of-magnitude estimate by dimensional analysis' : 'Your own equations', module: [1, 2], klass: !at && inv.klass && inv.klass.tags.includes('III') ? ['III', 'I'] : ['I'], hypothetical: !at,
    domains: domains.length ? domains : ['classical'], keywords: [],
    summary: at ? at.summary : 'A model assembled from the equations you supplied. Explicit relations are evaluated in order and time-dependent ones are integrated numerically.',
    background: at ? `${at.summary} These are standard textbook relations, assembled into a small model because no full model in the library covers the question. Every reference value can be replaced with your own.` : 'These equations are yours. They are treated as hypotheses: verified for syntax, dimensions and finiteness, solved as written, and given no standing beyond the evidence you bring to them.',
    laws: at ? at.laws || [] : [], refs: at ? ['Standard relations found in any university physics text, for example Halliday, Resnick & Walker, Fundamentals of Physics (Wiley).'] : [], limits: at ? at.limits || 'A compact textbook relation: it captures the leading effect only.' : 'Valid only as far as the supplied equations are. Symbols without a declared value run with a placeholder of 1.',
    inputs,
    symbols: Object.fromEntries([...defined].map(s => [s, [(S[s] && S[s].name) || `Symbol ${s}`, unitOf(s)]]).concat(tVar ? [[tVar, ['Time', unitOf(tVar)]]] : [])),
    assumptions: odes.length ? [{ id: 'saturate', text: 'Every rate of change is passed through a smooth cap f → f / √(1 + f²/F²), so no variable can reach infinity in finite time.', on: true, why: 'Guarantees a solution that exists and stays finite for all time', alt: 'Rates are used exactly as written; a solution that blows up is then reported as such.' }] : [],
    equations: () => parsed.map(p => ({ id: `user${p.i + 1}`, name: p.q.name || `Your equation ${p.i + 1}`, lhs: p.q.lhs, rhs: p.q.rhs, kind: p.q.kind || 'hypothesis', origin: p.q.origin || 'Supplied by you' })),
    derivation: () => [],
    numerics: { method: odes.length ? 'Adaptive Runge–Kutta (Dormand–Prince 4/5) with smoothly capped rates; algebraic relations evaluated in dependency order' : 'Direct evaluation in dependency order' },
    falsify: ['Any measurement that departs from the predicted curves by more than its uncertainty.'],
    solve(v, a) {
      const scalars = [], series = [], warnings = [], checks = [];
      const ph = inputs.filter(i => i.placeholder).map(i => i.sym);
      if (ph.length) warnings.push(`No value was declared for ${ph.join(', ')}; a placeholder of 1 is in use. Set real values in the input table.`);
      if (odes.length) {
        const F = v.rate_cap, capped = a.saturate !== false, sat = f => (capped ? f / Math.sqrt(1 + (f / F) * (f / F)) : f);
        let peak = 0;
        const rhs = (t, y) => {
          const env = { ...v, [tVar]: t }; states.forEach((s, k) => { env[s] = y[k]; }); evalAlg(env);
          return odes.map(o => { let f; try { f = E.evaluate(o.R, env); } catch { f = NaN; } if (!Number.isFinite(f)) { if (!capped) return f; f = f < 0 ? -F * 1e3 : F * 1e3; } peak = Math.max(peak, Math.abs(f)); return sat(f); });
        };
        const sol = N.rk45(rhs, states.map(s => v[s]), 0, v.t_end, 400, { rtol: 1e-7, atol: 1e-10, maxSteps: 60000 });
        const done = sol.t.length && sol.t[sol.t.length - 1] >= v.t_end * (1 - 1e-6), blew = sol.blewUp || !done;
        states.forEach((s, k) => { const y = sol.y[k]; scalars.push({ sym: `${s}_end`, name: `${s} at the end of the run`, value: y.length ? y[y.length - 1] : NaN, unit: unitOf(s), text: blew ? 'Not reached: the solution diverged first' : undefined }); scalars.push({ sym: `${s}_max`, name: `Largest magnitude of ${s}`, value: y.length ? N.maxOf(y.map(Math.abs)) : NaN, unit: unitOf(s) }); });
        if (sol.t.length > 1) {
          series.push({ id: 'states', title: 'Evolution of the state variables', x: { label: tVar, unit: unitOf(tVar), data: sol.t }, y: states.map((s, k) => ({ label: s, data: sol.y[k] })), yLabel: states.join(', '), yUnit: states.length === 1 ? unitOf(states[0]) : '', kind: 'line' });
          if (states.length >= 2) series.push({ id: 'phase', title: `Phase portrait: ${states[1]} against ${states[0]}`, x: { label: states[0], unit: unitOf(states[0]), data: sol.y[0] }, y: [{ label: states[1], data: sol.y[1] }], yLabel: states[1], yUnit: unitOf(states[1]), kind: 'line' });
        }
        if (blew) warnings.push(`As written, these equations blow up in finite time: the solution stopped being finite near ${tVar} = ${fmt(sol.blowUpTime ?? sol.t[sol.t.length - 1], 4)}. Switch the rate cap on to obtain a solution that exists for all time.`);
        else if (capped && peak > 0.05 * F) warnings.push(`The rate cap was active (peak rate ${fmt(peak, 3)} against a cap of ${fmt(F, 3)}). Without it these equations grow without bound in finite time; the capped solution is finite but is no longer the solution of the equations exactly as written.`);
        checks.push({ name: 'Solution finite over the whole run', value: blew ? 1 : 0, tol: 0, pass: !blew, note: capped ? 'Guaranteed by the rate cap: |dx/dt| ≤ F implies |x(t) − x(0)| ≤ F·t' : 'Rates used exactly as written' });
        scalars.push({ sym: 'rate_peak', name: 'Largest rate of change encountered', value: peak, unit: '1' });
      }
      if (order.length) {
        const env = evalAlg({ ...v, ...(tVar ? { [tVar]: 0 } : {}) });
        order.forEach(p => scalars.push({ sym: p.L.n, name: (S[p.L.n] && S[p.L.n].name) || `Computed ${p.L.n}`, value: env[p.L.n], unit: unitOf(p.L.n), text: Number.isFinite(env[p.L.n]) ? undefined : 'Not finite at these values' }));
        const xv = inputs.find(i => i.kind !== 'numerical' && !states.includes(i.sym));
        if (xv && !odes.length) {
          const u = tryUnit(xv.unit) || { f: 1, o: 0 }, xs = N.linspace(xv.min * u.f + u.o, xv.max * u.f + u.o, 160);
          order.slice(0, 4).forEach(p => { const ys = xs.map(x => { const e2 = evalAlg({ ...v, [xv.sym]: x }); return Number.isFinite(e2[p.L.n]) ? e2[p.L.n] : NaN; }); if (ys.some(Number.isFinite)) series.push({ id: `sweep-${p.L.n}`, title: `${p.L.n} against ${xv.sym}`, x: { label: xv.sym, unit: xv.unit === '1' ? '' : 'SI', data: xs }, y: [{ label: p.L.n, data: ys }], yLabel: p.L.n, yUnit: unitOf(p.L.n), kind: 'line' }); });
        }
      }
      return { scalars, series, warnings, checks };
    },
  };
}
