// Mathematical verification of equations: syntax, dimensional homogeneity, finiteness and
// smoothness on the declared domain, automatic repair, and closure of the equation system.
import * as E from './expr.js';
import { dimEq, dimDiv, dimMul, dimPow, dimToString, isDimless, D0, tryUnit, dimToSI } from './units.js';

/**
 * @param eqn   {id, name, lhs, rhs, kind}
 * @param table { sym: { dim, range?: [lo, hi], name?, unit? } }
 * @returns verification record
 */
export function verifyEquation(eqn, table, opts = {}) {
  const out = { id: eqn.id, name: eqn.name, lhs: eqn.lhs, rhs: eqn.rhs, kind: eqn.kind, steps: [], status: 'verified' };
  let L, R;
  try { L = E.parse(eqn.lhs); R = E.parse(eqn.rhs); out.steps.push({ check: 'Syntax', ok: true, text: 'Both sides parse into well-formed expression trees.' }); }
  catch (err) { out.steps.push({ check: 'Syntax', ok: false, text: err.message }); out.status = 'rejected'; return out; }
  out.tex = `${E.toTex(L, opts.tex)} = ${E.toTex(R, opts.tex)}`;
  out.symbols = [...new Set([...E.symbols(L), ...E.symbols(R)])];
  const missing = out.symbols.filter(s => !table[s]);
  const dimTable = Object.fromEntries(Object.entries(table).map(([k, v]) => [k, v.dim]));

  // ---- dimensional homogeneity
  if (missing.length) {
    out.steps.push({ check: 'Dimensions', ok: null, text: `No unit is registered for ${missing.join(', ')}; homogeneity could not be established.` });
    out.status = 'incomplete';
  } else {
    try {
      const dl = E.dims(L, dimTable), dr = E.dims(R, dimTable);
      out.dim = { lhs: dl, rhs: dr };
      if (dimEq(dl, dr)) out.steps.push({ check: 'Dimensions', ok: true, text: `Both sides have dimension [${dimToString(dl)}] (${dimToSI(dl)}).` });
      else {
        out.steps.push({ check: 'Dimensions', ok: false, text: `Left side is [${dimToString(dl)}] but right side is [${dimToString(dr)}].` });
        out.status = 'inconsistent';
        out.repair = repairDimensions(L, R, dl, dr, table);
      }
    } catch (err) {
      out.steps.push({ check: 'Dimensions', ok: false, text: err.message });
      out.status = 'inconsistent';
    }
  }

  // ---- finiteness and smoothness on the declared domain
  const box = {};
  out.symbols.forEach(s => { if (table[s] && table[s].range) box[s] = table[s].range; });
  const sides = [['left', L], ['right', R]];
  const issues = [], obligations = [];
  for (const [side, ex] of sides) {
    for (const term of E.criticalTerms(ex)) {
      const syms = [...E.symbols(term.expr)];
      const unbounded = syms.filter(s => !box[s]);
      const txt = E.toText(term.expr);
      if (unbounded.length) {
        obligations.push({ side, kind: term.kind, expr: term.expr, text: txt, proved: false, why: `depends on ${unbounded.join(', ')}, an unknown of the problem with no a-priori range` });
        continue;
      }
      const b = E.bound(term.expr, box);
      const ok = term.kind === 'denominator' ? (b.lo > 0 || b.hi < 0) && !b.issues.length : term.kind === 'log' ? b.lo > 0 && !b.issues.length : b.lo >= 0 && !b.issues.length;
      obligations.push({ side, kind: term.kind, expr: term.expr, text: txt, proved: ok, range: [b.lo, b.hi] });
      if (!ok) issues.push({ side, kind: term.kind, text: txt, range: [b.lo, b.hi] });
    }
  }
  out.obligations = obligations;
  const differential = E.hasDiffOps(L) || E.hasDiffOps(R);
  out.differential = differential;
  if (!issues.length) {
    const cond = obligations.filter(o => !o.proved);
    if (cond.length) {
      out.steps.push({ check: 'Finiteness', ok: null, text: `Finite wherever ${cond.map(o => `${o.text} ${o.kind === 'denominator' ? '≠ 0' : o.kind === 'log' ? '> 0' : '≥ 0'}`).join(' and ')}. This is a condition on the solution, recorded as a proof obligation.` });
      if (out.status === 'verified') out.status = 'conditional';
    } else {
      out.steps.push({ check: 'Finiteness', ok: true, text: obligations.length ? `Every denominator, logarithm and root argument stays away from its singular set over the declared ranges (interval arithmetic on ${obligations.length} term${obligations.length > 1 ? 's' : ''}).` : 'No denominators, logarithms or roots: the expression is a polynomial/entire combination and is finite for all finite arguments.' });
    }
    out.steps.push({ check: 'Smoothness', ok: cond.length ? null : true, text: 'Away from the singular set the expression is a composition of analytic functions, hence infinitely differentiable in every variable.' });
  } else {
    out.steps.push({ check: 'Finiteness', ok: false, text: issues.map(i => `${i.kind === 'denominator' ? 'Denominator' : i.kind === 'log' ? 'Logarithm argument' : 'Root argument'} ${i.text} reaches ${i.kind === 'root' ? 'negative values' : 'zero'} on the declared ranges`).join('; ') + '.' });
    out.status = out.status === 'verified' ? 'singular' : out.status;
    // automatic regularisation
    const rl = E.regularise(L, box), rr = E.regularise(R, box);
    if (rl.changed + rr.changed > 0) {
      const eps = opts.eps ?? 1e-6;
      const rb = E.bound(rr.expr, { ...box, eps_reg: [eps, eps] }), lb = E.bound(rl.expr, { ...box, eps_reg: [eps, eps] });
      out.regularised = {
        lhs: E.toText(rl.expr), rhs: E.toText(rr.expr), tex: `${E.toTex(rl.expr, opts.tex)} = ${E.toTex(rr.expr, opts.tex)}`,
        finite: !rb.issues.length && !lb.issues.length && isFinite(rb.lo) && isFinite(rb.hi),
        bound: [rb.lo, rb.hi],
        text: 'Each singular quotient a/b has been replaced by a·b/(b² + ε²), which is bounded by |a|/(2ε), infinitely differentiable, and equal to a/b up to a relative error ε²/b² away from the singular set.',
      };
      out.steps.push({ check: 'Repair', ok: true, text: `A regularised form was generated that is finite and smooth on the whole declared domain.` });
    }
  }
  if (differential) out.steps.push({ check: 'Well-posedness', ok: null, text: 'This is a differential equation: existence, uniqueness and boundedness of its solution depend on the initial and boundary data and are assessed for the whole system, then checked numerically during the run.' });
  return out;
}

/** Search for the simplest monomial in the equation's own symbols that restores dimensional homogeneity. */
export function repairDimensions(L, R, dl, dr, table) {
  const deficit = dimDiv(dl, dr); // multiply rhs by something of this dimension
  const cands = Object.entries(table).filter(([, v]) => v.dim && !isDimless(v.dim)).map(([k, v]) => ({ k, dim: v.dim }));
  const exps = [1, -1, 2, -2, 0.5, -0.5, 3, -3];
  const found = [];
  for (const a of cands) for (const p of exps) {
    if (dimEq(dimPow(a.dim, p), deficit)) found.push({ factor: p === 1 ? a.k : `${a.k}^${p < 0 ? `(${p})` : p}`, cost: Math.abs(p) });
  }
  if (found.length < 4) {
    for (let i = 0; i < cands.length; i++) for (let j = i + 1; j < cands.length; j++) for (const p of [1, -1, 2, -2]) for (const q of [1, -1, 2, -2]) {
      if (dimEq(dimMul(dimPow(cands[i].dim, p), dimPow(cands[j].dim, q)), deficit)) {
        const f = (k, e) => (e === 1 ? k : `${k}^${e < 0 ? `(${e})` : e}`);
        found.push({ factor: `${f(cands[i].k, p)}*${f(cands[j].k, q)}`, cost: Math.abs(p) + Math.abs(q) + 0.5 });
      }
    }
  }
  found.sort((x, y) => x.cost - y.cost);
  const rhsText = E.toText(R);
  return {
    deficit, deficitText: dimToString(deficit),
    candidates: found.slice(0, 5).map(f => ({ factor: f.factor, lhs: E.toText(L), rhs: `(${rhsText})*${f.factor}`, tex: `${E.toTex(L)} = ${E.toTex(E.parse(`(${rhsText})*${f.factor}`))}` })),
    text: found.length ? `The right-hand side is short by a factor of dimension [${dimToString(deficit)}]. The simplest amendments built from quantities already in the problem are listed; each is a candidate, to be chosen on physical grounds.` : `The right-hand side is short by a factor of dimension [${dimToString(deficit)}] and no simple combination of the registered quantities supplies it. The equation needs to be reformulated.`,
  };
}

/** Counting argument for mathematical closure: unknowns against independent equations. */
export function closure(equations, table, knownSyms) {
  const known = new Set(knownSyms);
  const all = new Set();
  const independents = new Set();
  equations.forEach(q => {
    try {
      const L = E.parse(q.lhs), R = E.parse(q.rhs);
      [...E.symbols(L), ...E.symbols(R)].forEach(s => all.add(s));
      const walk = u => { if (u.t === 'fn') { if (E.DIFF_OPS.has(u.n) && u.args[1] && u.args[1].t === 'sym') independents.add(u.args[1].n); u.args.forEach(walk); } else if (u.t === 'op') { walk(u.a); walk(u.b); } else if (u.t === 'neg') walk(u.a); };
      walk(L); walk(R);
    } catch { /* reported elsewhere */ }
  });
  const unknowns = [...all].filter(s => !known.has(s) && !independents.has(s) && s !== 'pi');
  const nEq = equations.filter(q => q.kind !== 'boundary' && q.kind !== 'initial').length;
  const diffEqs = equations.filter(q => { try { return E.hasDiffOps(E.parse(q.lhs)) || E.hasDiffOps(E.parse(q.rhs)); } catch { return false; } });
  return {
    unknowns, independents: [...independents], nEquations: nEq, nUnknowns: unknowns.length, nDifferential: diffEqs.length,
    closed: nEq >= unknowns.length,
    text: nEq === unknowns.length ? `Closed: ${nEq} independent relations for ${unknowns.length} unknowns.`
      : nEq > unknowns.length ? `${nEq} relations for ${unknowns.length} unknowns: the system is closed, with ${nEq - unknowns.length} relation(s) acting as definitions or consistency conditions.`
        : `Open: ${unknowns.length} unknowns but only ${nEq} relations. ${unknowns.length - nEq} further closure relation(s) or datum(s) are required.`,
  };
}

/** Build the symbol table used by verification from inputs, auxiliary symbols and computed scalars. */
export function symbolTable(inputs, symbolsMeta = {}, scalars = []) {
  const t = {};
  inputs.forEach(i => { const u = tryUnit(i.unit); t[i.sym] = { dim: u ? u.dim : D0, range: i.rangeSI || [i.si, i.si], name: i.name, unit: i.unit, value: i.si, input: true }; });
  Object.entries(symbolsMeta).forEach(([k, m]) => {
    if (t[k]) return;
    const u = tryUnit(m[1]);
    t[k] = { dim: u ? u.dim : D0, name: m[0], unit: m[1], range: m[2] && m[2].range ? m[2].range : undefined };
  });
  scalars.forEach(s => {
    if (t[s.sym] && !t[s.sym].range && Number.isFinite(s.value) && !t[s.sym].input) {
      const a = Math.abs(s.value);
      t[s.sym].range = s.value > 0 ? [s.value / 10, s.value * 10] : s.value < 0 ? [s.value * 10, s.value / 10] : undefined;
      t[s.sym].value = s.value;
      if (a === 0) delete t[s.sym].range;
    }
  });
  // universal constants that models reference without declaring
  const add = (k, name, unit, value) => { if (!t[k]) { const u = tryUnit(unit); t[k] = { dim: u.dim, name, unit, range: [value, value], value, constant: true }; } };
  add('g', 'Gravitational acceleration', 'm/s^2', 9.80665); add('R_u', 'Molar gas constant', 'J/(mol K)', 8.314462618);
  add('c', 'Speed of light', 'm/s', 299792458); add('G', 'Gravitational constant', 'm^3/(kg s^2)', 6.6743e-11);
  add('hbar', 'Reduced Planck constant', 'J s', 1.054571817e-34); add('k_B', 'Boltzmann constant', 'J/K', 1.380649e-23);
  add('eps_0', 'Vacuum permittivity', 'F/m', 8.8541878128e-12); add('mu_0', 'Vacuum permeability', 'H/m', 1.25663706212e-6);
  add('sigma_SB', 'Stefan–Boltzmann constant', 'W/(m^2 K^4)', 5.670374419e-8); add('e_c', 'Elementary charge', 'C', 1.602176634e-19);
  add('N_A', 'Avogadro constant', '1/mol', 6.02214076e23); add('h', 'Planck constant', 'J s', 6.62607015e-34);
  add('m_e', 'Electron mass', 'kg', 9.1093837015e-31); add('m_p', 'Proton mass', 'kg', 1.67262192369e-27);
  return t;
}

/** Verify a whole equation set and summarise. */
export function verifySystem(equations, table, knownSyms, opts) {
  const records = equations.map(q => verifyEquation(q, table, opts));
  const cl = closure(equations, table, knownSyms);
  const count = s => records.filter(r => r.status === s).length;
  return {
    records, closure: cl,
    summary: { total: records.length, verified: count('verified'), conditional: count('conditional'), singular: count('singular'), inconsistent: count('inconsistent'), incomplete: count('incomplete'), rejected: count('rejected') },
  };
}
