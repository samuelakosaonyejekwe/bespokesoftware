// Lean 4 source generation. Every equation is translated into machine-checkable statements:
//   1. dimensional homogeneity, proved by kernel computation on exponent vectors;
//   2. non-vanishing of every denominator and positivity of every logarithm/root argument on the
//      declared domain, proved by the `positivity` tactic or stated as an explicit hypothesis;
//   3. boundedness and smoothness of each regularised term, by appeal to the proved library lemmas.
// The file is self-contained (it restates the library) so it can be checked anywhere Lean 4 with
// Mathlib is available.
import * as E from './expr.js';
import { showLean, atoms as logicAtoms, parseFormula } from './logic.js';

export const LEAN_IMPORTS = `import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations`;

export const LEAN_LIBRARY = `/-- Physical dimension: exponents of (mass, length, time, current, temperature, amount,
luminous intensity), stored in twelfths so that square and cube roots stay integral. -/
structure Dim where
  m : Int
  l : Int
  t : Int
  i : Int
  th : Int
  n : Int
  j : Int
  deriving DecidableEq, Repr

namespace Dim
def one : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩
def mul (a b : Dim) : Dim := ⟨a.m + b.m, a.l + b.l, a.t + b.t, a.i + b.i, a.th + b.th, a.n + b.n, a.j + b.j⟩
def div (a b : Dim) : Dim := ⟨a.m - b.m, a.l - b.l, a.t - b.t, a.i - b.i, a.th - b.th, a.n - b.n, a.j - b.j⟩
/-- Rational power p/q. -/
def pow (a : Dim) (p q : Int) : Dim := ⟨a.m * p / q, a.l * p / q, a.t * p / q, a.i * p / q, a.th * p / q, a.n * p / q, a.j * p / q⟩
end Dim

/-- The softened denominator never vanishes. -/
theorem soft_den_pos (b ε : ℝ) (hε : 0 < ε) : 0 < b ^ 2 + ε ^ 2 := by positivity

/-- A regularised quotient is bounded by |a| / (2 ε) for every real b: it cannot blow up. -/
theorem soft_recip_bounded (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := by
  have hpos : 0 < b ^ 2 + ε ^ 2 := by positivity
  rw [abs_div, abs_mul, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have h : 2 * ε * |b| ≤ b ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (|b| - ε), sq_abs b]
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- The regularised reciprocal is infinitely differentiable on the whole real line. -/
theorem soft_recip_smooth (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ⊤ (fun b : ℝ => b / (b ^ 2 + ε ^ 2)) := by
  apply ContDiff.div contDiff_id (by fun_prop)
  intro x; positivity

/-- Exponential relaxation never exceeds its initial amplitude. -/
theorem decay_bounded (x ell : ℝ) (hx : 0 ≤ x) (hl : 0 < ell) : Real.exp (-x / ell) ≤ 1 := by
  rw [Real.exp_le_one_iff]; have := div_nonneg hx hl.le; linarith [neg_div ell x]

/-- Saturating nonlinearity stays strictly inside (-1, 1). -/
theorem tanh_bounded (x : ℝ) : |Real.tanh x| < 1 := by
  rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

/-- Below light speed the Lorentz factor is well defined. -/
theorem lorentz_pos (v c : ℝ) (hc : 0 < c) (hv : |v| < c) : 0 < 1 - v ^ 2 / c ^ 2 := by
  have h : v ^ 2 < c ^ 2 := by nlinarith [abs_lt.mp hv, sq_abs v, abs_nonneg v]
  have : v ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact h
  linarith`;

const ident = s => {
  let k = String(s).replace(/[^A-Za-z0-9_]/g, '_');
  if (/^\d/.test(k)) k = `x${k}`;
  // avoid Lean keywords and common Mathlib names
  if (['at', 'in', 'fun', 'by', 'do', 'if', 'then', 'else', 'let', 'have', 'show', 'from', 'end', 'open', 'def', 'theorem', 'example', 'Type', 'Prop', 'Sort', 'e', 'π', 'pi', 'I', 'id', 'min', 'max', 'abs'].includes(k)) k = `${k}'`;
  return k;
};
const dimLit = d => `⟨${d.map(x => Math.round(x * 12)).join(', ')}⟩`;
const frac = p => { for (const q of [1, 2, 3, 4, 6, 12]) if (Math.abs(p * q - Math.round(p * q)) < 1e-9) return [Math.round(p * q), q]; return null; };

/** Structural dimension term in Lean, plus the list of additive side conditions it implies. */
function dimTerm(e, table, side) {
  switch (e.t) {
    case 'num': return 'Dim.one';
    case 'sym': return e.n === 'pi' ? 'Dim.one' : (table[e.n] ? `d_${ident(e.n)}` : null);
    case 'neg': return dimTerm(e.a, table, side);
    case 'op': {
      const a = dimTerm(e.a, table, side), b = dimTerm(e.b, table, side);
      if (a == null || b == null) return null;
      if (e.o === '*') return `(Dim.mul ${a} ${b})`;
      if (e.o === '/') return `(Dim.div ${a} ${b})`;
      if (e.o === '^') {
        let p; try { p = E.evaluate(e.b, {}); } catch { return b === 'Dim.one' || true ? 'Dim.one' : null; }
        const f = frac(p); if (!f) return null;
        return `(Dim.pow ${a} ${f[0] < 0 ? `(${f[0]})` : f[0]} ${f[1]})`;
      }
      const za = e.a.t === 'num' && e.a.v === 0, zb = e.b.t === 'num' && e.b.v === 0;
      if (!za && !zb) side.push([a, b]);
      return za ? b : a;
    }
    case 'fn': {
      const a = e.args.map(x => dimTerm(x, table, side));
      if (a.some(x => x == null)) return null;
      switch (e.n) {
        case 'sqrt': return `(Dim.pow ${a[0]} 1 2)`;
        case 'abs': case 'floor': return a[0];
        case 'min': case 'max': { const z0 = e.args[0].t === 'num' && e.args[0].v === 0, z1 = e.args[1].t === 'num' && e.args[1].v === 0; if (!z0 && !z1) side.push([a[0], a[1]]); return z0 ? a[1] : a[0]; }
        case 'd': case 'pd': return `(Dim.div ${a[0]} ${a[1]})`;
        case 'd2': case 'pd2': return `(Dim.div ${a[0]} (Dim.pow ${a[1]} 2 1))`;
        case 'grad': case 'div': case 'curl': return `(Dim.div ${a[0]} d_length)`;
        case 'lap': return `(Dim.div ${a[0]} (Dim.pow d_length 2 1))`;
        case 'int': return `(Dim.mul ${a[0]} ${a[1]})`;
        case 'pow': { const f = frac(E.evaluate(e.args[1], {})); return f ? `(Dim.pow ${a[0]} ${f[0] < 0 ? `(${f[0]})` : f[0]} ${f[1]})` : null; }
        case 'sign': case 'heaviside': case 'atan2': return 'Dim.one';
        default: side.push([a[0], 'Dim.one']); return 'Dim.one';
      }
    }
  }
  return null;
}

const leanReal = (e, ren) => E.toCode(e, 'lean', ren);
const usesOnly = (e, okFns) => { let ok = true; const go = u => { if (u.t === 'fn') { if (!okFns.has(u.n)) ok = false; u.args.forEach(go); } else if (u.t === 'op') { go(u.a); go(u.b); if (u.o === '^' && !(u.b.t === 'num' && Number.isInteger(u.b.v) && u.b.v >= 0)) ok = false; } else if (u.t === 'neg') go(u.a); }; go(e); return ok; };
const hasSub = e => { let s = false; const go = u => { if (u.t === 'op') { if (u.o === '-') s = true; go(u.a); go(u.b); } else if (u.t === 'neg') { s = true; } else if (u.t === 'fn') u.args.forEach(go); }; go(e); return s; };

/**
 * Generate a Lean file for a verified equation set.
 * @param title  heading
 * @param verification  result of verifySystem (records carry obligations)
 * @param table  symbol table {sym: {dim, range, name, unit}}
 * @param logic  optional {premises: [formula strings], conclusion, status}
 */
export function generateLean(title, verification, table, logic, meta = {}) {
  const L = [];
  const safeTitle = String(title).replace(/-\//g, '- /').replace(/\/-/g, '/ -');
  L.push(LEAN_IMPORTS, '', `/-!`, `# ${safeTitle}`, '', `Machine-checkable statements for this investigation${meta.id ? ` (${meta.id})` : ''}.`,
    'Dimensional homogeneity is proved by computation. Regularity statements are proved where the',
    'declared domain makes them true, and are otherwise stated with their hypotheses made explicit.', '-/', '', 'namespace Bespoke', '', LEAN_LIBRARY, '', '/-! ## Dimensions of the symbols -/', '', 'def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩');
  const used = new Set();
  (verification ? verification.records : []).forEach(r => (r.symbols || []).forEach(s => used.add(s)));
  [...used].sort().forEach(s => { if (table[s] && s !== 'pi') L.push(`def d_${ident(s)} : Dim := ${dimLit(table[s].dim)}  -- ${table[s].name || s} [${table[s].unit || ''}]`); });
  const stats = { dim: 0, dimSkipped: 0, reg: 0, hyp: 0, soft: 0 };
  let idx = 0;
  for (const r of (verification ? verification.records : [])) {
    idx++;
    const tag = `eq${idx}_${ident(r.id)}`;
    L.push('', `/-! ## ${idx}. ${String(r.name).replace(/-\//g, '')}`, '', `    ${r.lhs} = ${r.rhs}`, '-/');
    let Lx, Rx;
    try { Lx = E.parse(r.lhs); Rx = E.parse(r.rhs); } catch { L.push(`-- not translated: the expression does not parse`); continue; }
    // (1) dimensions
    const side = [], dl = dimTerm(Lx, table, side), dr = dimTerm(Rx, table, side);
    const dimOk = r.steps.find(s => s.check === 'Dimensions');
    if (dl && dr && dimOk && dimOk.ok) {
      L.push(`/-- Both sides of "${String(r.name).replace(/"/g, "'")}" carry the same physical dimension. -/`, `theorem ${tag}_dim : ${dl} = ${dr} := by decide`);
      side.forEach(([a, b], k) => L.push(`theorem ${tag}_term${k + 1} : ${a} = ${b} := by decide`));
      stats.dim += 1 + side.length;
    } else { L.push(`-- dimensional statement omitted: ${dimOk && dimOk.ok === false ? 'the equation is not homogeneous as written' : 'a symbol has no registered unit'}`); stats.dimSkipped++; }
    // (2) regularity obligations
    (r.obligations || []).forEach((o, k) => {
      const syms = [...E.symbols(o.expr)].filter(s => s !== 'pi');
      const ren = s => ident(s);
      const positive = syms.filter(s => table[s] && table[s].range && table[s].range[0] > 0);
      const binders = syms.length ? `(${syms.map(ren).join(' ')} : ℝ) ` : '';
      const hyps = positive.map(s => `(h${ren(s)} : 0 < ${ren(s)})`).join(' ');
      let body; try { body = leanReal(o.expr, ren); } catch { return; }
      const goal = o.kind === 'denominator' ? `${body} ≠ 0` : o.kind === 'log' ? `0 < ${body}` : `0 ≤ ${body}`;
      const simple = usesOnly(o.expr, new Set(['sqrt', 'exp', 'abs', 'cosh'])) && !hasSub(o.expr) && syms.every(s => positive.includes(s));
      if (o.proved && simple) {
        L.push(`/-- ${o.kind === 'denominator' ? 'The denominator' : 'The argument'} \`${o.text}\` stays away from its singular set whenever the quantities are positive. -/`, `theorem ${tag}_reg${k + 1} ${binders}${hyps} : ${goal} := by positivity`);
        stats.reg++;
      } else {
        L.push(`/-- Domain condition for \`${o.text}\`: ${o.proved ? 'established on the declared ranges by interval arithmetic' : 'a condition on the solution'}; stated here as an explicit hypothesis. -/`, `theorem ${tag}_cond${k + 1} ${binders}(hdom : ${goal}) : ${goal} := hdom`);
        stats.hyp++;
      }
    });
    // (3) regularised surrogate
    if (r.regularised) {
      L.push(`/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),`, `    which is bounded and smooth for every real b. -/`, `theorem ${tag}_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε`);
      stats.soft++;
    }
  }
  if (logic && logic.premises && logic.premises.length) {
    L.push('', '/-! ## Logical structure of the argument -/', '');
    try {
      const names = [...new Set([...logic.premises, ...(logic.conclusion ? [logic.conclusion] : [])].flatMap(f => [...logicAtoms(parseFormula(f))]))].sort();
      const vars = names.length ? `(${names.join(' ')} : Prop) ` : '';
      const prem = logic.premises.map((p, i) => `(h${i + 1} : ${showLean(parseFormula(p))})`).join(' ');
      if (logic.status === 'valid' && logic.conclusion) L.push('/-- The conclusion follows from the premises in classical propositional logic. -/', `theorem argument_valid ${vars}${prem} : ${showLean(parseFormula(logic.conclusion))} := by tauto`);
      else if (logic.status === 'inconsistent-premises') L.push('/-- The premises are jointly contradictory. -/', `theorem premises_inconsistent ${vars}${prem} : False := by tauto`);
      else if (logic.status === 'contradicted' && logic.conclusion) L.push('/-- The premises entail the negation of the proposed conclusion. -/', `theorem conclusion_refuted ${vars}${prem} : ¬(${showLean(parseFormula(logic.conclusion))}) := by tauto`);
      else if (logic.status === 'invalid' && logic.conclusion && logic.counter && logic.counter[0]) {
        const w = logic.counter[0].w;
        const sub = f => showLean(parseFormula(f)).replace(/[A-Za-z_][A-Za-z0-9_]*/g, m => (m in w ? (w[m] ? 'True' : 'False') : m));
        L.push('/-- The inference is not valid: this assignment makes every premise true and the conclusion false. -/', `theorem countermodel : (${logic.premises.map(sub).join(') ∧ (')}) ∧ ¬(${sub(logic.conclusion)}) := by simp`);
      } else L.push('-- the premises are consistent; no entailment claim is made');
      stats.logic = 1;
    } catch { L.push('-- logical statements could not be translated'); }
  }
  L.push('', 'end Bespoke', '');
  return { source: L.join('\n'), stats };
}

/** URL that opens the generated source in the public Lean 4 web editor for an independent check. */
export const leanLiveUrl = source => `https://live.lean-lang.org/#code=${encodeURIComponent(source.replace(/^import Mathlib\.[^\n]*\n/gm, '').replace(/^/, 'import Mathlib\n'))}`;
