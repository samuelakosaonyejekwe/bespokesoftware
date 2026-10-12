// Propositional reasoning engine for logically analysable experiments:
// formula parsing, truth tables, satisfiability, entailment, countermodels,
// minimal inconsistent premise sets and possible-world enumeration.

const OPS = { '¬': 'not', '!': 'not', '~': 'not', '∧': 'and', '&': 'and', '∨': 'or', '|': 'or', '→': 'imp', '->': 'imp', '=>': 'imp', '↔': 'iff', '<->': 'iff', '<=>': 'iff', '⊕': 'xor' };
const WORDS = { not: 'not', and: 'and', or: 'or', implies: 'imp', iff: 'iff', xor: 'xor', then: 'imp' };

function tokenize(s) {
  const out = []; let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (c === '(' || c === ')') { out.push(c); i++; continue; }
    const three = s.slice(i, i + 3), two = s.slice(i, i + 2);
    if (OPS[three]) { out.push(OPS[three]); i += 3; continue; }
    if (OPS[two]) { out.push(OPS[two]); i += 2; continue; }
    if (OPS[c]) { out.push(OPS[c]); i++; continue; }
    const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(s.slice(i));
    if (m) {
      const w = m[0], lw = w.toLowerCase();
      i += w.length;
      if (lw === 'true' || lw === 'false') out.push({ c: lw === 'true' });
      else if (WORDS[lw]) out.push(WORDS[lw]);
      else out.push({ v: w });
      continue;
    }
    throw new Error(`Unexpected "${c}" in formula`);
  }
  return out;
}

/** Parse a formula such as "(P & Q) -> ~R". Precedence: not > and > or/xor > implies > iff. */
export function parseFormula(src) {
  const t = tokenize(src); let p = 0;
  const atom = () => {
    const k = t[p];
    if (k === 'not') { p++; return { t: 'not', a: atom() }; }
    if (k === '(') { p++; const e = iff(); if (t[p] !== ')') throw new Error('Missing ")"'); p++; return e; }
    if (k && typeof k === 'object') { p++; return 'c' in k ? { t: 'const', v: k.c } : { t: 'var', n: k.v }; }
    throw new Error('Incomplete formula');
  };
  const and = () => { let a = atom(); while (t[p] === 'and') { p++; a = { t: 'and', a, b: atom() }; } return a; };
  const or = () => { let a = and(); while (t[p] === 'or' || t[p] === 'xor') { const o = t[p++]; a = { t: o, a, b: and() }; } return a; };
  const imp = () => { const a = or(); if (t[p] === 'imp') { p++; return { t: 'imp', a, b: imp() }; } return a; };
  function iff() { let a = imp(); while (t[p] === 'iff') { p++; a = { t: 'iff', a, b: imp() }; } return a; }
  const e = iff();
  if (p < t.length) throw new Error('Unexpected text after formula');
  return e;
}
const F = f => (typeof f === 'string' ? parseFormula(f) : f);

export function atoms(f, out = new Set()) {
  f = F(f);
  if (f.t === 'var') out.add(f.n); else if (f.t !== 'const') { atoms(f.a, out); if (f.b) atoms(f.b, out); }
  return out;
}
export function evalFormula(f, w) {
  f = F(f);
  switch (f.t) {
    case 'const': return f.v;
    case 'var': return !!w[f.n];
    case 'not': return !evalFormula(f.a, w);
    case 'and': return evalFormula(f.a, w) && evalFormula(f.b, w);
    case 'or': return evalFormula(f.a, w) || evalFormula(f.b, w);
    case 'xor': return evalFormula(f.a, w) !== evalFormula(f.b, w);
    case 'imp': return !evalFormula(f.a, w) || evalFormula(f.b, w);
    case 'iff': return evalFormula(f.a, w) === evalFormula(f.b, w);
  }
  return false;
}
export function show(f) {
  f = F(f);
  const wrap = g => (g.t === 'var' || g.t === 'const' || g.t === 'not' ? show(g) : `(${show(g)})`);
  switch (f.t) {
    case 'const': return f.v ? '⊤' : '⊥';
    case 'var': return f.n;
    case 'not': return `¬${wrap(f.a)}`;
    case 'and': return `${wrap(f.a)} ∧ ${wrap(f.b)}`;
    case 'or': return `${wrap(f.a)} ∨ ${wrap(f.b)}`;
    case 'xor': return `${wrap(f.a)} ⊕ ${wrap(f.b)}`;
    case 'imp': return `${wrap(f.a)} → ${wrap(f.b)}`;
    case 'iff': return `${wrap(f.a)} ↔ ${wrap(f.b)}`;
  }
  return '?';
}
export function showTex(f) {
  return show(f).replace(/¬/g, '\\lnot ').replace(/∧/g, '\\land').replace(/∨/g, '\\lor').replace(/→/g, '\\rightarrow').replace(/↔/g, '\\leftrightarrow').replace(/⊕/g, '\\oplus').replace(/⊤/g, '\\top').replace(/⊥/g, '\\bot').replace(/_/g, '\\_');
}
export function showLean(f) {
  f = F(f);
  const wrap = g => (g.t === 'var' || g.t === 'const' ? showLean(g) : `(${showLean(g)})`);
  switch (f.t) {
    case 'const': return f.v ? 'True' : 'False';
    case 'var': return f.n;
    case 'not': return `¬${wrap(f.a)}`;
    case 'and': return `${wrap(f.a)} ∧ ${wrap(f.b)}`;
    case 'or': return `${wrap(f.a)} ∨ ${wrap(f.b)}`;
    case 'xor': return `Xor' ${wrap(f.a)} ${wrap(f.b)}`;
    case 'imp': return `${wrap(f.a)} → ${wrap(f.b)}`;
    case 'iff': return `${wrap(f.a)} ↔ ${wrap(f.b)}`;
  }
  return '?';
}

export function worlds(names) {
  const n = names.length, out = [];
  if (n > 16) throw new Error('Too many atomic propositions for exhaustive enumeration (limit 16)');
  for (let m = 0; m < (1 << n); m++) { const w = {}; names.forEach((nm, i) => { w[nm] = !!(m & (1 << (n - 1 - i))); }); out.push(w); }
  return out;
}

/**
 * Full analysis of an argument: premises ⊨ conclusion?
 * Returns the truth table, satisfying worlds, countermodels, consistency of the premises,
 * the smallest inconsistent premise sets, redundant premises and the premises the conclusion actually needs.
 */
export function analyse(premiseSrc, conclusionSrc) {
  const premises = premiseSrc.map(F), conclusion = conclusionSrc ? F(conclusionSrc) : null;
  const names = [...new Set([...premises.flatMap(p => [...atoms(p)]), ...(conclusion ? atoms(conclusion) : [])])].sort();
  const W = worlds(names);
  const rows = W.map(w => {
    const pv = premises.map(p => evalFormula(p, w));
    return { w, premises: pv, all: pv.every(Boolean), conclusion: conclusion ? evalFormula(conclusion, w) : null };
  });
  const models = rows.filter(r => r.all);
  const consistent = models.length > 0;
  const counter = conclusion ? models.filter(r => !r.conclusion) : [];
  const valid = conclusion ? counter.length === 0 : null;
  const entails = (idx, f) => W.every(w => !idx.every(i => evalFormula(premises[i], w)) || evalFormula(f, w));
  const sat = idx => W.some(w => idx.every(i => evalFormula(premises[i], w)));

  // minimal inconsistent subsets (premise conflicts)
  const conflicts = [];
  if (!consistent && premises.length <= 12) {
    const n = premises.length;
    for (let size = 1; size <= n && conflicts.length < 6; size++) {
      const pick = (start, cur) => {
        if (cur.length === size) { if (!sat(cur) && !conflicts.some(c => c.every(x => cur.includes(x)))) conflicts.push(cur.slice()); return; }
        for (let i = start; i < n; i++) { cur.push(i); pick(i + 1, cur); cur.pop(); }
      };
      pick(0, []);
    }
  }
  // which premises does the conclusion really depend on?
  let needed = [], redundant = [];
  if (conclusion && valid && consistent) {
    const all = premises.map((_, i) => i);
    needed = all.filter(i => !entails(all.filter(j => j !== i), conclusion));
    redundant = all.filter(i => !needed.includes(i));
  }
  const status = !consistent ? 'inconsistent-premises'
    : conclusion == null ? 'consistent'
      : valid ? 'valid'
        : models.every(r => !r.conclusion) ? 'contradicted' : 'invalid';
  const tautology = conclusion ? W.every(w => evalFormula(conclusion, w)) : false;
  return { names, rows, models, consistent, valid, counter, conflicts, needed, redundant, status, tautology, premises, conclusion };
}

/** Natural-deduction style explanation of why a valid conclusion follows (case analysis over the atoms). */
export function explain(result) {
  const { status, names, models, counter, conflicts, premises, needed } = result;
  const lines = [];
  const desc = w => names.map(n => `${n} = ${w[n] ? 'true' : 'false'}`).join(', ');
  if (status === 'inconsistent-premises') {
    lines.push('The premises cannot all be true together: no assignment of truth values satisfies every one of them.');
    conflicts.forEach(c => lines.push(`Conflict: premises ${c.map(i => `P${i + 1}`).join(', ')} are jointly unsatisfiable — ${c.map(i => show(premises[i])).join('  ;  ')}.`));
    lines.push('From inconsistent premises every statement follows (ex falso), so no conclusion drawn from them is informative.');
  } else if (status === 'valid') {
    lines.push(`Across all ${1 << names.length} possible worlds, the premises hold in ${models.length}; the conclusion is true in every one of those. The inference is therefore deductively valid.`);
    if (needed.length) lines.push(`The conclusion depends essentially on ${needed.map(i => `P${i + 1}`).join(', ')}; removing any of them breaks the inference.`);
  } else if (status === 'invalid') {
    lines.push(`The inference is not valid: the premises hold in ${models.length} world(s) but the conclusion fails in ${counter.length} of them.`);
    counter.slice(0, 3).forEach(r => lines.push(`Countermodel: ${desc(r.w)} — every premise is true while the conclusion is false.`));
  } else if (status === 'contradicted') {
    lines.push('The premises are consistent, but the conclusion is false in every world that satisfies them: the premises entail its negation.');
  } else lines.push(`The premises are jointly satisfiable in ${models.length} of ${1 << names.length} possible worlds.`);
  return lines;
}

const STOP = new Set(['the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'it', 'this', 'that', 'will', 'would', 'does', 'do', 'of', 'to', 'in', 'on', 'at', 'for', 'by', 'with', 'as', 'has', 'have', 'had', 'can', 'could', 'must', 'should', 'there']);
const norm = s => s.toLowerCase().replace(/[^a-z0-9\s]/g, ' ').split(/\s+/).filter(w => w && !STOP.has(w)).join(' ');

/**
 * Heuristic translation of plain English into propositional structure.
 * Recognises "if A then B", "A only if B", "A unless B", "A if and only if B", "either A or B",
 * "not A", "A and B", and conclusion markers ("therefore", "so", "hence", "thus", "it follows that").
 * The user can always edit the result; nothing is hidden.
 */
export function fromText(text) {
  const atomsMap = new Map(); const atomList = [];
  const letter = i => (i < 26 ? String.fromCharCode(80 + (i % 11)) + (i >= 11 ? Math.floor(i / 11) : '') : `X${i}`);
  const atomFor = raw => {
    let s = raw.trim().replace(/^[,;:\s]+|[,;:.\s]+$/g, '');
    let negated = false;
    const mNeg = /^(it is not the case that|it is false that|not)\s+(.*)$/i.exec(s);
    if (mNeg) { negated = true; s = mNeg[2]; }
    const POS = [[/\b(is|are|was|were) not\b/i, '$1'], [/\b(is|are|was|were)n't\b/i, '$1'], [/\b(has|have|had) not\b/i, '$1'], [/\b(has|have|had)n't\b/i, '$1'], [/\b(does|do|did) not\b\s*/i, ''], [/\b(does|do|did)n't\b\s*/i, ''],
      [/\bcannot\b|\bcan't\b/i, 'can'], [/\bwill not\b|\bwon't\b/i, 'will'], [/\bnever\b\s*/i, ''], [/\bno longer\b\s*/i, ''], [/\bnot\b\s*/i, '']];
    for (const [re, rep] of POS) if (re.test(s)) { negated = !negated; s = s.replace(re, rep); break; }
    const key = norm(s);
    if (!key) return null;
    if (!atomsMap.has(key)) { const k = letter(atomList.length); atomsMap.set(key, k); atomList.push({ k, text: s.replace(/\s+/g, ' ') }); }
    return (negated ? '~' : '') + atomsMap.get(key);
  };
  const clause = raw => {
    let s = raw.trim().replace(/[.]$/, '');
    if (!s) return null;
    let m;
    if ((m = /^(.+?)\s+if and only if\s+(.+)$/i.exec(s)) || (m = /^(.+?)\s+iff\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) <-> (${b})` : null; }
    if ((m = /^if\s+(.+?),?\s+then\s+(.+)$/i.exec(s)) || (m = /^if\s+(.+?),\s*(.+)$/i.exec(s)) || (m = /^(?:when|whenever|suppose|assuming)\s+(.+?),\s*(?:then\s+)?(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) -> (${b})` : null; }
    if ((m = /^(.+?)\s+only if\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) -> (${b})` : null; }
    if ((m = /^(.+?)\s+(?:if|whenever|provided that)\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${b}) -> (${a})` : null; }
    if ((m = /^(.+?)\s+unless\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `~(${b}) -> (${a})` : null; }
    if ((m = /^(.+?)\s+implies(?: that)?\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) -> (${b})` : null; }
    if ((m = /^either\s+(.+?)\s+or\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) | (${b})` : null; }
    if ((m = /^neither\s+(.+?)\s+nor\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `~(${a}) & ~(${b})` : null; }
    if ((m = /^(.+?)\s+(?:and|but|while|yet)\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) & (${b})` : null; }
    if ((m = /^(.+?),?\s+or\s+(.+)$/i.exec(s))) { const a = clause(m[1]), b = clause(m[2]); return a && b ? `(${a}) | (${b})` : null; }
    return atomFor(s);
  };
  const sentences = String(text).replace(/\s+/g, ' ').split(/(?<=[.;!?])\s+|\n+/).map(s => s.trim()).filter(Boolean);
  const premises = []; let conclusion = null; const notes = [];
  for (const raw of sentences) {
    if (/\?\s*$/.test(raw)) { notes.push(`Question left out of the formal premises: "${raw}"`); continue; }
    const mc = /^(?:therefore|thus|hence|so|consequently|it follows that|we conclude that|this means that|then)[,:]?\s+(.+)$/i.exec(raw.replace(/[.]$/, ''));
    try {
      if (mc) { const f = clause(mc[1]); if (f) { parseFormula(f); conclusion = f; } }
      else { const f = clause(raw); if (f) { parseFormula(f); premises.push(f); } }
    } catch { notes.push(`Could not formalise: "${raw}"`); }
  }
  return { atoms: atomList, premises, conclusion, notes };
}
