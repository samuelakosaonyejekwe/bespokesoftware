// Symbolic expressions: parse, evaluate, differentiate, simplify, check dimensions,
// bound over a domain with interval arithmetic, regularise singular terms, and
// translate to LaTeX / Python / MATLAB / C++ / Lean.
import { D0, dimMul, dimDiv, dimPow, dimEq, isDimless, dimToString } from './units.js';

export const num = v => ({ t: 'num', v });
export const sym = n => ({ t: 'sym', n });
export const op = (o, a, b) => ({ t: 'op', o, a, b });
export const neg = a => ({ t: 'neg', a });
export const fn = (n, ...args) => ({ t: 'fn', n, args });

const FN1 = {
  sqrt: Math.sqrt, exp: Math.exp, ln: Math.log, log: Math.log, log10: Math.log10, sin: Math.sin, cos: Math.cos, tan: Math.tan,
  asin: Math.asin, acos: Math.acos, atan: Math.atan, sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh, asinh: Math.asinh, acosh: Math.acosh, atanh: Math.atanh, abs: Math.abs,
  sign: Math.sign, floor: Math.floor, erf, heaviside: x => (x >= 0 ? 1 : 0),
};
const FN2 = { min: Math.min, max: Math.max, atan2: Math.atan2, pow: Math.pow };
// differential operators kept symbolic: d(y,t) dy/dt, d2(y,t), pd(u,x) ∂u/∂x, pd2(u,x), lap(u), grad(u), div(u), curl(u), int(f,x)
export const DIFF_OPS = new Set(['d', 'd2', 'pd', 'pd2', 'lap', 'grad', 'div', 'curl', 'int', 'mat']);
const CONSTS = { pi: Math.PI, e_euler: Math.E };

export function erf(x) {
  const s = Math.sign(x); x = Math.abs(x);
  const t = 1 / (1 + 0.3275911 * x);
  const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
  return s * y;
}

// ---------------------------------------------------------------- parsing
export function parse(src) {
  const s = String(src);
  let i = 0;
  const ws = () => { while (i < s.length && /\s/.test(s[i])) i++; };
  const peek = () => { ws(); return s[i]; };
  const primary = () => {
    ws();
    const c = s[i];
    if (c === '(') { i++; const e = additive(); ws(); if (s[i] !== ')') throw new Error(`Expected ")" at ${i} in "${s}"`); i++; return e; }
    const mn = /^(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?/.exec(s.slice(i));
    if (mn) { i += mn[0].length; return num(parseFloat(mn[0])); }
    const mi = /^[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_Ͱ-Ͽ]*/.exec(s.slice(i));
    if (mi) {
      i += mi[0].length;
      const name = mi[0];
      if (peek() === '(') {
        i++;
        const args = [];
        if (peek() !== ')') { args.push(additive()); while (peek() === ',') { i++; args.push(additive()); } }
        if (peek() !== ')') throw new Error(`Expected ")" after arguments of ${name}`);
        i++;
        return fn(name, ...args);
      }
      return sym(name);
    }
    throw new Error(`Unexpected "${c ?? 'end'}" at ${i} in "${s}"`);
  };
  const power = () => {
    const base = primary();
    if (peek() === '^') { i++; return op('^', base, unary()); }
    if (s[i] === '*' && s[i + 1] === '*') { i += 2; return op('^', base, unary()); }
    return base;
  };
  const unary = () => {
    const c = peek();
    if (c === '-') { i++; return neg(unary()); }
    if (c === '+') { i++; return unary(); }
    return power();
  };
  const mult = () => {
    let a = unary();
    for (;;) {
      const c = peek();
      if (c === '*' && s[i + 1] !== '*') { i++; a = op('*', a, unary()); }
      else if (c === '/') { i++; a = op('/', a, unary()); }
      else break;
    }
    return a;
  };
  function additive() {
    let a = mult();
    for (;;) {
      const c = peek();
      if (c === '+') { i++; a = op('+', a, mult()); }
      else if (c === '-') { i++; a = op('-', a, mult()); }
      else break;
    }
    return a;
  }
  const e = additive();
  ws();
  if (i < s.length) throw new Error(`Unexpected "${s[i]}" at ${i} in "${s}"`);
  return e;
}
const P = e => (typeof e === 'string' ? parse(e) : e);

export function symbols(e, out = new Set()) {
  e = P(e);
  if (e.t === 'sym') { if (!(e.n in CONSTS)) out.add(e.n); }
  else if (e.t === 'op') { symbols(e.a, out); symbols(e.b, out); }
  else if (e.t === 'neg') symbols(e.a, out);
  else if (e.t === 'fn') e.args.forEach(a => symbols(a, out));
  return out;
}
export const hasDiffOps = e => {
  e = P(e);
  if (e.t === 'fn') return DIFF_OPS.has(e.n) || e.args.some(hasDiffOps);
  if (e.t === 'op') return hasDiffOps(e.a) || hasDiffOps(e.b);
  if (e.t === 'neg') return hasDiffOps(e.a);
  return false;
};

// ---------------------------------------------------------------- evaluation
export function evaluate(e, env = {}) {
  e = P(e);
  switch (e.t) {
    case 'num': return e.v;
    case 'sym': {
      if (e.n in env) return env[e.n];
      if (e.n in CONSTS) return CONSTS[e.n];
      throw new Error(`No value for "${e.n}"`);
    }
    case 'neg': return -evaluate(e.a, env);
    case 'op': {
      const a = evaluate(e.a, env), b = evaluate(e.b, env);
      switch (e.o) { case '+': return a + b; case '-': return a - b; case '*': { // x·ln x → 0 as x → 0: the limit, where plain arithmetic would give 0·(−∞) = NaN
          if ((a === 0 && b === -Infinity && e.b.t === 'fn' && /^(ln|log|log10|log2)$/.test(e.b.n)) || (b === 0 && a === -Infinity && e.a.t === 'fn' && /^(ln|log|log10|log2)$/.test(e.a.n))) return 0;
          return a * b; } case '/': return a / b; case '^': return Math.pow(a, b); }
      break;
    }
    case 'fn': {
      if (FN1[e.n]) return FN1[e.n](evaluate(e.args[0], env));
      if (FN2[e.n]) return FN2[e.n](evaluate(e.args[0], env), evaluate(e.args[1], env));
      if (e.n === 'ifpos') return evaluate(e.args[0], env) > 0 ? evaluate(e.args[1], env) : evaluate(e.args[2], env);
      throw new Error(`"${e.n}" is a differential operator and has no pointwise value`);
    }
  }
  throw new Error('Malformed expression');
}
// ---------------------------------------------------------------- simplification & calculus
const isNum = (e, v) => e.t === 'num' && (v === undefined || e.v === v);
export function simplify(e) {
  e = P(e);
  if (e.t === 'neg') {
    const a = simplify(e.a);
    if (a.t === 'num') return num(-a.v);
    if (a.t === 'neg') return a.a;
    return neg(a);
  }
  if (e.t === 'fn') return fn(e.n, ...e.args.map(simplify));
  if (e.t !== 'op') return e;
  const a = simplify(e.a), b = simplify(e.b);
  if (a.t === 'num' && b.t === 'num') {
    const v = evaluate(op(e.o, a, b));
    if (isFinite(v)) return num(v);
  }
  switch (e.o) {
    case '+': if (isNum(a, 0)) return b; if (isNum(b, 0)) return a; if (b.t === 'neg') return op('-', a, b.a); break;
    case '-': if (isNum(b, 0)) return a; if (isNum(a, 0)) return simplify(neg(b)); if (b.t === 'neg') return op('+', a, b.a); break;
    case '*':
      if (isNum(a, 0) || isNum(b, 0)) return num(0);
      if (isNum(a, 1)) return b; if (isNum(b, 1)) return a;
      if (isNum(a, -1)) return simplify(neg(b)); if (isNum(b, -1)) return simplify(neg(a));
      if (a.t === 'neg' && b.t === 'neg') return op('*', a.a, b.a);
      if (b.t === 'num' && a.t !== 'num') return op('*', b, a);
      break;
    case '/': if (isNum(a, 0)) return num(0); if (isNum(b, 1)) return a; break;
    case '^': if (isNum(b, 0)) return num(1); if (isNum(b, 1)) return a; if (isNum(a, 1)) return num(1); break;
  }
  return op(e.o, a, b);
}

export function diff(e, x) {
  e = P(e);
  const D = u => diff(u, x);
  switch (e.t) {
    case 'num': return num(0);
    case 'sym': return num(e.n === x ? 1 : 0);
    case 'neg': return simplify(neg(D(e.a)));
    case 'op': {
      const { a, b } = e;
      switch (e.o) {
        case '+': return simplify(op('+', D(a), D(b)));
        case '-': return simplify(op('-', D(a), D(b)));
        case '*': return simplify(op('+', op('*', D(a), b), op('*', a, D(b))));
        case '/': return simplify(op('/', op('-', op('*', D(a), b), op('*', a, D(b))), op('^', b, num(2))));
        case '^': {
          if (!symbols(b).has(x)) return simplify(op('*', op('*', b, op('^', a, simplify(op('-', b, num(1))))), D(a)));
          // general a^b = exp(b ln a)
          return simplify(op('*', e, op('+', op('*', D(b), fn('ln', a)), op('/', op('*', b, D(a)), a))));
        }
      }
      break;
    }
    case 'fn': {
      const u = e.args[0], du = D(u);
      const chain = f => simplify(op('*', f, du));
      switch (e.n) {
        case 'sqrt': return chain(op('/', num(1), op('*', num(2), fn('sqrt', u))));
        case 'exp': return chain(e);
        case 'ln': case 'log': return chain(op('/', num(1), u));
        case 'log10': return chain(op('/', num(1), op('*', u, num(Math.LN10))));
        case 'sin': return chain(fn('cos', u));
        case 'cos': return chain(neg(fn('sin', u)));
        case 'tan': return chain(op('/', num(1), op('^', fn('cos', u), num(2))));
        case 'asin': return chain(op('/', num(1), fn('sqrt', op('-', num(1), op('^', u, num(2))))));
        case 'acos': return chain(neg(op('/', num(1), fn('sqrt', op('-', num(1), op('^', u, num(2)))))));
        case 'atan': return chain(op('/', num(1), op('+', num(1), op('^', u, num(2)))));
        case 'sinh': return chain(fn('cosh', u));
        case 'cosh': return chain(fn('sinh', u));
        case 'tanh': return chain(op('-', num(1), op('^', fn('tanh', u), num(2))));
        case 'asinh': return chain(op('/', num(1), fn('sqrt', op('+', op('^', u, num(2)), num(1)))));
        case 'acosh': return chain(op('/', num(1), fn('sqrt', op('-', op('^', u, num(2)), num(1)))));
        case 'atanh': return chain(op('/', num(1), op('-', num(1), op('^', u, num(2)))));
        case 'abs': return chain(fn('sign', u));
        case 'erf': return chain(op('*', num(2 / Math.sqrt(Math.PI)), fn('exp', neg(op('^', u, num(2))))));
        case 'pow': return diff(op('^', e.args[0], e.args[1]), x);
        default: return symbols(e).has(x) ? fn('pd', e, sym(x)) : num(0);
      }
    }
  }
  return num(0);
}

// ---------------------------------------------------------------- dimensional analysis
export class DimError extends Error {}
const isZero = u => u.t === 'num' && u.v === 0;
/** Dimension of an expression given symbol dimensions; throws DimError when inhomogeneous. */
export function dims(e, table) {
  e = P(e);
  switch (e.t) {
    case 'num': return D0;
    case 'sym': {
      if (e.n in CONSTS) return D0;
      const dd = table[e.n];
      if (!dd) throw new DimError(`No unit is registered for symbol "${e.n}"`);
      return dd;
    }
    case 'neg': return dims(e.a, table);
    case 'op': {
      const a = dims(e.a, table);
      if (e.o === '^') {
        const bd = dims(e.b, table);
        if (!isDimless(bd)) throw new DimError(`Exponent ${toText(e.b)} is not dimensionless`);
        if (isDimless(a)) return D0;
        let p;
        try { p = evaluate(e.b, {}); } catch { throw new DimError(`Dimensional quantity ${toText(e.a)} raised to a non-numeric power`); }
        return dimPow(a, p);
      }
      const b = dims(e.b, table);
      if (e.o === '*') return dimMul(a, b);
      if (e.o === '/') return dimDiv(a, b);
      if (isZero(e.a)) return b;
      if (isZero(e.b)) return a;
      if (!dimEq(a, b)) {
        // adding a bare number to a dimensionless-looking group is fine; anything else is an error
        throw new DimError(`Cannot ${e.o === '+' ? 'add' : 'subtract'} [${dimToString(a)}] and [${dimToString(b)}] in ${toText(e)}`);
      }
      return a;
    }
    case 'fn': {
      const a = e.args.map(x => dims(x, table));
      switch (e.n) {
        case 'sqrt': return dimPow(a[0], 0.5);
        case 'abs': case 'floor': return a[0];
        case 'sign': case 'heaviside': return D0;
        case 'min': case 'max':
          if (isZero(e.args[0])) return a[1];
          if (isZero(e.args[1])) return a[0];
          if (!dimEq(a[0], a[1])) throw new DimError(`Arguments of ${e.n} differ in dimension`);
          return a[0];
        case 'ifpos':
          if (isZero(e.args[1])) return a[2];
          if (isZero(e.args[2])) return a[1];
          if (!dimEq(a[1], a[2])) throw new DimError('The two branches of ifpos differ in dimension');
          return a[1];
        case 'atan2':
          if (!dimEq(a[0], a[1])) throw new DimError('Arguments of atan2 differ in dimension');
          return D0;
        case 'pow': return dimPow(a[0], evaluate(e.args[1], {}));
        case 'd': case 'pd': return dimDiv(a[0], a[1]);
        case 'd2': case 'pd2': return dimDiv(a[0], dimPow(a[1], 2));
        case 'grad': case 'div': case 'curl': return dimDiv(a[0], [0, 1, 0, 0, 0, 0, 0]);
        case 'lap': return dimDiv(a[0], [0, 2, 0, 0, 0, 0, 0]);
        case 'int': return dimMul(a[0], a[1]);
        default:
          if (!isDimless(a[0])) throw new DimError(`Argument of ${e.n}() must be dimensionless but is [${dimToString(a[0])}]`);
          return D0;
      }
    }
  }
  return D0;
}

// ---------------------------------------------------------------- interval arithmetic
const I = (lo, hi) => [lo, hi];
const iMul = (a, b) => { const p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]].map(x => (Number.isNaN(x) ? 0 : x)); return I(Math.min(...p), Math.max(...p)); };
const mono = f => a => I(f(a[0]), f(a[1]));
/**
 * Rigorous-style enclosure of an expression over a box {sym:[lo,hi]}.
 * Returns {lo, hi, issues[]} where issues list any place the value can leave the reals or diverge.
 */
export function bound(e, box) {
  const issues = [];
  const go = u => {
    switch (u.t) {
      case 'num': return I(u.v, u.v);
      case 'sym': {
        if (u.n in CONSTS) return I(CONSTS[u.n], CONSTS[u.n]);
        const b = box[u.n];
        if (!b) { issues.push({ kind: 'unbounded-input', at: u.n, text: `${u.n} has no declared range` }); return I(-Infinity, Infinity); }
        return I(b[0], b[1]);
      }
      case 'neg': { const a = go(u.a); return I(-a[1], -a[0]); }
      case 'op': {
        const a = go(u.a), b = go(u.b);
        switch (u.o) {
          case '+': return I(a[0] + b[0], a[1] + b[1]);
          case '-': return I(a[0] - b[1], a[1] - b[0]);
          case '*': return iMul(a, b);
          case '/': {
            if (b[0] <= 0 && b[1] >= 0) {
              issues.push({ kind: 'division-by-zero', at: toText(u.b), node: u, text: `Denominator ${toText(u.b)} can reach zero` });
              return I(-Infinity, Infinity);
            }
            return iMul(a, I(1 / b[1], 1 / b[0]));
          }
          case '^': {
            if (b[0] === b[1]) {
              const p = b[0];
              if (Number.isInteger(p)) {
                if (p < 0 && a[0] <= 0 && a[1] >= 0) {
                  issues.push({ kind: 'division-by-zero', at: toText(u.a), node: u, text: `${toText(u.a)} raised to a negative power can reach zero` });
                  return I(-Infinity, Infinity);
                }
                const c = [Math.pow(a[0], p), Math.pow(a[1], p)];
                if (p % 2 === 0 && a[0] < 0 && a[1] > 0) return I(p > 0 ? 0 : Math.min(...c), Math.max(...c));
                return I(Math.min(...c), Math.max(...c));
              }
              if (a[0] < 0) { issues.push({ kind: 'complex-value', at: toText(u.a), node: u, text: `${toText(u.a)} can be negative under a fractional power` }); return I(-Infinity, Infinity); }
              if (p < 0 && a[0] <= 0) { issues.push({ kind: 'division-by-zero', at: toText(u.a), node: u, text: `${toText(u.a)} raised to a negative power can reach zero` }); return I(-Infinity, Infinity); }
              const c = [Math.pow(a[0], p), Math.pow(a[1], p)];
              return I(Math.min(...c), Math.max(...c));
            }
            if (a[0] <= 0) { issues.push({ kind: 'complex-value', at: toText(u.a), node: u, text: `Base ${toText(u.a)} of a variable power can be non-positive` }); return I(-Infinity, Infinity); }
            const c = [Math.pow(a[0], b[0]), Math.pow(a[0], b[1]), Math.pow(a[1], b[0]), Math.pow(a[1], b[1])];
            return I(Math.min(...c), Math.max(...c));
          }
        }
        break;
      }
      case 'fn': {
        if (DIFF_OPS.has(u.n)) { u.args.forEach(go); return I(-Infinity, Infinity); }
        const a = go(u.args[0]);
        switch (u.n) {
          case 'sqrt':
            if (a[0] < 0) { issues.push({ kind: 'complex-value', at: toText(u.args[0]), node: u, text: `Argument of sqrt, ${toText(u.args[0])}, can be negative` }); return I(0, Math.sqrt(Math.max(a[1], 0))); }
            return mono(Math.sqrt)(a);
          case 'ln': case 'log': case 'log10':
            if (a[0] <= 0) { issues.push({ kind: 'log-singularity', at: toText(u.args[0]), node: u, text: `Argument of ${u.n}, ${toText(u.args[0])}, can reach zero or below` }); return I(-Infinity, Infinity); }
            return mono(FN1[u.n])(a);
          case 'exp': {
            const r = mono(Math.exp)(a);
            if (!isFinite(r[1])) issues.push({ kind: 'overflow', at: toText(u.args[0]), node: u, text: `exp(${toText(u.args[0])}) overflows on the declared range` });
            return r;
          }
          case 'sinh': return mono(Math.sinh)(a);
          case 'asinh': return mono(Math.asinh)(a);
          case 'acosh': if (a[0] < 1) issues.push({ kind: 'complex-value', at: toText(u.args[0]), node: u, text: `Argument of acosh, ${toText(u.args[0])}, can fall below 1` }); return I(0, Math.acosh(Math.max(a[1], 1)));
          case 'atanh': if (a[0] <= -1 || a[1] >= 1) { issues.push({ kind: 'pole', at: toText(u.args[0]), node: u, text: `Argument of atanh, ${toText(u.args[0])}, can reach ±1` }); return I(-Infinity, Infinity); } return mono(Math.atanh)(a);
          case 'tanh': return mono(Math.tanh)(a);
          case 'atan': return mono(Math.atan)(a);
          case 'erf': return mono(erf)(a);
          case 'cosh': { const c = [Math.cosh(a[0]), Math.cosh(a[1])]; return I(a[0] <= 0 && a[1] >= 0 ? 1 : Math.min(...c), Math.max(...c)); }
          case 'abs': { const c = [Math.abs(a[0]), Math.abs(a[1])]; return I(a[0] <= 0 && a[1] >= 0 ? 0 : Math.min(...c), Math.max(...c)); }
          case 'sin': case 'cos': {
            if (a[1] - a[0] >= 2 * Math.PI || !isFinite(a[0]) || !isFinite(a[1])) return I(-1, 1);
            const f = FN1[u.n]; let lo = Math.min(f(a[0]), f(a[1])), hi = Math.max(f(a[0]), f(a[1]));
            const shift = u.n === 'sin' ? Math.PI / 2 : 0;
            for (let k = Math.ceil((a[0] - shift) / Math.PI); k * Math.PI + shift <= a[1]; k++) { const v = f(k * Math.PI + shift); lo = Math.min(lo, v); hi = Math.max(hi, v); }
            return I(lo, hi);
          }
          case 'tan': {
            const k = Math.ceil((a[0] - Math.PI / 2) / Math.PI);
            if (k * Math.PI + Math.PI / 2 <= a[1] || !isFinite(a[0]) || !isFinite(a[1])) { issues.push({ kind: 'pole', at: toText(u.args[0]), node: u, text: `tan(${toText(u.args[0])}) has a pole on the declared range` }); return I(-Infinity, Infinity); }
            return mono(Math.tan)(a);
          }
          case 'asin': case 'acos':
            if (a[0] < -1 || a[1] > 1) issues.push({ kind: 'complex-value', at: toText(u.args[0]), node: u, text: `Argument of ${u.n} can leave [-1, 1]` });
            return u.n === 'asin' ? I(-Math.PI / 2, Math.PI / 2) : I(0, Math.PI);
          case 'sign': return I(-1, 1);
          case 'heaviside': return I(0, 1);
          case 'floor': return I(Math.floor(a[0]), Math.floor(a[1]));
          case 'min': { const b = go(u.args[1]); return I(Math.min(a[0], b[0]), Math.min(a[1], b[1])); }
          case 'max': { const b = go(u.args[1]); return I(Math.max(a[0], b[0]), Math.max(a[1], b[1])); }
          case 'atan2': go(u.args[1]); return I(-Math.PI, Math.PI);
          case 'ifpos': { const p1 = go(u.args[1]), p2 = go(u.args[2]); return I(Math.min(p1[0], p2[0]), Math.max(p1[1], p2[1])); }
          case 'pow': return go(op('^', u.args[0], u.args[1]));
          default: return I(-Infinity, Infinity);
        }
      }
    }
    return I(-Infinity, Infinity);
  };
  const r = go(P(e));
  return { lo: r[0], hi: r[1], issues };
}

/**
 * Replace every term that can diverge on the declared box by a bounded, infinitely
 * differentiable surrogate controlled by a small scale `eps` (same dimension as the
 * offending sub-expression):
 *    a / b      ->  a·b / (b² + eps²)            |·| ≤ |a| / (2 eps)
 *    ln(x)      ->  ln(sqrt(x² + eps²))           finite for every real x
 *    sqrt(x)    ->  sqrt(sqrt(x² + eps²))         real for every real x
 *    x^(-n)     ->  (x / (x² + eps²))^n
 * The surrogate agrees with the original to O(eps²/b²) away from the singular set.
 */
export function regularise(e, box, epsName = 'eps_reg') {
  let changed = 0;
  const soft = b => op('+', op('^', b, num(2)), op('^', sym(epsName), num(2)));
  const go = u => {
    switch (u.t) {
      case 'neg': return neg(go(u.a));
      case 'op': {
        const a = go(u.a), b = go(u.b);
        if (u.o === '/') {
          const bb = bound(u.b, box);
          if ((bb.lo <= 0 && bb.hi >= 0) || bb.issues.length) { changed++; return op('/', op('*', a, b), soft(b)); }
        }
        if (u.o === '^' && u.b.t === 'num' && u.b.v < 0) {
          const ab = bound(u.a, box);
          if (ab.lo <= 0 && ab.hi >= 0) { changed++; return op('^', op('/', a, soft(a)), num(-u.b.v)); }
        }
        if (u.o === '^' && u.b.t === 'neg' && u.b.a.t === 'num') {
          const ab = bound(u.a, box);
          if (ab.lo <= 0 && ab.hi >= 0) { changed++; return op('^', op('/', a, soft(a)), num(u.b.a.v)); }
        }
        return op(u.o, a, b);
      }
      case 'fn': {
        const args = u.args.map(go);
        if (u.n === 'ln' || u.n === 'log' || u.n === 'log10') {
          const ab = bound(u.args[0], box);
          if (ab.lo <= 0) { changed++; return fn(u.n, fn('sqrt', soft(args[0]))); }
        }
        if (u.n === 'sqrt') {
          const ab = bound(u.args[0], box);
          if (ab.lo < 0) { changed++; return fn('sqrt', fn('sqrt', soft(args[0]))); }
        }
        return fn(u.n, ...args);
      }
      default: return u;
    }
  };
  const out = go(P(e));
  return { expr: out, changed };
}

// ---------------------------------------------------------------- printing
const GREEK = {
  alpha: '\\alpha', beta: '\\beta', gamma: '\\gamma', delta: '\\delta', epsilon: '\\varepsilon', eps: '\\varepsilon', zeta: '\\zeta',
  eta: '\\eta', theta: '\\theta', kappa: '\\kappa', lambda: '\\lambda', mu: '\\mu', nu: '\\nu', xi: '\\xi', rho: '\\rho',
  sigma: '\\sigma', tau: '\\tau', phi: '\\varphi', chi: '\\chi', psi: '\\psi', omega: '\\omega', Gamma: '\\Gamma', Delta: '\\Delta',
  Theta: '\\Theta', Lambda: '\\Lambda', Sigma: '\\Sigma', Phi: '\\Phi', Psi: '\\Psi', Omega: '\\Omega', hbar: '\\hbar', ell: '\\ell',
  nabla: '\\nabla', infty: '\\infty', pi: '\\pi', Pi: '\\Pi', upsilon: '\\upsilon', iota: '\\iota',
};
export function symTex(name, overrides) {
  if (overrides && overrides[name]) return overrides[name];
  const parts = name.split('_');
  const head = parts[0];
  let base = GREEK[head] || (head.length > 1 && !/^[A-Z][a-z]$/.test(head) ? `\\mathrm{${head}}` : head);
  // dotted / primed conventions: xdot -> \dot{x}, xddot -> \ddot{x}
  const md = /^(.+?)(ddot|dot|bar|hat|tilde)$/.exec(head);
  if (md && md[1].length <= 6) { const inner = GREEK[md[1]] || md[1]; base = `\\${md[2]}{${inner}}`; }
  if (parts.length > 1) {
    const sub = parts.slice(1).map(p => GREEK[p] || (p.length > 1 ? `\\mathrm{${p}}` : p)).join(',');
    return `${base}_{${sub}}`;
  }
  return base;
}

const prec = e => (e.t === 'op' ? { '+': 1, '-': 1, '*': 2, '/': 2, '^': 4 }[e.o] : e.t === 'neg' ? 3 : 9);
const texNum = v => {
  if (Number.isInteger(v) && Math.abs(v) < 1e6) return String(v);
  const a = Math.abs(v);
  if (a >= 1e5 || (a < 1e-3 && a > 0)) { const [m, x] = v.toExponential(4).split('e'); const mm = parseFloat(m); return (mm === 1 ? '' : `${mm}\\times `) + `10^{${parseInt(x, 10)}}`; }
  return String(parseFloat(v.toPrecision(6)));
};
export function toTex(e, sy) {
  e = P(e);
  const T = u => toTex(u, sy);
  const par = (u, p) => (prec(u) < p ? `\\left(${T(u)}\\right)` : T(u));
  switch (e.t) {
    case 'num': return texNum(e.v);
    case 'sym': return symTex(e.n, sy);
    case 'neg': return `-${par(e.a, 3)}`;
    case 'op':
      switch (e.o) {
        case '+': return `${T(e.a)} + ${T(e.b)}`;
        case '-': return `${T(e.a)} - ${par(e.b, 2)}`;
        case '*': {
          const l = par(e.a, 2), r = par(e.b, 2);
          const needDot = /\d$/.test(l) && /^\d/.test(r);
          return `${l}${needDot ? ' \\cdot ' : '\\,'}${r}`;
        }
        case '/': return `\\frac{${T(e.a)}}{${T(e.b)}}`;
        case '^': {
          if (e.b.t === 'num' && e.b.v === 0.5) return `\\sqrt{${T(e.a)}}`;
          const base = e.a.t === 'sym' || e.a.t === 'num' ? T(e.a) : e.a.t === 'fn' && !DIFF_OPS.has(e.a.n) && e.a.n !== 'sqrt' && e.a.n !== 'abs' ? null : `\\left(${T(e.a)}\\right)`;
          if (base === null) return `\\${texFn(e.a.n)}^{${T(e.b)}}\\!\\left(${T(e.a.args[0])}\\right)`;
          return `${base}^{${T(e.b)}}`;
        }
      }
      break;
    case 'fn': {
      const a = e.args.map(T);
      switch (e.n) {
        case 'sqrt': return `\\sqrt{${a[0]}}`;
        case 'abs': return `\\left|${a[0]}\\right|`;
        case 'exp': return e.args[0].t === 'sym' || e.args[0].t === 'num' ? `e^{${a[0]}}` : `\\exp\\!\\left(${a[0]}\\right)`;
        case 'd': return `\\frac{\\mathrm{d}${wrapD(e.args[0], sy)}}{\\mathrm{d}${a[1]}}`;
        case 'd2': return `\\frac{\\mathrm{d}^2${wrapD(e.args[0], sy)}}{\\mathrm{d}${a[1]}^2}`;
        case 'pd': return `\\frac{\\partial ${wrapD(e.args[0], sy)}}{\\partial ${a[1]}}`;
        case 'pd2': return `\\frac{\\partial^2 ${wrapD(e.args[0], sy)}}{\\partial ${a[1]}^2}`;
        case 'lap': return `\\nabla^2 ${wrapD(e.args[0], sy)}`;
        case 'grad': return `\\nabla ${wrapD(e.args[0], sy)}`;
        case 'div': return `\\nabla\\!\\cdot\\!${wrapD(e.args[0], sy)}`;
        case 'curl': return `\\nabla\\!\\times\\!${wrapD(e.args[0], sy)}`;
        case 'int': return `\\int ${a[0]}\\,\\mathrm{d}${a[1]}`;
        case 'mat': return `\\frac{\\mathrm{D}${wrapD(e.args[0], sy)}}{\\mathrm{D}t}`;
        case 'pow': return `${par(e.args[0], 5)}^{${a[1]}}`;
        case 'heaviside': return `H\\!\\left(${a[0]}\\right)`;
        case 'ifpos': return `\\begin{cases}${a[1]} & ${a[0]} > 0\\\\ ${a[2]} & \\text{otherwise}\\end{cases}`;
        case 'min': case 'max': return `\\${e.n}\\!\\left(${a.join(',\\,')}\\right)`;
        default: return `\\${texFn(e.n)}\\!\\left(${a.join(',\\,')}\\right)`;
      }
    }
  }
  return '?';
}
const texFn = n => ({ ln: 'ln', log: 'ln', log10: 'log_{10}', asin: 'arcsin', acos: 'arccos', atan: 'arctan', asinh: 'operatorname{arsinh}', acosh: 'operatorname{arcosh}', atanh: 'operatorname{artanh}', atan2: 'operatorname{atan2}', erf: 'operatorname{erf}', sign: 'operatorname{sgn}', floor: 'operatorname{floor}' }[n] || n);
const wrapD = (u, sy) => (u.t === 'sym' ? toTex(u, sy) : `\\left(${toTex(u, sy)}\\right)`);

export function toText(e) {
  e = P(e);
  const par = (u, p) => (prec(u) < p ? `(${toText(u)})` : toText(u));
  switch (e.t) {
    case 'num': return String(parseFloat(e.v.toPrecision(10)));
    case 'sym': return e.n;
    case 'neg': return `-${par(e.a, 3)}`;
    case 'op': return e.o === '^' ? `${par(e.a, 5)}^${par(e.b, 5)}` : `${par(e.a, prec(e))} ${e.o} ${par(e.b, prec(e) + (e.o === '-' || e.o === '/' ? 1 : 0))}`;
    case 'fn': return `${e.n}(${e.args.map(toText).join(', ')})`;
  }
  return '?';
}

const CODE = {
  js: { pow: (a, b) => `Math.pow(${a},${b})`, fn: n => (n === 'erf' ? 'erf' : n === 'ln' || n === 'log' ? 'Math.log' : n === 'heaviside' ? '(x=>x>=0?1:0)' : `Math.${n}`), pi: 'Math.PI' },
  python: { pow: (a, b) => `${a}**${b}`, fn: n => ({ ln: 'np.log', log: 'np.log', log10: 'np.log10', abs: 'np.abs', asin: 'np.arcsin', acos: 'np.arccos', atan: 'np.arctan', asinh: 'np.arcsinh', acosh: 'np.arccosh', atanh: 'np.arctanh', atan2: 'np.arctan2', min: 'np.minimum', max: 'np.maximum', erf: 'math.erf', heaviside: '(lambda x: np.heaviside(x, 1.0))', pow: 'np.power' }[n] || `np.${n}`), pi: 'np.pi' },
  matlab: { pow: (a, b) => `${a}.^${b}`, fn: n => ({ ln: 'log', log: 'log', pow: 'power', heaviside: '(@(x) double(x>=0))' }[n] || n), pi: 'pi', mul: '.*', div: './' },
  cpp: { pow: (a, b) => `std::pow(${a}, ${b})`, fn: n => ({ ln: 'std::log', log: 'std::log', abs: 'std::fabs', min: 'std::min', max: 'std::max', heaviside: '([](double x){return x>=0?1.0:0.0;})', sign: '([](double x){return (x>0)-(x<0);})' }[n] || `std::${n}`), pi: 'M_PI', numFloat: true },
  lean: { pow: (a, b) => `${a} ^ ${b}`, fn: n => ({ sqrt: 'Real.sqrt', exp: 'Real.exp', ln: 'Real.log', log: 'Real.log', sin: 'Real.sin', cos: 'Real.cos', tan: 'Real.tan', tanh: 'Real.tanh', sinh: 'Real.sinh', cosh: 'Real.cosh', atan: 'Real.arctan', asin: 'Real.arcsin', acos: 'Real.arccos', log10: 'Real.logb 10', abs: 'abs', min: 'min', max: 'max' }[n] || unsupportedLean(n)), pi: 'Real.pi', lean: true },
};
/** Translate to source code in a target language (js | python | matlab | cpp | lean). */
export function toCode(e, lang = 'python', rename = n => n) {
  e = P(e);
  const L = CODE[lang];
  const go = (u, p = 0) => {
    const wrap = (s, q) => (q < p ? `(${s})` : s);
    switch (u.t) {
      case 'num': {
        if (L.lean) return u.v < 0 ? `(${leanNum(u.v)})` : leanNum(u.v);
        if (L.numFloat && Number.isInteger(u.v)) return `${u.v}.0`;
        return String(u.v);
      }
      case 'sym': return u.n === 'pi' ? L.pi : rename(u.n);
      case 'neg': return wrap(`-${go(u.a, 3)}`, 3);
      case 'op': {
        if (u.o === '^') {
          if (L.lean) {
            const isNat = u.b.t === 'num' && Number.isInteger(u.b.v) && u.b.v >= 0;
            return wrap(isNat ? `${go(u.a, 5)} ^ ${u.b.v}` : `Real.rpow ${go(u.a, 9)} ${go(u.b, 9)}`, isNat ? 4 : 8);
          }
          return lang === 'js' || lang === 'cpp' ? L.pow(go(u.a), go(u.b)) : wrap(L.pow(go(u.a, 5), go(u.b, 5)), 4);
        }
        const q = u.o === '+' || u.o === '-' ? 1 : 2;
        const sign = u.o === '*' && L.mul ? L.mul : u.o === '/' && L.div ? L.div : u.o;
        return wrap(`${go(u.a, q)} ${sign} ${go(u.b, q + (u.o === '-' || u.o === '/' ? 1 : 0))}`, q);
      }
      case 'fn': {
        if (DIFF_OPS.has(u.n)) throw new Error(`Differential operator ${u.n}() has no direct code form`);
        if (u.n === 'ifpos') {
          const [c, x, y] = u.args.map(q => go(q));
          if (L.lean) return `(if 0 < ${c} then ${x} else ${y})`;
          if (lang === 'python') return `np.where(${c} > 0, ${x}, ${y})`;
          if (lang === 'matlab') return `((${c}) > 0) .* (${x}) + ((${c}) <= 0) .* (${y})`;
          return `((${c}) > 0 ? (${x}) : (${y}))`;
        }
        if (L.lean) return wrap(`${L.fn(u.n)} ${u.args.map(a => go(a, 9)).join(' ')}`, 8);
        return `${L.fn(u.n)}(${u.args.map(a => go(a)).join(', ')})`;
      }
    }
    return '?';
  };
  return go(e);
}
function unsupportedLean(n) { throw new Error(`${n}() has no counterpart in the proof library`); }
function leanNum(v) {
  if (Number.isInteger(v)) return `(${v} : ℝ)`;
  // exact decimal as a rational so Lean treats it as a real literal without floats
  let s = v.toPrecision(12);
  if (/e/.test(s)) { const [m, x] = s.split('e'); const k = parseInt(x, 10); const mm = parseFloat(m); return k >= 0 ? `(${mm} * 10 ^ ${k} : ℝ)` : `(${mm} / 10 ^ ${-k} : ℝ)`; }
  return `(${parseFloat(s)} : ℝ)`;
}

/** Collect denominators, log and root arguments: the places where an expression may fail to be finite. */
export function criticalTerms(e) {
  const out = [];
  const go = u => {
    if (u.t === 'op') {
      go(u.a); go(u.b);
      if (u.o === '/') out.push({ kind: 'denominator', expr: u.b });
      if (u.o === '^' && ((u.b.t === 'num' && u.b.v < 0) || u.b.t === 'neg')) out.push({ kind: 'denominator', expr: u.a });
      if (u.o === '^' && u.b.t === 'num' && !Number.isInteger(u.b.v)) out.push({ kind: 'root', expr: u.a });
    } else if (u.t === 'neg') go(u.a);
    else if (u.t === 'fn') {
      u.args.forEach(go);
      if (u.n === 'sqrt') out.push({ kind: 'root', expr: u.args[0] });
      if (u.n === 'ln' || u.n === 'log' || u.n === 'log10') out.push({ kind: 'log', expr: u.args[0] });
    }
  };
  go(P(e));
  return out;
}

export const equal = (a, b) => toText(P(a)) === toText(P(b));
