// Physical dimensions and units.
// A dimension is a 7-vector of exponents over the SI base quantities
// [mass, length, time, current, temperature, amount, luminous intensity].

export const BASE = ['M', 'L', 'T', 'I', 'Θ', 'N', 'J'];
export const BASE_SI = ['kg', 'm', 's', 'A', 'K', 'mol', 'cd'];
export const D0 = [0, 0, 0, 0, 0, 0, 0];

const d = (M = 0, L = 0, T = 0, I = 0, Th = 0, N = 0, J = 0) => [M, L, T, I, Th, N, J];
export const dimMul = (a, b) => a.map((x, i) => x + b[i]);
export const dimDiv = (a, b) => a.map((x, i) => x - b[i]);
export const dimPow = (a, p) => a.map(x => x * p);
export const dimEq = (a, b) => a.every((x, i) => Math.abs(x - b[i]) < 1e-9);
export const isDimless = a => a.every(x => Math.abs(x) < 1e-9);

const fmtExp = x => {
  if (Number.isInteger(x)) return String(x);
  for (const q of [2, 3, 4, 6]) if (Number.isInteger(Math.round(x * q * 1e6) / 1e6)) return `${Math.round(x * q)}/${q}`;
  return x.toFixed(3);
};
export function dimToString(a) {
  const parts = [];
  a.forEach((x, i) => { if (Math.abs(x) > 1e-9) parts.push(x === 1 ? BASE[i] : `${BASE[i]}^${fmtExp(x)}`); });
  return parts.length ? parts.join(' ') : '1';
}
export function dimToSI(a) {
  const num = [], den = [];
  a.forEach((x, i) => {
    if (Math.abs(x) < 1e-9) return;
    const e = Math.abs(x), s = e === 1 ? BASE_SI[i] : `${BASE_SI[i]}^${fmtExp(e)}`;
    (x > 0 ? num : den).push(s);
  });
  if (!num.length && !den.length) return '–';
  return (num.join('·') || '1') + (den.length ? '/' + (den.length > 1 ? '(' + den.join('·') + ')' : den[0]) : '');
}

// name -> [dimension, factor to SI, offset]
const U = {};
const def = (names, dim, f = 1, o = 0) => names.split(' ').forEach(n => { U[n] = { dim, f, o }; });

def('1 - – dimensionless ratio fraction', D0);
def('% percent', D0, 0.01); def('ppm', D0, 1e-6); def('ppb', D0, 1e-9);
def('rad radian radians', D0); def('deg ° degree degrees', D0, Math.PI / 180); def('rev', D0, 2 * Math.PI); def('sr', D0);
// mass
def('kg', d(1)); def('g gram grams', d(1), 1e-3); def('mg', d(1), 1e-6); def('ug µg μg', d(1), 1e-9);
def('t tonne tonnes te', d(1), 1e3); def('lb lbm lbs', d(1), 0.45359237); def('oz', d(1), 0.028349523125);
def('u amu Da', d(1), 1.66053906660e-27); def('Msun', d(1), 1.98847e30); def('Mearth', d(1), 5.9722e24);
// length
def('m metre metres meter meters', d(0, 1)); def('km', d(0, 1), 1e3); def('cm', d(0, 1), 1e-2); def('mm', d(0, 1), 1e-3);
def('um µm μm micron microns', d(0, 1), 1e-6); def('nm', d(0, 1), 1e-9); def('pm', d(0, 1), 1e-12); def('fm', d(0, 1), 1e-15);
def('Å angstrom', d(0, 1), 1e-10); def('in inch inches "', d(0, 1), 0.0254); def('ft foot feet', d(0, 1), 0.3048);
def('yd', d(0, 1), 0.9144); def('mi mile miles', d(0, 1), 1609.344); def('nmi', d(0, 1), 1852);
def('AU au', d(0, 1), 1.495978707e11); def('ly', d(0, 1), 9.4607304725808e15); def('pc', d(0, 1), 3.0856775814913673e16);
def('kpc', d(0, 1), 3.0856775814913673e19); def('Mpc', d(0, 1), 3.0856775814913673e22);
// time
def('s sec second seconds', d(0, 0, 1)); def('ms', d(0, 0, 1), 1e-3); def('us µs μs', d(0, 0, 1), 1e-6); def('ns', d(0, 0, 1), 1e-9);
def('ps', d(0, 0, 1), 1e-12); def('fs', d(0, 0, 1), 1e-15); def('min minute minutes', d(0, 0, 1), 60);
def('h hr hour hours', d(0, 0, 1), 3600); def('d day days', d(0, 0, 1), 86400); def('yr year years a', d(0, 0, 1), 3.15576e7);
def('Gyr', d(0, 0, 1), 3.15576e16); def('Myr', d(0, 0, 1), 3.15576e13);
// frequency
def('Hz', d(0, 0, -1)); def('kHz', d(0, 0, -1), 1e3); def('MHz', d(0, 0, -1), 1e6); def('GHz', d(0, 0, -1), 1e9); def('THz', d(0, 0, -1), 1e12);
def('rpm', d(0, 0, -1), 2 * Math.PI / 60); def('rad/s', d(0, 0, -1));
// temperature
def('K kelvin', d(0, 0, 0, 0, 1)); def('mK', d(0, 0, 0, 0, 1), 1e-3); def('uK µK', d(0, 0, 0, 0, 1), 1e-6);
def('°C degC C celsius', d(0, 0, 0, 0, 1), 1, 273.15);
def('°F degF fahrenheit', d(0, 0, 0, 0, 1), 5 / 9, 459.67 * 5 / 9); def('R degR', d(0, 0, 0, 0, 1), 5 / 9);
// amount, current, luminous
def('mol', d(0, 0, 0, 0, 0, 1)); def('kmol', d(0, 0, 0, 0, 0, 1), 1e3); def('mmol', d(0, 0, 0, 0, 0, 1), 1e-3);
def('A amp ampere', d(0, 0, 0, 1)); def('mA', d(0, 0, 0, 1), 1e-3); def('uA µA', d(0, 0, 0, 1), 1e-6); def('nA', d(0, 0, 0, 1), 1e-9); def('kA', d(0, 0, 0, 1), 1e3);
def('cd', d(0, 0, 0, 0, 0, 0, 1));
// force, pressure, energy, power
def('N newton', d(1, 1, -2)); def('kN', d(1, 1, -2), 1e3); def('MN', d(1, 1, -2), 1e6); def('mN', d(1, 1, -2), 1e-3); def('uN µN', d(1, 1, -2), 1e-6);
def('lbf', d(1, 1, -2), 4.4482216152605); def('kgf', d(1, 1, -2), 9.80665); def('dyn', d(1, 1, -2), 1e-5);
def('Pa pascal', d(1, -1, -2)); def('kPa', d(1, -1, -2), 1e3); def('MPa', d(1, -1, -2), 1e6); def('GPa', d(1, -1, -2), 1e9); def('hPa mbar', d(1, -1, -2), 100);
def('bar bara', d(1, -1, -2), 1e5); def('barg', d(1, -1, -2), 1e5, 1.01325); def('atm', d(1, -1, -2), 101325);
def('psi psia', d(1, -1, -2), 6894.757293168); def('ksi', d(1, -1, -2), 6894757.293168); def('psig', d(1, -1, -2), 6894.757293168, 14.695948775);
def('torr Torr mmHg', d(1, -1, -2), 133.322368421);
def('J joule', d(1, 2, -2)); def('kJ', d(1, 2, -2), 1e3); def('MJ', d(1, 2, -2), 1e6); def('GJ', d(1, 2, -2), 1e9); def('mJ', d(1, 2, -2), 1e-3);
def('eV', d(1, 2, -2), 1.602176634e-19); def('keV', d(1, 2, -2), 1.602176634e-16); def('MeV', d(1, 2, -2), 1.602176634e-13); def('GeV', d(1, 2, -2), 1.602176634e-10); def('meV', d(1, 2, -2), 1.602176634e-22);
def('cal', d(1, 2, -2), 4.184); def('kcal', d(1, 2, -2), 4184); def('Wh', d(1, 2, -2), 3600); def('kWh', d(1, 2, -2), 3.6e6); def('MWh', d(1, 2, -2), 3.6e9); def('BTU Btu', d(1, 2, -2), 1055.05585262);
def('W watt', d(1, 2, -3)); def('mW', d(1, 2, -3), 1e-3); def('uW µW', d(1, 2, -3), 1e-6); def('kW', d(1, 2, -3), 1e3); def('MW', d(1, 2, -3), 1e6); def('GW', d(1, 2, -3), 1e9); def('hp', d(1, 2, -3), 745.699871582);
// electromagnetic
def('C coulomb', d(0, 0, 1, 1)); def('mC', d(0, 0, 1, 1), 1e-3); def('uC µC', d(0, 0, 1, 1), 1e-6); def('nC', d(0, 0, 1, 1), 1e-9); def('pC', d(0, 0, 1, 1), 1e-12);
def('V volt', d(1, 2, -3, -1)); def('mV', d(1, 2, -3, -1), 1e-3); def('kV', d(1, 2, -3, -1), 1e3); def('MV', d(1, 2, -3, -1), 1e6); def('uV µV', d(1, 2, -3, -1), 1e-6);
def('ohm Ω Ohm', d(1, 2, -3, -2)); def('kohm kΩ', d(1, 2, -3, -2), 1e3); def('Mohm MΩ', d(1, 2, -3, -2), 1e6); def('mohm mΩ', d(1, 2, -3, -2), 1e-3);
def('S siemens', d(-1, -2, 3, 2)); def('mS', d(-1, -2, 3, 2), 1e-3); def('uS µS', d(-1, -2, 3, 2), 1e-6);
def('F farad', d(-1, -2, 4, 2)); def('mF', d(-1, -2, 4, 2), 1e-3); def('uF µF', d(-1, -2, 4, 2), 1e-6); def('nF', d(-1, -2, 4, 2), 1e-9); def('pF', d(-1, -2, 4, 2), 1e-12);
def('H henry', d(1, 2, -2, -2)); def('mH', d(1, 2, -2, -2), 1e-3); def('uH µH', d(1, 2, -2, -2), 1e-6); def('nH', d(1, 2, -2, -2), 1e-9);
def('T tesla', d(1, 0, -2, -1)); def('mT', d(1, 0, -2, -1), 1e-3); def('uT µT', d(1, 0, -2, -1), 1e-6); def('nT', d(1, 0, -2, -1), 1e-9); def('G gauss', d(1, 0, -2, -1), 1e-4);
def('Wb', d(1, 2, -2, -1));
// viscosity and others
def('P poise', d(1, -1, -1), 0.1); def('cP cp', d(1, -1, -1), 1e-3); def('St', d(0, 2, -1), 1e-4); def('cSt', d(0, 2, -1), 1e-6);
def('L l litre litres liter liters', d(0, 3), 1e-3); def('mL ml', d(0, 3), 1e-6); def('bbl', d(0, 3), 0.158987294928); def('gal', d(0, 3), 0.003785411784);
def('scf', d(0, 3), 0.028316846592); def('ha', d(0, 2), 1e4); def('darcy D_perm', d(0, 2), 9.869233e-13); def('mD', d(0, 2), 9.869233e-16);
def('kn knot knots kt', d(0, 1, -1), 0.514444444); def('mph', d(0, 1, -1), 0.44704); def('kph', d(0, 1, -1), 1 / 3.6);
def('g0 gee', d(0, 1, -2), 9.80665);
def('Bq', d(0, 0, -1)); def('kBq', d(0, 0, -1), 1e3); def('MBq', d(0, 0, -1), 1e6); def('GBq', d(0, 0, -1), 1e9); def('Ci', d(0, 0, -1), 3.7e10); def('Gy', d(0, 2, -2)); def('Sv', d(0, 2, -2)); def('mSv', d(0, 2, -2), 1e-3); def('uSv µSv', d(0, 2, -2), 1e-6);
def('M_conc molar', d(0, -3, 0, 0, 0, 1), 1e3); def('psu', D0, 1e-3); def('ppt', D0, 1e-3);
def('lm', d(0, 0, 0, 0, 0, 0, 1)); def('lx', d(0, -2, 0, 0, 0, 0, 1)); def('dB', D0); def('Np', D0);
def('barn', d(0, 2), 1e-28); def('kat', d(0, 0, -1, 0, 0, 1));

export const unitNames = () => Object.keys(U);

function tokenize(s) {
  const out = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (c === ' ' || c === '·' || c === '*' || c === '⋅' || c === '×') { out.push('*'); i++; continue; }
    if (c === '.' && !/\d/.test(s[i + 1] || '')) { out.push('*'); i++; continue; }
    if (c === '/' || c === '(' || c === ')' || c === '^') { out.push(c); i++; continue; }
    if (c === '²') { out.push('^', '2'); i++; continue; }
    if (c === '³') { out.push('^', '3'); i++; continue; }
    if (c === '⁻') { out.push('^'); let n = '-'; i++; while ('¹²³⁴'.includes(s[i])) { n += '¹²³⁴'.indexOf(s[i]) + 1; i++; } out.push(n); continue; }
    const mNum = /^-?\d+(\.\d+)?/.exec(s.slice(i));
    if (mNum) { out.push(mNum[0]); i += mNum[0].length; continue; }
    const mId = /^[A-Za-zµμΩÅ°%"–_][A-Za-zµμΩÅ°%_]*/.exec(s.slice(i));
    if (mId) {
      let id = mId[0];
      // "m3", "s2", "m-1" style exponents written without a caret
      const tail = /^-?\d+/.exec(s.slice(i + id.length));
      out.push(id); i += id.length;
      if (tail) { out.push('^', tail[0]); i += tail[0].length; }
      continue;
    }
    throw new Error(`Unrecognised unit character "${c}"`);
  }
  // collapse repeated multiplication signs
  return out.filter((t, k) => !(t === '*' && (k === 0 || out[k - 1] === '*' || out[k - 1] === '/' || out[k - 1] === '(')));
}

const cache = new Map();
/** Parse a unit string; returns {dim, f, o} or throws. */
export function parseUnit(str) {
  const s = String(str == null ? '' : str).trim();
  if (s === '' ) return { dim: D0, f: 1, o: 0 };
  if (cache.has(s)) return cache.get(s);
  if (U[s]) { cache.set(s, U[s]); return U[s]; }
  const t = tokenize(s);
  let p = 0;
  const atom = () => {
    const k = t[p];
    if (k === '(') { p++; const v = expr(); if (t[p] !== ')') throw new Error('Unbalanced parentheses in unit'); p++; return power(v); }
    if (k == null) throw new Error('Incomplete unit');
    p++;
    if (/^-?\d/.test(k)) return power({ dim: D0, f: parseFloat(k), o: 0 });
    const u = U[k];
    if (!u) throw new Error(`Unknown unit "${k}"`);
    return power({ dim: u.dim, f: u.f, o: 0, o1: u.o });
  };
  const power = v => {
    if (t[p] === '^') {
      p++;
      let e = t[p++];
      if (e === '(') { e = t[p++]; if (t[p] === '/') { p++; e = parseFloat(e) / parseFloat(t[p++]); } p++; }
      const n = typeof e === 'number' ? e : parseFloat(e);
      if (!isFinite(n)) throw new Error('Bad unit exponent');
      return { dim: dimPow(v.dim, n), f: Math.pow(v.f, n), o: 0 };
    }
    return v;
  };
  const expr = () => {
    let v = atom();
    while (p < t.length && t[p] !== ')') {
      if (t[p] === '*') { p++; if (p >= t.length || t[p] === ')') break; const b = atom(); v = { dim: dimMul(v.dim, b.dim), f: v.f * b.f, o: 0 }; }
      else if (t[p] === '/') { p++; const b = atom(); v = { dim: dimDiv(v.dim, b.dim), f: v.f / b.f, o: 0 }; }
      else { const b = atom(); v = { dim: dimMul(v.dim, b.dim), f: v.f * b.f, o: 0 }; }
    }
    return v;
  };
  const v = expr();
  if (p < t.length) throw new Error('Unexpected text in unit');
  const res = { dim: v.dim, f: v.f, o: t.length === 1 && v.o1 ? v.o1 : 0 };
  cache.set(s, res);
  return res;
}

export function tryUnit(str) { try { return parseUnit(str); } catch { return null; } }
export const toSI = (value, unit) => { const u = parseUnit(unit); return value * u.f + u.o; };
export const fromSI = (value, unit) => { const u = parseUnit(unit); return (value - u.o) / u.f; };
export function convert(value, from, to) {
  const a = parseUnit(from), b = parseUnit(to);
  if (!dimEq(a.dim, b.dim)) throw new Error(`Cannot convert ${from} to ${to}: different dimensions`);
  return (value * a.f + a.o - b.o) / b.f;
}
export const unitDim = unit => parseUnit(unit).dim;

/** Human-friendly number formatting used across the interface. */
export function fmt(x, sig = 4) {
  if (x == null || Number.isNaN(x)) return '—';
  if (!isFinite(x)) return x > 0 ? '∞' : '−∞';
  if (x === 0) return '0';
  const a = Math.abs(x);
  if (a >= 1e5 || a < 1e-3) {
    const [m, e] = x.toExponential(sig - 1).split('e');
    return `${parseFloat(m)}×10${sup(parseInt(e, 10))}`;
  }
  return String(parseFloat(x.toPrecision(sig)));
}
const SUP = { '-': '⁻', 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
const sup = n => String(n).split('').map(c => SUP[c]).join('');

/** Named dimensions for recognising what kind of quantity a number is. */
export const QUANTITY = [
  ['length', d(0, 1)], ['area', d(0, 2)], ['volume', d(0, 3)], ['time', d(0, 0, 1)], ['mass', d(1)],
  ['velocity', d(0, 1, -1)], ['acceleration', d(0, 1, -2)], ['force', d(1, 1, -2)], ['pressure / stress', d(1, -1, -2)],
  ['energy / work / torque', d(1, 2, -2)], ['power', d(1, 2, -3)], ['density', d(1, -3)], ['dynamic viscosity', d(1, -1, -1)],
  ['kinematic viscosity / diffusivity', d(0, 2, -1)], ['frequency / rate', d(0, 0, -1)], ['temperature', d(0, 0, 0, 0, 1)],
  ['mass flow rate', d(1, 0, -1)], ['volumetric flow rate', d(0, 3, -1)], ['electric current', d(0, 0, 0, 1)],
  ['electric charge', d(0, 0, 1, 1)], ['electric potential', d(1, 2, -3, -1)], ['electric field', d(1, 1, -3, -1)],
  ['resistance', d(1, 2, -3, -2)], ['capacitance', d(-1, -2, 4, 2)], ['inductance', d(1, 2, -2, -2)], ['magnetic flux density', d(1, 0, -2, -1)],
  ['thermal conductivity', d(1, 1, -3, 0, -1)], ['specific heat', d(0, 2, -2, 0, -1)], ['heat transfer coefficient', d(1, 0, -3, 0, -1)],
  ['surface tension / stiffness', d(1, 0, -2)], ['momentum', d(1, 1, -1)], ['angular momentum / action', d(1, 2, -1)],
  ['amount of substance', d(0, 0, 0, 0, 0, 1)], ['molar mass', d(1, 0, 0, 0, 0, -1)], ['concentration', d(0, -3, 0, 0, 0, 1)],
  ['heat flux / intensity', d(1, 0, -3)], ['dimensionless', D0],
];
export function quantityName(dim) {
  const q = QUANTITY.find(([, dd]) => dimEq(dd, dim));
  return q ? q[0] : dimToString(dim);
}
