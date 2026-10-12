// Last-resort model synthesis for prompts that match nothing in the library or the formula atlas.
// The quantities stated in the prompt, together with the kind of answer asked for ("how long",
// "how fast", "what force"…), are combined by dimensional analysis (Buckingham Π) into the only
// product of powers that has the right units. The result is an order-of-magnitude scaling law with
// an unknown pure number in front; it is presented as exactly that.
import { dimensionalLaw, piToExpr } from '../core/discover.js';
import { dimEq, isDimless, dimToSI, quantityName } from '../core/units.js';

const d = (M = 0, L = 0, T = 0, I = 0, Th = 0) => [M, L, T, I, Th, 0, 0];
const TARGETS = [
  [/how long (does|will|would|until|before|to|it|for)|how much time|what time|duration|time taken|time to\b|period of/i, 't_x', 'Time', d(0, 0, 1), 's'],
  [/how fast|what speed|what velocity|how quickly|speed of|velocity of/i, 'v_x', 'Speed', d(0, 1, -1), 'm/s'],
  [/how far|how high|how deep|how long is|how tall|how big|what distance|what height|what size|what length|wavelength|radius of|diameter of/i, 'L_x', 'Length', d(0, 1), 'm'],
  [/how often|what frequency|frequency of|how many times per|oscillat|vibrat/i, 'f_x', 'Frequency', d(0, 0, -1), '1/s'],
  [/what force|how much force|how hard|force (on|needed|required|of)|thrust|tension in/i, 'F_x', 'Force', d(1, 1, -2), 'N'],
  [/what pressure|how much pressure|pressure (in|on|of|at)|stress in/i, 'p_x', 'Pressure', d(1, -1, -2), 'Pa'],
  [/how much energy|what energy|energy (of|needed|required|released|stored)|how much work|how much heat/i, 'E_x', 'Energy', d(1, 2, -2), 'J'],
  [/how much power|what power|power (of|needed|required|output)|how powerful/i, 'P_x', 'Power', d(1, 2, -3), 'W'],
  [/how heavy|what mass|how much mass|mass of|how much does .* weigh/i, 'm_x', 'Mass', d(1), 'kg'],
  [/what acceleration|how quickly does .* accelerate|acceleration of|deceleration/i, 'a_x', 'Acceleration', d(0, 1, -2), 'm/s^2'],
  [/flow rate|how much (water|fluid|gas|air|oil) (flows|passes)|discharge/i, 'Q_x', 'Volumetric flow rate', d(0, 3, -1), 'm^3/s'],
  [/what voltage|how many volts|voltage (across|of|needed)/i, 'V_x', 'Voltage', d(1, 2, -3, -1), 'V'],
  [/what current|how many amps|current (through|in|of)/i, 'I_x', 'Current', d(0, 0, 0, 1), 'A'],
];
const LETTER = [[d(0, 1), 'L'], [d(0, 0, 1), 't'], [d(1), 'm'], [d(0, 1, -1), 'v'], [d(0, 1, -2), 'a'], [d(1, 1, -2), 'F'], [d(1, -1, -2), 'p'], [d(1, 2, -2), 'E'], [d(1, 2, -3), 'P'], [d(1, -3), 'rho'], [d(0, 0, 0, 0, 1), 'T'], [d(0, 0, -1), 'f'], [d(1, -1, -1), 'mu'], [d(0, 2), 'A'], [d(0, 3), 'V'], [d(0, 2, -1), 'nu'], [d(1, 0, -2), 'k'], [d(0, 3, -1), 'Q'], [d(1, 2, -3, -1), 'U'], [d(0, 0, 0, 1), 'I'], [d(1, 2, -3, -2), 'R']];
const CONTEXT = [
  [/fall|drop|weight|weigh|gravity|heavy|lift|climb|pendulum|swing|slope|slide|float|sink|pour|drain|wave|ripple|tide|jump|throw|land|orbit|topple|tip over|tips over|bounce|hang|pond|lake|pool|roll down|downhill|siphon|splash/i, 'g', 'Gravitational acceleration', d(0, 1, -2), 'm/s^2', 9.80665],
  [/light|laser|photon|radio|electromagnetic|relativ/i, 'c_l', 'Speed of light', d(0, 1, -1), 'm/s', 299792458],
  [/water|sea|ocean|river|rain|swim|boat|ship|wet|liquid/i, 'rho_w', 'Density of water', d(1, -3), 'kg/m^3', 1000],
  [/\bair\b|wind|atmosphere|breath|fly|flying|flight|aircraft|bird|parachute/i, 'rho_a', 'Density of air', d(1, -3), 'kg/m^3', 1.225],
];

/** Returns {equations, symbols, note, text} or null when no dimensionally admissible combination exists. */
export function dimensionalEstimate(prompt, extracted) {
  const tgt = TARGETS.find(([re]) => re.test(prompt)); if (!tgt) return null;
  const [, tSym, tName, tDim, tUnit] = tgt;
  const counts = {}, qs = [];
  (extracted || []).filter(q => !q.bare && !isDimless(q.dim)).slice(0, 6).forEach(q => {
    const base = (LETTER.find(([dd]) => dimEq(dd, q.dim)) || [0, 'q'])[1]; counts[base] = (counts[base] || 0) + 1;
    qs.push({ sym: `${base}_${counts[base]}`, dim: q.dim, value: q.si, name: `${quantityName(q.dim)} stated in your prompt (${q.raw})`, unit: dimToSI(q.dim).replace(/·/g, ' '), user: true });
  });
  CONTEXT.forEach(([re, s, name, dim, unit, value]) => { if (re.test(prompt) && !qs.some(q => dimEq(q.dim, dim) && s !== 'g')) qs.push({ sym: s, dim, value, name, unit, user: false }); });
  if (qs.length < 1) return null;
  // try the full set first, then drop context quantities one at a time until a combination exists
  let use = qs.slice(), law = null;
  for (let k = 0; k < 4 && use.length; k++) {
    try { law = dimensionalLaw({ sym: tSym, dim: tDim }, use.map(q => ({ sym: q.sym, dim: q.dim }))); } catch { law = null; }
    if (law && law.ok) break;
    const i = use.map(q => q.user).lastIndexOf(false); if (i < 0) break; use.splice(i, 1); law = null;
  }
  if (!law || !law.ok) return null;
  const used = use.filter(q => q.sym in law.exponents);
  if (!used.some(q => q.user)) return null; // an estimate built only from assumed context would be an invention
  const symbols = { C_0: { name: 'Pure number of order one — unknown; fix it from theory or one measurement', unit: '1', value: 1, min: 0.1, max: 10, src: 'Dimensional analysis cannot determine this number' }, [tSym]: { name: `${tName} (order-of-magnitude estimate)`, unit: tUnit } };
  used.forEach(q => { symbols[q.sym] = { name: q.name, unit: q.unit, value: q.value, min: q.value > 0 ? q.value / 10 : q.value * 10, max: q.value > 0 ? q.value * 10 : q.value / 10, src: q.user ? 'From your prompt' : 'Reference value assumed from the context of the prompt', prov: q.user ? 'USER' : undefined }; });
  return {
    equations: [{ lhs: tSym, rhs: law.rhs, name: `${tName}: scaling law from dimensional analysis`, origin: 'Buckingham Π theorem applied to the quantities in the prompt', kind: 'hypothesis' }], symbols,
    note: `Nothing in the library or among the standard relations covers this question, so an order-of-magnitude estimate was built by dimensional analysis: the only combination of ${used.map(q => q.sym).join(', ')} with the units of ${tName.toLowerCase()}. ${law.unique ? 'The form is fixed by dimensions; only the pure number C₀ in front is unknown (taken as 1).' : `Dimensions alone do not fix the form completely: it may also depend on ${law.remaining.map(piToExpr).join(', ')}.`} Treat the result as a scale, not a prediction.`,
  };
}
