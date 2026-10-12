// Marine, offshore, geotechnical and structural mechanics: ship resistance and stability, wave loading,
// moorings, vortex-induced vibration, pipes conveying fluid, on-bottom stability, foundations,
// consolidation, slopes, beams, columns, seismic response, fatigue and pressure vessels.
import { inp, asm, eq, scalar, line, anim, check, bench, svg, S, lab, N } from './kit.js';

const g = 9.80665;
const val = (r, s) => r.scalars.find(q => q.sym === s).value;
const DEG = Math.PI / 180;

/** Wave number from the linear dispersion relation, optionally Doppler-shifted by a following current U. */
function waveNumber(omega, d, U = 0, deep = false) {
  const disp = k => (deep ? g * k : g * k * Math.tanh(k * d));
  let k = omega * omega / g;
  if (!deep) {
    k = k / Math.sqrt(Math.tanh(k * d));
    for (let i = 0; i < 60; i++) {
      const th = Math.tanh(k * d), f = g * k * th - omega * omega, df = g * th + g * k * d * (1 - th * th);
      const kn = k - f / df;
      if (!(kn > 0)) break;
      if (Math.abs(kn - k) < 1e-14 * kn) { k = kn; break; }
      k = kn;
    }
  }
  if (U > 0) {
    const hi = Math.min(k, omega / U * (1 - 1e-12));
    const f = q => (omega - q * U) ** 2 - disp(q);
    if (f(1e-12) > 0 && f(hi) < 0) k = N.bisect(f, 1e-12, hi, 1e-13);
  }
  return k;
}
/** cosh(k(z+d))/sinh(kd) written so that it cannot overflow in deep water (z ≤ 0). */
const coshRatio = (k, z, d) => (Math.exp(k * z) + Math.exp(-k * (z + 2 * d))) / (1 - Math.exp(-2 * k * d));

// ------------------------------------------------------------------ ship resistance and power
const cfLine = (Re, ittc) => {
  const R = Math.max(Re, 1e5);
  let cf = 0.075 / (Math.log10(R) - 2) ** 2;
  if (ittc) return cf;
  for (let i = 0; i < 80; i++) { const n = (0.242 / Math.log10(R * cf)) ** 2; if (Math.abs(n - cf) < 1e-16) { cf = n; break; } cf = n; }
  return cf;
};
function shipPoint(v, a, V) {
  const vol = v.C_B * v.L * v.B * v.T;
  const Sw = a.denny ? 1.7 * v.L * v.T + vol / v.T : 2.6 * Math.sqrt(vol * v.L);
  const Fn = V / Math.sqrt(g * v.L), Re = V * v.L / v.nu, CF = cfLine(Re, a.ittc57);
  const k = a.form ? v.k_form : 0, CW = v.c_w * Fn ** 4, CT = (1 + k) * CF + CW + v.C_A;
  const q = 0.5 * v.rho * Sw * V * V;
  const RF = q * CF, RV = q * (1 + k) * CF, RW = q * CW, RA = q * v.C_A, RT = q * CT;
  const PE = RT * V, PS = PE / (v.eta_D * v.eta_S) * (a.calm ? 1 : 1 + v.s_m);
  return { vol, Sw, Fn, Re, CF, CW, CT, RF, RV, RW, RA, RT, PE, PS };
}
const shipResistance = {
  id: 'ship-resistance-power',
  title: 'Ship resistance and powering',
  module: 2, klass: 'I', domains: ['marine'],
  keywords: ['ship resistance', 'hull resistance', 'effective power', 'shaft power', 'ittc 1957', 'ittc', 'froude number', 'frictional resistance', 'wave-making resistance', 'wetted surface', 'form factor', 'speed-power curve', 'powering', 'ship', 'vessel', 'hull', 'knots'],
  summary: 'Calm-water resistance of a displacement ship from the ITTC-1957 friction line, a form factor and an adjustable Froude-number closure for wave-making, with effective and shaft power against speed.',
  background: [
    'The resistance of a ship in calm water is conventionally split, following Froude, into a viscous part that scales with Reynolds number and a wave-making part that scales with Froude number. The viscous part is estimated from a model–ship correlation line for a flat plate of the same length and wetted area, multiplied by a form factor that accounts for the three-dimensional hull shape.',
    'Wave-making resistance has no simple closed form. At speeds well below the main resistance hump it rises steeply, roughly as the sixth power of speed, so its coefficient varies as the fourth power of Froude number. That trend is used here with a single adjustable coefficient that must be calibrated against model tests, trials or a statistical method such as Holtrop and Mennen for the hull in question.',
  ],
  phenomena: ['Turbulent skin friction', 'Viscous pressure (form) drag', 'Wave-making', 'Hull roughness', 'Propulsive losses'],
  laws: ['momentum', 'energy'],
  refs: ['ITTC (1957). Proceedings of the 8th International Towing Tank Conference, Madrid: model–ship correlation line.', 'ITTC (1978). Report of the Performance Committee, 15th International Towing Tank Conference, The Hague: 1978 performance prediction method.', 'Molland, A. F., Turnock, S. R. & Hudson, D. A. (2011). Ship Resistance and Propulsion. Cambridge University Press.', 'Holtrop, J. & Mennen, G. G. J. (1982). An approximate power prediction method. International Shipbuilding Progress 29, 166–170.', 'Schoenherr, K. E. (1932). Resistance of flat surfaces moving through a fluid. Trans. SNAME 40, 279–313.'],
  inputs: [
    inp('L', 'Waterline length', 'm', 120, { min: 20, max: 400, kind: 'geometry', aliases: ['length', 'waterline length', 'lwl', 'long'] }),
    inp('B', 'Beam', 'm', 20, { min: 3, max: 70, kind: 'geometry', aliases: ['beam', 'breadth', 'wide'] }),
    inp('T', 'Draught', 'm', 8, { min: 1, max: 25, kind: 'geometry', aliases: ['draught', 'draft'] }),
    inp('C_B', 'Block coefficient', '1', 0.70, { min: 0.4, max: 0.9, kind: 'geometry', aliases: ['block coefficient', 'cb'] }),
    inp('V', 'Ship speed', 'kn', 15, { min: 2, max: 40, aliases: ['speed', 'knots', 'service speed'] }),
    inp('rho', 'Sea-water density', 'kg/m^3', 1025, { min: 990, max: 1040, kind: 'fluid', aliases: ['density'] }),
    inp('nu', 'Kinematic viscosity of sea water', 'm^2/s', 1.19e-6, { min: 0.8e-6, max: 1.9e-6, kind: 'fluid', aliases: ['kinematic viscosity'], src: 'Sea water at 15 °C, ITTC recommended properties' }),
    inp('k_form', 'Form factor k', '1', 0.2, { min: 0, max: 0.6, kind: 'geometry', aliases: ['form factor'], src: 'Typical 0.1–0.35 for merchant hull forms; found by the Prohaska method from low-speed model tests' }),
    inp('c_w', 'Wave-resistance coefficient c_w in C_W = c_w·Fn⁴', '1', 0.3, { min: 0, max: 3, kind: 'fluid', aliases: ['wave resistance coefficient', 'wave coefficient'], src: 'Calibration constant: fit to model-test, trial or Holtrop–Mennen data for the hull. The default gives C_W ≈ 0.8×10⁻³ at Fn = 0.23.' }),
    inp('C_A', 'Correlation (roughness) allowance', '1', 0.0004, { min: 0, max: 0.001, kind: 'fluid', aliases: ['correlation allowance', 'roughness allowance'] }),
    inp('eta_D', 'Quasi-propulsive efficiency', '1', 0.65, { min: 0.3, max: 0.85, aliases: ['propulsive efficiency', 'quasi-propulsive'] }),
    inp('eta_S', 'Shaft transmission efficiency', '1', 0.98, { min: 0.9, max: 1, aliases: ['shaft efficiency', 'transmission efficiency'] }),
    inp('s_m', 'Sea margin', '%', 15, { min: 0, max: 50, aliases: ['sea margin', 'service margin'] }),
  ],
  assumptions: [
    asm('ittc57', 'Skin friction follows the ITTC-1957 model–ship correlation line.', { why: 'Standard basis of resistance extrapolation', alt: 'The Schoenherr (ATTC 1947) flat-plate line 0.242/√C_F = log₁₀(Re·C_F) is solved instead.' }),
    asm('form', 'Viscous resistance is (1 + k) times the flat-plate friction (three-dimensional form-factor method).', { why: 'ITTC-1978 practice', alt: 'Froude\'s two-dimensional approach: k = 0, with all form effects left in the residuary coefficient.' }),
    asm('denny', 'Wetted surface is estimated with the Denny–Mumford formula S = 1.7·L·T + ∇/T.', { why: 'Needs only principal dimensions', alt: 'Taylor\'s formula S = 2.6·√(∇·L) is used.' }),
    asm('calm', 'Calm, deep water with a clean hull: no sea margin is applied.', { why: 'Trial condition', alt: 'Shaft power is increased by the stated sea margin for weather and fouling.' }),
  ],
  symbols: { Fn: ['Froude number', '1'], Re: ['Reynolds number', '1'], C_F: ['Frictional resistance coefficient', '1'], C_W: ['Wave-making resistance coefficient', '1'], C_T: ['Total resistance coefficient', '1'], S: ['Wetted surface area', 'm^2'], V_d: ['Displaced volume', 'm^3'], R_T: ['Total resistance', 'N'], P_E: ['Effective power', 'W'], P_S: ['Shaft power', 'W'] },
  equations: a => [
    eq('fn', 'Froude number', 'Fn', 'V/sqrt(g*L)', { kind: 'definition' }),
    eq('re', 'Reynolds number', 'Re', 'V*L/nu', { kind: 'definition' }),
    a.ittc57
      ? eq('cf', 'ITTC-1957 correlation line', 'C_F', '0.075/(log10(Re) - 2)^2', { kind: 'empirical', origin: 'ITTC (1957) model–ship correlation line', needs: ['ittc57'] })
      : eq('cf', 'Schoenherr friction line', '0.242/sqrt(C_F)', 'log10(Re*C_F)', { kind: 'empirical', origin: 'Schoenherr (1932); adopted by the ATTC in 1947' }),
    eq('vol', 'Displaced volume', 'V_d', 'C_B*L*B*T', { kind: 'definition' }),
    a.denny
      ? eq('ws', 'Wetted surface (Denny–Mumford)', 'S', '1.7*L*T + V_d/T', { kind: 'empirical', origin: 'Mumford\'s formula as given by Molland, Turnock & Hudson (2011)', needs: ['denny'] })
      : eq('ws', 'Wetted surface (Taylor)', 'S', '2.6*sqrt(V_d*L)', { kind: 'empirical', origin: 'Taylor\'s mean wetted-surface coefficient' }),
    eq('cw', 'Wave-making coefficient', 'C_W', 'c_w*Fn^4', { kind: 'empirical', origin: 'Low-speed trend R_W ∝ V⁶ with an adjustable coefficient; not a prediction method in its own right' }),
    a.form
      ? eq('ct', 'Total resistance coefficient', 'C_T', '(1 + k_form)*C_F + C_W + C_A', { kind: 'closure', origin: 'ITTC-1978 decomposition', needs: ['form'] })
      : eq('ct', 'Total resistance coefficient', 'C_T', 'C_F + C_W + C_A', { kind: 'closure', origin: 'Froude decomposition into frictional and residuary parts' }),
    eq('rt', 'Total resistance', 'R_T', '0.5*rho*S*V^2*C_T', { kind: 'definition' }),
    eq('pe', 'Effective power', 'P_E', 'R_T*V', { kind: 'law', origin: 'Rate of work done against resistance' }),
    a.calm
      ? eq('ps', 'Shaft power', 'P_S', 'P_E/(eta_D*eta_S)', { kind: 'definition', needs: ['calm'] })
      : eq('ps', 'Shaft power with sea margin', 'P_S', 'P_E*(1 + s_m)/(eta_D*eta_S)', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'Dimensional analysis of a hull moving at a free surface shows that the resistance coefficient depends on Reynolds number (viscous effects) and Froude number (gravity waves).', tex: 'C_T = \\frac{R_T}{\\tfrac12\\rho S V^2} = f(Re, Fn),\\quad Re = \\frac{VL}{\\nu},\\quad Fn = \\frac{V}{\\sqrt{gL}}' },
    { text: `Froude's hypothesis separates the two dependencies. The viscous part is taken from ${a.ittc57 ? 'the ITTC-1957 line' : 'the Schoenherr line'}${a.form ? ', scaled by a form factor' : ''}.`, tex: a.ittc57 ? 'C_F = \\frac{0.075}{(\\log_{10}Re - 2)^2}' : '\\frac{0.242}{\\sqrt{C_F}} = \\log_{10}(Re\\,C_F)' },
    { text: 'At low Froude number wave-making resistance grows roughly as the sixth power of speed, which fixes the form of the closure; its magnitude is an empirical constant.', tex: 'C_W = c_w\\,Fn^4' },
    { text: 'Summing the components and multiplying by the dynamic pressure and wetted surface gives the resistance; power is resistance times speed, divided by the propulsive and shaft efficiencies.', tex: 'P_E = R_T V,\\qquad P_S = \\frac{P_E}{\\eta_D\\,\\eta_S}' },
  ],
  solve(v, a) {
    const p = shipPoint(v, a, v.V), warnings = [];
    if (p.Fn > 0.35) warnings.push('Froude number exceeds about 0.35: the Fn⁴ wave-making closure does not capture the resistance hump and is not reliable here.');
    if (v.L / v.B < 4 || v.L / v.B > 10) warnings.push('Length-to-beam ratio is outside the usual 4–10 range of displacement ships; the wetted-surface estimate is an extrapolation.');
    const Vs = N.linspace(0.2 * v.V, 1.3 * v.V, 60), pts = Vs.map(x => shipPoint(v, a, x)), kn = Vs.map(x => x / 0.514444444);
    return {
      scalars: [
        scalar('Fn', 'Froude number', p.Fn, '1'), scalar('Re', 'Reynolds number', p.Re, '1'),
        scalar('V_d', 'Displaced volume', p.vol, 'm^3'), scalar('Delta', 'Displacement', v.rho * p.vol, 'kg', { show: 't' }),
        scalar('S', 'Wetted surface area', p.Sw, 'm^2'),
        scalar('C_F', 'Frictional resistance coefficient', p.CF, '1'), scalar('C_W', 'Wave-making resistance coefficient', p.CW, '1', { status: 'empirical' }), scalar('C_T', 'Total resistance coefficient', p.CT, '1'),
        scalar('R_V', 'Viscous resistance', p.RV, 'N', { show: 'kN' }), scalar('R_W', 'Wave-making resistance', p.RW, 'N', { show: 'kN' }), scalar('R_T', 'Total resistance', p.RT, 'N', { show: 'kN' }),
        scalar('P_E', 'Effective power', p.PE, 'W', { show: 'kW' }), scalar('P_S', 'Shaft power', p.PS, 'W', { show: 'kW' }),
      ],
      series: [
        line('resistance', 'Resistance against speed', 'Speed', 'kn', kn, [{ label: 'Total', data: pts.map(q => q.RT / 1e3) }, { label: 'Viscous', data: pts.map(q => q.RV / 1e3), dash: true }, { label: 'Wave-making', data: pts.map(q => q.RW / 1e3), dash: true }], 'Resistance', 'kN'),
        line('power', 'Speed–power curve', 'Speed', 'kn', kn, [{ label: 'Shaft power', data: pts.map(q => q.PS / 1e3) }, { label: 'Effective power', data: pts.map(q => q.PE / 1e3), dash: true }], 'Power', 'kW'),
      ],
      checks: [check('Resistance components sum to the total', (p.RV + p.RW + p.RA - p.RT) / p.RT, 1e-12, 'Viscous + wave-making + allowance against total')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [bench('ITTC-1957 line at Re = 10⁷', cfLine(1e7, true), 0.003, 'Exact value 0.075/(7 − 2)²', 1e-12)];
    out.push(bench('Schoenherr line at Re = 10⁷', cfLine(1e7, false), 0.002934, 'Tabulated Schoenherr coefficient', 1e-3));
    const r = this.solve({ ...v, c_w: 0, C_A: 0 }, { ...a, form: false, ittc57: true });
    out.push(bench('Flat-plate limit: R_T = ½ρSV²C_F', val(r, 'R_T'), 0.5 * v.rho * val(r, 'S') * v.V ** 2 * 0.075 / (Math.log10(v.V * v.L / v.nu) - 2) ** 2, 'Closed form with no form, wave or roughness terms', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    return svg(`
      ${S.rect(30, 190, 580, 120, 'd-liquid', 0)} ${S.path('M30 190 L610 190', 'd-liquid-line')}
      ${S.path('M120 150 L520 150 L560 190 L540 250 L150 250 L110 190 Z', 'd-body')}
      ${S.path('M560 190 q14 -10 28 0 q14 10 28 0', 'd-liquid-line')} ${S.path('M60 190 q12 -8 24 0 q12 8 24 0', 'd-liquid-line')}
      ${S.arrow(330, 120, 440, 120)} ${S.text(385, 110, `V = ${lab(v.V / 0.514444444, 'kn')}`)}
      ${S.arrow(600, 222, 545, 222, 'd-arrow d-hazard')} ${S.text(604, 240, 'R_T', 'd-text', 'end')}
      ${S.dim(110, 285, 560, 285, `L = ${lab(v.L, 'm')}`)} ${S.dim(86, 190, 86, 250, '')} ${S.text(70, 224, `T = ${lab(v.T, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(335, 205, `B = ${lab(v.B, 'm')}   C_B = ${lab(v.C_B)}`)}
      ${S.text(320, 40, 'Calm-water resistance: friction + form + wave-making')}
    `);
  },
  experiment: {
    objective: 'Measure the calm-water resistance of a geometrically similar model over a range of speeds and extrapolate to full scale.',
    apparatus: ['Towing tank with carriage', 'Hull model, typically 4–8 m long, with turbulence stimulators near the bow', 'Resistance dynamometer free to heave and trim'],
    instruments: [{ name: 'Resistance dynamometer', measures: 'Tow force', range: '0–500 N', resolution: '±0.2 %' }, { name: 'Carriage speed encoder', measures: 'Model speed', range: '0–10 m/s', resolution: '±0.1 %' }, { name: 'Water thermometer', measures: 'Tank temperature for viscosity', range: '5–30 °C', resolution: '±0.1 K' }],
    procedure: ['Tow the model at Froude numbers matching the ship speed range, waiting for the tank to settle between runs.', 'Use the low-speed runs (Fn < 0.2) to find the form factor by Prohaska\'s method.', 'Subtract the scaled viscous part to obtain C_W(Fn) and fit the wave coefficient.'],
    controls: ['Repeat runs to quantify scatter', 'Blockage and temperature corrections'],
    signatures: ['C_T/C_F tending to a constant (1 + k) as Fn → 0', 'C_W rising approximately as Fn⁴ below the resistance hump'],
    safety: ['Guarding of the carriage and rails', 'Lifting plan for the model'],
  },
  falsify: ['A measured total resistance coefficient that does not approach (1 + k)·C_F at low Froude number.', 'Model-scale C_W that departs from an Fn⁴ trend below Fn ≈ 0.25 by more than the experimental scatter.'],
  alternatives: [{ name: 'Holtrop–Mennen statistical method', text: 'Regression on a large body of model tests giving wave resistance from hull-form parameters; preferable for preliminary design.' }, { name: 'Potential-flow or RANS computation', text: 'Resolves the wave pattern and viscous flow for the actual hull geometry.' }],
  hazards: [{ hazard: 'Under-powered ship', cause: 'Wave-making under-estimated near the resistance hump', mitigation: 'Calibrate against model tests; keep a sea margin' }],
  standards: ['ITTC Recommended Procedures and Guidelines 7.5-02-02-01 (resistance test)', 'ITTC Recommended Procedures 7.5-02-03-01.4 (1978 performance prediction method)', 'ISO 15016 (speed and power trials)'],
  limits: 'Displacement hulls in calm deep water at Froude numbers below about 0.3. The wave-making closure is a one-parameter trend, not a prediction: it must be calibrated. Appendage, air and added resistance in waves are not included.',
  numerics: { method: 'Algebraic evaluation; fixed-point iteration for the Schoenherr line' },
  optimise: { objective: 'P_S', sense: 'min', vars: ['L', 'B'], note: 'Longer, finer hulls lower the Froude number and wave-making; displacement changes with the dimensions, so compare at equal deadweight in practice.' },
  inverse: { series: 'resistance', fit: ['c_w', 'k_form'] },
  extensions: ['Holtrop–Mennen wave resistance with bulbous-bow and transom terms', 'Added resistance in waves and wind', 'Propeller matching with open-water curves'],
};

// ------------------------------------------------------------------ ship stability and roll
function rollSim(p) {
  const { GM, BM, k, zeta, beta, phi0, wall, nonlin, tEnd, n } = p;
  const wr = Math.sqrt(g * Math.abs(GM)) / k;
  const GZ = f => { const c = N.clamp(f, -1.4, 1.4); return wall ? Math.sin(c) * (GM + 0.5 * BM * Math.tan(c) ** 2) : GM * Math.sin(c); };
  const acc = (f, w) => -2 * zeta * wr * w - beta * Math.abs(w) * w - g * (nonlin ? GZ(f) : GM * f) / (k * k);
  const h = tEnd / n, t = [0], phi = [phi0];
  let f = phi0, w = 0, capsized = false;
  for (let i = 0; i < n; i++) {
    const a1 = acc(f, w), a2 = acc(f + 0.5 * h * w, w + 0.5 * h * a1), w2 = w + 0.5 * h * a1, a3 = acc(f + 0.5 * h * w2, w + 0.5 * h * a2), w3 = w + 0.5 * h * a2, a4 = acc(f + h * w3, w + h * a3), w4 = w + h * a3;
    f += h / 6 * (w + 2 * w2 + 2 * w3 + w4); w += h / 6 * (a1 + 2 * a2 + 2 * a3 + a4);
    t.push((i + 1) * h); phi.push(f);
    if (!(Math.abs(f) < 1.5)) { capsized = true; break; }
  }
  // positive peaks (parabolic refinement) and up-crossing period
  const peaks = [{ t: 0, phi: phi0 }], ups = [];
  for (let i = 1; i < phi.length - 1; i++) {
    if (phi[i] > phi[i - 1] && phi[i] >= phi[i + 1] && phi[i] > 0) {
      const den = phi[i - 1] - 2 * phi[i] + phi[i + 1], s = den !== 0 ? 0.5 * (phi[i - 1] - phi[i + 1]) / den : 0;
      peaks.push({ t: t[i] + s * h, phi: phi[i] - 0.25 * (phi[i - 1] - phi[i + 1]) * s });
    }
    if (phi[i - 1] < 0 && phi[i] >= 0) ups.push(t[i - 1] + h * (0 - phi[i - 1]) / (phi[i] - phi[i - 1]));
  }
  const Tm = ups.length >= 2 ? (ups[ups.length - 1] - ups[0]) / (ups.length - 1) : NaN;
  return { t, phi, peaks, Tm, capsized };
}
const shipStability = {
  id: 'ship-stability-roll',
  title: 'Intact stability and roll of a wall-sided hull',
  module: 2, klass: 'I', domains: ['marine'],
  keywords: ['metacentric height', 'metacentric', 'gz curve', 'righting lever', 'righting arm', 'roll period', 'roll decay', 'intact stability', 'box barge', 'barge stability', 'angle of loll', 'free surface effect', 'heel', 'roll', 'stability', 'barge', 'ship'],
  summary: 'Hydrostatics of a box-shaped hull (KB, BM, GM), the wall-sided righting-lever curve, natural roll period and free roll decay with linear and quadratic damping.',
  background: [
    'A floating body is stable when a small heel moves the centre of buoyancy far enough to give a righting couple. For small angles the buoyancy force acts through a fixed point, the metacentre, whose height above the centre of buoyancy is the second moment of the waterplane divided by the displaced volume. The righting lever is then GM·sin φ.',
    'For a hull whose sides are vertical in way of the waterline, the shift of buoyancy can be integrated exactly while the deck edge stays dry and the bilge stays wet, giving the wall-sided formula. Roll motion is a lightly damped oscillation about upright whose period depends on GM and the roll radius of gyration, including added inertia of the surrounding water.',
  ],
  phenomena: ['Hydrostatic restoring moment', 'Shift of the centre of buoyancy', 'Free-surface loss of stability', 'Roll damping by wave radiation, friction and eddy shedding'],
  laws: ['archimedes', 'angular', 'newton2'],
  refs: ['Rawson, K. J. & Tupper, E. C. (2001). Basic Ship Theory, 5th ed. Butterworth-Heinemann.', 'Biran, A. & López-Pulido, R. (2014). Ship Hydrostatics and Stability, 2nd ed. Butterworth-Heinemann.', 'Himeno, Y. (1981). Prediction of ship roll damping – state of the art. Report 239, Dept. of Naval Architecture and Marine Engineering, University of Michigan.', 'IMO (2008). International Code on Intact Stability (2008 IS Code), Resolution MSC.267(85).'],
  inputs: [
    inp('L', 'Length', 'm', 60, { min: 5, max: 400, kind: 'geometry', aliases: ['length', 'long'] }),
    inp('B', 'Beam', 'm', 12, { min: 1, max: 80, kind: 'geometry', aliases: ['beam', 'breadth', 'wide'] }),
    inp('T', 'Draught', 'm', 3, { min: 0.2, max: 25, kind: 'geometry', aliases: ['draught', 'draft'] }),
    inp('F_b', 'Freeboard', 'm', 3, { min: 0.2, max: 20, kind: 'geometry', aliases: ['freeboard'] }),
    inp('KG', 'Height of centre of gravity above keel', 'm', 4, { min: 0.2, max: 15, kind: 'geometry', aliases: ['kg', 'centre of gravity', 'center of gravity', 'vcg'] }),
    inp('k_B', 'Roll radius of gyration as a fraction of beam', '1', 0.40, { min: 0.25, max: 0.6, kind: 'geometry', aliases: ['radius of gyration', 'gyradius'], src: 'Typically 0.35–0.45 of beam including added inertia' }),
    inp('phi_0', 'Initial heel angle for the roll-decay test', 'deg', 15, { min: 1, max: 40, aliases: ['initial heel', 'initial angle', 'heel angle'] }),
    inp('zeta', 'Linear roll damping ratio', '1', 0.03, { min: 0, max: 0.3, kind: 'fluid', aliases: ['damping ratio', 'linear damping'], src: 'Bare hull without bilge keels: order 0.01–0.05' }),
    inp('beta_q', 'Quadratic roll damping coefficient', '1', 0.1, { min: 0, max: 2, kind: 'fluid', aliases: ['quadratic damping'], src: 'Per radian; obtained from the slope of a roll-decrement plot' }),
    inp('l_t', 'Slack-tank length', 'm', 10, { min: 0.5, max: 100, kind: 'geometry', aliases: ['tank length'] }),
    inp('b_t', 'Slack-tank breadth', 'm', 6, { min: 0.5, max: 40, kind: 'geometry', aliases: ['tank breadth', 'tank width'] }),
  ],
  assumptions: [
    asm('wall_sided', 'The hull is wall-sided over the heel range: GZ = sin φ·(GM + ½·BM·tan²φ).', { why: 'Exact for a box until the deck edge immerses or the bilge emerges', alt: 'The small-angle righting lever GZ = GM·sin φ is used at all angles.' }),
    asm('no_fs', 'All tanks are pressed full or empty: there is no free-surface effect.', { why: 'Design departure condition', alt: 'One slack tank of the stated plan dimensions, holding liquid of sea-water density, reduces GM by i_t/∇.' }),
    asm('nonlinear', 'The roll equation uses the full righting-lever curve.', { why: 'Needed at moderate angles', alt: 'The restoring moment is linearised to GM·φ.' }),
    asm('quad_damp', 'Roll damping has linear and velocity-squared parts.', { why: 'Eddy shedding at the bilges gives a quadratic term', alt: 'Only the linear damping term is retained.' }),
  ],
  symbols: { V_d: ['Displaced volume', 'm^3'], I_T: ['Transverse second moment of the waterplane', 'm^4'], KB: ['Centre of buoyancy above keel', 'm'], BM: ['Metacentric radius', 'm'], GM: ['Metacentric height', 'm'], GZ: ['Righting lever', 'm'], phi: ['Heel angle', 'rad'], t: ['Time', 's'], k_xx: ['Roll radius of gyration', 'm'], T_r: ['Natural roll period', 's'], omega_r: ['Natural roll frequency', '1/s'], i_t: ['Second moment of the tank free surface', 'm^4'] },
  equations: a => [
    eq('vol', 'Displaced volume of a box', 'V_d', 'L*B*T', { kind: 'law', origin: 'Archimedes\' principle' }),
    eq('kb', 'Centre of buoyancy', 'KB', 'T/2', { kind: 'derived', origin: 'Centroid of a rectangular underwater section' }),
    eq('it', 'Waterplane second moment', 'I_T', 'L*B^3/12', { kind: 'definition' }),
    eq('bm', 'Metacentric radius', 'BM', 'I_T/V_d', { kind: 'derived', origin: 'Transfer of the immersed and emerged wedges' }),
    a.no_fs
      ? eq('gm', 'Metacentric height', 'GM', 'KB + BM - KG', { kind: 'definition', needs: ['no_fs'] })
      : eq('gm', 'Metacentric height with free-surface correction', 'GM', 'KB + BM - KG - l_t*b_t^3/(12*V_d)', { kind: 'derived', origin: 'Virtual rise of the centre of gravity due to a free surface' }),
    a.wall_sided
      ? eq('gz', 'Wall-sided righting lever', 'GZ', 'sin(phi)*(GM + 0.5*BM*tan(phi)^2)', { kind: 'derived', origin: 'Exact wedge integration for vertical sides', needs: ['wall_sided'] })
      : eq('gz', 'Small-angle righting lever', 'GZ', 'GM*sin(phi)', { kind: 'derived', origin: 'Fixed metacentre' }),
    eq('kxx', 'Roll radius of gyration', 'k_xx', 'k_B*B', { kind: 'empirical', origin: 'Weight distribution plus added inertia' }),
    eq('tr', 'Natural roll period', 'T_r', '2*pi*k_xx/sqrt(g*GM)', { kind: 'derived', origin: 'Linearised roll equation' }),
    eq('wr', 'Natural roll frequency', 'omega_r', 'sqrt(g*abs(GM))/k_xx', { kind: 'definition', note: 'The magnitude of GM is used so that the damping term stays defined when the upright hull is unstable.' }),
    eq('roll', 'Free roll equation', 'd2(phi,t)', `-2*zeta*omega_r*d(phi,t)${a.quad_damp ? ' - beta_q*abs(d(phi,t))*d(phi,t)' : ''} - g*${a.nonlinear ? 'GZ' : 'GM*phi'}/k_xx^2`, { kind: 'law', origin: 'Angular momentum about the roll axis', needs: a.nonlinear ? ['nonlinear'] : [] }),
  ],
  derivation: a => [
    { text: 'When the hull heels by a small angle a wedge of buoyancy is transferred from the emerged to the immersed side. Taking moments of the wedges gives the horizontal shift of the centre of buoyancy and hence the metacentric radius.', tex: 'BM = \\frac{I_T}{\\nabla} = \\frac{L B^3/12}{L B T} = \\frac{B^2}{12\\,T}' },
    { text: 'The metacentric height is measured from the centre of gravity' + (a.no_fs ? '.' : ', raised virtually by the free surface in the slack tank.'), tex: a.no_fs ? 'GM = KB + BM - KG' : 'GM = KB + BM - KG - \\frac{i_t}{\\nabla}' },
    { text: a.wall_sided ? 'For vertical sides the wedge moments can be integrated at any angle, adding a term that grows with tan²φ.' : 'With a fixed metacentre the lever is simply the horizontal offset of M from G.', tex: a.wall_sided ? 'GZ = \\sin\\varphi\\left(GM + \\tfrac12 BM\\tan^2\\varphi\\right)' : 'GZ = GM\\sin\\varphi' },
    { text: 'Angular momentum about the roll axis, with the mass moment of inertia written as Δ·k², gives the roll equation; its small-angle solution is harmonic.', tex: '\\ddot\\varphi + 2\\zeta\\omega_r\\dot\\varphi + \\beta_q|\\dot\\varphi|\\dot\\varphi + \\frac{g\\,GZ(\\varphi)}{k_{xx}^2} = 0,\\qquad T_r = \\frac{2\\pi k_{xx}}{\\sqrt{g\\,GM}}' },
  ],
  solve(v, a) {
    const vol = v.L * v.B * v.T, KB = v.T / 2, IT = v.L * v.B ** 3 / 12, BM = IT / vol;
    const fsc = a.no_fs ? 0 : v.l_t * v.b_t ** 3 / 12 / vol, GM = KB + BM - v.KG - fsc, k = v.k_B * v.B;
    const GZ = f => (a.wall_sided ? Math.sin(f) * (GM + 0.5 * BM * Math.tan(f) ** 2) : GM * Math.sin(f));
    const stable = GM > 0, Tr = stable ? 2 * Math.PI * k / Math.sqrt(g * GM) : NaN;
    const phiLim = Math.min(Math.atan(2 * v.F_b / v.B), Math.atan(2 * v.T / v.B));
    const loll = !stable && a.wall_sided ? Math.atan(Math.sqrt(-2 * GM / BM)) : NaN;
    const tScale = 2 * Math.PI * k / Math.sqrt(g * Math.max(Math.abs(GM), 0.02 * v.B));
    const sim = rollSim({ GM, BM, k, zeta: v.zeta, beta: a.quad_damp ? v.beta_q : 0, phi0: v.phi_0, wall: a.wall_sided, nonlin: a.nonlinear, tEnd: 8 * tScale, n: 1600 });
    const ang = N.linspace(0, 60 * DEG, 121), gz = ang.map(GZ), gzs = ang.map(f => GM * Math.sin(f));
    const i30 = 60, A30 = N.trapz(ang.slice(0, i30 + 1), gz.slice(0, i30 + 1));
    const dec = sim.peaks.length >= 2 ? Math.log(sim.peaks[0].phi / sim.peaks[1].phi) : NaN;
    const warnings = [];
    if (!stable) warnings.push('Metacentric height is not positive: the hull is unstable when upright' + (Number.isFinite(loll) ? ' and will settle at the angle of loll.' : '.'));
    if (v.phi_0 > phiLim) warnings.push('The initial heel exceeds the angle at which the deck edge immerses or the bilge emerges; the wall-sided formula is not valid beyond that angle.');
    if (sim.capsized) warnings.push('The simulated roll angle exceeded 86°: the hull capsizes under the stated conditions.');
    const pk = sim.peaks.slice(0, 12);
    return {
      scalars: [
        scalar('Delta', 'Displacement', 1025 * vol, 'kg', { show: 't', note: 'Sea water, 1025 kg/m³' }), scalar('KB', 'Centre of buoyancy above keel', KB, 'm'), scalar('BM', 'Metacentric radius', BM, 'm'),
        scalar('GM', 'Metacentric height', GM, 'm', { note: stable ? 'stable upright' : 'unstable upright' }),
        scalar('GZ_30', 'Righting lever at 30°', GZ(30 * DEG), 'm'), scalar('A_30', 'Area under the GZ curve to 30°', A30, 'm rad'),
        scalar('phi_lim', 'Limit of the wall-sided range (deck edge or bilge)', phiLim, 'rad', { show: 'deg' }),
        scalar('phi_loll', 'Angle of loll', loll, 'rad', { show: 'deg', text: Number.isFinite(loll) ? undefined : stable ? 'None — GM is positive' : 'Not defined by the small-angle lever' }),
        scalar('T_r', 'Natural roll period (linear theory)', Tr, 's', { text: stable ? undefined : 'No oscillation — GM is not positive' }),
        scalar('T_meas', 'Roll period from the simulated decay', sim.Tm, 's', { text: Number.isFinite(sim.Tm) ? undefined : 'No complete cycle' }),
        scalar('delta_1', 'Logarithmic decrement over the first cycle', dec, '1', { text: Number.isFinite(dec) ? undefined : 'No complete cycle' }),
      ],
      series: [
        line('gz-curve', 'Righting-lever curve', 'Heel angle', 'deg', ang.map(x => x / DEG), [{ label: a.wall_sided ? 'Wall-sided GZ' : 'GZ = GM·sin φ', data: gz }, { label: 'Small-angle GM·sin φ', data: gzs, dash: true }], 'Righting lever', 'm', { note: `Valid up to ${lab(phiLim / DEG, '°')}, where the deck edge immerses or the bilge emerges.` }),
        line('roll-decay', 'Free roll decay', 'Time', 's', sim.t, [{ label: 'Roll angle', data: sim.phi.map(x => x / DEG) }], 'Roll angle', 'deg'),
        line('decrement', 'Successive roll peaks', 'Peak number', '–', pk.map((_, i) => i), [{ label: 'Peak amplitude', data: pk.map(q => q.phi / DEG) }], 'Amplitude', 'deg', { kind: 'scatter' }),
      ],
      checks: [check('Metacentric radius of a box', (BM - v.B ** 2 / (12 * v.T)) / BM, 1e-12, 'I_T/∇ against B²/(12T)')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const r = this.solve(v, a), out = [bench('Box barge BM = B²/(12T)', val(r, 'BM'), v.B ** 2 / (12 * v.T), 'Rawson & Tupper, Basic Ship Theory', 1e-12)];
    const GM = 1.5, k = 4.8, T0 = 2 * Math.PI * k / Math.sqrt(g * GM);
    const s = rollSim({ GM, BM: 4, k, zeta: 0, beta: 0, phi0: 0.01, wall: false, nonlin: false, tEnd: 8 * T0, n: 1600 });
    out.push(bench('Undamped small-angle roll period from the integrator', s.Tm, T0, 'T = 2πk/√(g·GM)', 1e-4));
    const z = 0.05, s2 = rollSim({ GM, BM: 4, k, zeta: z, beta: 0, phi0: 0.01, wall: false, nonlin: false, tEnd: 8 * T0, n: 3200 });
    out.push(bench('Linear roll decrement', Math.log(s2.peaks[0].phi / s2.peaks[1].phi), 2 * Math.PI * z / Math.sqrt(1 - z * z), 'Exact logarithmic decrement of a damped linear oscillator', 2e-3));
    return out;
  },
  validation: [],
  diagram(v) {
    const hw = 110, dr = 60, fb = 50, cx = 320, wl = 190, kg = Math.min(v.KG / (v.T + v.F_b), 1.3) * (dr + fb);
    return svg(`
      ${S.rect(40, wl, 560, 130, 'd-liquid', 0)} ${S.path(`M40 ${wl} L600 ${wl}`, 'd-liquid-line')}
      ${S.rect(cx - hw, wl - fb, 2 * hw, dr + fb, 'd-body', 2)}
      ${S.line(cx, wl - fb - 70, cx, wl + dr + 10, 'd-dim')}
      ${S.circle(cx, wl + dr / 2, 4, 'd-fill')} ${S.text(cx + 12, wl + dr / 2 + 4, 'B', 'd-text', 'start')}
      ${S.circle(cx, wl + dr - kg, 4, 'd-fill')} ${S.text(cx + 12, wl + dr - kg + 4, 'G', 'd-text', 'start')}
      ${S.circle(cx, wl - fb - 50, 4, 'd-fill')} ${S.text(cx + 12, wl - fb - 46, 'M', 'd-text', 'start')}
      ${S.text(cx + 12, wl + dr + 4, 'K', 'd-text', 'start')}
      ${S.dim(cx - hw, wl + dr + 30, cx + hw, wl + dr + 30, `B = ${lab(v.B, 'm')}`)}
      ${S.text(cx - hw - 12, wl + dr / 2 + 4, `T = ${lab(v.T, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(cx - hw - 12, wl - fb / 2 + 4, `freeboard ${lab(v.F_b, 'm')}`, 'd-text d-small', 'end')}
      ${S.path(`M${cx + 150} ${wl - 90} A 60 60 0 0 1 ${cx + 190} ${wl - 50}`, 'd-arrow')} ${S.text(cx + 200, wl - 80, 'roll φ', 'd-text', 'start')}
      ${S.text(320, 30, 'GM = KB + BM − KG;  BM = B²/(12T) for a box')}
    `);
  },
  experiment: {
    objective: 'Determine GM by an inclining experiment and the roll period and damping by a free roll-decay test.',
    apparatus: ['Rectangular barge model or pontoon in a still-water basin', 'Known weights that can be shifted transversely by a measured distance', 'Release mechanism to let the model go from a set heel without imparting sway'],
    instruments: [{ name: 'Inclinometer or pendulum', measures: 'Heel angle', range: '±30°', resolution: '±0.02°' }, { name: 'Inertial measurement unit', measures: 'Roll angle time history', range: '±60°', resolution: '100 Hz, ±0.05°' }, { name: 'Draught marks or gauges', measures: 'Draught at four corners', range: '—', resolution: '±1 mm' }],
    procedure: ['Shift a weight w a distance d across the deck and record the heel; GM = w·d/(Δ·tan φ).', 'Heel the model to the initial angle, release and record at least eight cycles.', 'Plot successive peak amplitudes to separate linear and quadratic damping (roll-decrement analysis).', 'Repeat with a partly filled tank to observe the free-surface loss of GM and longer period.'],
    controls: ['Shift the weights to both sides to cancel initial list', 'Still water, no mooring-line restraint'],
    signatures: ['Roll period proportional to 1/√GM', 'Decrement rising linearly with amplitude when quadratic damping is present'],
    safety: ['Secure all shifting weights', 'Do not approach a full-scale vessel\'s limiting heel during an inclining test'],
  },
  falsify: ['A measured righting lever for a box model that departs from the wall-sided formula before deck-edge immersion.', 'A roll period that does not scale as 1/√GM when the centre of gravity is raised.'],
  alternatives: [{ name: 'Cross-curves of stability', text: 'For real hull forms the righting lever is integrated numerically from the offsets at each heel angle.' }, { name: 'Ikeda component method', text: 'Predicts roll damping from friction, wave, eddy, lift and bilge-keel components.' }, { name: 'Six-degree-of-freedom seakeeping', text: 'Couples roll to sway and yaw and includes wave excitation.' }],
  hazards: [{ hazard: 'Capsize', cause: 'Insufficient GM or range of stability, free-surface effects, shifted cargo', mitigation: 'Loading computer, stability booklet limits, pressing up tanks' }, { hazard: 'Excessive accelerations', cause: 'Very large GM giving a short, stiff roll', mitigation: 'Adjust loading to moderate GM' }],
  standards: ['IMO 2008 Intact Stability Code (Resolution MSC.267(85))', 'ISO 12217 (small-craft stability and buoyancy)', 'ITTC Recommended Procedure 7.5-02-07-04.5 (roll damping estimation)'],
  limits: 'Rectangular (box) hull floating upright at even keel, heeled without trim, up to deck-edge immersion or bilge emergence. Roll is uncoupled from sway and yaw and there is no wave excitation.',
  numerics: { method: 'Closed-form hydrostatics; fourth-order Runge–Kutta for the roll equation (200 steps per natural period)', order: 4 },
  optimise: { objective: 'T_r', sense: 'max', vars: ['KG'], note: 'Raising the centre of gravity lengthens the roll period but reduces the stability margin.' },
  inverse: { series: 'roll-decay', fit: ['zeta', 'beta_q'] },
  extensions: ['Hull forms from offsets with numerical cross-curves', 'Beam-sea wave excitation and parametric roll', 'Wind heeling lever and weather criterion'],
};

// ------------------------------------------------------------------ linear waves and Morison loading
function simpson(f, a, b, n) { const h = (b - a) / n; let s = f(a) + f(b); for (let i = 1; i < n; i++) s += f(a + i * h) * (i % 2 ? 4 : 2); return s * h / 3; }
/** Bessel functions J0, J1, Y0, Y1 from their integral representations (x > 0). */
function besselJY(x) {
  const J = n => simpson(t => Math.cos(n * t - x * Math.sin(t)), 0, Math.PI, 400) / Math.PI;
  const tm = Math.asinh(45 / x);
  const Y = n => simpson(t => Math.sin(x * Math.sin(t) - n * t), 0, Math.PI, 400) / Math.PI - simpson(t => (n === 0 ? 2 : 2 * Math.sinh(t)) * Math.exp(-x * Math.sinh(t)), 0, tm, 4000) / Math.PI;
  return { J0: J(0), J1: J(1), Y0: Y(0), Y1: Y(1) };
}
/** MacCamy–Fuchs effective inertia coefficient for a vertical circular cylinder of radius a at wave number k. */
function macCamyFuchs(ka) {
  const x = Math.max(ka, 1e-3), b = besselJY(x), J1p = b.J0 - b.J1 / x, Y1p = b.Y0 - b.Y1 / x;
  return 4 / (Math.PI * x * x * Math.hypot(J1p, Y1p));
}
function morisonRun(v, a) {
  const om = 2 * Math.PI / v.T, U = v.U_c;
  const k = waveNumber(om, v.d, a.no_doppler ? 0 : U, !a.finite_depth);
  const d = v.d, Lw = 2 * Math.PI / k, sig = a.no_doppler ? om : om - k * U;
  const kd = a.finite_depth ? k * d : Infinity, tkd = a.finite_depth ? Math.tanh(k * d) : 1;
  const Hb = Math.min(0.142 * Lw * tkd, 0.78 * d), H = Math.min(v.H, Hb), A = H / 2;
  const ch = z => (a.finite_depth ? coshRatio(k, z, d) : Math.exp(k * z));
  const CM = a.slender ? v.C_M : macCamyFuchs(k * v.D / 2);
  const nz = 201, nt = 72, th = N.linspace(0, 2 * Math.PI, nt + 1), xi3 = new Float64Array(nz);
  for (let j = 0; j < nz; j++) xi3[j] = (j / (nz - 1)) ** 3;
  const F = [], FD = [], FI = [], M = [], eta = [], prof = [];
  const cd = 0.5 * v.rho * v.C_D * v.D, ci = v.rho * CM * Math.PI * v.D ** 2 / 4;
  const zs = new Float64Array(nz), cz = new Float64Array(nz), ft = new Float64Array(nz);
  const grid = (top, e) => { for (let j = 0; j < nz; j++) { zs[j] = top - (d + top) * xi3[j]; cz[j] = ch(Math.min(a.airy ? zs[j] : (zs[j] - e) * d / (d + e), 0)); } };
  grid(0, 0);
  const zGrid = Array.from(zs);
  for (const t of th) {
    const e = A * Math.cos(t), co = A * sig * Math.cos(t), si = -A * sig * om * Math.sin(t);
    if (!a.airy) grid(e, e);
    let d1 = 0, i1 = 0, m1 = 0, pd = 0, pi = 0;
    for (let j = 0; j < nz; j++) {
      const u = co * cz[j] + U, qd = cd * Math.abs(u) * u, qi = ci * si * cz[j];
      ft[j] = (qd + qi) / 1e3;
      if (j > 0) { const h = 0.5 * (zs[j - 1] - zs[j]); d1 += h * (qd + pd); i1 += h * (qi + pi); m1 += h * ((qd + qi) * (zs[j] + d) + (pd + pi) * (zs[j - 1] + d)); }
      pd = qd; pi = qi;
    }
    FD.push(d1); FI.push(i1); F.push(d1 + i1); M.push(m1); eta.push(e); prof.push(Array.from(ft));
  }
  return { om, k, Lw, sig, kd, tkd, H, Hb, A, CM, th, F, FD, FI, M, eta, prof, zGrid, ch };
}
const wavesMorison = {
  id: 'linear-waves-morison',
  title: 'Linear waves and Morison loading on a vertical pile',
  module: 2, klass: 'I', domains: ['offshore', 'marine', 'waves'],
  keywords: ['morison equation', 'morison', 'wave load', 'wave force', 'airy wave', 'linear wave theory', 'dispersion relation', 'wavelength', 'monopile', 'pile', 'base shear', 'overturning moment', 'keulegan-carpenter', 'wave kinematics', 'jacket leg', 'wave', 'waves'],
  summary: 'Airy wave dispersion and kinematics, and the drag-plus-inertia (Morison) force on a surface-piercing vertical cylinder integrated over depth: base shear and overturning moment through a wave cycle.',
  background: [
    'Small-amplitude (Airy) wave theory linearises the free-surface conditions of irrotational flow. It gives a dispersion relation linking wave period, depth and wavelength, and closed-form particle velocities and accelerations that decay with depth.',
    'For a cylinder that is slender compared with the wavelength, Morison and co-workers proposed that the in-line force per unit length is the sum of a drag term proportional to velocity squared and an inertia term proportional to the local fluid acceleration. The coefficients depend on Keulegan–Carpenter number, Reynolds number and roughness and are taken from experiments. When the diameter is no longer small the cylinder scatters the wave and linear diffraction theory replaces the inertia term.',
  ],
  phenomena: ['Gravity-wave dispersion', 'Orbital particle motion', 'Separated-flow drag', 'Inertia (Froude–Krylov plus added mass) force', 'Wave–current interaction'],
  laws: ['mass', 'momentum', 'bernoulli', 'newton2'],
  refs: ['Morison, J. R., O\'Brien, M. P., Johnson, J. W. & Schaaf, S. A. (1950). The force exerted by surface waves on piles. Petroleum Transactions, AIME 189, 149–154.', 'Dean, R. G. & Dalrymple, R. A. (1991). Water Wave Mechanics for Engineers and Scientists. World Scientific.', 'Sarpkaya, T. & Isaacson, M. (1981). Mechanics of Wave Forces on Offshore Structures. Van Nostrand Reinhold.', 'MacCamy, R. C. & Fuchs, R. A. (1954). Wave forces on piles: a diffraction theory. U.S. Army Beach Erosion Board, Technical Memorandum 69.', 'Wheeler, J. D. (1970). Method for calculating forces produced by irregular waves. Journal of Petroleum Technology 22, 359–367.'],
  inputs: [
    inp('H', 'Wave height', 'm', 4, { min: 0.1, max: 30, kind: 'environment', env: 'wave_height', aliases: ['wave height', 'significant wave height', 'hs'] }),
    inp('T', 'Wave period', 's', 9, { min: 2, max: 25, kind: 'environment', env: 'wave_period', aliases: ['wave period', 'period', 'tp'] }),
    inp('d', 'Water depth', 'm', 30, { min: 2, max: 500, kind: 'environment', env: 'water_depth', aliases: ['water depth', 'depth', 'deep'] }),
    inp('U_c', 'Current speed (in the wave direction)', 'm/s', 0.5, { min: 0, max: 3, kind: 'environment', env: 'current_speed', aliases: ['current', 'current speed'] }),
    inp('D', 'Pile diameter', 'm', 1.5, { min: 0.1, max: 12, kind: 'geometry', aliases: ['diameter', 'pile diameter'] }),
    inp('C_D', 'Drag coefficient', '1', 1.0, { min: 0, max: 2, kind: 'fluid', aliases: ['drag coefficient', 'cd'], src: 'Order 0.65 (smooth) to 1.05 (rough) at high Reynolds number; see API RP 2A and DNV-RP-C205' }),
    inp('C_M', 'Inertia coefficient', '1', 2.0, { min: 0, max: 2.5, kind: 'fluid', aliases: ['inertia coefficient', 'cm'], src: 'Potential-flow value 2.0 for a circular cylinder; lower at large Keulegan–Carpenter number' }),
    inp('rho', 'Sea-water density', 'kg/m^3', 1025, { min: 990, max: 1040, kind: 'fluid', aliases: ['density'] }),
  ],
  assumptions: [
    asm('airy', 'Linear kinematics are evaluated up to the still-water level only.', { why: 'Consistent first-order theory', alt: 'Wheeler stretching maps the linear profile onto the instantaneous wetted length, so loading extends to the crest.' }),
    asm('finite_depth', 'The full finite-depth dispersion relation ω² = g·k·tanh(k·d) is used.', { why: 'Valid at any depth', alt: 'The deep-water approximation ω² = g·k is used with exponential decay of the kinematics.' }),
    asm('slender', 'The pile is slender (D/L < 0.2): it does not disturb the incident wave and Morison\'s equation applies with the stated C_M.', { why: 'Typical jacket members and small piles', alt: 'The inertia coefficient is replaced by the MacCamy–Fuchs linear diffraction value (phase shift neglected).' }),
    asm('no_doppler', 'The current is simply added to the wave particle velocity; it does not change the wavelength.', { why: 'Weak current', alt: 'The dispersion relation is Doppler-shifted, (ω − k·U)² = g·k·tanh(k·d), for a following current.' }),
  ],
  symbols: { omega: ['Wave angular frequency', '1/s'], sigma_w: ['Intrinsic angular frequency', '1/s'], k: ['Wave number', '1/m'], L_w: ['Wavelength', 'm'], eta: ['Surface elevation', 'm'], z: ['Elevation above still water', 'm'], z_w: ['Stretched elevation', 'm'], t: ['Time', 's'], u: ['Horizontal particle velocity', 'm/s'], a_x: ['Horizontal particle acceleration', 'm/s^2'], f: ['In-line force per unit length', 'N/m'], F: ['Base shear', 'N'], M_b: ['Overturning moment about the seabed', 'N m'], C_Me: ['Effective inertia coefficient', '1'], J_1p: ['Derivative of the Bessel function J₁ at k·D/2', '1'], Y_1p: ['Derivative of the Bessel function Y₁ at k·D/2', '1'] },
  equations: a => {
    const zc = a.airy ? 'z' : 'z_w', depth = a.finite_depth ? `cosh(k*(${zc} + d))/sinh(k*d)` : `exp(k*${zc})`, cm = a.slender ? 'C_M' : 'C_Me';
    return [
      eq('om', 'Angular frequency', 'omega', '2*pi/T', { kind: 'definition' }),
      a.no_doppler ? eq('sig', 'Intrinsic frequency', 'sigma_w', 'omega', { kind: 'definition', needs: ['no_doppler'] }) : eq('sig', 'Intrinsic frequency in a current', 'sigma_w', 'omega - k*U_c', { kind: 'law', origin: 'Doppler shift for a frame moving with the current' }),
      a.finite_depth
        ? eq('disp', 'Dispersion relation', 'sigma_w^2', 'g*k*tanh(k*d)', { kind: 'law', origin: 'Linearised free-surface conditions for irrotational flow', needs: ['finite_depth'] })
        : eq('disp', 'Deep-water dispersion relation', 'sigma_w^2', 'g*k', { kind: 'law', origin: 'Limit k·d → ∞ of the linear dispersion relation' }),
      eq('lw', 'Wavelength', 'L_w', '2*pi/k', { kind: 'definition' }),
      eq('eta', 'Surface elevation at the pile', 'eta', 'H/2*cos(omega*t)', { kind: 'derived', origin: 'Progressive Airy wave' }),
      ...(a.airy ? [] : [eq('wh', 'Wheeler stretching', 'z_w', '(z - eta)*d/(d + eta)', { kind: 'empirical', origin: 'Wheeler (1970)' })]),
      eq('u', 'Horizontal particle velocity', 'u', `H/2*sigma_w*${depth}*cos(omega*t) + U_c`, { kind: 'derived', origin: 'Airy velocity potential plus steady current', needs: a.airy ? ['airy'] : [] }),
      eq('ax', 'Horizontal particle acceleration', 'a_x', `-H/2*sigma_w*omega*${depth}*sin(omega*t)`, { kind: 'derived', origin: 'Local time derivative of the velocity' }),
      ...(a.slender ? [] : [eq('mf', 'Diffraction inertia coefficient', 'C_Me', '4/(pi*(k*D/2)^2*sqrt(J_1p^2 + Y_1p^2))', { kind: 'derived', origin: 'MacCamy & Fuchs (1954) linear diffraction solution' })]),
      eq('mor', 'Morison equation', 'f', `0.5*rho*C_D*D*abs(u)*u + rho*${cm}*pi*D^2/4*a_x`, { kind: 'empirical', origin: 'Morison, O\'Brien, Johnson & Schaaf (1950)', needs: a.slender ? ['slender'] : [] }),
      eq('F', 'Base shear', 'F', 'int(f, z)', { kind: 'definition' }),
      eq('M', 'Overturning moment', 'M_b', 'int(f*(z + d), z)', { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'For irrotational flow the velocity potential satisfies Laplace\'s equation. Linearising the kinematic and dynamic free-surface conditions about still water and imposing no flow through the bed gives a progressive-wave solution that exists only if frequency and wave number satisfy the dispersion relation.', tex: a.finite_depth ? '\\omega^2 = g\\,k\\tanh(k d)' : '\\omega^2 = g\\,k' },
    { text: 'Differentiating the potential gives the horizontal particle velocity; its time derivative is the acceleration. Both decay with depth.', tex: 'u = \\frac{\\pi H}{T}\\,\\frac{\\cosh k(z+d)}{\\sinh kd}\\cos\\omega t,\\qquad \\dot u = -\\frac{2\\pi^2 H}{T^2}\\,\\frac{\\cosh k(z+d)}{\\sinh kd}\\sin\\omega t' },
    { text: 'On a slender member the force per unit length is modelled as drag, in phase with velocity, plus inertia, in phase with acceleration.', tex: 'f = \\tfrac12\\rho C_D D\\,|u|u + \\rho C_M \\frac{\\pi D^2}{4}\\,\\dot u' },
    { text: `Integrating from the seabed to ${a.airy ? 'the still-water level' : 'the instantaneous free surface'} gives the base shear and, with the lever arm, the overturning moment. Without current the inertia part has the closed-form amplitude shown.`, tex: 'F = \\int f\\,\\mathrm{d}z,\\quad M = \\int f\\,(z+d)\\,\\mathrm{d}z,\\quad F_{I,\\max} = \\rho C_M \\frac{\\pi D^2}{4}\\,\\frac{H}{2}\\,g\\tanh kd' },
  ],
  solve(v, a) {
    const r = morisonRun(v, a), warnings = [];
    if (r.H < v.H) warnings.push(`The stated wave height exceeds the breaking limit for this period and depth; it has been limited to ${lab(r.H, 'm')} (Miche steepness limit and H ≤ 0.78·d).`);
    const DL = v.D / r.Lw;
    if (a.slender && DL > 0.2) warnings.push('D/L exceeds 0.2: the pile diffracts the wave and Morison\'s equation over-predicts the inertia load. Switch off the slender-member assumption.');
    const uOrb = r.A * r.sig * r.ch(0), uMax = uOrb + v.U_c, KC = uOrb * v.T / v.D;
    const absF = r.F.map(Math.abs), iF = absF.indexOf(N.maxOf(absF)), Fmax = absF[iF], Mmax = N.maxOf(r.M.map(Math.abs));
    const c = 2 * Math.PI / v.T / r.k, x2 = 2 * r.kd, cRel = r.sig / r.k, cg = (a.no_doppler ? 0 : v.U_c) + (a.finite_depth ? 0.5 * cRel * (1 + (x2 > 600 ? 0 : x2 / Math.sinh(x2))) : 0.5 * cRel);
    const deg = r.th.map(x => x / DEG), zProf = r.zGrid, uProf = zProf.map(z => r.A * r.sig * r.ch(z) + v.U_c);
    const regime = r.kd < Math.PI / 10 ? 'shallow water' : r.kd > Math.PI ? 'deep water' : 'intermediate depth';
    return {
      scalars: [
        scalar('k', 'Wave number', r.k, '1/m'), scalar('L_w', 'Wavelength', r.Lw, 'm'), scalar('c_p', 'Phase speed', c, 'm/s'), scalar('c_g', 'Group speed', cg, 'm/s'),
        scalar('kd', 'Relative depth k·d', a.finite_depth ? r.kd : r.k * v.d, '1', { note: regime }), scalar('H_used', 'Wave height used', r.H, 'm'),
        scalar('u_max', 'Peak horizontal velocity at still-water level', uMax, 'm/s'), scalar('KC', 'Keulegan–Carpenter number (orbital velocity amplitude at still-water level)', KC, '1', { note: KC < 5 ? 'inertia-dominated' : KC > 25 ? 'drag-dominated' : 'drag and inertia both matter' }),
        scalar('DL', 'Diameter to wavelength ratio D/L', DL, '1'), scalar('C_Me', 'Inertia coefficient used', r.CM, '1'),
        scalar('F_D', 'Peak drag force', N.maxOf(r.FD.map(Math.abs)), 'N', { show: 'kN' }), scalar('F_I', 'Peak inertia force', N.maxOf(r.FI.map(Math.abs)), 'N', { show: 'kN' }),
        scalar('F', 'Maximum base shear', Fmax, 'N', { show: 'kN' }), scalar('M_b', 'Maximum overturning moment', Mmax, 'N m', { show: 'kN m' }),
        scalar('z_F', 'Lever arm of the peak load above the seabed', Fmax > 0 ? Math.abs(r.M[iF]) / Fmax : 0, 'm'), scalar('theta_F', 'Wave phase at maximum base shear', r.th[iF], 'rad', { show: 'deg' }),
      ],
      series: [
        line('force-history', 'Base shear through one wave period', 'Wave phase', 'deg', deg, [{ label: 'Total', data: r.F.map(x => x / 1e3) }, { label: 'Drag', data: r.FD.map(x => x / 1e3), dash: true }, { label: 'Inertia', data: r.FI.map(x => x / 1e3), dash: true }], 'Force', 'kN'),
        line('moment-history', 'Overturning moment through one wave period', 'Wave phase', 'deg', deg, [{ label: 'Moment about the seabed', data: r.M.map(x => x / 1e3) }], 'Moment', 'kN m'),
        line('u-profile', 'Horizontal velocity under the crest', 'Elevation', 'm', zProf.slice().reverse(), [{ label: 'Velocity', data: uProf.slice().reverse() }], 'Velocity', 'm/s'),
      ],
      anims: [anim('load-profile', 'Distributed load on the pile', 'Elevation at wave crest phase', 'm', zProf.slice().reverse(), r.prof.map(p => p.slice().reverse()), r.th.map(x => x / (2 * Math.PI) * v.T), 'Force per unit length', 'kN/m')],
      checks: [check('Dispersion relation residual', (r.sig ** 2 - g * r.k * r.tkd) / r.sig ** 2, 1e-9, 'σ² against g·k·tanh(k·d)')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], T = 8, kDeep = waveNumber(2 * Math.PI / T, 5000);
    out.push(bench('Deep-water wavelength L = gT²/(2π)', 2 * Math.PI / kDeep, g * T * T / (2 * Math.PI), 'Airy theory, k·d → ∞', 1e-9));
    const Ts = 100, ks = waveNumber(2 * Math.PI / Ts, 1);
    out.push(bench('Shallow-water phase speed c = √(g·d)', 2 * Math.PI / Ts / ks, Math.sqrt(g * 1), 'Airy theory, k·d → 0', 1e-3));
    const b0 = { ...a, airy: true, finite_depth: true, slender: true, no_doppler: true };
    const ri = this.solve({ ...v, U_c: 0, C_D: 0 }, b0), k = val(ri, 'k'), H = val(ri, 'H_used'), om = 2 * Math.PI / v.T;
    out.push(bench('Inertia base shear vs closed form', val(ri, 'F'), v.rho * v.C_M * Math.PI * v.D ** 2 / 4 * H / 2 * om * om / k, 'ρ·C_M·(πD²/4)·(H/2)·ω²/k', 1e-3));
    const rd = this.solve({ ...v, U_c: 0, C_M: 0 }, b0), kd = k * v.d;
    out.push(bench('Drag base shear vs closed form', val(rd, 'F'), 0.5 * v.rho * v.C_D * v.D * (H / 2) ** 2 * om * om * (Math.sinh(2 * kd) + 2 * kd) / (4 * k * Math.sinh(kd) ** 2), '½ρ·C_D·D·(H/2)²·ω²·(sinh 2kd + 2kd)/(4k·sinh²kd)', 1e-3));
    out.push(bench('MacCamy–Fuchs inertia coefficient for a slender pile', macCamyFuchs(0.01), 2, 'Long-wave limit of linear diffraction theory', 1e-3));
    return out;
  },
  validation: [],
  diagram(v) {
    const sw = 110, bed = 300;
    const wave = Array.from({ length: 57 }, (_, i) => [40 + i * 10, sw - 22 * Math.cos((i * 10 - 280) / 280 * 2 * Math.PI)]);
    return svg(`
      ${S.path(`M40 ${bed} L600 ${bed}`, 'd-ground')} ${S.line(40, sw, 600, sw, 'd-dim')}
      ${S.poly(wave, 'd-liquid-line')}
      ${S.rect(305, 50, 30, bed - 50, 'd-body', 2)}
      ${[0, 1, 2, 3, 4].map(i => S.arrow(215 + i * 12, sw + 20 + i * 38, 300, sw + 20 + i * 38)).join('')}
      ${S.text(250, sw + 6, 'u(z,t)')}
      ${S.arrow(420, bed - 20, 500, bed - 20)} ${S.text(460, bed - 30, `U_c = ${lab(v.U_c, 'm/s')}`)}
      ${S.dim(560, sw, 560, bed, '')} ${S.text(552, (sw + bed) / 2, `d = ${lab(v.d, 'm')}`, 'd-text d-small', 'end')}
      ${S.dim(305, 36, 335, 36, `D = ${lab(v.D, 'm')}`)}
      ${S.text(120, 70, `H = ${lab(v.H, 'm')},  T = ${lab(v.T, 's')}`)}
      ${S.arrow(345, bed + 24, 400, bed + 24, 'd-arrow d-hazard')} ${S.text(410, bed + 28, 'base shear F, moment M', 'd-text', 'start')}
    `);
  },
  experiment: {
    objective: 'Measure the in-line wave force on an instrumented vertical cylinder and recover the drag and inertia coefficients.',
    apparatus: ['Wave flume with a piston or flap wavemaker and an absorbing beach', 'Vertical cylinder mounted on a force balance at the bed, or with an instrumented segment', 'Optional towing carriage or recirculation for current'],
    instruments: [{ name: 'Resistance or capacitance wave gauges', measures: 'Surface elevation at and ahead of the cylinder', range: '±0.3 m', resolution: '±0.5 mm' }, { name: 'Two-component force balance', measures: 'Base shear and overturning moment', range: '0–200 N', resolution: '±0.5 %' }, { name: 'Acoustic Doppler velocimeter', measures: 'Particle velocity at several elevations', range: '±2 m/s', resolution: '±1 %' }],
    procedure: ['Generate regular waves of fixed period and record elevation and force for at least 20 cycles.', 'Fit C_D and C_M to the measured force by least squares using the measured or computed kinematics.', 'Repeat over a range of Keulegan–Carpenter numbers by varying height and period.'],
    controls: ['Run without the cylinder to verify kinematics against linear theory', 'Check for reflections with a two-gauge separation method'],
    signatures: ['Force leading the crest by nearly 90° at small KC (inertia regime)', 'Force peaks under the crest and varies as H² at large KC (drag regime)', 'Measured wavelength following the dispersion relation'],
    safety: ['Electrical isolation of instruments in wet areas', 'Guard the wavemaker mechanism'],
  },
  falsify: ['A measured wavelength that departs from the dispersion relation for small-steepness waves by more than measurement error.', 'A force record on a slender cylinder that cannot be fitted by any constant C_D and C_M pair at fixed KC and Reynolds number.'],
  alternatives: [{ name: 'Stokes fifth-order or stream-function wave theory', text: 'Needed for steep waves, where crest kinematics exceed the linear prediction.' }, { name: 'Linear diffraction theory', text: 'Replaces Morison\'s inertia term when the diameter is a significant fraction of the wavelength.' }, { name: 'Relative-velocity Morison formulation', text: 'Uses fluid velocity relative to a moving structure and so introduces hydrodynamic damping.' }],
  hazards: [{ hazard: 'Structural overload', cause: 'Under-estimated crest kinematics in steep or breaking waves', mitigation: 'Use a higher-order wave theory and slamming allowance for design waves' }, { hazard: 'Fatigue', cause: 'Cyclic wave loading over the service life', mitigation: 'Spectral fatigue assessment with appropriate S–N curves' }],
  standards: ['API RP 2A-WSD (fixed offshore platforms)', 'ISO 19902 (fixed steel offshore structures)', 'DNV-RP-C205 (environmental conditions and environmental loads)', 'IEC 61400-3 (offshore wind turbines)'],
  limits: 'Regular, small-steepness, non-breaking waves on a flat bed; rigid, fixed, vertical circular cylinder. Morison\'s equation requires D/L below about 0.2. Slamming, run-up, vortex-induced transverse forces and wave nonlinearity are not included.',
  numerics: { method: 'Newton iteration for the dispersion relation; trapezoidal integration over a surface-clustered depth grid at 72 phases per period', order: 2 },
  optimise: { objective: 'M_b', sense: 'min', vars: ['D'], note: 'Drag grows with D and inertia with D²; structural capacity grows faster, so this is only half of a design trade-off.' },
  inverse: { series: 'force-history', fit: ['C_D', 'C_M'] },
  extensions: ['Irregular seas from a JONSWAP spectrum', 'Stream-function kinematics for steep waves', 'Dynamic response of the pile with soil springs'],
};

// ------------------------------------------------------------------ catenary mooring line
function catenary(v, a, H) {
  const w = v.w, d = v.d, Lt = v.scope * d, EA = a.inelastic ? Infinity : v.EA, mu = a.no_friction ? 0 : v.mu_s;
  const zOf = (Va, s) => { const Vt = Va + w * s; return H / w * (Math.hypot(1, Vt / H) - Math.hypot(1, Va / H)) + (Vt * Vt - Va * Va) / (2 * w * EA); };
  const xOf = (Va, s) => { const Vt = Va + w * s; return H / w * (Math.asinh(Vt / H) - Math.asinh(Va / H)) + H * s / EA; };
  const ac = H / w, sInel = Math.sqrt(d * (d + 2 * ac));
  let s = sInel, Va = 0;
  if (!a.inelastic) { const f = q => zOf(0, q) - d; s = f(sInel) <= 0 ? sInel : N.bisect(f, 0, sInel, 1e-13); }
  if (s > Lt) {
    s = Lt;
    const f = q => zOf(q, Lt) - d;
    let hi = Math.max(w * Lt, H);
    for (let i = 0; i < 60 && f(hi) < 0; i++) hi *= 4;
    Va = f(0) >= 0 ? 0 : f(hi) < 0 ? hi : N.bisect(f, 0, hi, 1e-13);
  }
  const Lg = Lt - s, xs = xOf(Va, s), lf = mu > 0 ? Math.min(Lg, H / (mu * w)) : Lg;
  const stretch = Number.isFinite(EA) ? (H * lf - mu * w * lf * lf / 2) / EA : 0;
  const Vt = Va + w * s, Ttop = Math.hypot(H, Vt);
  const Ta = Va > 0 ? Math.hypot(H, Va) : Math.max(H - mu * w * Lg, 0);
  return { H, s, Va, Vt, Lg, xs, X: Lg + stretch + xs, xg: Lg + stretch, Ttop, Ta, theta: Math.atan2(Vt, H), Lt, ac, zOf, xOf, resid: (zOf(Va, s) - d) / d };
}
function catenaryFromTop(v, a, T0) {
  const f = H => catenary(v, a, H).Ttop - T0, lo = 1e-6 * T0;
  if (f(lo) >= 0) return { c: catenary(v, a, lo), slack: true };
  return { c: catenary(v, a, N.bisect(f, lo, T0, 1e-13)), slack: false };
}
const catenaryMooring = {
  id: 'catenary-mooring',
  title: 'Catenary mooring line',
  module: 2, klass: 'I', domains: ['offshore', 'marine'],
  keywords: ['catenary mooring', 'mooring line', 'catenary', 'mooring', 'anchor chain', 'chain', 'touchdown point', 'suspended length', 'fairlead', 'mooring stiffness', 'line tension', 'anchor', 'restoring force', 'spread mooring'],
  summary: 'Static shape and tension of a single mooring line hanging between a seabed anchor and a fairlead: suspended length, touchdown, top angle and the tension–offset stiffness curve, inelastic or elastic.',
  background: [
    'A heavy flexible line hanging under its own weight takes the shape of a catenary. Because a chain or wire carries no bending moment, horizontal equilibrium makes the horizontal component of tension constant along the suspended part, while the vertical component grows by the submerged weight of line below.',
    'A catenary mooring restrains a floating vessel mainly by geometry: an offset lifts more line off the seabed, increasing the horizontal tension. The resulting stiffness is strongly nonlinear. Axial stretch softens the system once most of the line is lifted, and the anchor must be designed for uplift if no line remains on the bed.',
  ],
  phenomena: ['Self-weight catenary', 'Seabed touchdown', 'Geometric stiffness', 'Axial elasticity', 'Seabed friction on the grounded length'],
  laws: ['newton2', 'newton3', 'hooke', 'archimedes'],
  refs: ['Irvine, H. M. (1981). Cable Structures. MIT Press.', 'Faltinsen, O. M. (1990). Sea Loads on Ships and Offshore Structures. Cambridge University Press.', 'Barltrop, N. D. P. (ed.) (1998). Floating Structures: A Guide for Design and Analysis. Oilfield Publications / CMPT.', 'DNV-OS-E301. Position mooring. DNV, Høvik.', 'API RP 2SK. Design and analysis of stationkeeping systems for floating structures. American Petroleum Institute.'],
  inputs: [
    inp('d', 'Water depth below the fairlead', 'm', 100, { min: 10, max: 3000, kind: 'environment', env: 'water_depth', aliases: ['water depth', 'depth', 'deep'] }),
    inp('w', 'Submerged weight of line per unit length', 'N/m', 1200, { min: 10, max: 10000, kind: 'geometry', aliases: ['submerged weight', 'weight per metre', 'line weight', 'weight in water'], src: 'Roughly 84 mm studless chain in sea water' }),
    inp('scope', 'Line length as a multiple of water depth (scope)', '1', 6, { min: 1.5, max: 20, kind: 'geometry', aliases: ['scope', 'line length ratio'] }),
    inp('T_0', 'Specified line tension', 'kN', 500, { min: 1, max: 20000, aliases: ['tension', 'horizontal tension', 'top tension', 'pretension'] }),
    inp('EA', 'Axial stiffness of the line', 'MN', 600, { min: 10, max: 5000, kind: 'geometry', aliases: ['axial stiffness', 'ea'] }),
    inp('mu_s', 'Seabed friction coefficient of the grounded line', '1', 0.7, { min: 0.05, max: 1.5, kind: 'environment', aliases: ['friction coefficient', 'seabed friction'], src: 'Indicative value for chain on sand; site- and line-specific' }),
    inp('MBL', 'Minimum breaking load', 'kN', 6000, { min: 100, max: 50000, kind: 'geometry', aliases: ['breaking load', 'mbl', 'breaking strength'] }),
  ],
  assumptions: [
    asm('inelastic', 'The line is inextensible.', { why: 'Classical catenary; good for chain at moderate tension', alt: 'The elastic catenary is solved with the stated axial stiffness EA.' }),
    asm('h_given', 'The specified tension is the horizontal component at the fairlead.', { why: 'Natural variable of the catenary equations', alt: 'The specified tension is the total tension at the fairlead; the horizontal component is found from it.' }),
    asm('no_friction', 'Seabed friction on the grounded length is neglected, so the anchor sees the full horizontal tension.', { why: 'Conservative for anchor load', alt: 'Coulomb friction μ·w per unit length reduces the tension along the grounded line towards the anchor.' }),
  ],
  symbols: { T_H: ['Horizontal tension', 'N'], T_top: ['Tension at the fairlead', 'N'], T_a: ['Tension at the anchor', 'N'], a_c: ['Catenary parameter', 'm'], s_s: ['Suspended (unstretched) length', 'm'], l_f: ['Grounded length over which friction is mobilised', 'm'], x_s: ['Horizontal span of the suspended length', 'm'], X: ['Horizontal distance from anchor to fairlead', 'm'], L_t: ['Total line length', 'm'], theta_top: ['Line angle to the horizontal at the fairlead', 'rad'], k_h: ['Horizontal restoring stiffness', 'N/m'] },
  equations: a => [
    a.h_given ? eq('spec', 'Specified tension', 'T_H', 'T_0', { kind: 'boundary', needs: ['h_given'] }) : eq('spec', 'Specified tension', 'T_top', 'T_0', { kind: 'boundary' }),
    eq('ac', 'Catenary parameter', 'a_c', 'T_H/w', { kind: 'definition' }),
    eq('lt', 'Total line length', 'L_t', 'scope*d', { kind: 'definition' }),
    a.inelastic
      ? eq('ss', 'Suspended length', 's_s', 'sqrt(d*(d + 2*a_c))', { kind: 'derived', origin: 'Vertical equilibrium and geometry of the catenary with zero slope at touchdown', needs: ['inelastic'], note: 'Holds while some line rests on the seabed (s_s ≤ L_t). Once the whole line is lifted the anchor carries uplift and the solver finds the anchor vertical force numerically.' })
      : eq('ss', 'Vertical span of the elastic catenary', 'd', 'a_c*(sqrt(1 + (w*s_s/T_H)^2) - 1) + w*s_s^2/(2*EA)', { kind: 'derived', origin: 'Irvine (1981), elastic catenary' }),
    eq('xs', 'Horizontal span of the suspended line', 'x_s', `a_c*ln(w*s_s/T_H + sqrt(1 + (w*s_s/T_H)^2))${a.inelastic ? '' : ' + T_H*s_s/EA'}`, { kind: 'derived', origin: 'Integration of the catenary slope along the line' }),
    a.inelastic
      ? eq('tt', 'Tension at the fairlead', 'T_top', 'T_H + w*d', { kind: 'derived', origin: 'Force equilibrium of the suspended line', needs: ['inelastic'] })
      : eq('tt', 'Tension at the fairlead', 'T_top', 'sqrt(T_H^2 + (w*s_s)^2)', { kind: 'law', origin: 'Force equilibrium of the suspended line' }),
    eq('ang', 'Line angle at the fairlead', 'tan(theta_top)', 'w*s_s/T_H', { kind: 'law', origin: 'Ratio of vertical to horizontal tension' }),
    ...(a.inelastic || a.no_friction ? [] : [eq('lf', 'Grounded length carrying tension', 'l_f', 'min(L_t - s_s, T_H/(mu_s*w))', { kind: 'derived', origin: 'Friction reduces the tension to zero a distance T_H/(μ·w) behind the touchdown point' })]),
    eq('X', 'Anchor-to-fairlead distance', 'X', `(L_t - s_s)${a.inelastic ? '' : a.no_friction ? '*(1 + T_H/EA)' : ' + (T_H*l_f - mu_s*w*l_f^2/2)/EA'} + x_s`, { kind: 'derived', origin: 'Grounded length' + (a.inelastic ? '' : ', its elastic stretch') + ' plus suspended span' }),
    a.no_friction ? eq('ta', 'Anchor tension', 'T_a', 'T_H', { kind: 'law', origin: 'Horizontal equilibrium', needs: ['no_friction'] }) : eq('ta', 'Anchor tension with seabed friction', 'T_a', 'max(T_H - mu_s*w*(L_t - s_s), 0)', { kind: 'law', origin: 'Coulomb friction on the grounded length' }),
    a.inelastic
      ? eq('kh', 'Horizontal stiffness', 'k_h', 'w/(ln(1 + d/a_c + sqrt((1 + d/a_c)^2 - 1)) - 2/sqrt(1 + 2*a_c/d))', { kind: 'derived', origin: 'Derivative of the anchor-to-fairlead distance with respect to horizontal tension', needs: ['inelastic'] })
      : eq('kh', 'Horizontal stiffness', 'k_h', '1/pd(X, T_H)', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'Consider an element of the suspended line. With no horizontal load the horizontal tension T_H is constant; the vertical component increases by the submerged weight w per unit length.', tex: '\\frac{\\mathrm{d}}{\\mathrm{d}s}(T\\cos\\theta) = 0,\\qquad \\frac{\\mathrm{d}}{\\mathrm{d}s}(T\\sin\\theta) = w' },
    { text: 'Starting from zero slope at the touchdown point, tan θ = w·s/T_H. Integrating dz = sin θ ds and dx = cos θ ds gives the catenary with parameter a = T_H/w.', tex: 'z = a\\left(\\cosh\\frac{x}{a} - 1\\right),\\qquad s = a\\sinh\\frac{x}{a}' },
    { text: a.inelastic ? 'Setting z = d at the fairlead gives the suspended length and the top tension.' : 'Allowing for axial strain T/EA adds a stretch term to both spans; the suspended length then follows from a root-finding step.', tex: a.inelastic ? 's_s = \\sqrt{d\\,(d + 2a)},\\qquad T_{top} = T_H + w\\,d' : 'd = a\\left(\\sqrt{1 + (w s_s/T_H)^2} - 1\\right) + \\frac{w s_s^2}{2EA}' },
    { text: 'The anchor-to-fairlead distance is the grounded length plus the suspended span. Differentiating with respect to T_H gives the restoring stiffness felt by the vessel.', tex: 'k_h = \\left(\\frac{\\partial X}{\\partial T_H}\\right)^{-1} = w\\left[\\cosh^{-1}\\!\\left(1 + \\frac{d}{a}\\right) - \\frac{2}{\\sqrt{1 + 2a/d}}\\right]^{-1}' },
  ],
  solve(v, a) {
    const warnings = [];
    let c;
    if (a.h_given) c = catenary(v, a, v.T_0);
    else { const q = catenaryFromTop(v, a, v.T_0); c = q.c; if (q.slack) warnings.push('The specified top tension does not exceed the weight of a vertically hanging line: the line is slack and the horizontal tension is effectively zero.'); }
    const H = c.H, Xof = h => catenary(v, a, h).X, dH = 1e-4 * H, kh = 2 * dH / (Xof(H + dH) - Xof(H - dH));
    if (c.Va > 0) warnings.push('The whole line is lifted off the seabed: the anchor carries uplift. Drag-embedment anchors are not designed for this; lengthen the line or reduce tension.');
    if (c.Ttop > v.MBL) warnings.push('The fairlead tension exceeds the minimum breaking load.');
    const Hs = N.logspace(0.1 * H, 4 * H, 50), cs = Hs.map(h => catenary(v, a, h));
    const sg = N.linspace(0, c.s, 80), px = [0, ...sg.map(q => c.xg + c.xOf(c.Va, q))], pz = [-v.d, ...sg.map(q => -v.d + c.zOf(c.Va, q))];
    const sAll = N.linspace(0, c.Lt, 100), mu = a.no_friction ? 0 : v.mu_s;
    const tens = sAll.map(q => (q < c.Lg ? Math.max(H - mu * v.w * (c.Lg - q), 0) : Math.hypot(H, c.Va + v.w * (q - c.Lg))));
    return {
      scalars: [
        scalar('T_H', 'Horizontal tension', H, 'N', { show: 'kN' }), scalar('T_top', 'Tension at the fairlead', c.Ttop, 'N', { show: 'kN' }),
        scalar('V_top', 'Vertical load on the fairlead', c.Vt, 'N', { show: 'kN' }), scalar('theta_top', 'Line angle to the horizontal at the fairlead', c.theta, 'rad', { show: 'deg' }),
        scalar('a_c', 'Catenary parameter T_H/w', c.ac, 'm'), scalar('s_s', 'Suspended length', c.s, 'm'), scalar('L_g', 'Length resting on the seabed', c.Lg, 'm', { note: c.Lg > 0 ? 'anchor loaded horizontally' : 'no grounded line' }),
        scalar('x_s', 'Horizontal span of the suspended length', c.xs, 'm'), scalar('X', 'Horizontal distance from anchor to fairlead', c.X, 'm'),
        scalar('T_a', 'Tension at the anchor', c.Ta, 'N', { show: 'kN' }), scalar('V_a', 'Uplift at the anchor', c.Va, 'N', { show: 'kN' }),
        scalar('k_h', 'Horizontal restoring stiffness', kh, 'N/m', { show: 'kN/m' }), scalar('SF', 'Safety factor on breaking load', v.MBL / c.Ttop, '1'),
      ],
      series: [
        line('tension-offset', 'Tension against fairlead excursion', 'Excursion from the operating point', 'm', cs.map(q => q.X - c.X), [{ label: 'Horizontal tension', data: Hs.map(h => h / 1e3) }, { label: 'Fairlead tension', data: cs.map(q => q.Ttop / 1e3), dash: true }], 'Tension', 'kN'),
        line('profile', 'Line profile', 'Distance from anchor', 'm', px, [{ label: 'Mooring line', data: pz }], 'Elevation relative to the fairlead', 'm'),
        line('tension-along', 'Tension along the line', 'Arc length from anchor', 'm', sAll, [{ label: 'Tension', data: tens.map(q => q / 1e3) }], 'Tension', 'kN'),
      ],
      checks: [check('Vertical span closes on the water depth', c.resid, 1e-8, 'Integrated catenary height against depth')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b0 = { ...a, inelastic: true, h_given: true, no_friction: true }, H = v.T_0, c = catenary(v, b0, H), ac = H / v.w, out = [];
    if (c.Va > 0) return out;
    const ce = catenary({ ...v, EA: 1e30 }, { ...b0, inelastic: false }, H);
    out.push(bench('Suspended length from the root-finder vs √(d(d + 2a))', ce.s, Math.sqrt(v.d * (v.d + 2 * ac)), 'Classical inelastic catenary', 1e-9));
    out.push(bench('Fairlead tension T = T_H + w·d', c.Ttop, H + v.w * v.d, 'Classical inelastic catenary', 1e-12));
    out.push(bench('Suspended span vs a·cosh⁻¹(1 + d/a)', c.xs, ac * Math.acosh(1 + v.d / ac), 'Classical inelastic catenary', 1e-10));
    const dH = 1e-4 * H, kn = 2 * dH / (catenary(v, b0, H + dH).X - catenary(v, b0, H - dH).X);
    out.push(bench('Horizontal stiffness vs analytical derivative', kn, v.w / (Math.acosh(1 + v.d / ac) - 2 / Math.sqrt(1 + 2 * ac / v.d)), 'Faltinsen (1990), catenary line stiffness', 1e-5));
    return out;
  },
  validation: [],
  diagram(v) {
    const pts = Array.from({ length: 30 }, (_, i) => { const u = i / 29; return [250 + 290 * u, 290 - 200 * (Math.cosh(2.2 * u) - 1) / (Math.cosh(2.2) - 1)]; });
    return svg(`
      ${S.rect(30, 80, 580, 210, 'd-liquid', 0)} ${S.path('M30 80 L610 80', 'd-liquid-line')} ${S.path('M30 290 L610 290', 'd-ground')}
      ${S.rect(520, 56, 80, 40, 'd-body')} ${S.text(560, 48, 'vessel')}
      ${S.line(70, 290, 250, 290, 'd-pipe')} ${S.poly(pts, 'd-pipe')}
      ${S.path('M60 290 l10 -12 l10 12 z', 'd-body')} ${S.text(70, 312, 'anchor')}
      ${S.text(250, 312, 'touchdown')} ${S.text(160, 280, 'grounded length')}
      ${S.arrow(545, 96, 600, 96)} ${S.text(604, 114, 'T_H', 'd-text', 'end')}
      ${S.arrow(540, 90, 512, 40, 'd-arrow d-hazard')} ${S.text(500, 36, 'T_top', 'd-text', 'end')}
      ${S.dim(40, 80, 40, 290, '')} ${S.text(52, 190, `d = ${lab(v.d, 'm')}`, 'd-text d-small', 'start')}
      ${S.dim(70, 334, 540, 334, 'X')}
      ${S.text(320, 30, `w = ${lab(v.w, 'N/m')}   line length = ${lab(v.scope * v.d, 'm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the tension–excursion characteristic of a model chain line and compare it with the catenary solution.',
    apparatus: ['Model chain of known submerged weight per unit length in a deep basin or dry rig', 'Fairlead mounted on a traverse with a measured horizontal position', 'Flat false floor representing the seabed'],
    instruments: [{ name: 'In-line load cell at the fairlead', measures: 'Top tension', range: '0–100 N', resolution: '±0.2 %' }, { name: 'Inclinometer on the top link', measures: 'Line angle at the fairlead', range: '0–90°', resolution: '±0.1°' }, { name: 'Linear encoder on the traverse', measures: 'Fairlead excursion', range: '0–2 m', resolution: '±0.5 mm' }, { name: 'Underwater camera', measures: 'Touchdown position', range: '—', resolution: '±5 mm' }],
    procedure: ['Weigh a measured length of the chain in water to obtain w.', 'Move the fairlead outward in steps, recording tension, angle and touchdown position after motion has ceased.', 'Reverse the traverse to reveal hysteresis from seabed friction.'],
    controls: ['Check that the load cell reads the hanging weight w·d with the line vertical', 'Repeat with a second chain size'],
    signatures: ['Top tension minus horizontal tension equal to w·d', 'Suspended length equal to √(d(d + 2T_H/w))', 'Stiffness rising steeply as the grounded length vanishes'],
    safety: ['Keep clear of tensioned lines', 'Rated shackles and load cells'],
  },
  falsify: ['A measured difference between top and horizontal tension that is not w·d for an inextensible line with grounded length.', 'A touchdown position inconsistent with the catenary span by more than the positional uncertainty.'],
  alternatives: [{ name: 'Multi-segment line', text: 'Chain–wire–chain systems are solved segment by segment with continuity of tension components.' }, { name: 'Taut-leg mooring', text: 'Synthetic lines restrain by axial stretch rather than weight; stiffness is EA/L projected on the horizontal.' }, { name: 'Dynamic line analysis', text: 'Includes drag and inertia of the line, which amplify tension at wave frequency in deep water.' }],
  hazards: [{ hazard: 'Line failure', cause: 'Tension above breaking strength, fatigue or wear at the touchdown and fairlead', mitigation: 'Design safety factors, inspection and replacement' }, { hazard: 'Anchor uplift and drag', cause: 'Insufficient grounded length in the extreme offset', mitigation: 'Longer line, clump weights or vertically loaded anchors' }],
  standards: ['DNV-OS-E301 (position mooring)', 'API RP 2SK (stationkeeping systems)', 'ISO 19901-7 (stationkeeping systems for floating offshore structures)'],
  limits: 'A single uniform line in a vertical plane on a flat, horizontal seabed, loaded only by its own submerged weight. No current drag, no bending stiffness, no dynamics. The elastic option assumes a linear axial stiffness.',
  numerics: { method: 'Closed-form catenary; bisection for the elastic suspended length, the anchor uplift and the horizontal tension when top tension is specified; central difference for stiffness' },
  optimise: { objective: 'T_top', sense: 'min', vars: ['scope'], note: 'A longer line does not reduce tension once some line already rests on the bed; it increases the offset capacity before uplift.' },
  inverse: { series: 'tension-offset', fit: ['w'] },
  extensions: ['Multi-line spread mooring with vessel offset equilibrium', 'Chain–wire–chain composite lines and buoys', 'Quasi-dynamic tension amplification'],
};

// ------------------------------------------------------------------ vortex-induced vibration of a riser
/** Facchinetti–de Langre–Biolley wake oscillator coupled to a structural oscillator, in time τ = Ω_f·t. */
function wakeOscillator(p) {
  const delta = p.delta, c = p.c, M = p.M, A = p.A, eps = p.eps, accel = !!p.accel, tauEnd = p.tauEnd || 500, record = !!p.record;
  const d2 = delta * delta, tTail = 0.7 * tauEnd, tRec = tauEnd - 24 * Math.PI, hist = { tau: [], y: [], q: [] };
  let y = 0, yd = 0, q = 2, qd = 0, tau = 0, ya = 0, qa = 0, steps = 0, lastRec = -1;
  let fy = NaN, ly = NaN, ny = 0, fq = NaN, lq = NaN, nq = 0;
  while (tau < tauEnd && steps < 400000) {
    // step limited by the stiffness of the van der Pol damping term so that the explicit scheme stays stable
    const h = Math.min(0.08, 1.2 / (eps * q * q + 1), tauEnd - tau), h2 = 0.5 * h;
    const a1 = -c * yd - d2 * y + M * q, b1 = -eps * (q * q - 1) * qd - q + A * (accel ? a1 : yd);
    const y2 = y + h2 * yd, v2 = yd + h2 * a1, q2 = q + h2 * qd, w2 = qd + h2 * b1;
    const a2 = -c * v2 - d2 * y2 + M * q2, b2 = -eps * (q2 * q2 - 1) * w2 - q2 + A * (accel ? a2 : v2);
    const y3 = y + h2 * v2, v3 = yd + h2 * a2, q3 = q + h2 * w2, w3 = qd + h2 * b2;
    const a3 = -c * v3 - d2 * y3 + M * q3, b3 = -eps * (q3 * q3 - 1) * w3 - q3 + A * (accel ? a3 : v3);
    const y4 = y + h * v3, v4 = yd + h * a3, q4 = q + h * w3, w4 = qd + h * b3;
    const a4 = -c * v4 - d2 * y4 + M * q4, b4 = -eps * (q4 * q4 - 1) * w4 - q4 + A * (accel ? a4 : v4);
    const yn = y + h / 6 * (yd + 2 * v2 + 2 * v3 + v4), qn = q + h / 6 * (qd + 2 * w2 + 2 * w3 + w4);
    yd += h / 6 * (a1 + 2 * a2 + 2 * a3 + a4); qd += h / 6 * (b1 + 2 * b2 + 2 * b3 + b4);
    if (!(Math.abs(yn) < 1e6 && Math.abs(qn) < 1e6)) break;
    if (tau >= tTail) {
      if (Math.abs(yn) > ya) ya = Math.abs(yn);
      if (Math.abs(qn) > qa) qa = Math.abs(qn);
      if (y < 0 && yn >= 0) { const tc = tau + h * y / (y - yn); if (ny === 0) fy = tc; ly = tc; ny++; }
      if (q < 0 && qn >= 0) { const tc = tau + h * q / (q - qn); if (nq === 0) fq = tc; lq = tc; nq++; }
    }
    y = yn; q = qn; tau += h; steps++;
    if (record && tau >= tRec && tau - lastRec >= 0.1) { hist.tau.push(tau); hist.y.push(y); hist.q.push(q); lastRec = tau; }
  }
  return { ya, qa, wResp: ny >= 2 ? 2 * Math.PI * (ny - 1) / (ly - fy) : NaN, wWake: nq >= 2 ? 2 * Math.PI * (nq - 1) / (lq - fq) : NaN, hist, complete: tau >= tauEnd };
}
const riserFreq = (n, L, T, m, EI) => n / (2 * L) * Math.sqrt(T / m + n * n * Math.PI ** 2 * EI / (m * L * L));
const riserViv = {
  id: 'riser-viv', heavy: true,
  title: 'Vortex-induced vibration of a tensioned riser',
  module: 2, klass: 'I', domains: ['fsi', 'offshore'],
  keywords: ['vortex-induced vibration', 'vortex induced vibration', 'viv', 'riser viv', 'lock-in', 'strouhal', 'vortex shedding', 'wake oscillator', 'reduced velocity', 'riser', 'tensioned riser', 'cross-flow vibration', 'van der pol', 'free span', 'cylinder vibration'],
  summary: 'Strouhal shedding frequency, tensioned-beam natural frequencies, the mode nearest lock-in, and cross-flow amplitude from a van der Pol wake oscillator coupled to the structure; bending-stress amplitude for fatigue.',
  background: [
    'A bluff cylinder in a steady current sheds vortices alternately from each side at a frequency set by the Strouhal number. The alternating lift can excite a flexible structure when the shedding frequency approaches a natural frequency. The motion then organises the wake, the shedding frequency locks on to the structural frequency over a range of flow speeds, and the amplitude is self-limited at about one diameter.',
    'Wake-oscillator models represent the fluctuating lift by a single variable that obeys a van der Pol equation, giving a self-sustained oscillation at the Strouhal frequency, and couple it to the structure. In the model of Facchinetti, de Langre and Biolley the wake is forced by the structural acceleration, the choice that reproduced lock-in and lift magnification most faithfully in their comparison.',
  ],
  phenomena: ['Kármán vortex shedding', 'Lock-in (synchronisation)', 'Self-limited limit-cycle response', 'Fluid added mass and damping', 'Bending fatigue'],
  laws: ['momentum', 'newton2', 'hooke'],
  refs: ['Facchinetti, M. L., de Langre, E. & Biolley, F. (2004). Coupling of structure and wake oscillators in vortex-induced vibrations. Journal of Fluids and Structures 19, 123–140.', 'Blevins, R. D. (1990). Flow-Induced Vibration, 2nd ed. Van Nostrand Reinhold.', 'Williamson, C. H. K. & Govardhan, R. (2004). Vortex-induced vibrations. Annual Review of Fluid Mechanics 36, 413–455.', 'Sarpkaya, T. (2004). A critical review of the intrinsic nature of vortex-induced vibrations. Journal of Fluids and Structures 19, 389–447.', 'DNV-RP-F204. Riser fatigue. DNV, Høvik.'],
  inputs: [
    inp('U', 'Current speed normal to the riser', 'm/s', 1.0, { min: 0.05, max: 3, kind: 'environment', env: 'current_speed', aliases: ['current', 'current speed', 'flow speed', 'velocity'] }),
    inp('D', 'Outer (hydrodynamic) diameter', 'm', 0.30, { min: 0.1, max: 1.5, kind: 'geometry', aliases: ['diameter', 'outer diameter'] }),
    inp('t_w', 'Wall thickness', 'mm', 20, { min: 3, max: 45, kind: 'geometry', aliases: ['wall thickness', 'wall'] }),
    inp('L', 'Riser length between supports', 'm', 500, { min: 5, max: 3000, kind: 'geometry', aliases: ['length', 'riser length', 'span'] }),
    inp('T_top', 'Effective top tension', 'kN', 1500, { min: 10, max: 20000, aliases: ['top tension', 'tension'] }),
    inp('E', 'Young\'s modulus', 'GPa', 207, { min: 1, max: 450, kind: 'geometry', aliases: ['young\'s modulus', 'elastic modulus', 'modulus'] }),
    inp('rho_s', 'Pipe material density', 'kg/m^3', 7850, { min: 900, max: 9000, kind: 'geometry', aliases: ['steel density', 'material density'] }),
    inp('rho_i', 'Density of the internal fluid', 'kg/m^3', 800, { min: 0, max: 2000, kind: 'fluid', aliases: ['contents density', 'internal fluid density'] }),
    inp('rho', 'Sea-water density', 'kg/m^3', 1025, { min: 990, max: 1040, kind: 'fluid', aliases: ['water density'] }),
    inp('St', 'Strouhal number', '1', 0.2, { min: 0.1, max: 0.3, kind: 'fluid', aliases: ['strouhal'], src: 'Sub-critical Reynolds number; Blevins (1990)' }),
    inp('C_L0', 'Lift coefficient of the fixed cylinder', '1', 0.3, { min: 0.05, max: 1, kind: 'fluid', aliases: ['lift coefficient'], src: 'Facchinetti et al. (2004)' }),
    inp('C_Ds', 'Sectional drag coefficient in the fluid-damping term', '1', 2.0, { min: 0.5, max: 4, kind: 'fluid', aliases: ['drag coefficient'], src: 'Amplified drag of an oscillating cylinder; gives the stall parameter γ = 0.8 used by Facchinetti et al. (2004)' }),
    inp('C_a', 'Added-mass coefficient', '1', 1.0, { min: 0.5, max: 1.5, kind: 'fluid', aliases: ['added mass coefficient'] }),
    inp('zeta_s', 'Structural damping ratio', '1', 0.003, { min: 0, max: 0.05, kind: 'geometry', aliases: ['structural damping', 'damping ratio'] }),
    inp('A_c', 'Wake coupling parameter A', '1', 12, { min: 1, max: 30, kind: 'fluid', aliases: ['coupling parameter'], src: 'Fitted to forced-vibration lift data by Facchinetti et al. (2004)' }),
    inp('eps_w', 'Van der Pol parameter ε', '1', 0.3, { min: 0.02, max: 2, kind: 'fluid', aliases: ['van der pol parameter'], src: 'Facchinetti et al. (2004)' }),
  ],
  assumptions: [
    asm('accel_coupling', 'The wake oscillator is forced by the structural acceleration.', { why: 'The coupling found most satisfactory by Facchinetti et al.', alt: 'Velocity coupling is used instead: the forcing is proportional to the structural velocity.' }),
    asm('beam', 'The riser is a tensioned Euler–Bernoulli beam with pinned ends.', { why: 'Bending stiffness matters for higher modes', alt: 'The riser is treated as a taut string; bending stiffness is neglected in the natural frequencies.' }),
    asm('const_tension', 'Effective tension is uniform along the riser and equal to the top tension.', { why: 'Short riser or small weight', alt: 'The mean of top and bottom tension is used, the bottom value being reduced by the submerged weight of the riser.' }),
    asm('rigid_equiv', 'The modal amplitude equals the amplitude of the equivalent rigid, spring-mounted cylinder.', { why: 'Direct use of the two-oscillator result', alt: 'The amplitude at the antinode is multiplied by the mode-shape factor √(4/3) ≈ 1.155 of a sinusoidal mode (Blevins 1990).' }),
  ],
  symbols: { f_s: ['Vortex-shedding frequency', '1/s'], Omega_f: ['Shedding angular frequency', '1/s'], m_s: ['Structural mass per unit length including contents', 'kg/m'], m_t: ['Total mass per unit length including added mass', 'kg/m'], T_e: ['Effective tension', 'N'], w_s: ['Submerged weight per unit length', 'N/m'], I_b: ['Second moment of area', 'm^4'], n_m: ['Mode number', '1'], f_n: ['Natural frequency of mode n', '1/s'], omega_n: ['Natural angular frequency', '1/s'], U_r: ['Reduced velocity', '1'], y: ['Cross-flow displacement', 'm'], q: ['Wake variable (reduced lift)', '1'], t: ['Time', 's'], r_t: ['Total damping per unit length', 'kg/(m s)'], gamma_f: ['Stall parameter', '1'], y_0: ['Limit-cycle amplitude of the oscillator pair', 'm'], A_y: ['Displacement amplitude at the antinode', 'm'], sigma_a: ['Bending-stress amplitude', 'Pa'] },
  equations: a => [
    eq('fs', 'Strouhal relation', 'f_s', 'St*U/D', { kind: 'empirical', origin: 'Strouhal (1878); constant St over the sub-critical Reynolds-number range' }),
    eq('of', 'Shedding angular frequency', 'Omega_f', '2*pi*f_s', { kind: 'definition' }),
    eq('mt', 'Mass per unit length', 'm_t', 'm_s + C_a*rho*pi*D^2/4', { kind: 'definition' }),
    a.const_tension ? eq('te', 'Effective tension', 'T_e', 'T_top', { kind: 'closure', needs: ['const_tension'] }) : eq('te', 'Mean effective tension', 'T_e', 'T_top - w_s*L/2', { kind: 'derived', origin: 'Axial equilibrium of a vertical riser' }),
    a.beam
      ? eq('fn', 'Tensioned-beam natural frequency', 'f_n', 'n_m/(2*L)*sqrt(T_e/m_t + n_m^2*pi^2*E*I_b/(m_t*L^2))', { kind: 'derived', origin: 'Pinned–pinned Euler–Bernoulli beam under axial tension', needs: ['beam'] })
      : eq('fn', 'Taut-string natural frequency', 'f_n', 'n_m/(2*L)*sqrt(T_e/m_t)', { kind: 'derived', origin: 'Wave equation for a string' }),
    eq('on', 'Natural angular frequency', 'omega_n', '2*pi*f_n', { kind: 'definition' }),
    eq('ur', 'Reduced velocity', 'U_r', 'U/(f_n*D)', { kind: 'definition' }),
    eq('gam', 'Stall parameter', 'gamma_f', 'C_Ds/(4*pi*St)', { kind: 'closure', origin: 'Facchinetti et al. (2004)' }),
    eq('rt', 'Damping per unit length', 'r_t', '2*zeta_s*m_t*omega_n + gamma_f*Omega_f*rho*D^2', { kind: 'closure', origin: 'Structural damping plus fluid-added (stall) damping; Facchinetti et al. (2004)' }),
    eq('str', 'Structural oscillator', 'm_t*d2(y,t) + r_t*d(y,t) + m_t*omega_n^2*y', '0.25*rho*U^2*D*C_L0*q', { kind: 'law', origin: 'Newton\'s second law for the lock-in mode with lift C_L = C_L0·q/2' }),
    a.accel_coupling
      ? eq('wake', 'Wake oscillator', 'd2(q,t) + eps_w*Omega_f*(q^2 - 1)*d(q,t) + Omega_f^2*q', 'A_c/D*d2(y,t)', { kind: 'hypothesis', origin: 'Van der Pol wake oscillator with acceleration coupling; Facchinetti et al. (2004)', needs: ['accel_coupling'] })
      : eq('wake', 'Wake oscillator', 'd2(q,t) + eps_w*Omega_f*(q^2 - 1)*d(q,t) + Omega_f^2*q', 'A_c*Omega_f/D*d(y,t)', { kind: 'hypothesis', origin: 'Van der Pol wake oscillator with velocity coupling; Facchinetti et al. (2004)' }),
    a.rigid_equiv ? eq('amp', 'Modal amplitude', 'A_y', 'y_0', { kind: 'closure', needs: ['rigid_equiv'] }) : eq('amp', 'Modal amplitude with mode-shape factor', 'A_y', 'sqrt(4/3)*y_0', { kind: 'derived', origin: 'Mode-shape factor ψ_max·√(∫ψ²/∫ψ⁴) for a sinusoidal mode; Blevins (1990)' }),
    eq('sig', 'Bending-stress amplitude', 'sigma_a', 'E*D/2*(n_m*pi/L)^2*A_y', { kind: 'derived', origin: 'Curvature of a sinusoidal mode shape' }),
  ],
  derivation: a => [
    { text: 'Vortices are shed at a frequency proportional to flow speed over diameter. Lock-in is expected when this frequency is close to a natural frequency, that is at a reduced velocity near 1/St.', tex: 'f_s = St\\,\\frac{U}{D},\\qquad U_r = \\frac{U}{f_n D} \\approx \\frac{1}{St}' },
    { text: `Separating variables in the equation of a ${a.beam ? 'tensioned beam' : 'taut string'} with pinned ends gives sinusoidal modes and their frequencies.`, tex: a.beam ? 'f_n = \\frac{n}{2L}\\sqrt{\\frac{T_e}{m} + \\frac{n^2\\pi^2 EI}{m L^2}}' : 'f_n = \\frac{n}{2L}\\sqrt{\\frac{T_e}{m}}' },
    { text: 'The fluctuating lift is written C_L = C_L0·q/2, where the wake variable q obeys a van der Pol equation with natural frequency Ω_f: it has a stable limit cycle of amplitude 2 when the cylinder is fixed.', tex: '\\ddot q + \\varepsilon\\,\\Omega_f\\,(q^2-1)\\,\\dot q + \\Omega_f^2\\,q = ' + (a.accel_coupling ? '\\frac{A}{D}\\,\\ddot y' : '\\frac{A\\,\\Omega_f}{D}\\,\\dot y') },
    { text: 'The structure is a damped oscillator at the modal frequency driven by that lift. In time scaled by Ω_f and displacement by D the pair depends on the frequency ratio δ = f_n/f_s, the mass number M = C_L0/(16π²St²μ) with μ = m/(ρD²), and the damping.', tex: 'y\'\' + \\left(2\\xi\\delta + \\frac{\\gamma}{\\mu}\\right)y\' + \\delta^2 y = M q,\\qquad q\'\' + \\varepsilon(q^2-1)q\' + q = ' + (a.accel_coupling ? 'A\\,y\'\'' : 'A\\,y\'') },
    { text: 'For a sinusoidal mode of amplitude A_y the peak curvature is A_y(nπ/L)², which gives the bending-stress amplitude at the outer fibre.', tex: '\\sigma_a = E\\,\\frac{D}{2}\\left(\\frac{n\\pi}{L}\\right)^2 A_y' },
  ],
  solve(v, a) {
    const D = v.D, Di = D - 2 * v.t_w, As = Math.PI * (D * D - Di * Di) / 4, Ai = Math.PI * Di * Di / 4, Ad = Math.PI * D * D / 4;
    const I = Math.PI * (D ** 4 - Di ** 4) / 64, EI = a.beam ? v.E * I : 0;
    const ms = v.rho_s * As + v.rho_i * Ai, mt = ms + v.C_a * v.rho * Ad, ws = (ms - v.rho * Ad) * g, warnings = [];
    let Te = v.T_top;
    if (!a.const_tension) { Te = v.T_top - ws * v.L / 2; if (Te < 0.05 * v.T_top) { Te = 0.05 * v.T_top; warnings.push('The top tension does not support the submerged weight of the riser: the mean tension has been limited to 5 % of the top tension. Increase the top tension.'); } }
    const fs = v.St * v.U / D, fn = n => riserFreq(n, v.L, Te, mt, EI), nMax = 400;
    let n = 1; while (n < nMax && fn(n + 1) <= fs) n++;
    if (n < nMax && Math.abs(fn(n + 1) - fs) < Math.abs(fn(n) - fs)) n++;
    if (n >= nMax) warnings.push('The shedding frequency lies above the 400th mode; the riser responds as an infinitely long cable and the single-mode picture does not apply.');
    const fN = fn(n), mu = mt / (v.rho * D * D), Mn = v.C_L0 / (16 * Math.PI ** 2 * v.St ** 2 * mu), gam = v.C_Ds / (4 * Math.PI * v.St), shapeF = a.rigid_equiv ? 1 : Math.sqrt(4 / 3);
    const run = (delta, record) => wakeOscillator({ delta, c: 2 * v.zeta_s * delta + gam / mu, M: Mn, A: v.A_c, eps: v.eps_w, accel: a.accel_coupling, record });
    const delta = fN / fs, op = run(delta, true), Ur = v.U / (fN * D), Ay = shapeF * op.ya * D;
    if (!op.complete) warnings.push('The oscillator integration did not reach a steady state within the step budget; the amplitude is indicative only.');
    if (v.A_c * Mn >= 1) warnings.push('The product of coupling parameter and mass number exceeds one: the structure is too light for this wake-oscillator calibration and the amplitude is not reliable.');
    const sig = v.E * D / 2 * (n * Math.PI / v.L) ** 2 * Ay, fResp = Number.isFinite(op.wResp) ? op.wResp * fs : fN;
    const urs = N.linspace(2, 12, 31), amp = urs.map(u => shapeF * run(1 / (v.St * u), false).ya);
    const nShow = Math.min(Math.max(n + 5, 10), 60), ns = Array.from({ length: nShow }, (_, i) => i + 1);
    const Of = 2 * Math.PI * fs, x = N.linspace(0, v.L, 121), ph = N.linspace(0, 2 * Math.PI, 25);
    const locked = Ur > 4 && Ur < 8;
    return {
      scalars: [
        scalar('f_s', 'Vortex-shedding frequency', fs, '1/s', { show: 'Hz' }), scalar('n_m', 'Mode nearest the shedding frequency', n, '1'),
        scalar('f_n', 'Natural frequency of that mode', fN, '1/s', { show: 'Hz' }), scalar('f_1', 'Fundamental natural frequency', fn(1), '1/s', { show: 'Hz' }),
        scalar('U_r', 'Reduced velocity U/(f_n·D)', Ur, '1', { note: locked ? 'inside the usual 4–8 cross-flow lock-in band' : 'outside the usual 4–8 cross-flow lock-in band' }),
        scalar('m_star', 'Mass ratio (structure and contents to displaced water)', ms / (v.rho * Ad), '1'), scalar('mu', 'Mass number m/(ρD²)', mu, '1'),
        scalar('S_G', 'Skop–Griffin parameter', 8 * Math.PI ** 2 * v.St ** 2 * mu * v.zeta_s, '1'), scalar('T_e', 'Effective tension used', Te, 'N', { show: 'kN' }),
        scalar('A_D', 'Cross-flow amplitude over diameter', shapeF * op.ya, '1'), scalar('A_y', 'Cross-flow amplitude', Ay, 'm'),
        scalar('q_0', 'Wake-variable amplitude (lift magnification × 2)', op.qa, '1'), scalar('f_resp', 'Response frequency', fResp, '1/s', { show: 'Hz' }),
        scalar('sigma_a', 'Bending-stress amplitude', sig, 'Pa', { show: 'MPa' }), scalar('S_r', 'Stress range for fatigue', 2 * sig, 'Pa', { show: 'MPa' }),
        scalar('N_yr', 'Stress cycles per year at this current', fResp * 3.15576e7, '1'),
      ],
      series: [
        line('amp-ur', 'Response amplitude against reduced velocity', 'Reduced velocity U/(f_n·D)', '–', urs, [{ label: 'Amplitude A/D', data: amp }], 'Amplitude / diameter', '–', { points: [{ x: Ur, y: shapeF * op.ya }], pointsLabel: 'Operating point' }),
        line('history', 'Structure and wake over the last twelve shedding periods', 'Time', 's', op.hist.tau.map(t => t / Of), [{ label: 'Displacement y/D', data: op.hist.y }, { label: 'Wake variable q/10', data: op.hist.q.map(z => z / 10), dash: true }], 'Amplitude', '–'),
        line('modes', 'Natural frequencies and the shedding frequency', 'Mode number', '–', ns, [{ label: 'Natural frequency', data: ns.map(fn) }, { label: 'Shedding frequency', data: ns.map(() => fs), dash: true }], 'Frequency', 'Hz'),
      ],
      anims: [anim('mode-shape', 'Riser deflection in the lock-in mode', 'Distance along the riser', 'm', x, ph.map(p => x.map(s => Ay * Math.sin(n * Math.PI * s / v.L) * Math.cos(p))), ph.map(p => p / (2 * Math.PI * Math.max(fResp, 1e-9))), 'Cross-flow displacement', 'm')],
      checks: [check('Selected mode brackets the shedding frequency', n > 1 && n < nMax ? Math.max(0, Math.abs(fN - fs) - Math.max(fn(n + 1) - fN, fN - fn(n - 1))) / fs : 0, 1e-9, 'Distance to the shedding frequency no larger than the local mode spacing')],
      warnings,
    };
  },
  benchmarks(v) {
    const out = [], free = wakeOscillator({ delta: 1, c: 0.1, M: 0, A: 0, eps: v.eps_w, accel: true });
    out.push(bench('Free wake oscillator: van der Pol limit-cycle amplitude', free.qa, 2, 'Limit-cycle amplitude 2 for small ε (method of averaging)', 2e-2));
    out.push(bench('Free wake oscillator: frequency equals the shedding frequency', free.wWake, 1, 'Van der Pol oscillator, small ε', 2e-2));
    out.push(bench('Taut-string fundamental', riserFreq(1, 100, 1e5, 50, 0), Math.sqrt(1e5 / 50) / 200, 'f₁ = (1/2L)√(T/m)', 1e-12));
    out.push(bench('Pinned beam fundamental without tension', riserFreq(1, 10, 0, 50, 2e6), Math.PI / 200 * Math.sqrt(2e6 / 50), 'f₁ = (π/2L²)√(EI/m)', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    const pts = Array.from({ length: 41 }, (_, i) => [320 + 26 * Math.sin(i / 40 * 3 * Math.PI), 60 + i * 6]);
    return svg(`
      ${S.rect(30, 60, 580, 240, 'd-liquid', 0)} ${S.path('M30 60 L610 60', 'd-liquid-line')} ${S.path('M30 300 L610 300', 'd-ground')}
      ${S.rect(280, 30, 80, 30, 'd-body')} ${S.text(320, 24, 'platform')}
      ${S.line(320, 60, 320, 300, 'd-dim')} ${S.poly(pts, 'd-pipe')}
      ${[0, 1, 2, 3].map(i => S.arrow(70, 100 + i * 50, 170, 100 + i * 50)).join('')} ${S.text(120, 86, `U = ${lab(v.U, 'm/s')}`)}
      ${S.circle(470, 180, 16, 'd-body')} ${S.path('M492 170 q10 -12 20 0 q10 12 20 0', 'd-line')} ${S.path('M502 192 q10 12 20 0 q10 -12 20 0', 'd-line')}
      ${S.arrow(470, 150, 470, 120, 'd-arrow d-hazard')} ${S.arrow(470, 210, 470, 240, 'd-arrow d-hazard')} ${S.text(470, 262, 'cross-flow motion')}
      ${S.text(520, 150, 'vortex street')}
      ${S.arrow(320, 60, 320, 36, 'd-arrow')} ${S.text(372, 50, `T = ${lab(v.T_top / 1e3, 'kN')}`, 'd-text', 'start')}
      ${S.text(250, 330, `L = ${lab(v.L, 'm')}   D = ${lab(v.D, 'm')}   f_s = St·U/D = ${lab(v.St * v.U / v.D, 'Hz')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the cross-flow response of a flexibly mounted or flexible cylinder over a range of reduced velocity and compare amplitude and lock-in range with the model.',
    apparatus: ['Towing tank or water channel with low turbulence', 'Smooth cylinder on air bearings and springs (rigid test) or a tensioned flexible pipe model', 'Adjustable damping device'],
    instruments: [{ name: 'Non-contact displacement sensor', measures: 'Cross-flow displacement', range: '±2 D', resolution: '±0.5 %' }, { name: 'Fibre-optic or foil strain gauges along the span', measures: 'Bending strain and mode shape', range: '±2000 µε', resolution: '±1 µε' }, { name: 'Hot-film or particle image velocimetry in the wake', measures: 'Shedding frequency and wake mode', range: '—', resolution: '—' }, { name: 'Load cell at the top end', measures: 'Tension', range: '0–5 kN', resolution: '±0.2 %' }],
    procedure: ['Measure natural frequency and damping in still water by a pluck test.', 'Increase flow speed in small steps through reduced velocities 2–14, recording at least 100 cycles after transients have decayed.', 'Repeat with decreasing speed to detect hysteresis between response branches.'],
    controls: ['Stationary-cylinder run to measure St and lift', 'Repeat at a second mass-damping value'],
    signatures: ['Response frequency locking to the natural frequency over a band of reduced velocity', 'Peak amplitude decreasing with the Skop–Griffin mass-damping parameter', 'Wake frequency following St·U/D outside lock-in'],
    safety: ['Guard moving carriage and tensioned model', 'Limit amplitude with end stops'],
  },
  falsify: ['Absence of a lock-in band near U_r ≈ 1/St for a lightly damped cylinder.', 'A peak amplitude that does not fall as mass-damping is increased.'],
  alternatives: [{ name: 'Empirical response models', text: 'Amplitude read from a response curve against reduced velocity and a stability parameter, as in recommended practices for free spans and risers.' }, { name: 'Semi-empirical frequency-domain tools', text: 'Excitation and damping coefficients from forced-vibration tests applied mode by mode with sheared current.' }, { name: 'Computational fluid dynamics with a moving cylinder', text: 'Resolves the wake directly; costly at field Reynolds numbers.' }],
  hazards: [{ hazard: 'Fatigue failure', cause: 'High-cycle bending stress at girth welds and connectors', mitigation: 'Strakes or fairings, tension management, fatigue monitoring' }, { hazard: 'Clashing of adjacent risers', cause: 'Amplified drag and in-line deflection during lock-in', mitigation: 'Spacing, suppression devices' }],
  standards: ['DNV-RP-F204 (riser fatigue)', 'DNV-RP-C205 (environmental conditions and environmental loads)', 'API RP 2RD (dynamic risers for floating production systems)', 'DNV-RP-F105 (free spanning pipelines)'],
  limits: 'Uniform current normal to a uniform riser, single-mode cross-flow response, sub-critical Strouhal number. The wake oscillator captures lock-in qualitatively; it tends to under-estimate peak amplitude at very low mass-damping, where experiments show about one diameter. Sheared current, multi-mode response, in-line vibration and suppression devices are not modelled.',
  numerics: { method: 'Fourth-order Runge–Kutta on the coupled oscillators in dimensionless time (step at most 0.08, 500 time units); amplitude from the last 30 % of the record; 31-point sweep of reduced velocity', order: 4 },
  optimise: { objective: 'sigma_a', sense: 'min', vars: ['T_top'], note: 'Tension shifts the natural frequencies and so the excited mode; the stress does not vary monotonically.' },
  inverse: { series: 'amp-ur', fit: ['A_c', 'C_L0'] },
  extensions: ['Sheared current with power-in and power-out regions', 'Distributed wake oscillators along the span (travelling-wave response)', 'Fatigue damage from a long-term current distribution'],
};

// ------------------------------------------------------------------ pipe conveying fluid
function pipeProps(v, a) {
  const Do = v.D_o, t = Math.min(v.t_w, 0.45 * Do), Di = Do - 2 * t, Ai = Math.PI * Di * Di / 4;
  const EI = v.E * Math.PI * (Do ** 4 - Di ** 4) / 64, mp = v.rho_p * Math.PI * (Do * Do - Di * Di) / 4, mf = v.rho_f * Ai;
  const me = a.in_air ? 0 : v.rho_e * Math.PI * Do * Do / 4, m = mp + mf + me, Ne = v.T_0 - (a.no_pressure ? 0 : v.p * Ai);
  const uc2 = (EI * (Math.PI / v.L) ** 2 + Ne) / mf;
  return { Do, t, Di, Ai, EI, mp, mf, me, m, Ne, Uc: uc2 > 0 ? Math.sqrt(uc2) : 0, thin: t < v.t_w };
}
/** First natural angular frequency squared at flow velocity U (negative when the pipe has diverged). */
function pipeOmega2(P, L, U, oneMode) {
  const kn = n => P.EI * (n * Math.PI / L) ** 4 + (P.Ne - P.mf * U * U) * (n * Math.PI / L) ** 2;
  const k1 = kn(1);
  if (oneMode) return { w1: k1 / P.m, w2: kn(2) / P.m };
  const k2 = kn(2), gc = 16 * P.mf * U / (3 * L), b = P.m * (k1 + k2) + gc * gc, disc = b * b - 4 * P.m * P.m * k1 * k2;
  if (disc < 0) return { w1: NaN, w2: NaN };
  const sq = Math.sqrt(disc), hiRoot = (b + sq) / (2 * P.m * P.m);
  return { w1: hiRoot !== 0 ? k1 * k2 / (P.m * P.m * hiRoot) : 0, w2: hiRoot };
}
const pipeConveying = {
  id: 'pipe-conveying-fluid',
  title: 'Stability of a pipe conveying fluid',
  module: 2, klass: 'I', domains: ['fsi', 'pipeline', 'mechanical'],
  keywords: ['pipe conveying fluid', 'conveying fluid', 'flow-induced buckling', 'divergence', 'critical flow velocity', 'critical velocity', 'païdoussis', 'paidoussis', 'pipe vibration', 'internal flow', 'flow velocity natural frequency', 'pipe span', 'coriolis', 'buckling of pipe'],
  summary: 'Natural frequency of a simply supported pipe as a function of internal flow velocity, the critical velocity at which it buckles (divergence), and the effect of tension, pressure and Coriolis coupling.',
  background: [
    'Fluid flowing through a flexible pipe must follow the pipe\'s curvature and rotation. The momentum change produces a centrifugal force proportional to the square of the flow velocity, which acts like an axial compression, and a Coriolis force proportional to velocity and to the rate of rotation of the pipe.',
    'For a pipe supported at both ends the centrifugal term lowers the natural frequencies as flow velocity rises until the first one reaches zero: the pipe then buckles statically, an instability called divergence. The critical velocity is that at which the centrifugal force equals the Euler buckling load. The Coriolis term does no net work on a pipe with supported ends but couples the modes and makes them complex.',
  ],
  phenomena: ['Centrifugal softening', 'Coriolis (gyroscopic) coupling', 'Static divergence (buckling)', 'Pressure-induced effective compression'],
  laws: ['momentum', 'newton2', 'hooke'],
  refs: ['Païdoussis, M. P. (2014). Fluid-Structure Interactions: Slender Structures and Axial Flow, Vol. 1, 2nd ed. Academic Press.', 'Housner, G. W. (1952). Bending vibrations of a pipe line containing flowing fluid. Journal of Applied Mechanics 19, 205–208.', 'Païdoussis, M. P. & Issid, N. T. (1974). Dynamic stability of pipes conveying fluid. Journal of Sound and Vibration 33, 267–294.', 'Blevins, R. D. (1990). Flow-Induced Vibration, 2nd ed. Van Nostrand Reinhold.'],
  inputs: [
    inp('L', 'Span between supports', 'm', 10, { min: 0.5, max: 200, kind: 'geometry', aliases: ['span', 'length', 'long'] }),
    inp('D_o', 'Outer diameter', 'mm', 168.3, { min: 10, max: 1500, kind: 'geometry', aliases: ['outer diameter', 'diameter'] }),
    inp('t_w', 'Wall thickness', 'mm', 7.11, { min: 0.5, max: 60, kind: 'geometry', aliases: ['wall thickness', 'wall'] }),
    inp('E', 'Young\'s modulus of the pipe', 'GPa', 207, { min: 0.5, max: 450, kind: 'geometry', aliases: ['young\'s modulus', 'elastic modulus', 'modulus'] }),
    inp('rho_p', 'Pipe material density', 'kg/m^3', 7850, { min: 800, max: 9000, kind: 'geometry', aliases: ['pipe density', 'steel density', 'material density'] }),
    inp('rho_f', 'Density of the conveyed fluid', 'kg/m^3', 1000, { min: 0.5, max: 2000, kind: 'fluid', aliases: ['fluid density', 'density'] }),
    inp('U', 'Mean flow velocity', 'm/s', 5, { min: 0, max: 300, aliases: ['flow velocity', 'velocity', 'flow speed'] }),
    inp('T_0', 'Externally applied axial tension', 'kN', 0, { min: 0, max: 5000, aliases: ['axial tension', 'tension'] }),
    inp('p', 'Internal gauge pressure', 'bar', 10, { min: 0, max: 500, aliases: ['pressure', 'internal pressure'] }),
    inp('rho_e', 'Density of the surrounding fluid', 'kg/m^3', 1025, { min: 1, max: 1100, kind: 'environment', aliases: ['external fluid density', 'sea water density'] }),
  ],
  assumptions: [
    asm('one_mode', 'The response is represented by the first sinusoidal mode alone.', { why: 'Gives the classical closed form; the Coriolis term then drops out', alt: 'A two-mode Galerkin model retains the Coriolis coupling between the first and second modes.' }),
    asm('no_pressure', 'Internal pressure does not reduce the effective axial tension (pressure negligible, or the pressure end-load is carried as tension in the pipe wall, as with closed ends).', { why: 'Low-pressure service or a capped span', alt: 'The pressure end-load is not carried by the wall (sliding joint or bellows at one end), so the pressure acts as an effective compression p·A_i. Axially fixed ends would reduce this to (1 − 2ν)·p·A_i through the Poisson effect, which is not modelled.' }),
    asm('in_air', 'The pipe vibrates in air: the surrounding fluid adds no mass.', { why: 'Topside or in-plant piping', alt: 'The pipe is submerged and the displaced external fluid is added to the vibrating mass (added-mass coefficient 1).' }),
  ],
  symbols: { y: ['Lateral deflection', 'm'], x: ['Distance along the pipe', 'm'], t: ['Time', 's'], I_b: ['Second moment of area of the pipe wall', 'm^4'], A_i: ['Internal flow area', 'm^2'], m_f: ['Fluid mass per unit length', 'kg/m'], m_p: ['Pipe mass per unit length', 'kg/m'], m_t: ['Total vibrating mass per unit length', 'kg/m'], N_e: ['Effective axial tension', 'N'], U_c: ['Critical flow velocity', 'm/s'], omega_0: ['Natural frequency at zero flow', '1/s'], omega_1: ['First natural frequency at velocity U', '1/s'], k_1: ['First modal stiffness', 'N/m^2'], k_2: ['Second modal stiffness', 'N/m^2'], g_c: ['Coriolis coupling coefficient', 'kg/(m s)'] },
  equations: a => [
    eq('mf', 'Fluid mass per unit length', 'm_f', 'rho_f*A_i', { kind: 'definition' }),
    eq('mt', 'Vibrating mass per unit length', 'm_t', `m_p + m_f${a.in_air ? '' : ' + rho_e*pi*D_o^2/4'}`, { kind: 'definition', needs: a.in_air ? ['in_air'] : [] }),
    eq('ne', 'Effective axial tension', 'N_e', a.no_pressure ? 'T_0' : 'T_0 - p*A_i', { kind: 'law', origin: 'Effective tension: wall tension less internal pressure times bore area', needs: a.no_pressure ? ['no_pressure'] : [] }),
    eq('eom', 'Equation of motion', 'm_t*pd2(y,t)', '-E*I_b*pd2(pd2(y,x),x) - (m_f*U^2 - N_e)*pd2(y,x) - 2*m_f*U*pd(pd(y,x),t)', { kind: 'law', origin: 'Newton\'s second law for pipe and fluid elements; Housner (1952), Païdoussis (2014)' }),
    eq('uc', 'Critical velocity for divergence', 'U_c', 'sqrt((E*I_b*(pi/L)^2 + N_e)/m_f)', { kind: 'derived', origin: 'Centrifugal force equal to the Euler load of the first mode' }),
    eq('w0', 'Natural frequency at zero flow', 'omega_0', 'pi/L*sqrt((E*I_b*(pi/L)^2 + N_e)/m_t)', { kind: 'derived', origin: 'Pinned–pinned Euler–Bernoulli beam with axial force' }),
    ...(a.one_mode
      ? [eq('w1', 'Natural frequency with flow', 'omega_1', 'omega_0*sqrt(1 - (U/U_c)^2)', { kind: 'derived', origin: 'One-mode Galerkin projection', needs: ['one_mode'] })]
      : [eq('k1', 'First modal stiffness', 'k_1', 'E*I_b*(pi/L)^4 + (N_e - m_f*U^2)*(pi/L)^2', { kind: 'derived', origin: 'Galerkin projection on sin(πx/L)' }),
        eq('k2', 'Second modal stiffness', 'k_2', 'E*I_b*(2*pi/L)^4 + (N_e - m_f*U^2)*(2*pi/L)^2', { kind: 'derived', origin: 'Galerkin projection on sin(2πx/L)' }),
        eq('gc', 'Coriolis coupling', 'g_c', '16*m_f*U/(3*L)', { kind: 'derived', origin: 'Projection of the Coriolis term between modes 1 and 2' }),
        eq('w1', 'Two-mode frequency equation', '(k_1 - m_t*omega_1^2)*(k_2 - m_t*omega_1^2)', 'omega_1^2*g_c^2', { kind: 'derived', origin: 'Determinant of the gyroscopic two-mode system' })]),
  ],
  derivation: a => [
    { text: 'A fluid particle moving at velocity U along a pipe that deflects by y(x,t) has lateral acceleration given by the material derivative applied twice. It contains local, Coriolis and centrifugal parts.', tex: '\\left(\\frac{\\partial}{\\partial t} + U\\frac{\\partial}{\\partial x}\\right)^2 y = \\frac{\\partial^2 y}{\\partial t^2} + 2U\\frac{\\partial^2 y}{\\partial x\\,\\partial t} + U^2\\frac{\\partial^2 y}{\\partial x^2}' },
    { text: 'Adding the fluid inertia force to the beam equation of the pipe gives the equation of motion.', tex: 'EI\\,y\'\'\'\' + (m_f U^2 - N_e)\\,y\'\' + 2 m_f U\\,\\dot y\' + (m_p + m_f)\\,\\ddot y = 0' },
    { text: 'For static buckling in the first mode sin(πx/L) the bending and tension restoring forces balance the centrifugal force, which fixes the critical velocity.', tex: 'U_c = \\sqrt{\\frac{EI(\\pi/L)^2 + N_e}{m_f}}\\ \\xrightarrow{N_e = 0}\\ \\frac{\\pi}{L}\\sqrt{\\frac{EI}{m_f}}' },
    { text: a.one_mode ? 'Projecting on the first mode alone, the Coriolis term integrates to zero and the frequency falls with velocity along an ellipse.' : 'With two modes the antisymmetric Coriolis matrix couples them; the determinant of the resulting gyroscopic system gives a quadratic in ω².', tex: a.one_mode ? '\\omega_1 = \\omega_0\\sqrt{1 - (U/U_c)^2}' : '(k_1 - m\\omega^2)(k_2 - m\\omega^2) = \\omega^2 g_c^2,\\qquad g_c = \\frac{16\\,m_f U}{3L}' },
  ],
  solve(v, a) {
    const P = pipeProps(v, a), L = v.L, warnings = [];
    if (P.thin) warnings.push('Wall thickness exceeds 45 % of the diameter and has been limited to that value.');
    const f = (U, one) => { const w = pipeOmega2(P, L, U, one).w1; return w > 0 ? Math.sqrt(w) / (2 * Math.PI) : 0; };
    const w = pipeOmega2(P, L, v.U, a.one_mode), w1 = w.w1 > 0 ? Math.sqrt(w.w1) : 0, f0 = f(0, true);
    const buckled = !(w.w1 > 0);
    if (buckled) warnings.push(P.Uc === 0 ? 'The pressure-induced compression alone exceeds the Euler load: the span buckles even without flow.' : 'The flow velocity is at or above the critical value: the pipe has lost stiffness and buckles (divergence).');
    const Umax = P.Uc > 0 ? 1.2 * P.Uc : Math.max(v.U, 1), Us = N.linspace(0, Umax, 121);
    const Ls = N.linspace(0.3 * L, 3 * L, 60), ucL = Ls.map(l => { const q = (P.EI * (Math.PI / l) ** 2 + P.Ne) / P.mf; return q > 0 ? Math.sqrt(q) : 0; });
    const k1 = P.EI * (Math.PI / L) ** 4 + (P.Ne - P.mf * v.U ** 2) * (Math.PI / L) ** 2;
    return {
      scalars: [
        scalar('EI', 'Bending stiffness', P.EI, 'N m^2'), scalar('m_p', 'Pipe mass per unit length', P.mp, 'kg/m'), scalar('m_f', 'Fluid mass per unit length', P.mf, 'kg/m'), scalar('m_t', 'Total vibrating mass per unit length', P.m, 'kg/m'),
        scalar('beta', 'Mass ratio m_f/m', P.mf / P.m, '1'), scalar('N_e', 'Effective axial tension', P.Ne, 'N', { show: 'kN' }),
        scalar('U_c', 'Critical flow velocity (divergence)', P.Uc, 'm/s', { text: P.Uc === 0 ? 'Zero — buckled by pressure without flow' : undefined }),
        scalar('u_star', 'Dimensionless velocity U·L·√(m_f/EI)', v.U * L * Math.sqrt(P.mf / P.EI), '1', { note: 'divergence at π with no axial force' }),
        scalar('U_ratio', 'Flow velocity over critical velocity', P.Uc > 0 ? v.U / P.Uc : 0, '1', { text: P.Uc > 0 ? undefined : 'Not defined' }),
        scalar('f_0', 'First natural frequency at zero flow', f0, '1/s', { show: 'Hz' }),
        scalar('omega_1', 'First natural angular frequency at this velocity', w1, '1/s', { text: buckled ? 'Zero — the pipe has diverged' : undefined }),
        scalar('f_1', 'First natural frequency at this velocity', w1 / (2 * Math.PI), '1/s', { show: 'Hz', text: buckled ? 'Zero — the pipe has diverged' : undefined }),
        scalar('df', 'Frequency reduction due to flow', f0 > 0 ? 1 - w1 / (2 * Math.PI) / f0 : 0, '1', { show: '%' }),
        scalar('P_c', 'Equivalent centrifugal compression m_f·U²', P.mf * v.U ** 2, 'N', { show: 'kN' }),
      ],
      series: [
        line('freq-sweep', 'First natural frequency against flow velocity', 'Flow velocity', 'm/s', Us, [{ label: 'One-mode approximation', data: Us.map(u => f(u, true)), dash: !a.one_mode }, { label: 'Two-mode model with Coriolis coupling', data: Us.map(u => f(u, false)), dash: a.one_mode }], 'Frequency', 'Hz', { points: [{ x: v.U, y: w1 / (2 * Math.PI) }], pointsLabel: 'Operating point' }),
        line('uc-span', 'Critical velocity against span', 'Span', 'm', Ls, [{ label: 'Critical velocity', data: ucL }, { label: 'Flow velocity', data: Ls.map(() => v.U), dash: true }], 'Velocity', 'm/s'),
      ],
      checks: [check('One-mode frequency consistent with the modal stiffness', a.one_mode && !buckled ? (w1 * w1 * P.m - k1) / Math.abs(k1) : 0, 1e-9, 'm·ω² against k₁')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const P = pipeProps({ ...v, T_0: 0 }, { ...a, no_pressure: true }), L = v.L, out = [];
    const eb = (Math.PI / L) ** 2 * Math.sqrt(P.EI / P.m), Uc = Math.PI / L * Math.sqrt(P.EI / P.mf);
    out.push(bench('Zero-flow frequency vs Euler–Bernoulli beam', Math.sqrt(pipeOmega2(P, L, 0, true).w1), eb, 'ω₁ = (π/L)²√(EI/m)', 1e-12));
    out.push(bench('Two-mode model at zero flow', Math.sqrt(pipeOmega2(P, L, 0, false).w1), eb, 'Coriolis coupling vanishes at U = 0', 1e-10));
    out.push(bench('Critical velocity U_c = (π/L)√(EI/m_f)', P.Uc, Uc, 'Païdoussis (2014), pinned–pinned pipe', 1e-12));
    out.push(bench('One-mode frequency at half the critical velocity', Math.sqrt(pipeOmega2(P, L, 0.5 * Uc, true).w1) / eb, Math.sqrt(0.75), 'ω/ω₀ = √(1 − (U/U_c)²)', 1e-10));
    out.push(bench('Two-mode model diverges at the same critical velocity', Math.sqrt(Math.abs(pipeOmega2(P, L, Uc, false).w1)) / eb, 0, 'Divergence is a static instability unaffected by Coriolis forces', 1e-5));
    return out;
  },
  validation: [],
  diagram(v) {
    const pts = Array.from({ length: 41 }, (_, i) => [80 + i * 12, 170 + 34 * Math.sin(i / 40 * Math.PI)]);
    return svg(`
      ${S.path('M60 216 l20 -40 l20 40 z', 'd-body')} ${S.path('M540 216 l20 -40 l20 40 z', 'd-body')} ${S.path('M40 216 L120 216 M520 216 L600 216', 'd-ground')}
      ${S.line(80, 170, 560, 170, 'd-dim')} ${S.poly(pts, 'd-pipe')}
      ${S.arrow(30, 170, 76, 170)} ${S.text(40, 158, `U = ${lab(v.U, 'm/s')}`, 'd-text', 'start')} ${S.arrow(566, 170, 612, 170)}
      ${S.arrow(320, 232, 320, 262, 'd-arrow d-hazard')} ${S.text(320, 280, 'centrifugal force m_f·U²·y″')}
      ${S.arrow(200, 150, 200, 122)} ${S.arrow(440, 122, 440, 150)} ${S.text(320, 116, 'Coriolis force 2·m_f·U·∂²y/∂x∂t')}
      ${S.dim(80, 320, 560, 320, `L = ${lab(v.L, 'm')}`)}
      ${S.text(320, 40, `D_o = ${lab(v.D_o * 1e3, 'mm')}   t = ${lab(v.t_w * 1e3, 'mm')}   ρ_f = ${lab(v.rho_f, 'kg/m³')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the fall of the first natural frequency of a supported flexible tube with increasing internal flow and extrapolate to the divergence velocity.',
    apparatus: ['Flexible elastomer or thin-walled metal tube between two pinned supports that allow axial sliding at one end', 'Pump with smooth flow control and a flow conditioner', 'Impulse hammer or small shaker'],
    instruments: [{ name: 'Electromagnetic or Coriolis flow meter', measures: 'Mean flow velocity', range: '0–30 m/s', resolution: '±0.5 %' }, { name: 'Laser displacement sensor or light accelerometer at mid-span', measures: 'Free-vibration response', range: '±10 mm', resolution: '1 kHz' }, { name: 'Pressure transducer', measures: 'Internal pressure at the test section', range: '0–10 bar', resolution: '±0.25 %' }],
    procedure: ['Measure the natural frequency with the tube full of still fluid.', 'Raise the flow in steps; at each step tap the tube and extract the first natural frequency from the decay record.', 'Plot frequency squared against velocity squared; the straight line meets zero at U_c².'],
    controls: ['Check that pump pulsation frequency is far from the natural frequency', 'Repeat with the sliding end clamped to show the pressure effect'],
    signatures: ['ω² falling linearly with U²', 'Static bowing of the tube as U approaches U_c', 'Mid-span and quarter-span motion out of phase at high flow (Coriolis coupling)'],
    safety: ['Shield against whip of a buckled pressurised tube', 'Pressure relief on the pump discharge'],
  },
  falsify: ['Measured ω² that is not linear in U² for a pinned–pinned tube at low velocity.', 'Divergence at a velocity differing from (π/L)√(EI/m_f) by more than the uncertainty in EI and end conditions.'],
  alternatives: [{ name: 'Cantilevered pipe', text: 'With a free downstream end the system is non-conservative and loses stability by flutter rather than divergence.' }, { name: 'Timoshenko-beam and shell models', text: 'Needed for short or thin-walled pipes where shear deformation or shell modes matter.' }, { name: 'Two-phase or pulsating flow', text: 'Slugs and pulsations excite the span parametrically below the steady critical velocity.' }],
  hazards: [{ hazard: 'Buckling or large static deflection of a span', cause: 'High velocity combined with pressure and thermal compression', mitigation: 'Shorter spans, guides and axial restraint review' }, { hazard: 'Resonance', cause: 'Natural frequency lowered into the range of pump or slug excitation', mitigation: 'Check frequency separation at the highest operating velocity' }],
  standards: ['ASME B31.3 (process piping)', 'Energy Institute guidelines for the avoidance of vibration-induced fatigue failure in process pipework', 'DNV-RP-F105 (free spanning pipelines)'],
  limits: 'Straight, uniform, slender pipe with pinned ends and steady plug flow of a single-phase fluid. No gravity sag, damping, or support flexibility. For ordinary steel pipework the critical velocity is far above practical flow speeds; the theory matters for flexible hoses, thin tubes and very long spans.',
  numerics: { method: 'Closed-form one-mode solution; closed-form roots of the two-mode gyroscopic determinant' },
  optimise: { objective: 'U_c', sense: 'max', vars: ['L'], note: 'Critical velocity is inversely proportional to span when there is no axial force.' },
  inverse: { series: 'freq-sweep', fit: ['E'] },
  extensions: ['Other end conditions (clamped, cantilevered with flutter)', 'Gravity and initial sag', 'Unsteady and two-phase internal flow'],
};

// ------------------------------------------------------------------ on-bottom stability of a subsea pipeline
function obsRun(v, a, tc, full = false) {
  const om = 2 * Math.PI / v.T, k = waveNumber(om, v.d), sh = Math.sinh(k * v.d);
  const uw = Math.PI * v.H / (v.T * sh), aw = om * uw, D = v.D_s + 2 * tc, Di = v.D_s - 2 * v.t_s;
  const Ue = a.uniform_current ? v.U_c : 7 / 8 * v.U_c * Math.pow(D / v.z_r, 1 / 7);
  const As = Math.PI * (v.D_s ** 2 - Di ** 2) / 4, Ai = Math.PI * Di * Di / 4, Ac = Math.PI * (D * D - v.D_s ** 2) / 4, Ad = Math.PI * D * D / 4;
  const ws = g * (v.rho_s * As + v.rho_i * Ai + v.rho_c * Ac - v.rho * Ad);
  const FR = a.coulomb ? 0 : v.F_R, n = 360, cd = 0.5 * v.rho * D * v.C_D, ci = v.rho * Ad * v.C_M * aw, cl = a.lift ? 0.5 * v.rho * D * v.C_L : 0;
  const th = [], FD = [], FI = [], FL = [];
  let dem = 0, iCrit = 0, FDm = 0, FIm = 0, FLm = 0;
  for (let i = 0; i <= n; i++) {
    const t = 2 * Math.PI * i / n, u = uw * Math.cos(t) + Ue, fd = cd * Math.abs(u) * u, fi = -ci * Math.sin(t), fl = cl * u * u;
    if (full) { th.push(t); FD.push(fd); FI.push(fi); FL.push(fl); }
    if (Math.abs(fd) > FDm) FDm = Math.abs(fd);
    if (Math.abs(fi) > FIm) FIm = Math.abs(fi);
    if (fl > FLm) FLm = fl;
    const q = Math.abs(fd + fi) / v.mu_s + fl;
    if (q > dem) { dem = q; iCrit = i; }
  }
  if (!a.in_phase) dem = (FDm + FIm) / v.mu_s + FLm;
  const wReq = Math.max(v.gamma_sc * dem - FR / v.mu_s, 0), SF = dem > 0 ? (ws + FR / v.mu_s) / dem : Infinity;
  return { k, uw, aw, D, Ue, ws, th, FD, FI, FL, FDm, FIm, FLm, dem, iCrit, thCrit: 2 * Math.PI * iCrit / n, wReq, SF, FR, Ad };
}
const onBottom = {
  id: 'on-bottom-stability',
  title: 'On-bottom stability of a subsea pipeline',
  module: 2, klass: 'I', domains: ['offshore', 'pipeline'],
  keywords: ['on-bottom stability', 'on bottom stability', 'pipeline stability', 'lateral stability', 'concrete coating', 'concrete weight coating', 'submerged weight', 'required weight', 'subsea pipeline', 'seabed pipeline', 'dnv-rp-f109', 'f109', 'hydrodynamic lift', 'pipe on seabed'],
  summary: 'Simplified absolute lateral static stability of a pipeline resting on the seabed under combined wave and current: near-bed kinematics, drag, inertia and lift, required submerged weight, safety factor and concrete coating thickness.',
  background: [
    'A pipeline laid on the seabed is exposed to the oscillatory flow of waves and to steady current. The flow produces an in-line force with drag and inertia parts and, because the pipe sits against a boundary, a lift force that reduces the contact force and with it the friction available to resist sliding.',
    'In an absolute static stability check the pipe must not move at all under the design sea state: at every instant of the wave cycle the horizontal load must not exceed the soil resistance, and the lift must not exceed the submerged weight. Weight is normally added with a concrete coating, which also increases the diameter and so the loads; the required thickness therefore comes from an iteration.',
  ],
  phenomena: ['Near-bed wave orbital velocity', 'Drag, inertia and lift on a cylinder at a wall', 'Coulomb friction', 'Seabed boundary-layer reduction of current'],
  laws: ['momentum', 'newton2', 'archimedes'],
  refs: ['DNV-RP-F109. On-bottom stability design of submarine pipelines. DNV, Høvik.', 'Sumer, B. M. & Fredsøe, J. (1997). Hydrodynamics Around Cylindrical Structures. World Scientific.', 'Morison, J. R., O\'Brien, M. P., Johnson, J. W. & Schaaf, S. A. (1950). The force exerted by surface waves on piles. Petroleum Transactions, AIME 189, 149–154.', 'Bai, Y. & Bai, Q. (2005). Subsea Pipelines and Risers. Elsevier.', 'Dean, R. G. & Dalrymple, R. A. (1991). Water Wave Mechanics for Engineers and Scientists. World Scientific.'],
  inputs: [
    inp('D_s', 'Steel outer diameter', 'mm', 323.9, { min: 100, max: 1500, kind: 'geometry', aliases: ['outer diameter', 'steel diameter', 'diameter'] }),
    inp('t_s', 'Steel wall thickness', 'mm', 12.7, { min: 5, max: 40, kind: 'geometry', aliases: ['wall thickness', 'wall'] }),
    inp('t_c', 'Concrete coating thickness', 'mm', 40, { min: 0, max: 200, kind: 'geometry', aliases: ['concrete thickness', 'coating thickness', 'concrete coating'] }),
    inp('rho_c', 'Concrete density', 'kg/m^3', 3040, { min: 1800, max: 3600, kind: 'geometry', aliases: ['concrete density'], src: 'Typical high-density (iron-ore aggregate) weight coating' }),
    inp('rho_s', 'Steel density', 'kg/m^3', 7850, { min: 7000, max: 8200, kind: 'geometry', aliases: ['steel density'] }),
    inp('rho_i', 'Density of pipe contents', 'kg/m^3', 100, { min: 0, max: 1100, kind: 'fluid', aliases: ['contents density', 'product density'] }),
    inp('rho', 'Sea-water density', 'kg/m^3', 1025, { min: 990, max: 1040, kind: 'fluid', aliases: ['water density'] }),
    inp('H', 'Design wave height', 'm', 6, { min: 0.1, max: 25, kind: 'environment', env: 'wave_height', aliases: ['wave height', 'significant wave height', 'hs'] }),
    inp('T', 'Wave period', 's', 10, { min: 3, max: 25, kind: 'environment', env: 'wave_period', aliases: ['wave period', 'period', 'tp'] }),
    inp('d', 'Water depth', 'm', 40, { min: 5, max: 2000, kind: 'environment', env: 'water_depth', aliases: ['water depth', 'depth', 'deep'] }),
    inp('U_c', 'Current speed perpendicular to the pipe', 'm/s', 0.5, { min: 0, max: 3, kind: 'environment', env: 'current_speed', aliases: ['current', 'current speed'] }),
    inp('z_r', 'Reference height of the current measurement', 'm', 1, { min: 0.5, max: 10, kind: 'environment', aliases: ['reference height'] }),
    inp('mu_s', 'Pipe–soil friction coefficient', '1', 0.6, { min: 0.1, max: 1.5, kind: 'environment', aliases: ['friction coefficient', 'soil friction'], src: 'Commonly adopted for concrete-coated pipe on sand; clay is lower' }),
    inp('C_D', 'Drag coefficient', '1', 0.7, { min: 0, max: 2, kind: 'fluid', aliases: ['drag coefficient', 'cd'], src: 'Traditional value for a pipe on the seabed in steady and oscillatory flow' }),
    inp('C_M', 'Inertia coefficient', '1', 3.29, { min: 0, max: 4.5, kind: 'fluid', aliases: ['inertia coefficient', 'cm'], src: 'Potential-flow value for a cylinder touching a plane wall' }),
    inp('C_L', 'Lift coefficient', '1', 0.9, { min: 0, max: 2, kind: 'fluid', aliases: ['lift coefficient', 'cl'], src: 'Traditional value for a pipe on the seabed' }),
    inp('gamma_sc', 'Safety factor on hydrodynamic load', '1', 1.1, { min: 1, max: 2, aliases: ['safety factor', 'safety class factor'] }),
    inp('F_R', 'Passive soil resistance per unit length', 'N/m', 300, { min: 0, max: 5000, kind: 'environment', aliases: ['passive resistance', 'soil resistance'] }),
  ],
  assumptions: [
    asm('in_phase', 'Drag, inertia and lift are combined in their true phase and the most onerous instant of the wave cycle governs.', { why: 'Force balance at each instant', alt: 'Peak drag, peak inertia and peak lift are assumed to act simultaneously (conservative).' }),
    asm('lift', 'Hydrodynamic lift reduces the normal force on the seabed.', { why: 'A pipe at a wall experiences lift', alt: 'Lift is neglected (non-conservative; for comparison only).' }),
    asm('uniform_current', 'The stated current acts over the whole pipe diameter.', { why: 'Current given at pipe level', alt: 'A one-seventh power-law boundary layer is averaged over the pipe diameter from the stated reference height.' }),
    asm('coulomb', 'Soil resistance is pure Coulomb friction on the contact force.', { why: 'No embedment relied upon', alt: 'The stated passive resistance from partial embedment is added to the friction.' }),
  ],
  symbols: { omega: ['Wave angular frequency', '1/s'], k: ['Wave number', '1/m'], u_w: ['Near-bed orbital velocity amplitude', 'm/s'], a_w: ['Near-bed orbital acceleration amplitude', 'm/s^2'], D_h: ['Hydrodynamic outer diameter', 'm'], U_e: ['Effective current over the pipe', 'm/s'], theta: ['Wave phase', 'rad'], F_D: ['Drag force per unit length', 'N/m'], F_I: ['Inertia force per unit length', 'N/m'], F_L: ['Lift force per unit length', 'N/m'], w_s: ['Submerged weight per unit length', 'N/m'], w_req: ['Required submerged weight per unit length', 'N/m'], A_s: ['Steel cross-section', 'm^2'], A_i: ['Bore area', 'm^2'], A_c: ['Concrete cross-section', 'm^2'], SF: ['Factor of safety against sliding', '1'], F_Dm: ['Peak drag force per unit length', 'N/m'], F_Im: ['Peak inertia force per unit length', 'N/m'], F_Lm: ['Peak lift force per unit length', 'N/m'] },
  equations: a => {
    const lift = a.lift ? ' + F_L' : '', fr = a.coulomb ? '' : ' - F_R/mu_s', liftm = a.lift ? ' + F_Lm' : '';
    return [
      eq('om', 'Angular frequency', 'omega', '2*pi/T', { kind: 'definition' }),
      eq('disp', 'Dispersion relation', 'omega^2', 'g*k*tanh(k*d)', { kind: 'law', origin: 'Linear wave theory' }),
      eq('uw', 'Near-bed orbital velocity', 'u_w', 'pi*H/(T*sinh(k*d))', { kind: 'derived', origin: 'Airy theory evaluated at the seabed' }),
      eq('aw', 'Near-bed orbital acceleration', 'a_w', 'omega*u_w', { kind: 'derived', origin: 'Harmonic motion' }),
      eq('dh', 'Hydrodynamic diameter', 'D_h', 'D_s + 2*t_c', { kind: 'definition' }),
      a.uniform_current ? eq('ue', 'Effective current', 'U_e', 'U_c', { kind: 'closure', needs: ['uniform_current'] }) : eq('ue', 'Boundary-layer averaged current', 'U_e', '7/8*U_c*(D_h/z_r)^(1/7)', { kind: 'empirical', origin: 'Mean of a one-seventh power-law profile over the pipe diameter' }),
      eq('fd', 'Drag force', 'F_D', '0.5*rho*D_h*C_D*abs(u_w*cos(theta) + U_e)*(u_w*cos(theta) + U_e)', { kind: 'empirical', origin: 'Morison drag term' }),
      eq('fi', 'Inertia force', 'F_I', '-pi*rho*D_h^2/4*C_M*a_w*sin(theta)', { kind: 'empirical', origin: 'Morison inertia term' }),
      ...(a.lift ? [eq('fl', 'Lift force', 'F_L', '0.5*rho*D_h*C_L*(u_w*cos(theta) + U_e)^2', { kind: 'empirical', origin: 'Lift on a cylinder at a plane boundary', needs: ['lift'] })] : []),
      eq('ws', 'Submerged weight', 'w_s', 'g*(rho_s*A_s + rho_i*A_i + rho_c*A_c - rho*pi*D_h^2/4)', { kind: 'law', origin: 'Weight less buoyancy (Archimedes)' }),
      a.in_phase
        ? eq('req', 'Required submerged weight', 'w_req', a.coulomb ? `gamma_sc*(abs(F_D + F_I)/mu_s${lift})` : `max(gamma_sc*(abs(F_D + F_I)/mu_s${lift})${fr}, 0)`, { kind: 'law', origin: 'Horizontal and vertical equilibrium with Coulomb friction at the governing phase', needs: ['in_phase'] })
        : eq('req', 'Required submerged weight', 'w_req', a.coulomb ? `gamma_sc*((F_Dm + F_Im)/mu_s${liftm})` : `max(gamma_sc*((F_Dm + F_Im)/mu_s${liftm})${fr}, 0)`, { kind: 'law', origin: 'Equilibrium with peak loads taken as simultaneous' }),
      eq('sf', 'Factor of safety against sliding', 'SF', `(mu_s*w_s${a.coulomb ? '' : ' + F_R'})/(${a.in_phase ? 'abs(F_D + F_I)' : 'F_Dm + F_Im'}${a.lift ? (a.in_phase ? ' + mu_s*F_L' : ' + mu_s*F_Lm') : ''})`, { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'Linear wave theory gives the horizontal orbital velocity at the seabed; its amplitude falls rapidly once the depth exceeds about half a wavelength.', tex: 'u_w = \\frac{\\pi H}{T\\,\\sinh kd},\\qquad a_w = \\omega\\,u_w' },
    { text: 'With wave and current perpendicular to the pipe the instantaneous velocity is U = u_w cos θ + U_e. The in-line force has drag and inertia parts and the wall-induced lift acts upward.', tex: 'F_D = \\tfrac12\\rho D C_D |U| U,\\quad F_I = -\\rho\\frac{\\pi D^2}{4} C_M a_w \\sin\\theta,\\quad F_L = \\tfrac12\\rho D C_L U^2' },
    { text: 'The pipe does not slide if the horizontal load, with a safety factor, stays below the friction on the reduced contact force' + (a.coulomb ? '.' : ' plus passive resistance.'), tex: '\\gamma_{SC}\\left(|F_D + F_I| + \\mu F_L\\right) \\le \\mu\\,w_s' + (a.coulomb ? '' : ' + F_R') },
    { text: 'Solving for the submerged weight and taking the worst phase gives the requirement. Since concrete adds both weight and diameter, the necessary thickness is found by root-finding.', tex: 'w_{req} = \\gamma_{SC}\\max_\\theta\\left[\\frac{|F_D + F_I|}{\\mu} + F_L\\right]' + (a.coulomb ? '' : ' - \\frac{F_R}{\\mu}') },
  ],
  solve(v, a) {
    const r = obsRun(v, a, v.t_c, true), warnings = [];
    if (r.ws <= 0) warnings.push('The pipe is buoyant: its submerged weight is not positive.');
    if (v.H > 0.78 * v.d) warnings.push('The wave height exceeds the depth-limited breaking height (about 0.78·d); linear kinematics are not valid.');
    const margin = t => { const q = obsRun(v, a, t); return q.ws - q.wReq; };
    let tReq = 0, tTxt;
    if (margin(0) < 0) { if (margin(0.6) < 0) { tReq = NaN; tTxt = 'Not achievable with up to 600 mm of this concrete'; } else tReq = N.bisect(margin, 0, 0.6, 1e-7); }
    const SFv = r.FLm > 0 ? r.ws / (v.gamma_sc * r.FLm) : NaN;
    const stable = r.ws >= r.wReq && (!(r.FLm > 0) || SFv >= 1);
    if (!stable) warnings.push('The pipe does not meet the absolute stability criterion with the stated coating: it is predicted to move in the design sea state.');
    const tcs = N.linspace(0, 0.2, 41), sfs = tcs.map(t => { const q = obsRun(v, a, t); return Number.isFinite(q.SF) ? q.SF : 0; });
    const deg = r.th.map(x => x / DEG), KC = r.uw * v.T / r.D;
    return {
      scalars: [
        scalar('k', 'Wave number', r.k, '1/m'), scalar('u_w', 'Near-bed orbital velocity amplitude', r.uw, 'm/s'), scalar('a_w', 'Near-bed orbital acceleration amplitude', r.aw, 'm/s^2'),
        scalar('U_e', 'Effective current over the pipe', r.Ue, 'm/s'), scalar('KC', 'Keulegan–Carpenter number', KC, '1'), scalar('D_h', 'Hydrodynamic outer diameter', r.D, 'm', { show: 'mm' }),
        scalar('F_Dm', 'Peak drag force per unit length', r.FDm, 'N/m'), scalar('F_Im', 'Peak inertia force per unit length', r.FIm, 'N/m'), scalar('F_Lm', 'Peak lift force per unit length', r.FLm, 'N/m'),
        scalar('theta_c', 'Governing wave phase', r.thCrit, 'rad', { show: 'deg' }),
        scalar('w_s', 'Submerged weight per unit length', r.ws, 'N/m'), scalar('SG', 'Specific gravity of the coated pipe', 1 + r.ws / (v.rho * g * r.Ad), '1'),
        scalar('w_req', 'Required submerged weight per unit length', r.wReq, 'N/m'),
        scalar('SF', 'Factor of safety against sliding (no load factor)', Number.isFinite(r.SF) ? r.SF : NaN, '1', { text: Number.isFinite(r.SF) ? undefined : 'Unlimited — no hydrodynamic load' }),
        scalar('SF_v', 'Factored weight over peak lift', SFv, '1', { text: Number.isFinite(SFv) ? undefined : 'Not applicable — no lift' }),
        scalar('util', 'Utilisation w_req/w_s', r.ws > 0 ? r.wReq / r.ws : NaN, '1', { text: r.ws > 0 ? undefined : 'Pipe is buoyant' }),
        scalar('t_req', 'Concrete thickness required for stability', tReq, 'm', { show: 'mm', text: tTxt }),
      ],
      series: [
        line('forces-phase', 'Loads and resistance through the wave cycle', 'Wave phase', 'deg', deg, [{ label: 'Horizontal load', data: r.FD.map((q, i) => q + r.FI[i]) }, { label: 'Drag', data: r.FD, dash: true }, { label: 'Inertia', data: r.FI, dash: true }, { label: 'Lift', data: r.FL, dash: true }, { label: 'Available resistance', data: r.FL.map(q => Math.max(v.mu_s * (r.ws - q), 0) + r.FR) }], 'Force per unit length', 'N/m'),
        line('sf-concrete', 'Safety factor against concrete thickness', 'Concrete thickness', 'mm', tcs.map(t => t * 1e3), [{ label: 'Factor of safety against sliding', data: sfs }, { label: 'Required (load factor)', data: tcs.map(() => v.gamma_sc), dash: true }], 'Factor of safety', '–'),
      ],
      checks: [check('Dispersion relation residual', (4 * Math.PI ** 2 / v.T ** 2 - g * r.k * Math.tanh(r.k * v.d)) * v.T ** 2 / (4 * Math.PI ** 2), 1e-9, 'ω² against g·k·tanh(k·d)')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], Ts = 200, ds = 5, ks = waveNumber(2 * Math.PI / Ts, ds);
    out.push(bench('Shallow-water seabed velocity u = (H/2)√(g/d)', Math.PI * 1 / (Ts * Math.sinh(ks * ds)), 0.5 * Math.sqrt(g / ds), 'Long-wave limit of Airy theory', 1e-3));
    const b0 = { ...a, in_phase: true, lift: true, uniform_current: true, coulomb: true };
    const rd = obsRun({ ...v, U_c: 0, C_M: 0, C_L: 0 }, b0, v.t_c);
    out.push(bench('Drag-only required weight', rd.wReq, v.gamma_sc * 0.5 * v.rho * rd.D * v.C_D * rd.uw ** 2 / v.mu_s, 'γ·½ρ·D·C_D·u_w²/μ', 1e-12));
    const ri = obsRun({ ...v, U_c: 0, C_D: 0, C_L: 0 }, b0, v.t_c);
    out.push(bench('Inertia-only required weight', ri.wReq, v.gamma_sc * v.rho * Math.PI * ri.D ** 2 / 4 * v.C_M * ri.aw / v.mu_s, 'γ·ρ·(πD²/4)·C_M·a_w/μ', 1e-12));
    const rc = obsRun({ ...v, C_M: 0, C_L: 0 }, b0, v.t_c);
    out.push(bench('Drag-only required weight with a following current', rc.wReq, v.gamma_sc * 0.5 * v.rho * rc.D * v.C_D * (rc.uw + v.U_c) ** 2 / v.mu_s, 'γ·½ρ·D·C_D·(u_w + U_c)²/μ under the crest', 1e-12));
    const rl = obsRun({ ...v, C_D: 0, C_M: 0 }, b0, v.t_c);
    out.push(bench('Lift-only required weight', rl.wReq, v.gamma_sc * 0.5 * v.rho * rl.D * v.C_L * (rl.uw + v.U_c) ** 2, 'γ·½ρ·D·C_L·(u_w + U_c)²: weight must exceed the factored peak lift', 1e-12));
    const bl = { ...b0, uniform_current: false }, re = obsRun({ ...v, z_r: v.D_s + 2 * v.t_c }, bl, v.t_c);
    out.push(bench('Power-law current averaged over a pipe as tall as the reference height', re.Ue, 7 / 8 * v.U_c, 'Mean of (z/z_r)^(1/7) over 0 ≤ z ≤ z_r is 7/8', 1e-12));
    out.push(bench('Potential-flow inertia coefficient of a cylinder on a wall', 3.29, Math.PI ** 2 / 3, 'C_M = π²/3 (added mass π²/3 − 1 plus Froude–Krylov)', 1e-3));
    return out;
  },
  validation: [],
  diagram(v) {
    return svg(`
      ${S.rect(30, 40, 580, 230, 'd-liquid', 0)} ${S.path('M30 40 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q20 -10 40 0 q20 10 40 0 q10 -5 20 -5', 'd-liquid-line')}
      ${S.path('M30 270 L610 270', 'd-ground')}
      ${S.circle(320, 226, 44, 'd-body')} ${S.circle(320, 226, 32, 'd-pipe-fill')} ${S.text(320, 230, 'pipe')}
      ${[0, 1, 2].map(i => S.arrow(90, 190 + i * 30, 190 - i * 16, 190 + i * 30)).join('')} ${S.text(130, 174, 'wave + current')}
      ${S.arrow(370, 226, 450, 226, 'd-arrow d-hazard')} ${S.text(456, 220, 'F_D + F_I', 'd-text', 'start')}
      ${S.arrow(320, 180, 320, 120, 'd-arrow d-hazard')} ${S.text(330, 130, 'F_L', 'd-text', 'start')}
      ${S.arrow(320, 290, 320, 330)} ${S.text(330, 322, 'w_s', 'd-text', 'start')}
      ${S.arrow(300, 282, 230, 282)} ${S.text(222, 300, 'friction μ(w_s − F_L)', 'd-text', 'end')}
      ${S.dim(570, 44, 570, 270, '')} ${S.text(562, 160, `d = ${lab(v.d, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(470, 80, `H = ${lab(v.H, 'm')}, T = ${lab(v.T, 's')}`)} ${S.text(470, 100, `concrete ${lab(v.t_c * 1e3, 'mm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the in-line and lift forces on a pipe section resting on a bed under combined oscillatory flow and current, and the load at which it begins to slide.',
    apparatus: ['Oscillating-water tunnel or wave flume with current recirculation', 'Pipe section on a sand bed or roughened plate, either fixed on a force balance or free to slide on low-friction guides', 'Bed preparation tools to control initial embedment'],
    instruments: [{ name: 'Two-component force transducers', measures: 'In-line and lift force per unit length', range: '0–500 N/m', resolution: '±1 %' }, { name: 'Laser or acoustic Doppler velocimeter', measures: 'Near-bed velocity at pipe mid-height', range: '±3 m/s', resolution: '±1 %' }, { name: 'Displacement transducer', measures: 'Lateral pipe movement', range: '0–1 m', resolution: '±0.5 mm' }],
    procedure: ['Measure the pipe–bed friction coefficient by a slow pull test in still water.', 'With the pipe fixed, record forces over a matrix of Keulegan–Carpenter number and current ratio.', 'With the pipe free, increase the oscillatory velocity until sliding starts and compare the threshold with the prediction.'],
    controls: ['Pull test repeated after each run to detect bed changes', 'Runs with the pipe lifted clear of the bed to isolate the wall effect on lift'],
    signatures: ['Onset of sliding at the phase where horizontal load over friction is greatest, not necessarily at peak velocity', 'Lift proportional to velocity squared near the wall'],
    safety: ['Guard moving pistons and carriage', 'Electrical isolation in wet areas'],
  },
  falsify: ['Sliding observed at a horizontal load clearly below μ·(w_s − F_L) on a flat bed without embedment.', 'Near-bed velocities for small-steepness waves that differ from πH/(T·sinh kd) beyond measurement error.'],
  alternatives: [{ name: 'Generalised lateral stability', text: 'Allows limited displacement in a design storm, based on dynamic simulation with pipe–soil interaction.' }, { name: 'Peak load coefficients', text: 'Recommended practice gives peak horizontal and vertical load coefficients as functions of Keulegan–Carpenter number and current ratio in place of constant Morison coefficients.' }, { name: 'Spectral near-bed velocity', text: 'Uses the significant near-bed velocity and zero-up-crossing period from a wave spectrum rather than a single regular wave.' }],
  hazards: [{ hazard: 'Lateral movement or flotation of the pipeline', cause: 'Insufficient submerged weight in a storm, especially when empty or gas-filled', mitigation: 'Concrete coating, trenching, rock cover or anchoring' }, { hazard: 'Coating damage', cause: 'Movement over a rough bed or excessive concrete thickness during laying', mitigation: 'Installation analysis and coating specification' }],
  standards: ['DNV-RP-F109 (on-bottom stability design of submarine pipelines)', 'DNV-ST-F101 (submarine pipeline systems)', 'ISO 13623 (pipeline transportation systems)'],
  limits: 'A screening calculation with constant Morison coefficients, a regular linear wave and flow perpendicular to the pipe on a flat bed. It does not reproduce the calibrated load coefficients, spectral wave treatment, soil models or safety-class format of any design code. Spreading, wave direction, embedment build-up, trenching and scour are not included.',
  numerics: { method: 'Newton iteration for the dispersion relation; scan of 360 phases per wave cycle; bisection for the required concrete thickness' },
  optimise: { objective: 't_req', sense: 'min', vars: ['rho_c'], note: 'Denser concrete adds weight with less increase of diameter and load.' },
  inverse: { series: 'forces-phase', fit: ['C_D', 'C_M'] },
  extensions: ['Peak load coefficients as functions of Keulegan–Carpenter number and current ratio', 'Wave spectrum transfer to the seabed with directional spreading', 'Pipe–soil interaction with embedment and passive resistance models'],
};

// ------------------------------------------------------------------ mudmat bearing capacity
const bearingFactors = phi => { const t = Math.tan(phi), Kp = Math.tan(Math.PI / 4 + phi / 2) ** 2, Nq = Math.exp(Math.PI * t) * Kp; return { Kp, Nq, Nc: t > 0 ? (Nq - 1) / t : Math.PI + 2, Ng: (Nq - 1) * Math.tan(1.4 * phi) }; };
function mudmatRun(v, a, scale = 1, Hload = v.H) {
  const B = Math.min(v.B, v.L) * scale, L = Math.max(v.B, v.L) * scale, A = B * L, Df = v.D_f, H = Hload;
  let qu, Hu, parts;
  if (a.undrained) {
    const Nc = Math.PI + 2, sa = a.shape ? 0.2 * B / L : 0, da = a.no_depth ? 0 : 0.4 * (Df <= B ? Df / B : Math.atan(Df / B));
    const ia = a.incl ? 0.5 - 0.5 * Math.sqrt(Math.max(0, 1 - H / (A * v.s_u))) : 0;
    qu = Nc * v.s_u * (1 + sa + da - ia) + v.gamma_sub * Df; Hu = v.alpha_s * v.s_u * A; parts = { Nc, sa, da, ia };
  } else {
    const f = bearingFactors(v.phi), sg = a.shape ? 1 + 0.1 * f.Kp * B / L : 1, dg = a.no_depth ? 1 : 1 + 0.1 * Math.sqrt(f.Kp) * Df / B;
    const th = Math.atan2(H, v.V), iq = a.incl ? (1 - th / (Math.PI / 2)) ** 2 : 1, ig = a.incl ? (th < v.phi ? (1 - th / v.phi) ** 2 : 0) : 1;
    qu = 0.5 * v.gamma_sub * B * f.Ng * sg * dg * ig + v.gamma_sub * Df * f.Nq * sg * dg * iq; Hu = v.alpha_s * v.V * Math.tan(v.phi); parts = { ...f, sg, dg, iq, ig };
  }
  const Qu = qu * A;
  return { B, L, A, qu, Qu, Hu, FSb: Qu / v.V, FSs: H > 0 ? Hu / H : Infinity, parts };
}
const mudmat = {
  id: 'mudmat-bearing-capacity',
  title: 'Bearing capacity and sliding of a subsea mudmat',
  module: 2, klass: 'I', domains: ['geotechnical', 'offshore'],
  keywords: ['mudmat', 'mud mat', 'bearing capacity', 'undrained shear strength', 'shallow foundation', 'sliding resistance', 'foundation', 'skirted foundation', 'footing', 'terzaghi', 'meyerhof', 'brinch hansen', 'clay', 'plem', 'manifold foundation', 'seabed bearing'],
  summary: 'Ultimate bearing capacity of a rectangular mudmat on clay (undrained, N_c = π + 2 with shape, depth and inclination factors) or on sand (drained, Meyerhof), sliding resistance, safety factors and required plan size.',
  background: [
    'A shallow foundation fails when the soil beneath it shears along a mechanism reaching the surface. For a strip on a weightless, purely cohesive soil the exact plasticity solution of Prandtl gives a bearing pressure of (π + 2) times the shear strength. Real foundations are corrected for plan shape, embedment and load inclination with semi-empirical factors.',
    'Subsea structures such as manifolds and pipeline end terminations are commonly set on steel mudmats on soft clay, where loading is fast compared with drainage and the undrained strength governs. Horizontal load both inclines the resultant, reducing vertical capacity, and must be resisted by shear on the base. On sand the drained capacity depends on the friction angle through the factors N_q and N_γ.',
  ],
  phenomena: ['Plastic shear failure of soil', 'Undrained (total-stress) response of clay', 'Load inclination and sliding', 'Frictional (drained) capacity of sand'],
  laws: ['newton2', 'newton3'],
  refs: ['Prandtl, L. (1921). Über die Eindringungsfestigkeit (Härte) plastischer Baustoffe und die Festigkeit von Schneiden. Zeitschrift für angewandte Mathematik und Mechanik 1, 15–20.', 'Skempton, A. W. (1951). The bearing capacity of clays. Proceedings of the Building Research Congress, London, 1, 180–189.', 'Brinch Hansen, J. (1970). A revised and extended formula for bearing capacity. Danish Geotechnical Institute Bulletin 28, 5–11.', 'Meyerhof, G. G. (1963). Some recent research on the bearing capacity of foundations. Canadian Geotechnical Journal 1, 16–26.', 'Randolph, M. & Gourvenec, S. (2011). Offshore Geotechnical Engineering. Spon Press.', 'API RP 2GEO. Geotechnical and foundation design considerations. American Petroleum Institute.'],
  inputs: [
    inp('B', 'Mudmat width', 'm', 6, { min: 1, max: 30, kind: 'geometry', aliases: ['width', 'breadth', 'wide'] }),
    inp('L', 'Mudmat length', 'm', 10, { min: 1, max: 50, kind: 'geometry', aliases: ['length', 'long'] }),
    inp('D_f', 'Embedment (skirt) depth', 'm', 0.5, { min: 0, max: 5, kind: 'geometry', aliases: ['embedment', 'skirt depth', 'skirt'] }),
    inp('s_u', 'Undrained shear strength', 'kPa', 10, { min: 1, max: 300, kind: 'environment', aliases: ['undrained shear strength', 'shear strength', 'su'], src: 'Soft marine clay' }),
    inp('gamma_sub', 'Submerged unit weight of soil', 'kN/m^3', 6, { min: 3, max: 12, kind: 'environment', aliases: ['submerged unit weight', 'unit weight'] }),
    inp('phi', 'Drained friction angle', 'deg', 30, { min: 20, max: 45, kind: 'environment', aliases: ['friction angle', 'angle of friction'] }),
    inp('alpha_s', 'Base interface roughness factor', '1', 0.6, { min: 0.1, max: 1, kind: 'geometry', aliases: ['roughness factor', 'adhesion factor', 'interface factor'], src: 'Ratio of mobilised base shear to soil strength; approaches 1 for a skirted or rough base' }),
    inp('V', 'Vertical load (submerged weight and operating loads)', 'kN', 1500, { min: 10, max: 100000, aliases: ['vertical load', 'weight', 'vertical'] }),
    inp('H', 'Horizontal load', 'kN', 150, { min: 0, max: 20000, aliases: ['horizontal load', 'lateral load', 'horizontal'] }),
    inp('FS_bt', 'Target safety factor on bearing', '1', 2.0, { min: 1, max: 4, aliases: ['bearing safety factor', 'target safety factor'], src: 'Value commonly required for shallow foundations under working-stress design' }),
    inp('FS_st', 'Target safety factor on sliding', '1', 1.5, { min: 1, max: 3, aliases: ['sliding safety factor'], src: 'Value commonly required for shallow foundations under working-stress design' }),
  ],
  assumptions: [
    asm('undrained', 'The soil is clay loaded undrained: capacity depends on the undrained shear strength.', { why: 'Rapid loading of soft clay', alt: 'The soil is cohesionless and drained: Meyerhof\'s capacity with N_q and N_γ from the friction angle is used.' }),
    asm('shape', 'A shape factor accounts for the finite length of the mat (Skempton and Brinch Hansen: 1 + 0.2·B/L undrained).', { why: 'Three-dimensional failure mechanism', alt: 'The mat is treated as an infinite strip (shape factor 1).' }),
    asm('incl', 'Horizontal load inclines the resultant and reduces vertical capacity through an inclination factor.', { why: 'Combined loading', alt: 'Vertical capacity is computed for vertical load only; sliding is checked separately.' }),
    asm('no_depth', 'Embedment contributes overburden only; no depth factor is applied.', { why: 'Conservative for shallow skirts in disturbed soil', alt: 'A depth factor is applied (Brinch Hansen undrained: 0.4·D/B; Meyerhof drained).' }),
  ],
  symbols: { N_c: ['Bearing-capacity factor for cohesion', '1'], N_q: ['Bearing-capacity factor for surcharge', '1'], N_gamma: ['Bearing-capacity factor for self-weight', '1'], K_p: ['Passive earth-pressure coefficient', '1'], s_ca: ['Shape term', '1'], d_ca: ['Depth term', '1'], i_ca: ['Inclination term', '1'], s_g: ['Shape factor', '1'], d_g: ['Depth factor', '1'], i_q: ['Inclination factor on surcharge', '1'], i_g: ['Inclination factor on self-weight', '1'], theta_l: ['Load inclination from the vertical', 'rad'], q_u: ['Ultimate bearing pressure', 'Pa'], Q_u: ['Ultimate vertical capacity', 'N'], H_u: ['Ultimate sliding resistance', 'N'], FS_b: ['Factor of safety on bearing', '1'], FS_s: ['Factor of safety on sliding', '1'] },
  equations: a => {
    const out = [];
    if (a.undrained) {
      out.push(eq('nc', 'Prandtl bearing-capacity factor', 'N_c', 'pi + 2', { kind: 'law', origin: 'Exact plasticity solution for a strip on a weightless Tresca material; Prandtl (1921)' }));
      if (a.shape) out.push(eq('sc', 'Shape term', 's_ca', '0.2*B/L', { kind: 'empirical', origin: 'Skempton (1951); Brinch Hansen (1970)', needs: ['shape'] }));
      if (!a.no_depth) out.push(eq('dc', 'Depth term', 'd_ca', '0.4*D_f/B', { kind: 'empirical', origin: 'Brinch Hansen (1970), D ≤ B', note: 'For embedment deeper than the width the solver uses 0.4·atan(D_f/B), as Brinch Hansen gives.' }));
      if (a.incl) out.push(eq('ic', 'Inclination term', 'i_ca', '0.5 - 0.5*sqrt(max(1 - H/(B*L*s_u), 0))', { kind: 'empirical', origin: 'Brinch Hansen (1970)', needs: ['incl'] }));
      out.push(eq('qu', 'Ultimate bearing pressure', 'q_u', `N_c*s_u*(1${a.shape ? ' + s_ca' : ''}${a.no_depth ? '' : ' + d_ca'}${a.incl ? ' - i_ca' : ''}) + gamma_sub*D_f`, { kind: 'closure', origin: 'Brinch Hansen (1970) for φ = 0', needs: ['undrained'], note: 'B is the shorter and L the longer plan dimension; the solver swaps them if they are entered the other way round.' }));
      out.push(eq('hu', 'Sliding resistance', 'H_u', 'alpha_s*s_u*B*L', { kind: 'closure', origin: 'Base shear at a fraction of the undrained strength' }));
    } else {
      out.push(eq('kp', 'Passive coefficient', 'K_p', 'tan(pi/4 + phi/2)^2', { kind: 'definition' }));
      out.push(eq('nq', 'Surcharge factor', 'N_q', 'exp(pi*tan(phi))*K_p', { kind: 'law', origin: 'Prandtl–Reissner plasticity solution' }));
      out.push(eq('ng', 'Self-weight factor', 'N_gamma', '(N_q - 1)*tan(1.4*phi)', { kind: 'empirical', origin: 'Meyerhof (1963)' }));
      if (a.shape) out.push(eq('sg', 'Shape factor', 's_g', '1 + 0.1*K_p*B/L', { kind: 'empirical', origin: 'Meyerhof (1963)', needs: ['shape'] }));
      if (!a.no_depth) out.push(eq('dg', 'Depth factor', 'd_g', '1 + 0.1*sqrt(K_p)*D_f/B', { kind: 'empirical', origin: 'Meyerhof (1963)' }));
      if (a.incl) { out.push(eq('th', 'Load inclination', 'tan(theta_l)', 'H/V', { kind: 'definition' })); out.push(eq('iq', 'Inclination factor on surcharge', 'i_q', '(1 - 2*theta_l/pi)^2', { kind: 'empirical', origin: 'Meyerhof (1963)', needs: ['incl'] })); out.push(eq('ig', 'Inclination factor on self-weight', 'i_g', 'max(1 - theta_l/phi, 0)^2', { kind: 'empirical', origin: 'Meyerhof (1963)', needs: ['incl'] })); }
      const f = `${a.shape ? '*s_g' : ''}${a.no_depth ? '' : '*d_g'}`;
      out.push(eq('qu', 'Ultimate bearing pressure', 'q_u', `0.5*gamma_sub*B*N_gamma${f}${a.incl ? '*i_g' : ''} + gamma_sub*D_f*N_q${f}${a.incl ? '*i_q' : ''}`, { kind: 'closure', origin: 'Terzaghi superposition with Meyerhof factors, c′ = 0', note: 'B is the shorter and L the longer plan dimension; the solver swaps them if they are entered the other way round.' }));
      out.push(eq('hu', 'Sliding resistance', 'H_u', 'alpha_s*V*tan(phi)', { kind: 'law', origin: 'Coulomb friction on the base' }));
    }
    out.push(eq('Qu', 'Ultimate vertical capacity', 'Q_u', 'q_u*B*L', { kind: 'definition' }));
    out.push(eq('fsb', 'Factor of safety on bearing', 'FS_b', 'Q_u/V', { kind: 'definition' }));
    out.push(eq('fss', 'Factor of safety on sliding', 'FS_s', 'H_u/H', { kind: 'definition' }));
    return out;
  },
  derivation: a => (a.undrained ? [
    { text: 'For a strip on a weightless soil that yields at a shear stress s_u, the slip-line field consists of an active wedge under the footing, a fan and a passive wedge. Its exact collapse pressure is Prandtl\'s result.', tex: 'q_u = (\\pi + 2)\\,s_u = 5.14\\,s_u' },
    { text: 'A rectangular plan mobilises end resistance, embedment adds overburden and some shear above the base, and a horizontal load reduces the capacity. Brinch Hansen combined these as additive terms.', tex: 'q_u = (\\pi+2)\\,s_u\\left(1 + s_c^a + d_c^a - i_c^a\\right) + \\gamma\' D,\\quad s_c^a = 0.2\\frac{B}{L},\\ i_c^a = \\tfrac12 - \\tfrac12\\sqrt{1 - \\frac{H}{A\\,s_u}}' },
    { text: 'Sliding is resisted by shear on the base, limited to a fraction α of the undrained strength.', tex: 'H_u = \\alpha\\,s_u\\,A,\\qquad FS_s = H_u/H,\\qquad FS_b = q_u A / V' },
  ] : [
    { text: 'For a frictional soil the surcharge factor follows from the Prandtl–Reissner solution; the self-weight factor has no closed form and Meyerhof\'s approximation is used.', tex: 'N_q = e^{\\pi\\tan\\varphi}\\tan^2\\!\\left(45^\\circ + \\tfrac{\\varphi}{2}\\right),\\qquad N_\\gamma = (N_q - 1)\\tan(1.4\\varphi)' },
    { text: 'Terzaghi\'s superposition adds the self-weight and surcharge contributions, each with shape, depth and inclination factors.', tex: 'q_u = \\tfrac12\\gamma\' B N_\\gamma s_\\gamma d_\\gamma i_\\gamma + \\gamma\' D\\,N_q s_q d_q i_q' },
    { text: 'Sliding is resisted by friction on the base.', tex: 'H_u = \\alpha\\,V\\tan\\varphi' },
  ]),
  solve(v, a) {
    const r = mudmatRun(v, a), warnings = [];
    if (a.undrained && a.incl && v.H >= r.A * v.s_u) warnings.push('The horizontal load exceeds the full undrained shear strength over the base: the mat slides regardless of vertical capacity.');
    if (v.D_f > r.B) warnings.push('Embedment exceeds the width: the foundation is no longer shallow and these formulas are not appropriate.');
    const ok = s => { const q = mudmatRun(v, a, s); return Math.min(q.FSb / v.FS_bt, q.FSs / v.FS_st) - 1; };
    let sReq = NaN, sTxt;
    if (ok(50) < 0) sTxt = a.undrained ? 'Not achievable up to 50 times the stated size' : 'Not achievable by enlarging the mat — drained sliding does not depend on area';
    else if (ok(0.02) >= 0) sReq = 0.02; else sReq = N.bisect(ok, 0.02, 50, 1e-10);
    const sc = N.linspace(0.4, 2.5, 50), cap = sc.map(s => mudmatRun(v, a, s).Qu / 1e3);
    const Hmax = Math.max(r.Hu, 1), Hs = N.linspace(0, Hmax, 60), Vu = Hs.map(h => mudmatRun(v, a, 1, h).Qu / 1e3);
    return {
      scalars: [
        scalar('A_f', 'Plan area', r.A, 'm^2'), scalar('q_app', 'Applied bearing pressure', v.V / r.A, 'Pa', { show: 'kPa' }),
        scalar('q_u', 'Ultimate bearing pressure', r.qu, 'Pa', { show: 'kPa' }), scalar('Q_u', 'Ultimate vertical capacity', r.Qu, 'N', { show: 'kN' }),
        scalar('FS_b', 'Factor of safety on bearing', r.FSb, '1', { note: r.FSb >= v.FS_bt ? 'meets the target' : 'below the target' }),
        scalar('H_u', 'Ultimate sliding resistance', r.Hu, 'N', { show: 'kN' }),
        scalar('FS_s', 'Factor of safety on sliding', Number.isFinite(r.FSs) ? r.FSs : NaN, '1', { text: Number.isFinite(r.FSs) ? undefined : 'Unlimited — no horizontal load', note: r.FSs >= v.FS_st ? 'meets the target' : 'below the target' }),
        scalar('theta_l', 'Load inclination from the vertical', Math.atan2(v.H, v.V), 'rad', { show: 'deg' }),
        ...(a.undrained ? [scalar('N_c', 'Bearing-capacity factor N_c', r.parts.Nc, '1'), scalar('i_ca', 'Inclination term', r.parts.ia, '1')] : [scalar('N_q', 'Bearing-capacity factor N_q', r.parts.Nq, '1'), scalar('N_gamma', 'Bearing-capacity factor N_γ', r.parts.Ng, '1')]),
        scalar('scale_req', 'Plan scale factor needed to meet both targets', sReq, '1', { text: sTxt }),
        scalar('B_req', 'Width needed at the same aspect ratio', sReq * r.B, 'm', { text: sTxt }),
      ],
      series: [
        line('capacity-width', 'Vertical capacity against mat size', 'Width (aspect ratio held)', 'm', sc.map(s => s * r.B), [{ label: 'Ultimate capacity', data: cap }, { label: 'Vertical load × target factor', data: sc.map(() => v.V * v.FS_bt / 1e3), dash: true }], 'Force', 'kN'),
        line('vh-envelope', 'Vertical capacity against horizontal load', 'Horizontal load', 'kN', Hs.map(h => h / 1e3), [{ label: 'Ultimate vertical capacity', data: Vu }], 'Vertical capacity', 'kN', { points: [{ x: v.H / 1e3, y: v.V / 1e3 }], pointsLabel: 'Applied load', note: 'The envelope ends at the sliding resistance.' }),
      ],
      checks: [check('Bearing pressure is non-negative', r.qu < 0 ? 1 : 0, 0, 'q_u ≥ 0')],
      warnings,
    };
  },
  benchmarks() {
    const f30 = bearingFactors(30 * DEG);
    return [
      bench('N_c in the limit φ → 0', bearingFactors(1e-5).Nc, Math.PI + 2, 'Prandtl (1921): N_c = π + 2', 1e-4),
      bench('N_q at φ = 30°', f30.Nq, 18.40, 'Tabulated Prandtl–Reissner value: e^{π tan φ}·tan²(45° + φ/2) = 18.40', 1e-3),
      bench('Surface strip on clay: q_u = (π + 2)·s_u', mudmatRun({ B: 1, L: 1e9, D_f: 0, s_u: 1e4, gamma_sub: 6e3, phi: 0.5, alpha_s: 1, V: 1e4, H: 0 }, { undrained: true, shape: true, incl: true, no_depth: false }).qu / 1e4, Math.PI + 2, 'Prandtl (1921), exact for a strip on a Tresca soil', 1e-8),
      bench('Strip with full base shear mobilised: q_u = (1 + π/2)·s_u', mudmatRun({ B: 1, L: 1, D_f: 0, s_u: 1e4, gamma_sub: 6e3, phi: 0.5, alpha_s: 1, V: 1e4, H: 1e4 }, { undrained: true, shape: false, incl: true, no_depth: true }).qu / 1e4, 1 + Math.PI / 2, 'Exact plasticity solution for a strip sliding at H = A·s_u', 1e-12),
      bench('N_c at φ = 30°', f30.Nc, 30.14, 'Tabulated Prandtl–Reissner value', 1e-3),
      bench('Meyerhof N_γ at φ = 30°', f30.Ng, 15.67, 'Tabulated value, Meyerhof (1963)', 1e-3),
    ];
  },
  validation: [],
  diagram(v) {
    return svg(`
      ${S.rect(30, 30, 580, 150, 'd-liquid', 0)} ${S.path('M30 180 L610 180', 'd-ground')}
      ${S.rect(200, 168, 240, 12, 'd-body', 1)} ${S.rect(200, 180, 6, 26, 'd-body', 0)} ${S.rect(434, 180, 6, 26, 'd-body', 0)}
      ${S.rect(260, 100, 120, 68, 'd-body')} ${S.text(320, 138, 'structure')}
      ${S.arrow(320, 50, 320, 96, 'd-arrow d-hazard')} ${S.text(332, 66, `V = ${lab(v.V / 1e3, 'kN')}`, 'd-text', 'start')}
      ${S.arrow(180, 134, 256, 134, 'd-arrow d-hazard')} ${S.text(174, 128, `H = ${lab(v.H / 1e3, 'kN')}`, 'd-text', 'end')}
      ${S.path('M200 206 Q320 330 440 206', 'd-line')} ${S.path('M440 206 Q500 290 560 180', 'd-line')} ${S.path('M200 206 Q140 290 80 180', 'd-line')}
      ${S.text(320, 246, 'failure mechanism')} ${S.text(320, 300, `s_u = ${lab(v.s_u / 1e3, 'kPa')}   γ′ = ${lab(v.gamma_sub / 1e3, 'kN/m³')}`)}
      ${S.dim(200, 226, 440, 226, `B = ${lab(v.B, 'm')}`)}
      ${S.text(460, 200, `skirt ${lab(v.D_f, 'm')}`, 'd-text d-small', 'start')}
      ${S.text(320, 345, `plan ${lab(v.B, 'm')} × ${lab(v.L, 'm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the vertical and combined-load capacity of a model mudmat on a prepared clay bed and compare with the bearing-capacity formulas.',
    apparatus: ['Consolidated kaolin clay bed in a strongbox (on the laboratory floor or in a geotechnical centrifuge)', 'Rigid rectangular model foundations with and without skirts', 'Two-axis actuator applying vertical and horizontal displacement'],
    instruments: [{ name: 'Load cells on both axes', measures: 'Vertical and horizontal load', range: '0–5 kN', resolution: '±0.1 %' }, { name: 'Displacement transducers', measures: 'Settlement and sliding', range: '0–50 mm', resolution: '±0.01 mm' }, { name: 'T-bar or miniature vane', measures: 'Undrained shear strength profile', range: '0–100 kPa', resolution: '±3 %' }],
    procedure: ['Characterise the strength profile immediately before and after each test.', 'Push the foundation vertically at a rate fast enough for undrained response until a plateau load is reached.', 'On fresh sites apply a fixed vertical load, then displace horizontally to failure to trace the V–H envelope.'],
    controls: ['Repeat tests at two penetration rates to confirm undrained conditions', 'Strip-shaped model to isolate the shape factor'],
    signatures: ['Bearing pressure at failure close to 5.14·s_u for a long strip and about 6·s_u for a square', 'Vertical capacity falling as horizontal load approaches the base shear limit'],
    safety: ['Centrifuge containment and balance checks', 'Guard actuators'],
  },
  falsify: ['A surface strip on uniform clay failing at a pressure outside about 5.14·s_u by more than the uncertainty in strength.', 'No reduction of vertical capacity under substantial horizontal load.'],
  alternatives: [{ name: 'Failure envelopes in V–H–M space', text: 'Combined vertical, horizontal and moment loading assessed with interaction diagrams from finite-element limit analysis.' }, { name: 'Strength increasing with depth', text: 'Davis and Booker\'s solution corrects N_c for a linear strength gradient, typical of normally consolidated clay.' }, { name: 'Effective-area method', text: 'Eccentric loads are handled by reducing the plan dimensions to B − 2e.' }],
  hazards: [{ hazard: 'Bearing failure or excessive settlement', cause: 'Strength over-estimated, or loads during installation and hydrotest higher than assumed', mitigation: 'Site-specific soil investigation, safety factors, skirts' }, { hazard: 'Sliding', cause: 'Pipeline expansion or snag loads on a smooth base', mitigation: 'Skirts or increased area; allow controlled sliding by design where intended' }],
  standards: ['API RP 2GEO (geotechnical and foundation design considerations)', 'ISO 19901-4 (geotechnical and foundation design considerations)', 'DNV-RP-C212 (offshore soil mechanics and geotechnical engineering)'],
  limits: 'Centrally loaded rigid rectangular mat on a level, homogeneous soil. No overturning moment or eccentricity, no torsion, uniform strength with depth. The undrained option applies to clay under short-term load, the drained option to cohesionless soil. Settlement is not assessed.',
  numerics: { method: 'Closed-form bearing-capacity factors; bisection for the plan scale that meets both safety targets' },
  optimise: { objective: 'FS_b', sense: 'max', vars: ['B', 'L'], note: 'Capacity grows with plan area; steel weight and installation limits bound the size in practice.' },
  inverse: { series: 'capacity-width', fit: ['s_u'] },
  extensions: ['Moment loading with effective area and V–H–M envelopes', 'Strength increasing linearly with depth', 'Consolidation settlement under sustained load'],
};

// ------------------------------------------------------------------ one-dimensional consolidation
const YEAR = 3.15576e7;
/** Average degree of consolidation for a uniform initial excess pore pressure (Terzaghi's Fourier series). */
function consolSeries(Tv, terms = 400) { let s = 0; for (let m = 0; m < terms; m++) { const M = Math.PI * (2 * m + 1) / 2; s += 2 / (M * M) * Math.exp(-M * M * Tv); } return 1 - s; }
function consolRun(v, a) {
  const H = v.H_c, dr = a.double ? H / 2 : H, nx = Math.max(11, Math.round(v.n_x)), cv = v.c_v;
  const shape = z => (a.uniform ? 1 : 1 - z / H), fMean = a.uniform ? 1 : 0.5, tc = a.instant ? 0 : v.t_c;
  const tSim = Math.min(v.t_end, tc + 3 * dr * dr / cv), tA = 0.02 * tSim;
  const left = { type: 'dirichlet', value: 0 }, right = a.double ? { type: 'dirichlet', value: 0 } : { type: 'neumann', value: 0 };
  const src = a.instant ? undefined : (z, t) => (t < tc ? v.dq * shape(z) / tc : 0);
  const A = N.diffusion1D({ D: cv, L: H, nx, tEnd: tA, nt: 120, u0: a.instant ? z => v.dq * shape(z) : () => 0, left, right, source: src, frames: 12 });
  const B = N.diffusion1D({ D: cv, L: H, nx, tEnd: tSim - tA, nt: 360, u0: (z, i) => A.final[i], left, right, source: src ? (z, t) => src(z, t + tA) : undefined, frames: 48 });
  const times = [...A.times, ...B.times.slice(1).map(t => t + tA)], snaps = [...A.snaps, ...B.snaps.slice(1)];
  if (tSim < v.t_end) { times.push(v.t_end); snaps.push(B.final.map(u => u * Math.exp(-(Math.PI * Math.PI / 4) * cv * (v.t_end - tSim) / (dr * dr)))); }
  const load = t => (a.instant ? 1 : Math.min(t / tc, 1)), tot = v.dq * fMean * H;
  const U = snaps.map((u, i) => N.clamp((load(times[i]) * tot - N.trapz(A.x, u)) / tot, 0, 1));
  return { x: A.x, times, snaps, U, dr, tSim, fMean, exactOK: a.instant && (a.uniform || a.double) };
}
const consolidation = {
  id: 'consolidation-1d',
  title: 'One-dimensional consolidation of a clay layer',
  module: 2, klass: 'I', domains: ['geotechnical'],
  keywords: ['consolidation', 'terzaghi consolidation', 'excess pore pressure', 'pore pressure dissipation', 'degree of consolidation', 'coefficient of consolidation', 'settlement', 'clay layer', 'time factor', 'isochrones', 'oedometer', 'primary consolidation', 'embankment settlement'],
  summary: 'Dissipation of excess pore pressure in a loaded clay layer by Terzaghi\'s diffusion equation, average degree of consolidation and settlement against time, with single or double drainage and instantaneous or ramp loading.',
  background: [
    'When a saturated clay is loaded, the nearly incompressible pore water initially carries the whole increment as excess pore pressure. Water then drains slowly towards the permeable boundaries, the pressure is transferred to the soil skeleton as effective stress, and the layer compresses. Terzaghi showed that for one-dimensional strain, Darcy flow and a linear skeleton the excess pore pressure obeys a diffusion equation whose diffusivity is the coefficient of consolidation.',
    'The time needed scales with the square of the longest drainage path, which is why a layer drained on both faces consolidates four times faster than one drained on a single face, and why field settlements can take years although laboratory samples finish in hours.',
  ],
  phenomena: ['Pore-water flow (Darcy)', 'Transfer of total stress to effective stress', 'Compression of the soil skeleton', 'Diffusion with drained boundaries'],
  laws: ['mass', 'fick', 'hooke'],
  refs: ['Terzaghi, K. (1943). Theoretical Soil Mechanics. Wiley.', 'Taylor, D. W. (1948). Fundamentals of Soil Mechanics. Wiley.', 'Knappett, J. A. & Craig, R. F. (2012). Craig\'s Soil Mechanics, 8th ed. Spon Press.', 'Olson, R. E. (1977). Consolidation under time-dependent loading. Journal of the Geotechnical Engineering Division, ASCE 103, 55–60.'],
  inputs: [
    inp('H_c', 'Clay layer thickness', 'm', 6, { min: 0.5, max: 50, kind: 'geometry', aliases: ['layer thickness', 'thickness', 'thick'] }),
    inp('c_v', 'Coefficient of consolidation', 'm^2/yr', 2, { min: 0.1, max: 100, kind: 'environment', aliases: ['coefficient of consolidation', 'cv'], src: 'Typical for soft to firm clay, from oedometer tests' }),
    inp('dq', 'Applied surface load', 'kPa', 100, { min: 1, max: 1000, aliases: ['surcharge', 'applied load', 'load', 'stress increment'] }),
    inp('m_v', 'Coefficient of volume compressibility', '1/MPa', 0.5, { min: 0.01, max: 5, kind: 'environment', aliases: ['volume compressibility', 'compressibility', 'mv'] }),
    inp('t_end', 'Time of interest', 'yr', 2, { min: 0.01, max: 200, aliases: ['time', 'years', 'after'] }),
    inp('t_c', 'Construction (ramp) time', 'yr', 0.5, { min: 0.01, max: 20, aliases: ['construction time', 'ramp time'] }),
    inp('C_c', 'Compression index', '1', 0.3, { min: 0.05, max: 2, kind: 'environment', aliases: ['compression index', 'cc'] }),
    inp('e_0', 'Initial void ratio', '1', 1.0, { min: 0.3, max: 4, kind: 'environment', aliases: ['void ratio'] }),
    inp('sigma_0', 'Initial vertical effective stress at mid-layer', 'kPa', 50, { min: 5, max: 1000, kind: 'environment', aliases: ['initial effective stress', 'overburden'] }),
    inp('n_x', 'Number of grid points through the layer', '1', 81, { min: 21, max: 401, kind: 'numerical' }),
  ],
  assumptions: [
    asm('double', 'The layer drains at both top and bottom, so the drainage path is half the thickness.', { why: 'Clay between two sand layers', alt: 'The base is impermeable: drainage is upward only and the drainage path is the full thickness.' }),
    asm('instant', 'The load is applied instantaneously.', { why: 'Terzaghi\'s classical case', alt: 'The load is ramped linearly over the stated construction time.' }),
    asm('uniform', 'The initial excess pore pressure is uniform with depth (wide loaded area).', { why: 'One-dimensional loading', alt: 'The stress increment decreases linearly from the applied value at the top to zero at the base.' }),
    asm('mv', 'Final settlement follows from a constant coefficient of volume compressibility.', { why: 'Linear skeleton, consistent with the consolidation theory', alt: 'Final settlement is computed from the compression index and void ratio (normally consolidated clay).' }),
  ],
  symbols: { u: ['Excess pore pressure', 'Pa'], z: ['Depth below the top of the layer', 'm'], t: ['Time', 's'], d_r: ['Longest drainage path', 'm'], T_v: ['Time factor', '1'], U_avg: ['Average degree of consolidation', '1'], s_inf: ['Final consolidation settlement', 'm'], s_t: ['Settlement at time t', 'm'] },
  equations: a => [
    a.instant
      ? eq('pde', 'Terzaghi consolidation equation', 'pd(u,t)', 'c_v*pd2(u,z)', { kind: 'law', origin: 'Continuity of pore water with Darcy flow and a linear skeleton; Terzaghi (1943)', needs: ['instant'] })
      : eq('pde', 'Consolidation under ramp loading', 'pd(u,t)', `c_v*pd2(u,z) + dq${a.uniform ? '' : '*(1 - z/H_c)'}/t_c*heaviside(t_c - t)`, { kind: 'law', origin: 'Terzaghi\'s equation with a source equal to the rate of total-stress increase' }),
    ...(a.instant ? [eq('ic', 'Initial condition', 'u', a.uniform ? 'dq' : 'dq*(1 - z/H_c)', { kind: 'initial', origin: 'Pore water carries the whole stress increment at first' })] : []),
    eq('dr', 'Drainage path', 'd_r', a.double ? 'H_c/2' : 'H_c', { kind: 'definition', needs: a.double ? ['double'] : [] }),
    eq('tv', 'Time factor', 'T_v', 'c_v*t_end/d_r^2', { kind: 'definition' }),
    eq('U', 'Average degree of consolidation', 'U_avg', `${a.instant ? '1' : 'min(t_end/t_c, 1)'} - int(u, z)/(${a.uniform ? '' : '0.5*'}dq*H_c)`, { kind: 'definition', origin: a.instant ? 'Fraction of the applied excess pore pressure that has dissipated' : 'Effective-stress increase so far as a fraction of the final load; the first term is the fraction of the load applied' }),
    a.mv
      ? eq('sinf', 'Final settlement', 's_inf', `${a.uniform ? '' : '0.5*'}m_v*dq*H_c`, { kind: 'law', origin: 'One-dimensional strain of a linear skeleton', needs: ['mv'] })
      : eq('sinf', 'Final settlement', 's_inf', `C_c/(1 + e_0)*H_c*log10((sigma_0 + ${a.uniform ? '' : '0.5*'}dq)/sigma_0)`, { kind: 'empirical', origin: 'Linear void ratio–log stress relation of normally consolidated clay' }),
    eq('st', 'Settlement at time t', 's_t', 'U_avg*s_inf', { kind: 'derived', origin: 'Settlement proportional to dissipated pore pressure' }),
  ],
  derivation: a => [
    { text: 'Water leaving an element by Darcy flow equals the rate of volume decrease of the skeleton. With vertical flow only and a skeleton of constant compressibility m_v this gives a diffusion equation for the excess pore pressure.', tex: '\\frac{\\partial u}{\\partial t} = c_v\\,\\frac{\\partial^2 u}{\\partial z^2},\\qquad c_v = \\frac{k}{m_v\\,\\gamma_w}' },
    { text: `The pore pressure is zero at a drained boundary and has zero gradient at an impermeable one. Here the layer is drained ${a.double ? 'at both faces' : 'at the top only'}, so the longest drainage path is ${a.double ? 'half the thickness' : 'the full thickness'}.`, tex: a.double ? 'u(0,t) = u(H,t) = 0,\\qquad d = H/2' : 'u(0,t) = 0,\\ \\partial u/\\partial z\\,(H,t) = 0,\\qquad d = H' },
    { text: 'Separation of variables for a uniform initial pressure gives a Fourier series; integrating it over depth gives the average degree of consolidation as a function of the time factor alone.', tex: 'U = 1 - \\sum_{m=0}^{\\infty}\\frac{2}{M^2}\\,e^{-M^2 T_v},\\quad M = \\frac{\\pi}{2}(2m+1),\\quad T_v = \\frac{c_v t}{d^2}' },
    { text: 'Settlement at any time is the degree of consolidation times the final settlement.', tex: a.mv ? 's(t) = U(t)\\,m_v\\,\\Delta q\\,H' : 's(t) = U(t)\\,\\frac{C_c}{1+e_0}\\,H\\log_{10}\\frac{\\sigma\'_0 + \\Delta\\sigma}{\\sigma\'_0}' },
  ],
  solve(v, a) {
    const r = consolRun(v, a), Tv = v.c_v * v.t_end / r.dr ** 2, Unum = r.U[r.U.length - 1];
    const Uex = r.exactOK ? consolSeries(Tv) : NaN;
    const dqm = v.dq * r.fMean, sInf = a.mv ? v.m_v * dqm * v.H_c : v.C_c / (1 + v.e_0) * v.H_c * Math.log10((v.sigma_0 + dqm) / v.sigma_0);
    const tU = target => { if (r.exactOK) return (target === 0.5 ? 0.19675 : 0.84795) * r.dr ** 2 / v.c_v; const i = r.U.findIndex(q => q >= target); return i <= 0 ? NaN : r.times[i - 1] + (r.times[i] - r.times[i - 1]) * (target - r.U[i - 1]) / (r.U[i] - r.U[i - 1]); };
    const t50 = tU(0.5), t90 = tU(0.9), ty = r.times.map(t => t / YEAR), last = r.snaps[r.snaps.length - 1];
    const pick = [0.02, 0.1, 0.3, 0.6, 1].map(f => Math.min(r.snaps.length - 1, Math.round(f * (r.snaps.length - 1))));
    const warnings = [];
    if (!a.mv && !a.uniform) warnings.push('With a stress increment that varies with depth the compression-index settlement uses the mean increment; a layered calculation is more accurate.');
    return {
      scalars: [
        scalar('d_r', 'Longest drainage path', r.dr, 'm'), scalar('T_v', 'Time factor at the time of interest', Tv, '1'),
        scalar('U_avg', 'Average degree of consolidation (numerical)', Unum, '1', { show: '%' }),
        scalar('U_exact', 'Degree of consolidation from Terzaghi\'s series', Uex, '1', { show: '%', text: r.exactOK ? undefined : 'No closed form for this loading case' }),
        scalar('s_inf', 'Final consolidation settlement', sInf, 'm', { show: 'mm' }), scalar('s_t', 'Settlement at the time of interest', Unum * sInf, 'm', { show: 'mm' }),
        scalar('u_max', 'Largest remaining excess pore pressure', N.maxOf(last), 'Pa', { show: 'kPa' }),
        scalar('t_50', 'Time to 50 % consolidation', t50, 's', { show: 'yr', text: Number.isFinite(t50) ? undefined : 'Not reached within the time simulated' }),
        scalar('t_90', 'Time to 90 % consolidation', t90, 's', { show: 'yr', text: Number.isFinite(t90) ? undefined : 'Not reached within the time simulated' }),
      ],
      series: [
        line('U-time', 'Degree of consolidation against time', 'Time', 'yr', ty, [{ label: 'Numerical', data: r.U.map(q => q * 100) }, ...(r.exactOK ? [{ label: 'Terzaghi series', data: r.times.map(t => consolSeries(v.c_v * t / r.dr ** 2, 200) * 100), dash: true }] : [])], 'Degree of consolidation', '%'),
        line('settlement', 'Settlement against time', 'Time', 'yr', ty, [{ label: 'Settlement', data: r.U.map(q => q * sInf * 1e3) }, { label: 'Final settlement', data: ty.map(() => sInf * 1e3), dash: true }], 'Settlement', 'mm'),
        line('isochrones', 'Excess pore pressure isochrones', 'Depth', 'm', r.x, pick.map(i => ({ label: `t = ${lab(r.times[i] / YEAR, 'yr')}`, data: r.snaps[i].map(q => q / 1e3) })), 'Excess pore pressure', 'kPa'),
      ],
      anims: [anim('pore-pressure', 'Dissipation of excess pore pressure', 'Depth', 'm', r.x, r.snaps.map(s => s.map(q => q / 1e3)), ty, 'Excess pore pressure', 'kPa', { yRange: [0, v.dq / 1e3], fill: true, tUnit: 'yr' })],
      checks: [check('Numerical solution against Terzaghi\'s series', r.exactOK ? Unum - Uex : 0, 5e-3, 'Difference in average degree of consolidation at the time of interest')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b0 = { ...a, double: true, instant: true, uniform: true, mv: true }, out = [];
    const r = this.solve(v, b0);
    out.push(bench('Degree of consolidation vs Fourier series', val(r, 'U_avg'), val(r, 'U_exact'), 'Terzaghi (1943)', 2e-3));
    const r1 = this.solve(v, { ...b0, double: false });
    out.push(bench('Single drainage vs Fourier series', val(r1, 'U_avg'), val(r1, 'U_exact'), 'Terzaghi (1943)', 2e-3));
    const r2 = this.solve(v, { ...b0, uniform: false });
    out.push(bench('Linear initial pressure with double drainage', val(r2, 'U_avg'), val(r, 'U_exact'), 'Same U–T_v curve as the uniform case (Taylor 1948)', 2e-3));
    const dr = v.H_c / 2, Tv = v.c_v * v.t_end / dr ** 2, Tc = v.c_v * v.t_c / dr ** 2;
    if (Tv > Tc) {
      let sr = 0; for (let j = 0; j < 400; j++) { const M = Math.PI * (2 * j + 1) / 2; sr += 2 / M ** 4 * (Math.exp(-M * M * (Tv - Tc)) - Math.exp(-M * M * Tv)); }
      const r3 = this.solve(v, { ...b0, instant: false });
      out.push(bench('Ramp loading after the end of construction', val(r3, 'U_avg'), 1 - sr / Tc, 'Superposition of Terzaghi\'s series over a linear ramp (Olson 1977)', 3e-3));
    }
    out.push(bench('Time factor for 50 % consolidation', consolSeries(0.197), 0.5, 'T_50 = 0.197', 2e-3));
    out.push(bench('Time factor for 90 % consolidation', consolSeries(0.848), 0.9, 'T_90 = 0.848', 1e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const iso = Array.from({ length: 21 }, (_, i) => { const s = i / 20; return [250 + 150 * (a.double ? Math.sin(Math.PI * s) : Math.sin(Math.PI * s / 2)), 130 + 130 * s]; });
    return svg(`
      ${S.rect(120, 60, 400, 30, 'd-body', 2)} ${S.text(320, 80, `load Δq = ${lab(v.dq / 1e3, 'kPa')}`)}
      ${[0, 1, 2, 3, 4].map(i => S.arrow(160 + i * 80, 30, 160 + i * 80, 56, 'd-arrow d-hazard')).join('')}
      ${S.rect(120, 90, 400, 40, 'd-ground', 0)} ${S.text(130, 114, 'sand (drained)', 'd-text d-small', 'start')}
      ${S.rect(120, 130, 400, 130, 'd-liquid', 0)} ${S.text(130, 150, 'clay', 'd-text', 'start')}
      ${S.rect(120, 260, 400, 40, 'd-ground', 0)} ${S.text(130, 284, a.double ? 'sand (drained)' : 'impermeable base', 'd-text d-small', 'start')}
      ${S.line(250, 130, 250, 260, 'd-dim')} ${S.poly(iso, 'd-line')} ${S.text(430, 200, 'u(z, t)')}
      ${S.arrow(470, 160, 470, 134)} ${a.double ? S.arrow(470, 230, 470, 256) : ''} ${S.text(500, 180, 'drainage', 'd-text d-small')}
      ${S.dim(90, 130, 90, 260, '')} ${S.text(84, 200, `H = ${lab(v.H_c, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(320, 335, `c_v = ${lab(v.c_v * YEAR, 'm²/yr')}   drainage path ${lab(a.double ? v.H_c / 2 : v.H_c, 'm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the coefficient of consolidation and compressibility of a clay specimen in an oedometer and check the predicted settlement–time curve.',
    apparatus: ['Oedometer (consolidometer) with a confining ring, porous stones top and bottom', 'Loading frame applying stress increments', 'Saturated undisturbed specimen, typically 75 mm diameter and 20 mm high'],
    instruments: [{ name: 'Displacement transducer', measures: 'Specimen compression', range: '0–10 mm', resolution: '±0.002 mm' }, { name: 'Miniature pore-pressure transducer at the undrained base (optional)', measures: 'Excess pore pressure', range: '0–1000 kPa', resolution: '±0.5 kPa' }, { name: 'Load cell or calibrated weights', measures: 'Vertical stress', range: '0–3200 kPa', resolution: '±0.5 %' }],
    procedure: ['Apply a stress increment, usually doubling the previous stress, and record compression at times in geometric progression for 24 hours.', 'Plot compression against the square root of time (Taylor) or log time (Casagrande) to obtain t_90 or t_50 and hence c_v.', 'Repeat for each increment to obtain m_v and the compression index.'],
    controls: ['Calibrate apparatus compliance with a steel dummy specimen', 'Keep the specimen submerged and at constant temperature'],
    signatures: ['Compression linear in √t up to about 60 % consolidation', 'Consolidation time proportional to the square of the drainage path when specimen height is changed'],
    safety: ['Secure hanger weights', 'Care when trimming specimens with sharp tools'],
  },
  falsify: ['Consolidation time that does not scale with the square of the drainage path for the same soil and stress range.', 'A measured mid-plane pore-pressure decay inconsistent with the diffusion solution fitted to the settlement curve.'],
  alternatives: [{ name: 'Large-strain (Gibson) consolidation', text: 'Accounts for changing thickness, permeability and compressibility in very soft soils.' }, { name: 'Radial consolidation with vertical drains', text: 'Barron\'s solution for flow to drains, which usually dominates when drains are installed.' }, { name: 'Secondary compression', text: 'Creep of the skeleton continues at constant effective stress and is added with the secondary compression index.' }],
  hazards: [{ hazard: 'Long-term and differential settlement', cause: 'Slow dissipation in thick or single-drained layers', mitigation: 'Preloading, vertical drains, staged construction, monitoring' }, { hazard: 'Undrained instability during construction', cause: 'Excess pore pressure reduces effective stress and strength', mitigation: 'Control the rate of loading using piezometer readings' }],
  standards: ['ISO 17892-5 (incremental loading oedometer test)', 'ASTM D2435 (one-dimensional consolidation properties of soils)', 'EN 1997 (Eurocode 7: geotechnical design)'],
  limits: 'Saturated, homogeneous clay with one-dimensional strain and flow, small strains, and constant c_v and m_v over the stress increment. Secondary compression, lateral drainage, layering and large-strain effects are not included.',
  numerics: { method: 'Crank–Nicolson finite differences in two stages (fine steps for the first 2 % of the time, then coarser), trapezoidal integration for the degree of consolidation', order: 2, stability: 'Unconditionally stable', resolution: 'n_x' },
  optimise: { objective: 't_90', sense: 'min', vars: ['H_c'], note: 'Time scales with the square of the drainage path; in practice the path is shortened with vertical drains.' },
  inverse: { series: 'settlement', fit: ['c_v', 'm_v'] },
  extensions: ['Vertical drains with combined radial and vertical flow', 'Multi-layer profiles with different c_v', 'Secondary compression and staged loading'],
};

// ------------------------------------------------------------------ infinite slope
const GAMMA_W = 1000 * g;
function slopeFS(v, a, beta = v.beta, z = v.z, m = v.m_w) {
  const mm = a.seepage ? m : 0, ga = (1 - mm) * v.gamma + mm * v.gamma_sat, cb = Math.cos(beta), sb = Math.sin(beta), kh = a.static ? 0 : v.k_h;
  const sig = ga * z * cb * cb - kh * ga * z * sb * cb, tau = ga * z * sb * cb + kh * ga * z * cb * cb, u = a.drained ? GAMMA_W * mm * z * cb * cb : 0;
  const sigE = Math.max(sig - u, 0), tauF = a.drained ? (a.cohesion ? v.c_eff : 0) + sigE * Math.tan(v.phi) : v.s_u;
  return { FS: tauF / tau, sig, tau, u, tauF, ga, sigE, W: ga * z * cb * Math.hypot(1, kh) };
}
/** Smallest slope angle at which the factor of safety falls to one (NaN if it never does below 85°). */
function slopeCritAngle(v, a) {
  const f = b => slopeFS(v, a, b).FS - 1;
  let lo = 0.5 * DEG;
  if (f(lo) <= 0) return NaN;
  for (let d = 1; d <= 85; d += 0.5) { const hi = d * DEG; if (f(hi) <= 0) return N.bisect(f, lo, hi, 1e-12); lo = hi; }
  return NaN;
}
const slopeStability = {
  id: 'slope-stability-infinite',
  title: 'Infinite-slope stability',
  module: 2, klass: 'I', domains: ['geotechnical'],
  keywords: ['infinite slope', 'slope stability', 'factor of safety', 'landslide', 'slope failure', 'seepage', 'translational slide', 'shallow slide', 'slope angle', 'mohr-coulomb', 'pore pressure ratio', 'submarine slope', 'slope'],
  summary: 'Factor of safety of a long uniform slope against shallow translational sliding, with cohesion, steady seepage parallel to the slope, an optional pseudo-static seismic coefficient, and an undrained alternative.',
  background: [
    'Where a slide is long compared with its depth, end effects are negligible and every vertical slice is in the same state. Resolving the weight of a slice parallel and normal to a slip plane at depth z gives the shear and normal stresses directly, and the factor of safety is the ratio of the Mohr–Coulomb strength on that plane to the shear stress.',
    'Ground water flowing parallel to the slope reduces the effective normal stress and so the frictional strength; in a cohesionless soil with the water table at the surface the factor of safety is roughly halved. Cohesion makes the factor of safety depend on depth, defining a critical depth below which a slip can occur.',
  ],
  phenomena: ['Gravity-driven shear on a planar slip surface', 'Mohr–Coulomb frictional strength', 'Pore-pressure reduction of effective stress', 'Pseudo-static seismic loading'],
  laws: ['newton2', 'newton3'],
  refs: ['Skempton, A. W. & DeLory, F. A. (1957). Stability of natural slopes in London Clay. Proceedings of the 4th International Conference on Soil Mechanics and Foundation Engineering, London, 2, 378–381.', 'Duncan, J. M., Wright, S. G. & Brandon, T. L. (2014). Soil Strength and Slope Stability, 2nd ed. Wiley.', 'Knappett, J. A. & Craig, R. F. (2012). Craig\'s Soil Mechanics, 8th ed. Spon Press.', 'Lambe, T. W. & Whitman, R. V. (1969). Soil Mechanics. Wiley.'],
  inputs: [
    inp('beta', 'Slope angle', 'deg', 25, { min: 2, max: 60, kind: 'geometry', aliases: ['slope angle', 'slope', 'inclination'] }),
    inp('z', 'Depth of the slip plane (vertical)', 'm', 3, { min: 0.3, max: 30, kind: 'geometry', aliases: ['depth', 'slip depth', 'slip plane'] }),
    inp('c_eff', 'Effective cohesion', 'kPa', 5, { min: 0, max: 100, kind: 'environment', aliases: ['cohesion', 'effective cohesion'] }),
    inp('phi', 'Effective friction angle', 'deg', 30, { min: 5, max: 50, kind: 'environment', aliases: ['friction angle', 'angle of friction'] }),
    inp('gamma', 'Bulk unit weight above the water table', 'kN/m^3', 18, { min: 12, max: 24, kind: 'environment', aliases: ['unit weight', 'bulk unit weight'] }),
    inp('gamma_sat', 'Saturated unit weight', 'kN/m^3', 20, { min: 14, max: 25, kind: 'environment', aliases: ['saturated unit weight'] }),
    inp('m_w', 'Height of the water table above the slip plane as a fraction of its depth', '1', 0.5, { min: 0, max: 1, kind: 'environment', aliases: ['water table', 'groundwater', 'saturation ratio'] }),
    inp('k_h', 'Horizontal seismic coefficient', '1', 0.1, { min: 0, max: 0.5, kind: 'environment', aliases: ['seismic coefficient', 'earthquake coefficient'] }),
    inp('s_u', 'Undrained shear strength on the slip plane', 'kPa', 25, { min: 1, max: 300, kind: 'environment', aliases: ['undrained shear strength', 'su'] }),
  ],
  assumptions: [
    asm('drained', 'Strength is drained (effective-stress Mohr–Coulomb).', { why: 'Long-term stability of natural slopes', alt: 'Short-term undrained analysis: the strength on the slip plane is the undrained shear strength.' }),
    asm('seepage', 'Steady seepage flows parallel to the slope with the water table at the stated height above the slip plane.', { why: 'Wet-season condition', alt: 'The slope is dry or fully drained: pore pressure is zero.' }),
    asm('cohesion', 'The effective cohesion is mobilised on the slip plane.', { why: 'Cemented or over-consolidated soil, or root reinforcement', alt: 'Cohesion is neglected (c′ = 0), as for residual strength or clean sand.' }),
    asm('static', 'Loading is static.', { why: 'No earthquake', alt: 'A pseudo-static horizontal inertia force k_h·W acts on each slice.' }),
  ],
  symbols: { gamma_a: ['Average unit weight above the slip plane', 'N/m^3'], gamma_w: ['Unit weight of water', 'N/m^3'], sigma_n: ['Total normal stress on the slip plane', 'Pa'], tau: ['Shear stress on the slip plane', 'Pa'], u_p: ['Pore pressure on the slip plane', 'Pa'], tau_f: ['Shear strength on the slip plane', 'Pa'], FS: ['Factor of safety', '1'] },
  equations: a => {
    const wet = a.seepage, kh = !a.static;
    return [
      eq('ga', 'Average unit weight', 'gamma_a', wet ? '(1 - m_w)*gamma + m_w*gamma_sat' : 'gamma', { kind: 'definition', needs: wet ? ['seepage'] : [] }),
      eq('sig', 'Normal stress on the slip plane', 'sigma_n', `gamma_a*z*cos(beta)^2${kh ? ' - k_h*gamma_a*z*sin(beta)*cos(beta)' : ''}`, { kind: 'law', origin: 'Force equilibrium of a slice normal to the slope' + (kh ? ', including the pseudo-static inertia force' : '') }),
      eq('tau', 'Shear stress on the slip plane', 'tau', `gamma_a*z*sin(beta)*cos(beta)${kh ? ' + k_h*gamma_a*z*cos(beta)^2' : ''}`, { kind: 'law', origin: 'Force equilibrium of a slice parallel to the slope', needs: kh ? [] : ['static'] }),
      ...(wet && a.drained ? [eq('u', 'Pore pressure', 'u_p', 'gamma_w*m_w*z*cos(beta)^2', { kind: 'derived', origin: 'Flow net for seepage parallel to the slope', needs: ['seepage'] })] : []),
      a.drained
        ? eq('tf', 'Shear strength', 'tau_f', `${a.cohesion ? 'c_eff + ' : ''}max(sigma_n${wet ? ' - u_p' : ''}, 0)*tan(phi)`, { kind: 'closure', origin: 'Mohr–Coulomb failure criterion in effective stress', needs: ['drained'] })
        : eq('tf', 'Shear strength', 'tau_f', 's_u', { kind: 'closure', origin: 'Undrained (total-stress) strength' }),
      eq('fs', 'Factor of safety', 'FS', 'tau_f/tau', { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'Take a vertical slice of unit width and depth z. Its weight per unit slope length is γ·z·cos β. Resolving normal and parallel to the slope, with the side forces on the slice cancelling because every slice is identical, gives the stresses on the slip plane.', tex: '\\sigma_n = \\gamma z\\cos^2\\beta,\\qquad \\tau = \\gamma z\\sin\\beta\\cos\\beta' },
    { text: 'For seepage parallel to the slope the equipotentials are normal to it, so the pressure head on the slip plane is the water height above it times cos²β.', tex: 'u = \\gamma_w\\,m\\,z\\cos^2\\beta' },
    { text: a.drained ? 'The strength follows the Mohr–Coulomb criterion in terms of effective stress, and the factor of safety is strength over shear stress.' : 'In undrained conditions the strength is independent of normal stress.', tex: a.drained ? 'FS = \\frac{c\' + (\\gamma z\\cos^2\\beta - u)\\tan\\varphi\'}{\\gamma z\\sin\\beta\\cos\\beta}' : 'FS = \\frac{s_u}{\\gamma z\\sin\\beta\\cos\\beta}' },
    { text: 'For a dry cohesionless slope this reduces to the ratio of tangents: the slope is stable up to the angle of repose.', tex: 'FS = \\frac{\\tan\\varphi\'}{\\tan\\beta}' },
  ],
  solve(v, a) {
    const r = slopeFS(v, a), warnings = [];
    if (r.FS < 1) warnings.push('The factor of safety is below one: a slope in this condition would already have failed. Check the inputs or expect instability.');
    if (a.drained && r.sigE === 0) warnings.push('The effective normal stress on the slip plane is zero: pore pressure and seismic force have removed all frictional strength.');
    const bc = slopeCritAngle(v, a), flat = slopeFS(v, a, 0.5 * DEG).FS;
    const fZ = q => slopeFS(v, a, v.beta, q).FS - 1;
    const zc = fZ(0.05) > 0 && fZ(200) < 0 ? N.bisect(fZ, 0.05, 200, 1e-10) : NaN;
    const bs = N.linspace(2 * DEG, 60 * DEG, 59), zs = N.linspace(0.3, Math.max(3 * v.z, 3), 60), ms = N.linspace(0, 1, 41);
    return {
      scalars: [
        scalar('FS', 'Factor of safety', r.FS, '1', { note: r.FS >= 1.5 ? 'above the customary 1.5' : r.FS >= 1 ? 'marginal' : 'unstable' }),
        scalar('sigma_n', 'Total normal stress on the slip plane', r.sig, 'Pa', { show: 'kPa' }), scalar('tau', 'Driving shear stress on the slip plane', r.tau, 'Pa', { show: 'kPa' }),
        scalar('u_p', 'Pore pressure on the slip plane', r.u, 'Pa', { show: 'kPa' }), scalar('tau_f', 'Shear strength on the slip plane', r.tauF, 'Pa', { show: 'kPa' }),
        scalar('r_u', 'Pore-pressure ratio u/(γz)', r.u / (r.ga * v.z), '1'),
        scalar('beta_c', 'Slope angle at which FS = 1', bc, 'rad', { show: 'deg', text: Number.isFinite(bc) ? undefined : flat <= 1 ? 'Unstable at any angle' : 'Stable up to 85°' }),
        scalar('z_c', 'Critical depth at which FS = 1', zc, 'm', { text: Number.isFinite(zc) ? undefined : fZ(0.05) <= 0 ? 'Unstable at any depth' : 'Stable at any depth to 200 m' }),
      ],
      series: [
        line('fs-angle', 'Factor of safety against slope angle', 'Slope angle', 'deg', bs.map(b => b / DEG), [{ label: 'Stated conditions', data: bs.map(b => slopeFS(v, a, b).FS) }, { label: 'Dry slope', data: bs.map(b => slopeFS(v, { ...a, seepage: false }, b).FS), dash: true }, { label: 'FS = 1', data: bs.map(() => 1), dash: true }], 'Factor of safety', '–', { yRange: [0, 4] }),
        line('fs-depth', 'Factor of safety against slip-plane depth', 'Depth', 'm', zs, [{ label: 'Factor of safety', data: zs.map(q => slopeFS(v, a, v.beta, q).FS) }, { label: 'FS = 1', data: zs.map(() => 1), dash: true }], 'Factor of safety', '–'),
        line('fs-water', 'Factor of safety against water-table height', 'Water-table ratio m', '–', ms, [{ label: 'Factor of safety', data: ms.map(q => slopeFS(v, { ...a, seepage: true }, v.beta, v.z, q).FS) }], 'Factor of safety', '–'),
      ],
      checks: [check('Slice equilibrium', (Math.hypot(r.sig, r.tau) - r.W) / (r.ga * v.z), 1e-12, 'Resultant of normal and shear stress against the weight and inertia force of the slice')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b0 = { ...a, drained: true, static: true }, out = [];
    out.push(bench('Dry cohesionless slope FS = tan φ / tan β', slopeFS(v, { ...b0, seepage: false, cohesion: false }).FS, Math.tan(v.phi) / Math.tan(v.beta), 'Lambe & Whitman (1969)', 1e-12));
    out.push(bench('Seepage to the surface, cohesionless: FS = (γ′/γ_sat)·tan φ / tan β', slopeFS(v, { ...b0, seepage: true, cohesion: false }, v.beta, v.z, 1).FS, (v.gamma_sat - GAMMA_W) / v.gamma_sat * Math.tan(v.phi) / Math.tan(v.beta), 'Skempton & DeLory (1957)', 1e-12));
    const kh = Math.max(v.k_h, 0.05), psi = Math.atan(kh);
    out.push(bench('Pseudo-static dry cohesionless slope: FS = tan φ / tan(β + ψ)', slopeFS({ ...v, k_h: kh }, { ...b0, static: false, seepage: false, cohesion: false }).FS, Math.tan(v.phi) / Math.tan(v.beta + psi), 'Resultant body force rotated by ψ = atan k_h', 1e-12));
    out.push(bench('Limiting angle of a dry cohesionless slope', slopeCritAngle(v, { ...b0, seepage: false, cohesion: false }), v.phi, 'Angle of repose equals the friction angle', 1e-9));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const b = Math.min(Math.max(v.beta, 8 * DEG), 40 * DEG), x0 = 60, x1 = 580, y0 = 110, y1 = y0 + (x1 - x0) * Math.tan(b) * 0.45, dz = 60, dw = dz * (a.seepage ? v.m_w : 0);
    return svg(`
      ${S.path(`M${x0} ${y0} L${x1} ${y1} L${x1} 340 L${x0} 340 Z`, 'd-ground')}
      ${S.line(x0, y0, x1, y1, 'd-line')} ${S.line(x0, y0 + dz, x1, y1 + dz, 'd-hazard')}
      ${a.seepage ? S.line(x0, y0 + dz - dw, x1, y1 + dz - dw, 'd-liquid-line') : ''}
      ${S.path(`M300 ${y0 + (300 - x0) / (x1 - x0) * (y1 - y0)} l40 ${40 / (x1 - x0) * (y1 - y0)} l0 ${dz} l-40 ${-40 / (x1 - x0) * (y1 - y0)} z`, 'd-body')}
      ${S.arrow(320, y0 + 80, 320, y0 + 150)} ${S.text(332, y0 + 146, 'W', 'd-text', 'start')}
      ${S.text(x1 - 10, y1 + dz + 18, 'slip plane', 'd-text d-small', 'end')} ${a.seepage ? S.text(x1 - 10, y1 + dz - dw - 6, 'water table', 'd-text d-small', 'end') : ''}
      ${S.text(110, y0 - 12, `β = ${lab(v.beta / DEG, '°')}`)} ${S.text(240, y0 + 60, `z = ${lab(v.z, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(320, 40, `c′ = ${lab(v.c_eff / 1e3, 'kPa')}   φ′ = ${lab(v.phi / DEG, '°')}   γ = ${lab(v.gamma / 1e3, 'kN/m³')}`)}
      ${S.arrow(430, y0 + 30, 500, y0 + 30 + 70 / (x1 - x0) * (y1 - y0), 'd-arrow d-hazard')} ${S.text(470, y0 + 22, 'τ')}
    `);
  },
  experiment: {
    objective: 'Find the inclination at which a uniform soil layer on a tilting plane slides, dry and with seepage, and compare with the infinite-slope prediction.',
    apparatus: ['Tilting flume at least ten times longer than the soil depth, with a roughened base', 'Uniformly placed sand or silt layer', 'Header tank and drain to establish seepage parallel to the bed'],
    instruments: [{ name: 'Inclinometer', measures: 'Flume angle', range: '0–60°', resolution: '±0.1°' }, { name: 'Standpipe piezometers or miniature transducers on the base', measures: 'Pore pressure at the slip plane', range: '0–10 kPa', resolution: '±0.02 kPa' }, { name: 'Direct shear or triaxial apparatus', measures: 'Friction angle and cohesion of the soil at the test density', range: '—', resolution: '±1°' }],
    procedure: ['Measure strength parameters of the soil at the placement density and stress level.', 'Raise the flume slowly, dry, until sliding starts and record the angle.', 'Repeat with steady seepage at several water-table heights.'],
    controls: ['Vary layer length to confirm end effects are negligible', 'Repeat at two layer depths to separate cohesion from friction'],
    signatures: ['Dry failure angle equal to the friction angle for cohesionless soil', 'Failure angle roughly halved, in terms of tan β, with seepage to the surface'],
    safety: ['Secure the flume against over-rotation', 'Contain released soil and water'],
  },
  falsify: ['A dry, cohesionless layer remaining stable at slope angles well above its measured friction angle.', 'No reduction in the failure angle when seepage parallel to the slope is established.'],
  alternatives: [{ name: 'Method of slices', text: 'Bishop, Spencer or Morgenstern–Price analyses handle curved slip surfaces, layered soils and non-uniform geometry.' }, { name: 'Unsaturated strength', text: 'Matric suction above the water table adds apparent cohesion, important for rainfall-triggered slides.' }, { name: 'Newmark sliding block', text: 'Estimates permanent seismic displacement rather than a pseudo-static factor of safety.' }],
  hazards: [{ hazard: 'Landslide', cause: 'Rise of ground water, loss of cohesion, toe erosion or earthquake', mitigation: 'Drainage, regrading, reinforcement, monitoring' }],
  standards: ['EN 1997-1 (Eurocode 7: geotechnical design)', 'BS 6031 (code of practice for earthworks)', 'ISO 19901-4 (geotechnical considerations for offshore sites, for submarine slopes)'],
  limits: 'A planar slip surface parallel to a long, uniform slope with homogeneous soil above it. End and side resistance, curved slip surfaces, layering, suction, and progressive failure are not represented. The pseudo-static option is a crude screening tool.',
  numerics: { method: 'Closed-form evaluation; bisection for the critical angle and depth' },
  optimise: { objective: 'FS', sense: 'max', vars: ['m_w'], note: 'Lowering the water table by drainage is usually the most effective stabilising measure.' },
  inverse: { series: 'fs-angle', fit: ['c_eff', 'phi'] },
  extensions: ['Rainfall infiltration and transient pore pressure', 'Root or soil-nail reinforcement', 'Probabilistic factor of safety with variable strength'],
};

// ------------------------------------------------------------------ beam bending
function beamRun(v, a, n = 201) {
  const L = v.L, EI = v.E * v.I_b, wt = v.w + (a.no_self ? 0 : v.m_l * g), P = v.P, ap = v.a_P * L, bp = L - ap;
  const x = N.linspace(0, L, n), vb = new Array(n), th = new Array(n), M = new Array(n), V = new Array(n);
  for (let i = 0; i < n; i++) {
    const s = x[i];
    if (a.simply) {
      const left = s <= ap;
      vb[i] = wt * s * (L ** 3 - 2 * L * s * s + s ** 3) / (24 * EI) + (left ? P * bp * s * (L * L - bp * bp - s * s) : P * ap * (L - s) * (L * L - ap * ap - (L - s) ** 2)) / (6 * EI * L);
      th[i] = wt * (L ** 3 - 6 * L * s * s + 4 * s ** 3) / (24 * EI) + (left ? P * bp * (L * L - bp * bp - 3 * s * s) : -P * ap * (L * L - ap * ap - 3 * (L - s) ** 2)) / (6 * EI * L);
      M[i] = wt * s * (L - s) / 2 + (left ? P * bp * s / L : P * ap * (L - s) / L);
      V[i] = wt * (L / 2 - s) + (s < ap ? P * bp / L : s > ap ? -P * ap / L : P * (bp - ap) / (2 * L));
    } else {
      const left = s <= ap;
      vb[i] = wt * s * s * (6 * L * L - 4 * L * s + s * s) / (24 * EI) + (left ? P * s * s * (3 * ap - s) : P * ap * ap * (3 * s - ap)) / (6 * EI);
      th[i] = wt * s * (3 * L * L - 3 * L * s + s * s) / (6 * EI) + (left ? P * s * (2 * ap - s) : P * ap * ap) / (2 * EI);
      M[i] = -wt * (L - s) ** 2 / 2 - (left ? P * (ap - s) : 0);
      V[i] = wt * (L - s) + (s < ap ? P : s > ap ? 0 : P / 2);
    }
  }
  const GA = v.E / (2 * (1 + v.nu_p)) * v.A_v, vs = M.map(m => (a.euler ? 0 : (m - M[0]) / GA)), def = vb.map((q, i) => q + vs[i]);
  const absM = M.map(Math.abs), Mmax = N.maxOf(absM), iD = def.reduce((b, q, i) => (Math.abs(q) > Math.abs(def[b]) ? i : b), 0);
  const lam = a.simply ? Math.PI : 1.8751040687, f1 = lam * lam / (2 * Math.PI * L * L) * Math.sqrt(EI / v.m_l);
  let res = 0; const h = L / (n - 1);
  for (let i = 1; i < n - 1; i++) res = Math.max(res, Math.abs(EI * (vb[i - 1] - 2 * vb[i] + vb[i + 1]) / (h * h) + M[i]));
  return { x, def, vb, th, M, V, Mmax, dmax: Math.abs(def[iD]), xD: x[iD], thMax: N.maxOf(th.map(Math.abs)), Vmax: N.maxOf(V.map(Math.abs)), f1, wt, EI, res: Mmax > 0 ? res / Mmax : 0, RA: a.simply ? wt * L / 2 + P * bp / L : wt * L + P, RB: a.simply ? wt * L / 2 + P * ap / L : 0 };
}
const beamBending = {
  id: 'beam-bending',
  title: 'Euler–Bernoulli beam under distributed and point loads',
  module: 2, klass: 'I', domains: ['structural', 'mechanical'],
  keywords: ['beam bending', 'beam deflection', 'euler-bernoulli', 'simply supported beam', 'cantilever', 'bending moment', 'shear force', 'bending stress', 'udl', 'uniformly distributed load', 'point load', 'deflection', 'second moment of area', 'beam', 'girder', 'natural frequency of beam'],
  summary: 'Deflection, slope, bending-moment and shear-force diagrams of a simply supported or cantilever beam carrying a uniform load and a point load, with peak stress and first natural frequency.',
  background: [
    'Euler–Bernoulli theory assumes that plane cross-sections remain plane and normal to the deflected axis. With Hooke\'s law this makes the bending moment proportional to curvature, the constant being the flexural rigidity EI. Combined with equilibrium of a beam element, the deflection satisfies a fourth-order differential equation that can be integrated in closed form for common loads and supports.',
    'Because the theory is linear, the effects of several loads add. Shear deformation, which the theory ignores, becomes noticeable only for short, deep beams and can be added with Timoshenko\'s correction.',
  ],
  phenomena: ['Elastic bending', 'Shear force and bending-moment equilibrium', 'Superposition of load effects', 'Shear deformation in deep beams', 'Flexural vibration'],
  laws: ['hooke', 'newton2', 'newton3'],
  refs: ['Gere, J. M. & Timoshenko, S. P. (1997). Mechanics of Materials, 4th ed. PWS Publishing.', 'Young, W. C., Budynas, R. G. & Sadegh, A. M. (2012). Roark\'s Formulas for Stress and Strain, 8th ed. McGraw-Hill.', 'Timoshenko, S. P. (1921). On the correction for shear of the differential equation for transverse vibrations of prismatic bars. Philosophical Magazine 41, 744–746.', 'Blevins, R. D. (1979). Formulas for Natural Frequency and Mode Shape. Van Nostrand Reinhold.'],
  inputs: [
    inp('L', 'Span (or cantilever length)', 'm', 6, { min: 0.2, max: 100, kind: 'geometry', aliases: ['span', 'length', 'long'] }),
    inp('E', 'Young\'s modulus', 'GPa', 210, { min: 1, max: 450, kind: 'geometry', aliases: ['young\'s modulus', 'elastic modulus', 'modulus'], src: 'Structural steel' }),
    inp('I_b', 'Second moment of area', 'cm^4', 8356, { min: 1, max: 1e7, kind: 'geometry', aliases: ['second moment of area', 'moment of inertia', 'inertia'], src: 'IPE 300 about its major axis' }),
    inp('c_y', 'Distance from the neutral axis to the extreme fibre', 'mm', 150, { min: 5, max: 2000, kind: 'geometry', aliases: ['extreme fibre', 'half depth'] }),
    inp('m_l', 'Mass per unit length of the beam', 'kg/m', 42.2, { min: 0.1, max: 5000, kind: 'geometry', aliases: ['mass per metre', 'mass per unit length', 'self weight'], src: 'IPE 300' }),
    inp('w', 'Uniformly distributed load', 'kN/m', 10, { min: 0, max: 1000, aliases: ['udl', 'distributed load', 'uniform load'] }),
    inp('P', 'Point load', 'kN', 20, { min: 0, max: 5000, aliases: ['point load', 'concentrated load'] }),
    inp('a_P', 'Position of the point load as a fraction of the span (from the left support or fixed end)', '1', 0.5, { min: 0.02, max: 1, kind: 'geometry', aliases: ['load position', 'position'] }),
    inp('sigma_y', 'Yield strength', 'MPa', 355, { min: 50, max: 2000, kind: 'geometry', aliases: ['yield strength', 'yield stress', 'yield'] }),
    inp('A_v', 'Shear area', 'cm^2', 25.7, { min: 0.5, max: 5000, kind: 'geometry', aliases: ['shear area'], src: 'IPE 300' }),
    inp('nu_p', 'Poisson\'s ratio', '1', 0.3, { min: 0, max: 0.5, kind: 'geometry', aliases: ['poisson'] }),
  ],
  assumptions: [
    asm('simply', 'The beam is simply supported at both ends.', { why: 'Most common idealisation', alt: 'The beam is a cantilever, fixed at the left end and free at the right.' }),
    asm('euler', 'Shear deformation is neglected (Euler–Bernoulli theory).', { why: 'Slender beam', alt: 'Timoshenko\'s shear deflection, V/(G·A_v) per unit length, is added.' }),
    asm('no_self', 'The self-weight of the beam is neglected.', { why: 'Small against the applied load, or already included in it', alt: 'Self-weight m·g is added to the distributed load.' }),
  ],
  symbols: { v_d: ['Deflection', 'm'], v_s: ['Shear deflection', 'm'], x: ['Distance along the beam', 'm'], w_t: ['Total distributed load', 'N/m'], M_b: ['Bending moment', 'N m'], V_s: ['Shear force', 'N'], M_max: ['Largest bending moment', 'N m'], sigma_max: ['Largest bending stress', 'Pa'], delta_w: ['Deflection due to the distributed load', 'm'], delta_P: ['Deflection due to a central or tip point load', 'm'], f_1: ['First natural frequency', '1/s'], G_s: ['Shear modulus', 'Pa'] },
  equations: a => [
    a.no_self ? eq('wt', 'Distributed load', 'w_t', 'w', { kind: 'definition', needs: ['no_self'] }) : eq('wt', 'Distributed load with self-weight', 'w_t', 'w + m_l*g', { kind: 'definition' }),
    eq('eb', 'Euler–Bernoulli beam equation', 'E*I_b*pd2(pd2(v_d,x),x)', 'w_t', { kind: 'law', origin: 'Equilibrium of a beam element with moment proportional to curvature' }),
    eq('mk', 'Moment–curvature relation', 'M_b', '-E*I_b*pd2(v_d,x)', { kind: 'law', origin: 'Hooke\'s law with plane sections remaining plane' }),
    eq('vm', 'Shear force', 'V_s', 'pd(M_b,x)', { kind: 'law', origin: 'Moment equilibrium of a beam element' }),
    ...(a.euler ? [] : [eq('gs', 'Shear modulus', 'G_s', 'E/(2*(1 + nu_p))', { kind: 'definition' }), eq('sh', 'Shear deflection', 'pd(v_s,x)', 'V_s/(G_s*A_v)', { kind: 'law', origin: 'Timoshenko (1921)' })]),
    a.simply
      ? eq('dw', 'Mid-span deflection under uniform load', 'delta_w', '5*w_t*L^4/(384*E*I_b)', { kind: 'derived', origin: 'Integration of the beam equation with pinned ends', needs: ['simply'] })
      : eq('dw', 'Tip deflection under uniform load', 'delta_w', 'w_t*L^4/(8*E*I_b)', { kind: 'derived', origin: 'Integration of the beam equation with one end fixed' }),
    a.simply
      ? eq('dp', 'Mid-span deflection under a central point load', 'delta_P', 'P*L^3/(48*E*I_b)', { kind: 'derived', origin: 'Integration of the beam equation with pinned ends', needs: ['simply'] })
      : eq('dp', 'Tip deflection under a tip point load', 'delta_P', 'P*L^3/(3*E*I_b)', { kind: 'derived', origin: 'Integration of the beam equation with one end fixed' }),
    eq('sig', 'Bending stress', 'sigma_max', 'M_max*c_y/I_b', { kind: 'derived', origin: 'Linear strain distribution over the depth' }),
    a.simply
      ? eq('f1', 'First natural frequency', 'f_1', 'pi/(2*L^2)*sqrt(E*I_b/m_l)', { kind: 'derived', origin: 'Free vibration of a pinned–pinned beam', needs: ['simply'] })
      : eq('f1', 'First natural frequency', 'f_1', '1.8751040687^2/(2*pi*L^2)*sqrt(E*I_b/m_l)', { kind: 'derived', origin: 'Free vibration of a cantilever; 1.8751 is the first root of cos λ·cosh λ = −1' }),
  ],
  derivation: a => [
    { text: 'Vertical and moment equilibrium of an element of length dx relate load, shear force and bending moment.', tex: '\\frac{\\mathrm{d}V}{\\mathrm{d}x} = -w,\\qquad \\frac{\\mathrm{d}M}{\\mathrm{d}x} = V' },
    { text: 'If plane sections remain plane, the axial strain varies linearly through the depth and Hooke\'s law gives a moment proportional to curvature.', tex: 'M = -EI\\,\\frac{\\mathrm{d}^2 v}{\\mathrm{d}x^2},\\qquad \\sigma = \\frac{M\\,y}{I}' },
    { text: 'Eliminating M and V gives the beam equation, which is integrated four times with the support conditions.', tex: 'EI\\,\\frac{\\mathrm{d}^4 v}{\\mathrm{d}x^4} = w' },
    { text: a.simply ? 'For pinned ends (zero deflection and moment) the standard results follow.' : 'For a fixed end (zero deflection and slope) and a free end (zero moment and shear) the standard results follow.', tex: a.simply ? '\\delta_w = \\frac{5 w L^4}{384\\,EI},\\qquad \\delta_P = \\frac{P L^3}{48\\,EI}' : '\\delta_w = \\frac{w L^4}{8\\,EI},\\qquad \\delta_P = \\frac{P L^3}{3\\,EI}' },
  ],
  solve(v, a) {
    const r = beamRun(v, a), sig = r.Mmax * v.c_y / v.I_b, warnings = [];
    if (sig > v.sigma_y) warnings.push('The peak bending stress exceeds the yield strength: the elastic solution no longer applies.');
    if (r.dmax > v.L / 10) warnings.push('The deflection exceeds a tenth of the span: small-deflection theory is not valid.');
    if (v.L / (2 * v.c_y) < 10 && a.euler) warnings.push('Span-to-depth ratio is below about 10: shear deformation may be significant. Consider switching off the Euler–Bernoulli assumption.');
    const mm = r.def.map(q => q * 1e3);
    return {
      scalars: [
        scalar('delta_max', 'Maximum deflection', r.dmax, 'm', { show: 'mm' }), scalar('x_d', 'Position of maximum deflection', r.xD, 'm'),
        scalar('span_ratio', 'Span over deflection', r.dmax > 0 ? v.L / r.dmax : NaN, '1', { text: r.dmax > 0 ? undefined : 'No deflection' }),
        scalar('theta_max', 'Maximum slope', r.thMax, 'rad', { show: 'deg' }),
        scalar('M_max', 'Largest bending moment', r.Mmax, 'N m', { show: 'kN m' }), scalar('V_max', 'Largest shear force', r.Vmax, 'N', { show: 'kN' }),
        scalar('R_A', a.simply ? 'Left reaction' : 'Reaction at the fixed end', r.RA, 'N', { show: 'kN' }), scalar('R_B', 'Right reaction', r.RB, 'N', { show: 'kN', note: a.simply ? undefined : 'free end' }),
        scalar('sigma_max', 'Largest bending stress', sig, 'Pa', { show: 'MPa' }), scalar('util', 'Stress utilisation against yield', sig / v.sigma_y, '1'),
        scalar('f_1', 'First natural frequency (beam mass only)', r.f1, '1/s', { show: 'Hz' }), scalar('EI', 'Flexural rigidity', r.EI, 'N m^2'),
      ],
      series: [
        line('deflection', 'Deflected shape', 'Position', 'm', r.x, [{ label: 'Deflection (downward positive)', data: mm }], 'Deflection', 'mm'),
        line('moment', 'Bending-moment diagram', 'Position', 'm', r.x, [{ label: 'Bending moment (sagging positive)', data: r.M.map(q => q / 1e3) }], 'Moment', 'kN m'),
        line('shear', 'Shear-force diagram', 'Position', 'm', r.x, [{ label: 'Shear force', data: r.V.map(q => q / 1e3) }], 'Shear', 'kN'),
        line('slope', 'Slope', 'Position', 'm', r.x, [{ label: 'Slope', data: r.th.map(q => q * 1e3) }], 'Slope', 'mrad'),
      ],
      checks: [
        check('Moment–curvature consistency', r.res, 2e-2, 'EI·v″ + M by finite differences, relative to the peak moment'),
        check('Vertical equilibrium', (r.RA + r.RB - r.wt * v.L - v.P) / Math.max(r.wt * v.L + v.P, 1), 1e-12, 'Reactions against total load'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const EI = v.E * v.I_b, L = v.L, ss = { ...a, simply: true, euler: true, no_self: true }, cl = { ...ss, simply: false };
    const w = Math.max(v.w, 1e3), P = Math.max(v.P, 1e3);
    return [
      bench('Simply supported, uniform load: δ = 5wL⁴/(384EI)', beamRun({ ...v, w, P: 0 }, ss).dmax, 5 * w * L ** 4 / (384 * EI), 'Gere & Timoshenko, Mechanics of Materials', 1e-10),
      bench('Simply supported, central point load: δ = PL³/(48EI)', beamRun({ ...v, w: 0, P, a_P: 0.5 }, ss).dmax, P * L ** 3 / (48 * EI), 'Gere & Timoshenko, Mechanics of Materials', 1e-10),
      bench('Cantilever, uniform load: δ = wL⁴/(8EI)', beamRun({ ...v, w, P: 0 }, cl).dmax, w * L ** 4 / (8 * EI), 'Gere & Timoshenko, Mechanics of Materials', 1e-10),
      bench('Cantilever, tip point load: δ = PL³/(3EI)', beamRun({ ...v, w: 0, P, a_P: 1 }, cl).dmax, P * L ** 3 / (3 * EI), 'Gere & Timoshenko, Mechanics of Materials', 1e-10),
      bench('Simply supported, uniform load: M = wL²/8', beamRun({ ...v, w, P: 0 }, ss).Mmax, w * L * L / 8, 'Statics', 1e-10),
    ];
  },
  validation: [],
  diagram(v, a) {
    const xa = 80, xb = 560, y = 170, xp = xa + (xb - xa) * v.a_P;
    const shape = Array.from({ length: 41 }, (_, i) => { const s = i / 40; return [xa + (xb - xa) * s, y + 4 + (a.simply ? 34 * Math.sin(Math.PI * s) : 44 * s * s * (3 - s) / 2)]; });
    return svg(`
      ${S.rect(xa, y - 8, xb - xa, 16, 'd-body', 2)} ${S.poly(shape, 'd-dim')}
      ${a.simply ? `${S.path(`M${xa - 14} ${y + 34} l14 -26 l14 26 z`, 'd-body')} ${S.path(`M${xb - 14} ${y + 34} l14 -26 l14 26 z`, 'd-body')} ${S.circle(xb - 7, y + 40, 5)} ${S.circle(xb + 7, y + 40, 5)}` : `${S.rect(xa - 30, y - 60, 30, 120, 'd-ground', 0)} ${S.line(xa, y - 60, xa, y + 60, 'd-line')}`}
      ${Array.from({ length: 13 }, (_, i) => S.arrow(xa + (xb - xa) * i / 12, y - 50, xa + (xb - xa) * i / 12, y - 12)).join('')} ${S.line(xa, y - 50, xb, y - 50, 'd-line')}
      ${S.text((xa + xb) / 2, y - 60, `w = ${lab(v.w / 1e3, 'kN/m')}`)}
      ${S.arrow(xp, y - 120, xp, y - 54, 'd-arrow d-hazard')} ${S.text(xp + 8, y - 104, `P = ${lab(v.P / 1e3, 'kN')}`, 'd-text', 'start')}
      ${S.dim(xa, y + 90, xb, y + 90, `L = ${lab(v.L, 'm')}`)}
      ${S.text(320, 320, `E = ${lab(v.E / 1e9, 'GPa')}   I = ${lab(v.I_b * 1e8, 'cm⁴')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the load–deflection response of a beam and determine its flexural rigidity and Young\'s modulus.',
    apparatus: ['Beam of uniform section on knife-edge or roller supports (or clamped at one end)', 'Loading hanger and calibrated weights, or a test machine with a load spreader', 'Rigid reference frame'],
    instruments: [{ name: 'Dial gauge or displacement transducer at mid-span', measures: 'Deflection', range: '0–25 mm', resolution: '±0.01 mm' }, { name: 'Strain gauges on top and bottom fibres', measures: 'Bending strain', range: '±2000 µε', resolution: '±1 µε' }, { name: 'Load cell', measures: 'Applied load', range: '0–10 kN', resolution: '±0.2 %' }],
    procedure: ['Measure the section dimensions and span.', 'Apply load in at least eight increments within the elastic range, recording deflection and strain; unload and check for return to zero.', 'Fit a straight line to load against deflection; its slope gives EI through the appropriate deflection formula.'],
    controls: ['Measure support settlement with a second gauge and subtract it', 'Repeat with the load at a different position to verify superposition'],
    signatures: ['Deflection proportional to load and to the cube of span for a point load', 'Equal and opposite strains at the top and bottom fibres of a symmetric section'],
    safety: ['Keep feet clear of hanging weights', 'Do not exceed the elastic limit of brittle specimens'],
  },
  falsify: ['Deflection that is not proportional to load within the elastic range.', 'A strain distribution through the depth that is not linear for a slender beam of homogeneous material.'],
  alternatives: [{ name: 'Timoshenko beam theory', text: 'Adds shear deformation and rotary inertia; needed for deep beams, sandwich sections and higher vibration modes.' }, { name: 'Large-deflection (elastica) theory', text: 'Uses exact curvature; needed when deflection is a sizeable fraction of the span.' }, { name: 'Plastic analysis', text: 'Beyond first yield a plastic hinge forms and collapse load is found from mechanisms.' }],
  hazards: [{ hazard: 'Excessive deflection or yielding', cause: 'Overload or an under-sized section', mitigation: 'Serviceability and strength checks with appropriate load factors' }, { hazard: 'Lateral–torsional buckling', cause: 'Unrestrained compression flange of a slender open section', mitigation: 'Lateral restraint; buckling check, which this model does not perform' }],
  standards: ['EN 1993-1-1 (Eurocode 3: design of steel structures)', 'AISC 360 (specification for structural steel buildings)', 'EN 1990 (basis of structural design)'],
  limits: 'Straight, prismatic, linearly elastic beam with small deflections, loaded in a principal plane. Lateral–torsional buckling, local buckling, plasticity and dynamic amplification are not assessed. The natural frequency uses the beam mass only.',
  numerics: { method: 'Closed-form superposition evaluated at 201 stations; finite-difference check of the moment–curvature relation' },
  optimise: { objective: 'delta_max', sense: 'min', vars: ['I_b'], note: 'Deflection is inversely proportional to the second moment of area; weight and cost grow with it.' },
  inverse: { series: 'deflection', fit: ['E'] },
  extensions: ['Other support conditions and multiple spans', 'Moving and dynamic loads', 'Lateral–torsional buckling check'],
};

// ------------------------------------------------------------------ column buckling
function columnRun(v, a, P = v.P) {
  const r = Math.sqrt(v.I_b / v.A), Le = v.K * v.L, lam = Le / r, PE = Math.PI ** 2 * v.E * v.I_b / (Le * Le), sE = PE / v.A, sy = v.sigma_y;
  const lamC = Math.PI * Math.sqrt(2 * v.E / sy), eta = a.imperfect ? v.e_0 * v.c_y / (r * r) : 0;
  const sCr = l => { const e = Math.PI ** 2 * v.E / (l * l); return a.johnson ? (l < lamC ? sy * (1 - sy * l * l / (4 * Math.PI ** 2 * v.E)) : e) : Math.min(sy, e); };
  const sPR = (e, h) => { const b = 0.5 * (sy + (1 + h) * e); return b - Math.sqrt(Math.max(b * b - sy * e, 0)); };
  const sec = p => 1 / Math.cos(Math.PI / 2 * Math.sqrt(Math.min(p / PE, 1 - 1e-12)));
  const defl = p => (!a.imperfect ? 0 : a.bow ? v.e_0 / (1 - p / PE) : v.e_0 * (sec(p) - 1));
  const sMax = p => (!a.imperfect ? p / v.A : a.bow ? p / v.A + p * defl(p) * v.c_y / v.I_b : p / v.A * (1 + eta * sec(p)));
  let Py = Math.min(PE, sy * v.A);
  if (a.imperfect && eta > 0) {
    if (a.bow) Py = sPR(sE, eta) * v.A;
    else { const f = p => sMax(p) - sy, hi = PE * (1 - 1e-10); Py = f(hi) > 0 ? N.bisect(f, 0, hi, 1e-12) : hi; }
  }
  const Pcr = sCr(lam) * v.A, Pfail = Math.min(Pcr, Py), over = P >= PE;
  return { r, Le, lam, PE, sE, lamC, eta, Pcr, Py, Pfail, over, delta: over ? NaN : defl(P), sig: over ? NaN : sMax(P), sCr, sPR, defl, sMax };
}
const columnBuckling = {
  id: 'column-buckling',
  title: 'Column buckling: Euler, Johnson and imperfect columns',
  module: 2, klass: 'I', domains: ['structural', 'mechanical'],
  keywords: ['column buckling', 'euler buckling', 'buckling', 'critical load', 'slenderness ratio', 'effective length', 'johnson parabola', 'perry-robertson', 'secant formula', 'strut', 'column', 'compression member', 'initial imperfection', 'buckling load'],
  summary: 'Elastic critical load of a column with an effective-length factor, the Johnson parabola for intermediate slenderness, and the amplified deflection and first-yield load of a column with an initial bow or an eccentric load.',
  background: [
    'A perfectly straight elastic column under axial load remains straight until the load reaches a critical value at which a bent equilibrium shape becomes possible. Euler found this load for a pin-ended column; other end conditions are handled with an effective length. For stocky columns the Euler stress exceeds the yield strength and failure is by inelastic buckling or squashing, which the Johnson parabola interpolates empirically.',
    'Real columns are never perfect. An initial bow or an eccentricity of the load causes bending from the start, and the lateral deflection is amplified as the load approaches the Euler value. Setting the peak fibre stress equal to yield gives the Perry–Robertson formula for a bowed column and the secant formula for an eccentric load; these underlie modern design curves.',
  ],
  phenomena: ['Bifurcation of equilibrium', 'Amplification of imperfections', 'Combined axial and bending stress', 'Inelastic buckling of stocky columns'],
  laws: ['hooke', 'newton2'],
  refs: ['Timoshenko, S. P. & Gere, J. M. (1961). Theory of Elastic Stability, 2nd ed. McGraw-Hill.', 'Ayrton, W. E. & Perry, J. (1886). On struts. The Engineer 62, 464–465, 513–515.', 'Robertson, A. (1925). The strength of struts. Institution of Civil Engineers, Selected Engineering Papers 28.', 'Budynas, R. G. & Nisbett, J. K. (2015). Shigley\'s Mechanical Engineering Design, 10th ed. McGraw-Hill.', 'Galambos, T. V. & Surovek, A. E. (2008). Structural Stability of Steel: Concepts and Applications for Structural Engineers. Wiley.'],
  inputs: [
    inp('L', 'Column length', 'm', 3, { min: 0.2, max: 30, kind: 'geometry', aliases: ['length', 'height', 'long', 'tall'] }),
    inp('K', 'Effective-length factor', '1', 1.0, { min: 0.5, max: 2.1, kind: 'geometry', aliases: ['effective length factor', 'k factor'], src: 'Theoretical values: 0.5 fixed–fixed, 0.7 fixed–pinned, 1.0 pinned–pinned, 2.0 fixed–free' }),
    inp('E', 'Young\'s modulus', 'GPa', 210, { min: 1, max: 450, kind: 'geometry', aliases: ['young\'s modulus', 'elastic modulus', 'modulus'] }),
    inp('sigma_y', 'Yield strength', 'MPa', 355, { min: 50, max: 2000, kind: 'geometry', aliases: ['yield strength', 'yield stress', 'yield'] }),
    inp('A', 'Cross-sectional area', 'cm^2', 53.8, { min: 0.5, max: 5000, kind: 'geometry', aliases: ['area', 'cross-sectional area'], src: 'IPE 300' }),
    inp('I_b', 'Second moment of area about the buckling axis', 'cm^4', 604, { min: 0.01, max: 1e7, kind: 'geometry', aliases: ['second moment of area', 'moment of inertia', 'inertia'], src: 'IPE 300 about its minor axis' }),
    inp('c_y', 'Distance from the centroid to the extreme fibre', 'mm', 75, { min: 2, max: 1000, kind: 'geometry', aliases: ['extreme fibre'] }),
    inp('e_0', 'Initial bow amplitude or load eccentricity', 'mm', 3, { min: 0, max: 100, kind: 'geometry', aliases: ['imperfection', 'initial bow', 'eccentricity', 'out-of-straightness'], src: 'L/1000 is a common fabrication tolerance' }),
    inp('P', 'Applied axial load', 'kN', 400, { min: 1, max: 100000, aliases: ['axial load', 'load', 'compression'] }),
  ],
  assumptions: [
    asm('johnson', 'Below the transition slenderness the critical stress follows the Johnson parabola.', { why: 'Empirical allowance for inelastic buckling', alt: 'The Euler hyperbola is simply capped at the yield strength.' }),
    asm('imperfect', 'The column has an initial geometric imperfection of the stated size.', { why: 'All real columns are imperfect', alt: 'The column is perfectly straight and concentrically loaded: it stays straight up to the critical load.' }),
    asm('bow', 'The imperfection is a half-sine initial bow.', { why: 'Basis of the Perry–Robertson formula', alt: 'The imperfection is an equal load eccentricity at both ends (secant formula).' }),
  ],
  symbols: { r_g: ['Radius of gyration', 'm'], lambda: ['Slenderness ratio', '1'], lambda_c: ['Transition slenderness', '1'], P_E: ['Euler critical load', 'N'], sigma_cr: ['Critical stress', 'Pa'], delta: ['Lateral deflection at mid-height', 'm'], sigma_max: ['Peak compressive stress', 'Pa'] },
  equations: a => [
    eq('rg', 'Radius of gyration', 'r_g', 'sqrt(I_b/A)', { kind: 'definition' }),
    eq('lam', 'Slenderness ratio', 'lambda', 'K*L/r_g', { kind: 'definition' }),
    eq('pe', 'Euler critical load', 'P_E', 'pi^2*E*I_b/(K*L)^2', { kind: 'law', origin: 'Bifurcation of the elastic beam–column equation; Euler (1744)' }),
    eq('lc', 'Transition slenderness', 'lambda_c', 'pi*sqrt(2*E/sigma_y)', { kind: 'derived', origin: 'Tangency of the Johnson parabola and the Euler hyperbola at half the yield strength' }),
    a.johnson
      ? eq('scr', 'Johnson parabola (λ < λ_c)', 'sigma_cr', 'sigma_y*(1 - sigma_y*lambda^2/(4*pi^2*E))', { kind: 'empirical', origin: 'J. B. Johnson\'s parabolic column formula', needs: ['johnson'], note: 'Applies below the transition slenderness; for λ ≥ λ_c the solver uses the Euler stress π²E/λ².' })
      : eq('scr', 'Critical stress', 'sigma_cr', 'min(sigma_y, pi^2*E/lambda^2)', { kind: 'closure', origin: 'Euler stress limited by yield' }),
    ...(a.imperfect ? [
      a.bow
        ? eq('dl', 'Amplified bow', 'delta', 'e_0/(1 - P/P_E)', { kind: 'derived', origin: 'Beam–column equation with a sinusoidal initial bow', needs: ['imperfect', 'bow'] })
        : eq('dl', 'Deflection under eccentric load', 'delta', 'e_0*(1/cos(pi/2*sqrt(P/P_E)) - 1)', { kind: 'derived', origin: 'Beam–column equation with equal end eccentricities', needs: ['imperfect'] }),
      a.bow
        ? eq('sm', 'Peak stress', 'sigma_max', 'P/A + P*delta*c_y/I_b', { kind: 'derived', origin: 'Axial plus bending stress at mid-height' })
        : eq('sm', 'Secant formula', 'sigma_max', 'P/A*(1 + e_0*c_y/r_g^2/cos(pi/2*sqrt(P/P_E)))', { kind: 'derived', origin: 'Axial plus bending stress at mid-height' }),
    ] : [eq('sm', 'Axial stress', 'sigma_max', 'P/A', { kind: 'definition' })]),
  ],
  derivation: a => [
    { text: 'For a pin-ended column in a slightly bent position the bending moment at any section is the load times the deflection. With the moment–curvature relation this gives a linear equation whose non-trivial solutions exist only at discrete loads; the lowest is the Euler load.', tex: 'EI\\,v\'\' + P\\,v = 0\\ \\Rightarrow\\ P_E = \\frac{\\pi^2 EI}{(KL)^2},\\qquad \\sigma_E = \\frac{\\pi^2 E}{\\lambda^2}' },
    { text: 'The Johnson parabola starts at the yield strength for zero slenderness and meets the Euler curve tangentially where the critical stress is half the yield strength.', tex: '\\sigma_{cr} = \\sigma_y\\left[1 - \\frac{\\sigma_y\\lambda^2}{4\\pi^2 E}\\right],\\qquad \\lambda_c = \\pi\\sqrt{\\frac{2E}{\\sigma_y}}' },
    { text: a.bow ? 'With an initial bow e₀ sin(πx/L) the same equation has a forcing term and the mid-height deflection is the initial bow divided by (1 − P/P_E).' : 'With the load applied at an eccentricity e the moment includes P·e and the mid-height deflection follows a secant law.', tex: a.bow ? '\\delta = \\frac{e_0}{1 - P/P_E}' : '\\delta = e\\left[\\sec\\!\\left(\\frac{\\pi}{2}\\sqrt{\\frac{P}{P_E}}\\right) - 1\\right]' },
    { text: 'First yield occurs when axial plus bending stress at the concave fibre reaches the yield strength. For the bowed column this gives the Perry–Robertson quadratic with imperfection parameter η = e₀c/r².', tex: '(\\sigma_y - \\sigma)(\\sigma_E - \\sigma) = \\eta\\,\\sigma_E\\,\\sigma' },
  ],
  solve(v, a) {
    const r = columnRun(v, a), warnings = [];
    if (r.over) warnings.push('The applied load is at or above the Euler load: no stable equilibrium exists.');
    else if (v.P > r.Pfail) warnings.push('The applied load exceeds the predicted failure load.');
    if (r.lam > 200) warnings.push('Slenderness exceeds 200, beyond the range usually permitted for main compression members.');
    const Ps = N.linspace(0, 0.98 * r.PE, 80), ls = N.linspace(5, 250, 99), eta = v.e_0 * v.c_y / (r.r * r.r);
    const cap = 1.5 * v.sigma_y / 1e6;
    return {
      scalars: [
        scalar('r_g', 'Radius of gyration', r.r, 'm', { show: 'mm' }), scalar('lambda', 'Slenderness ratio', r.lam, '1', { note: r.lam < r.lamC ? 'intermediate or stocky column' : 'slender (Euler) column' }), scalar('lambda_c', 'Transition slenderness', r.lamC, '1'),
        scalar('P_E', 'Euler critical load', r.PE, 'N', { show: 'kN' }), scalar('P_cr', a.johnson ? 'Critical load (Euler or Johnson)' : 'Critical load (Euler capped at yield)', r.Pcr, 'N', { show: 'kN' }),
        scalar('P_y', a.imperfect ? (a.bow ? 'First-yield load (Perry–Robertson)' : 'First-yield load (secant formula)') : 'Squash or Euler load', r.Py, 'N', { show: 'kN' }),
        scalar('P_fail', 'Governing failure load', r.Pfail, 'N', { show: 'kN' }), scalar('SF', 'Factor of safety on the applied load', r.Pfail / v.P, '1'),
        scalar('eta', 'Imperfection parameter e₀c/r²', r.eta, '1'),
        scalar('delta', 'Lateral deflection at mid-height under the applied load', r.delta, 'm', { show: 'mm', text: r.over ? 'Unbounded — load exceeds the Euler load' : undefined }),
        scalar('sigma_max', 'Peak compressive stress under the applied load', r.sig, 'Pa', { show: 'MPa', text: r.over ? 'Unbounded — load exceeds the Euler load' : undefined }),
      ],
      series: [
        line('load-deflection', 'Lateral deflection against axial load', 'Axial load', 'kN', Ps.map(p => p / 1e3), [{ label: 'Mid-height deflection', data: Ps.map(p => r.defl(p) * 1e3) }], 'Deflection', 'mm', { note: 'The deflection grows without limit as the load approaches the Euler load.' }),
        line('column-curve', 'Column strength curves', 'Slenderness ratio', '–', ls, [{ label: a.johnson ? 'Euler / Johnson' : 'Euler capped at yield', data: ls.map(l => r.sCr(l) / 1e6) }, { label: 'Euler hyperbola', data: ls.map(l => Math.min(Math.PI ** 2 * v.E / (l * l) / 1e6, cap)), dash: true }, { label: 'Perry–Robertson (first yield, this imperfection)', data: ls.map(l => r.sPR(Math.PI ** 2 * v.E / (l * l), eta) / 1e6), dash: true }], 'Stress', 'MPa', { points: [{ x: r.lam, y: v.P / v.A / 1e6 }], pointsLabel: 'Applied load' }),
      ],
      checks: [check('First-yield load reproduces the yield stress', a.imperfect && r.eta > 0 && r.Py < r.PE * (1 - 1e-9) ? (r.sMax(r.Py) - v.sigma_y) / v.sigma_y : 0, 1e-6, 'Peak stress at the first-yield load against yield strength')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b0 = { ...a, johnson: true, imperfect: true, bow: true }, r = columnRun({ ...v, K: 1 }, b0), out = [];
    out.push(bench('Euler load of a pin-ended column', r.PE, Math.PI ** 2 * v.E * v.I_b / v.L ** 2, 'P_E = π²EI/L²', 1e-12));
    out.push(bench('Johnson parabola meets the Euler curve at λ_c', r.sCr(r.lamC * (1 - 1e-9)), v.sigma_y / 2, 'Both equal σ_y/2 at the transition slenderness', 1e-6));
    out.push(bench('Perry–Robertson with no imperfection', r.sPR(r.sE, 0), Math.min(v.sigma_y, r.sE), 'Reduces to the lower of yield and Euler stress', 1e-9));
    const p = 0.5 * r.PE, rs = columnRun({ ...v, K: 1 }, { ...b0, bow: false });
    out.push(bench('Amplification of an initial bow at P = P_E/2', r.defl(p) / v.e_0 || 2, 2, 'δ/e₀ = 1/(1 − P/P_E)', 1e-12));
    out.push(bench('Secant deflection at P = P_E/2', rs.defl(p) / v.e_0 || 1 / Math.cos(Math.PI / 2 * Math.SQRT1_2) - 1, 1 / Math.cos(Math.PI / 2 * Math.SQRT1_2) - 1, 'δ/e = sec((π/2)√(P/P_E)) − 1', 1e-10));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const pts = Array.from({ length: 31 }, (_, i) => [320 + (a.imperfect ? 36 : 0) * Math.sin(Math.PI * i / 30), 70 + i * 7.4]);
    return svg(`
      ${S.path('M270 300 L370 300', 'd-ground')} ${S.path('M306 300 l14 -8 l14 8 z', 'd-body')}
      ${S.line(320, 70, 320, 292, 'd-dim')} ${S.poly(pts, 'd-pipe')}
      ${S.path('M306 62 l14 8 l14 -8 z', 'd-body')}
      ${S.arrow(320, 14, 320, 58, 'd-arrow d-hazard')} ${S.text(332, 30, `P = ${lab(v.P / 1e3, 'kN')}`, 'd-text', 'start')}
      ${a.imperfect ? `${S.dim(320, 181, 356, 181, '')} ${S.text(366, 185, a.bow ? 'δ = e₀/(1 − P/P_E)' : 'δ (eccentric load)', 'd-text', 'start')}` : S.text(336, 185, 'straight until P_cr', 'd-text', 'start')}
      ${S.dim(230, 70, 230, 292, '')} ${S.text(222, 185, `L = ${lab(v.L, 'm')}`, 'd-text d-small', 'end')}
      ${S.text(320, 330, `K = ${lab(v.K)}   effective length ${lab(v.K * v.L, 'm')}`)}
      ${S.text(520, 110, `E = ${lab(v.E / 1e9, 'GPa')}`)} ${S.text(520, 130, `σ_y = ${lab(v.sigma_y / 1e6, 'MPa')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the load–lateral deflection curve of a pin-ended strut and determine its critical load by a Southwell plot.',
    apparatus: ['Slender strut of uniform section with knife-edge or ball end fittings', 'Compression test machine or screw jack with a load cell', 'Lateral guides to prevent sudden collapse'],
    instruments: [{ name: 'Load cell', measures: 'Axial load', range: '0–50 kN', resolution: '±0.2 %' }, { name: 'Displacement transducer at mid-height', measures: 'Lateral deflection', range: '±25 mm', resolution: '±0.01 mm' }, { name: 'Straight edge and feeler gauges', measures: 'Initial bow', range: '0–5 mm', resolution: '±0.05 mm' }],
    procedure: ['Measure the section, length and initial out-of-straightness.', 'Increase the load in small steps, recording lateral deflection, to about 80 % of the expected critical load.', 'Plot deflection divided by load against deflection (Southwell plot): the inverse slope is the critical load and the intercept gives the equivalent initial bow.', 'Repeat for several lengths to trace the column curve.'],
    controls: ['Tension test on the same material for E and yield strength', 'Rotate the strut to check for a preferred bow direction'],
    signatures: ['Critical load proportional to 1/L² for slender struts', 'A straight Southwell plot', 'Failure stress approaching yield for stocky struts'],
    safety: ['Guard against sudden lateral buckling and stored energy release', 'Eye protection'],
  },
  falsify: ['A critical load of slender pin-ended struts that does not vary as the inverse square of length.', 'A Southwell plot that is not linear for an elastic strut with a single-curvature imperfection.'],
  alternatives: [{ name: 'Tangent-modulus and reduced-modulus theories', text: 'Engesser and Shanley treat inelastic buckling using the slope of the stress–strain curve instead of an empirical parabola.' }, { name: 'Code column curves', text: 'Design standards use families of Perry–Robertson-type curves calibrated to tests, with imperfection factors that depend on section type and residual stress.' }, { name: 'Geometrically nonlinear finite-element analysis', text: 'Handles local buckling, residual stress and frame interaction.' }],
  hazards: [{ hazard: 'Sudden collapse', cause: 'Buckling gives little warning in slender members', mitigation: 'Adequate safety factors, bracing to reduce effective length' }, { hazard: 'Unconservative effective length', cause: 'Assuming more end fixity than the connections provide', mitigation: 'Use recommended design values of K rather than theoretical ones' }],
  standards: ['EN 1993-1-1 (Eurocode 3: design of steel structures)', 'AISC 360 (specification for structural steel buildings)', 'API RP 2A-WSD (tubular members of fixed offshore platforms)'],
  limits: 'Prismatic column of homogeneous elastic–perfectly-plastic material buckling in one plane. Local and torsional buckling, residual stress, frame action and post-buckling behaviour are not included. First yield is a lower bound on the strength of an imperfect column.',
  numerics: { method: 'Closed-form expressions; bisection for the first-yield load of the secant formula' },
  optimise: { objective: 'P_fail', sense: 'max', vars: ['K'], note: 'Bracing or end fixity that halves the effective length quadruples the Euler load.' },
  inverse: { series: 'load-deflection', fit: ['e_0'] },
  extensions: ['Beam–columns with lateral load and end moments', 'Tangent-modulus inelastic buckling', 'Design column curves with section-dependent imperfection factors'],
};

// ------------------------------------------------------------------ shear building under ground motion
/** Exact response of a damped linear oscillator to piecewise-linear forcing p (per unit mass); Nigam & Jennings (1969). */
function sdofResponse(om, zeta, p, dt) {
  const n = p.length, u = new Float64Array(n), k = om * om, z = Math.min(zeta, 0.999), s1 = Math.sqrt(1 - z * z), wd = om * s1;
  const e = Math.exp(-z * om * dt), sn = Math.sin(wd * dt), cs = Math.cos(wd * dt), zr = z / s1, tw = 2 * z / (om * dt);
  const A = e * (zr * sn + cs), B = e * sn / wd;
  const C = (tw + e * (((1 - 2 * z * z) / (wd * dt) - zr) * sn - (1 + tw) * cs)) / k, D = (1 - tw + e * ((2 * z * z - 1) / (wd * dt) * sn + tw * cs)) / k;
  const A1 = -e * om / s1 * sn, B1 = e * (cs - zr * sn);
  const C1 = (-1 / dt + e * ((om / s1 + zr / dt) * sn + cs / dt)) / k, D1 = (1 - e * (zr * sn + cs)) / (k * dt);
  let x = 0, w = 0;
  for (let i = 0; i < n - 1; i++) {
    const xn = A * x + B * w + C * p[i] + D * p[i + 1]; w = A1 * x + B1 * w + C1 * p[i] + D1 * p[i + 1]; x = xn; u[i + 1] = x;
  }
  return u;
}
function buildingModes(n, m, ks) {
  // solved in dimensionless form (stiffness over k₁, unit mass) so that the Jacobi iteration converges to its tolerance
  const k0 = ks[0], K = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 0; i < n; i++) { K[i][i] = (ks[i] + (i + 1 < n ? ks[i + 1] : 0)) / k0; if (i + 1 < n) { K[i][i + 1] = -ks[i + 1] / k0; K[i + 1][i] = -ks[i + 1] / k0; } }
  const eg = N.eigGen(K, N.identity(n)), sm = Math.sqrt(m), phi = eg.vectors.map(ph => ph.map(q => q / sm));
  return { om: eg.values.map(q => Math.sqrt(Math.max(q, 0) * k0 / m)), phi, gamma: phi.map(ph => ph.reduce((s, q) => s + q * m, 0)) };
}
const shearBuilding = {
  id: 'shear-building-seismic',
  title: 'Shear building under ground motion',
  module: 2, klass: 'I', domains: ['structural'],
  keywords: ['shear building', 'seismic response', 'earthquake', 'storey drift', 'story drift', 'ground motion', 'modal analysis', 'mode shapes', 'natural frequencies', 'base shear', 'multi-storey', 'multi-story', 'modal superposition', 'building vibration', 'storeys', 'floors'],
  summary: 'Natural frequencies and mode shapes of an N-storey shear building and its response to harmonic or pulse ground acceleration by modal superposition: roof displacement, storey drifts and base shear.',
  background: [
    'In the shear-building idealisation the floors are rigid and carry all the mass, the columns are inextensible and provide lateral stiffness, and each floor has a single horizontal degree of freedom. The equations of motion are then a set of coupled linear oscillators with a tridiagonal stiffness matrix.',
    'Free vibration is described by the generalised eigenproblem of stiffness and mass. Because the mode shapes are orthogonal with respect to both matrices, the response to ground acceleration separates into independent single-degree-of-freedom equations, one per mode, each excited in proportion to its participation factor. Storey drifts, which govern damage, follow from differences of the floor displacements.',
  ],
  phenomena: ['Multi-degree-of-freedom vibration', 'Modal orthogonality', 'Resonance with ground motion', 'Inertial loading from base acceleration', 'Viscous damping'],
  laws: ['newton2', 'hooke'],
  refs: ['Chopra, A. K. (2012). Dynamics of Structures: Theory and Applications to Earthquake Engineering, 4th ed. Prentice Hall.', 'Clough, R. W. & Penzien, J. (1993). Dynamics of Structures, 2nd ed. McGraw-Hill.', 'Nigam, N. C. & Jennings, P. C. (1969). Calculation of response spectra from strong-motion earthquake records. Bulletin of the Seismological Society of America 59, 909–922.'],
  inputs: [
    inp('n_s', 'Number of storeys', '1', 5, { min: 1, max: 12, kind: 'geometry', aliases: ['storeys', 'stories', 'floors', 'storey', 'story'] }),
    inp('m_s', 'Mass of each floor', 't', 50, { min: 1, max: 5000, kind: 'geometry', aliases: ['floor mass', 'storey mass', 'mass'] }),
    inp('k_s', 'Lateral stiffness of each storey', 'MN/m', 60, { min: 0.1, max: 10000, kind: 'geometry', aliases: ['storey stiffness', 'story stiffness', 'stiffness'] }),
    inp('h_s', 'Storey height', 'm', 3.2, { min: 2, max: 8, kind: 'geometry', aliases: ['storey height', 'story height'] }),
    inp('zeta', 'Damping ratio', '1', 0.05, { min: 0, max: 0.3, kind: 'geometry', aliases: ['damping ratio', 'damping'], src: 'Five per cent of critical is conventional for buildings' }),
    inp('a_g', 'Peak ground acceleration', 'g0', 0.3, { min: 0.01, max: 2, kind: 'environment', aliases: ['peak ground acceleration', 'pga', 'ground acceleration'] }),
    inp('f_g', 'Frequency of the ground motion', 'Hz', 2, { min: 0.1, max: 20, kind: 'environment', aliases: ['excitation frequency', 'ground motion frequency', 'frequency'] }),
    inp('t_d', 'Duration analysed', 's', 10, { min: 1, max: 60, kind: 'numerical' }),
  ],
  assumptions: [
    asm('harmonic', 'The ground acceleration is a sustained sinusoid.', { why: 'Shows resonance clearly', alt: 'The ground acceleration is a single half-sine pulse of duration 1/(2·f_g).' }),
    asm('uniform', 'All storeys have the same stiffness.', { why: 'Regular building', alt: 'Storey stiffness tapers linearly to half its base value at the top storey.' }),
    asm('modal_damp', 'Every mode has the same damping ratio.', { why: 'Conventional modal damping', alt: 'Damping is stiffness-proportional: the damping ratio grows in proportion to modal frequency from the stated value in the first mode.' }),
    asm('all_modes', 'All modes are included in the superposition.', { why: 'Complete solution of the linear model', alt: 'Only the fundamental mode is retained.' }),
  ],
  symbols: { K_m: ['Stiffness matrix entry', 'N/m'], M_m: ['Mass matrix entry', 'kg'], phi_n: ['Mode shape n', '1'], phi_1: ['Fundamental mode shape', '1'], omega_n: ['Natural angular frequency of mode n', '1/s'], omega_1: ['Fundamental angular frequency', '1/s'], k_i: ['Stiffness of storey i', 'N/m'], i_s: ['Storey index', '1'], Gamma_n: ['Modal participation factor', '1'], L_n: ['Modal excitation factor φᵀM1', 'kg'], M_n: ['Modal mass φᵀMφ', 'kg'], q_n: ['Modal coordinate', 'm'], q_1: ['Fundamental modal coordinate', 'm'], zeta_n: ['Damping ratio of mode n', '1'], a_gt: ['Ground acceleration', 'm/s^2'], t: ['Time', 's'], u_i: ['Displacement of floor i relative to the ground', 'm'], u_im: ['Displacement of the floor below', 'm'], Delta_i: ['Drift of storey i', 'm'], Delta_1: ['Drift of the first storey', 'm'], V_b: ['Base shear', 'N'] },
  equations: a => [
    eq('eig', 'Free-vibration eigenproblem', 'K_m*phi_n', 'omega_n^2*M_m*phi_n', { kind: 'law', origin: 'Newton\'s second law for undamped free vibration' }),
    a.uniform
      ? eq('w1', 'Fundamental frequency of a uniform shear building', 'omega_1', '2*sqrt(k_s/m_s)*sin(pi/(2*(2*n_s + 1)))', { kind: 'derived', origin: 'Closed-form eigenvalues of the uniform fixed–free spring–mass chain', needs: ['uniform'] })
      : eq('ki', 'Tapered storey stiffness', 'k_i', 'k_s*(1 - 0.5*(i_s - 1)/max(n_s - 1, 1))', { kind: 'closure', origin: 'Linear taper to half stiffness at the top' }),
    eq('gam', 'Participation factor', 'Gamma_n', 'L_n/M_n', { kind: 'definition' }),
    a.modal_damp ? eq('zn', 'Modal damping', 'zeta_n', 'zeta', { kind: 'closure', needs: ['modal_damp'] }) : eq('zn', 'Stiffness-proportional damping', 'zeta_n', 'zeta*omega_n/omega_1', { kind: 'closure', origin: 'Damping matrix proportional to the stiffness matrix' }),
    a.harmonic
      ? eq('ag', 'Ground acceleration', 'a_gt', 'a_g*sin(2*pi*f_g*t)', { kind: 'boundary', needs: ['harmonic'] })
      : eq('ag', 'Ground acceleration (half-sine pulse)', 'a_gt', 'a_g*sin(2*pi*f_g*t)*heaviside(1/(2*f_g) - t)', { kind: 'boundary' }),
    eq('modal', 'Modal equation of motion', 'd2(q_n,t) + 2*zeta_n*omega_n*d(q_n,t) + omega_n^2*q_n', '-Gamma_n*a_gt', { kind: 'law', origin: 'Projection of the equations of motion on mode n' }),
    a.all_modes
      ? eq('sup', 'Modal superposition (summed over all modes n)', 'u_i', 'phi_n*q_n', { kind: 'derived', origin: 'Expansion theorem', needs: ['all_modes'] })
      : eq('sup', 'Fundamental-mode response', 'u_i', 'phi_1*q_1', { kind: 'closure', origin: 'Truncation to one mode' }),
    eq('dr', 'Storey drift', 'Delta_i', 'u_i - u_im', { kind: 'definition' }),
    eq('vb', 'Base shear', 'V_b', 'k_s*Delta_1', { kind: 'law', origin: 'Shear carried by the first-storey columns' }),
  ],
  derivation: a => [
    { text: 'Each floor of mass m is acted on by the shear forces of the storeys above and below, which are proportional to the storey drifts, and by damping. In a frame moving with the ground the base acceleration appears as an inertia force on every floor.', tex: '\\mathbf{M}\\ddot{\\mathbf{u}} + \\mathbf{C}\\dot{\\mathbf{u}} + \\mathbf{K}\\mathbf{u} = -\\mathbf{M}\\mathbf{1}\\,a_g(t)' },
    { text: 'Seeking harmonic free vibration gives the generalised eigenproblem. Its eigenvectors are orthogonal with respect to M and K.' + (a.uniform ? ' For identical storeys the eigenvalues have a closed form.' : ''), tex: a.uniform ? '\\omega_j = 2\\sqrt{\\frac{k}{m}}\\,\\sin\\frac{(2j-1)\\pi}{2(2N+1)}' : '\\mathbf{K}\\boldsymbol\\varphi_n = \\omega_n^2\\,\\mathbf{M}\\boldsymbol\\varphi_n' },
    { text: 'Writing u = Σ φₙ qₙ and using orthogonality uncouples the equations. Each mode behaves as a single oscillator driven by the ground acceleration scaled by its participation factor.', tex: '\\ddot q_n + 2\\zeta_n\\omega_n\\dot q_n + \\omega_n^2 q_n = -\\Gamma_n\\,a_g(t),\\qquad \\Gamma_n = \\frac{\\boldsymbol\\varphi_n^{T}\\mathbf{M}\\mathbf{1}}{\\boldsymbol\\varphi_n^{T}\\mathbf{M}\\boldsymbol\\varphi_n}' },
    { text: 'Floor displacements are recovered by superposition, drifts by differencing, and the base shear from the first-storey drift.', tex: '\\Delta_i = u_i - u_{i-1},\\qquad V_b = k_1\\,\\Delta_1' },
  ],
  solve(v, a) {
    const n = N.clamp(Math.round(v.n_s), 1, 12), m = v.m_s, ks = Array.from({ length: n }, (_, i) => (a.uniform || n === 1 ? v.k_s : v.k_s * (1 - 0.5 * i / (n - 1))));
    const md = buildingModes(n, m, ks), w1 = md.om[0], T1 = 2 * Math.PI / w1, warnings = [];
    let dt = Math.min(1 / (40 * v.f_g), T1 / 40, v.t_d / 400); const ns = Math.min(Math.ceil(v.t_d / dt), 6000); dt = v.t_d / ns;
    const tt = Array.from({ length: ns + 1 }, (_, i) => i * dt), tp = 1 / (2 * v.f_g);
    const ag = tt.map(t => (a.harmonic || t <= tp ? v.a_g * Math.sin(2 * Math.PI * v.f_g * t) : 0));
    const nm = a.all_modes ? n : 1, q = [];
    for (let j = 0; j < nm; j++) { const z = a.modal_damp ? v.zeta : v.zeta * md.om[j] / w1; q.push(sdofResponse(md.om[j], z, ag.map(x => -md.gamma[j] * x), dt)); }
    if (!a.modal_damp && v.zeta * md.om[n - 1] / w1 >= 1) warnings.push('Stiffness-proportional damping makes the highest modes over-critically damped; their damping ratio has been limited to just below one.');
    const roof = new Array(ns + 1), driftMax = new Array(n).fill(0), U = Array.from({ length: n }, () => new Float64Array(ns + 1));
    for (let i = 0; i < n; i++) for (let j = 0; j < nm; j++) { const ph = md.phi[j][i], qj = q[j], Ui = U[i]; for (let s = 0; s <= ns; s++) Ui[s] += ph * qj[s]; }
    let roofMax = 0, vbMax = 0;
    for (let s = 0; s <= ns; s++) {
      roof[s] = U[n - 1][s]; roofMax = Math.max(roofMax, Math.abs(roof[s]));
      for (let i = 0; i < n; i++) { const d = Math.abs(U[i][s] - (i > 0 ? U[i - 1][s] : 0)); if (d > driftMax[i]) driftMax[i] = d; }
      vbMax = Math.max(vbMax, Math.abs(ks[0] * U[0][s]));
    }
    const dMax = N.maxOf(driftMax), W = n * m * g, ratio = dMax / v.h_s;
    if (ratio > 0.02) warnings.push('The peak drift ratio exceeds 2 %: a real structure would respond inelastically and this linear analysis no longer applies.');
    const rf = v.f_g / (w1 / (2 * Math.PI));
    if (a.harmonic && Math.abs(rf - 1) < 0.1) warnings.push('The ground-motion frequency is within 10 % of the fundamental frequency: the response is near resonance and controlled by damping.');
    const st = Array.from({ length: n + 1 }, (_, i) => i), shapes = [0, 1, 2].filter(j => j < n).map(j => ({ label: `Mode ${j + 1} (${lab(md.om[j] / (2 * Math.PI), 'Hz')})`, data: [0, ...md.phi[j].map(p => p / md.phi[j][n - 1])], dash: j > 0 }));
    const every = Math.max(1, Math.floor(ns / 80)), fr = [], ft = [];
    for (let s = 0; s <= ns; s += every) { fr.push([0, ...U.map(u => u[s] * 1e3)]); ft.push(tt[s]); }
    const mTot = n * m, gsum = md.gamma.reduce((s, x) => s + x * x, 0);
    return {
      scalars: [
        scalar('f_1', 'Fundamental frequency', w1 / (2 * Math.PI), '1/s', { show: 'Hz' }), scalar('T_1', 'Fundamental period', T1, 's'),
        scalar('f_2', 'Second-mode frequency', n > 1 ? md.om[1] / (2 * Math.PI) : NaN, '1/s', { show: 'Hz', text: n > 1 ? undefined : 'Single-storey structure has one mode' }),
        scalar('M_eff', 'Effective modal mass of the first mode over total mass', md.gamma[0] ** 2 / mTot, '1', { show: '%' }),
        scalar('r_f', 'Excitation frequency over fundamental frequency', rf, '1'),
        scalar('u_roof', 'Peak roof displacement relative to the ground', roofMax, 'm', { show: 'mm' }),
        scalar('drift_max', 'Peak storey drift', dMax, 'm', { show: 'mm' }), scalar('i_crit', 'Storey with the largest drift', driftMax.indexOf(dMax) + 1, '1'),
        scalar('drift_ratio', 'Peak drift ratio', ratio, '1', { show: '%' }),
        scalar('V_b', 'Peak base shear', vbMax, 'N', { show: 'kN' }), scalar('C_s', 'Base shear over building weight', vbMax / W, '1'),
      ],
      series: [
        line('roof', 'Roof displacement history', 'Time', 's', tt, [{ label: 'Roof displacement', data: roof.map(x => x * 1e3) }], 'Displacement', 'mm'),
        line('drift', 'Peak storey drifts', 'Storey', '–', st.slice(1), [{ label: 'Peak drift', data: driftMax.map(x => x * 1e3) }], 'Drift', 'mm', { kind: 'bar' }),
        line('modes', 'Mode shapes', 'Floor', '–', st, shapes, 'Modal displacement (roof = 1)', '–'),
      ],
      anims: [anim('sway', 'Displaced shape of the building', 'Floor', '–', st, fr, ft, 'Displacement relative to the ground', 'mm')],
      checks: [check('Effective modal masses sum to the total mass', (gsum - mTot) / mTot, 1e-8, 'Σ Γₙ² against total mass (mass-normalised modes)')],
      warnings,
    };
  },
  benchmarks(v) {
    const out = [], one = buildingModes(1, v.m_s, [v.k_s]);
    out.push(bench('Single-storey frequency f = (1/2π)√(k/m)', one.om[0] / (2 * Math.PI), Math.sqrt(v.k_s / v.m_s) / (2 * Math.PI), 'Single-degree-of-freedom oscillator', 1e-10));
    const md = buildingModes(5, v.m_s, new Array(5).fill(v.k_s)), w = j => 2 * Math.sqrt(v.k_s / v.m_s) * Math.sin((2 * j - 1) * Math.PI / 22);
    out.push(bench('Uniform five-storey building, first mode', md.om[0], w(1), 'ω_j = 2√(k/m)·sin((2j−1)π/(2(2N+1)))', 1e-8));
    out.push(bench('Uniform five-storey building, fifth mode', md.om[4], w(5), 'ω_j = 2√(k/m)·sin((2j−1)π/(2(2N+1)))', 1e-8));
    const om = 2 * Math.PI * 5, z = 0.05, wf = 2 * Math.PI * 2, dt = 0.002, p = Array.from({ length: 5001 }, (_, i) => Math.sin(wf * i * dt)), u = sdofResponse(om, z, p, dt);
    let amp = 0; for (let i = 4000; i <= 5000; i++) amp = Math.max(amp, Math.abs(u[i]));
    const rr = wf / om;
    out.push(bench('Steady-state harmonic amplitude of one mode', amp, 1 / (om * om) / Math.sqrt((1 - rr * rr) ** 2 + (2 * z * rr) ** 2), 'Dynamic amplification of a damped oscillator', 2e-3));
    return out;
  },
  validation: [],
  diagram(v) {
    const n = N.clamp(Math.round(v.n_s), 1, 12), h = Math.min(44, 250 / n), base = 310, sway = i => 36 * Math.sin(Math.PI / 2 * i / n);
    let body = '';
    for (let i = 1; i <= n; i++) {
      const y = base - i * h, x = 250 + sway(i), xb = 250 + sway(i - 1), yb = base - (i - 1) * h;
      body += S.line(xb + 8, yb, x + 8, y, 'd-line') + S.line(xb + 132, yb, x + 132, y, 'd-line') + S.rect(x, y - 5, 140, 10, 'd-body', 1);
    }
    return svg(`
      ${S.path('M150 310 L490 310', 'd-ground')} ${body}
      ${S.arrow(180, 330, 250, 330, 'd-arrow d-hazard')} ${S.arrow(250, 330, 180, 330, 'd-arrow d-hazard')} ${S.text(215, 350, 'ground motion a_g(t)')}
      ${S.text(520, 120, `${n} storeys`)} ${S.text(520, 140, `m = ${lab(v.m_s / 1e3, 't')}`)} ${S.text(520, 160, `k = ${lab(v.k_s / 1e6, 'MN/m')}`)}
      ${S.text(520, 180, `ζ = ${lab(v.zeta * 100, '%')}`)} ${S.text(110, 140, `a_g = ${lab(v.a_g / g, 'g')}`)} ${S.text(110, 160, `f_g = ${lab(v.f_g, 'Hz')}`)}
      ${S.text(320, 26, 'Rigid floors, flexible columns: one sway freedom per floor')}
    `);
  },
  experiment: {
    objective: 'Identify the natural frequencies, mode shapes and damping of a model shear frame and measure its response to base excitation.',
    apparatus: ['Multi-storey model frame with rigid floor plates and thin spring-steel columns', 'Shaking table driven by an electrodynamic or servo-hydraulic actuator', 'Signal generator and amplifier'],
    instruments: [{ name: 'Accelerometers on every floor and on the table', measures: 'Absolute accelerations', range: '±5 g', resolution: '1 kHz, ±1 %' }, { name: 'Laser displacement sensors', measures: 'Floor displacement relative to a fixed frame', range: '±50 mm', resolution: '±0.02 mm' }, { name: 'Dynamic signal analyser', measures: 'Frequency response functions', range: '0–100 Hz', resolution: '0.05 Hz' }],
    procedure: ['Weigh the floors and measure the static stiffness of one storey by a pull test.', 'Sweep the table frequency slowly at low amplitude and record transfer functions; pick resonances and mode shapes.', 'Obtain damping from the half-power bandwidth or free decay.', 'Apply a sine dwell or pulse and compare the measured drift histories with the prediction.'],
    controls: ['Repeat sweeps at two amplitudes to confirm linearity', 'Check table motion for distortion at resonance'],
    signatures: ['Frequencies in the ratios predicted for a uniform chain (about 1 : 2.9 : 4.6 for five storeys)', 'Largest drift in the first storey for first-mode response', 'Phase of roof motion passing through 90° at each resonance'],
    safety: ['Enclose the shaking table', 'Restrain the model against collapse'],
  },
  falsify: ['Measured mode shapes that are not orthogonal with respect to the mass matrix.', 'Natural frequencies of a uniform frame that depart from the sine-law ratios by more than the uncertainty in stiffness and mass.'],
  alternatives: [{ name: 'Response-spectrum analysis', text: 'Peak modal responses are read from a design spectrum and combined by SRSS or CQC rather than integrated in time.' }, { name: 'Flexural and frame models', text: 'Beam flexibility and axial column deformation make tall buildings behave more like cantilever beams than shear chains.' }, { name: 'Nonlinear time-history analysis', text: 'Tracks yielding and energy dissipation, which control response to strong earthquakes.' }],
  hazards: [{ hazard: 'Soft-storey collapse', cause: 'Drift concentrating in a flexible or weak storey', mitigation: 'Regular stiffness distribution; capacity design' }, { hazard: 'Resonant amplification', cause: 'Ground motion with dominant period close to the building period', mitigation: 'Supplemental damping, base isolation or period shift' }],
  standards: ['EN 1998-1 (Eurocode 8: design of structures for earthquake resistance)', 'ASCE/SEI 7 (minimum design loads for buildings and other structures)', 'ISO 3010 (seismic actions on structures)'],
  limits: 'Linear elastic response of a planar building with rigid floors and no torsion, foundation flexibility, P–Δ effect or yielding. A sinusoid or single pulse is an idealisation of real ground motion.',
  numerics: { method: 'Jacobi iteration on the Cholesky-reduced generalised eigenproblem; exact recurrence for each modal oscillator under piecewise-linear excitation (Nigam–Jennings)', stability: 'Unconditionally stable; exact for linearly interpolated forcing', resolution: 't_d' },
  optimise: { objective: 'drift_max', sense: 'min', vars: ['k_s'], note: 'Stiffening moves the building away from the excitation frequency or towards it; the trend is not monotonic near resonance.' },
  inverse: { series: 'roof', fit: ['k_s', 'zeta'] },
  extensions: ['Recorded accelerograms and response spectra', 'Tuned mass dampers and base isolation', 'Elastic–plastic storey behaviour'],
};

// ------------------------------------------------------------------ fatigue: S–N curve and Miner's rule
function fatigueRun(v, a) {
  // the second slope is anchored to the in-air curve at 10⁷ cycles and is not reduced in sea water, so the knee of the
  // cathodically protected curve moves to about 10⁶ cycles (as in the tabulated bilinear design curves)
  const aAir = Math.pow(10, v.log_a), aSN = aAir / (a.in_air ? 1 : 2.5), m = v.m, m2 = 2 * m - 1, a2 = 1e7 * Math.pow(aAir / 1e7, m2 / m), Sk = Math.pow(a2 / aSN, 1 / (m2 - m));
  const fT = a.no_thick ? 1 : Math.pow(Math.max(v.t_pl, 0.025) / 0.025, v.k_th), fG = a.goodman ? 1 / (1 - Math.min(v.sigma_m / v.sigma_u, 0.95)) : 1, fS = v.K_t * fT * fG;
  const Nf = S => (a.single_slope || S >= Sk ? aSN * Math.pow(S, -m) : a2 * Math.pow(S, -m2));
  const S = [v.S_1, v.S_2, v.S_3].map(s => fS * s / 1e6), n = [v.n_1, v.n_2, v.n_3], Ni = S.map(Nf), d = n.map((q, i) => q / Ni[i]), D = N.sum(d);
  return { aSN, m, m2, Sk, a2, fS, fT, fG, Nf, S, n, Ni, d, D };
}
const fatigueMiner = {
  id: 'fatigue-sn-miner',
  title: 'Fatigue life from an S–N curve and Miner\'s rule',
  module: 2, klass: 'I', domains: ['mechanical', 'structural', 'offshore'],
  keywords: ['fatigue life', 'fatigue damage', 's-n curve', 'sn curve', 'miner\'s rule', 'miner', 'palmgren-miner', 'stress range', 'stress concentration', 'goodman', 'mean stress', 'cumulative damage', 'welded joint', 'fatigue', 'cycles to failure', 'endurance'],
  summary: 'Cycles to failure from a basic S–N curve N = a·S⁻ᵐ with stress concentration, thickness and Goodman mean-stress corrections, and linear damage accumulation over a three-block stress histogram to give fatigue life.',
  background: [
    'Under repeated loading metals fail at stresses well below their static strength. For high-cycle fatigue the number of cycles to failure at a constant stress range follows, over a wide range, a power law that plots as a straight line on logarithmic axes: the S–N curve. Design curves for welded details lie two standard deviations below the mean of test data.',
    'Service loading contains many stress ranges. The Palmgren–Miner hypothesis assumes that each cycle consumes a fraction 1/N of the life at its own stress range, independent of order, and that failure occurs when the fractions sum to one. The local stress is raised by geometric stress concentration, and for unwelded material a tensile mean stress reduces the allowable amplitude, which the Goodman relation approximates.',
  ],
  phenomena: ['Crack initiation and growth under cyclic stress', 'Stress concentration', 'Mean-stress sensitivity', 'Cumulative damage', 'Environmental reduction of fatigue strength'],
  laws: ['hooke'],
  refs: ['Miner, M. A. (1945). Cumulative damage in fatigue. Journal of Applied Mechanics 12, A159–A164.', 'Palmgren, A. (1924). Die Lebensdauer von Kugellagern. Zeitschrift des Vereines Deutscher Ingenieure 68, 339–341.', 'Basquin, O. H. (1910). The exponential law of endurance tests. Proceedings of the American Society for Testing and Materials 10, 625–630.', 'DNV-RP-C203. Fatigue design of offshore steel structures. DNV, Høvik.', 'Dowling, N. E. (2013). Mechanical Behavior of Materials, 4th ed. Pearson.', 'Haibach, E. (2006). Betriebsfestigkeit: Verfahren und Daten zur Bauteilberechnung, 3rd ed. Springer.'],
  inputs: [
    inp('S_1', 'Stress range of block 1 (nominal)', 'MPa', 80, { min: 1, max: 1000, aliases: ['stress range', 'block 1 stress'] }),
    inp('n_1', 'Cycles per year in block 1', '1/yr', 1e4, { min: 0, max: 1e9, aliases: ['block 1 cycles'] }),
    inp('S_2', 'Stress range of block 2 (nominal)', 'MPa', 50, { min: 1, max: 1000, aliases: ['block 2 stress'] }),
    inp('n_2', 'Cycles per year in block 2', '1/yr', 1e5, { min: 0, max: 1e9, aliases: ['block 2 cycles'] }),
    inp('S_3', 'Stress range of block 3 (nominal)', 'MPa', 25, { min: 1, max: 1000, aliases: ['block 3 stress'] }),
    inp('n_3', 'Cycles per year in block 3', '1/yr', 1e6, { min: 0, max: 1e9, aliases: ['block 3 cycles'] }),
    inp('m', 'Inverse slope of the S–N curve', '1', 3, { min: 2, max: 10, kind: 'geometry', aliases: ['slope', 'sn slope', 'exponent'], src: 'm = 3 for welded steel details' }),
    inp('log_a', 'log₁₀ of the S–N intercept (stress range in MPa)', '1', 12.164, { min: 8, max: 20, kind: 'geometry', aliases: ['intercept', 'log a'], src: 'DNV-RP-C203, curve D in air, first slope' }),
    inp('K_t', 'Stress concentration factor', '1', 1.0, { min: 1, max: 10, kind: 'geometry', aliases: ['stress concentration', 'scf', 'kt'] }),
    inp('sigma_m', 'Mean stress', 'MPa', 50, { min: 0, max: 150, aliases: ['mean stress'] }),
    inp('sigma_u', 'Ultimate tensile strength', 'MPa', 500, { min: 200, max: 2000, kind: 'geometry', aliases: ['ultimate strength', 'tensile strength', 'uts'] }),
    inp('t_pl', 'Plate thickness', 'mm', 40, { min: 5, max: 200, kind: 'geometry', aliases: ['thickness', 'plate thickness'] }),
    inp('k_th', 'Thickness exponent', '1', 0.2, { min: 0, max: 0.3, kind: 'geometry', aliases: ['thickness exponent'], src: 'Typical for welded plate details with a 25 mm reference thickness' }),
    inp('DFF', 'Design fatigue factor', '1', 1, { min: 1, max: 10, aliases: ['design fatigue factor', 'dff', 'safety factor'] }),
    inp('T_d', 'Design life', 'yr', 25, { min: 1, max: 100, aliases: ['design life', 'service life'] }),
  ],
  assumptions: [
    asm('single_slope', 'The S–N curve is a single straight line on logarithmic axes with no endurance limit.', { why: 'Basic Basquin form', alt: 'A second, shallower slope 2m − 1 applies below the knee of the curve, which lies at 10⁷ cycles in air (Haibach extension, as in bilinear design curves).' }),
    asm('goodman', 'Tensile mean stress is allowed for with the Goodman relation.', { why: 'Unwelded, stress-relieved material', alt: 'No mean-stress correction: appropriate for as-welded joints, where residual stress makes the range alone govern.' }),
    asm('no_thick', 'No thickness correction is applied.', { why: 'Thickness at or below the 25 mm reference', alt: 'Stress ranges are multiplied by (t/25 mm)^k for plate thicker than the reference; thinner plate is not credited.' }),
    asm('in_air', 'The detail is in air or fully protected from the environment.', { why: 'Curve as tested', alt: 'Sea water with cathodic protection: the first-slope intercept is divided by 2.5. The second slope of a bilinear curve is left unchanged, so its knee moves from 10⁷ to about 10⁶ cycles.' }),
  ],
  symbols: { S_i: ['Nominal stress range of block i', 'Pa'], S_ref: ['Reference stress of the S–N curve (1 MPa)', 'Pa'], f_s: ['Combined stress factor', '1'], a_sn: ['S–N intercept', '1'], a_2: ['Intercept of the second slope', '1'], N_i: ['Cycles to failure at block i', '1'], N_1: ['Cycles to failure at block 1', '1'], N_2: ['Cycles to failure at block 2', '1'], N_3: ['Cycles to failure at block 3', '1'], D_r: ['Damage rate', '1/s'], T_f: ['Fatigue life', 's'], t_ref: ['Reference thickness (25 mm)', 'm'] },
  equations: a => [
    eq('fs', 'Combined stress factor', 'f_s', `K_t${a.no_thick ? '' : '*(max(t_pl, t_ref)/t_ref)^k_th'}${a.goodman ? '/(1 - sigma_m/sigma_u)' : ''}`, { kind: 'closure', origin: 'Stress concentration' + (a.no_thick ? '' : ', thickness effect') + (a.goodman ? ', Goodman mean-stress correction' : ''), needs: a.goodman ? ['goodman'] : [] }),
    eq('asn', 'S–N intercept', 'a_sn', a.in_air ? '10^log_a' : '10^log_a/2.5', { kind: 'empirical', origin: 'Regression of constant-amplitude fatigue tests', needs: a.in_air ? ['in_air'] : [] }),
    eq('sn', 'S–N curve', 'N_i', 'a_sn*(f_s*S_i/S_ref)^(-m)', { kind: 'empirical', origin: 'Basquin (1910) power law', needs: a.single_slope ? ['single_slope'] : [] }),
    ...(a.single_slope ? [] : [eq('sn2', 'Second slope below the knee', 'N_i', 'a_2*(f_s*S_i/S_ref)^(-(2*m - 1))', { kind: 'empirical', origin: 'Haibach extension of the S–N curve below the knee', note: 'Used for effective stress ranges below the knee, where the two branches intersect; a_2 makes the in-air branches meet at 10⁷ cycles.' })]),
    eq('miner', 'Linear damage accumulation', 'D_r', 'n_1/N_1 + n_2/N_2 + n_3/N_3', { kind: 'hypothesis', origin: 'Palmgren (1924), Miner (1945): damage fractions add independently of sequence' }),
    eq('life', 'Fatigue life', 'T_f', '1/(DFF*D_r)', { kind: 'derived', origin: 'Failure when the damage sum reaches one, with a design fatigue factor' }),
  ],
  derivation: a => [
    { text: 'Constant-amplitude tests give a straight line when the logarithm of life is plotted against the logarithm of stress range.', tex: '\\log_{10}N = \\log_{10}a - m\\,\\log_{10}S\\quad\\Leftrightarrow\\quad N = a\\,S^{-m}' },
    { text: 'The nominal stress range is raised to the local value by the stress concentration factor' + (a.no_thick ? '' : ', the thickness factor') + (a.goodman ? '. A tensile mean stress is accounted for by the Goodman line, which scales the range to the equivalent fully reversed value.' : '.'), tex: a.goodman ? 'S_e = \\frac{K_t\\,S}{1 - \\sigma_m/\\sigma_u}' : 'S_e = K_t\\,S' },
    { text: 'If nᵢ cycles occur per year at a stress range whose life is Nᵢ, the damage accumulated per year is the sum of the cycle ratios.', tex: 'D = \\sum_i \\frac{n_i}{N_i}' },
    { text: 'Failure is predicted when the accumulated damage reaches one; dividing by the design fatigue factor gives the design life.', tex: 'T_f = \\frac{1}{DFF\\cdot D}' },
  ],
  solve(v, a) {
    const r = fatigueRun(v, a), life = r.D > 0 ? 1 / (v.DFF * r.D) : NaN, Dlife = r.D * v.T_d * v.DFF, warnings = [];
    if (Dlife > 1) warnings.push('The factored damage over the design life exceeds one: the detail does not achieve the design life.');
    if (a.goodman && v.sigma_m / v.sigma_u > 0.5) warnings.push('Mean stress exceeds half the tensile strength; the Goodman line is a rough guide here.');
    if (N.maxOf(r.Ni) < 1e4 && r.D > 0) warnings.push('Lives below about 10⁴ cycles are in the low-cycle regime, where a strain-based method is required.');
    const ntot = N.sum(r.n), Seq = ntot > 0 ? Math.pow(N.sum(r.n.map((q, i) => q * Math.pow(r.S[i], r.m))) / ntot, 1 / r.m) : 0;
    const Ss = N.logspace(10, 1000, 60), yrs = N.linspace(0, v.T_d, 51), iMax = r.d.indexOf(N.maxOf(r.d));
    return {
      scalars: [
        scalar('f_s', 'Combined stress factor', r.fS, '1'), scalar('S_e1', 'Effective stress range, block 1', r.S[0] * 1e6, 'Pa', { show: 'MPa' }),
        scalar('N_1', 'Cycles to failure at block 1', r.Ni[0], '1'), scalar('N_2', 'Cycles to failure at block 2', r.Ni[1], '1'), scalar('N_3', 'Cycles to failure at block 3', r.Ni[2], '1'),
        scalar('S_knee', 'Stress range at the knee of the bilinear curve', r.Sk * 1e6, 'Pa', { show: 'MPa' }), scalar('S_eq', 'Equivalent constant-amplitude stress range', Seq * 1e6, 'Pa', { show: 'MPa' }),
        scalar('D_r', 'Damage rate', r.D, '1/s', { show: '1/yr' }), scalar('i_dom', 'Block contributing most damage', iMax + 1, '1'),
        scalar('T_f', 'Fatigue life (with design fatigue factor)', life, 's', { show: 'yr', text: Number.isFinite(life) ? undefined : 'Unlimited — no cycles applied' }),
        scalar('D_life', 'Factored damage over the design life', Dlife, '1', { note: Dlife <= 1 ? 'acceptable' : 'exceeds one' }),
      ],
      series: [
        line('sn-curve', 'S–N curve and applied blocks', 'Effective stress range', 'MPa', Ss, [{ label: 'Cycles to failure', data: Ss.map(r.Nf) }], 'Cycles', '–', { logx: true, logy: true, overlay: [{ label: 'Cycles applied over the design life', x: r.S, y: r.n.map(q => Math.max(q * v.T_d, 1)), scatter: true }] }),
        line('damage-blocks', 'Damage contributed by each block over the design life', 'Block', '–', [1, 2, 3], [{ label: 'Damage fraction', data: r.d.map(q => q * v.T_d * v.DFF) }], 'Factored damage', '–', { kind: 'bar' }),
        line('damage-time', 'Accumulated damage', 'Time', 'yr', yrs.map(t => t / YEAR), [{ label: 'Factored damage', data: yrs.map(t => r.D * t * v.DFF) }, { label: 'Failure criterion', data: yrs.map(() => 1), dash: true }], 'Damage', '–'),
      ],
      checks: [check('Block damages sum to the total', r.D > 0 ? (N.sum(r.d) - r.D) / r.D : 0, 1e-12, 'Σ nᵢ/Nᵢ')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b0 = { ...a, single_slope: true, goodman: false, no_thick: true, in_air: true }, out = [];
    const n1 = Math.max(v.n_1, 1e-6), r = fatigueRun({ ...v, K_t: 1, n_1: n1, n_2: 0, n_3: 0 }, b0);
    out.push(bench('Single block: life = a/(n·Sᵐ)', 1 / r.D, Math.pow(10, v.log_a) / (n1 * Math.pow(v.S_1 / 1e6, v.m)), 'Closed form for constant-amplitude loading', 1e-10));
    out.push(bench('Design curve D in air at its knee', Math.pow(10, 12.164) * Math.pow(52.63, -3), 1e7, 'DNV-RP-C203: 52.63 MPa at 10⁷ cycles', 2e-3));
    const rb = fatigueRun(v, { ...b0, single_slope: false });
    out.push(bench('Bilinear curve is continuous at the knee', rb.a2 * Math.pow(rb.Sk, -rb.m2), rb.aSN * Math.pow(rb.Sk, -rb.m), 'Both branches give the same life', 1e-10));
    const dD = { ...v, m: 3, log_a: 12.164 }, ra = fatigueRun(dD, { ...b0, single_slope: false }), rw = fatigueRun(dD, { ...b0, single_slope: false, in_air: false });
    out.push(bench('Design curve D in air: second-slope intercept', Math.log10(ra.a2), 15.606, 'DNV-RP-C203 tabulated log ā₂ for m₂ = 5', 1e-4));
    out.push(bench('Design curve D with cathodic protection: first-slope intercept', Math.log10(rw.aSN), 11.764, 'DNV-RP-C203 tabulated log ā₁ in sea water (a factor 10^0.4 ≈ 2.5 below air)', 5e-4));
    out.push(bench('Design curve D with cathodic protection: life at the knee', rw.Nf(rw.Sk), 1e6, 'DNV-RP-C203: slope changes at 10⁶ cycles in sea water', 2e-2));
    const r2 = fatigueRun({ ...v, K_t: 2 }, b0), r1 = fatigueRun({ ...v, K_t: 1 }, b0);
    out.push(bench('Doubling the stress multiplies damage by 2ᵐ', r1.D > 0 ? r2.D / r1.D : Math.pow(2, v.m), Math.pow(2, v.m), 'Power-law scaling', 1e-10));
    return out;
  },
  validation: [],
  diagram(v) {
    const X = S => 90 + 440 * (Math.log10(S) - 6) / 2, Y = n => 290 - 220 * Math.log10(Math.max(n, 1)) / 8;
    const blocks = [[v.S_1, v.n_1], [v.S_2, v.n_2], [v.S_3, v.n_3]];
    return svg(`
      ${S.line(90, 290, 560, 290, 'd-line')} ${S.line(90, 290, 90, 50, 'd-line')}
      ${S.text(325, 325, 'log cycles N')} ${S.text(40, 60, 'log S', 'd-text', 'start')}
      ${S.line(110, 80, 540, 250, 'd-hazard')} ${S.text(420, 180, 'N = a·S⁻ᵐ', 'd-text', 'start')}
      ${blocks.map((b, i) => { const y = 250 - 150 * N.clamp((Math.log10(b[0]) - 6) / 3, 0, 1), x = 110 + 380 * N.clamp(Math.log10(Math.max(b[1] * v.T_d / YEAR, 1)) / 9, 0, 1); return S.line(110, y, x, y, 'd-dim') + S.circle(x, y, 5, 'd-fill') + S.text(x + 10, y - 6, `block ${i + 1}: ${lab(b[0] / 1e6, 'MPa')}`, 'd-text d-small', 'start'); }).join('')}
      ${S.text(320, 30, 'Miner sum D = Σ nᵢ / Nᵢ; failure at D = 1')}
      ${S.text(320, 350, `m = ${lab(v.m)}   log a = ${lab(v.log_a, '', 5)}   K_t = ${lab(v.K_t)}`)}
    `);
  },
  experiment: {
    objective: 'Establish the S–N curve of a material or welded detail and test the linear damage rule with two-level block loading.',
    apparatus: ['Servo-hydraulic or resonance fatigue testing machine', 'Set of nominally identical specimens (at least twelve for a curve)', 'Alignment fixture'],
    instruments: [{ name: 'Load cell', measures: 'Load range and mean', range: '±100 kN', resolution: '±0.5 %' }, { name: 'Strain gauges near the detail', measures: 'Local stress range and bending', range: '±3000 µε', resolution: '±1 µε' }, { name: 'Cycle counter and crack detection (compliance drop or potential drop)', measures: 'Cycles to initiation and failure', range: '10³–10⁸', resolution: '1 cycle' }],
    procedure: ['Test specimens at four or more stress ranges at constant amplitude and fixed stress ratio until failure or run-out.', 'Fit log N against log S by least squares; report the mean and the mean-minus-two-standard-deviations design line.', 'Apply high–low and low–high two-block sequences and compare the damage sum at failure with one.'],
    controls: ['Verify alignment (bending below 5 %)', 'Keep frequency low enough to avoid heating', 'Randomise test order'],
    signatures: ['Straight line on log–log axes with slope near −1/3 for welded steel', 'Damage sums at failure scattered about one, typically below one for high–low sequences and above for low–high'],
    safety: ['Guard specimens: fracture releases stored energy', 'Hydraulic pressure hazards'],
  },
  falsify: ['Constant-amplitude lives that do not follow a power law over the tested range.', 'Damage sums at failure consistently far from one under variable-amplitude loading representative of service.'],
  alternatives: [{ name: 'Fracture-mechanics crack growth', text: 'Integrates the Paris law from an initial flaw; captures sequence effects and inspection planning.' }, { name: 'Strain-life (Coffin–Manson) method', text: 'Used for low-cycle fatigue where plastic strain dominates.' }, { name: 'Other mean-stress corrections', text: 'Gerber, Morrow and Smith–Watson–Topper relations often fit ductile metals better than the Goodman line.' }, { name: 'Rainflow counting and spectral methods', text: 'Convert an irregular stress history or spectrum into the cycle histogram used here.' }],
  hazards: [{ hazard: 'Fatigue cracking and fracture', cause: 'Under-estimated stress ranges, poor weld quality, corrosion', mitigation: 'Design fatigue factors, inspection, weld improvement, corrosion protection' }],
  standards: ['DNV-RP-C203 (fatigue design of offshore steel structures)', 'BS 7608 (fatigue design and assessment of steel products)', 'EN 1993-1-9 (Eurocode 3: fatigue)', 'IIW Recommendations for fatigue design of welded joints and components'],
  limits: 'High-cycle, stress-based fatigue with a user-supplied S–N curve; linear damage accumulation without sequence or overload effects. The Goodman correction applies to unwelded material; design curves for welded joints are normally used with stress range alone. The curve constants must match the detail category, environment and stress definition.',
  numerics: { method: 'Closed-form evaluation of the S–N curve and damage sum' },
  optimise: { objective: 'D_life', sense: 'min', vars: ['K_t'], note: 'Life varies as the stress to the power −m: reducing stress concentration is the most effective improvement.' },
  inverse: { series: 'sn-curve', fit: ['m', 'log_a'] },
  extensions: ['Rainflow counting of a measured stress history', 'Weibull long-term stress-range distribution with closed-form damage', 'Crack-growth assessment with inspection intervals'],
};

// ------------------------------------------------------------------ thick-walled cylinder (Lamé)
function lameRun(v, a, t = v.t_w, pi = v.p_i) {
  const ri = v.r_i, ro = ri + t, po = v.p_o, den = ro * ro - ri * ri, A = (pi * ri * ri - po * ro * ro) / den, B = (pi - po) * ri * ri * ro * ro / den;
  const sr = r => (a.thick ? A - B / (r * r) : 0), sh = r => (a.thick ? A + B / (r * r) : (pi * ri - po * ro) / t), sz = a.closed ? A : 0;
  const seq = r => { const s1 = sh(r), s2 = sr(r), s3 = sz; return a.von_mises ? Math.sqrt(0.5 * ((s1 - s2) ** 2 + (s2 - s3) ** 2 + (s3 - s1) ** 2)) : Math.max(s1, s2, s3) - Math.min(s1, s2, s3); };
  return { ri, ro, K: ro / ri, A, B, sr, sh, sz, seq, seqMax: Math.max(seq(ri), seq(ro)) };
}
const pressureVessel = {
  id: 'pressure-vessel-lame',
  title: 'Thick-walled cylinder under pressure (Lamé)',
  module: 2, klass: 'I', domains: ['mechanical', 'pipeline'],
  keywords: ['thick-walled cylinder', 'thick walled cylinder', 'lamé', 'lame equations', 'pressure vessel', 'hoop stress', 'radial stress', 'von mises', 'burst pressure', 'thin-wall', 'barlow', 'internal pressure', 'external pressure', 'wall thickness', 'cylinder stress', 'pipe stress'],
  summary: 'Radial, hoop and axial stress through the wall of a cylinder under internal and external pressure from Lamé\'s solution, with the thin-wall alternative, equivalent stress, yield margin, burst estimate and required thickness.',
  background: [
    'In a long cylinder loaded by uniform pressure the stresses depend only on radius. Equilibrium of a ring element, compatibility of the radial displacement and Hooke\'s law give Lamé\'s solution: the hoop and radial stresses are the sum and difference of a constant and a term in 1/r². The hoop stress is greatest at the bore, where yielding starts.',
    'When the wall is thin compared with the radius the hoop stress is almost uniform and the membrane formula p·r/t suffices; the two solutions converge as the radius ratio approaches one. Beyond first yield a plastic zone spreads outward from the bore, and a ductile cylinder bursts at a pressure well above that of first yield, which Faupel correlated with yield and tensile strength.',
  ],
  phenomena: ['Elastic stress gradient through a thick wall', 'Membrane (thin-wall) behaviour', 'Yield initiation at the bore', 'Plastic collapse and burst'],
  laws: ['hooke', 'newton2', 'newton3'],
  refs: ['Lamé, G. (1852). Leçons sur la théorie mathématique de l\'élasticité des corps solides. Bachelier, Paris.', 'Timoshenko, S. P. & Goodier, J. N. (1970). Theory of Elasticity, 3rd ed. McGraw-Hill.', 'Faupel, J. H. (1956). Yield and bursting characteristics of heavy-wall cylinders. Transactions of the ASME 78, 1031–1064.', 'Hill, R. (1950). The Mathematical Theory of Plasticity. Oxford University Press.'],
  inputs: [
    inp('r_i', 'Inner radius', 'mm', 100, { min: 5, max: 3000, kind: 'geometry', aliases: ['inner radius', 'bore radius', 'radius'] }),
    inp('t_w', 'Wall thickness', 'mm', 25, { min: 0.5, max: 1000, kind: 'geometry', aliases: ['wall thickness', 'thickness', 'wall'] }),
    inp('p_i', 'Internal pressure', 'bar', 200, { min: 0, max: 5000, aliases: ['internal pressure', 'pressure', 'design pressure'] }),
    inp('p_o', 'External pressure', 'bar', 0, { min: 0, max: 1000, aliases: ['external pressure', 'outside pressure'] }),
    inp('sigma_y', 'Yield strength', 'MPa', 448, { min: 100, max: 2000, kind: 'geometry', aliases: ['yield strength', 'yield stress', 'yield', 'smys'], src: 'API 5L grade X65, specified minimum' }),
    inp('sigma_u', 'Ultimate tensile strength', 'MPa', 531, { min: 150, max: 2500, kind: 'geometry', aliases: ['ultimate strength', 'tensile strength', 'uts', 'smts'], src: 'API 5L grade X65, specified minimum' }),
    inp('f_d', 'Design factor on yield', '1', 0.72, { min: 0.3, max: 1, aliases: ['design factor', 'usage factor'] }),
  ],
  assumptions: [
    asm('thick', 'Stresses follow Lamé\'s thick-wall solution.', { why: 'Exact for a linear elastic cylinder', alt: 'Thin-wall membrane theory: hoop stress (p_i·r_i − p_o·r_o)/t, uniform through the wall, radial stress neglected.' }),
    asm('closed', 'The ends are closed, so the pressure thrust is carried as axial stress in the wall.', { why: 'Vessel or capped pipe', alt: 'The ends are open or the thrust is carried externally: axial stress is zero.' }),
    asm('von_mises', 'Yielding is governed by the von Mises equivalent stress.', { why: 'Best fit for ductile metals', alt: 'The Tresca (maximum shear stress) criterion is used.' }),
    asm('faupel', 'Burst pressure is estimated with Faupel\'s formula.', { why: 'Correlated against burst tests of ductile cylinders', alt: 'The fully plastic (limit) pressure with flow stress equal to the tensile strength is used.' }),
  ],
  symbols: { r: ['Radius', 'm'], r_o: ['Outer radius', 'm'], A_l: ['Lamé constant A', 'Pa'], B_l: ['Lamé constant B', 'N'], sigma_r: ['Radial stress', 'Pa'], sigma_theta: ['Hoop stress', 'Pa'], sigma_z: ['Axial stress', 'Pa'], sigma_eq: ['Equivalent stress', 'Pa'], p_b: ['Burst pressure', 'Pa'] },
  equations: a => [
    eq('ro', 'Outer radius', 'r_o', 'r_i + t_w', { kind: 'definition' }),
    ...(a.thick ? [
      eq('eqm', 'Radial equilibrium', 'pd(sigma_r, r)', '(sigma_theta - sigma_r)/r', { kind: 'law', origin: 'Force balance on a ring element' }),
      eq('A', 'Lamé constant A', 'A_l', '(p_i*r_i^2 - p_o*r_o^2)/(r_o^2 - r_i^2)', { kind: 'derived', origin: 'Boundary conditions σ_r = −p at both surfaces' }),
      eq('B', 'Lamé constant B', 'B_l', '(p_i - p_o)*r_i^2*r_o^2/(r_o^2 - r_i^2)', { kind: 'derived', origin: 'Boundary conditions σ_r = −p at both surfaces' }),
      eq('sr', 'Radial stress', 'sigma_r', 'A_l - B_l/r^2', { kind: 'derived', origin: 'Lamé (1852)', needs: ['thick'] }),
      eq('sh', 'Hoop stress', 'sigma_theta', 'A_l + B_l/r^2', { kind: 'derived', origin: 'Lamé (1852)', needs: ['thick'] }),
    ] : [
      eq('sh', 'Thin-wall hoop stress', 'sigma_theta', '(p_i*r_i - p_o*r_o)/t_w', { kind: 'law', origin: 'Equilibrium of a half-cylinder' }),
    ]),
    ...(a.closed ? [eq('sz', 'Axial stress with closed ends', 'sigma_z', '(p_i*r_i^2 - p_o*r_o^2)/(r_o^2 - r_i^2)', { kind: 'law', origin: 'Axial equilibrium of the end cap', needs: ['closed'] })] : []),
    a.von_mises
      ? (a.closed
        ? eq('eq', 'Von Mises equivalent stress', 'sigma_eq', `sqrt(0.5*((sigma_theta - ${a.thick ? 'sigma_r' : '0'})^2 + (${a.thick ? 'sigma_r' : '0'} - sigma_z)^2 + (sigma_z - sigma_theta)^2))`, { kind: 'closure', origin: 'Distortion-energy yield criterion', needs: ['von_mises'] })
        : eq('eq', 'Von Mises equivalent stress (zero axial stress)', 'sigma_eq', a.thick ? 'sqrt(sigma_theta^2 - sigma_theta*sigma_r + sigma_r^2)' : 'abs(sigma_theta)', { kind: 'closure', origin: 'Distortion-energy yield criterion', needs: ['von_mises'] }))
      : eq('eq', 'Tresca equivalent stress', 'sigma_eq', a.thick ? (a.closed ? 'abs(sigma_theta - sigma_r)' : 'max(max(sigma_theta, sigma_r), 0) - min(min(sigma_theta, sigma_r), 0)') : (a.closed ? 'max(max(sigma_theta, sigma_z), 0) - min(min(sigma_theta, sigma_z), 0)' : 'abs(sigma_theta)'), { kind: 'closure', origin: 'Maximum shear-stress yield criterion' }),
    a.faupel
      ? eq('pb', 'Burst pressure', 'p_b', '2/sqrt(3)*sigma_y*(2 - sigma_y/sigma_u)*ln(r_o/r_i)', { kind: 'empirical', origin: 'Faupel (1956)', needs: ['faupel'] })
      : eq('pb', 'Fully plastic pressure at the tensile strength', 'p_b', '2/sqrt(3)*sigma_u*ln(r_o/r_i)', { kind: 'derived', origin: 'Limit analysis of a von Mises cylinder; Hill (1950)' }),
  ],
  derivation: a => (a.thick ? [
    { text: 'Radial equilibrium of an element bounded by radii r and r + dr relates the two in-plane stresses.', tex: '\\frac{\\mathrm{d}\\sigma_r}{\\mathrm{d}r} + \\frac{\\sigma_r - \\sigma_\\theta}{r} = 0' },
    { text: 'With strains derived from a single radial displacement and Hooke\'s law, the equations reduce to an Euler-type equation whose solution has two constants.', tex: '\\sigma_r = A - \\frac{B}{r^2},\\qquad \\sigma_\\theta = A + \\frac{B}{r^2}' },
    { text: 'Requiring the radial stress to equal minus the pressure at the inner and outer surfaces fixes the constants.', tex: 'A = \\frac{p_i r_i^2 - p_o r_o^2}{r_o^2 - r_i^2},\\qquad B = \\frac{(p_i - p_o)\\,r_i^2 r_o^2}{r_o^2 - r_i^2}' },
    { text: 'The hoop stress is largest at the bore. For internal pressure alone its ratio to the thin-wall value tends to one as the wall becomes thin.', tex: '\\sigma_\\theta(r_i) = p_i\\,\\frac{r_o^2 + r_i^2}{r_o^2 - r_i^2}\\ \\xrightarrow{t \\ll r}\\ \\frac{p_i\\,r_i}{t}' },
  ] : [
    { text: 'Cut the cylinder along a diameter. The pressure on the projected area is balanced by the hoop force in the two wall sections; if the wall is thin the stress is taken as uniform.', tex: '\\sigma_\\theta = \\frac{p_i r_i - p_o r_o}{t}' },
    { text: 'With closed ends the pressure thrust on the end is carried by the wall cross-section.', tex: '\\sigma_z = \\frac{p_i r_i^2 - p_o r_o^2}{r_o^2 - r_i^2} \\approx \\frac{p\\,r}{2t}' },
  ]),
  solve(v, a) {
    const r = lameRun(v, a), dp = v.p_i - v.p_o, su = Math.max(v.sigma_u, v.sigma_y), warnings = [];
    if (v.sigma_u < v.sigma_y) warnings.push('The stated tensile strength is below the yield strength; the yield strength has been used for both in the burst estimate.');
    if (!a.thick && r.K > 1.1) warnings.push('Radius ratio exceeds 1.1: thin-wall theory under-estimates the bore hoop stress by more than about 5 %.');
    if (r.seqMax > v.sigma_y) warnings.push('The equivalent stress exceeds the yield strength: the wall has started to yield and the elastic solution no longer applies.');
    if (v.p_o > v.p_i) warnings.push('Net external pressure: collapse by buckling may govern and is not assessed here.');
    const pb = 2 / Math.sqrt(3) * (a.faupel ? v.sigma_y * (2 - v.sigma_y / su) : su) * Math.log(r.K);
    const fy = p => lameRun(v, a, v.t_w, p).seqMax - v.sigma_y, hiP = v.p_o + 200 * v.sigma_y;
    const py = fy(v.p_o) >= 0 ? v.p_o : fy(hiP) > 0 ? N.bisect(fy, v.p_o, hiP, 1e-12) : NaN;
    const ft = t => lameRun(v, a, t).seqMax - v.f_d * v.sigma_y, tLo = 1e-5 * v.r_i, tHi = 50 * v.r_i;
    let tReq = NaN, tTxt;
    if (ft(tLo) <= 0) tReq = tLo; else if (ft(tHi) > 0) tTxt = 'Not achievable — the pressure exceeds what any elastic wall can carry at this design factor'; else tReq = N.bisect(ft, tLo, tHi, 1e-12);
    const rs = N.linspace(r.ri, r.ro, 61), ts = N.logspace(0.01 * v.r_i, 2 * v.r_i, 60);
    return {
      scalars: [
        scalar('K', 'Radius ratio r_o/r_i', r.K, '1'), scalar('sigma_theta_i', 'Hoop stress at the bore', r.sh(r.ri), 'Pa', { show: 'MPa' }), scalar('sigma_theta_o', 'Hoop stress at the outer surface', r.sh(r.ro), 'Pa', { show: 'MPa' }),
        scalar('sigma_r_i', 'Radial stress at the bore', r.sr(r.ri), 'Pa', { show: 'MPa' }), scalar('sigma_z', 'Axial stress', r.sz, 'Pa', { show: 'MPa' }),
        scalar('sigma_eq', a.von_mises ? 'Largest von Mises stress' : 'Largest Tresca stress', r.seqMax, 'Pa', { show: 'MPa' }), scalar('util', 'Utilisation against yield', r.seqMax / v.sigma_y, '1'),
        scalar('thin_ratio', 'Bore hoop stress over the thin-wall value', dp !== 0 && a.thick ? r.sh(r.ri) / ((v.p_i * r.ri - v.p_o * r.ro) / v.t_w) : 1, '1'),
        scalar('p_y', 'Internal pressure at first yield', py, 'Pa', { show: 'bar', text: Number.isFinite(py) ? undefined : 'Not reached' }),
        scalar('p_b', 'Estimated burst pressure (differential)', pb, 'Pa', { show: 'bar' }),
        scalar('burst_margin', 'Burst pressure over operating differential pressure', dp > 0 ? pb / dp : NaN, '1', { text: dp > 0 ? undefined : 'No net internal pressure' }),
        scalar('t_req', 'Wall thickness for the design factor', tReq, 'm', { show: 'mm', text: tTxt }),
      ],
      series: [
        line('stress-wall', 'Stress distribution through the wall', 'Radius', 'mm', rs.map(x => x * 1e3), [{ label: 'Hoop', data: rs.map(x => r.sh(x) / 1e6) }, { label: 'Radial', data: rs.map(x => r.sr(x) / 1e6) }, { label: 'Axial', data: rs.map(() => r.sz / 1e6), dash: true }, { label: a.von_mises ? 'Von Mises' : 'Tresca', data: rs.map(x => r.seq(x) / 1e6), dash: true }], 'Stress', 'MPa'),
        line('thick-vs-thin', 'Bore equivalent stress against wall thickness', 'Wall thickness', 'mm', ts.map(t => t * 1e3), [{ label: 'Lamé', data: ts.map(t => lameRun(v, { ...a, thick: true }, t).seqMax / 1e6) }, { label: 'Thin-wall', data: ts.map(t => lameRun(v, { ...a, thick: false }, t).seqMax / 1e6), dash: true }, { label: 'Yield strength', data: ts.map(() => v.sigma_y / 1e6), dash: true }], 'Equivalent stress', 'MPa', { logx: true, yRange: [0, 2 * v.sigma_y / 1e6] }),
      ],
      checks: [
        check('Radial stress at the bore equals minus the internal pressure', a.thick ? (r.sr(r.ri) + v.p_i) / Math.max(v.p_i, v.p_o, 1) : 0, 1e-9, 'Boundary condition'),
        check('Radial stress at the outer surface equals minus the external pressure', a.thick ? (r.sr(r.ro) + v.p_o) / Math.max(v.p_i, v.p_o, 1) : 0, 1e-9, 'Boundary condition'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const th = { ...a, thick: true, closed: true, von_mises: true }, out = [];
    const r2 = lameRun({ ...v, r_i: 0.1, p_i: 1e7, p_o: 0 }, th, 0.1);
    out.push(bench('Bore hoop stress for r_o/r_i = 2', r2.sh(0.1) / 1e7, 5 / 3, 'σ_θ = p·(K² + 1)/(K² − 1)', 1e-12));
    const rt = lameRun({ ...v, r_i: 1, p_i: 1e6, p_o: 0 }, th, 0.001);
    out.push(bench('Thin-wall limit: Lamé bore hoop stress over p·r/t', rt.sh(1) / (1e6 * 1 / 0.001), 1, 'Converges as t/r → 0', 1e-3));
    out.push(bench('Sum of hoop and radial stress is constant through the wall', (r2.sh(0.15) + r2.sr(0.15)) / (2 * r2.A), 1, 'σ_θ + σ_r = 2A', 1e-12));
    const rx = lameRun({ ...v, r_i: 0.1, p_i: 0, p_o: 1e7 }, th, 0.1);
    out.push(bench('External pressure only: bore hoop stress for r_o/r_i = 2', rx.sh(0.1) / 1e7, -8 / 3, 'σ_θ = −2p·K²/(K² − 1)', 1e-12));
    out.push(bench('First-yield pressure, closed ends, Tresca', lameRun({ ...v, r_i: 0.1, p_i: v.sigma_y * 0.375, p_o: 0 }, { ...th, von_mises: false }, 0.1).seqMax, v.sigma_y, 'p_y = σ_y·(K² − 1)/(2K²)', 1e-12));
    out.push(bench('First-yield pressure, closed ends, von Mises', lameRun({ ...v, r_i: 0.1, p_i: v.sigma_y * 0.75 / Math.sqrt(3), p_o: 0 }, th, 0.1).seqMax, v.sigma_y, 'p_y = σ_y·(K² − 1)/(√3·K²)', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    const ro = 110, ri = Math.max(30, Math.min(100, ro * v.r_i / (v.r_i + v.t_w)));
    return svg(`
      ${S.circle(220, 185, ro, 'd-body')} ${S.circle(220, 185, ri, 'd-liquid')}
      ${[0, 1, 2, 3, 4, 5, 6, 7].map(i => { const c = Math.cos(i * Math.PI / 4), s = Math.sin(i * Math.PI / 4); return S.arrow(220 + 0.35 * ri * c, 185 + 0.35 * ri * s, 220 + 0.92 * ri * c, 185 + 0.92 * ri * s); }).join('')}
      ${S.text(220, 189, 'p_i')} ${S.line(220, 185, 220 + ro, 185, 'd-dim')}
      ${S.text(220, 322, `r_i = ${lab(v.r_i * 1e3, 'mm')}   t = ${lab(v.t_w * 1e3, 'mm')}`)}
      ${S.line(400, 280, 600, 280, 'd-line')} ${S.line(400, 280, 400, 70, 'd-line')}
      ${S.path('M420 90 Q470 190 590 215', 'd-hazard')} ${S.text(596, 208, 'σ_θ', 'd-text', 'end')}
      ${S.path('M420 330 Q470 292 590 281', 'd-line')} ${S.text(596, 300, 'σ_r', 'd-text', 'end')}
      ${S.text(420, 60, 'bore', 'd-text d-small')} ${S.text(590, 60, 'outer', 'd-text d-small')} ${S.text(500, 350, 'radius')}
      ${S.text(320, 30, `p_i = ${lab(v.p_i / 1e5, 'bar')}   p_o = ${lab(v.p_o / 1e5, 'bar')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the strains on a thick-walled cylinder under internal pressure, compare them with Lamé\'s solution, and observe first yield and burst.',
    apparatus: ['Thick-walled test cylinder with closed ends, radius ratio 1.5–2.5', 'High-pressure hand pump or intensifier with a hydraulic fluid', 'Burst containment cell for destructive tests'],
    instruments: [{ name: 'Biaxial strain-gauge rosettes on the outer surface (and in the bore if accessible)', measures: 'Hoop and axial strain', range: '±5000 µε', resolution: '±1 µε' }, { name: 'Pressure transducer', measures: 'Internal pressure', range: '0–4000 bar', resolution: '±0.1 %' }, { name: 'Volume or stroke measurement of the pump', measures: 'Onset of gross yielding', range: '—', resolution: '—' }],
    procedure: ['Pressurise in steps within the elastic range, recording strains; convert to stress with Hooke\'s law for biaxial stress.', 'Continue until the pressure–strain curve departs from linearity (first yield at the bore).', 'In a containment cell, pressurise to burst and compare with the Faupel estimate.'],
    controls: ['Tensile test of the cylinder material for E, ν, yield and tensile strength', 'Unload from the elastic range and verify zero residual strain'],
    signatures: ['Outer-surface hoop stress equal to 2p/(K² − 1)', 'Outer-surface hoop stress twice the axial stress for closed ends', 'Burst pressure well above first-yield pressure for ductile material'],
    safety: ['Use liquid, never gas, as the pressurising medium', 'Remote operation and containment for burst tests', 'Bleed trapped air before pressurising'],
  },
  falsify: ['Outer-surface strains that disagree with Lamé\'s prediction in the elastic range by more than the measurement uncertainty.', 'First yield occurring at the outer surface rather than the bore under internal pressure.'],
  alternatives: [{ name: 'Autofrettage and compound cylinders', text: 'Residual compressive stress at the bore raises the elastic pressure range.' }, { name: 'Code design formulas', text: 'Pressure-vessel and pipeline codes use modified membrane formulas with design factors, weld efficiencies and corrosion allowances.' }, { name: 'External-pressure collapse', text: 'Under net external pressure failure is by elastic or plastic buckling, governed by ovality and D/t.' }],
  hazards: [{ hazard: 'Burst and fragment projection', cause: 'Over-pressure, wall loss by corrosion, material defects', mitigation: 'Relief devices, design factors, inspection, hydrostatic proof test' }, { hazard: 'Stored-energy release', cause: 'Compressed gas or trapped air during testing', mitigation: 'Hydraulic test medium, exclusion zones' }],
  standards: ['ASME Boiler and Pressure Vessel Code, Section VIII', 'EN 13445 (unfired pressure vessels)', 'ASME B31.3 (process piping) and B31.8 (gas transmission piping)', 'DNV-ST-F101 (submarine pipeline systems)'],
  limits: 'Long, straight, circular cylinder of homogeneous isotropic material in the elastic range, away from end closures, nozzles and supports. No thermal stress, bending, residual stress or buckling under external pressure. The burst estimate applies to ductile materials without defects.',
  numerics: { method: 'Closed-form Lamé solution; bisection for the first-yield pressure and the required thickness' },
  optimise: { objective: 'util', sense: 'min', vars: ['t_w'], note: 'Adding wall gives diminishing returns: the elastic bore stress cannot fall below the pressure itself, however thick the wall.' },
  inverse: { series: 'stress-wall', fit: ['p_i'] },
  extensions: ['Elastic–plastic analysis and autofrettage', 'Thermal stress from a through-wall temperature gradient', 'Collapse under external pressure with ovality'],
};

export default [shipResistance, shipStability, wavesMorison, catenaryMooring, riserViv, pipeConveying, onBottom, mudmat, consolidation, slopeStability, beamBending, columnBuckling, shearBuilding, fatigueMiner, pressureVessel];
