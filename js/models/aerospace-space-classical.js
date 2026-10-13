// Aerospace, space-flight and classical-mechanics models: wings, nozzles, rockets, orbit transfers,
// atmospheric entry, Kepler and three-body motion, projectiles, pendulums, oscillators, collisions
// and two classical thought experiments (Newton's cannonball, Galileo's falling bodies).
import { inp, asm, eq, scalar, line, motion, path3d, check, bench, svg, S, lab, N, R, C } from './kit.js';

const G0 = C.g_0;               // standard gravity, m/s²
const DEG = Math.PI / 180;
const val = (r, sym) => r.scalars.find(q => q.sym === sym).value;
const every = (n, max) => Math.max(1, Math.ceil(n / max));

// ------------------------------------------------------------------ shared numerical helpers
const rk4step = (f, t, y, h) => {
  const ax = (b, s) => y.map((x, i) => x + s * b[i]);
  const k1 = f(t, y), k2 = f(t + h / 2, ax(k1, h / 2)), k3 = f(t + h / 2, ax(k2, h / 2)), k4 = f(t + h, ax(k3, h));
  return y.map((x, i) => x + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]));
};
/**
 * Integrate y' = f(t, y) from t = 0 until gf(y) falls through zero (or tMax is reached), locate the
 * crossing with Newton steps on the event function, then resample the solution on nOut points.
 * gdot(y) is the time derivative of gf along the solution; when omitted it is formed by finite difference.
 * When gf is the minimum of several conditions, scale each to order one so that they are comparable.
 */
function toEvent(f, y0, tMax, gf, gdot, nOut = 300, o = {}) {
  const opt = { rtol: o.rtol ?? 1e-9, atol: o.atol ?? 1e-9, maxSteps: o.maxSteps ?? 60000 }, event = (t, y) => gf(y) < 0;
  const miss = () => { const s = N.rk45(f, y0, 0, tMax, nOut, opt); return { ...s, hit: false, tHit: s.t.length ? s.t[s.t.length - 1] : 0, yHit: s.final || y0 }; };
  // a cheap low-accuracy pass finds roughly when the event happens, so the accurate pass can be sampled finely
  const rough = N.rk45(f, y0, 0, tMax, 2, { rtol: 1e-5, atol: Math.max(opt.atol, 1e-7), maxSteps: opt.maxSteps, event });
  if (!rough.stopped) return miss();
  let s = N.rk45(f, y0, 0, Math.min(1.05 * rough.stopT, tMax), nOut, { ...opt, event });
  if (!s.stopped) s = N.rk45(f, y0, 0, tMax, nOut, { ...opt, event });
  if (!s.stopped) return miss();
  // Newton iteration on the event function, confined to the interval between the last sample and the stopping step
  let t = s.stopT, y = s.final, lo = s.t.length - 1;
  while (lo > 0 && s.t[lo] >= t) lo--;
  const tLo = s.t[lo] < t ? s.t[lo] : 0, tHi = t;
  for (let i = 0; i < 10; i++) {
    let gd;
    if (gdot) gd = gdot(y);
    else { const fy = f(t, y), h = 1e-6; gd = (gf(y.map((x, k) => x + h * fy[k])) - gf(y)) / h; }
    const dt = N.clamp(t - gf(y) / gd, tLo, tHi) - t;
    if (!Number.isFinite(dt) || dt === 0) break;
    y = rk4step(f, t, y, dt); t += dt;
    if (Math.abs(dt) < 1e-13 * Math.max(1, t)) break;
  }
  // keep the samples before the event and close the record with the event state itself
  let keep = s.t.length; while (keep > 0 && s.t[keep - 1] >= t) keep--;
  return { t: [...s.t.slice(0, keep), t], y: s.y.map((r, k) => [...r.slice(0, keep), y[k]]), hit: true, tHit: t, yHit: y };
}
/**
 * Adaptive Dormand–Prince RK45 on typed arrays for larger systems: f(t, y, dydt) writes the derivative in place.
 * Returns the state rows at nOut equally spaced times in [0, t1] (fewer if the step limit is reached).
 */
function dopri(f, y0, t1, nOut, { rtol = 1e-9, atol = 1e-12, maxSteps = 20000 } = {}) {
  const n = y0.length, y = Float64Array.from(y0), ys = new Float64Array(n), k = Array.from({ length: 7 }, () => new Float64Array(n));
  const A = [[1 / 5], [3 / 40, 9 / 40], [44 / 45, -56 / 15, 32 / 9], [19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729], [9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656], [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84]];
  const Cn = [1 / 5, 3 / 10, 4 / 5, 8 / 9, 1, 1];
  const E = [35 / 384 - 5179 / 57600, 0, 500 / 1113 - 7571 / 16695, 125 / 192 - 393 / 640, -2187 / 6784 + 92097 / 339200, 11 / 84 - 187 / 2100, -1 / 40];
  const tOut = N.linspace(0, t1, nOut), ts = [], rows = [];
  let t = 0, h = t1 / 200, io = 0, steps = 0;
  const rec = () => { while (io < nOut && tOut[io] <= t + 1e-13 * t1) { ts.push(tOut[io]); rows.push(Float64Array.from(y)); io++; } };
  rec(); f(t, y, k[0]);
  while (io < nOut && steps < maxSteps) {
    const cut = tOut[io] - t < h, hh = cut ? tOut[io] - t : h;
    for (let s = 0; s < 6; s++) {
      const a = A[s];
      for (let i = 0; i < n; i++) { let d = 0; for (let q = 0; q <= s; q++) d += a[q] * k[q][i]; ys[i] = y[i] + hh * d; }
      f(t + Cn[s] * hh, ys, k[s + 1]);
    }
    let err = 0;
    for (let i = 0; i < n; i++) { let e = 0; for (let q = 0; q < 7; q++) e += E[q] * k[q][i]; err = Math.max(err, Math.abs(hh * e) / (atol + rtol * Math.max(Math.abs(y[i]), Math.abs(ys[i])))); }
    steps++;
    if (!Number.isFinite(err) || hh < 1e-14 * t1) break;
    const fac = N.clamp(0.9 * Math.pow(Math.max(err, 1e-12), -0.2), 0.2, 5);
    if (err > 1) { h = hh * fac; continue; }
    t = cut ? tOut[io] : t + hh; y.set(ys); k[0].set(k[6]); rec();
    h = cut ? Math.max(h, hh * fac) : hh * fac;
  }
  return { t: ts, y: rows, steps, complete: io >= nOut };
}
/** Arithmetic–geometric mean; K(k) = π / (2·agm(1, √(1−k²))). */
const agm = (a, b) => { for (let i = 0; i < 60 && Math.abs(a - b) > 1e-16 * a; i++) [a, b] = [(a + b) / 2, Math.sqrt(a * b)]; return a; };
/** Fourth-order symplectic (Yoshida) composition of velocity-Verlet steps for q'' = acc(q); acc(q, out) writes in place. */
function yoshida4(acc, q0, v0, h, n, stride = 1) {
  const w1 = 1 / (2 - Math.cbrt(2)), w0 = -Math.cbrt(2) * w1, ws = [w1, w0, w1], m = q0.length;
  const q = Array.from(q0), v = Array.from(v0), a = new Array(m).fill(0);
  const t = [], Q = [], V = [];
  acc(q, a);
  for (let k = 0; k <= n; k++) {
    if (k % stride === 0 || k === n) { t.push(k * h); Q.push(q.slice()); V.push(v.slice()); }
    if (k === n) break;
    for (let s = 0; s < 3; s++) {
      const d = ws[s] * h;
      for (let j = 0; j < m; j++) { v[j] += 0.5 * d * a[j]; q[j] += d * v[j]; }
      acc(q, a);
      for (let j = 0; j < m; j++) v[j] += 0.5 * d * a[j];
    }
  }
  return { t, q: Q, v: V };
}
/** Classical RK4 for q'' = acc(q), same output layout as yoshida4 (used as the non-symplectic comparison). */
function rk4second(acc, q0, v0, h, n, stride = 1) {
  const m = q0.length, q = Array.from(q0), v = Array.from(v0), z = () => new Array(m).fill(0);
  const a1 = z(), a2 = z(), a3 = z(), a4 = z(), qq = z(), t = [], Q = [], V = [];
  for (let k = 0; k <= n; k++) {
    if (k % stride === 0 || k === n) { t.push(k * h); Q.push(q.slice()); V.push(v.slice()); }
    if (k === n) break;
    acc(q, a1);
    for (let j = 0; j < m; j++) qq[j] = q[j] + 0.5 * h * v[j];
    acc(qq, a2);
    for (let j = 0; j < m; j++) qq[j] = q[j] + 0.5 * h * v[j] + 0.25 * h * h * a1[j];
    acc(qq, a3);
    for (let j = 0; j < m; j++) qq[j] = q[j] + h * v[j] + 0.5 * h * h * a2[j];
    acc(qq, a4);
    for (let j = 0; j < m; j++) { q[j] += h * v[j] + h * h / 6 * (a1[j] + a2[j] + a3[j]); v[j] += h / 6 * (a1[j] + 2 * a2[j] + 2 * a3[j] + a4[j]); }
  }
  return { t, q: Q, v: V };
}
/** Least-squares slope of ys against xs. */
const slope = (xs, ys) => { const n = xs.length; if (n < 2) return 0; const mx = N.mean(xs), my = N.mean(ys); let sxy = 0, sxx = 0; for (let i = 0; i < n; i++) { sxy += (xs[i] - mx) * (ys[i] - my); sxx += (xs[i] - mx) ** 2; } return sxx > 0 ? sxy / sxx : 0; };
/**
 * Growth of the separation between twin trajectories before saturation: straight-line fits of ln(separation)
 * against t (exponential, chaotic) and against ln t (power law, regular). The motion is classed as chaotic
 * only when the exponential fit is the better one and spans at least three e-foldings.
 */
function growthFit(ts, sep) {
  const ix = sep.map((_, k) => k).filter(k => ts[k] > 0 && sep[k] > 0 && sep[k] < 0.1);
  if (ix.length < 6) return { lam: 0, power: 0, chaotic: false };
  const x = ix.map(k => ts[k]), y = ix.map(k => Math.log(sep[k])), my = N.mean(y);
  const fit = xs => { const b = slope(xs, y), mx = N.mean(xs); let e = 0; for (let i = 0; i < xs.length; i++) e += (y[i] - my - b * (xs[i] - mx)) ** 2; return [b, e]; };
  const [lam, eExp] = fit(x), [power, ePow] = fit(x.map(Math.log));
  return { lam, power, chaotic: eExp < ePow && lam * (x[x.length - 1] - x[0]) > 3 };   // exponential fit better, and at least e³ of growth
}
const GROWTH = ['No sustained exponential growth: consistent with regular (non-chaotic) motion over this interval', 'Exponential growth: the motion is chaotic over this interval'];
const circlePts = (r, n = 121) => N.linspace(0, 2 * Math.PI, n).map(th => [r * Math.cos(th), r * Math.sin(th)]);

// ------------------------------------------------------------------ 1. finite wing: lift, drag, performance
function wingState(v, a) {
  const atm = R.atmosphere(v.z), rho = a.isa ? atm.rho : 1.225;
  const M = v.V / atm.a, Mc = Math.min(M, 0.85);
  const a0 = a.incompressible ? v.a_0 : v.a_0 / Math.sqrt(1 - Mc * Mc);
  const e = a.oswald ? v.e_o : 1, K = 1 / (Math.PI * e * v.AR);
  const aw = a.lifting_line ? a0 / (1 + a0 * K) : a0;
  return { atm, rho, M, a0, e, K, aw };
}
const wing = {
  id: 'wing-lift-drag',
  title: 'Finite-wing lift, drag polar and level-flight performance',
  module: 2, klass: 'I', domains: ['aerospace'],
  keywords: ['lifting-line theory', 'drag polar', 'lift coefficient', 'induced drag', 'stall speed', 'lift-to-drag ratio', 'breguet range', 'aspect ratio', 'oswald efficiency', 'wing lift', 'wing', 'aerofoil', 'airfoil', 'angle of attack', 'lift', 'stall', 'glide ratio', 'power required', 'aircraft performance'],
  summary: 'Lift and drag of a finite wing from lifting-line theory and a parabolic drag polar, with stall speed, best lift-to-drag ratio, power required and Breguet range in the standard atmosphere.',
  background: [
    'A wing of finite span sheds trailing vortices that tilt the local flow downward. Prandtl\'s lifting-line theory shows that this downwash reduces the lift-curve slope below the two-dimensional section value and creates a drag force, the induced drag, proportional to the square of the lift coefficient and inversely proportional to aspect ratio.',
    'Adding the induced drag to a constant zero-lift (parasitic) drag coefficient gives the parabolic drag polar. Combined with the requirement that lift equals weight in level flight, the polar fixes the stall speed, the speed for minimum drag (maximum lift-to-drag ratio), the speed for minimum power and, through the Breguet relation, the cruise range.',
  ],
  phenomena: ['Circulation and lift', 'Trailing-vortex downwash', 'Induced drag', 'Parasitic (profile and friction) drag', 'Stall'],
  laws: ['momentum', 'newton2', 'mass', 'ideal_gas'],
  refs: ['Prandtl, L. (1921). Applications of modern hydrodynamics to aeronautics. NACA Report 116.', 'Glauert, H. (1926). The Elements of Aerofoil and Airscrew Theory. Cambridge University Press.', 'Abbott, I. H. & von Doenhoff, A. E. (1959). Theory of Wing Sections. Dover.', 'Anderson, J. D. (2017). Fundamentals of Aerodynamics, 6th ed., McGraw-Hill.', 'Anderson, J. D. (1999). Aircraft Performance and Design. McGraw-Hill.'],
  inputs: [
    inp('m', 'Aircraft mass', 'kg', 1100, { min: 50, max: 400000, aliases: ['mass', 'weight', 'all-up mass'], src: 'Four-seat light aircraft at maximum take-off mass' }),
    inp('S', 'Wing reference area', 'm^2', 16.2, { min: 0.5, max: 900, kind: 'geometry', aliases: ['wing area', 'reference area', 'planform area'] }),
    inp('AR', 'Aspect ratio (span² / area)', '1', 7.4, { min: 2, max: 40, kind: 'geometry', aliases: ['aspect ratio'] }),
    inp('a_0', 'Section lift-curve slope (per radian)', '1', 6.2832, { min: 4, max: 7, kind: 'fluid', aliases: ['lift slope', 'lift curve slope'], src: 'Thin-aerofoil theory gives 2π per radian; measured sections lie within about 10 % of it (Abbott & von Doenhoff)' }),
    inp('alpha_0', 'Zero-lift angle of attack', 'deg', -2, { min: -8, max: 2, kind: 'geometry', aliases: ['zero-lift angle'], src: 'Typical for a section with about 2 % camber' }),
    inp('alpha', 'Angle of attack', 'deg', 4, { min: -6, max: 22, aliases: ['angle of attack', 'incidence', 'aoa'] }),
    inp('e_o', 'Oswald span-efficiency factor', '1', 0.8, { min: 0.5, max: 1, kind: 'geometry', aliases: ['oswald', 'span efficiency'], src: 'Typical range 0.7–0.85 for conventional aircraft' }),
    inp('C_D0', 'Zero-lift drag coefficient', '1', 0.028, { min: 0.004, max: 0.15, kind: 'fluid', aliases: ['zero-lift drag', 'parasitic drag', 'cd0'], src: 'Fixed-gear light aircraft; clean jet transports are nearer 0.018' }),
    inp('C_Lmax', 'Maximum lift coefficient', '1', 1.5, { min: 0.6, max: 3.5, kind: 'fluid', aliases: ['maximum lift coefficient', 'clmax'], src: 'Unflapped wing of moderate aspect ratio' }),
    inp('V', 'True airspeed', 'm/s', 55, { min: 8, max: 250, aliases: ['airspeed', 'speed', 'velocity', 'cruise speed'] }),
    inp('z', 'Pressure altitude', 'm', 2000, { min: 0, max: 20000, kind: 'environment', aliases: ['altitude', 'flight level', 'height'] }),
    inp('zeta', 'Fuel mass fraction of take-off mass', '1', 0.12, { min: 0.01, max: 0.5, aliases: ['fuel fraction'] }),
    inp('eta_p', 'Propulsive (propeller) efficiency', '1', 0.8, { min: 0.3, max: 0.95, aliases: ['propeller efficiency', 'propulsive efficiency'] }),
    inp('c_b', 'Brake specific fuel consumption', 'g/kWh', 300, { min: 150, max: 700, aliases: ['bsfc', 'specific fuel consumption'], src: 'Spark-ignition aero piston engine in cruise' }),
    inp('c_T', 'Thrust specific fuel consumption', 'g/(kN s)', 17, { min: 8, max: 45, aliases: ['tsfc'], src: 'High-bypass turbofan in cruise, about 0.6 lb/(lbf h)' }),
  ],
  assumptions: [
    asm('lifting_line', 'The wing lift-curve slope is reduced by trailing-vortex downwash as given by lifting-line theory.', { why: 'Unswept wing of aspect ratio above about 4', alt: 'The wing behaves as an infinite-span section: the two-dimensional slope is used unchanged.' }),
    asm('oswald', 'Span loading is non-elliptic; its efficiency is the stated Oswald factor.', { why: 'Real planforms and fuselage interference', alt: 'Ideal elliptic loading: the span-efficiency factor is 1 (minimum possible induced drag).' }),
    asm('isa', 'Air density follows the ISO standard atmosphere at the stated altitude.', { why: 'Standard-day performance', alt: 'Sea-level standard density is used at every altitude, so the airspeed is read as equivalent airspeed.' }),
    asm('incompressible', 'Compressibility is neglected (low Mach number).', { why: 'Mach number below about 0.3', alt: 'The section lift slope is raised by the Prandtl–Glauert factor 1/√(1 − M²).' }),
    asm('prop', 'The aircraft is propeller-driven: fuel flow is proportional to shaft power.', { why: 'Piston or turboprop', alt: 'Jet aircraft: fuel flow is proportional to thrust, and range follows the jet form of the Breguet relation at the stated speed.' }),
  ],
  symbols: { a_w: ['Wing lift-curve slope (per radian)', '1'], a_c: ['Compressibility-corrected section slope', '1'], C_L: ['Lift coefficient', '1'], C_D: ['Drag coefficient', '1'], L: ['Lift', 'N'], D: ['Drag', 'N'], rho: ['Air density', 'kg/m^3'], rho_sl: ['Sea-level standard density', 'kg/m^3'], p_a: ['Ambient pressure', 'Pa'], T_a: ['Ambient temperature', 'K'], R_air: ['Specific gas constant of air', 'J/(kg K)'], M: ['Mach number', '1'], a_s: ['Speed of sound', 'm/s'], V_s: ['Stall speed', 'm/s'], LD: ['Lift-to-drag ratio in level flight', '1'], LD_max: ['Maximum lift-to-drag ratio', '1'], P_req: ['Power required for level flight', 'W'], R_b: ['Breguet range', 'm'], g: ['Standard gravity', 'm/s^2'] },
  equations: a => {
    const e = a.oswald ? 'e_o*' : '', a0 = a.incompressible ? 'a_0' : 'a_c';
    return [
      a.isa ? eq('rho', 'Air density', 'rho', 'p_a/(R_air*T_a)', { kind: 'closure', origin: 'Ideal-gas law with standard-atmosphere pressure and temperature', needs: ['isa'] })
        : eq('rho', 'Air density', 'rho', 'rho_sl', { kind: 'closure', origin: 'Sea-level standard value 1.225 kg/m³' }),
      ...(a.incompressible ? [] : [eq('mach', 'Mach number', 'M', 'V/a_s', { kind: 'definition' }), eq('pg', 'Prandtl–Glauert correction', 'a_c', 'a_0/sqrt(1 - min(M, 0.85)^2)', { kind: 'derived', origin: 'Linearised subsonic potential flow (Glauert 1928)', note: 'The Mach number in the correction is capped at 0.85, where the linear theory has already failed.' })]),
      a.lifting_line
        ? eq('slope', 'Finite-wing lift-curve slope', 'a_w', `${a0}/(1 + ${a0}/(pi*${e}AR))`, { kind: 'derived', origin: 'Prandtl lifting-line theory', needs: ['lifting_line'] })
        : eq('slope', 'Lift-curve slope', 'a_w', a0, { kind: 'closure', origin: 'Two-dimensional section value' }),
      eq('cl', 'Lift coefficient', 'C_L', 'max(-C_Lmax, min(C_Lmax, a_w*(alpha - alpha_0)))', { kind: 'derived', origin: 'Linear lift below stall, held at the maximum lift coefficient beyond it' }),
      eq('cd', 'Parabolic drag polar', 'C_D', `C_D0 + C_L^2/(pi*${e}AR)`, { kind: 'derived', origin: 'Induced drag of a lifting line plus constant parasitic drag' }),
      eq('lift', 'Lift', 'L', '0.5*rho*V^2*S*C_L', { kind: 'definition' }),
      eq('drag', 'Drag', 'D', '0.5*rho*V^2*S*C_D', { kind: 'definition' }),
      eq('vs', 'Stall speed', 'V_s', 'sqrt(2*m*g/(rho*S*C_Lmax))', { kind: 'derived', origin: 'Lift equals weight at maximum lift coefficient' }),
      eq('ldmax', 'Maximum lift-to-drag ratio', 'LD_max', `0.5*sqrt(pi*${e}AR/C_D0)`, { kind: 'derived', origin: 'Induced drag equals parasitic drag at minimum total drag' }),
      eq('preq', 'Power required in level flight', 'P_req', `0.5*rho*V^3*S*C_D0 + 2*(m*g)^2/(pi*${e}AR*rho*V*S)`, { kind: 'derived', origin: 'Drag times speed with lift equal to weight' }),
      eq('ld', 'Lift-to-drag ratio in level flight', 'LD', 'm*g*V/P_req', { kind: 'derived', origin: 'Weight over the drag in level flight at the stated speed' }),
      a.prop ? eq('range', 'Breguet range (propeller)', 'R_b', 'eta_p/(g*c_b)*LD*ln(1/(1 - zeta))', { kind: 'derived', origin: 'Breguet range equation', needs: ['prop'] })
        : eq('range', 'Breguet range (jet)', 'R_b', 'V/(g*c_T)*LD*ln(1/(1 - zeta))', { kind: 'derived', origin: 'Breguet range equation at constant speed and lift coefficient' }),
    ];
  },
  derivation: a => [
    { text: 'The bound vortex of the wing continues downstream as a trailing vortex sheet. At the wing it induces a downwash that reduces the effective angle of attack of every section by an induced angle.', tex: '\\alpha_{eff} = \\alpha - \\alpha_i,\\qquad \\alpha_i = \\frac{C_L}{\\pi e\\,AR}' },
    { text: 'Each section still obeys its two-dimensional lift law at the effective angle. Eliminating the induced angle gives the lift-curve slope of the whole wing.', tex: 'C_L = a_0(\\alpha-\\alpha_0-\\alpha_i)\\ \\Rightarrow\\ a = \\frac{a_0}{1 + a_0/(\\pi e\\,AR)}' },
    { text: 'Because the local lift vector is tilted back through the induced angle, a drag component appears even in inviscid flow. Adding the parasitic drag gives the polar.', tex: 'C_D = C_{D0} + \\frac{C_L^2}{\\pi e\\,AR}' },
    { text: 'In steady level flight lift equals weight, which fixes the lift coefficient at each speed. Drag is then the sum of a term growing as V² and a term falling as 1/V².', tex: 'D = \\tfrac12\\rho V^2 S\\,C_{D0} + \\frac{2W^2}{\\pi e\\,AR\\,\\rho V^2 S}' },
    { text: 'Drag is least where the two terms are equal, giving the maximum lift-to-drag ratio; the stall speed follows from the maximum lift coefficient.', tex: '\\left(\\frac{L}{D}\\right)_{max} = \\frac12\\sqrt{\\frac{\\pi e\\,AR}{C_{D0}}},\\qquad V_s = \\sqrt{\\frac{2W}{\\rho S\\,C_{L,max}}}' },
    { text: a.prop ? 'For a propeller aircraft fuel is burned in proportion to power. Integrating the distance flown per unit of fuel as the weight falls gives the Breguet range.' : 'For a jet fuel is burned in proportion to thrust. Integrating at constant speed and lift coefficient gives the jet form of the Breguet range.', tex: a.prop ? 'R = \\frac{\\eta_p}{g\\,c_b}\\,\\frac{L}{D}\\,\\ln\\frac{W_0}{W_1}' : 'R = \\frac{V}{g\\,c_T}\\,\\frac{L}{D}\\,\\ln\\frac{W_0}{W_1}' },
  ],
  solve(v, a) {
    const s = wingState(v, a), { rho, K, aw } = s, W = v.m * G0, q = 0.5 * rho * v.V ** 2;
    const CLlin = aw * (v.alpha - v.alpha_0), stalled = Math.abs(CLlin) > v.C_Lmax, CL = N.clamp(CLlin, -v.C_Lmax, v.C_Lmax);
    const CD = v.C_D0 + K * CL * CL, L = q * v.S * CL, D = q * v.S * CD;
    const dragAt = V => { const qq = 0.5 * rho * V * V; return qq * v.S * v.C_D0 + K * W * W / (qq * v.S); };
    const CLreq = W / (q * v.S), Dlev = dragAt(v.V), LD = W / Dlev;
    const Vs = Math.sqrt(2 * W / (rho * v.S * v.C_Lmax)), LDmax = 0.5 / Math.sqrt(K * v.C_D0), CLmd = Math.sqrt(v.C_D0 / K);
    const Vmd = Math.sqrt(2 * W / (rho * v.S * CLmd)), Vmp = Vmd / Math.pow(3, 0.25);
    const fuel = Math.log(1 / (1 - v.zeta));
    const range = a.prop ? v.eta_p / (G0 * v.c_b) * LD * fuel : v.V / (G0 * v.c_T) * LD * fuel;
    const rangeMax = a.prop ? v.eta_p / (G0 * v.c_b) * LDmax * fuel : Vmd / (G0 * v.c_T) * LDmax * fuel;
    const chord = Math.sqrt(v.S / v.AR), Re = rho * v.V * chord / s.atm.mu;
    const warnings = [];
    if (stalled) warnings.push('The linear lift law gives a lift coefficient beyond the stated maximum: the wing is stalled at this angle of attack. The lift coefficient has been held at its maximum; post-stall behaviour is not modelled.');
    if (CLreq > v.C_Lmax) warnings.push('Level flight at this speed would need a lift coefficient above the maximum: the speed is below the stall speed for this mass and altitude.');
    if (Vmd < Vs) warnings.push('The minimum-drag speed lies below the stall speed, so the best lift-to-drag ratio cannot be reached in steady flight.');
    if (!a.incompressible && s.M > 0.7) warnings.push('The Prandtl–Glauert correction loses accuracy above about Mach 0.7 and ignores wave drag; the Mach number used in the correction is capped at 0.85.');
    if (a.incompressible && s.M > 0.3) warnings.push('The Mach number exceeds 0.3; compressibility affects the lift slope and should not be neglected.');
    const al = N.linspace(-6, 22, 57), cut = x => N.clamp(x, -v.C_Lmax, v.C_Lmax);
    const cls = N.linspace(-0.4, v.C_Lmax, 60);
    const Vs2 = N.linspace(0.85 * Vs, Math.max(3 * Vmd, 1.2 * v.V), 90);
    return {
      scalars: [
        scalar('rho', 'Air density', rho, 'kg/m^3'), scalar('M', 'Mach number', s.M, '1'), scalar('Re', 'Reynolds number on the mean chord', Re, '1'),
        scalar('a_w', 'Wing lift-curve slope (per radian)', aw, '1'), scalar('C_L', 'Lift coefficient at the stated angle of attack', CL, '1', { note: stalled ? 'stalled' : 'attached flow' }),
        scalar('C_D', 'Drag coefficient', CD, '1'), scalar('C_Di', 'Induced drag coefficient', K * CL * CL, '1'),
        scalar('L', 'Lift', L, 'N', { show: 'kN' }), scalar('D', 'Drag', D, 'N', { show: 'kN' }), scalar('n', 'Load factor (lift / weight)', L / W, '1'),
        scalar('alpha_s', 'Stall angle of attack', v.alpha_0 + v.C_Lmax / aw, 'rad', { show: 'deg' }),
        scalar('alpha_lf', 'Angle of attack for level flight at this speed', v.alpha_0 + CLreq / aw, 'rad', { show: 'deg' }),
        scalar('C_Lreq', 'Lift coefficient for level flight at this speed', CLreq, '1'),
        scalar('V_s', 'Stall speed', Vs, 'm/s', { show: 'kn' }), scalar('LD', 'Lift-to-drag ratio in level flight', LD, '1'), scalar('LD_max', 'Maximum lift-to-drag ratio', LDmax, '1'),
        scalar('V_md', 'Minimum-drag speed', Vmd, 'm/s', { show: 'kn' }), scalar('V_mp', 'Minimum-power speed', Vmp, 'm/s', { show: 'kn' }),
        scalar('D_lf', 'Drag in level flight', Dlev, 'N'), scalar('P_req', 'Power required for level flight', Dlev * v.V, 'W', { show: 'kW' }),
        scalar('P_min', 'Minimum power required', dragAt(Vmp) * Vmp, 'W', { show: 'kW' }),
        scalar('R_b', 'Breguet range at this speed', range, 'm', { show: 'km' }), scalar('R_max', 'Breguet range at maximum lift-to-drag ratio', rangeMax, 'm', { show: 'km' }),
      ],
      series: [
        line('lift-curve', 'Lift curve', 'Angle of attack', 'deg', al, [{ label: 'Finite wing', data: al.map(x => cut(aw * (x * DEG - v.alpha_0))) }, { label: 'Two-dimensional section', data: al.map(x => cut(s.a0 * (x * DEG - v.alpha_0))), dash: true }], 'Lift coefficient', '–', { note: 'Held at the maximum lift coefficient beyond stall.' }),
        line('drag-polar', 'Drag polar', 'Lift coefficient', '–', cls, [{ label: 'Total drag coefficient', data: cls.map(c => v.C_D0 + K * c * c) }, { label: 'Induced part', data: cls.map(c => K * c * c), dash: true }], 'Drag coefficient', '–'),
        line('drag-speed', 'Drag in level flight', 'True airspeed', 'm/s', Vs2, [{ label: 'Total drag', data: Vs2.map(dragAt) }, { label: 'Parasitic', data: Vs2.map(V => 0.5 * rho * V * V * v.S * v.C_D0), dash: true }, { label: 'Induced', data: Vs2.map(V => K * W * W / (0.5 * rho * V * V * v.S)), dash: true }], 'Drag', 'N'),
        line('power-speed', 'Power required in level flight', 'True airspeed', 'm/s', Vs2, [{ label: 'Power required', data: Vs2.map(V => dragAt(V) * V / 1000) }], 'Power', 'kW'),
      ],
      checks: [
        check('Induced and parasitic drag equal at the minimum-drag speed', (K * CLmd * CLmd - v.C_D0) / v.C_D0, 1e-12, 'Condition for maximum lift-to-drag ratio'),
        check('Level-flight force balance', (0.5 * rho * v.V ** 2 * v.S * CLreq - W) / W, 1e-12, 'Lift at the level-flight lift coefficient against weight'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const s = wingState(v, a), W = v.m * G0, out = [];
    const drag = V => { const q = 0.5 * s.rho * V * V; return q * v.S * v.C_D0 + s.K * W * W / (q * v.S); };
    const Vmd = Math.sqrt(2 * W / (s.rho * v.S * Math.sqrt(v.C_D0 / s.K)));
    const Vn = N.golden(drag, 0.3 * Vmd, 4 * Vmd, 1e-10);
    out.push(bench('Numerically located minimum drag vs analytic maximum L/D', W / drag(Vn), 0.5 * Math.sqrt(Math.PI * s.e * v.AR / v.C_D0), 'Closed form (L/D)max = ½√(π e AR / C_D0)', 1e-9));
    const Vp = N.golden(V => drag(V) * V, 0.3 * Vmd, 4 * Vmd, 1e-10);
    out.push(bench('Numerically located minimum power vs analytic value', drag(Vp) * Vp, W * (Vmd / Math.pow(3, 0.25)) / (Math.sqrt(3) / 2 * val(wing.solve(v, a), 'LD_max')), 'Minimum power at C_L = √(3 π e AR C_D0), where L/D = (√3/2)(L/D)max', 1e-9));
    const r = wing.solve({ ...v, a_0: 2 * Math.PI }, { ...a, oswald: false, incompressible: true, lifting_line: true });
    out.push(bench('Lift slope of an elliptic wing with a thin-aerofoil section', val(r, 'a_w'), 2 * Math.PI * v.AR / (v.AR + 2), 'Lifting-line result a = 2π AR/(AR + 2)', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    const al = N.clamp(v.alpha / DEG, -6, 22), c = Math.cos(-al * DEG), s = Math.sin(-al * DEG), cx = 300, cy = 200;
    const pt = (x, y) => `${(cx + x * c - y * s).toFixed(1)} ${(cy + x * s + y * c).toFixed(1)}`;
    return svg(`
      ${S.path(`M${pt(-130, 0)} Q${pt(-110, -42)} ${pt(-20, -34)} Q${pt(80, -18)} ${pt(150, 0)} Q${pt(40, 10)} ${pt(-100, 12)} Q${pt(-132, 12)} ${pt(-130, 0)} Z`, 'd-body')}
      ${S.arrow(40, 200, 150, 200)} ${S.text(95, 190, `V = ${lab(v.V, 'm/s')}`)}
      ${S.line(170, 200, 460, 200, 'd-dim')} ${S.text(520, 204, `α = ${lab(al, '°')}`, 'd-text', 'start')}
      ${S.arrow(300, 190, 300, 70)} ${S.text(312, 76, 'lift L', 'd-text', 'start')}
      ${S.arrow(330, 200, 430, 200, 'd-arrow d-hazard')} ${S.text(436, 222, 'drag D', 'd-text', 'start')}
      ${S.arrow(300, 215, 300, 310)} ${S.text(312, 306, `weight ${lab(v.m * G0 / 1000, 'kN')}`, 'd-text', 'start')}
      ${S.path('M470 150 q22 10 0 20 q-22 10 0 20', 'd-line')} ${S.text(500, 150, 'trailing vortices', 'd-text d-small', 'start')}
      ${S.text(320, 36, `S = ${lab(v.S, 'm²')}   AR = ${lab(v.AR)}   altitude ${lab(v.z, 'm')}`)}
      ${S.text(320, 345, `C_D = C_D0 + C_L² / (π e AR)`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the lift curve and drag polar of a finite-span wing model in a wind tunnel and compare the slope, induced-drag factor and stall with the lifting-line predictions.',
    apparatus: ['Low-speed closed-return wind tunnel with a test section at least 1.5 spans wide', 'Rectangular or tapered wing model of known section, with interchangeable tips to vary aspect ratio', 'Turntable or sting with remotely set incidence', 'Six-component force balance'],
    instruments: [{ name: 'Strain-gauge force balance', measures: 'Lift, drag and pitching moment', range: '0–500 N', resolution: '±0.1 % of full scale' }, { name: 'Pitot-static probe with differential transducer', measures: 'Dynamic pressure', range: '0–2.5 kPa', resolution: '±0.25 %' }, { name: 'Digital inclinometer', measures: 'Angle of attack', range: '−10° to 25°', resolution: '±0.05°' }, { name: 'Barometer and thermometer', measures: 'Air density', range: 'ambient', resolution: '±0.1 %' }],
    procedure: ['Measure tare and interference loads with the model removed.', 'At fixed dynamic pressure step the incidence from −6° to beyond stall in 1° increments, then back down to detect hysteresis.', 'Repeat at two further aspect ratios.', 'Apply blockage and lift-interference corrections, then plot C_L against α and C_D against C_L².'],
    controls: ['Repeat at a second Reynolds number to separate viscous effects on C_D0 and C_Lmax', 'Two-dimensional run with end plates to obtain the section slope a₀ directly'],
    signatures: ['C_D linear in C_L² with slope 1/(π e AR)', 'Lift-curve slope falling with aspect ratio as a₀/(1 + a₀/(π e AR))', 'Abrupt loss of linearity at the stall angle'],
    safety: ['Secure the model and balance against flutter and divergence before raising speed', 'Keep clear of the fan and diffuser; observe the tunnel maximum-speed limit for the model load'],
  },
  falsify: ['A measured induced-drag factor below 1/(π AR) for a planar wing, which would beat the elliptic-loading minimum.', 'A lift-curve slope that does not fall as aspect ratio is reduced.', 'Minimum drag in level flight occurring where induced and parasitic drag are clearly unequal while the polar remains parabolic.'],
  alternatives: [{ name: 'Helmbold and DATCOM slope formulae', text: 'For low aspect ratio or swept wings the lifting-line slope is replaced by a = 2π AR / (2 + √(4 + AR²(1 + tan²Λ − M²)/κ²)).' }, { name: 'Vortex-lattice and panel methods', text: 'Resolve span loading, sweep, twist and wing–body interference numerically instead of assuming a single efficiency factor.' }, { name: 'Non-parabolic polar', text: 'Cambered sections have minimum drag at a non-zero lift coefficient: C_D = C_Dmin + K (C_L − C_L0)².' }],
  hazards: [{ hazard: 'Stall and loss of control', cause: 'Flight below the stall speed or abrupt increase in load factor', mitigation: 'Stall-warning margin, training, and speed margins of at least 1.3 V_s on approach' }, { hazard: 'Structural overload', cause: 'Load factor above the design limit at high speed', mitigation: 'Observe the manoeuvring speed and the flight envelope' }],
  standards: ['ISO 2533:1975 (Standard Atmosphere)', 'EASA CS-23 (normal-category aeroplanes)', 'FAA 14 CFR Part 23 (airworthiness standards: normal category airplanes)'],
  limits: 'Unswept or mildly swept wings of aspect ratio above about 4, attached flow below stall, Mach number below about 0.7 with the compressibility correction and below 0.3 without it. Constant zero-lift drag coefficient; no wave drag, flap, ground-effect or propeller-slipstream effects. Standard atmosphere to 20 km.',
  numerics: { method: 'Closed-form algebraic relations; golden-section search for the benchmark extrema' },
  optimise: { objective: 'R_b', sense: 'max', vars: ['V'], note: 'For a propeller aircraft the range peaks at the minimum-drag speed.' },
  inverse: { series: 'drag-polar', fit: ['C_D0', 'e_o'] },
  extensions: ['Sweep and taper through a vortex-lattice span loading', 'Climb, turn and glide performance from the same polar', 'Wave drag and drag-divergence Mach number for transonic cruise'],
};

// ------------------------------------------------------------------ 2. nozzle flow and normal shocks
const isenT = (M, g) => 1 + (g - 1) / 2 * M * M;                       // T0/T
const isenP = (M, g) => Math.pow(isenT(M, g), g / (g - 1));            // p0/p
const areaMach = (M, g) => Math.pow(2 / (g + 1) * isenT(M, g), (g + 1) / (2 * (g - 1))) / M; // A/A*
/**
 * Invert the area–Mach relation. In the variables (ln M, ln A/A*) each branch is convex and monotonic,
 * so Newton's method started from the far end of the branch converges monotonically.
 */
function machFromArea(ar, g, supersonic) {
  if (!(ar > 1 + 1e-13)) return 1;
  const lo = 1e-9, target = Math.log(ar);
  if (!supersonic && ar >= areaMach(lo, g)) return areaMach(lo, g) * lo / ar;   // A/A* → const/M as M → 0
  let x = Math.log(supersonic ? 500 : lo);
  for (let i = 0; i < 80; i++) {
    const M = Math.exp(x), dx = (Math.log(areaMach(M, g)) - target) * isenT(M, g) / (M * M - 1);
    x -= dx;
    if (Math.abs(dx) < 1e-15) break;
  }
  return Math.exp(x);
}
function normalShock(M1, g) {
  const m2 = M1 * M1, p = 1 + 2 * g / (g + 1) * (m2 - 1), r = (g + 1) * m2 / ((g - 1) * m2 + 2);
  const M2 = Math.sqrt((1 + (g - 1) / 2 * m2) / (g * m2 - (g - 1) / 2));
  return { p, r, T: p / r, M2, p0: isenP(M2, g) / isenP(M1, g) * p };
}
const NOZ_REGIMES = ['No flow (back pressure not below stagnation pressure)', 'Subsonic throughout (not choked)', 'Choked, normal shock in the diverging section', 'Choked, over-expanded supersonic exit', 'Choked, ideally expanded', 'Choked, under-expanded', 'Choked converging nozzle'];
const CONTRACTION = 3; // inlet-to-throat area ratio used for the plotted contour
function nozzleFlow(v, a) {
  const g = v.gamma, eps = a.cd_nozzle ? v.eps : 1, Ae = eps * v.A_t, Cd = a.cd_unity ? 1 : v.C_d, pr = v.p_b / v.p_0;
  const Msup = machFromArea(eps, g, true), Msub = machFromArea(eps, g, false);
  const pSub = 1 / isenP(Msub, g), pSup = 1 / isenP(Msup, g), pNse = pSup * normalShock(Msup, g).p;
  let regime, Me, p0r = 1, As = null, sh = null, astar = 1;
  if (pr >= 1) { regime = 0; Me = 0; astar = 0; }
  else if (pr > pSub) { regime = 1; Me = Math.sqrt(2 / (g - 1) * (Math.pow(pr, -(g - 1) / g) - 1)); astar = eps / areaMach(Math.max(Me, 1e-12), g); }
  else if (a.shock && eps > 1 + 1e-9 && pr > pNse) {
    regime = 2;
    const exitP = A => { const s = normalShock(machFromArea(A, g, true), g); return s.p0 / isenP(machFromArea(eps * s.p0, g, false), g); };
    try { As = N.bisect(A => exitP(A) - pr, 1, eps, 1e-13); } catch { As = pr > 0.5 * (pSub + pNse) ? 1 : eps; }
    sh = normalShock(machFromArea(As, g, true), g); p0r = sh.p0; Me = machFromArea(eps * sh.p0, g, false);
  } else { Me = Msup; regime = eps <= 1 + 1e-9 ? 6 : Math.abs(pr - pSup) <= 1e-6 * pSup ? 4 : pr > pSup ? 3 : 5; }
  const Te = v.T_0 / isenT(Me, g), pe = regime === 0 ? v.p_b : v.p_0 * p0r / isenP(Me, g), rhoE = pe / (v.R_g * Te), Ve = Me * Math.sqrt(g * v.R_g * Te);
  const choked = regime >= 2;
  const mIdeal = choked ? v.A_t * v.p_0 * Math.sqrt(g / (v.R_g * v.T_0)) * Math.pow(2 / (g + 1), (g + 1) / (2 * (g - 1))) : rhoE * Ve * Ae;
  const mdot = Cd * mIdeal, lam = a.quasi1d ? 1 : (1 + Math.cos(v.theta_d)) / 2;
  const F = lam * mdot * Ve + (pe - v.p_b) * Ae;
  return { g, eps, Ae, Cd, pr, Msup, Msub, pSub, pSup, pNse, regime, Me, p0r, As, sh, astar, Te, pe, rhoE, Ve, mIdeal, mdot, lam, F, choked };
}
const nozzle = {
  id: 'compressible-nozzle-shock',
  title: 'Converging–diverging nozzle flow and normal shocks',
  module: 2, klass: 'I', domains: ['aerospace', 'cfd', 'thermal'],
  keywords: ['converging-diverging nozzle', 'de laval nozzle', 'normal shock', 'area-mach relation', 'isentropic flow', 'choked flow', 'supersonic nozzle', 'compressible flow', 'nozzle', 'shock wave', 'mach number', 'back pressure', 'over-expanded', 'under-expanded', 'thrust coefficient', 'supersonic'],
  summary: 'Quasi-one-dimensional isentropic flow through a converging–diverging nozzle with normal-shock relations: operating regime, Mach and pressure distributions, mass flow and thrust.',
  background: [
    'In steady adiabatic frictionless flow of a perfect gas the stagnation temperature and pressure are constant, and the local state depends only on the Mach number. Conservation of mass then links the Mach number to the duct area through the area–Mach relation, which has a subsonic and a supersonic root for every area larger than the sonic throat.',
    'Which root is realised depends on the back pressure. As it is lowered the nozzle first behaves as a venturi, then chokes; a normal shock appears in the diverging section and moves to the exit; below that the exit flow is supersonic and adjusts to the surroundings through oblique shocks or expansion fans outside the nozzle. Across a normal shock the Rankine–Hugoniot conditions give the jump in pressure, density and Mach number and the loss of stagnation pressure.',
  ],
  phenomena: ['Isentropic expansion', 'Choking at the sonic throat', 'Normal shock wave', 'Over- and under-expansion', 'Momentum and pressure thrust'],
  laws: ['mass', 'momentum', 'energy', 'second', 'ideal_gas'],
  refs: ['Ames Research Staff (1953). Equations, tables, and charts for compressible flow. NACA Report 1135.', 'Shapiro, A. H. (1953). The Dynamics and Thermodynamics of Compressible Fluid Flow, Vol. 1. Ronald Press.', 'Liepmann, H. W. & Roshko, A. (1957). Elements of Gasdynamics. Wiley.', 'Anderson, J. D. (2003). Modern Compressible Flow: With Historical Perspective, 3rd ed., McGraw-Hill.', 'Sutton, G. P. & Biblarz, O. (2017). Rocket Propulsion Elements, 9th ed., Wiley.', 'Malina, F. J. (1940). Characteristics of the rocket motor unit based on the theory of perfect gases. J. Franklin Institute 230, 433–454.'],
  inputs: [
    inp('p_0', 'Stagnation (chamber) pressure', 'bar', 10, { min: 1.05, max: 300, aliases: ['stagnation pressure', 'chamber pressure', 'total pressure', 'reservoir pressure'] }),
    inp('T_0', 'Stagnation (chamber) temperature', 'K', 300, { min: 150, max: 3800, aliases: ['stagnation temperature', 'chamber temperature', 'total temperature'] }),
    inp('p_b', 'Back (ambient) pressure', 'bar', 1.01325, { min: 0.0001, max: 300, kind: 'environment', aliases: ['back pressure', 'ambient pressure', 'exit pressure'] }),
    inp('gamma', 'Ratio of specific heats', '1', 1.4, { min: 1.1, max: 1.67, kind: 'fluid', aliases: ['gamma', 'specific heat ratio', 'heat capacity ratio'], src: 'Air at moderate temperature' }),
    inp('R_g', 'Specific gas constant', 'J/(kg K)', 287.05, { min: 100, max: 4200, kind: 'fluid', aliases: ['gas constant'], src: 'Dry air, ISO 2533' }),
    inp('A_t', 'Throat area', 'cm^2', 10, { min: 0.01, max: 20000, kind: 'geometry', aliases: ['throat area', 'throat'] }),
    inp('eps', 'Exit-to-throat area ratio', '1', 2, { min: 1.02, max: 100, kind: 'geometry', aliases: ['area ratio', 'expansion ratio'] }),
    inp('L', 'Nozzle length', 'm', 0.3, { min: 0.01, max: 10, kind: 'geometry', aliases: ['length', 'nozzle length'] }),
    inp('M_1', 'Mach number ahead of a normal shock (calculator)', '1', 2, { min: 1.01, max: 10, aliases: ['upstream mach', 'shock mach', 'mach'] }),
    inp('C_d', 'Discharge coefficient', '1', 0.98, { min: 0.8, max: 1, kind: 'fluid', aliases: ['discharge coefficient'], src: 'Well-rounded throat at high Reynolds number' }),
    inp('theta_d', 'Divergence half-angle of a conical nozzle', 'deg', 15, { min: 0, max: 40, kind: 'geometry', aliases: ['half-angle', 'divergence angle', 'cone angle'] }),
  ],
  assumptions: [
    asm('cd_nozzle', 'The nozzle has a diverging section downstream of the throat.', { why: 'De Laval nozzle', alt: 'Converging nozzle only: the exit plane is the throat and the area ratio is 1.' }),
    asm('shock', 'A normal shock stands in the diverging section whenever the back pressure requires one.', { why: 'Physical response to back pressure', alt: 'The shock-free supersonic branch is followed to the exit whatever the back pressure (an idealisation valid only when the jet separates outside the nozzle).' }),
    asm('quasi1d', 'The exit flow is uniform and axial.', { why: 'Contoured (bell) nozzle', alt: 'Conical nozzle: the momentum thrust is reduced by the divergence factor λ = (1 + cos θ)/2.' }),
    asm('cd_unity', 'Boundary layers do not reduce the mass flow (discharge coefficient of 1).', { why: 'Ideal inviscid flow', alt: 'The mass flow is the ideal value times the stated discharge coefficient.' }),
  ],
  symbols: { M: ['Local Mach number', '1'], T: ['Static temperature', 'K'], p: ['Static pressure', 'Pa'], A: ['Local area', 'm^2'], A_star: ['Sonic (critical) area', 'm^2'], A_e: ['Exit area', 'm^2'], mdot: ['Mass flow rate', 'kg/s'], mdot_ch: ['Choked ideal mass flow', 'kg/s'], mdot_sub: ['Ideal mass flow of an exit plane at the back pressure', 'kg/s'], p_crit: ['Critical (sonic) pressure', 'Pa'], p_1: ['Pressure ahead of the shock', 'Pa'], p_2: ['Pressure behind the shock', 'Pa'], rho_1: ['Density ahead of the shock', 'kg/m^3'], rho_2: ['Density behind the shock', 'kg/m^3'], M_2: ['Mach number behind the shock', '1'], F: ['Thrust', 'N'], V_e: ['Exit velocity', 'm/s'], p_e: ['Exit-plane pressure', 'Pa'], T_e: ['Exit temperature', 'K'], M_e: ['Exit Mach number', '1'], lambda_d: ['Divergence factor', '1'] },
  equations: a => [
    eq('ien', 'Energy (stagnation temperature)', 'T_0/T', '1 + (gamma - 1)/2*M^2', { kind: 'law', origin: 'Steady adiabatic energy equation for a perfect gas' }),
    eq('isen', 'Isentropic pressure ratio', 'p_0/p', '(1 + (gamma - 1)/2*M^2)^(gamma/(gamma - 1))', { kind: 'law', origin: 'Second law with zero entropy change' }),
    ...(a.cd_nozzle ? [eq('area', 'Area–Mach relation', 'A/A_star', '1/M*(2/(gamma + 1)*(1 + (gamma - 1)/2*M^2))^((gamma + 1)/(2*(gamma - 1)))', { kind: 'derived', origin: 'Continuity with isentropic relations' }), eq('ae', 'Exit area', 'A_e', 'eps*A_t', { kind: 'definition' })] : [eq('ae', 'Exit area', 'A_e', 'A_t', { kind: 'definition' })]),
    eq('pcrit', 'Critical (sonic) pressure', 'p_crit', 'p_0*(2/(gamma + 1))^(gamma/(gamma - 1))', { kind: 'derived', origin: 'Isentropic pressure ratio at M = 1' }),
    eq('mch', 'Choked ideal mass flow', 'mdot_ch', 'A_t*p_0*sqrt(gamma/(R_g*T_0))*(2/(gamma + 1))^((gamma + 1)/(2*(gamma - 1)))', { kind: 'derived', origin: 'Sonic conditions at the throat' }),
    eq('msub', 'Ideal mass flow of an exit plane at the back pressure', 'mdot_sub', 'A_e*p_0*sqrt(2*gamma/((gamma - 1)*R_g*T_0)*max((p_b/p_0)^(2/gamma) - (p_b/p_0)^((gamma + 1)/gamma), 0))', { kind: 'derived', origin: 'Continuity with isentropic expansion from stagnation to the back pressure (Saint-Venant and Wantzel)', note: 'Zero when the back pressure is not below the stagnation pressure: there is then no flow.' }),
    eq('mdot', 'Mass flow', 'mdot', `${a.cd_unity ? '' : 'C_d*'}ifpos(p_b - p_crit, min(mdot_ch, mdot_sub), mdot_ch)`, { kind: 'derived', origin: 'Choking limit on the subsonic exit-plane flow', note: 'While the throat is subsonic the exit pressure equals the back pressure and the exit-plane value, which is then the smaller, applies. Once the throat is sonic the flow is fixed at the choked value however far the back pressure is lowered.' }),
    ...(a.shock ? [
      eq('sp', 'Shock pressure ratio', 'p_2/p_1', '1 + 2*gamma/(gamma + 1)*(M_1^2 - 1)', { kind: 'law', origin: 'Rankine–Hugoniot jump conditions', needs: ['shock'] }),
      eq('sr', 'Shock density ratio', 'rho_2/rho_1', '(gamma + 1)*M_1^2/((gamma - 1)*M_1^2 + 2)', { kind: 'law', origin: 'Rankine–Hugoniot jump conditions', needs: ['shock'] }),
      eq('sm', 'Mach number behind the shock', 'M_2^2', '(1 + (gamma - 1)/2*M_1^2)/(gamma*M_1^2 - (gamma - 1)/2)', { kind: 'law', origin: 'Rankine–Hugoniot jump conditions', needs: ['shock'] }),
    ] : []),
    eq('ve', 'Exit velocity', 'V_e', 'M_e*sqrt(gamma*R_g*T_e)', { kind: 'definition' }),
    ...(a.quasi1d ? [eq('thrust', 'Thrust', 'F', 'mdot*V_e + (p_e - p_b)*A_e', { kind: 'law', origin: 'Momentum balance on the nozzle', needs: ['quasi1d'] })]
      : [eq('lam', 'Divergence factor', 'lambda_d', '(1 + cos(theta_d))/2', { kind: 'derived', origin: 'Integration of axial momentum over a spherical exit cap (Malina 1940)' }), eq('thrust', 'Thrust', 'F', 'lambda_d*mdot*V_e + (p_e - p_b)*A_e', { kind: 'law', origin: 'Momentum balance on the nozzle' })]),
  ],
  derivation: a => [
    { text: 'With no heat transfer or shaft work the stagnation enthalpy is constant; for a perfect gas this fixes the static temperature at each Mach number.', tex: '\\frac{T_0}{T} = 1 + \\frac{\\gamma-1}{2}M^2' },
    { text: 'If the flow is also frictionless it is isentropic, so pressure follows temperature.', tex: '\\frac{p_0}{p} = \\left(1 + \\frac{\\gamma-1}{2}M^2\\right)^{\\gamma/(\\gamma-1)}' },
    { text: 'Continuity ρuA = const, written with these relations and referred to the section where M = 1, gives the area–Mach relation. It has a minimum at M = 1: sonic flow can occur only at a throat.', tex: '\\frac{A}{A^*} = \\frac{1}{M}\\left[\\frac{2}{\\gamma+1}\\left(1+\\frac{\\gamma-1}{2}M^2\\right)\\right]^{\\frac{\\gamma+1}{2(\\gamma-1)}}' },
    { text: 'Once the throat is sonic the mass flow depends only on stagnation conditions and throat area: the nozzle is choked.', tex: '\\dot m = A_t\\,p_0\\sqrt{\\frac{\\gamma}{R\\,T_0}}\\left(\\frac{2}{\\gamma+1}\\right)^{\\frac{\\gamma+1}{2(\\gamma-1)}}' },
    { text: 'At higher back pressures the throat stays subsonic, the exit pressure equals the back pressure and the mass flow is the exit-plane value, which falls to zero as the back pressure rises to the stagnation pressure.', tex: '\\dot m = A_e\\,p_0\\sqrt{\\frac{2\\gamma}{(\\gamma-1)R\\,T_0}\\left[\\left(\\frac{p_b}{p_0}\\right)^{2/\\gamma}-\\left(\\frac{p_b}{p_0}\\right)^{(\\gamma+1)/\\gamma}\\right]}' },
    ...(a.shock ? [{ text: 'Mass, momentum and energy conserved across a thin discontinuity give the normal-shock jump conditions. Entropy rises, so stagnation pressure falls and the sonic area grows in proportion.', tex: '\\frac{p_2}{p_1} = 1+\\frac{2\\gamma}{\\gamma+1}(M_1^2-1),\\qquad M_2^2 = \\frac{1+\\frac{\\gamma-1}{2}M_1^2}{\\gamma M_1^2-\\frac{\\gamma-1}{2}},\\qquad \\frac{A_2^*}{A_1^*} = \\frac{p_{01}}{p_{02}}' }] : []),
    { text: 'A momentum balance on a control volume around the nozzle gives the thrust as momentum flux plus the pressure imbalance on the exit plane.', tex: a.quasi1d ? 'F = \\dot m\\,V_e + (p_e - p_b)A_e' : 'F = \\lambda\\,\\dot m\\,V_e + (p_e - p_b)A_e,\\qquad \\lambda = \\tfrac12(1+\\cos\\theta)' },
  ],
  solve(v, a) {
    const f = nozzleFlow(v, a), { g, eps } = f, sk = normalShock(v.M_1, g);
    const xt = a.cd_nozzle ? v.L / 3 : v.L, re = Math.sqrt(eps), ri = Math.sqrt(CONTRACTION);
    const blend = (r0, r1, s) => r0 + (r1 - r0) * (1 - Math.cos(Math.PI * s)) / 2;
    const arOf = x => (x <= xt ? blend(ri, 1, x / xt) : blend(1, re, (x - xt) / (v.L - xt))) ** 2;
    const xs = N.linspace(0, v.L, 161);
    const local = x => {
      const ar = arOf(x), up = x <= xt;
      if (f.regime === 0) return [0, 1];
      if (f.regime === 1) return [machFromArea(ar / f.astar, g, false), 1];
      if (up) return [machFromArea(ar, g, false), 1];
      if (f.regime === 2 && ar >= f.As) return [machFromArea(ar * f.p0r, g, false), f.p0r];
      return [machFromArea(ar, g, true), 1];
    };
    const prof = xs.map(local), Mx = prof.map(q => q[0]), px = prof.map(q => q[1] / isenP(q[0], g));
    const xShock = f.regime === 2 ? xt + (v.L - xt) * Math.acos(N.clamp(1 - 2 * (Math.sqrt(f.As) - 1) / Math.max(re - 1, 1e-12), -1, 1)) / Math.PI : NaN;
    const pbs = N.linspace(0, 1, 41), Fs = pbs.map(q => nozzleFlow({ ...v, p_b: Math.max(q, 1e-6) * v.p_0 }, a).F);
    const M1s = N.linspace(1, 5, 81), shs = M1s.map(M => normalShock(M, g));
    const u1 = v.M_1, u2 = sk.M2 * Math.sqrt(sk.T); // velocities in units of the upstream sound speed
    const warnings = [];
    if (f.regime === 0) warnings.push('The back pressure is not below the stagnation pressure, so there is no flow through the nozzle; reverse flow is not modelled.');
    if (f.regime === 3 && f.pe < 0.35 * v.p_b) warnings.push('The exit pressure is well below ambient: in practice the jet separates from the wall inside the nozzle (Summerfield criterion, exit pressure below roughly 0.35–0.4 of ambient), which the model does not capture.');
    if (!a.shock && eps > 1 + 1e-9 && f.pr >= f.pNse && f.pr < f.pSub) warnings.push('With the shock switched off the supersonic branch is forced to the exit even though this back pressure would place a normal shock inside or at the exit of the nozzle.');
    return {
      scalars: [
        scalar('regime', 'Operating regime', f.regime, '1', { text: NOZ_REGIMES[f.regime] }),
        scalar('mdot', 'Mass flow rate', f.mdot, 'kg/s'), scalar('M_e', 'Exit Mach number', f.Me, '1'), scalar('p_e', 'Exit-plane pressure', f.pe, 'Pa', { show: 'bar' }),
        scalar('T_e', 'Exit temperature', f.Te, 'K'), scalar('V_e', 'Exit velocity', f.Ve, 'm/s'), scalar('F', 'Thrust', f.F, 'N', { show: 'kN' }),
        scalar('I_sp', 'Specific impulse', f.mdot > 0 ? f.F / (f.mdot * G0) : 0, 's'), scalar('C_F', 'Thrust coefficient F/(p₀ A_t)', f.F / (v.p_0 * v.A_t), '1'),
        scalar('p_des', 'Design back pressure (ideal expansion)', f.pSup * v.p_0, 'Pa', { show: 'bar' }),
        scalar('p_ch', 'Back pressure below which the throat is choked', f.pSub * v.p_0, 'Pa', { show: 'bar' }),
        scalar('p_nse', 'Back pressure placing a normal shock at the exit', f.pNse * v.p_0, 'Pa', { show: 'bar' }),
        scalar('M_des', 'Design exit Mach number', f.Msup, '1'),
        scalar('x_s', 'Shock position from the inlet', xShock, 'm', { text: f.regime === 2 ? undefined : 'No shock inside the nozzle' }),
        scalar('M_s', 'Mach number just ahead of the nozzle shock', f.regime === 2 ? machFromArea(f.As, g, true) : NaN, '1', { text: f.regime === 2 ? undefined : 'No shock inside the nozzle' }),
        scalar('p_ratio', 'Normal shock at M₁: static pressure ratio p₂/p₁', sk.p, '1'), scalar('rho_ratio', 'Normal shock at M₁: density ratio ρ₂/ρ₁', sk.r, '1'),
        scalar('T_ratio', 'Normal shock at M₁: temperature ratio T₂/T₁', sk.T, '1'), scalar('M_2', 'Normal shock at M₁: downstream Mach number', sk.M2, '1'),
        scalar('p0_ratio', 'Normal shock at M₁: stagnation pressure ratio p₀₂/p₀₁', sk.p0, '1'), scalar('A_ratio', 'Area ratio A/A* at M₁', areaMach(v.M_1, g), '1'),
        scalar('ds', 'Normal shock at M₁: entropy rise', -v.R_g * Math.log(sk.p0), 'J/(kg K)'),
      ],
      series: [
        line('mach', 'Mach number along the nozzle', 'Distance from inlet', 'm', xs, [{ label: 'Mach number', data: Mx }, { label: 'Sonic', data: xs.map(() => 1), dash: true }], 'Mach number', '–'),
        line('pressure', 'Static pressure along the nozzle', 'Distance from inlet', 'm', xs, [{ label: 'p / p₀', data: px }, { label: 'Back pressure / p₀', data: xs.map(() => Math.min(f.pr, 1)), dash: true }], 'Pressure ratio', '–'),
        line('thrust-pb', 'Thrust against back pressure', 'Back pressure / stagnation pressure', '–', pbs, [{ label: 'Thrust', data: Fs }], 'Thrust', 'N'),
        line('shock', 'Normal-shock ratios', 'Upstream Mach number', '–', M1s, [{ label: 'p₂/p₁', data: shs.map(q => q.p) }, { label: 'ρ₂/ρ₁', data: shs.map(q => q.r) }, { label: 'T₂/T₁', data: shs.map(q => q.T) }, { label: 'p₀₂/p₀₁', data: shs.map(q => q.p0) }, { label: 'M₂', data: shs.map(q => q.M2) }], 'Ratio', '–'),
      ],
      checks: [
        check('Mass conservation, throat to exit', f.mIdeal > 0 ? (f.rhoE * f.Ve * f.Ae - f.mIdeal) / f.mIdeal : 0, 1e-8, 'Exit-plane ρ·V·A against the throat mass flow'),
        check('Momentum conservation across the normal shock', (1 + g * u1 * u1 - sk.p * (1 + g * sk.M2 ** 2)) / (1 + g * u1 * u1), 1e-12, 'p + ρu² ahead of and behind the shock'),
        check('Mass conservation across the normal shock', (u1 - sk.r * u2) / u1, 1e-12, 'ρu ahead of and behind the shock'),
        check('Second law across the normal shock', sk.p0 > 1 + 1e-12 ? 1 : 0, 0, 'Stagnation pressure must not rise'),
      ],
      warnings,
    };
  },
  benchmarks() {
    const s = normalShock(2, 1.4);
    return [
      bench('Normal shock, M = 2, γ = 1.4: pressure ratio', s.p, 4.5, 'NACA Report 1135, exact value', 1e-12),
      bench('Normal shock, M = 2, γ = 1.4: downstream Mach number', s.M2, 1 / Math.sqrt(3), 'NACA Report 1135: 0.5774 (exactly 1/√3)', 1e-12),
      bench('Normal shock, M = 2, γ = 1.4: density ratio', s.r, 8 / 3, 'NACA Report 1135: 2.6667', 1e-12),
      bench('Normal shock, M = 2, γ = 1.4: stagnation pressure ratio', s.p0, 0.7209, 'NACA Report 1135 tabulated value', 1e-4),
      bench('Area ratio A/A* at M = 2, γ = 1.4', areaMach(2, 1.4), 1.6875, 'NACA Report 1135, exact value 27/16', 1e-12),
      bench('Supersonic Mach number recovered from A/A* = 1.6875', machFromArea(1.6875, 1.4, true), 2, 'Inverse of the area–Mach relation', 1e-10),
      bench('Critical pressure ratio p*/p₀ for γ = 1.4', 1 / isenP(1, 1.4), 0.5283, 'NACA Report 1135 tabulated value', 1e-4),
    ];
  },
  validation: [],
  diagram(v, a) {
    const f = nozzleFlow(v, a), re = Math.sqrt(f.eps), ri = Math.sqrt(CONTRACTION), sc = 60 / Math.max(re, ri), x0 = 90, x1 = 550, xt = a.cd_nozzle ? x0 + (x1 - x0) / 3 : x1;
    const blend = (r0, r1, s) => r0 + (r1 - r0) * (1 - Math.cos(Math.PI * s)) / 2;
    const rOf = x => sc * (x <= xt ? blend(ri, 1, (x - x0) / (xt - x0)) : blend(1, re, (x - xt) / (x1 - xt)));
    const xs = N.linspace(x0, x1, 60), top = xs.map(x => [x.toFixed(1), (180 - rOf(x)).toFixed(1)]), bot = xs.map(x => [x.toFixed(1), (180 + rOf(x)).toFixed(1)]);
    const xsh = f.regime === 2 ? xt + (x1 - xt) * Math.acos(N.clamp(1 - 2 * (Math.sqrt(f.As) - 1) / Math.max(re - 1, 1e-12), -1, 1)) / Math.PI : null;
    return svg(`
      ${S.poly(top, 'd-pipe')} ${S.poly(bot, 'd-pipe')}
      ${S.line(60, 180, 590, 180, 'd-dim')}
      ${S.arrow(100, 180, 170, 180)} ${S.text(70, 150, `p₀ = ${lab(v.p_0 / 1e5, 'bar')}`, 'd-text', 'start')} ${S.text(70, 215, `T₀ = ${lab(v.T_0, 'K')}`, 'd-text', 'start')}
      ${S.line(xt, 180 - sc, xt, 180 + sc, 'd-dim')} ${S.text(xt, 180 + sc + 24, a.cd_nozzle ? 'throat, M = 1 when choked' : 'exit = throat', 'd-text d-small')}
      ${xsh ? S.line(xsh, 180 - rOf(xsh), xsh, 180 + rOf(xsh), 'd-line d-hazard') + S.text(xsh, 180 - rOf(xsh) - 10, 'normal shock', 'd-text d-small') : ''}
      ${S.arrow(x1 - 40, 180, x1 + 40, 180)} ${S.text(x1 + 46, 172, `M_e = ${lab(f.Me)}`, 'd-text', 'start')}
      ${S.text(x1 + 46, 196, `p_b = ${lab(v.p_b / 1e5, 'bar')}`, 'd-text d-small', 'start')}
      ${S.text(320, 40, NOZ_REGIMES[f.regime])}
      ${S.text(320, 335, `A_e / A_t = ${lab(f.eps)}    γ = ${lab(v.gamma)}    thrust ${lab(f.F, 'N')}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Record the wall-pressure distribution of a converging–diverging nozzle as the back pressure is lowered, and compare the regimes, shock positions and choked mass flow with one-dimensional theory.',
    apparatus: ['Blow-down or continuous dry-air supply with a settling chamber and screens', 'Planar or axisymmetric converging–diverging nozzle with a row of wall pressure tappings', 'Downstream throttle valve or vacuum receiver to set back pressure', 'Schlieren or shadowgraph system with windows if the nozzle is planar'],
    instruments: [{ name: 'Multi-channel pressure scanner', measures: 'Wall static pressures', range: '0–10 bar absolute', resolution: '±0.05 % of full scale' }, { name: 'Stagnation-chamber transducer and thermocouple', measures: 'p₀ and T₀', range: '0–16 bar, 250–350 K', resolution: '±0.1 %, ±0.5 K' }, { name: 'Critical-flow venturi or Coriolis meter upstream', measures: 'Mass flow rate', range: 'to suit', resolution: '±0.5 %' }, { name: 'Schlieren camera', measures: 'Shock position and structure', range: '—', resolution: '≥ 1 kHz' }],
    procedure: ['Dry the supply air to avoid condensation shocks.', 'Set p₀, then reduce back pressure in steps from p₀ to the lowest attainable value.', 'At each step record the wall pressures, mass flow and a schlieren image.', 'Plot p/p₀ against distance for each back pressure and identify choking, shock position and the supersonic branch.'],
    controls: ['Leak check with the exit blanked', 'Repeat at a second stagnation pressure: p/p₀ distributions should be unchanged in the choked regimes'],
    signatures: ['Mass flow independent of back pressure once the throat pressure ratio reaches 0.528 (air)', 'Pressure jump across the shock matching the Rankine–Hugoniot value for the local Mach number', 'Supersonic-branch pressures independent of back pressure'],
    safety: ['Pressure-rated settling chamber and windows with relief protection', 'Hearing protection: supersonic jets are intensely noisy', 'Restrain the nozzle against thrust'],
  },
  falsify: ['Mass flow continuing to rise as back pressure falls below the critical value with fixed stagnation conditions.', 'A measured shock pressure jump differing from the Rankine–Hugoniot value by more than the uncertainty in the local Mach number.', 'A stationary expansion shock (pressure falling across the discontinuity), which would violate the second law.'],
  alternatives: [{ name: 'Method of characteristics', text: 'Resolves the two-dimensional supersonic field and is used to design shock-free bell contours.' }, { name: 'Shock–boundary-layer interaction and separation', text: 'Real over-expanded nozzles separate with oblique (lambda) shocks rather than a single normal shock; empirical criteria such as Summerfield\'s predict the separation pressure.' }, { name: 'Fanno and Rayleigh flow', text: 'Add wall friction or heat transfer in constant-area ducts, where stagnation pressure is not conserved.' }],
  hazards: [{ hazard: 'Over-pressure of the supply vessel', cause: 'Regulator failure or blocked exit', mitigation: 'Relief valve and burst disc sized for full supply flow' }, { hazard: 'Noise', cause: 'Shock-associated and jet-mixing noise', mitigation: 'Silencer, enclosure, hearing protection' }, { hazard: 'Side loads', cause: 'Asymmetric flow separation in an over-expanded nozzle', mitigation: 'Avoid sustained operation between shock-at-exit and design pressure ratios; structural margin' }],
  standards: ['ISO 9300 (measurement of gas flow by critical-flow Venturi nozzles)', 'ASME MFC-7 (measurement of gas flow by means of critical flow Venturi nozzles)', 'NASA SP-8120 (liquid rocket engine nozzles)'],
  limits: 'Steady quasi-one-dimensional flow of a calorically perfect gas, adiabatic and frictionless apart from a thin normal shock. Not valid where the boundary layer separates, where the gas condenses or reacts, or for strongly two-dimensional contours. The plotted contour uses a fixed inlet contraction ratio of 3.',
  numerics: { method: 'Closed-form isentropic and shock relations; Newton iteration on the area–Mach relation and bisection on the shock location', stability: 'Monotonic Newton iteration on each branch of the area–Mach relation; bracketed root finding for the shock location' },
  optimise: { objective: 'F', sense: 'max', vars: ['eps'], note: 'Thrust is greatest when the area ratio expands the flow exactly to ambient pressure.' },
  inverse: { series: 'pressure', fit: ['eps', 'p_b'] },
  extensions: ['Oblique shocks and Prandtl–Meyer expansions in the jet outside the nozzle', 'Friction and heat transfer (Fanno, Rayleigh) in the duct', 'Chemically reacting or frozen-flow expansion for rocket propellants'],
};

// ------------------------------------------------------------------ 3. rocket ascent
function ascent(v, a, rtol = 1e-9) {
  const ve = G0 * v.I_sp, mf = v.m_0 * (1 - v.zeta), Fv = v.TW * v.m_0 * v.g_s, mdot = Fv / ve, tb = (v.m_0 - mf) / mdot;
  const A = Math.PI * v.d ** 2 / 4, ps = 101325 * v.rho_0 / 1.225;
  const gOf = h => (a.gravity ? (a.g_varies ? v.g_s * (v.R_p / (v.R_p + Math.max(h, 0))) ** 2 : v.g_s) : 0);
  const rhoOf = h => (a.drag ? v.rho_0 * Math.exp(-Math.max(h, 0) / v.H) : 0);
  const thrust = h => (a.const_thrust ? Fv : Math.max(Fv - ps * Math.exp(-Math.max(h, 0) / v.H) * v.A_e, 0));
  const rhs = burning => (t, y) => {
    const [h, u] = y, m = burning ? Math.max(v.m_0 - mdot * t, mf) : mf, F = burning ? thrust(h) : 0;
    const D = 0.5 * rhoOf(h) * u * Math.abs(u) * v.C_D * A, g = gOf(h), acc = (F - D) / m - g;
    if (h <= 0 && u <= 0 && acc < 0) return [0, 0, F / m, 0, F / m];   // held on the pad: thrust below weight
    return [u, acc, g, D / m, F / m];
  };
  const o = { rtol, atol: 1e-8, maxSteps: 60000 };
  const b = N.rk45(rhs(true), [0, 0, 0, 0, 0], 0, tb, 161, o), yb = b.final || b.y.map(r => r[r.length - 1]);
  const fc = rhs(false);
  let c, apogee = false;
  if (a.gravity) {
    c = toEvent(fc, yb, 20 * Math.max(yb[1], 0) / v.g_s + 60, y => y[1], y => fc(0, y)[1], 121, o);
    apogee = c.hit;
  } else c = N.rk45(fc, yb, 0, tb, 81, o);
  const t = [...b.t, ...c.t.slice(1).map(x => x + tb)], cat = k => [...b.y[k], ...c.y[k].slice(1)];
  const h = cat(0), u = cat(1), nb = b.t.length;
  const acc = t.map((tt, i) => (i < nb ? rhs(true)(tt, [h[i], u[i]]) : fc(0, [h[i], u[i]]))[1]);
  const q = h.map((hh, i) => 0.5 * rhoOf(hh) * u[i] * u[i]);
  const mass = t.map(tt => (tt < tb ? v.m_0 - mdot * tt : mf));
  const last = c.hit ? c.yHit : (c.final || yb);
  return { ve, mf, Fv, mdot, tb, A, t, h, u, acc, q, mass, yb, apogee, hAp: last[0], tAp: tb + c.tHit, dvId: ve * Math.log(v.m_0 / mf) };
}
const rocket = {
  id: 'rocket-ascent',
  title: 'Vertical rocket ascent with drag and gravity',
  module: 2, klass: 'I', domains: ['aerospace', 'space'],
  keywords: ['tsiolkovsky', 'rocket equation', 'rocket ascent', 'delta-v', 'specific impulse', 'burnout velocity', 'gravity loss', 'drag loss', 'sounding rocket', 'rocket', 'launch vehicle', 'max q', 'thrust-to-weight', 'apogee', 'propellant mass fraction'],
  summary: 'Vertical ascent of a single-stage rocket: the Tsiolkovsky ideal velocity, gravity and drag losses, burnout state, apogee and maximum dynamic pressure.',
  background: [
    'A rocket accelerates by expelling mass. In the absence of external forces, conservation of momentum gives the Tsiolkovsky equation: the velocity gained equals the effective exhaust velocity times the logarithm of the mass ratio.',
    'A real ascent falls short of that ideal. Gravity acting during the burn removes a velocity equal to the time integral of the local gravitational acceleration, and aerodynamic drag removes a further amount that peaks near the maximum dynamic pressure. This model integrates the vertical equation of motion through an exponential atmosphere with inverse-square gravity and keeps a running account of each loss.',
  ],
  phenomena: ['Reaction thrust from expelled mass', 'Variable-mass dynamics', 'Gravity loss', 'Aerodynamic drag and dynamic pressure', 'Ballistic coast to apogee'],
  laws: ['momentum', 'newton2', 'newton3', 'mass', 'gravitation'],
  refs: ['Tsiolkovsky, K. E. (1903). The exploration of cosmic space by means of reaction devices (in Russian). Nauchnoe Obozrenie 5.', 'Sutton, G. P. & Biblarz, O. (2017). Rocket Propulsion Elements, 9th ed., Wiley.', 'Curtis, H. D. (2020). Orbital Mechanics for Engineering Students, 4th ed., Butterworth-Heinemann.', 'Turner, M. J. L. (2009). Rocket and Spacecraft Propulsion, 3rd ed., Springer.'],
  inputs: [
    inp('m_0', 'Lift-off mass', 'kg', 5000, { min: 10, max: 3e6, aliases: ['lift-off mass', 'launch mass', 'initial mass', 'mass'] }),
    inp('zeta', 'Propellant mass fraction', '1', 0.8, { min: 0.05, max: 0.95, aliases: ['propellant fraction', 'mass fraction'] }),
    inp('I_sp', 'Specific impulse (vacuum)', 's', 280, { min: 50, max: 480, aliases: ['specific impulse', 'isp'], src: 'Kerosene–oxygen engine; solid motors about 250 s, hydrogen–oxygen about 450 s' }),
    inp('TW', 'Thrust-to-weight ratio at lift-off', '1', 1.6, { min: 1.05, max: 20, aliases: ['thrust-to-weight', 'thrust to weight'] }),
    inp('d', 'Body diameter', 'm', 1.0, { min: 0.02, max: 10, kind: 'geometry', aliases: ['diameter'] }),
    inp('C_D', 'Drag coefficient (frontal-area basis)', '1', 0.35, { min: 0.05, max: 2, kind: 'fluid', aliases: ['drag coefficient'], src: 'Slender body, averaged over subsonic to supersonic flight' }),
    inp('A_e', 'Nozzle exit area', 'm^2', 0.2, { min: 0, max: 50, kind: 'geometry', aliases: ['exit area', 'nozzle area'] }),
    inp('rho_0', 'Air density at the launch site', 'kg/m^3', 1.225, { min: 0, max: 2, kind: 'environment', env: 'air_density', aliases: ['air density', 'surface density'] }),
    inp('H', 'Atmospheric scale height', 'km', 8.5, { min: 3, max: 30, kind: 'environment', aliases: ['scale height'], src: 'Earth, lower atmosphere' }),
    inp('g_s', 'Surface gravitational acceleration', 'm/s^2', 9.80665, { min: 0.5, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity', 'surface gravity'] }),
    inp('R_p', 'Planet radius', 'km', 6371, { min: 500, max: 80000, kind: 'environment', aliases: ['planet radius', 'earth radius'], src: 'Earth mean radius' }),
  ],
  assumptions: [
    asm('gravity', 'Gravity acts on the vehicle throughout the flight.', { why: 'Launch from a planetary surface', alt: 'Gravity-free flight, as in deep space: there is no gravity loss and no apogee.' }),
    asm('drag', 'Aerodynamic drag acts, with density falling exponentially with altitude.', { why: 'Flight through an atmosphere', alt: 'Vacuum flight: no drag loss.' }),
    asm('g_varies', 'Gravitational acceleration falls with altitude as the inverse square of distance from the planet centre.', { why: 'Flights reaching a significant fraction of the planet radius', alt: 'Gravity is constant at its surface value.' }),
    asm('const_thrust', 'Thrust is constant at its vacuum value.', { why: 'Simplest closure; exact above the atmosphere', alt: 'Thrust is reduced by ambient pressure acting on the nozzle exit area, F = F_vac − p_a A_e.' }),
  ],
  symbols: { m: ['Vehicle mass', 'kg'], t: ['Time', 's'], v: ['Vertical velocity', 'm/s'], z: ['Altitude', 'm'], F: ['Thrust', 'N'], F_v: ['Vacuum thrust', 'N'], D: ['Drag', 'N'], rho: ['Air density', 'kg/m^3'], g_h: ['Local gravitational acceleration', 'm/s^2'], p_a: ['Ambient pressure', 'Pa'], p_s: ['Surface pressure', 'Pa'], p_sl: ['Standard sea-level pressure, 101 325 Pa', 'Pa'], rho_sl: ['Standard sea-level density, 1.225 kg/m³', 'kg/m^3'], dv_id: ['Ideal velocity increment', 'm/s'], m_f: ['Burnout mass', 'kg'], A_ref: ['Frontal area', 'm^2'], t_b: ['Burn time', 's'], g: ['Standard gravity', 'm/s^2'] },
  equations: a => [
    eq('fv', 'Vacuum thrust', 'F_v', 'TW*m_0*g_s', { kind: 'definition' }),
    eq('mass', 'Propellant consumption', 'd(m,t)', '-F_v/(g*I_sp)', { kind: 'law', origin: 'Conservation of mass; definition of specific impulse' }),
    eq('mf', 'Burnout mass', 'm_f', 'm_0*(1 - zeta)', { kind: 'definition' }),
    eq('tsi', 'Ideal velocity increment', 'dv_id', 'g*I_sp*ln(m_0/m_f)', { kind: 'law', origin: 'Tsiolkovsky rocket equation (conservation of momentum)' }),
    eq('mom', 'Equation of motion', 'm*d(v,t)', `F${a.drag ? ' - D' : ''}${a.gravity ? ' - m*g_h' : ''}`, { kind: 'law', origin: 'Newton\'s second law for a variable-mass body', needs: ['gravity', 'drag'].filter(k => a[k]) }),
    eq('kin', 'Kinematics', 'd(z,t)', 'v', { kind: 'definition' }),
    a.const_thrust ? eq('thr', 'Thrust', 'F', 'F_v', { kind: 'closure', origin: 'Vacuum thrust at all altitudes', needs: ['const_thrust'] })
      : eq('thr', 'Thrust with ambient back-pressure', 'F', 'max(F_v - p_a*A_e, 0)', { kind: 'law', origin: 'Momentum balance on the nozzle' }),
    ...(a.const_thrust ? [] : [eq('ps', 'Surface pressure', 'p_s', 'p_sl*rho_0/rho_sl', { kind: 'closure', origin: 'Standard sea-level pressure scaled in proportion to the launch-site density' }), eq('pa', 'Ambient pressure', 'p_a', 'p_s*exp(-z/H)', { kind: 'closure', origin: 'Isothermal hydrostatic atmosphere' })]),
    ...(a.drag ? [eq('drag', 'Drag', 'D', '0.5*rho*v*abs(v)*C_D*A_ref', { kind: 'empirical', origin: 'Quadratic drag law', needs: ['drag'] }), eq('rho', 'Air density', 'rho', 'rho_0*exp(-z/H)', { kind: 'closure', origin: 'Isothermal hydrostatic atmosphere', needs: ['drag'] })] : []),
    ...(a.gravity ? [a.g_varies ? eq('grav', 'Local gravity', 'g_h', 'g_s*(R_p/(R_p + z))^2', { kind: 'law', origin: 'Newton\'s law of gravitation', needs: ['g_varies'] }) : eq('grav', 'Local gravity', 'g_h', 'g_s', { kind: 'closure', origin: 'Uniform field' })] : []),
  ],
  derivation: a => [
    { text: 'In a short time the rocket of mass m expels propellant −dm at exhaust velocity v_e relative to itself. Conservation of momentum of rocket plus exhaust gives the thrust.', tex: 'm\\,\\mathrm{d}v = -v_e\\,\\mathrm{d}m \\quad\\Rightarrow\\quad F = \\dot m\\,v_e,\\qquad v_e = g_0 I_{sp}' },
    { text: 'With no other force this integrates to the Tsiolkovsky equation.', tex: '\\Delta v_{ideal} = g_0 I_{sp}\\,\\ln\\frac{m_0}{m_f}' },
    { text: `Adding ${[a.gravity && 'weight', a.drag && 'drag'].filter(Boolean).join(' and ') || 'no external force'} to the momentum balance gives the ascent equation.`, tex: 'm\\frac{\\mathrm{d}v}{\\mathrm{d}t} = F - \\tfrac12\\rho v|v|C_D A - m\\,g(z)' },
    { text: 'Dividing by m and integrating over the burn separates the burnout velocity into the ideal value less the gravity and drag losses.', tex: 'v_{bo} = \\int_0^{t_b}\\frac{F}{m}\\,\\mathrm{d}t - \\int_0^{t_b} g\\,\\mathrm{d}t - \\int_0^{t_b}\\frac{D}{m}\\,\\mathrm{d}t' },
    { text: 'For constant gravity and no drag the burn can be integrated in closed form, giving the burnout velocity and altitude used as benchmarks.', tex: 'v_{bo} = v_e\\ln R - g t_b,\\qquad z_{bo} = v_e t_b\\left(1 - \\frac{\\ln R}{R-1}\\right) - \\tfrac12 g t_b^2,\\quad R = \\frac{m_0}{m_f}' },
  ],
  solve(v, a) {
    const r = ascent(v, a), [hbo, vbo, gl, dl, tl] = r.yb;
    const pq = N.peak(r.q), iq = pq.i, amax = N.maxOf(r.acc), warnings = [];
    if (!a.const_thrust && r.Fv - 101325 * v.rho_0 / 1.225 * v.A_e < v.m_0 * v.g_s) warnings.push('With the ambient-pressure correction the sea-level thrust is below the lift-off weight: the vehicle stays on the pad until enough propellant has burned.');
    if (a.gravity && !r.apogee) warnings.push('The vehicle does not reach an apogee within the simulated coast: its burnout speed is close to or above the local escape speed.');
    if (a.drag && vbo > 1500 && hbo < 3e4) warnings.push('High speed deep in the atmosphere: aerodynamic heating and transonic drag rise, neither of which is modelled, would be severe.');
    const ideal = r.t.map((t, i) => r.ve * Math.log(v.m_0 / r.mass[i]));
    const sub = every(r.t.length, 300);
    const pick = arr => arr.filter((_, i) => i % sub === 0 || i === arr.length - 1);
    return {
      scalars: [
        scalar('F_v', 'Vacuum thrust', r.Fv, 'N', { show: 'kN' }), scalar('mdot', 'Propellant mass flow', r.mdot, 'kg/s'), scalar('t_b', 'Burn time', r.tb, 's'),
        scalar('dv_id', 'Ideal (Tsiolkovsky) velocity increment', r.dvId, 'm/s'), scalar('v_bo', 'Burnout velocity', vbo, 'm/s'), scalar('h_bo', 'Burnout altitude', hbo, 'm', { show: 'km' }),
        scalar('dv_g', 'Gravity loss', gl, 'm/s'), scalar('dv_d', 'Drag loss', dl, 'm/s'), scalar('dv_p', 'Back-pressure thrust loss', r.dvId - tl, 'm/s'),
        scalar('h_ap', 'Apogee altitude', a.gravity && r.apogee ? r.hAp : NaN, 'm', { show: 'km', text: !a.gravity ? 'No apogee without gravity' : r.apogee ? undefined : 'Not reached within the simulated coast' }),
        scalar('t_ap', 'Time to apogee', a.gravity && r.apogee ? r.tAp : NaN, 's', { text: !a.gravity ? 'No apogee without gravity' : r.apogee ? undefined : 'Not reached within the simulated coast' }),
        scalar('q_max', 'Maximum dynamic pressure', pq.value, 'Pa', { show: 'kPa' }), scalar('h_q', 'Altitude of maximum dynamic pressure', pq.interp(r.h), 'm', { show: 'km' }),
        scalar('a_max', 'Peak acceleration', amax, 'm/s^2', { show: 'g0' }), scalar('m_f', 'Burnout mass', r.mf, 'kg'),
      ],
      series: [
        line('altitude', 'Altitude', 'Time', 's', pick(r.t), [{ label: 'Altitude', data: pick(r.h).map(x => x / 1000) }], 'Altitude', 'km'),
        line('velocity', 'Velocity', 'Time', 's', pick(r.t), [{ label: 'Velocity', data: pick(r.u) }, { label: 'Ideal (Tsiolkovsky)', data: pick(ideal), dash: true }], 'Velocity', 'm/s'),
        line('accel', 'Acceleration', 'Time', 's', pick(r.t), [{ label: 'Acceleration', data: pick(r.acc).map(x => x / G0) }], 'Acceleration', 'g₀'),
        line('dynp', 'Dynamic pressure', 'Time', 's', pick(r.t), [{ label: 'Dynamic pressure', data: pick(r.q).map(x => x / 1000) }], 'Dynamic pressure', 'kPa'),
      ],
      checks: [
        check('Velocity budget at burnout', (tl - gl - dl - vbo) / r.dvId, 1e-9, 'Thrust integral less gravity and drag losses against the integrated velocity'),
        check('Thrust integral against the rocket equation', a.const_thrust ? (tl - r.dvId) / r.dvId : 0, 1e-8, a.const_thrust ? '∫(F/m)dt against g₀ I_sp ln(m₀/m_f)' : 'Not applicable with altitude-dependent thrust'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const free = ascent(v, { gravity: false, drag: false, g_varies: false, const_thrust: true }, 1e-11);
    const cg = ascent(v, { gravity: true, drag: false, g_varies: false, const_thrust: true }, 1e-11);
    const Rm = 1 / (1 - v.zeta), ve = G0 * v.I_sp;
    return [
      bench('Burnout velocity with gravity and drag off vs Tsiolkovsky', free.yb[1], ve * Math.log(Rm), 'Ideal rocket equation', 1e-8),
      bench('Burnout velocity, constant gravity, no drag', cg.yb[1], ve * Math.log(Rm) - v.g_s * cg.tb, 'v = v_e ln R − g t_b', 1e-8),
      bench('Burnout altitude, constant gravity, no drag', cg.yb[0], ve * cg.tb * (1 - Math.log(Rm) / (Rm - 1)) - 0.5 * v.g_s * cg.tb ** 2, 'Closed-form integral of the rocket equation', 1e-8),
      bench('Coast apogee, constant gravity, no drag', cg.hAp, cg.yb[0] + cg.yb[1] ** 2 / (2 * v.g_s), 'Ballistic coast: h = h_bo + v_bo²/(2g)', 1e-8),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.path('M40 320 L600 320', 'd-ground')}
      ${S.path('M300 70 Q322 110 322 150 L322 270 L278 270 L278 150 Q278 110 300 70 Z', 'd-body')}
      ${S.path('M278 240 L256 276 L278 270 Z', 'd-body')} ${S.path('M322 240 L344 276 L322 270 Z', 'd-body')}
      ${S.path('M286 272 L300 318 L314 272 Z', 'd-hazard')}
      ${S.arrow(300, 60, 300, 20)} ${S.text(312, 30, `thrust = ${lab(v.TW)} × weight`, 'd-text', 'start')}
      ${a.gravity ? S.arrow(360, 150, 360, 220) + S.text(370, 190, 'weight m·g(z)', 'd-text', 'start') : S.text(370, 190, 'no gravity', 'd-text d-small', 'start')}
      ${a.drag ? S.arrow(240, 120, 240, 180, 'd-arrow d-hazard') + S.text(230, 150, 'drag ½ρv²C_D A', 'd-text', 'end') : S.text(230, 150, 'vacuum', 'd-text d-small', 'end')}
      ${S.text(470, 290, `m₀ = ${lab(v.m_0, 'kg')}`, 'd-text', 'start')} ${S.text(470, 308, `I_sp = ${lab(v.I_sp, 's')}`, 'd-text d-small', 'start')}
      ${S.text(60, 290, `propellant fraction ${lab(v.zeta)}`, 'd-text', 'start')} ${S.text(60, 308, `ρ(z) = ρ₀ exp(−z/H)`, 'd-text d-small', 'start')}
    `);
  },
  experiment: {
    objective: 'Fly an instrumented sounding rocket of known mass, thrust curve and drag coefficient and compare the measured velocity and altitude history with the predicted ascent.',
    apparatus: ['Single-stage sounding or high-power model rocket with a motor of certified thrust curve', 'Launch rail and remote ignition system', 'Recovery system (parachute) and tracking beacon'],
    instruments: [{ name: 'Barometric altimeter', measures: 'Altitude', range: '0–30 km', resolution: '±1 % of reading' }, { name: 'Three-axis accelerometer', measures: 'Axial acceleration', range: '±50 g', resolution: '±0.05 g at ≥ 400 Hz' }, { name: 'GNSS receiver', measures: 'Position and velocity during coast', range: '—', resolution: '±3 m, ±0.1 m/s' }, { name: 'Static test stand with load cell', measures: 'Thrust curve and total impulse before flight', range: '0–5 kN', resolution: '±0.5 %' }],
    procedure: ['Weigh the vehicle before and after motor burn-out mass is established from a static firing.', 'Record launch-site pressure, temperature and wind.', 'Launch near-vertically, logging acceleration and pressure altitude.', 'Integrate the accelerometer record to obtain velocity, and compare burnout velocity, burnout altitude and apogee with the model.'],
    controls: ['Static firing of a motor from the same batch to confirm specific impulse', 'Wind-tunnel or coast-phase deceleration measurement to fix the drag coefficient independently'],
    signatures: ['Burnout velocity below the Tsiolkovsky value by the gravity loss g·t_b plus a drag loss', 'Coast deceleration exceeding g by the drag term, falling toward g as density drops'],
    safety: ['Range safety: exclusion zone sized for ballistic impact and motor failure', 'Handle propellants and igniters under the applicable explosives regulations', 'No launch with winds above the stability limit'],
  },
  falsify: ['A burnout velocity exceeding the Tsiolkovsky value for the measured mass ratio and exhaust velocity.', 'A gravity loss that does not scale with burn time for vertical flight.', 'A measured coast deceleration below the local gravitational acceleration in still air.'],
  alternatives: [{ name: 'Gravity-turn trajectory', text: 'Orbital launchers pitch over so that thrust stays along the velocity vector; gravity loss is then ∫ g sin γ dt and steering loss appears.' }, { name: 'Multi-stage vehicle', text: 'Discarding empty tankage raises the overall mass ratio; the ideal velocity is the sum of the stage increments.' }, { name: 'Mach-dependent drag', text: 'The drag coefficient rises sharply through the transonic range; a tabulated C_D(M) replaces the constant value.' }],
  hazards: [{ hazard: 'Explosion or fire on the pad', cause: 'Motor case or feed-system failure', mitigation: 'Remote operations, blast exclusion zone, flight-termination system' }, { hazard: 'Uncontrolled impact', cause: 'Recovery failure or unstable flight', mitigation: 'Dispersion analysis, cleared range, stability margin of at least one calibre' }, { hazard: 'Structural failure at maximum dynamic pressure', cause: 'Bending loads from wind shear', mitigation: 'Throttle or trajectory shaping through max-q; wind limits' }],
  standards: ['NFPA 1127 (code for high power rocketry)', 'ISO 14620-1 (space systems — safety requirements — system safety)', 'ECSS-E-ST-35C (space engineering — propulsion general requirements)'],
  limits: 'Vertical, non-rotating, single-stage flight with constant mass flow and constant drag coefficient through an isothermal exponential atmosphere. No pitch-over, wind, staging, throttling, Earth rotation or aerodynamic heating.',
  numerics: { method: 'Adaptive Dormand–Prince RK45 in two phases (burn, coast), with Newton refinement of the apogee event', order: 5, stability: 'Step-size controlled to a relative tolerance of 10⁻⁹' },
  optimise: { objective: 'h_ap', sense: 'max', vars: ['TW'], note: 'High thrust cuts gravity loss but raises drag loss; the best thrust-to-weight ratio balances the two.' },
  inverse: { series: 'velocity', fit: ['C_D', 'I_sp'] },
  extensions: ['Gravity-turn ascent to orbit with pitch programme', 'Two-stage optimisation of the mass split', 'Standard-atmosphere density and Mach-dependent drag'],
};

// ------------------------------------------------------------------ 4. Hohmann and bi-elliptic transfers
/** Half-ellipse from apsis radius rA to apsis radius rB: time, radius and speed along the arc. */
function orbitLeg(mu, rA, rB, n = 81) {
  const sma = (rA + rB) / 2, e = Math.abs(rB - rA) / (rA + rB), k = Math.sqrt(sma ** 3 / mu), outward = rA <= rB;
  const E = N.linspace(outward ? 0 : Math.PI, outward ? Math.PI : 2 * Math.PI, n);
  const r = E.map(x => sma * (1 - e * Math.cos(x)));
  return { t: E.map(x => k * (x - e * Math.sin(x) - (outward ? 0 : Math.PI))), r, v: r.map(x => Math.sqrt(mu * (2 / x - 1 / sma))), tof: Math.PI * k };
}
function transfer(v, a) {
  const mu = v.GM, r1 = v.r_1, r2 = v.r_2, vc1 = Math.sqrt(mu / r1), vc2 = Math.sqrt(mu / r2), ve = G0 * v.I_sp;
  const vis = (r, sma) => Math.sqrt(mu * (2 / r - 1 / sma));
  const comb = (x, y, ang) => Math.sqrt(Math.max(x * x + y * y - 2 * x * y * Math.cos(ang), 0));
  const di = a.coplanar ? 0 : v.di, vd = a.circular ? vc1 : Math.sqrt(mu * (1 + v.e_1) / r1);
  const hoh = () => { const at = (r1 + r2) / 2; return { kind: 'hohmann', dv: [Math.abs(vis(r1, at) - vd), comb(vis(r2, at), vc2, di)], tof: Math.PI * Math.sqrt(at ** 3 / mu), legs: [[r1, r2]], sweep: Math.PI }; };
  const bi = () => { const a1 = (r1 + v.r_b) / 2, a2 = (r2 + v.r_b) / 2; return { kind: 'bi-elliptic', dv: [Math.abs(vis(r1, a1) - vd), comb(vis(v.r_b, a1), vis(v.r_b, a2), di), Math.abs(vis(r2, a2) - vc2)], tof: Math.PI * (Math.sqrt(a1 ** 3 / mu) + Math.sqrt(a2 ** 3 / mu)), legs: [[r1, v.r_b], [v.r_b, r2]], sweep: 2 * Math.PI }; };
  const low = () => { const dv = comb(vc1, vc2, Math.min(Math.PI / 2 * di, Math.PI)); return { kind: 'low-thrust', dv: [dv], tof: v.m_0 * ve * (1 - Math.exp(-dv / ve)) / v.F_T, legs: [], sweep: NaN }; };
  const main = !a.impulsive ? low() : a.hohmann ? hoh() : bi(), other = a.hohmann ? bi() : hoh();
  return { mu, r1, r2, vc1, vc2, ve, vis, main, other, dvTot: N.sum(main.dv), dvOther: N.sum(other.dv) };
}
const LEO_GEO = { r_1: 6.678e6, r_2: 4.2164e7, GM: R.BODIES.earth.GM };
const hohmann = {
  id: 'hohmann-transfer',
  title: 'Hohmann and bi-elliptic orbit transfers',
  module: [1, 2], klass: 'I', domains: ['space', 'aerospace'],
  keywords: ['hohmann transfer', 'bi-elliptic transfer', 'transfer orbit', 'orbit transfer', 'delta-v', 'geostationary transfer', 'leo to geo', 'vis-viva', 'orbit raising', 'time of flight', 'plane change', 'low-thrust spiral', 'circular orbit', 'geostationary', 'transfer'],
  summary: 'Velocity increments and time of flight for a two-impulse Hohmann transfer between circular orbits about any central body, with bi-elliptic, plane-change and low-thrust alternatives.',
  background: [
    'A spacecraft in a circular orbit can reach another circular orbit of different radius by following half of an ellipse that touches both. The speed at any point of a Kepler orbit follows from the vis-viva equation, so the two impulses needed — one to enter the transfer ellipse and one to circularise at the far side — are differences of known speeds. Hohmann showed in 1925 that this is the two-impulse transfer of least velocity increment.',
    'For radius ratios above about 11.94 a three-impulse bi-elliptic transfer, which first climbs far beyond the target and then drops back, can need less velocity increment at the cost of a much longer flight. Continuous low thrust follows a slow spiral whose total velocity increment equals the difference of the circular speeds.',
  ],
  phenomena: ['Kepler motion under inverse-square gravity', 'Conservation of orbital energy and angular momentum', 'Impulsive velocity change', 'Oberth effect (burning deep in the gravity well)'],
  laws: ['gravitation', 'newton2', 'energy', 'angular', 'momentum'],
  refs: ['Hohmann, W. (1925). Die Erreichbarkeit der Himmelskörper. Oldenbourg, Munich.', 'Edelbaum, T. N. (1961). Propulsion requirements for controllable satellites. ARS Journal 31, 1079–1089.', 'Bate, R. R., Mueller, D. D. & White, J. E. (1971). Fundamentals of Astrodynamics. Dover.', 'Vallado, D. A. (2013). Fundamentals of Astrodynamics and Applications, 4th ed., Microcosm Press.', 'Curtis, H. D. (2020). Orbital Mechanics for Engineering Students, 4th ed., Butterworth-Heinemann.'],
  inputs: [
    inp('r_1', 'Initial orbit radius (from the body centre)', 'km', 6678, { min: 100, max: 1e9, kind: 'geometry', aliases: ['initial radius', 'initial orbit', 'parking orbit', 'leo'], src: 'Low Earth orbit at 300 km altitude' }),
    inp('r_2', 'Final orbit radius (from the body centre)', 'km', 42164, { min: 100, max: 1e9, kind: 'geometry', aliases: ['final radius', 'final orbit', 'target orbit', 'geo'], src: 'Geostationary radius' }),
    inp('GM', 'Gravitational parameter of the central body', 'm^3/s^2', 3.986004418e14, { min: 1e6, max: 1e21, kind: 'environment', aliases: ['gravitational parameter', 'gm', 'mu'], src: 'Earth (IAU). Sun 1.327×10²⁰, Moon 4.905×10¹², Mars 4.283×10¹³ m³/s²' }),
    inp('r_b', 'Intermediate apoapsis radius (bi-elliptic)', 'km', 200000, { min: 100, max: 1e10, kind: 'geometry', aliases: ['intermediate radius', 'apoapsis radius'] }),
    inp('e_1', 'Eccentricity of the initial orbit (when not circular)', '1', 0.2, { min: 0, max: 0.9, kind: 'geometry', aliases: ['eccentricity'] }),
    inp('di', 'Plane change (when not coplanar)', 'deg', 28.5, { min: 0, max: 180, kind: 'geometry', aliases: ['plane change', 'inclination change', 'inclination'], src: 'Launch latitude of Cape Canaveral to the equatorial plane' }),
    inp('m_0', 'Spacecraft mass before the transfer', 'kg', 2000, { min: 1, max: 1e6, aliases: ['spacecraft mass', 'mass'] }),
    inp('I_sp', 'Specific impulse', 's', 320, { min: 50, max: 10000, aliases: ['specific impulse', 'isp'], src: 'Storable bipropellant apogee engine' }),
    inp('F_T', 'Thrust (low-thrust case)', 'N', 400, { min: 0.001, max: 1e6, aliases: ['thrust'] }),
  ],
  assumptions: [
    asm('hohmann', 'The transfer is a two-impulse Hohmann ellipse tangent to both orbits.', { why: 'Minimum two-impulse velocity increment', alt: 'Three-impulse bi-elliptic transfer through the stated intermediate apoapsis.' }),
    asm('impulsive', 'Each burn is short enough to be treated as an instantaneous change of velocity.', { why: 'Chemical propulsion: burn arc small against the orbit period', alt: 'Continuous low tangential thrust: a slow spiral between circular orbits (Edelbaum), with the initial orbit taken as circular.' }),
    asm('coplanar', 'Initial and final orbits lie in the same plane.', { why: 'Simplest case', alt: 'A plane change is combined, by the law of cosines, with the second burn: the one at the final radius for a Hohmann transfer, or at the intermediate apoapsis for a bi-elliptic transfer.' }),
    asm('circular', 'The initial orbit is circular.', { why: 'Parking orbit', alt: 'The initial orbit is an ellipse with the stated eccentricity; the first burn is made at its periapsis, whose radius is the initial radius.' }),
  ],
  symbols: { v: ['Orbital speed', 'm/s'], r: ['Orbital radius', 'm'], a_o: ['Semi-major axis of the orbit', 'm'], a_t: ['Semi-major axis of the transfer ellipse', 'm'], a_1: ['Semi-major axis of the first ellipse', 'm'], a_2: ['Semi-major axis of the second ellipse', 'm'], v_c1: ['Circular speed at the initial radius', 'm/s'], v_c2: ['Circular speed at the final radius', 'm/s'], v_d: ['Speed in the initial orbit at departure', 'm/s'], v_tp: ['Transfer-orbit speed at the initial radius', 'm/s'], v_ta: ['Transfer-orbit speed at the final radius', 'm/s'], v_b1: ['Speed at the intermediate apoapsis, first ellipse', 'm/s'], v_b2: ['Speed at the intermediate apoapsis, second ellipse', 'm/s'], dv_1: ['First velocity increment', 'm/s'], dv_2: ['Second velocity increment', 'm/s'], dv_3: ['Third velocity increment', 'm/s'], dv_tot: ['Total velocity increment', 'm/s'], t_f: ['Time of flight', 's'], m_p: ['Propellant mass', 'kg'], g: ['Standard gravity', 'm/s^2'] },
  equations: a => {
    const out = [
      eq('vv', 'Vis-viva equation', 'v^2', 'GM*(2/r - 1/a_o)', { kind: 'law', origin: 'Conservation of energy in an inverse-square field' }),
      eq('vc1', 'Circular speed, initial orbit', 'v_c1', 'sqrt(GM/r_1)', { kind: 'derived', origin: 'Gravity supplies the centripetal force' }),
      eq('vc2', 'Circular speed, final orbit', 'v_c2', 'sqrt(GM/r_2)', { kind: 'derived', origin: 'Gravity supplies the centripetal force' }),
    ];
    if (!a.impulsive) {
      out.push(a.coplanar ? eq('dvt', 'Low-thrust velocity increment', 'dv_tot', 'abs(v_c1 - v_c2)', { kind: 'derived', origin: 'Quasi-circular spiral under tangential thrust' })
        : eq('dvt', 'Low-thrust velocity increment with plane change', 'dv_tot', 'sqrt(v_c1^2 + v_c2^2 - 2*v_c1*v_c2*cos(min(pi/2*di, pi)))', { kind: 'derived', origin: 'Edelbaum (1961)', note: 'Edelbaum\'s expression holds for plane changes up to 2 rad (114.6°); beyond that the cost saturates at v_c1 + v_c2.' }));
      out.push(eq('mp', 'Propellant mass', 'm_p', 'm_0*(1 - exp(-dv_tot/(g*I_sp)))', { kind: 'law', origin: 'Tsiolkovsky rocket equation' }));
      out.push(eq('tf', 'Thrusting time', 't_f', 'm_p*g*I_sp/F_T', { kind: 'derived', origin: 'Constant propellant flow F/(g₀ I_sp)' }));
    } else {
      out.push(a.circular ? eq('vd', 'Departure speed', 'v_d', 'v_c1', { kind: 'definition', needs: ['circular'] }) : eq('vd', 'Periapsis speed of the initial ellipse', 'v_d', 'sqrt(GM*(1 + e_1)/r_1)', { kind: 'derived', origin: 'Vis-viva at periapsis' }));
      if (a.hohmann) {
        out.push(eq('at', 'Transfer semi-major axis', 'a_t', '(r_1 + r_2)/2', { kind: 'definition', needs: ['hohmann'] }));
        out.push(eq('vtp', 'Transfer speed at the initial radius', 'v_tp', 'sqrt(GM*(2/r_1 - 1/a_t))', { kind: 'derived', origin: 'Vis-viva' }));
        out.push(eq('vta', 'Transfer speed at the final radius', 'v_ta', 'sqrt(GM*(2/r_2 - 1/a_t))', { kind: 'derived', origin: 'Vis-viva' }));
        out.push(eq('dv1', 'First impulse', 'dv_1', 'abs(v_tp - v_d)', { kind: 'derived', origin: 'Tangential burn', needs: ['impulsive'] }));
        out.push(a.coplanar ? eq('dv2', 'Second impulse', 'dv_2', 'abs(v_c2 - v_ta)', { kind: 'derived', origin: 'Tangential burn', needs: ['impulsive', 'coplanar'] })
          : eq('dv2', 'Second impulse with plane change', 'dv_2', 'sqrt(v_ta^2 + v_c2^2 - 2*v_ta*v_c2*cos(di))', { kind: 'derived', origin: 'Vector difference of velocities (law of cosines)', needs: ['impulsive'] }));
        out.push(eq('dvt', 'Total velocity increment', 'dv_tot', 'dv_1 + dv_2', { kind: 'definition' }));
        out.push(eq('tf', 'Time of flight', 't_f', 'pi*sqrt(a_t^3/GM)', { kind: 'law', origin: 'Kepler\'s third law, half a period' }));
      } else {
        out.push(eq('a1', 'First ellipse', 'a_1', '(r_1 + r_b)/2', { kind: 'definition' }), eq('a2', 'Second ellipse', 'a_2', '(r_2 + r_b)/2', { kind: 'definition' }));
        out.push(eq('vb1', 'Apoapsis speed, first ellipse', 'v_b1', 'sqrt(GM*(2/r_b - 1/a_1))', { kind: 'derived', origin: 'Vis-viva' }), eq('vb2', 'Apoapsis speed, second ellipse', 'v_b2', 'sqrt(GM*(2/r_b - 1/a_2))', { kind: 'derived', origin: 'Vis-viva' }));
        out.push(eq('dv1', 'First impulse', 'dv_1', 'abs(sqrt(GM*(2/r_1 - 1/a_1)) - v_d)', { kind: 'derived', origin: 'Tangential burn', needs: ['impulsive'] }));
        out.push(a.coplanar ? eq('dv2', 'Second impulse', 'dv_2', 'abs(v_b2 - v_b1)', { kind: 'derived', origin: 'Tangential burn at the intermediate apoapsis', needs: ['impulsive', 'coplanar'] })
          : eq('dv2', 'Second impulse with plane change', 'dv_2', 'sqrt(v_b1^2 + v_b2^2 - 2*v_b1*v_b2*cos(di))', { kind: 'derived', origin: 'Vector difference of velocities (law of cosines)', needs: ['impulsive'] }));
        out.push(eq('dv3', 'Third impulse', 'dv_3', 'abs(v_c2 - sqrt(GM*(2/r_2 - 1/a_2)))', { kind: 'derived', origin: 'Tangential burn', needs: ['impulsive'] }));
        out.push(eq('dvt', 'Total velocity increment', 'dv_tot', 'dv_1 + dv_2 + dv_3', { kind: 'definition' }));
        out.push(eq('tf', 'Time of flight', 't_f', 'pi*(sqrt(a_1^3/GM) + sqrt(a_2^3/GM))', { kind: 'law', origin: 'Kepler\'s third law, two half periods' }));
      }
    }
    if (a.impulsive) out.push(eq('mp', 'Propellant mass', 'm_p', 'm_0*(1 - exp(-dv_tot/(g*I_sp)))', { kind: 'law', origin: 'Tsiolkovsky rocket equation' }));
    return out;
  },
  derivation: a => [
    { text: 'For motion under an inverse-square attraction the specific orbital energy depends only on the semi-major axis. Equating it to kinetic plus potential energy gives the vis-viva equation.', tex: '\\frac{v^2}{2} - \\frac{GM}{r} = -\\frac{GM}{2a}\\quad\\Rightarrow\\quad v^2 = GM\\left(\\frac{2}{r}-\\frac{1}{a}\\right)' },
    { text: 'A circular orbit has a = r, so its speed is fixed by the radius.', tex: 'v_c = \\sqrt{GM/r}' },
    ...(!a.impulsive ? [{ text: 'Under continuous tangential thrust that is small against gravity the orbit stays nearly circular while its radius changes slowly. The velocity increment delivered equals the change in circular speed; with a simultaneous plane change Edelbaum\'s result applies.', tex: '\\Delta v = \\sqrt{v_{c1}^2 + v_{c2}^2 - 2 v_{c1}v_{c2}\\cos\\!\\left(\\tfrac{\\pi}{2}\\Delta i\\right)}\\qquad(\\Delta i \\le 2\\ \\text{rad})' }]
      : a.hohmann ? [
        { text: 'The Hohmann ellipse touches the inner orbit at periapsis and the outer at apoapsis, so its major axis is the sum of the two radii.', tex: 'a_t = \\tfrac12(r_1 + r_2)' },
        { text: 'Each impulse is the difference between the transfer-orbit speed and the local orbital speed.', tex: '\\Delta v_1 = \\sqrt{\\frac{GM}{r_1}}\\left(\\sqrt{\\frac{2r_2}{r_1+r_2}}-1\\right),\\qquad \\Delta v_2 = \\sqrt{\\frac{GM}{r_2}}\\left(1-\\sqrt{\\frac{2r_1}{r_1+r_2}}\\right)' },
        { text: 'The flight lasts half the period of the transfer ellipse.', tex: 't_f = \\pi\\sqrt{a_t^3/GM}' },
      ] : [
        { text: 'The bi-elliptic transfer uses two half-ellipses meeting at a distant apoapsis r_b. The first burn raises apoapsis to r_b, the second (made where the speed is low) moves periapsis to the final radius, and the third circularises.', tex: 'a_1 = \\tfrac12(r_1+r_b),\\qquad a_2 = \\tfrac12(r_2+r_b)' },
        { text: 'Its flight time is the sum of the two half-periods.', tex: 't_f = \\pi\\left(\\sqrt{a_1^3/GM} + \\sqrt{a_2^3/GM}\\right)' },
      ]),
    ...(a.coplanar || !a.impulsive ? [] : [{ text: 'When the orbit plane must also turn through Δi, the impulse is the vector difference of the velocities before and after. Combining the turn with the burn made at the lowest speed is cheapest.', tex: '\\Delta v = \\sqrt{v_a^2 + v_b^2 - 2 v_a v_b\\cos\\Delta i}' }]),
    { text: 'The propellant needed follows from the rocket equation.', tex: 'm_p = m_0\\left(1 - e^{-\\Delta v/(g_0 I_{sp})}\\right)' },
  ],
  solve(v, a) {
    const s = transfer(v, a), { mu, r1, r2, main } = s, dv = main.dv;
    const n1 = Math.sqrt(mu / r1 ** 3), n2 = Math.sqrt(mu / r2 ** 3);
    const wrap = x => { const y = ((x + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI; return y; };
    const phase = a.impulsive ? wrap(main.sweep - n2 * main.tof) : NaN;
    const syn = Math.abs(n1 - n2) > 1e-12 * n1 ? 2 * Math.PI / Math.abs(n1 - n2) : NaN;
    const mp = v.m_0 * (1 - Math.exp(-s.dvTot / s.ve));
    const [tu, tun] = main.tof > 2 * 86400 ? [86400, 'd'] : [3600, 'h'];
    // profile along the transfer
    let tt = [], rr = [], vv = [];
    if (a.impulsive) main.legs.forEach(([ra, rb], k) => { const l = orbitLeg(mu, ra, rb), t0 = tt.length ? tt[tt.length - 1] : 0; l.t.forEach((t, i) => { if (k && !i) return; tt.push(t0 + t); rr.push(l.r[i]); vv.push(l.v[i]); }); });
    else {
      const md = v.F_T / s.ve;
      tt = N.linspace(0, main.tof, 161);
      vv = tt.map(t => s.vc1 + (s.vc2 - s.vc1) * N.clamp(-s.ve * Math.log(Math.max(1 - md * t / v.m_0, 1e-12)) / Math.max(s.dvTot, 1e-12), 0, 1));
      rr = vv.map(x => mu / (x * x));
    }
    // geometry for the path plot
    const ring = r => { const c = circlePts(r, 181); return { x: c.map(p => p[0]), y: c.map(p => p[1]), z: c.map(() => 0) }; };
    const arc = (ra, rb, th0) => { const th = N.linspace(0, Math.PI, 91), r = th.map(t => 2 * ra * rb / ((ra + rb) + (rb - ra) * Math.cos(t))); return { x: th.map((t, i) => r[i] * Math.cos(t + th0)), y: th.map((t, i) => r[i] * Math.sin(t + th0)), z: th.map(() => 0) }; };
    const paths = [{ label: 'Initial orbit', ...ring(r1) }, { label: 'Final orbit', ...ring(r2) }];
    if (a.impulsive) main.legs.forEach(([ra, rb], k) => paths.push({ label: main.legs.length > 1 ? `Transfer ellipse ${k + 1}` : 'Transfer ellipse', ...arc(ra, rb, k * Math.PI) }));
    else { const th = N.linspace(0, 16 * Math.PI, 481); paths.push({ label: 'Spiral (schematic: the number of turns is reduced)', x: th.map((t, i) => (r1 + (r2 - r1) * i / 480) * Math.cos(t)), y: th.map((t, i) => (r1 + (r2 - r1) * i / 480) * Math.sin(t)), z: th.map(() => 0) }); }
    // classic comparison against radius ratio (coplanar, circular, impulsive)
    const Rs = N.logspace(1.2, 60, 70), rbR = Math.max(v.r_b / r1, 1);
    const hohN = Rr => Math.sqrt(2 * Rr / (1 + Rr)) - 1 + (1 - Math.sqrt(2 / (1 + Rr))) / Math.sqrt(Rr);
    const biN = (Rr, b) => Math.abs(Math.sqrt(2 * b / (1 + b)) - 1) + Math.abs(Math.sqrt(2 * Rr / (b * (Rr + b))) - Math.sqrt(2 / (b * (1 + b)))) + Math.abs(Math.sqrt(2 * b / (Rr * (Rr + b))) - 1 / Math.sqrt(Rr));
    const at = (r1 + r2) / 2, hp = r1 * s.vis(r1, at), ha = r2 * s.vis(r2, at);
    const warnings = [];
    if (a.impulsive && !a.hohmann && v.r_b < Math.max(r1, r2)) warnings.push('The intermediate apoapsis lies inside the larger orbit; a bi-elliptic transfer is normally flown with it well outside both orbits.');
    if (!a.impulsive && v.F_T / v.m_0 > 0.01 * mu / Math.max(r1, r2) ** 2) warnings.push('The thrust acceleration is not small against local gravity, so the quasi-circular spiral approximation is poor.');
    if (!a.impulsive && !a.coplanar && v.di > 2) warnings.push('The plane change exceeds 2 rad (114.6°), the limit of Edelbaum\'s expression; the velocity increment is held at its saturated value, the sum of the two circular speeds.');
    if (!a.impulsive && !a.circular) warnings.push('The low-thrust estimate treats the initial orbit as circular at the stated radius.');
    return {
      scalars: [
        scalar('v_c1', 'Circular speed at the initial radius', s.vc1, 'm/s', { show: 'km/s' }), scalar('v_c2', 'Circular speed at the final radius', s.vc2, 'm/s', { show: 'km/s' }),
        scalar('a_t', 'Semi-major axis of the (first) transfer ellipse', a.impulsive ? (main.legs[0][0] + main.legs[0][1]) / 2 : NaN, 'm', { show: 'km', text: a.impulsive ? undefined : 'Not an ellipse: continuous spiral' }),
        scalar('e_t', 'Eccentricity of the (first) transfer ellipse', a.impulsive ? Math.abs(main.legs[0][1] - main.legs[0][0]) / (main.legs[0][1] + main.legs[0][0]) : NaN, '1', { text: a.impulsive ? undefined : 'Not an ellipse: continuous spiral' }),
        scalar('dv_1', 'First velocity increment', dv[0], 'm/s', { show: 'km/s' }),
        scalar('dv_2', 'Second velocity increment', dv.length > 1 ? dv[1] : 0, 'm/s', { show: 'km/s' }),
        scalar('dv_3', 'Third velocity increment', dv.length > 2 ? dv[2] : 0, 'm/s', { show: 'km/s' }),
        scalar('dv_tot', 'Total velocity increment', s.dvTot, 'm/s', { show: 'km/s' }),
        scalar('dv_alt', `Total for the ${s.other.kind} alternative`, s.dvOther, 'm/s', { show: 'km/s' }),
        scalar('t_f', a.impulsive ? 'Time of flight' : 'Thrusting time', main.tof, 's', { show: tun }),
        scalar('T_1', 'Period of the initial circular orbit', 2 * Math.PI / n1, 's', { show: 'h' }), scalar('T_2', 'Period of the final circular orbit', 2 * Math.PI / n2, 's', { show: 'h' }),
        scalar('phi_r', 'Lead angle of a target in the final orbit at departure (rendezvous)', phase, 'rad', { show: 'deg', text: a.impulsive ? undefined : 'Not defined for a spiral' }),
        scalar('T_syn', 'Synodic period (interval between launch opportunities)', syn, 's', { show: 'h', text: Number.isFinite(syn) ? undefined : 'Undefined: the orbits have the same period' }),
        scalar('m_p', 'Propellant mass', mp, 'kg'), scalar('R_r', 'Radius ratio r₂/r₁', r2 / r1, '1'),
      ],
      series: [
        line('profile', 'Radius along the transfer', 'Time', tun, tt.map(t => t / tu), [{ label: 'Radius', data: rr.map(x => x / 1000) }], 'Radius', 'km'),
        line('speed', 'Speed along the transfer', 'Time', tun, tt.map(t => t / tu), [{ label: 'Orbital speed', data: vv.map(x => x / 1000) }], 'Speed', 'km/s'),
        line('dv-ratio', 'Velocity increment against radius ratio (coplanar, circular)', 'Radius ratio r₂/r₁', '–', Rs, [{ label: 'Hohmann', data: Rs.map(hohN) }, { label: `Bi-elliptic, r_b/r₁ = ${lab(rbR)}`, data: Rs.map(x => biN(x, rbR)) }, { label: 'Bi-parabolic limit', data: Rs.map(x => (Math.SQRT2 - 1) * (1 + 1 / Math.sqrt(x))), dash: true }], 'Δv / v_c1', '–', { logx: true }),
      ],
      paths: [path3d('transfer', 'Transfer geometry', paths, { equal: true, unit: 'm' })],
      checks: [
        check('Angular momentum on the Hohmann ellipse', (hp - ha) / hp, 1e-12, 'r·v at the two apsides, each from the vis-viva equation'),
        check('Rocket-equation round trip', mp > 0 ? (-s.ve * Math.log(1 - mp / v.m_0) - s.dvTot) / s.dvTot : 0, 1e-9, 'Velocity increment recovered from the propellant mass'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const on = { hohmann: true, impulsive: true, coplanar: true, circular: true }, q = { ...v, ...LEO_GEO };
    const s = transfer(q, on), Rr = q.r_2 / q.r_1;
    const closed = s.vc1 * (Math.sqrt(2 * Rr / (1 + Rr)) - 1) + s.vc2 * (1 - Math.sqrt(2 / (1 + Rr)));
    const at = (q.r_1 + q.r_2) / 2, vp = s.vis(q.r_1, at);
    const f = (t, y) => { const r3 = Math.pow(y[0] * y[0] + y[1] * y[1], 1.5); return [y[2], y[3], -q.GM * y[0] / r3, -q.GM * y[1] / r3]; };
    const p = N.rk45(f, [q.r_1, 0, 0, vp], 0, s.main.tof, 2, { rtol: 1e-11, atol: 1e-6 }).final;
    const Rx = 11.938765, hoh = Math.sqrt(2 * Rx / (1 + Rx)) - 1 + (1 - Math.sqrt(2 / (1 + Rx))) / Math.sqrt(Rx);
    return [
      bench('LEO (6678 km) to GEO (42164 km): total Δv from vis-viva vs closed form', s.dvTot, closed, 'Hohmann closed-form expression', 1e-12),
      bench('LEO to GEO total Δv against the textbook figure', s.dvTot, 3900, 'About 3.9 km/s (Curtis; Vallado)', 1e-2),
      bench('Numerically propagated transfer arrives at the target radius', Math.hypot(p[0], p[1]), q.r_2, 'RK45 integration of the two-body equations over the Hohmann flight time', 1e-8),
      bench('Hohmann equals the bi-parabolic limit at r₂/r₁ = 11.94', hoh, (Math.SQRT2 - 1) * (1 + 1 / Math.sqrt(Rx)), 'Known cross-over radius ratio 11.94 (Vallado)', 1e-6),
      bench('Low-thrust plane change of exactly 2 rad costs the sum of the circular speeds', transfer({ ...q, di: 2 }, { ...on, impulsive: false, coplanar: false }).dvTot, s.vc1 + s.vc2, 'Edelbaum (1961): cos(π·Δi/2) = −1 at Δi = 2 rad, so Δv = v_c1 + v_c2', 1e-12),
      bench('Low-thrust plane change beyond 2 rad stays at the sum of the circular speeds', transfer({ ...q, di: 3 }, { ...on, impulsive: false, coplanar: false }).dvTot, s.vc1 + s.vc2, 'Spiral out to escape, turn at no cost, spiral back', 1e-12),
      bench('Geostationary transfer time of flight', s.main.tof, Math.PI * Math.sqrt(at ** 3 / q.GM), 'Half the Kepler period of the transfer ellipse', 1e-12),
    ];
  },
  validation: [],
  diagram(v, a) {
    const rmax = Math.max(v.r_1, v.r_2, a.impulsive && !a.hohmann ? v.r_b : 0), sc = 150 / rmax, cx = 320, cy = 180;
    const R1 = Math.max(v.r_1 * sc, 4), R2 = Math.max(v.r_2 * sc, 4), s = transfer(v, a);
    const arc = (ra, rb, flip) => { const th = N.linspace(0, Math.PI, 40); return S.poly(th.map(t => { const r = 2 * ra * rb / ((ra + rb) + (rb - ra) * Math.cos(t)) * sc, tt = t + (flip ? Math.PI : 0); return [(cx + r * Math.cos(tt)).toFixed(1), (cy - r * Math.sin(tt)).toFixed(1)]; }), 'd-line d-heat'); };
    return svg(`
      ${S.circle(cx, cy, R1, 'd-line')} ${S.circle(cx, cy, R2, 'd-line')} ${S.circle(cx, cy, 5, 'd-body')}
      ${a.impulsive ? s.main.legs.map(([ra, rb], k) => arc(ra, rb, k === 1)).join('') : S.text(cx, cy - 20, 'slow spiral', 'd-text d-small')}
      ${S.text(40, 40, `r₁ = ${lab(v.r_1 / 1000, 'km')}`, 'd-text', 'start')} ${S.text(40, 60, `r₂ = ${lab(v.r_2 / 1000, 'km')}`, 'd-text', 'start')}
      ${S.text(600, 40, `Δv total = ${lab(s.dvTot / 1000, 'km/s')}`, 'd-text', 'end')}
      ${S.text(600, 60, s.main.dv.map((d, i) => `Δv${i + 1} = ${lab(d / 1000, 'km/s')}`).join('   '), 'd-text d-small', 'end')}
      ${S.text(320, 345, `${s.main.kind} transfer, ${a.impulsive ? 'flight time' : 'thrusting time'} ${lab(s.main.tof / 3600, 'h')}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Confirm the predicted velocity increments and flight time by comparing with tracked orbit-raising manoeuvres of a spacecraft, or with a high-fidelity numerical propagation.',
    apparatus: ['Published orbital elements of a geostationary-transfer mission before and after each apogee burn', 'Orbit propagator including the J₂ term for cross-checking', 'Telemetry of engine burn duration and accelerometer-integrated velocity change'],
    instruments: [{ name: 'Radar or laser ranging and radiometric tracking', measures: 'Orbital elements', range: '—', resolution: 'position to tens of metres' }, { name: 'On-board accelerometers', measures: 'Delivered velocity increment per burn', range: '0–3 km/s', resolution: '±0.1 %' }, { name: 'Propellant gauging', measures: 'Propellant consumed', range: '—', resolution: '±1 %' }],
    procedure: ['Obtain element sets before and after each burn.', 'Compute perigee and apogee speeds from vis-viva and compare the change with the accelerometer-derived velocity increment.', 'Compare the interval between perigee departure and apogee arrival with half the transfer period.'],
    controls: ['Propagate the transfer numerically with and without J₂ to bound the effect of the point-mass assumption', 'Check the finite-burn loss by splitting a burn across several apogee passes'],
    signatures: ['Total Δv of about 3.9 km/s for an equatorial low-orbit to geostationary transfer', 'Transfer time close to 5.3 h for that case', 'Bi-elliptic advantage only above a radius ratio of about 11.94'],
    safety: ['Collision-avoidance screening of transfer orbits against catalogued objects', 'End-of-life disposal consistent with debris-mitigation guidelines'],
  },
  falsify: ['A two-impulse transfer between coplanar circular orbits achieved with less total velocity increment than the Hohmann value.', 'A measured transfer time differing from half the Kepler period of the ellipse by more than perturbation effects allow.', 'A bi-elliptic transfer cheaper than Hohmann at a radius ratio below 11.94 for coplanar circular orbits.'],
  alternatives: [{ name: 'Finite-burn (gravity-loss) analysis', text: 'Long burns are not impulsive: thrust is applied off the optimum point and the delivered Δv must exceed the impulsive value.' }, { name: 'Lambert targeting', text: 'For rendezvous in a fixed time, or between non-coplanar and non-circular orbits, the two-point boundary-value problem replaces the tangent ellipse.' }, { name: 'Gravity-assist and weak-stability-boundary transfers', text: 'Use a third body to change energy at little propellant cost, at the price of flight time.' }],
  hazards: [{ hazard: 'Stranding in the transfer orbit', cause: 'Apogee-engine failure', mitigation: 'Redundant thrusters, staged burns, contingency orbit-raising plan' }, { hazard: 'Radiation dose', cause: 'Repeated passage through the Van Allen belts on slow transfers', mitigation: 'Shielding and limiting the number of belt crossings' }, { hazard: 'Orbital debris', cause: 'Spent stages left in transfer orbit', mitigation: 'Passivation and perigee lowering for timely re-entry' }],
  standards: ['ISO 24113 (space systems — space debris mitigation requirements)', 'ECSS-E-ST-10-04C (space engineering — space environment)', 'CCSDS 502.0-B (orbit data messages)'],
  limits: 'Point-mass central body, no perturbations (oblateness, third bodies, drag, radiation pressure), impulsive burns unless the low-thrust option is chosen. Radii are measured from the body centre and must exceed its physical radius. The low-thrust result assumes thrust acceleration much smaller than gravity.',
  numerics: { method: 'Closed-form vis-viva and Kepler relations; RK45 two-body propagation for the benchmark' },
  optimise: { objective: 'dv_tot', sense: 'min', vars: ['r_b'], note: 'Relevant with the bi-elliptic option: beyond the cross-over radius ratio a larger intermediate apoapsis lowers Δv.' },
  inverse: { series: 'profile', fit: ['r_2'] },
  extensions: ['Lambert solver for timed rendezvous', 'Finite-burn losses and optimal burn splitting', 'Interplanetary patched-conic transfers with departure and arrival hyperbolae'],
};

// ------------------------------------------------------------------ 5. ballistic atmospheric entry
const K_SG = 1.7415e-4;   // Sutton–Graves stagnation-point heating constant for Earth air, kg^0.5/m
const RHO32 = R.atmosphere(32000).rho;
const erfApprox = x => { const s = Math.sign(x), z = Math.abs(x), t = 1 / (1 + 0.3275911 * z); return s * (1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-z * z)); };
/** Vertex of the parabola through three equally spaced samples around index i: returns [offset in samples, peak value]. */
const vertex = (y, i) => { if (i <= 0 || i >= y.length - 1) return [0, y[i]]; const d = y[i - 1] - 2 * y[i] + y[i + 1]; if (!(Math.abs(d) > 0)) return [0, y[i]]; const o = 0.5 * (y[i - 1] - y[i + 1]) / d; return [o, y[i] - 0.25 * (y[i - 1] - y[i + 1]) * o]; };
function entryRun(v, a) {
  const rhoOf = h => (a.exp_atm ? v.rho_0 * Math.exp(-h / v.H) : h < 32000 ? R.atmosphere(Math.max(h, 0)).rho : RHO32 * Math.exp(-(h - 32000) / v.H));
  const gOf = h => (a.no_gravity ? 0 : v.g_s * (v.R_p / (v.R_p + h)) ** 2), LD = a.ballistic ? 0 : v.LD;
  const f = (t, y) => {
    const [V, gam, h] = y, rho = rhoOf(h), g = gOf(h), k = rho * V / (2 * v.beta);
    let dg = -k * LD;
    if (!a.straight) dg += (g / Math.max(V, 1) - V / (v.R_p + h)) * Math.cos(gam);
    return [-k * V + g * Math.sin(gam), dg, -V * Math.sin(gam), V * Math.cos(gam) * v.R_p / (v.R_p + h), K_SG * Math.sqrt(rho / v.R_n) * Math.abs(V) ** 3, k * V * V];
  };
  const vStop = a.no_gravity ? 0.01 * v.V_E : -1;
  const gf = y => Math.min(y[2] / v.h_E, 1 + 2000 / v.h_E - y[2] / v.h_E, (y[0] - vStop) / v.V_E);
  const s = toEvent(f, [v.V_E, v.gamma_E, v.h_E, 0, 0, 0], 4000, gf, null, 401, { rtol: 1e-9, atol: 1e-7, maxSteps: 40000 });
  const n = s.t.length, V = s.y[0], gam = s.y[1], h = s.y[2];
  const rho = h.map(rhoOf), dec = V.map((x, i) => rho[i] * x * x / (2 * v.beta)), q = V.map((x, i) => K_SG * Math.sqrt(rho[i] / v.R_n) * x ** 3);
  const ia = dec.indexOf(N.maxOf(dec)), iq = q.indexOf(N.maxOf(q)), va = vertex(dec, ia), vq = vertex(q, iq);
  const at = (arr, i, o) => { const j = N.clamp(i + (o > 0 ? 1 : -1), 0, n - 1); return arr[i] + (arr[j] - arr[i]) * Math.abs(o); };
  const yf = s.yHit, end = !s.hit ? 3 : yf[2] <= 1 ? 0 : yf[2] >= v.h_E + 1000 ? 1 : 2;
  return { s, n, V, gam, h, rho, dec, q, aMax: va[1], hA: at(h, ia, va[0]), VA: at(V, ia, va[0]), qMax: vq[1], hQ: at(h, iq, vq[0]), yf, end, tEnd: s.tHit, rhoOf };
}
const ENTRY_ENDS = ['Reaches the surface', 'Skips back out of the atmosphere', 'Decelerated to 1 % of entry speed before reaching the surface', 'Still in flight at the end of the simulated time'];
const AE_ON = { no_gravity: true, straight: true, exp_atm: true, ballistic: true };
const entry = {
  id: 'atmospheric-entry',
  title: 'Ballistic atmospheric entry (Allen–Eggers)',
  module: 2, klass: 'I', domains: ['space', 'aerospace', 'thermal'],
  keywords: ['allen-eggers', 'atmospheric entry', 'ballistic entry', 're-entry', 'reentry', 'peak deceleration', 'ballistic coefficient', 'entry heating', 'stagnation heating', 'sutton-graves', 'heat shield', 'entry capsule', 'entry', 'deceleration', 'flight-path angle', 'meteor'],
  summary: 'Velocity, deceleration and stagnation-point heating of a body entering an exponential atmosphere, with the Allen–Eggers closed-form solution checked against numerical integration of the planar entry equations.',
  background: [
    'A body entering an atmosphere at orbital speed is slowed almost entirely by drag over a few scale heights. Allen and Eggers showed that for a steep ballistic entry, where gravity is small against drag and the path is nearly straight, the velocity depends on altitude through a simple exponential of the local density, and that the peak deceleration depends only on entry speed, entry angle and atmospheric scale height — not on the mass or size of the body.',
    'The ballistic coefficient m/(C_D A) sets the altitude at which the deceleration occurs. Convective heating at the stagnation point scales with the square root of density over nose radius and the cube of speed (Sutton and Graves), which is why blunt bodies survive entry.',
  ],
  phenomena: ['Hypersonic drag deceleration', 'Exponential density variation', 'Stagnation-point convective heating', 'Radiative cooling of the surface', 'Gravity turn and skip-out for shallow or lifting entries'],
  laws: ['newton2', 'momentum', 'energy', 'gravitation', 'stefan'],
  refs: ['Allen, H. J. & Eggers, A. J. (1958). A study of the motion and aerodynamic heating of ballistic missiles entering the Earth\'s atmosphere at high supersonic speeds. NACA Report 1381.', 'Chapman, D. R. (1959). An approximate analytical method for studying entry into planetary atmospheres. NASA TR R-11.', 'Sutton, K. & Graves, R. A. (1971). A general stagnation-point convective-heating equation for arbitrary gas mixtures. NASA TR R-376.', 'Regan, F. J. & Anandakrishnan, S. M. (1993). Dynamics of Atmospheric Re-Entry. AIAA Education Series.', 'Vinh, N. X., Busemann, A. & Culp, R. D. (1980). Hypersonic and Planetary Entry Flight Mechanics. University of Michigan Press.'],
  inputs: [
    inp('V_E', 'Entry speed', 'km/s', 7.5, { min: 1, max: 15, aliases: ['entry speed', 'entry velocity', 'speed', 'velocity'], src: 'Return from low Earth orbit' }),
    inp('gamma_E', 'Entry flight-path angle below the horizontal', 'deg', 30, { min: 3, max: 90, aliases: ['flight-path angle', 'entry angle', 'flight path angle'] }),
    inp('beta', 'Ballistic coefficient m/(C_D A)', 'kg/m^2', 500, { min: 10, max: 20000, aliases: ['ballistic coefficient'], src: 'Blunt capsule 300–500 kg/m²; slender warhead above 5000 kg/m²' }),
    inp('R_n', 'Nose radius', 'm', 0.5, { min: 0.01, max: 5, kind: 'geometry', aliases: ['nose radius'] }),
    inp('h_E', 'Entry-interface altitude', 'km', 120, { min: 60, max: 200, kind: 'geometry', aliases: ['entry interface', 'entry altitude', 'altitude'], src: 'Conventional Earth entry interface' }),
    inp('rho_0', 'Reference surface density of the exponential fit', 'kg/m^3', 1.225, { min: 0.005, max: 100, kind: 'environment', aliases: ['surface density', 'air density'] }),
    inp('H', 'Density scale height', 'km', 7.2, { min: 4, max: 20, kind: 'environment', aliases: ['scale height'], src: 'Exponential fit to the standard atmosphere over entry altitudes, about 7 km' }),
    inp('g_s', 'Surface gravitational acceleration', 'm/s^2', 9.80665, { min: 0.5, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity'] }),
    inp('R_p', 'Planet radius', 'km', 6371, { min: 500, max: 80000, kind: 'environment', aliases: ['planet radius'] }),
    inp('LD', 'Lift-to-drag ratio (lifting entry)', '1', 0.3, { min: 0, max: 2, aliases: ['lift-to-drag', 'l/d'], src: 'Apollo-type capsule flown at trim' }),
    inp('eps_w', 'Surface emissivity', '1', 0.85, { min: 0.1, max: 1, kind: 'fluid', aliases: ['emissivity'] }),
  ],
  assumptions: [
    asm('no_gravity', 'Gravity is negligible against drag during the deceleration pulse.', { why: 'Steep, fast entry: drag is tens of g', alt: 'Inverse-square gravity is included in the equations of motion.' }),
    asm('straight', 'The flight-path angle stays at its entry value (straight-line path).', { why: 'Steep entry over a short arc', alt: 'The path curves under gravity and the curvature of the planet.' }),
    asm('exp_atm', 'Density falls exponentially with altitude with a single scale height.', { why: 'Needed for the closed-form solution', alt: 'ISO standard-atmosphere density below 32 km, continued exponentially above.' }),
    asm('ballistic', 'The body generates no lift.', { why: 'Axisymmetric body at zero incidence', alt: 'A constant lift-to-drag ratio turns the path upward (lifting entry).' }),
  ],
  symbols: { V: ['Speed', 'm/s'], gamma: ['Flight-path angle below the horizontal', 'rad'], z: ['Altitude', 'm'], t: ['Time', 's'], rho: ['Atmospheric density', 'kg/m^3'], g_h: ['Local gravitational acceleration', 'm/s^2'], a_AE: ['Peak deceleration from the Allen–Eggers solution', 'm/s^2'], q_s: ['Stagnation-point heat flux', 'W/m^2'], k_SG: ['Sutton–Graves constant, 1.7415×10⁻⁴', 'kg^0.5/m'], T_w: ['Radiative-equilibrium wall temperature', 'K'], z_AE: ['Altitude of peak deceleration from the Allen–Eggers solution', 'm'], rho_32: ['Standard-atmosphere density at 32 km', 'kg/m^3'], z_32: ['Matching altitude, 32 km', 'm'] },
  equations: a => {
    const ae = a.no_gravity && a.straight && a.ballistic;
    const turn = [...(a.straight ? [] : [a.no_gravity ? '-V/(R_p + z)*cos(gamma)' : '(g_h/V - V/(R_p + z))*cos(gamma)']), ...(a.ballistic ? [] : ['- rho*V*LD/(2*beta)'])].join(' ');
    return [
      a.exp_atm ? eq('rho', 'Atmospheric density', 'rho', 'rho_0*exp(-z/H)', { kind: 'closure', origin: 'Isothermal hydrostatic atmosphere', needs: ['exp_atm'] })
        : eq('rho', 'Atmospheric density above 32 km', 'rho', 'rho_32*exp(-(z - z_32)/H)', { kind: 'closure', origin: 'Exponential continuation of the standard atmosphere', exportable: false, note: 'ρ₃₂ is the ISO 2533 density at 32 km. Below 32 km the tabulated standard-atmosphere density is used instead, and the stated surface density plays no part.' }),
      eq('drag', 'Along-path momentum', 'd(V,t)', `-rho*V^2/(2*beta)${a.no_gravity ? '' : ' + g_h*sin(gamma)'}`, { kind: 'law', origin: 'Newton\'s second law along the flight path', needs: a.no_gravity ? ['no_gravity'] : [] }),
      eq('alt', 'Altitude rate', 'd(z,t)', '-V*sin(gamma)', { kind: 'definition' }),
      turn ? eq('turn', 'Flight-path angle rate', 'd(gamma,t)', turn, { kind: 'law', origin: 'Newton\'s second law normal to the flight path over a spherical planet' })
        : eq('turn', 'Flight-path angle', 'gamma', 'gamma_E', { kind: 'closure', origin: 'Straight-line path', needs: ['straight', 'ballistic'] }),
      ...(a.no_gravity ? [] : [eq('grav', 'Local gravity', 'g_h', 'g_s*(R_p/(R_p + z))^2', { kind: 'law', origin: 'Newton\'s law of gravitation' })]),
      ...(ae && a.exp_atm ? [
        eq('ae', 'Allen–Eggers velocity', 'V', 'V_E*exp(-rho*H/(2*beta*sin(gamma_E)))', { kind: 'derived', origin: 'Allen & Eggers (1958)', needs: ['no_gravity', 'straight', 'exp_atm', 'ballistic'] }),
        eq('amax', 'Peak deceleration (Allen–Eggers)', 'a_AE', 'V_E^2*sin(gamma_E)/(2*exp(1)*H)', { kind: 'derived', origin: 'Maximum of ρV²/(2β) along the Allen–Eggers solution', needs: ['no_gravity', 'straight', 'exp_atm', 'ballistic'] }),
        eq('za', 'Altitude of peak deceleration (Allen–Eggers)', 'z_AE', 'H*ln(rho_0*H/(beta*sin(gamma_E)))', { kind: 'derived', origin: 'Density at the peak equals β sin γ / H', needs: ['no_gravity', 'straight', 'exp_atm', 'ballistic'] }),
      ] : []),
      eq('heat', 'Stagnation-point convective heat flux', 'q_s', 'k_SG*sqrt(rho/R_n)*V^3', { kind: 'empirical', origin: 'Sutton & Graves (1971), cold-wall, Earth air' }),
      eq('wall', 'Radiative-equilibrium wall temperature', 'q_s', 'eps_w*sigma_SB*T_w^4', { kind: 'law', origin: 'Stefan–Boltzmann law with convective heating balanced by re-radiation' }),
    ];
  },
  derivation: a => [
    { text: 'Resolve Newton\'s second law along the flight path. Drag per unit mass is ρV²/(2β), with β = m/(C_D A) the ballistic coefficient.', tex: '\\frac{\\mathrm{d}V}{\\mathrm{d}t} = -\\frac{\\rho V^2}{2\\beta} + g\\sin\\gamma,\\qquad \\frac{\\mathrm{d}z}{\\mathrm{d}t} = -V\\sin\\gamma' },
    { text: 'Neglect gravity and hold γ fixed. Dividing the two equations removes time, and with ρ = ρ₀e^{−z/H} the altitude can be replaced by density.', tex: '\\frac{\\mathrm{d}V}{V} = -\\frac{H}{2\\beta\\sin\\gamma_E}\\,\\mathrm{d}\\rho' },
    { text: 'Integrating from the top of the atmosphere, where ρ → 0 and V = V_E, gives the Allen–Eggers velocity profile.', tex: 'V = V_E\\exp\\!\\left(-\\frac{\\rho H}{2\\beta\\sin\\gamma_E}\\right)' },
    { text: 'The deceleration ρV²/(2β) is greatest where ρ = β sin γ_E / H. There the speed has fallen to V_E/√e and the peak deceleration is independent of β.', tex: 'a_{max} = \\frac{V_E^2\\sin\\gamma_E}{2eH},\\qquad z_a = H\\ln\\frac{\\rho_0 H}{\\beta\\sin\\gamma_E}' },
    { text: 'Stagnation-point convective heating follows the Sutton–Graves correlation. Along the Allen–Eggers path it peaks earlier, where ρ = β sin γ_E/(3H) and V = V_E e^{−1/6}.', tex: '\\dot q_s = k\\sqrt{\\frac{\\rho}{R_n}}\\,V^3,\\qquad \\dot q_{max} = k\\sqrt{\\frac{\\beta\\sin\\gamma_E}{3HR_n}}\\;V_E^3\\,e^{-1/2}' },
    ...(a.no_gravity && a.straight && a.ballistic ? [] : [{ text: 'With the simplifications removed, the component of Newton\'s law normal to the path governs the flight-path angle: gravity steepens it, the centrifugal term and lift flatten it.', tex: 'V\\frac{\\mathrm{d}\\gamma}{\\mathrm{d}t} = \\left(g - \\frac{V^2}{R_p+z}\\right)\\cos\\gamma - \\frac{\\rho V^2}{2\\beta}\\,\\frac{L}{D}' }]),
  ],
  solve(v, a) {
    const r = entryRun(v, a), sg = Math.sin(v.gamma_E), B = v.rho_0 * v.H / (2 * v.beta * sg);
    const aAE = v.V_E ** 2 * sg / (2 * Math.E * v.H), hAE = v.H * Math.log(2 * B), qAE = K_SG * Math.sqrt(v.beta * sg / (3 * v.H * v.R_n)) * v.V_E ** 3 * Math.exp(-0.5);
    const Q = r.yf[4], Tw = Math.pow(Math.max(r.qMax, 0) / (v.eps_w * C.sigma_SB), 0.25), warnings = [];
    if (2 * B <= 1) warnings.push('The ballistic coefficient is so high that the Allen–Eggers deceleration peak would lie below the surface: the body reaches the ground still decelerating, and the closed-form peak is not attained.');
    if (a.no_gravity && v.gamma_E < 10 * DEG) warnings.push('The entry is shallow: gravity and path curvature are not negligible, so the Allen–Eggers assumptions are poor. Switch them off to integrate the full equations.');
    if (r.end === 1) warnings.push('The body skips back out of the atmosphere; the simulation stops when it climbs above the entry interface.');
    if (v.V_E > 9000) warnings.push('Above about 9 km/s radiative heating from the shock layer becomes important and is not included in the Sutton–Graves convective estimate.');
    if (!a.exp_atm) warnings.push('The standard-atmosphere option ignores the stated surface density; the scale height is used only above 32 km.');
    const hk = r.h.map(x => x / 1000), sub = every(r.n, 300), pick = arr => arr.filter((_, i) => i % sub === 0 || i === arr.length - 1);
    const VAE = r.h.map(h => v.V_E * Math.exp(-B * Math.exp(-h / v.H)));
    return {
      scalars: [
        scalar('a_max', 'Peak deceleration (numerical)', r.aMax, 'm/s^2', { show: 'g0' }), scalar('a_AE', 'Peak deceleration (Allen–Eggers)', aAE, 'm/s^2', { show: 'g0', note: 2 * B <= 1 ? 'peak would lie below the surface' : undefined }),
        scalar('z_a', 'Altitude of peak deceleration (numerical)', r.hA, 'm', { show: 'km' }), scalar('z_AE', 'Altitude of peak deceleration (Allen–Eggers)', hAE, 'm', { show: 'km' }),
        scalar('V_a', 'Speed at peak deceleration', r.VA, 'm/s', { show: 'km/s' }),
        scalar('q_max', 'Peak stagnation-point heat flux (numerical)', r.qMax, 'W/m^2', { show: 'MW/m^2' }), scalar('q_AE', 'Peak stagnation-point heat flux (Allen–Eggers)', qAE, 'W/m^2', { show: 'MW/m^2' }),
        scalar('z_q', 'Altitude of peak heating', r.hQ, 'm', { show: 'km' }), scalar('Q_s', 'Stagnation-point heat load', Q, 'J/m^2', { show: 'MJ/m^2' }),
        scalar('T_w', 'Radiative-equilibrium wall temperature at peak heating', Tw, 'K'),
        scalar('V_f', 'Speed at the end of the simulation', r.yf[0], 'm/s'), scalar('t_f', 'Simulated flight time', r.tEnd, 's'),
        scalar('s_d', 'Downrange distance along the surface', r.yf[3], 'm', { show: 'km' }), scalar('gamma_f', 'Final flight-path angle below the horizontal', r.yf[1], 'rad', { show: 'deg' }),
        scalar('end', 'Outcome', r.end, '1', { text: ENTRY_ENDS[r.end] }),
      ],
      series: [
        line('v-alt', 'Speed against altitude', 'Altitude', 'km', pick(hk), [{ label: 'Numerical', data: pick(r.V).map(x => x / 1000) }, { label: 'Allen–Eggers', data: pick(VAE).map(x => x / 1000), dash: true }], 'Speed', 'km/s'),
        line('dec-alt', 'Deceleration against altitude', 'Altitude', 'km', pick(hk), [{ label: 'Numerical', data: pick(r.dec).map(x => x / G0) }, { label: 'Allen–Eggers', data: pick(r.h.map((h, i) => v.rho_0 * Math.exp(-h / v.H) * VAE[i] ** 2 / (2 * v.beta))).map(x => x / G0), dash: true }], 'Deceleration', 'g₀'),
        line('heat-alt', 'Stagnation-point heat flux against altitude', 'Altitude', 'km', pick(hk), [{ label: 'Heat flux', data: pick(r.q).map(x => x / 1e6) }], 'Heat flux', 'MW/m²'),
        line('alt-time', 'Altitude and speed against time', 'Time', 's', pick(r.s.t), [{ label: 'Altitude (km)', data: pick(hk) }, { label: 'Speed (0.1 km/s)', data: pick(r.V).map(x => x / 100) }], 'Value', 'see legend'),
      ],
      checks: [
        check('Energy balance', (() => { const e0 = 0.5 * v.V_E ** 2, grav = a.no_gravity ? 0 : v.g_s * v.R_p ** 2 * (1 / (v.R_p + r.yf[2]) - 1 / (v.R_p + v.h_E)); return (e0 + grav - 0.5 * r.yf[0] ** 2 - r.yf[5]) / e0; })(), 1e-6, 'Kinetic plus potential energy lost against the integrated drag power'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const sg = Math.sin(v.gamma_E), B = v.rho_0 * v.H / (2 * v.beta * sg), out = [];
    if (2 * B < 3) return [bench('Allen–Eggers peak-deceleration identity', Math.exp(-1) * 2, 2 / Math.E, 'ρ* V*² H/(β sin γ V_E²) = e⁻¹ at the peak', 1e-12)];
    const r = entryRun(v, AE_ON), b = v.H / (v.beta * sg);
    out.push(bench('Peak deceleration: numerical integration vs Allen–Eggers', r.aMax, v.V_E ** 2 * sg / (2 * Math.E * v.H), 'a_max = V_E² sin γ / (2 e H)', 2e-3));
    out.push(bench('Speed at peak deceleration vs V_E/√e', r.VA, v.V_E * Math.exp(-0.5), 'Allen & Eggers (1958)', 1e-2));
    out.push(bench('Altitude of peak deceleration vs H ln(ρ₀H/(β sin γ))', r.hA, v.H * Math.log(2 * B), 'Allen & Eggers (1958)', 1e-2));
    out.push(bench('Peak heat flux: numerical vs closed form', r.qMax, K_SG * Math.sqrt(v.beta * sg / (3 * v.H * v.R_n)) * v.V_E ** 3 * Math.exp(-0.5), 'Maximum of √ρ·V³ along the Allen–Eggers path', 2e-3));
    const rhoEnd = r.rhoOf(r.yf[2]), rhoTop = r.rhoOf(v.h_E);
    out.push(bench('Heat load: numerical vs closed form', r.yf[4], K_SG * v.H * v.V_E ** 2 * Math.sqrt(Math.PI / b) * (erfApprox(Math.sqrt(b * rhoEnd)) - erfApprox(Math.sqrt(b * rhoTop))) / (sg * Math.sqrt(v.R_n)), 'Error-function integral of the heating rate along the Allen–Eggers path', 2e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const g = N.clamp(v.gamma_E / DEG, 3, 90) * DEG, x0 = 110, y0 = 70, len = 300, x1 = x0 + len * Math.cos(g), y1 = y0 + len * Math.sin(g) * 0.8;
    return svg(`
      ${S.path('M30 300 Q320 262 610 300', 'd-ground')} ${S.text(600, 322, `planet surface, radius ${lab(v.R_p / 1000, 'km')}`, 'd-text d-small', 'end')}
      ${S.path('M30 70 Q320 40 610 70', 'd-dim')} ${S.text(600, 50, `entry interface ${lab(v.h_E / 1000, 'km')}`, 'd-text d-small', 'end')}
      ${[0, 1, 2, 3].map(i => S.path(`M30 ${150 + i * 40} Q320 ${118 + i * 40} 610 ${150 + i * 40}`, 'd-dim')).join('')}
      ${S.arrow(x0, y0, x1, y1)} ${S.circle(x0, y0, 9, 'd-body')}
      ${S.line(x0, y0, x0 + 110, y0, 'd-dim')} ${S.text(x0 + 120, y0 + 22, `γ = ${lab(v.gamma_E / DEG, '°')}`, 'd-text', 'start')}
      ${S.text(x0 - 10, y0 - 18, `V_E = ${lab(v.V_E / 1000, 'km/s')}`, 'd-text', 'start')}
      ${S.rect((x0 + x1) / 2 + 16, (y0 + y1) / 2 - 12, 150, 24, 'd-hazard', 6)} ${S.text((x0 + x1) / 2 + 91, (y0 + y1) / 2 + 5, 'peak deceleration and heating', 'd-text d-small')}
      ${S.text(40, 340, `β = ${lab(v.beta, 'kg/m²')}    nose radius ${lab(v.R_n, 'm')}    ρ = ρ₀ exp(−z/H), H = ${lab(v.H / 1000, 'km')}${a.ballistic ? '' : `    L/D = ${lab(v.LD)}`}`, 'd-text d-small', 'start')}
    `);
  },
  experiment: {
    objective: 'Compare the deceleration history recorded by an instrumented entry capsule or sounding-rocket payload with the predicted pulse, and its heat-shield thermocouple record with the predicted heating.',
    apparatus: ['Blunt entry capsule of known mass, reference area and nose radius', 'Sounding rocket or orbital deorbit providing a known entry speed and angle', 'Recovery system and tracking radar'],
    instruments: [{ name: 'Three-axis accelerometer', measures: 'Deceleration pulse', range: '0–100 g', resolution: '±0.1 g at ≥ 100 Hz' }, { name: 'Heat-shield thermocouples and calorimeter plugs', measures: 'Surface and in-depth temperature; heat flux', range: 'to 2000 K', resolution: '±1 %' }, { name: 'Tracking radar and GNSS', measures: 'Trajectory: altitude, speed, flight-path angle', range: '—', resolution: '±10 m, ±1 m/s' }, { name: 'Radiosonde launched at the time of entry', measures: 'Atmospheric density profile', range: '0–35 km', resolution: '±1 %' }],
    procedure: ['Determine mass, reference area and drag coefficient before flight to fix the ballistic coefficient.', 'Record acceleration, surface temperatures and tracking data through entry.', 'Reconstruct the trajectory and density profile, then overlay measured deceleration against altitude on the prediction.'],
    controls: ['Arc-jet test of a heat-shield sample at the predicted peak heat flux', 'Hypersonic wind-tunnel or ballistic-range measurement of the drag coefficient'],
    signatures: ['Peak deceleration independent of ballistic coefficient for steep entries at the same speed and angle', 'Speed at the deceleration peak close to 61 % of entry speed', 'Peak heating preceding peak deceleration'],
    safety: ['Range clearance for the impact footprint', 'Pyrotechnic and pressurised-system handling procedures', 'Hot-surface and toxic-ablation-product precautions on recovery'],
  },
  falsify: ['Peak deceleration of steep ballistic entries depending strongly on ballistic coefficient at fixed entry speed and angle.', 'A measured speed at the deceleration peak far from V_E/√e for a steep entry in a near-exponential atmosphere.', 'Stagnation heat flux not scaling as the inverse square root of nose radius at fixed flight condition.'],
  alternatives: [{ name: 'Chapman\'s entry theory', text: 'A single transformed equation covering shallow and lifting entries where gravity and centrifugal terms matter.' }, { name: 'Equilibrium glide', text: 'For lifting vehicles lift balances the difference between weight and centrifugal force; deceleration is then gentle and set by L/D.' }, { name: 'Coupled aerothermodynamics', text: 'Computational fluid dynamics with chemistry, ablation and radiation replaces the Sutton–Graves correlation for design.' }],
  hazards: [{ hazard: 'Heat-shield burn-through', cause: 'Heat flux or heat load above the material capability', mitigation: 'Ablator sizing with margin, arc-jet qualification' }, { hazard: 'Excessive deceleration', cause: 'Entry too steep', mitigation: 'Entry-corridor control; lifting entry for crewed vehicles' }, { hazard: 'Skip-out or uncontrolled footprint', cause: 'Entry too shallow', mitigation: 'Guidance within the entry corridor; debris-footprint analysis' }],
  standards: ['ISO 27875 (space systems — re-entry risk management for unmanned spacecraft and launch vehicle orbital stages)', 'ECSS-E-ST-31C (space engineering — thermal control general requirements)', 'NASA-STD-8719.14 (process for limiting orbital debris)'],
  limits: 'Planar entry over a non-rotating spherical planet, constant ballistic coefficient and lift-to-drag ratio, continuum hypersonic flow. The closed form needs steep entries (roughly above 10°) and an exponential atmosphere. The heating constant is for Earth air, cold wall, convective heating only; no ablation, radiation from the shock layer, or rarefied-flow effects.',
  numerics: { method: 'Adaptive Dormand–Prince RK45 with Newton location of the terminating event; three-point parabolic refinement of the peaks', order: 5, stability: 'Step-size controlled to a relative tolerance of 10⁻⁹' },
  optimise: { objective: 'q_max', sense: 'min', vars: ['R_n'], note: 'Heat flux falls as the inverse square root of nose radius: the blunt-body principle.' },
  inverse: { series: 'dec-alt', fit: ['beta', 'H'] },
  extensions: ['Entry corridor: overshoot and undershoot boundaries', 'Bank-angle modulation for a lifting capsule', 'Ablating heat-shield response coupled to the heat-flux history'],
};

// ------------------------------------------------------------------ 6. two-body orbit
function keplerRun(v, a) {
  const mu = v.GM * (a.fixed_centre ? 1 : 1 + v.q_m), r0 = v.r_0, vt = v.v_0 * Math.cos(v.phi), vr = v.v_0 * Math.sin(v.phi), hA = r0 * vt;
  const kJ = a.point_mass ? 0 : 1.5 * mu * v.J_2 * v.R_b ** 2, kG = a.newtonian ? 0 : 3 * mu * hA * hA / C.c ** 2, k4 = kJ + kG;
  const eps = v.v_0 ** 2 / 2 - mu / r0, bound = eps < 0, sma = -mu / (2 * eps), ecc = Math.sqrt(Math.max(0, 1 + 2 * eps * hA * hA / (mu * mu)));
  const p = hA * hA / mu, rp = p / (1 + ecc), ra = bound ? sma * (1 + ecc) : Infinity;
  const Tc = 2 * Math.PI * Math.sqrt(r0 ** 3 / mu), T = bound ? 2 * Math.PI * Math.sqrt(sma ** 3 / mu) : NaN, unit = bound ? T : Tc;
  const boost = N.clamp(unit / (2 * Math.PI * Math.sqrt(Math.max(rp, 1e-4 * r0) ** 3 / mu)), 1, 50);
  const n = Math.max(20, Math.min(Math.round(v.n_orb * v.n_step * boost), 80000)), tEnd = v.n_orb * unit, stride = every(n, 20000);
  const floor2 = (1e-5 * r0) ** 2;
  const acc = (q, o) => { const r2 = Math.max(q[0] * q[0] + q[1] * q[1], floor2), r = Math.sqrt(r2), s = -mu / (r2 * r) - k4 / (r2 * r2 * r); o[0] = s * q[0]; o[1] = s * q[1]; };
  const run = (a.symplectic ? yoshida4 : rk4second)(acc, [r0, 0], [vr, vt], tEnd / n, n, stride);
  const m = run.t.length, r = new Array(m), sp = new Array(m), en = new Array(m), hh = new Array(m), th = new Array(m), om = new Array(m);
  for (let i = 0; i < m; i++) {
    const x = run.q[i][0], y = run.q[i][1], ux = run.v[i][0], uy = run.v[i][1];
    r[i] = Math.hypot(x, y); sp[i] = Math.hypot(ux, uy); hh[i] = x * uy - y * ux; om[i] = hh[i] / (r[i] * r[i]);
    en[i] = 0.5 * sp[i] ** 2 - mu / r[i] - k4 / (3 * r[i] ** 3);
    if (i === 0) th[i] = 0; else { let d = Math.atan2(y, x) - Math.atan2(run.q[i - 1][1], run.q[i - 1][0]); if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI; th[i] = th[i - 1] + d; }
  }
  // sidereal period: time at which the swept angle reaches 2π (angular rate taken as linear across the step)
  let Tnum = NaN; const sgn = Math.sign(hA) || 1;
  for (let i = 1; i < m; i++) if (sgn * th[i] >= 2 * Math.PI) {
    const dt = run.t[i] - run.t[i - 1], need = 2 * Math.PI - sgn * th[i - 1], w0 = sgn * om[i - 1], w1 = sgn * om[i], al = (w1 - w0) / dt;
    const tau = Math.abs(al) > 1e-14 * w0 / dt ? (-w0 + Math.sqrt(Math.max(w0 * w0 + 2 * al * need, 0))) / al : need / w0;
    Tnum = run.t[i - 1] + tau; break;
  }
  // successive periapsis passages for the apsidal advance
  const peri = [];
  if (ecc > 1e-3) for (let i = 1; i < m - 1; i++) if (r[i] < r[i - 1] && r[i] <= r[i + 1]) { const o = vertex(r, i)[0]; peri.push(th[i] + o * (o > 0 ? th[i + 1] - th[i] : th[i] - th[i - 1])); }
  const adv = peri.length >= 2 ? sgn * (peri[peri.length - 1] - peri[0]) / (peri.length - 1) - 2 * Math.PI : NaN;
  const pe = bound ? p : NaN;
  const advTh = (a.newtonian ? 0 : 6 * Math.PI * mu / (C.c ** 2 * pe)) + (a.point_mass ? 0 : 3 * Math.PI * v.J_2 * (v.R_b / pe) ** 2);
  const e0 = en[0], escale = Math.max(Math.abs(e0), 0.5 * v.v_0 ** 2);
  return { mu, r0, hA, k4, eps, bound, sma, ecc, p, rp, ra, T, Tc, tEnd, n, run, m, r, sp, th, Tnum, adv, advTh, dE: en.map(e => (e - e0) / escale), dH: hh.map(x => (x - hA) / (Math.abs(hA) || 1)) };
}
const AU = 1.495978707e11;
const twoBody = {
  id: 'orbital-two-body',
  title: 'Two-body orbit by symplectic integration',
  module: [1, 2], klass: 'I', domains: ['classical', 'space'],
  keywords: ['two-body problem', 'kepler orbit', 'keplerian orbit', 'kepler\'s third law', 'orbital period', 'elliptical orbit', 'symplectic', 'perihelion precession', 'planetary orbit', 'two-body', 'orbit', 'satellite orbit', 'eccentricity', 'semi-major axis', 'escape velocity', 'planet'],
  summary: 'Planar motion of a body under inverse-square gravity, integrated from an initial position and velocity with a fourth-order symplectic scheme, with conservation checks and comparison against Kepler\'s laws.',
  background: [
    'Two bodies attracting each other by Newtonian gravity move so that their separation traces a conic section: an ellipse when the total energy is negative, a parabola at zero and a hyperbola above. Energy and angular momentum are conserved, and for bound motion the period depends only on the semi-major axis (Kepler\'s third law).',
    'A numerical integrator that respects the Hamiltonian structure of the problem — a symplectic scheme — does not let the energy drift secularly, which makes it the method of choice for long orbit integrations. Small departures from the inverse-square law, such as the oblateness of the central body or the leading relativistic correction, make the ellipse precess.',
  ],
  phenomena: ['Inverse-square central force', 'Conservation of energy and angular momentum', 'Closed elliptical orbits', 'Apsidal precession under perturbations'],
  laws: ['gravitation', 'newton2', 'energy', 'angular', 'noether'],
  refs: ['Newton, I. (1687). Philosophiæ Naturalis Principia Mathematica. Royal Society, London.', 'Goldstein, H., Poole, C. & Safko, J. (2002). Classical Mechanics, 3rd ed., Addison-Wesley.', 'Yoshida, H. (1990). Construction of higher order symplectic integrators. Physics Letters A 150, 262–268.', 'Murray, C. D. & Dermott, S. F. (1999). Solar System Dynamics. Cambridge University Press.', 'Einstein, A. (1915). Erklärung der Perihelbewegung des Merkur aus der allgemeinen Relativitätstheorie. Sitzungsberichte der Preussischen Akademie der Wissenschaften, 831–839.', 'Clemence, G. M. (1947). The relativity effect in planetary motions. Reviews of Modern Physics 19, 361–364.'],
  inputs: [
    inp('GM', 'Gravitational parameter of the central body', 'm^3/s^2', 1.32712440018e20, { min: 1e8, max: 1e22, kind: 'environment', aliases: ['gravitational parameter', 'gm', 'mu'], src: 'Sun (IAU nominal). Earth 3.986×10¹⁴ m³/s²' }),
    inp('r_0', 'Initial distance from the centre', 'AU', 1, { min: 1e-5, max: 1000, kind: 'geometry', aliases: ['initial distance', 'distance', 'radius', 'orbital radius'] }),
    inp('v_0', 'Initial speed', 'km/s', 29.7847, { min: 0.01, max: 500, aliases: ['initial speed', 'speed', 'velocity', 'orbital speed'], src: 'Circular speed at 1 AU from the Sun' }),
    inp('phi', 'Initial velocity direction above the local horizontal', 'deg', 0, { min: -80, max: 80, aliases: ['flight-path angle', 'launch angle'] }),
    inp('n_orb', 'Number of orbital periods to simulate', '1', 3, { min: 0.5, max: 20, aliases: ['orbits', 'periods', 'revolutions'] }),
    inp('q_m', 'Mass ratio, orbiting body to central body', '1', 0.01, { min: 0, max: 1, aliases: ['mass ratio'] }),
    inp('J_2', 'Oblateness coefficient J₂ of the central body', '1', 2.2e-7, { min: 0, max: 0.05, kind: 'environment', aliases: ['j2', 'oblateness'], src: 'Solar quadrupole moment, about 2×10⁻⁷ (helioseismology). Earth 1.0826×10⁻³' }),
    inp('R_b', 'Equatorial radius of the central body', 'km', 695700, { min: 1, max: 1e7, kind: 'environment', aliases: ['body radius', 'equatorial radius'], src: 'Sun (IAU nominal)' }),
    inp('n_step', 'Integration steps per orbital period', '1', 2000, { min: 100, max: 20000, kind: 'numerical' }),
  ],
  assumptions: [
    asm('fixed_centre', 'The central body is fixed: the orbiting body is a test mass.', { why: 'Mass ratio much less than 1', alt: 'Both bodies orbit their common centre of mass; the relative motion feels the combined mass.' }),
    asm('newtonian', 'Gravity is exactly Newtonian inverse-square.', { why: 'Weak field, low speed', alt: 'The leading relativistic (Schwarzschild) correction is added, producing perihelion precession.' }),
    asm('point_mass', 'The central body is spherically symmetric (a point mass).', { why: 'Distant orbit', alt: 'The oblateness term J₂ is added for an orbit in the equatorial plane.' }),
    asm('symplectic', 'The equations are integrated with a fourth-order symplectic (Yoshida) scheme.', { why: 'No secular energy drift', alt: 'Classical fourth-order Runge–Kutta with the same step, for comparison of the energy error.' }),
  ],
  symbols: { x: ['Position, first Cartesian component', 'm'], y: ['Position, second Cartesian component', 'm'], t: ['Time', 's'], r: ['Separation', 'm'], v: ['Speed', 'm/s'], v_x: ['Velocity, first component', 'm/s'], v_y: ['Velocity, second component', 'm/s'], eps: ['Specific orbital energy', 'J/kg'], h_a: ['Specific angular momentum', 'm^2/s'], a_sm: ['Semi-major axis', 'm'], ecc: ['Eccentricity', '1'], T_K: ['Kepler period', 's'], mu_g: ['Effective gravitational parameter', 'm^3/s^2'], dw: ['Apsidal advance per orbit', 'rad'] },
  equations: a => {
    const extra = (c) => `${a.point_mass ? '' : ` - 3*mu_g*J_2*R_b^2*${c}/(2*r^5)`}${a.newtonian ? '' : ` - 3*mu_g*h_a^2*${c}/(c^2*r^5)`}`;
    const pre = [a.newtonian ? null : '6*pi*mu_g/(c^2*a_sm*(1 - ecc^2))', a.point_mass ? null : '3*pi*J_2*(R_b/(a_sm*(1 - ecc^2)))^2'].filter(Boolean);
    return [
      a.fixed_centre ? eq('mu', 'Gravitational parameter', 'mu_g', 'GM', { kind: 'definition', needs: ['fixed_centre'] }) : eq('mu', 'Gravitational parameter of the pair', 'mu_g', 'GM*(1 + q_m)', { kind: 'derived', origin: 'Reduction of the two-body problem to relative motion' }),
      eq('mx', 'Equation of motion, x', 'd2(x,t)', `-mu_g*x/r^3${extra('x')}`, { kind: 'law', origin: 'Newton\'s second law with the law of gravitation' }),
      eq('my', 'Equation of motion, y', 'd2(y,t)', `-mu_g*y/r^3${extra('y')}`, { kind: 'law', origin: 'Newton\'s second law with the law of gravitation' }),
      eq('r', 'Separation', 'r', 'sqrt(x^2 + y^2)', { kind: 'definition' }),
      eq('en', 'Specific orbital energy', 'eps', 'v^2/2 - mu_g/r', { kind: 'law', origin: 'Conservation of energy (Keplerian part)' }),
      eq('am', 'Specific angular momentum', 'h_a', 'x*v_y - y*v_x', { kind: 'law', origin: 'Conservation of angular momentum for a central force' }),
      eq('sma', 'Semi-major axis', 'a_sm', '-mu_g/(2*eps)', { kind: 'derived', origin: 'Energy of a Kepler orbit' }),
      eq('ecc', 'Eccentricity', 'ecc', 'sqrt(1 + 2*eps*h_a^2/mu_g^2)', { kind: 'derived', origin: 'Geometry of the conic' }),
      eq('k3', 'Kepler\'s third law', 'T_K', '2*pi*sqrt(a_sm^3/mu_g)', { kind: 'law', origin: 'Kepler\'s third law' }),
      ...(pre.length ? [eq('prec', 'Apsidal advance per orbit', 'dw', pre.join(' + '), { kind: 'derived', origin: 'First-order perturbation theory' })] : []),
    ];
  },
  derivation: a => [
    { text: a.fixed_centre ? 'A test body at position r from a fixed centre feels the inverse-square attraction.' : 'For two attracting bodies the separation vector obeys the same equation as a test body about a fixed centre of the combined mass.', tex: `\\ddot{\\mathbf r} = -\\frac{\\mu\\,\\mathbf r}{r^3},\\qquad \\mu = ${a.fixed_centre ? 'GM' : 'G(M+m)'}` },
    { text: 'The force is central, so the angular momentum per unit mass is constant (Kepler\'s second law); it is conservative, so the energy per unit mass is constant.', tex: 'h = x\\dot y - y\\dot x,\\qquad \\varepsilon = \\tfrac12 v^2 - \\frac{\\mu}{r}' },
    { text: 'Solving the radial equation gives a conic with the centre at one focus. Its size and shape follow from the two constants.', tex: 'r = \\frac{h^2/\\mu}{1 + e\\cos\\theta},\\qquad a = -\\frac{\\mu}{2\\varepsilon},\\qquad e = \\sqrt{1 + \\frac{2\\varepsilon h^2}{\\mu^2}}' },
    { text: 'Dividing the area of the ellipse by the constant areal velocity h/2 gives the period.', tex: 'T = 2\\pi\\sqrt{a^3/\\mu}' },
    ...(a.newtonian && a.point_mass ? [] : [{ text: 'A small additional attraction varying as 1/r⁴ makes the radial and angular periods differ, so the ellipse turns slowly in its plane.', tex: `\\Delta\\varpi = ${[a.newtonian ? null : '\\frac{6\\pi\\mu}{c^2 a(1-e^2)}', a.point_mass ? null : '3\\pi J_2\\left(\\frac{R}{a(1-e^2)}\\right)^2'].filter(Boolean).join(' + ')}\\ \\text{per orbit}` }]),
    { text: a.symplectic ? 'The motion is advanced with a composition of three velocity-Verlet (kick–drift–kick) steps whose weights cancel the leading error term. Each sub-step is a canonical map, so the scheme conserves angular momentum exactly and the energy error stays bounded.' : 'The motion is advanced with the classical fourth-order Runge–Kutta scheme, which is accurate per step but lets the energy drift slowly.', tex: a.symplectic ? 'w_1 = \\frac{1}{2-2^{1/3}},\\quad w_0 = -\\frac{2^{1/3}}{2-2^{1/3}}' : '\\mathbf y_{n+1} = \\mathbf y_n + \\tfrac{h}{6}(k_1 + 2k_2 + 2k_3 + k_4)' },
  ],
  solve(v, a) {
    const k = keplerRun(v, a), q = a.fixed_centre ? 0 : v.q_m, warnings = [];
    const type = !k.bound ? 2 : k.ecc < 1e-3 ? 0 : 1, TYPES = ['Circular orbit', 'Elliptical orbit', 'Unbound (hyperbolic or parabolic) trajectory'];
    if (k.rp < 0.02 * k.r0) warnings.push('The periapsis is very close to the centre compared with the starting distance. A fixed time step resolves that passage poorly; raise the steps per period and treat conservation errors as the guide to accuracy.');
    if (!a.point_mass && k.rp < v.R_b) warnings.push('The periapsis lies inside the stated body radius: the trajectory intersects the central body.');
    if (!k.bound) warnings.push('The specific energy is not negative, so the body escapes; the period is undefined and the simulation covers the stated number of local circular periods.');
    if (!a.newtonian && k.mu / (k.rp * C.c ** 2) > 0.01) warnings.push('The orbit reaches a strong-field region where the first-order relativistic correction is inadequate.');
    const sub = every(k.m, 600), idx = k.run.t.map((_, i) => i).filter(i => i % sub === 0 || i === k.m - 1);
    const [tu, tun] = k.tEnd > 3 * 3.15576e7 ? [3.15576e7, 'yr'] : k.tEnd > 3 * 86400 ? [86400, 'd'] : k.tEnd > 3 * 3600 ? [3600, 'h'] : [1, 's'];
    const tt = idx.map(i => k.run.t[i] / tu), X = idx.map(i => k.run.q[i][0]), Y = idx.map(i => k.run.q[i][1]);
    const fs = every(k.m, 240), fi = k.run.t.map((_, i) => i).filter(i => i % fs === 0);
    const f1 = -q / (1 + q), f2 = 1 / (1 + q), lim = 1.1 * N.maxOf(idx.map(i => k.r[i]));
    return {
      scalars: [
        scalar('type', 'Orbit type', type, '1', { text: TYPES[type] }),
        scalar('eps', 'Specific orbital energy', k.eps, 'J/kg'), scalar('h_a', 'Specific angular momentum', k.hA, 'm^2/s'),
        scalar('a_sm', 'Semi-major axis', k.sma, 'm', { show: 'AU' }), scalar('ecc', 'Eccentricity', k.ecc, '1'),
        scalar('r_p', 'Periapsis distance', k.rp, 'm', { show: 'AU' }), scalar('r_a', 'Apoapsis distance', k.bound ? k.ra : NaN, 'm', { show: 'AU', text: k.bound ? undefined : 'None: the trajectory is unbound' }),
        scalar('T_K', 'Period from Kepler\'s third law', k.T, 's', { show: 'd', text: k.bound ? undefined : 'Undefined: the trajectory is unbound' }),
        scalar('T_num', 'Period measured from the simulation', k.Tnum, 's', { show: 'd', text: Number.isFinite(k.Tnum) ? undefined : 'A full revolution was not completed' }),
        scalar('v_c', 'Circular speed at the starting distance', Math.sqrt(k.mu / k.r0), 'm/s', { show: 'km/s' }), scalar('v_esc', 'Escape speed at the starting distance', Math.sqrt(2 * k.mu / k.r0), 'm/s', { show: 'km/s' }),
        scalar('v_p', 'Speed at periapsis', k.hA !== 0 ? Math.abs(k.hA) / k.rp : NaN, 'm/s', { show: 'km/s', text: k.hA !== 0 ? undefined : 'Radial trajectory' }),
        scalar('dE', 'Largest relative energy error', N.maxOf(k.dE.map(Math.abs)), '1'), scalar('dh', 'Largest relative angular-momentum error', N.maxOf(k.dH.map(Math.abs)), '1'),
        scalar('dw', 'Apsidal advance per orbit (perturbation theory)', k.bound ? k.advTh : NaN, 'rad', { text: !k.bound ? 'Undefined: the trajectory is unbound' : a.newtonian && a.point_mass ? 'Zero: no perturbation is active' : undefined }),
        scalar('dw_num', 'Apsidal advance per orbit (measured)', k.adv, 'rad', { text: Number.isFinite(k.adv) ? undefined : 'Needs an eccentric orbit and at least two periapsis passages' }),
      ],
      series: [
        line('radius', 'Separation against time', 'Time', tun, tt, [{ label: 'Separation', data: idx.map(i => k.r[i] / AU) }], 'Separation', 'AU'),
        line('speed', 'Speed against time', 'Time', tun, tt, [{ label: 'Speed', data: idx.map(i => k.sp[i] / 1000) }], 'Speed', 'km/s'),
        line('conservation', 'Conservation errors', 'Time', tun, tt, [{ label: 'Relative energy error', data: idx.map(i => k.dE[i]) }, { label: 'Relative angular-momentum error', data: idx.map(i => k.dH[i]) }], 'Relative error', '–'),
      ],
      anims: [motion('orbit', 'Orbital motion', fi.map(i => [[f1 * k.run.q[i][0], f1 * k.run.q[i][1]], [f2 * k.run.q[i][0], f2 * k.run.q[i][1]]]), fi.map(i => k.run.t[i]), { trails: true, labels: ['Central body', 'Orbiting body'], bounds: [-lim, lim, -lim, lim], unit: 'm' })],
      paths: [path3d('trajectory', 'Trajectory', [{ label: 'Orbit', x: X, y: Y, z: X.map(() => 0) }, { label: 'Centre', x: [0], y: [0], z: [0] }], { equal: true, unit: 'm' })],
      checks: [
        check('Energy conservation', N.maxOf(k.dE.map(Math.abs)), 1e-8, 'Largest relative change of the specific energy, including perturbation potentials'),
        check('Angular-momentum conservation', N.maxOf(k.dH.map(Math.abs)), 1e-10, 'Largest relative change of x·v_y − y·v_x'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const on = { fixed_centre: true, newtonian: true, point_mass: true, symplectic: true };
    const circ = keplerRun({ ...v, GM: R.BODIES.sun.GM, r_0: AU, v_0: Math.sqrt(R.BODIES.sun.GM / AU), phi: 0, n_orb: 1.5 }, on);
    const ell = keplerRun({ ...v, GM: R.BODIES.sun.GM, r_0: AU, v_0: 0.8 * Math.sqrt(R.BODIES.sun.GM / AU), phi: 0, n_orb: 1.5, n_step: 4000 }, on);
    return [
      bench('Measured period of a circular orbit at 1 AU vs Kepler\'s third law', circ.Tnum, 2 * Math.PI * Math.sqrt(AU ** 3 / R.BODIES.sun.GM), 'T = 2π√(a³/GM)', 1e-9),
      bench('Measured period of an eccentric orbit vs Kepler\'s third law', ell.Tnum, ell.T, 'T = 2π√(a³/GM)', 1e-7),
      bench('Smallest simulated distance vs analytic periapsis', N.minOf(ell.r), ell.rp, 'r_p = a(1 − e)', 1e-6),
      bench('Gaussian year from the solar gravitational parameter', 2 * Math.PI * Math.sqrt(AU ** 3 / R.BODIES.sun.GM) / 86400, 365.2568983, 'Gaussian year, 365.2568983 d (IAU 1976 system of constants)', 1e-8),
    ];
  },
  validation: [
    { name: 'Sidereal year of the Earth', ref: 'IERS Conventions (2010); Astronomical Almanac: sidereal year 365.25636 d', note: 'Kepler period for a = 1 AU about the Sun alone. The small excess reflects the neglected mass of the Earth–Moon system.',
      cases: [{ label: 'a = 1 AU', inputs: { GM: R.BODIES.sun.GM, r_0: AU, v_0: Math.sqrt(R.BODIES.sun.GM / AU), phi: 0 }, observable: 'T_K', observed: 365.25636 * 86400, sigma: 0.002 * 86400 }] },
    { name: 'Anomalous perihelion advance of Mercury', ref: 'Clemence, G. M. (1947). Rev. Mod. Phys. 19, 361: 43.11 ± 0.45 arcsec per century', note: 'Relativistic term only; switch off the Newtonian assumption to reproduce. Converted to radians per orbit with a period of 87.969 d.',
      cases: [{ label: 'a = 0.3871 AU, e = 0.2056', inputs: { GM: R.BODIES.sun.GM, r_0: R.BODIES.mercury.a * (1 - R.BODIES.mercury.ecc), v_0: Math.sqrt(R.BODIES.sun.GM * (1 + R.BODIES.mercury.ecc) / (R.BODIES.mercury.a * (1 - R.BODIES.mercury.ecc))), phi: 0 }, assumptions: { newtonian: false }, observable: 'dw', observed: 43.11 * (87.969 / 36525) * DEG / 3600, sigma: 0.45 * (87.969 / 36525) * DEG / 3600 }] },
  ],
  diagram(v, a) {
    const k = keplerRun({ ...v, n_orb: 1, n_step: 200 }, { ...a, symplectic: true }), ext = N.maxOf(k.r) || 1, sc = 135 / ext, cx = 320, cy = 185;
    const st = every(k.m, 160), pts = k.run.q.filter((_, i) => i % st === 0).map(p => [(cx + p[0] * sc).toFixed(1), (cy - p[1] * sc).toFixed(1)]);
    const ang = v.phi, ax = cx + k.r0 * sc;
    return svg(`
      ${S.poly(pts, 'd-line')} ${S.circle(cx, cy, 8, 'd-body d-heat')} ${S.text(cx, cy + 26, 'central body', 'd-text d-small')}
      ${S.circle(ax, cy, 5, 'd-body')} ${S.arrow(ax, cy, ax + 60 * Math.sin(ang), cy - 60 * Math.cos(ang))}
      ${S.text(ax + 12, cy + 20, `v₀ = ${lab(v.v_0 / 1000, 'km/s')}`, 'd-text', 'start')}
      ${S.dim(cx, cy + 46, ax, cy + 46, `r₀ = ${lab(v.r_0 / AU, 'AU')}`)}
      ${S.text(40, 36, `e = ${lab(k.ecc)}    a = ${lab(k.sma / AU, 'AU')}`, 'd-text', 'start')}
      ${S.text(600, 36, k.bound ? `period ${lab(k.T / 86400, 'd')}` : 'unbound', 'd-text', 'end')}
      ${S.text(320, 345, 'energy ε = v²/2 − μ/r and angular momentum h = r × v are conserved', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Test Kepler\'s third law and the conservation of angular momentum using tracked positions of a satellite or planet over several revolutions.',
    apparatus: ['Published ephemerides or tracking data for bodies spanning a range of semi-major axes about one primary', 'Telescope with astrometric camera, or satellite laser-ranging data', 'Timing reference traceable to UTC'],
    instruments: [{ name: 'Astrometric CCD camera', measures: 'Angular position against reference stars', range: '—', resolution: '0.1 arcsec' }, { name: 'Laser or radar ranging', measures: 'Distance', range: 'to planetary distances', resolution: 'centimetres to metres' }, { name: 'GNSS-disciplined clock', measures: 'Epoch of each observation', range: '—', resolution: '1 µs' }],
    procedure: ['Collect positions over at least two revolutions for each body.', 'Fit an ellipse and determine the semi-major axis, eccentricity and period.', 'Plot log T against log a for all bodies; the slope should be 3/2 and the intercept gives GM.', 'Compute the swept area per unit time around the orbit.'],
    controls: ['Use bodies with widely different eccentricities to show the period depends on a alone', 'Remove known perturbations (other planets, J₂) before testing closure of the ellipse'],
    signatures: ['T² proportional to a³ with a single constant for all bodies about one primary', 'Equal areas swept in equal times', 'A residual apsidal advance of 43 arcsec per century for Mercury'],
    safety: ['Never point optics at or near the Sun without certified solar filtration', 'Observe laser-ranging aircraft-avoidance procedures'],
  },
  falsify: ['A period depending on eccentricity at fixed semi-major axis.', 'Areal velocity varying around an unperturbed orbit.', 'A bound unperturbed orbit that fails to close.'],
  alternatives: [{ name: 'Analytic Kepler propagation', text: 'Solving Kepler\'s equation for the eccentric anomaly gives the position at any time without stepping.' }, { name: 'Regularised integration', text: 'Kustaanheimo–Stiefel or time-transformed leapfrog schemes handle close approaches that defeat a fixed time step.' }, { name: 'Full post-Newtonian or geodesic equations', text: 'Needed for compact binaries and orbits near black holes, where the first-order correction fails.' }],
  hazards: [{ hazard: 'Misleading long-term predictions', cause: 'Step too coarse for an eccentric orbit', mitigation: 'Monitor the conservation errors and refine the step until results converge' }],
  standards: ['IAU 2015 Resolution B3 (nominal solar and planetary conversion constants)', 'IERS Conventions (2010)', 'CCSDS 502.0-B (orbit data messages)'],
  limits: 'Planar motion about a single centre. Perturbations are limited to an equatorial J₂ term and the first-order relativistic correction. A fixed time step is used, refined automatically for eccentric orbits but unsuitable for near-collision trajectories. Radiation pressure, drag and third bodies are not included.',
  numerics: { method: 'Fourth-order symplectic Yoshida composition of velocity-Verlet steps (or classical RK4 for comparison)', order: 4, stability: 'Bounded energy error for steps well below the periapsis passage time', resolution: 'n_step' },
  optimise: { objective: 'ecc', sense: 'min', vars: ['v_0'], note: 'The eccentricity vanishes at the circular speed.' },
  inverse: { series: 'radius', fit: ['GM', 'v_0'] },
  extensions: ['Kepler-equation propagation and orbital elements in three dimensions', 'Third-body perturbations and resonances', 'Regularised integration for near-parabolic encounters'],
};

// ------------------------------------------------------------------ 7. planar three-body problem
const FIG8_T = 6.32591398;   // period of the figure-eight choreography in units of √(L³/(G m))
function threeIC(a, v) {
  const m3 = a.equal ? 1 : v.mu_3, m = [1, 1, m3], M = 2 + m3;
  let q, u;
  if (a.figure8) {
    q = [0.97000436, -0.24308753, -0.97000436, 0.24308753, 0, 0];
    u = [0.466203685, 0.43236573, 0.466203685, 0.43236573, -0.93240737, -0.86473146];
  } else {
    q = [90, 210, 330].flatMap(d => [Math.cos(d * DEG), Math.sin(d * DEG)]);
    const om = Math.sqrt(M / Math.pow(3, 1.5)), cx = (q[0] + q[2] + m3 * q[4]) / M, cy = (q[1] + q[3] + m3 * q[5]) / M;
    u = [0, 1, 2].flatMap(i => [-om * (q[2 * i + 1] - cy), om * (q[2 * i] - cx)]);
  }
  for (const arr of [q, u]) for (let k = 0; k < 2; k++) { const c = (arr[k] + arr[2 + k] + m3 * arr[4 + k]) / M; for (let i = 0; i < 3; i++) arr[2 * i + k] -= c; }
  return { m, q, u, omega: Math.sqrt(M / Math.pow(3, 1.5)) };
}
/** Accelerations of three bodies whose coordinates start at q[qo]; written to a[ao…ao+5]. */
const threeAcc = (m, e2) => (q, a, qo = 0, ao = 0) => {
  for (let i = 0; i < 6; i++) a[ao + i] = 0;
  for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) {
    const dx = q[qo + 2 * j] - q[qo + 2 * i], dy = q[qo + 2 * j + 1] - q[qo + 2 * i + 1], r2 = dx * dx + dy * dy + e2, inv = 1 / (r2 * Math.sqrt(r2));
    a[ao + 2 * i] += m[j] * dx * inv; a[ao + 2 * i + 1] += m[j] * dy * inv; a[ao + 2 * j] -= m[i] * dx * inv; a[ao + 2 * j + 1] -= m[i] * dy * inv;
  }
};
function threeInv(m, q, u, e2) {
  let E = 0, Lz = 0, px = 0, py = 0, rmin = Infinity; const d = [];
  for (let i = 0; i < 3; i++) { E += 0.5 * m[i] * (u[2 * i] ** 2 + u[2 * i + 1] ** 2); Lz += m[i] * (q[2 * i] * u[2 * i + 1] - q[2 * i + 1] * u[2 * i]); px += m[i] * u[2 * i]; py += m[i] * u[2 * i + 1]; }
  for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) { const r = Math.hypot(q[2 * j] - q[2 * i], q[2 * j + 1] - q[2 * i + 1]); d.push(r); rmin = Math.min(rmin, r); E -= m[i] * m[j] / Math.sqrt(r * r + e2); }
  return { E, Lz, px, py, rmin, d };
}
/** Integrate the reference system and a perturbed twin in units G = m = L = 1. Returns rows of [q(6), u(6)]. */
function threeRun(a, v, tEnd, nOut) {
  const ic = threeIC(a, v), e2 = a.point ? 0 : v.eps_s ** 2, acc = threeAcc(ic.m, e2), q2 = ic.q.slice(); q2[0] += v.delta;
  let t, A, B, truncated = false;
  if (a.adaptive) {
    // state layout: reference [q(6), u(6)] then twin [q(6), u(6)]
    const f = (tt, y, d) => { for (let o = 0; o < 24; o += 12) { for (let i = 0; i < 6; i++) d[o + i] = y[o + 6 + i]; acc(y, d, o, o + 6); } };
    const s = dopri(f, [...ic.q, ...ic.u, ...q2, ...ic.u], tEnd, nOut, { rtol: 1e-9, atol: 1e-12, maxSteps: 25000 });
    t = s.t; truncated = !s.complete;
    A = s.y.map(r => [r.subarray(0, 6), r.subarray(6, 12)]); B = s.y.map(r => [r.subarray(12, 18), r.subarray(18, 24)]);
  } else {
    const n = Math.max(50, Math.round(tEnd / FIG8_T * v.n_step)), st = every(n, nOut), ra = yoshida4(acc, ic.q, ic.u, tEnd / n, n, st), rb = yoshida4(acc, q2, ic.u, tEnd / n, n, st);
    t = ra.t; A = t.map((_, k) => [ra.q[k], ra.v[k]]); B = t.map((_, k) => [rb.q[k], rb.v[k]]);
  }
  return { ic, e2, t, A, B, truncated };
}
const threeBody = {
  id: 'three-body-chaos',
  title: 'Planar three-body problem and sensitivity to initial conditions',
  module: [1, 2], klass: 'I', domains: ['classical', 'space'], heavy: true,
  keywords: ['three-body problem', 'three body problem', 'figure-eight orbit', 'figure eight', 'chenciner', 'three-body', 'three body', 'n-body', 'lyapunov exponent', 'chaos', 'chaotic', 'sensitivity to initial conditions', 'lagrange points', 'choreography', 'butterfly effect', 'gravitational dynamics'],
  summary: 'Three gravitating bodies in a plane, started on the Chenciner–Montgomery figure-eight choreography or the Lagrange equilateral solution, with conservation checks and the divergence of a perturbed twin trajectory.',
  background: [
    'Unlike the two-body problem, three bodies under mutual gravity have no general closed-form solution: only ten classical integrals exist (energy, linear and angular momentum, centre-of-mass motion), too few to make the system integrable. Poincaré showed that the generic motion is chaotic — neighbouring trajectories separate exponentially.',
    'A few special periodic solutions are known. Lagrange\'s equilateral triangle rotates rigidly but is unstable unless one mass dominates. In 1993 Moore found numerically, and in 2000 Chenciner and Montgomery proved, the existence of a stable orbit in which three equal masses chase each other around a single figure-eight curve.',
  ],
  phenomena: ['Mutual Newtonian gravitation', 'Deterministic chaos', 'Exponential divergence of nearby trajectories', 'Periodic choreographies', 'Close encounters and ejection'],
  laws: ['gravitation', 'newton2', 'newton3', 'energy', 'momentum', 'angular'],
  refs: ['Poincaré, H. (1890). Sur le problème des trois corps et les équations de la dynamique. Acta Mathematica 13, 1–270.', 'Moore, C. (1993). Braids in classical dynamics. Physical Review Letters 70, 3675–3679.', 'Chenciner, A. & Montgomery, R. (2000). A remarkable periodic solution of the three-body problem in the case of equal masses. Annals of Mathematics 152, 881–901.', 'Simó, C. (2002). Dynamical properties of the figure eight solution of the three-body problem. Contemporary Mathematics 292, 209–228.', 'Szebehely, V. (1967). Theory of Orbits: The Restricted Problem of Three Bodies. Academic Press.'],
  inputs: [
    inp('m', 'Mass of each body', 'Msun', 1, { min: 1e-6, max: 100, aliases: ['mass', 'body mass', 'stellar mass'] }),
    inp('L', 'Length scale of the configuration', 'AU', 1, { min: 0.001, max: 1000, kind: 'geometry', aliases: ['length scale', 'separation', 'size', 'distance'] }),
    inp('n_T', 'Simulated time in figure-eight periods', '1', 5, { min: 0.5, max: 12, aliases: ['periods', 'duration'] }),
    inp('delta', 'Initial displacement of the twin (fraction of the length scale)', '1', 1e-9, { min: 1e-12, max: 1e-3, aliases: ['perturbation', 'initial separation'] }),
    inp('mu_3', 'Mass of the third body relative to the others (when unequal)', '1', 1.2, { min: 0.1, max: 10, aliases: ['mass ratio', 'third mass'] }),
    inp('eps_s', 'Softening length (fraction of the length scale, when softened)', '1', 0.05, { min: 0.001, max: 0.5, kind: 'numerical' }),
    inp('n_step', 'Fixed steps per figure-eight period (symplectic option)', '1', 3000, { min: 500, max: 20000, kind: 'numerical' }),
  ],
  assumptions: [
    asm('figure8', 'The bodies start on the Chenciner–Montgomery figure-eight choreography.', { why: 'A stable periodic solution for equal masses', alt: 'They start on the Lagrange equilateral triangle in rigid rotation, which is unstable for comparable masses.' }),
    asm('equal', 'All three masses are equal.', { why: 'Required by the figure-eight solution', alt: 'The third body has the stated relative mass; the motion is then generically chaotic.' }),
    asm('point', 'The bodies are point masses with exact inverse-square attraction.', { why: 'Physical law', alt: 'Plummer softening removes the singularity at zero separation.' }),
    asm('adaptive', 'Integration uses an adaptive fifth-order Runge–Kutta scheme with tight tolerance.', { why: 'Handles close encounters', alt: 'Fixed-step fourth-order symplectic integration.' }),
  ],
  symbols: { x_1: ['Position of body 1 (each Cartesian component)', 'm'], x_2: ['Position of body 2', 'm'], x_3: ['Position of body 3', 'm'], v_1: ['Speed of body 1', 'm/s'], v_2: ['Speed of body 2', 'm/s'], v_3: ['Speed of body 3', 'm/s'], r_12: ['Separation of bodies 1 and 2', 'm'], r_13: ['Separation of bodies 1 and 3', 'm'], r_23: ['Separation of bodies 2 and 3', 'm'], m_3: ['Mass of body 3', 'kg'], t: ['Time', 's'], E: ['Total energy', 'J'], tau: ['Dynamical time unit', 's'], eps_L: ['Softening length', 'm'], delta_s: ['Phase-space separation of the twin trajectories (scaled)', '1'], lambda: ['Finite-time Lyapunov exponent', '1/s'], T_8: ['Figure-eight period', 's'] },
  equations: a => {
    const m3 = a.equal ? 'm' : 'm_3', den = p => (a.point ? `r_${p}^3` : `(r_${p}^2 + eps_L^2)^1.5`), pot = p => (a.point ? `r_${p}` : `sqrt(r_${p}^2 + eps_L^2)`);
    return [
      eq('b1', 'Body 1', 'd2(x_1,t)', `G*m*(x_2 - x_1)/${den('12')} + G*${m3}*(x_3 - x_1)/${den('13')}`, { kind: 'law', origin: 'Newton\'s second law with universal gravitation', note: 'Holds for each Cartesian component.' }),
      eq('b2', 'Body 2', 'd2(x_2,t)', `G*m*(x_1 - x_2)/${den('12')} + G*${m3}*(x_3 - x_2)/${den('23')}`, { kind: 'law', origin: 'Newton\'s second law with universal gravitation' }),
      eq('b3', 'Body 3', 'd2(x_3,t)', `G*m*(x_1 - x_3)/${den('13')} + G*m*(x_2 - x_3)/${den('23')}`, { kind: 'law', origin: 'Newton\'s second law with universal gravitation' }),
      ...(a.equal ? [] : [eq('m3', 'Third mass', 'm_3', 'mu_3*m', { kind: 'definition' })]),
      ...(a.point ? [] : [eq('soft', 'Softening length', 'eps_L', 'eps_s*L', { kind: 'definition' })]),
      eq('en', 'Total energy', 'E', `0.5*m*v_1^2 + 0.5*m*v_2^2 + 0.5*${m3}*v_3^2 - G*m*m/${pot('12')} - G*m*${m3}/${pot('13')} - G*m*${m3}/${pot('23')}`, { kind: 'law', origin: 'Conservation of energy' }),
      eq('tau', 'Dynamical time unit', 'tau', 'sqrt(L^3/(G*m))', { kind: 'definition', origin: 'Dimensional analysis of the equations of motion' }),
      ...(a.figure8 && a.equal ? [eq('t8', 'Figure-eight period', 'T_8', '6.32591398*tau', { kind: 'derived', origin: 'Numerical value from Simó (2002)', needs: ['figure8', 'equal'] })] : []),
      eq('lyap', 'Growth of the twin separation', 'd(delta_s,t)', 'lambda*delta_s', { kind: 'definition', origin: 'Definition of the (finite-time) Lyapunov exponent' }),
    ];
  },
  derivation: a => [
    { text: 'Each body is accelerated by the gravitational pull of the other two. Third-law pairs make the total momentum constant.', tex: `m_i\\,\\ddot{\\mathbf r}_i = \\sum_{j\\ne i}\\frac{G\\,m_i m_j(\\mathbf r_j-\\mathbf r_i)}{${a.point ? '|\\mathbf r_j-\\mathbf r_i|^3' : '(|\\mathbf r_j-\\mathbf r_i|^2+\\epsilon^2)^{3/2}'}}` },
    { text: 'Measuring lengths in L, masses in m and times in τ removes every parameter from the equal-mass equations: all such systems are copies of one another.', tex: '\\tau = \\sqrt{L^3/(G m)}' },
    { text: 'The forces derive from a potential and depend only on separations, so energy, linear momentum and angular momentum are conserved. They are monitored as a test of the integration.', tex: 'E = \\sum_i \\tfrac12 m_i v_i^2 - \\sum_{i<j}\\frac{G m_i m_j}{r_{ij}},\\qquad \\mathbf P = \\sum_i m_i\\mathbf v_i,\\qquad L_z = \\sum_i m_i(x_i\\dot y_i - y_i\\dot x_i)' },
    { text: a.figure8 ? 'In the figure-eight solution the three bodies follow one closed curve, each a third of a period behind the next, with zero total angular momentum.' : 'In the Lagrange solution the bodies sit at the corners of an equilateral triangle of side s that rotates rigidly about the centre of mass.', tex: a.figure8 ? '\\mathbf r_i(t) = \\mathbf q\\!\\left(t + \\tfrac{i}{3}T\\right),\\qquad T = 6.3259\\,\\tau' : '\\omega^2 = \\frac{G(m_1+m_2+m_3)}{s^3}' },
    { text: 'A twin system is started a small distance δ₀ away in phase space. In chaotic motion the separation grows exponentially on average; the growth rate is the largest Lyapunov exponent. In regular motion it grows only as a power of time.', tex: '\\delta(t) \\simeq \\delta_0\\,e^{\\lambda t}' },
  ],
  solve(v, a) {
    const tau = Math.sqrt(v.L ** 3 / (C.G * v.m)), tEnd = v.n_T * FIG8_T, r = threeRun(a, v, tEnd, 401), n = r.t.length, m = r.ic.m;
    const inv = r.A.map(s => threeInv(m, s[0], s[1], r.e2)), i0 = inv[0], Es = Math.abs(i0.E), Ls = N.sum(m);
    const dE = inv.map(x => (x.E - i0.E) / Es), dL = inv.map(x => (x.Lz - i0.Lz) / Ls), dP = inv.map(x => Math.hypot(x.px - i0.px, x.py - i0.py) / Ls);
    const sep = r.A.map((s, k) => { let d = 0; for (let j = 0; j < 6; j++) d += (s[0][j] - r.B[k][0][j]) ** 2 + (s[1][j] - r.B[k][1][j]) ** 2; return Math.sqrt(d); });
    const gr = growthFit(r.t, sep), lam = gr.lam, noExp = 'Not exponential: the separation grows as a power of time';
    const rmin = N.minOf(inv.map(x => x.rmin)), growth = sep[n - 1] / sep[0];
    const dist = (p, q) => { let d = 0; for (let j = 0; j < p.length; j++) d += (p[j] - q[j]) ** 2; return Math.sqrt(d); };
    const one = a.figure8 && a.equal ? threeRun(a, v, FIG8_T, 2).A : null, ret = one && one.length > 1 ? dist(one[one.length - 1][0], one[0][0]) : NaN;
    const warnings = [];
    if (r.truncated) warnings.push('The adaptive integrator reached its step limit during a close encounter; the results cover only part of the requested time.');
    if (rmin < 0.01 && a.point) warnings.push('A very close encounter occurs. Point-mass results after such an encounter are extremely sensitive to rounding; consider softening.');
    if (a.figure8 && !a.equal) warnings.push('The figure-eight initial conditions are a periodic solution only for equal masses; with a different third mass they simply provide a starting point for chaotic motion.');
    if (N.maxOf(sep) > 0.5) warnings.push('The twin trajectories have separated to the size of the system: beyond that time the individual positions are not predictable.');
    let ext = 0; r.A.forEach(s => s[0].forEach(x => { ext = Math.max(ext, Math.abs(x)); }));
    const tp = r.t.map(t => t / FIG8_T), lim = 1.15 * ext * v.L;
    const fs = every(n, 300), fi = r.t.map((_, k) => k).filter(k => k % fs === 0);
    return {
      scalars: [
        scalar('tau', 'Dynamical time unit', tau, 's', { show: 'd' }), scalar('T_8', 'Figure-eight period', FIG8_T * tau, 's', { show: 'd' }), scalar('t_end', 'Simulated time', r.t[n - 1] * tau, 's', { show: 'd' }),
        scalar('E', 'Total energy', i0.E * C.G * v.m ** 2 / v.L, 'J'), scalar('L_z', 'Total angular momentum', i0.Lz * v.m * v.L ** 2 / tau, 'kg m^2/s'),
        scalar('dE', 'Largest relative energy error', N.maxOf(dE.map(Math.abs)), '1'), scalar('dL', 'Largest angular-momentum error (scaled)', N.maxOf(dL.map(Math.abs)), '1'), scalar('dP', 'Largest linear-momentum error (scaled)', N.maxOf(dP), '1'),
        scalar('r_min', 'Closest approach of any pair', rmin * v.L, 'm', { show: 'AU' }),
        scalar('law', 'Character of the divergence', gr.chaotic ? 1 : 0, '1', { text: GROWTH[gr.chaotic ? 1 : 0] }),
        scalar('lambda', 'Finite-time Lyapunov exponent (slope of ln separation against time)', lam / tau, '1/s', { show: '1/yr', note: gr.chaotic ? undefined : 'the growth is not exponential, so this slope is not a true exponent' }),
        scalar('t_e', 'E-folding time of the twin separation', gr.chaotic ? tau / lam : NaN, 's', { show: 'd', text: gr.chaotic ? undefined : noExp }),
        scalar('t_e8', 'E-folding time in figure-eight periods', gr.chaotic ? 1 / (lam * FIG8_T) : NaN, '1', { text: gr.chaotic ? undefined : noExp }),
        scalar('p_g', 'Power-law exponent of the separation growth', gr.power, '1'),
        scalar('growth', 'Growth factor of the twin separation', growth, '1'),
        scalar('ret', 'Distance from the starting configuration after one period (scaled)', ret, '1', { text: Number.isFinite(ret) ? undefined : 'Only defined for the equal-mass figure-eight' }),
      ],
      series: [
        line('separation', 'Divergence of the perturbed twin', 'Time', 'figure-eight periods', tp, [{ label: 'log₁₀ phase-space separation', data: sep.map(s => Math.log10(Math.max(s, 1e-300))) }, { label: 'Exponential fit', data: r.t.map(t => (Math.log(sep[0] || v.delta) + lam * t) / Math.LN10), dash: true }], 'log₁₀ separation', '–'),
        line('distances', 'Pair separations', 'Time', 'figure-eight periods', tp, [{ label: 'r₁₂ / L', data: inv.map(x => x.d[0]) }, { label: 'r₁₃ / L', data: inv.map(x => x.d[1]) }, { label: 'r₂₃ / L', data: inv.map(x => x.d[2]) }], 'Separation / L', '–'),
        line('conservation', 'Conservation errors', 'Time', 'figure-eight periods', tp, [{ label: 'Energy (relative)', data: dE }, { label: 'Angular momentum (scaled)', data: dL }, { label: 'Linear momentum (scaled)', data: dP }], 'Error', '–'),
      ],
      anims: [motion('bodies', 'Motion of the three bodies', fi.map(k => [0, 1, 2].map(i => [r.A[k][0][2 * i] * v.L, r.A[k][0][2 * i + 1] * v.L])), fi.map(k => r.t[k] * tau), { trails: true, labels: ['Body 1', 'Body 2', 'Body 3'], bounds: [-lim, lim, -lim, lim], unit: 'm' })],
      paths: [path3d('tracks', 'Trajectories', [0, 1, 2].map(i => ({ label: `Body ${i + 1}`, x: r.A.map(s => s[0][2 * i] * v.L), y: r.A.map(s => s[0][2 * i + 1] * v.L), z: r.A.map(() => 0) })), { equal: true, unit: 'm' })],
      checks: [
        check('Energy conservation', N.maxOf(dE.map(Math.abs)), 1e-7, 'Largest relative change of total energy'),
        check('Linear-momentum conservation', N.maxOf(dP), 1e-9, 'Change of total momentum in units of total mass × L/τ'),
        check('Angular-momentum conservation', N.maxOf(dL.map(Math.abs)), 1e-8, 'Change of L_z in units of total mass × L²/τ'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const base = { ...v, delta: 1e-9 };
    const f8 = threeRun({ figure8: true, equal: true, point: true, adaptive: true }, base, FIG8_T, 3), s = f8.A[f8.A.length - 1], q0 = f8.A[0];
    const gap = (p, q) => { let d = 0; for (let c = 0; c < 2; c++) for (let j = 0; j < 6; j++) d += (p[c][j] - q[c][j]) ** 2; return Math.sqrt(d); };
    const err = gap(s, q0);
    const om = threeIC({ figure8: false, equal: true }, base).omega;
    const lg = threeRun({ figure8: false, equal: true, point: true, adaptive: true }, base, 2 * Math.PI / om, 3), sl = lg.A[lg.A.length - 1];
    const errL = gap(sl, lg.A[0]);
    const i8 = threeInv([1, 1, 1], q0[0], q0[1], 0);
    const icL = threeIC({ figure8: false, equal: true }, base), aL = new Array(6).fill(0);
    threeAcc(icL.m, 0)(icL.q, aL);
    return [
      bench('Figure-eight orbit returns to its start after one period (1 = exact)', 1 + err, 1, 'Period 6.32591398 √(L³/Gm), Simó (2002)', 1e-6),
      bench('Lagrange triangle returns to its start after one rotation (1 = exact)', 1 + errL, 1, 'Rigid rotation with ω² = G·3m/s³', 1e-6),
      bench('Figure-eight total angular momentum (1 = exactly zero)', 1 + Math.abs(i8.Lz), 1, 'Chenciner & Montgomery (2000): zero angular momentum', 1e-7),
      bench('Lagrange solution: summed pairwise attraction on one body vs the centripetal requirement', Math.hypot(aL[0], aL[1]) / Math.hypot(icL.q[0], icL.q[1]), 1 / Math.sqrt(3), 'ω² = G·3m/s³ = Gm/(√3 R³) for side s = √3 R', 1e-12),
    ];
  },
  validation: [],
  diagram(v, a) {
    const ic = threeIC(a, v), sc = 120, cx = 320, cy = 185, P = i => [cx + ic.q[2 * i] * sc, cy - ic.q[2 * i + 1] * sc];
    const th = N.linspace(0, 2 * Math.PI, 80);
    const curve = a.figure8 ? S.poly(th.map(t => [(cx + 1.08 * sc * Math.sin(t)).toFixed(1), (cy - 0.36 * sc * Math.sin(2 * t)).toFixed(1)]), 'd-dim') : S.circle(cx, cy, sc, 'd-dim');
    return svg(`
      ${curve}
      ${[0, 1, 2].map(i => { const [x, y] = P(i); return S.circle(x, y, 7 + 2 * Math.cbrt(ic.m[i]), 'd-body') + S.arrow(x, y, x + ic.u[2 * i] * 60, y - ic.u[2 * i + 1] * 60) + S.text(x + 14, y + 24, `m${i + 1}`, 'd-text d-small', 'start'); }).join('')}
      ${S.line(P(0)[0], P(0)[1], P(1)[0], P(1)[1], 'd-dim')} ${S.line(P(1)[0], P(1)[1], P(2)[0], P(2)[1], 'd-dim')} ${S.line(P(0)[0], P(0)[1], P(2)[0], P(2)[1], 'd-dim')}
      ${S.text(320, 36, a.figure8 ? 'figure-eight choreography' : 'Lagrange equilateral configuration')}
      ${S.text(40, 340, `m = ${lab(v.m / 1.98847e30, 'M☉')}    L = ${lab(v.L / AU, 'AU')}    twin displaced by ${lab(v.delta)} L`, 'd-text d-small', 'start')}
    `);
  },
  experiment: {
    objective: 'Demonstrate sensitive dependence on initial conditions in a three-body system and measure the divergence rate, using a numerical experiment cross-checked with independent integrators.',
    apparatus: ['Two independent integration codes (for example an adaptive Runge–Kutta and a symplectic scheme)', 'Extended-precision arithmetic for the reference run', 'For an analogue demonstration: three magnetically or electrostatically interacting pucks on an air table with video tracking'],
    instruments: [{ name: 'Video tracking camera (analogue demonstration)', measures: 'Positions of the three bodies', range: '1 m field', resolution: '0.5 mm at 120 frames/s' }, { name: 'Conservation monitors (numerical)', measures: 'Energy, momentum, angular momentum', range: '—', resolution: 'relative 10⁻¹²' }],
    procedure: ['Integrate the reference initial condition and a twin displaced by a known small amount.', 'Record the phase-space separation against time and fit the exponential growth rate before saturation.', 'Repeat with the displacement and the tolerance each reduced tenfold; the growth rate should not change.', 'Repeat for the figure-eight (regular) and a nearby unequal-mass case (chaotic) and compare.'],
    controls: ['Time-reversal test: integrate forward then backward and compare with the start', 'Agreement of two different integrators up to the predictability horizon'],
    signatures: ['Straight line on a plot of log separation against time in the chaotic case', 'Power-law (not exponential) growth for the figure-eight orbit', 'Conserved quantities constant to the integration tolerance'],
    safety: ['No physical hazard for the numerical experiment', 'Air-table demonstration: strong magnets can pinch fingers and damage electronic devices'],
  },
  falsify: ['Total energy, momentum or angular momentum changing by more than the integration tolerance in an isolated system.', 'The figure-eight orbit failing to repeat after 6.3259 dynamical time units for equal masses.', 'A measured divergence rate that changes when the initial displacement is reduced (it would then be numerical, not dynamical).'],
  alternatives: [{ name: 'Restricted three-body problem', text: 'One body of negligible mass moving in the field of two in circular orbit: admits the Jacobi integral and the five Lagrange points.' }, { name: 'Regularised and symplectic N-body codes', text: 'Algorithmic regularisation and time-symmetric schemes follow close encounters and long evolutions more reliably.' }, { name: 'Statistical description', text: 'For chaotic triples the outcome (which body is ejected, the binary left behind) is best predicted as a probability distribution.' }],
  hazards: [{ hazard: 'Over-interpretation of a single trajectory', cause: 'Chaos amplifies rounding error beyond the predictability horizon', mitigation: 'Report ensembles and the e-folding time; trust individual trajectories only for a few e-folding times' }],
  standards: ['IEEE 754 (floating-point arithmetic)', 'IAU 2015 Resolution B3 (nominal solar and planetary conversion constants)'],
  limits: 'Planar Newtonian point masses (optionally softened). No collisions, tides, relativity or mass loss. Individual trajectories are meaningful only up to a few e-folding times of the divergence; the Lyapunov exponent reported is a finite-time estimate over the simulated interval.',
  numerics: { method: 'Adaptive Dormand–Prince RK45 at relative tolerance 10⁻⁹ on the reference and twin systems together (or fixed-step fourth-order Yoshida)', order: 5, stability: 'Step limit of 25 000 guards against collapse of the step at a close encounter', resolution: 'n_step' },
  optimise: { objective: 'lambda', sense: 'min', vars: ['mu_3'], note: 'With unequal masses switched on, the divergence rate is smallest near equal masses.' },
  inverse: { series: 'distances', fit: ['mu_3'] },
  extensions: ['Stability map of the figure-eight under mass and velocity perturbations', 'Restricted problem with Jacobi constant and Lagrange points', 'Hierarchical triples and the Kozai–Lidov mechanism in three dimensions'],
};

// ------------------------------------------------------------------ 8. projectile with drag and wind
const H_AIR = 8500, R_EARTH = 6.371e6;
function projRun(v, a, th = v.theta, nOut = 241, rtol = 1e-10) {
  const A = Math.PI * v.d ** 2 / 4, w = a.still_air ? 0 : v.w, kD = a.drag ? 0.5 * v.C_D * A / v.m : 0, kL = a.drag && !a.no_spin ? 0.5 * v.C_L * A / v.m : 0;
  const rhoOf = y => (a.const_rho ? v.rho : v.rho * Math.exp(-y / H_AIR)), gOf = y => (a.flat_g ? v.g : v.g * (R_EARTH / (R_EARTH + y)) ** 2);
  const f = (t, s) => {
    const rx = s[2] - w, uy = s[3], q = rhoOf(s[1]) * Math.hypot(rx, uy), ax = -q * (kD * rx + kL * uy), ay = -q * (kD * uy - kL * rx);
    return [s[2], uy, ax, ay - gOf(s[1]), v.m * (ax * s[2] + ay * uy)];    // last entry: power of the aerodynamic force
  };
  const u0 = [0, v.h_0, v.v_0 * Math.cos(th), v.v_0 * Math.sin(th), 0], tv = (u0[3] + Math.sqrt(u0[3] ** 2 + 2 * v.g * v.h_0)) / v.g;
  const s = toEvent(f, u0, 20 * tv + 100, y => y[1], y => y[3], nOut, { rtol, atol: 1e-9 });
  const pe = y => (a.flat_g ? v.g * y : v.g * R_EARTH * y / (R_EARTH + y));
  return { s, A, w, tv, u0, pe, yf: s.yHit, tf: s.tHit, landed: s.hit };
}
const projectile = {
  id: 'projectile-drag',
  title: 'Projectile motion with air resistance and wind',
  module: [1, 2], klass: 'I', domains: ['classical'],
  keywords: ['projectile motion', 'projectile', 'trajectory', 'air resistance', 'quadratic drag', 'range of a projectile', 'launch angle', 'ballistics', 'cannonball', 'thrown ball', 'terminal velocity', 'magnus effect', 'wind', 'parabola', 'maximum range'],
  summary: 'Flight of a projectile under gravity with quadratic air drag, optional wind, altitude-dependent density and spin lift, compared with the vacuum parabola.',
  background: [
    'Without air a projectile follows a parabola: horizontal velocity is constant, vertical velocity changes at the rate g, and on level ground the range is v² sin 2θ / g, greatest at 45°. This result, due to Galileo, is exact in a uniform field.',
    'In air the drag force grows roughly as the square of the speed relative to the air. It shortens the range, lowers the best launch angle below 45° and makes the descent steeper than the ascent. The importance of drag is measured by the ratio of launch speed to terminal velocity.',
  ],
  phenomena: ['Uniform gravitational acceleration', 'Quadratic aerodynamic drag', 'Advection by wind', 'Magnus lift on a spinning ball'],
  laws: ['newton2', 'momentum', 'energy'],
  refs: ['Galilei, G. (1638). Discorsi e dimostrazioni matematiche intorno a due nuove scienze. Elzevir, Leiden.', 'Thornton, S. T. & Marion, J. B. (2004). Classical Dynamics of Particles and Systems, 5th ed., Brooks/Cole.', 'Hoerner, S. F. (1965). Fluid-Dynamic Drag. Published by the author.', 'Adair, R. K. (2002). The Physics of Baseball, 3rd ed., HarperCollins.', 'de Mestre, N. (1990). The Mathematics of Projectiles in Sport. Cambridge University Press.'],
  inputs: [
    inp('v_0', 'Launch speed', 'm/s', 45, { min: 1, max: 1000, aliases: ['launch speed', 'initial speed', 'initial velocity', 'muzzle velocity', 'speed', 'velocity'] }),
    inp('theta', 'Launch angle above the horizontal', 'deg', 40, { min: 1, max: 89, aliases: ['launch angle', 'elevation', 'angle'] }),
    inp('h_0', 'Launch height above the landing level', 'm', 1, { min: 0, max: 1000, kind: 'geometry', aliases: ['launch height', 'height'] }),
    inp('m', 'Mass', 'kg', 0.145, { min: 0.001, max: 1000, aliases: ['mass'], src: 'Regulation baseball' }),
    inp('d', 'Diameter', 'm', 0.074, { min: 0.002, max: 2, kind: 'geometry', aliases: ['diameter'], src: 'Regulation baseball' }),
    inp('C_D', 'Drag coefficient', '1', 0.4, { min: 0.01, max: 2, kind: 'fluid', aliases: ['drag coefficient'], src: 'Sphere at sub-critical Reynolds number, about 0.4–0.5 (Hoerner 1965)' }),
    inp('C_L', 'Lift coefficient from backspin (when spinning)', '1', 0.2, { min: -0.5, max: 0.5, kind: 'fluid', aliases: ['lift coefficient', 'magnus'], src: 'Baseball with strong backspin (Adair 2002)' }),
    inp('rho', 'Air density at the launch level', 'kg/m^3', 1.225, { min: 0.01, max: 2, kind: 'environment', env: 'air_density', aliases: ['air density'] }),
    inp('w', 'Wind speed along the direction of fire (tailwind positive)', 'm/s', 5, { min: -40, max: 40, kind: 'environment', env: 'wind_speed', aliases: ['wind speed', 'wind', 'tailwind', 'headwind'] }),
    inp('g', 'Gravitational acceleration', 'm/s^2', 9.80665, { min: 1, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity', 'gravitational acceleration'] }),
  ],
  assumptions: [
    asm('drag', 'Air resistance acts, proportional to the square of the speed relative to the air.', { why: 'Reynolds number well above 1000', alt: 'No air resistance: the trajectory is the vacuum parabola.' }),
    asm('still_air', 'The air is still.', { why: 'Calm conditions', alt: 'A steady horizontal wind of the stated speed blows along the direction of fire.' }),
    asm('const_rho', 'Air density is uniform over the height of the trajectory.', { why: 'Apex well below the atmospheric scale height', alt: 'Density falls exponentially with height (scale height 8.5 km).' }),
    asm('flat_g', 'Gravity is uniform.', { why: 'Trajectory small against the planet radius', alt: 'Gravity weakens with height as the inverse square of distance from the Earth\'s centre.' }),
    asm('no_spin', 'The projectile does not spin: there is no aerodynamic lift.', { why: 'Simplest case', alt: 'Backspin produces a Magnus lift force perpendicular to the relative velocity with the stated lift coefficient.' }),
  ],
  symbols: { x: ['Horizontal position', 'm'], y: ['Height', 'm'], t: ['Time', 's'], v_x: ['Horizontal velocity', 'm/s'], v_y: ['Vertical velocity', 'm/s'], v_r: ['Speed relative to the air', 'm/s'], A: ['Frontal area', 'm^2'], R: ['Range', 'm'], v_t: ['Terminal velocity', 'm/s'], rho_h: ['Air density at height', 'kg/m^3'], g_y: ['Gravitational acceleration at height', 'm/s^2'], H_s: ['Atmospheric scale height, 8.5 km', 'm'], R_E: ['Earth radius', 'm'], u_w: ['Wind speed used', 'm/s'], t_f: ['Time of flight', 's'] },
  equations: a => {
    if (!a.drag) return [
      eq('x', 'Horizontal motion', 'x', 'v_0*cos(theta)*t', { kind: 'law', origin: 'Newton\'s first law: no horizontal force' }),
      a.flat_g ? eq('y', 'Vertical motion', 'y', 'h_0 + v_0*sin(theta)*t - g*t^2/2', { kind: 'law', origin: 'Newton\'s second law in a uniform field', needs: ['flat_g'] })
        : eq('y', 'Vertical motion', 'd2(y,t)', '-g*(R_E/(R_E + y))^2', { kind: 'law', origin: 'Newton\'s second law with inverse-square gravity' }),
      ...(a.flat_g ? [eq('tf', 'Time of flight', 't_f', '(v_0*sin(theta) + sqrt((v_0*sin(theta))^2 + 2*g*h_0))/g', { kind: 'derived', origin: 'Root of the vertical motion' }), eq('range', 'Range', 'R', 'v_0*cos(theta)*t_f', { kind: 'derived', origin: 'Reduces to v₀² sin 2θ / g for launch at the landing level' })] : []),
    ];
    const rho = a.const_rho ? 'rho' : 'rho_h', g = a.flat_g ? 'g' : 'g_y', rx = a.still_air ? 'v_x' : '(v_x - u_w)';
    return [
      eq('area', 'Frontal area', 'A', 'pi*d^2/4', { kind: 'definition' }),
      eq('vr', 'Speed relative to the air', 'v_r', `sqrt(${rx}^2 + v_y^2)`, { kind: 'definition' }),
      ...(a.still_air ? [] : [eq('wind', 'Wind', 'u_w', 'w', { kind: 'boundary', origin: 'Steady uniform wind' })]),
      eq('mx', 'Horizontal momentum', 'm*d(v_x,t)', `-0.5*${rho}*C_D*A*v_r*${rx}${a.no_spin ? '' : ` - 0.5*${rho}*C_L*A*v_r*v_y`}`, { kind: 'law', origin: 'Newton\'s second law with quadratic drag', needs: ['drag'] }),
      eq('my', 'Vertical momentum', 'm*d(v_y,t)', `-m*${g} - 0.5*${rho}*C_D*A*v_r*v_y${a.no_spin ? '' : ` + 0.5*${rho}*C_L*A*v_r*${rx}`}`, { kind: 'law', origin: 'Newton\'s second law with quadratic drag', needs: ['drag'] }),
      eq('kx', 'Kinematics, x', 'd(x,t)', 'v_x', { kind: 'definition' }), eq('ky', 'Kinematics, y', 'd(y,t)', 'v_y', { kind: 'definition' }),
      ...(a.const_rho ? [] : [eq('rho', 'Density with height', 'rho_h', 'rho*exp(-y/H_s)', { kind: 'closure', origin: 'Isothermal atmosphere' })]),
      ...(a.flat_g ? [] : [eq('grav', 'Gravity with height', 'g_y', 'g*(R_E/(R_E + y))^2', { kind: 'law', origin: 'Newton\'s law of gravitation' })]),
      eq('vt', 'Terminal velocity', 'v_t', 'sqrt(2*m*g/(rho*C_D*A))', { kind: 'derived', origin: 'Drag equals weight' }),
    ];
  },
  derivation: a => (a.drag ? [
    { text: 'The forces on the projectile are its weight and the aerodynamic force, which depends on the velocity relative to the air.', tex: 'm\\,\\dot{\\mathbf v} = m\\,\\mathbf g - \\tfrac12\\rho C_D A\\,|\\mathbf v_r|\\,\\mathbf v_r,\\qquad \\mathbf v_r = \\mathbf v - \\mathbf w' },
    { text: 'Resolving horizontally and vertically gives two coupled equations: because the drag depends on the total relative speed, the horizontal and vertical motions no longer separate.', tex: '\\dot v_x = -k\\,v_r\\,(v_x-w),\\qquad \\dot v_y = -g - k\\,v_r\\,v_y,\\qquad k = \\frac{\\rho C_D A}{2m}' },
    { text: 'Drag balances weight at the terminal velocity, which sets the scale of the problem: drag matters when the launch speed is comparable with it.', tex: 'v_t = \\sqrt{\\frac{2mg}{\\rho C_D A}}' },
    { text: 'There is no general closed-form solution, so the equations are integrated numerically until the projectile returns to the landing level. For a vertical launch the apex has the exact value used as a benchmark.', tex: 'y_{max} = \\frac{v_t^2}{2g}\\ln\\!\\left(1 + \\frac{v_0^2}{v_t^2}\\right)' },
  ] : [
    { text: 'With no air the only force is the weight, so the horizontal velocity is constant and the vertical velocity falls at the rate g.', tex: 'x = v_0\\cos\\theta\\;t,\\qquad y = h_0 + v_0\\sin\\theta\\;t - \\tfrac12 g t^2' },
    { text: 'Eliminating time gives a parabola.', tex: 'y = h_0 + x\\tan\\theta - \\frac{g\\,x^2}{2v_0^2\\cos^2\\theta}' },
    { text: 'Setting y = 0 gives the time of flight and the range; for launch at the landing level the range reduces to the classical result, greatest at 45°.', tex: 'R = \\frac{v_0^2\\sin 2\\theta}{g}\\quad (h_0 = 0)' },
  ]),
  solve(v, a) {
    const r = projRun(v, a), s = r.s, n = s.t.length, X = s.y[0], Y = s.y[1], sp = s.t.map((_, i) => Math.hypot(s.y[2][i], s.y[3][i]));
    const ia = Y.indexOf(N.maxOf(Y)), apex = vertex(Y, ia)[1], yf = r.yf;
    const Rvac = r.u0[2] * r.tv, vt = Math.sqrt(2 * v.m * v.g / (v.rho * v.C_D * r.A));
    const e0 = 0.5 * v.v_0 ** 2 + r.pe(v.h_0), ef = 0.5 * (yf[2] ** 2 + yf[3] ** 2) + r.pe(yf[1]);
    const angs = N.linspace(5, 85, 21), Rs = angs.map(d => projRun(v, a, d * DEG, 2, 1e-7).yf[0]);
    const ib = Rs.indexOf(N.maxOf(Rs)), ob = vertex(Rs, ib);
    const tv = N.linspace(0, r.tv, 121), warnings = [];
    if (!r.landed) warnings.push('The projectile had not returned to the landing level by the end of the simulated time.');
    if (a.drag && v.v_0 > 250) warnings.push('The launch speed is transonic or supersonic: the drag coefficient then varies strongly with Mach number and a constant value is a rough approximation.');
    if (a.drag && !a.no_spin && Math.abs(v.C_L) > 0.3) warnings.push('Lift coefficients this large require very high spin rates; the lift also decays as the spin does, which is not modelled.');
    return {
      scalars: [
        scalar('R', 'Range', yf[0], 'm'), scalar('t_f', 'Time of flight', r.tf, 's'), scalar('y_max', 'Maximum height', apex, 'm'),
        scalar('v_f', 'Impact speed', Math.hypot(yf[2], yf[3]), 'm/s'), scalar('theta_f', 'Impact angle below the horizontal', Math.atan2(-yf[3], yf[2]), 'rad', { show: 'deg' }),
        scalar('R_vac', 'Range without air (uniform gravity)', Rvac, 'm'), scalar('R_ratio', 'Range relative to the vacuum value', yf[0] / Rvac, '1'),
        scalar('v_t', 'Terminal velocity', vt, 'm/s'), scalar('v_ratio', 'Launch speed over terminal velocity', v.v_0 / vt, '1'),
        scalar('E_loss', 'Mechanical energy dissipated', v.m * (e0 - ef), 'J'), scalar('E_frac', 'Fraction of launch kinetic energy dissipated', (e0 - ef) / (0.5 * v.v_0 ** 2), '1'),
        scalar('theta_opt', 'Launch angle for greatest range', (angs[ib] + ob[0] * (angs[1] - angs[0])) * DEG, 'rad', { show: 'deg' }), scalar('R_opt', 'Greatest range', ob[1], 'm'),
      ],
      series: [
        line('trajectory', 'Trajectory', 'Horizontal distance', 'm', X, [{ label: a.drag ? 'With air resistance' : 'No air resistance', data: Y }], 'Height', 'm', { overlay: [{ label: 'Vacuum parabola', x: tv.map(t => r.u0[2] * t), y: tv.map(t => v.h_0 + r.u0[3] * t - 0.5 * v.g * t * t), dash: true }], equal: true }),
        line('speed', 'Speed during flight', 'Time', 's', s.t, [{ label: 'Speed', data: sp }, { label: 'Vertical velocity', data: s.y[3], dash: true }], 'Velocity', 'm/s'),
        line('range-angle', 'Range against launch angle', 'Launch angle', 'deg', angs, [{ label: 'Range', data: Rs }, { label: 'Vacuum, level ground', data: angs.map(d => v.v_0 ** 2 * Math.sin(2 * d * DEG) / v.g), dash: true }], 'Range', 'm'),
      ],
      anims: [motion('flight', 'Flight of the projectile', s.t.filter((_, i) => i % every(n, 160) === 0).map((_, k) => { const i = k * every(n, 160); return [[X[i], Y[i]]]; }), s.t.filter((_, i) => i % every(n, 160) === 0), { trails: true, labels: ['Projectile'], bounds: [Math.min(0, N.minOf(X)), Math.max(N.maxOf(X), 1), 0, Math.max(apex, 1)], unit: 'm' })],
      checks: [
        check('Energy balance', (ef - e0 - yf[4] / v.m) / e0, 1e-7, 'Change of mechanical energy against the work done by the aerodynamic force'),
        check('Landing level reached', r.landed ? yf[1] / Math.max(apex, 1) : 0, 1e-9, 'Height at the located landing point'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const off = { drag: false, still_air: true, const_rho: true, flat_g: true, no_spin: true }, on = { ...off, drag: true };
    const r0 = projRun(v, off), tv = (v.v_0 * Math.sin(v.theta) + Math.sqrt((v.v_0 * Math.sin(v.theta)) ** 2 + 2 * v.g * v.h_0)) / v.g;
    const r1 = projRun({ ...v, h_0: 0 }, off);
    const up = projRun({ ...v, h_0: 0 }, on, Math.PI / 2, 401), Y = up.s.y[1], vt2 = 2 * v.m * v.g / (v.rho * v.C_D * up.A);
    const tUp = Math.sqrt(vt2) / v.g * Math.atan(v.v_0 / Math.sqrt(vt2)), tDown = Math.sqrt(vt2) / v.g * Math.acosh(Math.sqrt(1 + v.v_0 ** 2 / vt2));
    return [
      bench('Range with no air resistance vs analytic parabola', r0.yf[0], v.v_0 * Math.cos(v.theta) * tv, 'x = v₀ cos θ · t_f', 1e-9),
      bench('Level-ground range with no air resistance vs v² sin 2θ / g', r1.yf[0], v.v_0 ** 2 * Math.sin(2 * v.theta) / v.g, 'Galileo\'s range formula', 1e-9),
      bench('Time of flight with no air resistance', r0.tf, tv, 'Root of the vertical motion', 1e-9),
      bench('Apex of a vertical launch with quadratic drag', vertex(Y, Y.indexOf(N.maxOf(Y)))[1], vt2 / (2 * v.g) * Math.log(1 + v.v_0 ** 2 / vt2), 'y_max = (v_t²/2g) ln(1 + v₀²/v_t²)', 1e-6),
      bench('Flight time of a vertical launch with quadratic drag', up.tf, tUp + tDown, 't = (v_t/g)[atan(v₀/v_t) + acosh√(1 + v₀²/v_t²)]', 1e-8),
    ];
  },
  validation: [],
  diagram(v, a) {
    const th = v.theta, x0 = 70, y0 = 290, c = Math.cos(th), s = Math.sin(th);
    const pts = N.linspace(0, 1, 40).map(u => [(x0 + 480 * u).toFixed(1), (y0 - 4 * 190 * u * (1 - u) * (a.drag ? 1 - 0.25 * u : 1)).toFixed(1)]);
    return svg(`
      ${S.path('M30 300 L610 300', 'd-ground')}
      ${S.poly(pts, 'd-line')} ${S.circle(x0, y0, 7, 'd-body')}
      ${S.arrow(x0, y0, x0 + 90 * c, y0 - 90 * s)} ${S.text(x0 + 96 * c + 6, y0 - 96 * s, `v₀ = ${lab(v.v_0, 'm/s')}`, 'd-text', 'start')}
      ${S.text(x0 + 60, y0 - 8, `θ = ${lab(th / DEG, '°')}`, 'd-text d-small', 'start')}
      ${S.arrow(330, 150, 330, 205)} ${S.text(338, 196, 'weight m·g', 'd-text', 'start')}
      ${a.drag ? S.arrow(330, 150, 270, 150, 'd-arrow d-hazard') + S.text(264, 142, 'drag ½ρC_D A v_r²', 'd-text', 'end') : S.text(264, 142, 'no air', 'd-text d-small', 'end')}
      ${a.still_air ? '' : S.arrow(470, 60, 550, 60) + S.text(510, 48, `wind ${lab(v.w, 'm/s')}`, 'd-text d-small')}
      ${S.dim(x0, 328, 550, 328, 'range R')}
    `);
  },
  experiment: {
    objective: 'Measure the trajectory of a launched ball with and without significant air resistance and compare range, apex and impact angle with the model.',
    apparatus: ['Spring or compressed-air launcher with adjustable elevation and repeatable speed', 'Dense steel ball (little drag) and a light ball of the same diameter such as a table-tennis ball (strong drag)', 'Calibrated backdrop grid and landing sand tray or carbon paper', 'Anemometer if working outdoors'],
    instruments: [{ name: 'High-speed camera', measures: 'Position against time', range: '10 m field of view', resolution: '240 frames/s, 2 mm' }, { name: 'Photogate pair at the muzzle', measures: 'Launch speed', range: '1–60 m/s', resolution: '±0.5 %' }, { name: 'Digital inclinometer', measures: 'Launch angle', range: '0–90°', resolution: '±0.1°' }, { name: 'Balance and callipers', measures: 'Mass and diameter', range: '—', resolution: '0.01 g, 0.02 mm' }],
    procedure: ['Measure launch speed with the photogates at each launcher setting.', 'Fire the steel ball at angles from 15° to 75° in 10° steps, recording range and video; repeat five times at each angle.', 'Repeat with the light ball.', 'Digitise the trajectories and fit the drag coefficient to the light-ball data; compare the steel-ball data with the parabola.'],
    controls: ['Steel ball as a near-vacuum control', 'Drop test of the light ball to measure terminal velocity independently', 'Indoor runs to remove wind'],
    signatures: ['Steel-ball range proportional to sin 2θ, greatest at 45°', 'Light-ball range greatest below 45°, with descent steeper than ascent', 'Range ratio set by launch speed over terminal velocity'],
    safety: ['Eye protection and a cleared firing line', 'Catch box or net behind the landing area', 'Never look down the launcher barrel'],
  },
  falsify: ['A dense projectile in still air whose range on level ground is not symmetric about 45° to within measurement error.', 'A horizontal velocity that changes in the absence of any horizontal force.', 'A fitted drag coefficient that must vary by orders of magnitude between shots at similar Reynolds number.'],
  alternatives: [{ name: 'Linear (Stokes) drag', text: 'For very small or slow bodies drag is proportional to speed and the equations separate, giving a closed-form trajectory.' }, { name: 'Mach- and Reynolds-dependent drag', text: 'Artillery and sports balls show a drag crisis or transonic drag rise; tabulated C_D replaces the constant.' }, { name: 'Rotating-Earth ballistics', text: 'Long-range fire needs the Coriolis and centrifugal terms and a curved Earth.' }],
  hazards: [{ hazard: 'Impact injury', cause: 'Projectile striking a person', mitigation: 'Cleared range, barriers, eye protection, low-energy launcher' }, { hazard: 'Ricochet', cause: 'Hard projectile on a hard surface', mitigation: 'Sand tray or soft catch box' }],
  standards: ['ISO 2533:1975 (Standard Atmosphere)', 'STANAG 4355 (the modified point mass and five degrees of freedom trajectory models)'],
  limits: 'Point mass in a vertical plane with constant drag and lift coefficients. Valid for subsonic flight at Reynolds numbers where the drag coefficient is roughly constant, over ranges small against the Earth\'s radius. No Coriolis force, cross-wind, spin decay or drag crisis.',
  numerics: { method: 'Adaptive Dormand–Prince RK45 with Newton location of the landing point', order: 5, stability: 'Step-size controlled to a relative tolerance of 10⁻¹⁰' },
  optimise: { objective: 'R', sense: 'max', vars: ['theta'], note: 'With drag the best angle lies below 45°; a tailwind raises it and a headwind lowers it.' },
  inverse: { series: 'trajectory', fit: ['C_D', 'v_0'] },
  extensions: ['Cross-wind and three-dimensional spin effects', 'Drag crisis for sports balls', 'Coriolis deflection for long-range trajectories'],
};

// ------------------------------------------------------------------ 9. nonlinear pendulum
const pendOmega = (v, a) => Math.sqrt((a.point_mass ? 1 : 1.5) * v.g / v.L);
const pendRhs = (v, a) => {
  const w0 = pendOmega(v, a);
  return (t, y) => { const d = !a.damped ? 0 : a.linear_damping ? 2 * v.zeta * w0 * y[1] : v.beta_q * y[1] * Math.abs(y[1]); return [y[1], -w0 * w0 * (a.exact_sin ? Math.sin(y[0]) : y[0]) - d, d * y[1]]; };
};
/** Period as twice the interval between the first two passages through the vertical, starting at rest at th0. */
function pendPeriod(v, a, th0 = v.theta_0, rtol = 1e-11) {
  const T0 = 2 * Math.PI / pendOmega(v, a), f = pendRhs(v, a), o = { rtol, atol: 1e-13 };
  const q1 = toEvent(f, [th0, 0, 0], 60 * T0, y => y[0], y => y[1], 2, o);
  if (!q1.hit) return NaN;
  const q2 = toEvent(f, [Math.min(q1.yHit[0], 0), q1.yHit[1], 0], 60 * T0, y => -y[0], y => -y[1], 2, o);
  return q2.hit ? 2 * q2.tHit : NaN;
}
const pendExact = th0 => 1 / agm(1, Math.cos(th0 / 2));     // T / T0 for the undamped pendulum
const pendulum = {
  id: 'pendulum-nonlinear',
  title: 'Large-angle pendulum with damping',
  module: [1, 2], klass: 'I', domains: ['classical', 'waves'],
  keywords: ['simple pendulum', 'pendulum period', 'large-angle pendulum', 'nonlinear pendulum', 'pendulum', 'small-angle approximation', 'elliptic integral', 'period of oscillation', 'isochronism', 'amplitude', 'damped pendulum', 'phase portrait', 'local gravity', 'swing'],
  summary: 'Motion of a pendulum at any amplitude, with viscous or quadratic damping: the exact period from the elliptic integral, its departure from the small-angle value, and the phase portrait.',
  background: [
    'For small swings the restoring torque of a pendulum is proportional to the angle and the motion is simple harmonic with a period independent of amplitude — the isochronism noticed by Galileo. At larger amplitudes the torque follows sin θ, the oscillation is no longer sinusoidal and the period lengthens, diverging as the amplitude approaches 180°.',
    'The exact period is a complete elliptic integral of the first kind, which is evaluated here to machine precision by the arithmetic–geometric mean. The pendulum is the standard example of a nonlinear oscillator, and because its period depends on the local gravitational acceleration it has long been used for gravimetry.',
  ],
  phenomena: ['Gravitational restoring torque', 'Amplitude-dependent period', 'Viscous and aerodynamic damping', 'Separatrix between oscillation and rotation'],
  laws: ['newton2', 'angular', 'energy', 'action'],
  refs: ['Huygens, C. (1673). Horologium Oscillatorium. F. Muguet, Paris.', 'Abramowitz, M. & Stegun, I. A. (1964). Handbook of Mathematical Functions. National Bureau of Standards.', 'Baker, G. L. & Blackburn, J. A. (2005). The Pendulum: A Case Study in Physics. Oxford University Press.', 'Nelson, R. A. & Olsson, M. G. (1986). The pendulum — rich physics from a simple system. American Journal of Physics 54, 112–121.', 'Carvalhaes, C. G. & Suppes, P. (2008). Approximations for the period of the simple pendulum based on the arithmetic-geometric mean. American Journal of Physics 76, 1150–1154.'],
  inputs: [
    inp('L', 'Pendulum length', 'm', 1, { min: 0.01, max: 100, kind: 'geometry', aliases: ['length', 'string length', 'pendulum length'] }),
    inp('theta_0', 'Release angle from the vertical', 'deg', 60, { min: 0.1, max: 179, aliases: ['amplitude', 'release angle', 'initial angle', 'angle'] }),
    inp('m', 'Mass', 'kg', 1, { min: 0.001, max: 1000, aliases: ['mass', 'bob mass'] }),
    inp('g', 'Local gravitational acceleration', 'm/s^2', 9.80665, { min: 0.1, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity', 'gravitational acceleration'] }),
    inp('zeta', 'Viscous damping ratio', '1', 0.01, { min: 0, max: 2, aliases: ['damping ratio', 'damping'] }),
    inp('beta_q', 'Quadratic damping coefficient (per radian)', '1', 0.02, { min: 0, max: 2, aliases: ['quadratic damping', 'air drag coefficient'] }),
    inp('n_per', 'Simulated time in small-angle periods', '1', 10, { min: 1, max: 100, aliases: ['periods', 'duration'] }),
  ],
  assumptions: [
    asm('exact_sin', 'The restoring torque is proportional to sin θ (no small-angle approximation).', { why: 'Exact for any amplitude', alt: 'Small-angle approximation sin θ ≈ θ: simple harmonic motion with amplitude-independent period.' }),
    asm('damped', 'Damping acts on the pendulum.', { why: 'Air and pivot friction', alt: 'No damping: mechanical energy is conserved.' }),
    asm('linear_damping', 'The damping torque is proportional to angular velocity (viscous).', { why: 'Low speed, pivot or laminar drag', alt: 'The damping torque is proportional to the square of angular velocity (aerodynamic drag on the bob).' }),
    asm('point_mass', 'The pendulum is a point mass on a massless rigid rod.', { why: 'Simple pendulum', alt: 'A uniform rod pivoted at one end (physical pendulum), equivalent to a simple pendulum of length 2L/3.' }),
  ],
  symbols: { theta: ['Angle from the vertical', 'rad'], t: ['Time', 's'], omega_0: ['Small-angle angular frequency', '1/s'], T_0: ['Small-angle period', 's'], T: ['Period at finite amplitude', 's'], phi: ['Integration variable', 'rad'], E: ['Mechanical energy', 'J'], I_p: ['Moment of inertia about the pivot', 'kg m^2'], L_c: ['Distance from pivot to centre of mass', 'm'] },
  equations: a => {
    const rest = a.exact_sin ? 'sin(theta)' : 'theta';
    const damp = !a.damped ? '' : a.linear_damping ? ' - 2*zeta*omega_0*d(theta,t)' : ' - beta_q*d(theta,t)*abs(d(theta,t))';
    return [
      eq('mom', 'Equation of motion', 'd2(theta,t)', `-omega_0^2*${rest}${damp}`, { kind: 'law', origin: 'Angular form of Newton\'s second law about the pivot', needs: ['exact_sin', 'damped'].filter(k => a[k]) }),
      a.point_mass ? eq('w0', 'Natural frequency', 'omega_0', 'sqrt(g/L)', { kind: 'derived', origin: 'm g L / (m L²)', needs: ['point_mass'] }) : eq('w0', 'Natural frequency of a uniform rod', 'omega_0', 'sqrt(3*g/(2*L))', { kind: 'derived', origin: 'm g (L/2) / (m L²/3)' }),
      eq('t0', 'Small-angle period', 'T_0', '2*pi/omega_0', { kind: 'derived', origin: 'Simple harmonic motion' }),
      a.exact_sin ? eq('per', 'Period at amplitude θ₀ (undamped)', 'T', '4/omega_0*int(1/sqrt(1 - sin(theta_0/2)^2*sin(phi)^2), phi)', { kind: 'derived', origin: 'Energy integral; complete elliptic integral of the first kind, φ from 0 to π/2' })
        : eq('per', 'Period (undamped)', 'T', 'T_0', { kind: 'derived', origin: 'Isochronism of small oscillations', needs: [] }),
      a.point_mass ? eq('en', 'Mechanical energy', 'E', `0.5*m*L^2*d(theta,t)^2 + ${a.exact_sin ? 'm*g*L*(1 - cos(theta))' : '0.5*m*g*L*theta^2'}`, { kind: 'law', origin: 'Kinetic plus gravitational potential energy' })
        : eq('en', 'Mechanical energy', 'E', `m*L^2*d(theta,t)^2/6 + ${a.exact_sin ? 'm*g*L*(1 - cos(theta))/2' : 'm*g*L*theta^2/4'}`, { kind: 'law', origin: 'Kinetic plus gravitational potential energy of a uniform rod' }),
    ];
  },
  derivation: a => [
    { text: 'Take moments about the pivot. The weight acts at the centre of mass and supplies a restoring torque; the angular acceleration follows from the moment of inertia.', tex: 'I\\,\\ddot\\theta = -m g\\,\\ell_c\\sin\\theta \\quad\\Rightarrow\\quad \\ddot\\theta = -\\omega_0^2\\sin\\theta,\\qquad \\omega_0^2 = \\frac{m g\\,\\ell_c}{I}' },
    ...(a.exact_sin ? [
      { text: 'Without damping the energy is conserved, which gives the angular velocity as a function of angle.', tex: '\\tfrac12\\dot\\theta^2 = \\omega_0^2(\\cos\\theta - \\cos\\theta_0)' },
      { text: 'Integrating dt = dθ/θ̇ over a quarter swing and substituting sin(θ/2) = k sin φ with k = sin(θ₀/2) gives the period as a complete elliptic integral.', tex: 'T = \\frac{4}{\\omega_0}\\int_0^{\\pi/2}\\frac{\\mathrm{d}\\varphi}{\\sqrt{1-k^2\\sin^2\\varphi}} = \\frac{4}{\\omega_0}K(k)' },
      { text: 'Gauss showed that K is given by the arithmetic–geometric mean, which converges quadratically; the series in the amplitude follows by expansion.', tex: '\\frac{T}{T_0} = \\frac{1}{\\mathrm{agm}\\!\\left(1,\\cos\\tfrac{\\theta_0}{2}\\right)} = 1 + \\frac{\\theta_0^2}{16} + \\frac{11\\,\\theta_0^4}{3072} + \\dots' },
    ] : [{ text: 'For small angles sin θ ≈ θ and the equation is that of a harmonic oscillator, with a period independent of amplitude.', tex: '\\ddot\\theta = -\\omega_0^2\\theta,\\qquad T_0 = \\frac{2\\pi}{\\omega_0}' }]),
    ...(a.damped ? [{ text: a.linear_damping ? 'A viscous torque proportional to angular velocity removes energy at a rate proportional to θ̇²; small oscillations decay exponentially with quality factor Q = 1/(2ζ).' : 'A torque proportional to θ̇|θ̇| models aerodynamic drag on the bob; the amplitude then decays algebraically rather than exponentially.', tex: a.linear_damping ? '\\ddot\\theta + 2\\zeta\\omega_0\\dot\\theta + \\omega_0^2\\sin\\theta = 0' : '\\ddot\\theta + \\beta\\,\\dot\\theta|\\dot\\theta| + \\omega_0^2\\sin\\theta = 0' }] : []),
  ],
  solve(v, a) {
    const w0 = pendOmega(v, a), T0 = 2 * Math.PI / w0, tEnd = v.n_per * T0, f = pendRhs(v, a);
    const s = dopri((t, y, d) => { const q = f(t, y); d[0] = q[0]; d[1] = q[1]; d[2] = q[2]; }, [v.theta_0, 0, 0], tEnd, 601, { rtol: 1e-9, atol: 1e-12, maxSteps: 100000 }), n = s.t.length, th = s.y.map(r => r[0]), om = s.y.map(r => r[1]), ds = s.y.map(r => r[2]);
    const pot = x => (a.exact_sin ? w0 * w0 * (1 - Math.cos(x)) : 0.5 * w0 * w0 * x * x), en = th.map((x, i) => 0.5 * om[i] ** 2 + pot(x)), e0 = en[0];
    const Iscale = (a.point_mass ? 1 : 1 / 3) * v.m * v.L ** 2;
    const Tex = (a.exact_sin ? pendExact(v.theta_0) : 1) * T0, Tnum = pendPeriod(v, a, v.theta_0, 1e-9);
    const wmax = a.exact_sin ? 2 * w0 * Math.sin(v.theta_0 / 2) : w0 * v.theta_0;
    const tension = a.point_mass ? v.m * v.g + v.m * v.L * wmax ** 2 : v.m * v.g + v.m * (v.L / 2) * wmax ** 2;
    const amps = N.linspace(1, 179, 90), small = s.t.map(t => v.theta_0 * Math.cos(w0 * t) / DEG);
    const warnings = [];
    if (v.theta_0 > 170 * DEG) warnings.push('The release angle is close to the inverted position, where the period diverges and the motion is extremely sensitive to damping and to the release conditions.');
    if (a.point_mass && v.theta_0 > 90 * DEG) warnings.push('Above 90° a string would go slack during part of the swing; the model assumes a rigid rod.');
    if (!a.exact_sin && v.theta_0 > 20 * DEG) warnings.push(`The small-angle approximation is being used at ${lab(v.theta_0 / DEG, '°')}, where it under-predicts the period by ${lab((pendExact(v.theta_0) - 1) * 100, '%')}.`);
    if (a.damped && a.linear_damping && v.zeta >= 1) warnings.push('The damping ratio is at or above critical: the pendulum returns to the vertical without oscillating.');
    const fs = every(n, 240), fi = s.t.map((_, i) => i).filter(i => i % fs === 0);
    return {
      scalars: [
        scalar('omega_0', 'Small-angle angular frequency', w0, '1/s'), scalar('T_0', 'Small-angle period', T0, 's'),
        scalar('T', 'Exact undamped period at this amplitude', Tex, 's'), scalar('T_num', 'Period measured from the simulation', Tnum, 's', { text: Number.isFinite(Tnum) ? undefined : 'No oscillation: the motion is overdamped' }),
        scalar('T_ratio', 'Exact period over small-angle period', Tex / T0, '1'), scalar('err_sa', 'Error of the small-angle period', T0 / (pendExact(v.theta_0) * T0) - 1, '1', { show: '%' }),
        scalar('v_max', a.point_mass ? 'Greatest speed of the bob (undamped)' : 'Greatest speed of the rod tip (undamped)', v.L * wmax, 'm/s'),
        scalar('F_max', a.point_mass ? 'Greatest tension in the rod (undamped)' : 'Greatest pivot reaction (undamped)', tension, 'N'),
        scalar('E_0', 'Initial mechanical energy above the rest position', Iscale * e0, 'J'), scalar('E_frac', 'Fraction of energy remaining at the end', en[n - 1] / e0, '1'),
        scalar('Q', 'Quality factor of small oscillations', a.damped && a.linear_damping && v.zeta > 0 ? 1 / (2 * v.zeta) : NaN, '1', { text: a.damped && a.linear_damping && v.zeta > 0 ? undefined : 'Not defined without viscous damping' }),
        scalar('theta_end', 'Angle at the end of the simulation', th[n - 1], 'rad', { show: 'deg' }),
      ],
      series: [
        line('angle', 'Angle against time', 'Time', 's', s.t, [{ label: 'Pendulum', data: th.map(x => x / DEG) }, { label: 'Undamped small-angle solution', data: small, dash: true }], 'Angle', 'deg'),
        line('phase', 'Phase portrait', 'Angle', 'deg', th.map(x => x / DEG), [{ label: 'Angular velocity', data: om }], 'Angular velocity', 'rad/s', { note: 'A closed curve when undamped; a spiral into the origin when damped.' }),
        line('period-amplitude', 'Period against amplitude', 'Amplitude', 'deg', amps, [{ label: 'Exact (elliptic integral)', data: amps.map(d => pendExact(d * DEG)) }, { label: 'Series to fourth order', data: amps.map(d => 1 + (d * DEG) ** 2 / 16 + 11 * (d * DEG) ** 4 / 3072), dash: true }, { label: 'Small-angle', data: amps.map(() => 1), dash: true }], 'Period / small-angle period', '–'),
        line('energy', 'Mechanical energy', 'Time', 's', s.t, [{ label: 'Energy / initial energy', data: en.map(e => e / e0) }], 'Relative energy', '–'),
      ],
      anims: [motion('swing', 'Pendulum motion', fi.map(i => [[0, 0], [v.L * Math.sin(th[i]), -v.L * Math.cos(th[i])]]), fi.map(i => s.t[i]), { trails: true, links: [[0, 1]], labels: ['Pivot', a.point_mass ? 'Bob' : 'Rod tip'], bounds: [-1.1 * v.L, 1.1 * v.L, -1.1 * v.L, 1.1 * v.L], unit: 'm' })],
      checks: [check('Energy balance', N.maxOf(en.map((e, i) => Math.abs(e0 - e - ds[i]))) / e0, 1e-7, a.damped ? 'Energy lost against the integrated damping power' : 'Mechanical energy is conserved')],
      warnings,
    };
  },
  benchmarks(v) {
    const ex = { exact_sin: true, damped: false, linear_damping: true, point_mass: true }, T0 = 2 * Math.PI * Math.sqrt(v.L / v.g), th10 = 10 * DEG;
    return [
      bench('Numerically integrated period vs elliptic-integral value', pendPeriod(v, ex), pendExact(v.theta_0) * T0, 'T = 4 K(sin θ₀/2)/ω₀ by the arithmetic–geometric mean', 1e-8),
      bench('Period ratio at 90° amplitude', pendExact(Math.PI / 2), 1.1803405990, '2K(1/√2)/π, Abramowitz & Stegun table 17.1', 1e-9),
      bench('Small-angle model: integrated period vs 2π√(L/g)', pendPeriod(v, { ...ex, exact_sin: false }), T0, 'Simple harmonic motion', 1e-8),
      bench('Period ratio at 10° vs amplitude series', pendExact(th10), 1 + th10 ** 2 / 16 + 11 * th10 ** 4 / 3072 + 173 * th10 ** 6 / 737280, 'Series expansion of the elliptic integral', 1e-9),
      bench('Uniform rod: integrated small-swing period', pendPeriod({ ...v, theta_0: 1e-4 }, { ...ex, point_mass: false }), 2 * Math.PI * Math.sqrt(2 * v.L / (3 * v.g)), 'Physical pendulum, T = 2π√(2L/3g)', 1e-8),
    ];
  },
  validation: [],
  diagram(v, a) {
    const th = Math.min(v.theta_0, 150 * DEG), px = 320, py = 70, len = 190, bx = px + len * Math.sin(th), by = py + len * Math.cos(th);
    return svg(`
      ${S.path('M240 70 L400 70', 'd-ground')} ${S.line(px, py, px, py + len + 20, 'd-dim')}
      ${a.point_mass ? S.line(px, py, bx, by, 'd-line') + S.circle(bx, by, 14, 'd-body') : S.path(`M${px} ${py} L${bx} ${by}`, 'd-pipe')}
      ${S.path(`M${px} ${py + 60} A60 60 0 0 0 ${(px + 60 * Math.sin(th)).toFixed(1)} ${(py + 60 * Math.cos(th)).toFixed(1)}`, 'd-line')} ${S.text(px + 34, py + 86, `θ₀ = ${lab(v.theta_0 / DEG, '°')}`, 'd-text', 'start')}
      ${S.arrow(bx, by, bx, by + 60)} ${S.text(bx + 10, by + 56, 'm·g', 'd-text', 'start')}
      ${S.text((px + bx) / 2 - 12, (py + by) / 2 - 8, `L = ${lab(v.L, 'm')}`, 'd-text', 'end')}
      ${S.text(40, 40, `T₀ = ${lab(2 * Math.PI / pendOmega(v, a), 's')}`, 'd-text', 'start')} ${S.text(40, 60, `T = ${lab(pendExact(v.theta_0) * 2 * Math.PI / pendOmega(v, a), 's')} at this amplitude`, 'd-text d-small', 'start')}
      ${S.text(320, 345, a.exact_sin ? 'θ̈ = −ω₀² sin θ' : 'θ̈ = −ω₀² θ (small-angle)', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the period of a pendulum as a function of amplitude and compare with the elliptic-integral prediction; use the small-amplitude period to determine local g.',
    apparatus: ['Rigid light rod or bifilar suspension with a dense compact bob', 'Low-friction knife-edge or ball-bearing pivot on a rigid support', 'Protractor scale or rotary encoder at the pivot', 'Release mechanism giving zero initial velocity'],
    instruments: [{ name: 'Photogate timer at the lowest point', measures: 'Period', range: '0.1–20 s', resolution: '0.1 ms' }, { name: 'Rotary encoder', measures: 'Angle against time', range: '±180°', resolution: '0.1°, 1 kHz' }, { name: 'Steel tape and callipers', measures: 'Length to the centre of mass of the bob', range: '0–2 m', resolution: '0.5 mm' }],
    procedure: ['Measure the length from pivot to the centre of the bob.', 'Release from amplitudes of 5°, 10°, 20°, … up to 150°, timing the first few complete swings before damping reduces the amplitude appreciably.', 'Record the amplitude at the start and end of each timed interval and assign the period to the mean amplitude.', 'Plot T/T₀ against amplitude; extrapolate to zero amplitude to obtain T₀ and hence g = 4π²L/T₀².'],
    controls: ['Repeat with a second length to confirm T₀ ∝ √L', 'Repeat with a different bob mass of the same size to confirm independence of mass', 'Measure the decay of amplitude to correct the period for damping'],
    signatures: ['Period independent of mass', 'T/T₀ = 1.0043 at 15°, 1.0174 at 30°, 1.0732 at 60°, 1.1803 at 90°', 'T₀ proportional to the square root of length'],
    safety: ['Keep clear of the swing arc at large amplitudes', 'Secure the support against tipping', 'Check the suspension for wear before large-angle releases'],
  },
  falsify: ['A period that depends on the mass of the bob at fixed length and amplitude.', 'A period ratio at 90° amplitude differing from 1.1803 by more than the experimental uncertainty for a rigid, lightly damped pendulum.', 'A period that shortens as amplitude increases.'],
  alternatives: [{ name: 'Cycloidal pendulum', text: 'Huygens showed that a bob constrained to a cycloid is exactly isochronous at all amplitudes.' }, { name: 'Driven damped pendulum', text: 'Adding a periodic drive produces period doubling and chaos.' }, { name: 'Finite-size and buoyancy corrections', text: 'Precision gravimetry corrects for the bob\'s moment of inertia, air buoyancy, added mass and the stretch of the suspension.' }],
  hazards: [{ hazard: 'Impact from the bob', cause: 'Standing in the swing arc', mitigation: 'Mark and guard the swept area' }, { hazard: 'Suspension failure', cause: 'Worn string or pivot at large amplitude', mitigation: 'Inspect before use; apply a safety factor of at least 5 on the peak tension' }],
  standards: ['ISO 80000-3 (quantities and units — space and time)', 'ISO/IEC Guide 98-3 (uncertainty of measurement — guide to the expression of uncertainty in measurement)'],
  limits: 'Rigid pendulum in a plane with a fixed pivot. Amplitudes below 180°; the exact period refers to the undamped pendulum. Damping is idealised as purely viscous or purely quadratic. No string elasticity, pivot motion, buoyancy or added-mass corrections.',
  numerics: { method: 'Adaptive Dormand–Prince RK45; exact period by the arithmetic–geometric mean; measured period from a Newton-located zero crossing', order: 5, stability: 'Step-size controlled to a relative tolerance of 10⁻⁹' },
  optimise: { objective: 'err_sa', sense: 'max', vars: ['theta_0'], note: 'The small-angle error is negative and grows in magnitude with amplitude; it vanishes as the amplitude tends to zero.' },
  inverse: { series: 'angle', fit: ['g', 'zeta'] },
  extensions: ['Periodically driven pendulum and the route to chaos', 'Kapitza pendulum with a vibrating pivot', 'Precision gravimetry corrections (Kater\'s reversible pendulum)'],
};

// ------------------------------------------------------------------ 10. double pendulum
function dpCoef(v, a) {
  const p = a.point_masses, k1 = p ? 1 : 1 / 3, kb = p ? 1 : 0.5, k2 = p ? 1 : 1 / 3, kg = p ? 1 : 0.5;
  return { A: (k1 * v.m_1 + v.m_2) * v.L_1 ** 2, B: kb * v.m_2 * v.L_1 * v.L_2, Cc: k2 * v.m_2 * v.L_2 ** 2, G1: (kg * v.m_1 + v.m_2) * v.g * v.L_1, G2: kg * v.m_2 * v.g * v.L_2 };
}
/** Angular accelerations from the 2×2 mass matrix; `out` receives [θ̈₁, θ̈₂]. */
const dpAccel = (c, a, cj) => (t1, t2, w1, w2, out, o = 0) => {
  const D = t1 - t2, cD = a.nonlinear ? Math.cos(D) : 1, sD = a.nonlinear ? Math.sin(D) : 0, s1 = a.nonlinear ? Math.sin(t1) : t1, s2 = a.nonlinear ? Math.sin(t2) : t2;
  const f1 = -c.B * w2 * w2 * sD - c.G1 * s1 - cj * (2 * w1 - w2), f2 = c.B * w1 * w1 * sD - c.G2 * s2 - cj * (w2 - w1), M12 = c.B * cD, det = c.A * c.Cc - M12 * M12;
  out[o] = (c.Cc * f1 - M12 * f2) / det; out[o + 1] = (c.A * f2 - M12 * f1) / det;
};
const dpEnergy = (c, a) => (t1, t2, w1, w2) => 0.5 * c.A * w1 * w1 + 0.5 * c.Cc * w2 * w2 + c.B * (a.nonlinear ? Math.cos(t1 - t2) : 1) * w1 * w2 + (a.nonlinear ? c.G1 * (1 - Math.cos(t1)) + c.G2 * (1 - Math.cos(t2)) : 0.5 * c.G1 * t1 * t1 + 0.5 * c.G2 * t2 * t2);
const dpModes = c => { const p = c.A * c.Cc - c.B * c.B, q = c.A * c.G2 + c.Cc * c.G1, disc = Math.sqrt(Math.max(q * q - 4 * p * c.G1 * c.G2, 0)); return [Math.sqrt((q - disc) / (2 * p)), Math.sqrt((q + disc) / (2 * p))]; };
const doublePendulum = {
  id: 'double-pendulum',
  title: 'Double pendulum: chaos and energy conservation',
  module: [1, 2], klass: 'I', domains: ['classical'],
  keywords: ['double pendulum', 'chaotic pendulum', 'coupled pendulums', 'lyapunov exponent', 'chaos', 'sensitive dependence', 'normal modes', 'lagrangian mechanics', 'butterfly effect', 'two-link pendulum', 'compound pendulum'],
  summary: 'Planar double pendulum integrated from the Lagrangian equations of motion, with an energy check, normal-mode frequencies, and the divergence of a minutely displaced twin to exhibit chaos.',
  background: [
    'Two pendulums hung one from the other form a system with two degrees of freedom whose only conserved quantity is the energy. For small swings the motion is a superposition of two normal modes with fixed frequencies. At large amplitudes the equations are strongly nonlinear and the motion is chaotic: two releases differing by an immeasurably small angle follow visibly different paths within seconds.',
    'The double pendulum is the standard laboratory example of deterministic chaos in a conservative mechanical system, and a convenient test of numerical integrators because the energy must remain constant however irregular the motion.',
  ],
  phenomena: ['Coupled nonlinear oscillation', 'Normal modes', 'Deterministic chaos', 'Exponential divergence of nearby trajectories'],
  laws: ['action', 'newton2', 'energy', 'angular'],
  refs: ['Shinbrot, T., Grebogi, C., Wisdom, J. & Yorke, J. A. (1992). Chaos in a double pendulum. American Journal of Physics 60, 491–499.', 'Levien, R. B. & Tan, S. M. (1993). Double pendulum: an experiment in chaos. American Journal of Physics 61, 1038–1044.', 'Goldstein, H., Poole, C. & Safko, J. (2002). Classical Mechanics, 3rd ed., Addison-Wesley.', 'Landau, L. D. & Lifshitz, E. M. (1976). Mechanics, 3rd ed., Pergamon Press.', 'Strogatz, S. H. (2015). Nonlinear Dynamics and Chaos, 2nd ed., Westview Press.'],
  inputs: [
    inp('m_1', 'Upper mass', 'kg', 1, { min: 0.01, max: 100, aliases: ['upper mass', 'first mass'] }),
    inp('m_2', 'Lower mass', 'kg', 1, { min: 0.01, max: 100, aliases: ['lower mass', 'second mass'] }),
    inp('L_1', 'Upper length', 'm', 1, { min: 0.05, max: 10, kind: 'geometry', aliases: ['upper length', 'first length', 'length'] }),
    inp('L_2', 'Lower length', 'm', 1, { min: 0.05, max: 10, kind: 'geometry', aliases: ['lower length', 'second length'] }),
    inp('theta_1', 'Initial angle of the upper arm from the vertical', 'deg', 120, { min: -180, max: 180, aliases: ['upper angle', 'first angle', 'initial angle'] }),
    inp('theta_2', 'Initial angle of the lower arm from the vertical', 'deg', -10, { min: -180, max: 180, aliases: ['lower angle', 'second angle'] }),
    inp('g', 'Gravitational acceleration', 'm/s^2', 9.80665, { min: 0.5, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity'] }),
    inp('t_end', 'Simulated time', 's', 20, { min: 1, max: 60, aliases: ['duration', 'simulation time'] }),
    inp('delta', 'Initial angular offset of the twin', 'rad', 1e-8, { min: 1e-12, max: 0.01, aliases: ['perturbation', 'offset'] }),
    inp('c_j', 'Viscous damping coefficient at each joint', 'N m s', 0.02, { min: 0, max: 5, aliases: ['joint damping', 'damping'] }),
  ],
  assumptions: [
    asm('nonlinear', 'The full nonlinear equations of motion are used.', { why: 'Exact for any amplitude', alt: 'Linearised small-angle equations: a superposition of two normal modes, never chaotic.' }),
    asm('frictionless', 'The joints are frictionless: mechanical energy is conserved.', { why: 'Good bearings over a short run', alt: 'Viscous torque at each joint proportional to the relative angular velocity.' }),
    asm('point_masses', 'Each arm is a point mass on a massless rigid rod.', { why: 'Idealised double pendulum', alt: 'Each arm is a uniform rigid rod of the stated mass and length.' }),
  ],
  symbols: { phi_1: ['Angle of the upper arm', 'rad'], phi_2: ['Angle of the lower arm', 'rad'], omega_1: ['Angular velocity of the upper arm', '1/s'], omega_2: ['Angular velocity of the lower arm', '1/s'], t: ['Time', 's'], E: ['Mechanical energy', 'J'], delta_s: ['Separation of the twin trajectories', 'rad'], lambda: ['Finite-time Lyapunov exponent', '1/s'], omega_n: ['Normal-mode angular frequency (equal masses and lengths)', '1/s'] },
  equations: a => {
    const p = a.point_masses, A = p ? '(m_1 + m_2)*L_1^2' : '(m_1/3 + m_2)*L_1^2', B = p ? 'm_2*L_1*L_2' : 'm_2*L_1*L_2/2', Cc = p ? 'm_2*L_2^2' : 'm_2*L_2^2/3', G1 = p ? '(m_1 + m_2)*g*L_1' : '(m_1/2 + m_2)*g*L_1', G2 = p ? 'm_2*g*L_2' : 'm_2*g*L_2/2';
    const cD = a.nonlinear ? '*cos(phi_1 - phi_2)' : '', s = k => (a.nonlinear ? `sin(phi_${k})` : `phi_${k}`);
    const d1 = a.frictionless ? '' : ' - c_j*(2*omega_1 - omega_2)', d2 = a.frictionless ? '' : ' - c_j*(omega_2 - omega_1)';
    return [
      eq('e1', 'Upper arm', `${A}*d(omega_1,t) + ${B}${cD}*d(omega_2,t)`, `${a.nonlinear ? `-${B}*omega_2^2*sin(phi_1 - phi_2) ` : ''}- ${G1}*${s(1)}${d1}`, { kind: 'law', origin: 'Euler–Lagrange equation for the first coordinate', needs: ['nonlinear', 'frictionless'].filter(k => a[k]) }),
      eq('e2', 'Lower arm', `${B}${cD}*d(omega_1,t) + ${Cc}*d(omega_2,t)`, `${a.nonlinear ? `${B}*omega_1^2*sin(phi_1 - phi_2) ` : ''}- ${G2}*${s(2)}${d2}`, { kind: 'law', origin: 'Euler–Lagrange equation for the second coordinate', needs: ['nonlinear', 'frictionless'].filter(k => a[k]) }),
      eq('k1', 'Kinematics, upper arm', 'd(phi_1,t)', 'omega_1', { kind: 'definition' }), eq('k2', 'Kinematics, lower arm', 'd(phi_2,t)', 'omega_2', { kind: 'definition' }),
      eq('i1', 'Initial upper angle', 'phi_1', 'theta_1', { kind: 'initial' }), eq('i2', 'Initial lower angle', 'phi_2', 'theta_2', { kind: 'initial' }),
      eq('en', 'Mechanical energy', 'E', `0.5*${A}*omega_1^2 + 0.5*${Cc}*omega_2^2 + ${B}${cD}*omega_1*omega_2 ${a.nonlinear ? `+ ${G1}*(1 - cos(phi_1)) + ${G2}*(1 - cos(phi_2))` : `+ 0.5*${G1}*phi_1^2 + 0.5*${G2}*phi_2^2`}`, { kind: 'law', origin: 'Kinetic plus potential energy, measured from the hanging position', needs: a.frictionless ? ['frictionless'] : [] }),
      ...(p ? [eq('modes', 'Normal modes for equal masses and lengths', 'omega_n^2', '(2 + sqrt(2))*g/L_1', { kind: 'derived', origin: 'Eigenvalues of the linearised equations; the second mode has 2 − √2', note: 'Shown for m₁ = m₂ and L₁ = L₂.' })] : [eq('modes', 'Normal modes for equal uniform rods', 'omega_n^2', '(3 + 6/sqrt(7))*g/L_1', { kind: 'derived', origin: 'Eigenvalues of the linearised equations; the second mode has 3 − 6/√7', note: 'Shown for m₁ = m₂ and L₁ = L₂.' })]),
      eq('lyap', 'Growth of the twin separation', 'd(delta_s,t)', 'lambda*delta_s', { kind: 'definition', origin: 'Definition of the (finite-time) Lyapunov exponent' }),
    ];
  },
  derivation: a => [
    { text: 'Use the two angles from the vertical as generalised coordinates. The kinetic energy contains a cross term because the lower arm is carried by the upper one.', tex: a.point_masses ? 'T = \\tfrac12(m_1+m_2)L_1^2\\dot\\varphi_1^2 + \\tfrac12 m_2L_2^2\\dot\\varphi_2^2 + m_2L_1L_2\\dot\\varphi_1\\dot\\varphi_2\\cos(\\varphi_1-\\varphi_2)' : 'T = \\tfrac12\\left(\\tfrac13 m_1+m_2\\right)L_1^2\\dot\\varphi_1^2 + \\tfrac16 m_2L_2^2\\dot\\varphi_2^2 + \\tfrac12 m_2L_1L_2\\dot\\varphi_1\\dot\\varphi_2\\cos(\\varphi_1-\\varphi_2)' },
    { text: 'The potential energy is gravitational.', tex: a.point_masses ? 'V = -(m_1+m_2)gL_1\\cos\\varphi_1 - m_2gL_2\\cos\\varphi_2' : 'V = -\\left(\\tfrac12 m_1+m_2\\right)gL_1\\cos\\varphi_1 - \\tfrac12 m_2gL_2\\cos\\varphi_2' },
    { text: 'The Euler–Lagrange equations for L = T − V give two coupled second-order equations, linear in the angular accelerations, which are solved at each step as a 2×2 system.', tex: '\\frac{\\mathrm d}{\\mathrm dt}\\frac{\\partial L}{\\partial\\dot\\varphi_i} - \\frac{\\partial L}{\\partial\\varphi_i} = 0\\quad\\Rightarrow\\quad \\mathbf M(\\varphi)\\,\\ddot{\\boldsymbol\\varphi} = \\mathbf f(\\varphi,\\dot\\varphi)' },
    { text: 'Linearising about the hanging position gives constant matrices; the normal-mode frequencies are the roots of the characteristic equation.', tex: '\\det\\!\\left(\\mathbf K - \\omega^2\\mathbf M_0\\right) = 0\\quad\\Rightarrow\\quad \\omega^2 = (2\\pm\\sqrt2)\\,\\frac{g}{L}\\ \\text{for equal point masses and lengths}' },
    { text: 'A twin pendulum released with a slightly different upper angle is integrated alongside. In the chaotic regime their separation grows exponentially until it saturates at the size of the accessible region.', tex: '\\delta(t)\\simeq\\delta_0\\,e^{\\lambda t}' },
  ],
  solve(v, a) {
    const c = dpCoef(v, a), cj = a.frictionless ? 0 : v.c_j, acc = dpAccel(c, a, cj), en = dpEnergy(c, a), w0 = Math.sqrt(v.g / v.L_1);
    const f = (t, y, d) => { for (let o = 0; o < 8; o += 4) { d[o] = y[o + 2]; d[o + 1] = y[o + 3]; acc(y[o], y[o + 1], y[o + 2], y[o + 3], d, o + 2); } };
    const s = dopri(f, [v.theta_1, v.theta_2, 0, 0, v.theta_1 + v.delta, v.theta_2, 0, 0], v.t_end, 601, { rtol: 1e-9, atol: 1e-12, maxSteps: 30000 }), n = s.t.length;
    const E = s.y.map(r => en(r[0], r[1], r[2], r[3])), Es = c.G1 + c.G2, dE = E.map(e => (e - E[0]) / Es);
    const sep = s.y.map(r => Math.sqrt((r[0] - r[4]) ** 2 + (r[1] - r[5]) ** 2 + ((r[2] - r[6]) ** 2 + (r[3] - r[7]) ** 2) / (w0 * w0)));
    const gr = growthFit(s.t, sep), lam = gr.lam, noExp = 'Not exponential: the separation does not grow exponentially';
    const kf = s.y.findIndex(r => Math.abs(r[1]) > Math.PI || Math.abs(r[0]) > Math.PI), modes = dpModes(c);
    const ksat = sep.findIndex(x => x > 1), rise = N.maxOf(dE);
    const warnings = [];
    if (!s.complete) warnings.push('The integrator reached its step limit before the end of the requested time; results cover only the part shown.');
    if (a.nonlinear && ksat > 0) warnings.push(`The twin trajectories have fully separated after about ${lab(s.t[ksat], 's')}: beyond that time the detailed motion is unpredictable from the stated initial conditions.`);
    if (!a.nonlinear && Math.max(Math.abs(v.theta_1), Math.abs(v.theta_2)) > 20 * DEG) warnings.push('The linearised equations are being used far outside their small-angle range.');
    const fs = every(n, 300), fi = s.t.map((_, k) => k).filter(k => k % fs === 0), reach = v.L_1 + v.L_2;
    const pos = r => { const x1 = v.L_1 * Math.sin(r[0]), y1 = -v.L_1 * Math.cos(r[0]); return [[0, 0], [x1, y1], [x1 + v.L_2 * Math.sin(r[1]), y1 - v.L_2 * Math.cos(r[1])]]; };
    return {
      scalars: [
        scalar('E', 'Initial mechanical energy above the hanging position', E[0], 'J'), scalar('dE', 'Largest energy error (fraction of the potential-energy scale)', N.maxOf(dE.map(Math.abs)), '1', { note: a.frictionless ? undefined : 'includes the energy removed by joint damping' }),
        scalar('omega_a', 'Lower normal-mode angular frequency', modes[0], '1/s'), scalar('omega_b', 'Upper normal-mode angular frequency', modes[1], '1/s'),
        scalar('T_a', 'Period of the lower normal mode', 2 * Math.PI / modes[0], 's'), scalar('T_b', 'Period of the upper normal mode', 2 * Math.PI / modes[1], 's'),
        scalar('law', 'Character of the divergence', gr.chaotic ? 1 : 0, '1', { text: GROWTH[gr.chaotic ? 1 : 0] }),
        scalar('lambda', 'Finite-time Lyapunov exponent (slope of ln separation against time)', lam, '1/s', { note: gr.chaotic ? undefined : 'the growth is not exponential, so this slope is not a true exponent' }),
        scalar('t_e', 'E-folding time of the twin separation', gr.chaotic ? 1 / lam : NaN, 's', { text: gr.chaotic ? undefined : noExp }),
        scalar('growth', 'Growth factor of the twin separation', sep[n - 1] / sep[0], '1'),
        scalar('t_flip', 'Time of the first full rotation of an arm', kf >= 0 ? s.t[kf] : NaN, 's', { text: kf >= 0 ? undefined : 'Neither arm passes through the inverted position' }),
        scalar('t_pred', 'Predictability horizon (twin separation reaches 1 rad)', ksat > 0 ? s.t[ksat] : NaN, 's', { text: ksat > 0 ? undefined : 'Not reached within the simulated time' }),
        scalar('E_end', 'Fraction of initial energy remaining', E[0] !== 0 ? E[n - 1] / E[0] : 1, '1'),
      ],
      series: [
        line('angles', 'Angles against time', 'Time', 's', s.t, [{ label: 'Upper arm', data: s.y.map(r => r[0] / DEG) }, { label: 'Lower arm', data: s.y.map(r => r[1] / DEG) }, { label: 'Lower arm of the twin', data: s.y.map(r => r[5] / DEG), dash: true }], 'Angle', 'deg'),
        line('separation', 'Divergence of the twin', 'Time', 's', s.t, [{ label: 'log₁₀ separation', data: sep.map(x => Math.log10(Math.max(x, 1e-300))) }, { label: 'Exponential fit', data: s.t.map(t => (Math.log(sep[0] || v.delta) + lam * t) / Math.LN10), dash: true }], 'log₁₀ separation', '–'),
        line('energy', 'Energy error', 'Time', 's', s.t, [{ label: 'Energy change / potential-energy scale', data: dE }], 'Relative change', '–'),
        line('config', 'Configuration-space path', 'Upper angle', 'deg', s.y.map(r => r[0] / DEG), [{ label: 'Lower angle', data: s.y.map(r => r[1] / DEG) }], 'Lower angle', 'deg'),
      ],
      anims: [motion('pendulum', 'Double-pendulum motion', fi.map(k => pos(s.y[k])), fi.map(k => s.t[k]), { trails: true, links: [[0, 1], [1, 2]], labels: ['Pivot', 'Upper mass', 'Lower mass'], bounds: [-1.1 * reach, 1.1 * reach, -1.1 * reach, 1.1 * reach], unit: 'm' })],
      checks: [a.frictionless ? check('Energy conservation', N.maxOf(dE.map(Math.abs)), 1e-7, 'Largest change of mechanical energy relative to the potential-energy scale')
        : check('Energy never increases', Math.max(rise, 0), 1e-8, 'With joint damping the mechanical energy can only fall')],
      warnings,
    };
  },
  benchmarks(v) {
    const pt = { nonlinear: true, frictionless: true, point_masses: true }, eqv = { ...v, m_1: 1, m_2: 1, L_1: v.L_1, L_2: v.L_1 };
    const mp = dpModes(dpCoef(eqv, pt)), mr = dpModes(dpCoef(eqv, { ...pt, point_masses: false })), gl = v.g / v.L_1;
    // quarter period of the slow mode at small amplitude, from the nonlinear equations
    const c = dpCoef(eqv, pt), acc = dpAccel(c, pt, 0), ratio = (c.G1 - mp[0] ** 2 * c.A) / (mp[0] ** 2 * c.B), e = 1e-4;
    const f = (t, y) => { const o = [0, 0]; acc(y[0], y[1], y[2], y[3], o); return [y[2], y[3], o[0], o[1]]; };
    const q = toEvent(f, [e, e * ratio, 0, 0], 20 / mp[0], y => y[0], y => y[2], 2, { rtol: 1e-11, atol: 1e-15 });
    return [
      bench('Lower normal mode, equal point masses and lengths', mp[0] ** 2, (2 - Math.SQRT2) * gl, 'ω² = (2 − √2) g/L', 1e-12),
      bench('Upper normal mode, equal point masses and lengths', mp[1] ** 2, (2 + Math.SQRT2) * gl, 'ω² = (2 + √2) g/L', 1e-12),
      bench('Lower normal mode, two equal uniform rods', mr[0] ** 2, (3 - 6 / Math.sqrt(7)) * gl, 'ω² = (3 − 6/√7) g/L', 1e-12),
      bench('Upper normal mode, two equal uniform rods', mr[1] ** 2, (3 + 6 / Math.sqrt(7)) * gl, 'ω² = (3 + 6/√7) g/L', 1e-12),
      bench('Small-amplitude period of the slow mode from the nonlinear equations', 4 * q.tHit, 2 * Math.PI / mp[0], 'Linear normal-mode analysis', 1e-6),
    ];
  },
  validation: [],
  diagram(v, a) {
    const sc = 120 / Math.max(v.L_1 + v.L_2, 1e-9) * 1.4, px = 320, py = 150, x1 = px + sc * v.L_1 * Math.sin(v.theta_1), y1 = py + sc * v.L_1 * Math.cos(v.theta_1), x2 = x1 + sc * v.L_2 * Math.sin(v.theta_2), y2 = y1 + sc * v.L_2 * Math.cos(v.theta_2);
    return svg(`
      ${S.path('M250 150 L390 150', 'd-ground')} ${S.line(px, py, px, py + 150, 'd-dim')}
      ${a.point_masses ? S.line(px, py, x1, y1, 'd-line') + S.line(x1, y1, x2, y2, 'd-line') + S.circle(x1, y1, 11, 'd-body') + S.circle(x2, y2, 11, 'd-body') : S.path(`M${px} ${py} L${x1.toFixed(1)} ${y1.toFixed(1)}`, 'd-pipe') + S.path(`M${x1.toFixed(1)} ${y1.toFixed(1)} L${x2.toFixed(1)} ${y2.toFixed(1)}`, 'd-pipe')}
      ${S.circle(px, py, 4, 'd-body')}
      ${S.text(x1 + 16, y1 - 6, `m₁ = ${lab(v.m_1, 'kg')}`, 'd-text d-small', 'start')} ${S.text(x2 + 16, y2 + 4, `m₂ = ${lab(v.m_2, 'kg')}`, 'd-text d-small', 'start')}
      ${S.text(40, 40, `θ₁ = ${lab(v.theta_1 / DEG, '°')}   θ₂ = ${lab(v.theta_2 / DEG, '°')}`, 'd-text', 'start')}
      ${S.text(40, 60, `L₁ = ${lab(v.L_1, 'm')}   L₂ = ${lab(v.L_2, 'm')}`, 'd-text d-small', 'start')}
      ${S.text(600, 40, `twin offset ${lab(v.delta, 'rad')}`, 'd-text d-small', 'end')}
      ${S.arrow(560, 250, 560, 310)} ${S.text(550, 300, 'g', 'd-text', 'end')}
    `);
  },
  experiment: {
    objective: 'Observe the transition from regular normal-mode motion to chaos in a double pendulum and measure the rate at which nominally identical releases diverge.',
    apparatus: ['Double pendulum of two rigid aluminium bars on low-friction ball bearings', 'Rigid wall mount', 'Release jig giving repeatable initial angles and zero velocity', 'Reflective markers or LEDs on each joint and tip'],
    instruments: [{ name: 'High-speed camera with tracking software', measures: 'Angles of both arms against time', range: 'full rotation', resolution: '0.2°, 240 frames/s' }, { name: 'Rotary encoders on both joints (optional)', measures: 'Angles directly', range: 'continuous', resolution: '0.05°' }, { name: 'Balance and rule', measures: 'Masses, lengths and centre-of-mass positions', range: '—', resolution: '0.1 g, 0.5 mm' }],
    procedure: ['Measure the small-amplitude frequencies by releasing in each normal-mode shape and compare with the predicted values.', 'Release repeatedly from the same large angle, recording at least ten runs.', 'Overlay the angle histories and measure the growth of the spread between runs with time.', 'Repeat for a range of release angles to map regular and chaotic regions.'],
    controls: ['Single-arm run (lower joint clamped) to characterise bearing friction', 'Small-angle releases, which must remain repeatable for the whole run'],
    signatures: ['Two sharp spectral lines at the normal-mode frequencies for small swings', 'Run-to-run spread growing exponentially at large angles and broad-band spectra', 'Energy decaying slowly and monotonically through bearing friction'],
    safety: ['Guard the swept circle: the lower arm moves fast and unpredictably', 'Check fasteners before each session', 'Keep hair and loose clothing clear'],
  },
  falsify: ['Mechanical energy increasing in the absence of a drive.', 'Small-amplitude frequencies differing from the normal-mode values by more than the uncertainty in the measured inertias.', 'Large-angle releases that remain repeatable indefinitely as release precision is varied, contradicting sensitive dependence.'],
  alternatives: [{ name: 'Hamiltonian formulation', text: 'Using angles and conjugate momenta gives first-order canonical equations and allows Poincaré sections to separate regular from chaotic regions.' }, { name: 'Driven or damped double pendulum', text: 'With dissipation and forcing the long-term motion settles on a strange attractor.' }, { name: 'Elastic or three-dimensional pendulums', text: 'Spring pendulums and spherical double pendulums show internal resonance and additional chaotic regimes.' }],
  hazards: [{ hazard: 'Impact from the rotating lower arm', cause: 'Unpredictable full rotations', mitigation: 'Transparent guard and a marked exclusion circle' }, { hazard: 'Fastener loosening', cause: 'Reversing loads', mitigation: 'Thread-lock and inspection before use' }],
  standards: ['ISO 12100 (safety of machinery — general principles for design)', 'IEEE 754 (floating-point arithmetic)'],
  limits: 'Planar motion of two rigid arms with ideal pivots. Chaotic trajectories are individually meaningful only for a few e-folding times; the Lyapunov exponent is a finite-time estimate from one pair of trajectories. No aerodynamic drag, bearing stiction or arm flexibility.',
  numerics: { method: 'Adaptive Dormand–Prince RK45 at relative tolerance 10⁻⁹, reference and twin integrated together', order: 5, stability: 'Energy error monitored as the accuracy indicator' },
  optimise: { objective: 'lambda', sense: 'max', vars: ['theta_1'], note: 'The divergence rate rises steeply once the release energy allows the lower arm to rotate.' },
  inverse: { series: 'angles', fit: ['L_2', 'm_2'] },
  extensions: ['Poincaré sections and flip-time maps over the plane of initial angles', 'Driven double pendulum and control at the inverted position', 'Triple pendulum and chains'],
};

// ------------------------------------------------------------------ 11. mass–spring–damper
/** Closed-form response of m x'' + c x' + k x = Fc cos ωt + Fs sin ωt with x(0) = x0, x'(0) = v0. Returns x(t). */
function sdofExact(m, c, k, Fc, Fs, w, x0, v0) {
  const wn = Math.sqrt(k / m), z = c / (2 * Math.sqrt(k * m)), dk = k - m * w * w, det = dk * dk + (c * w) ** 2;
  const pa = det > 0 ? (dk * Fc - c * w * Fs) / det : 0, pb = det > 0 ? (dk * Fs + c * w * Fc) / det : 0, h0 = x0 - pa, g0 = v0 - w * pb;
  let hom;
  if (Math.abs(z - 1) < 1e-9) hom = t => (h0 + (g0 + wn * h0) * t) * Math.exp(-wn * t);
  else if (z < 1) { const wd = wn * Math.sqrt(1 - z * z), c2 = (g0 + z * wn * h0) / wd; hom = t => Math.exp(-z * wn * t) * (h0 * Math.cos(wd * t) + c2 * Math.sin(wd * t)); }
  else { const q = wn * Math.sqrt(z * z - 1), s1 = -z * wn + q, s2 = -z * wn - q, c1 = (g0 - s2 * h0) / (s1 - s2); hom = t => c1 * Math.exp(s1 * t) + (h0 - c1) * Math.exp(s2 * t); }
  return { x: t => hom(t) + pa * Math.cos(w * t) + pb * Math.sin(w * t), steady: t => pa * Math.cos(w * t) + pb * Math.sin(w * t), amp: Math.hypot(pa, pb) };
}
const sdofMass = (v, a) => (a.massless_spring ? v.m : v.m + v.m_s / 3);
/** Steady-state amplitude(s) at angular frequency w: [upper branch, lower branch]. */
function sdofAmp(v, a, w) {
  const m = sdofMass(v, a), Fa = a.force_excited ? v.F_0 : v.Y_b * Math.hypot(v.k, a.viscous ? v.c * w : 0), dk = v.k - m * w * w, cw = a.viscous ? v.c * w : 0;
  if (a.linear) {
    if (a.viscous) { const x = Fa / Math.sqrt(dk * dk + cw * cw); return [x, x]; }
    const fr = 4 * v.mu_f * m * G0 / Math.PI, x = Fa > fr ? Math.sqrt(Fa * Fa - fr * fr) / Math.max(Math.abs(dk), 1e-3 * v.k) : 0;    // Den Hartog equivalent-damping result
    return [x, x];
  }
  // Duffing spring by harmonic balance: [(dk + ¾ k₃ A²)² + (cω)²] A² = Fa²
  const p = u => ((dk + 0.75 * v.k_3 * u) ** 2 + cw * cw) * u - Fa * Fa;
  if (!(Fa > 0)) return [0, 0];
  const us = N.logspace(1e-8, 1e4, 121).map(s => s * (Fa / v.k) ** 2), roots = [];
  for (let i = 1; i < us.length; i++) if (p(us[i - 1]) * p(us[i]) <= 0) roots.push(N.bisect(p, us[i - 1], us[i], 1e-12));
  if (!roots.length) return [0, 0];
  return [Math.sqrt(roots[roots.length - 1]), Math.sqrt(roots[0])];
}
function sdofTime(v, a, tEnd, nOut) {
  const m = sdofMass(v, a), w = 2 * Math.PI * v.f_d, Fc = a.force_excited ? v.F_0 : (a.viscous ? v.c * w * v.Y_b : 0), Fs = a.force_excited ? 0 : v.k * v.Y_b;
  const vs = 1e-3 * (Math.sqrt(v.k / m) * Math.abs(v.x_0) + Math.abs(v.v_0) + Math.hypot(Fc, Fs) / Math.sqrt(v.k * m)) + 1e-9;
  const f = (t, y) => [y[1], (Fc * Math.cos(w * t) + Fs * Math.sin(w * t) - v.k * y[0] - (a.linear ? 0 : v.k_3 * y[0] ** 3) - (a.viscous ? v.c * y[1] : v.mu_f * m * G0 * Math.tanh(y[1] / vs))) / m];
  const run = () => { const s = dopri((t, y, d) => { const q = f(t, y); d[0] = q[0]; d[1] = q[1]; }, [v.x_0, v.v_0], tEnd, nOut, { rtol: 1e-9, atol: 1e-13, maxSteps: 12000 }); return { t: s.t, y: [s.y.map(r => r[0]), s.y.map(r => r[1])] }; };
  return { m, w, Fc, Fs, f, run };
}
const SDOF_ON = { linear: true, viscous: true, force_excited: true, massless_spring: true };
const sdof = {
  id: 'mass-spring-damper',
  title: 'Mass–spring–damper: free and forced vibration',
  module: 2, klass: 'I', domains: ['mechanical', 'classical', 'waves'],
  keywords: ['mass-spring-damper', 'mass spring damper', 'spring-mass system', 'forced vibration', 'free vibration', 'resonance', 'damping ratio', 'natural frequency', 'transmissibility', 'vibration isolation', 'harmonic oscillator', 'damped oscillator', 'logarithmic decrement', 'frequency response', 'spring', 'damper', 'vibration'],
  summary: 'Single-degree-of-freedom oscillator: natural frequency, damping ratio, free decay, steady-state harmonic response, resonance curve and transmissibility, with nonlinear-spring, dry-friction and base-excitation options.',
  background: [
    'A mass on a spring with a viscous damper is the basic model of mechanical vibration. Left alone it oscillates at its damped natural frequency while the amplitude decays exponentially; the damping ratio compares the actual damping with the critical value at which oscillation just ceases.',
    'Under harmonic forcing the steady response has the forcing frequency, with an amplitude that peaks near the natural frequency — resonance — and a phase that lags from 0 to 180°. The same algebra gives the transmissibility, the fraction of force passed to the foundation or of base motion passed to the mass, which falls below one only above √2 times the natural frequency: the basis of vibration isolation.',
  ],
  phenomena: ['Elastic restoring force', 'Viscous energy dissipation', 'Resonance', 'Transient decay', 'Vibration isolation'],
  laws: ['newton2', 'hooke', 'energy'],
  refs: ['Den Hartog, J. P. (1956). Mechanical Vibrations, 4th ed., McGraw-Hill.', 'Thomson, W. T. & Dahleh, M. D. (1998). Theory of Vibration with Applications, 5th ed., Prentice Hall.', 'Rao, S. S. (2017). Mechanical Vibrations, 6th ed., Pearson.', 'Inman, D. J. (2014). Engineering Vibration, 4th ed., Pearson.', 'Nayfeh, A. H. & Mook, D. T. (1979). Nonlinear Oscillations. Wiley.'],
  inputs: [
    inp('m', 'Mass', 'kg', 10, { min: 0.01, max: 1e4, aliases: ['mass'] }),
    inp('k', 'Spring stiffness', 'N/m', 4000, { min: 1, max: 1e8, aliases: ['stiffness', 'spring constant', 'spring rate'] }),
    inp('c', 'Viscous damping coefficient', 'N s/m', 40, { min: 0.001, max: 1e5, aliases: ['damping coefficient', 'damper', 'damping'] }),
    inp('x_0', 'Initial displacement', 'mm', 10, { min: -200, max: 200, aliases: ['initial displacement', 'displacement'] }),
    inp('v_0', 'Initial velocity', 'm/s', 0, { min: -10, max: 10, aliases: ['initial velocity'] }),
    inp('F_0', 'Forcing amplitude', 'N', 50, { min: 0, max: 1e5, aliases: ['force amplitude', 'forcing amplitude', 'force'] }),
    inp('f_d', 'Forcing frequency', 'Hz', 2, { min: 0.01, max: 1000, aliases: ['forcing frequency', 'driving frequency', 'excitation frequency', 'frequency'] }),
    inp('Y_b', 'Base displacement amplitude (base excitation)', 'mm', 5, { min: 0, max: 200, aliases: ['base amplitude', 'base motion'] }),
    inp('k_3', 'Cubic stiffness (nonlinear spring)', 'N/m^3', 4e7, { min: 0, max: 1e12, aliases: ['cubic stiffness', 'duffing'] }),
    inp('mu_f', 'Coefficient of sliding friction (dry friction)', '1', 0.05, { min: 0, max: 1, aliases: ['friction coefficient', 'coulomb friction'] }),
    inp('m_s', 'Spring mass (when not negligible)', 'kg', 1, { min: 0, max: 1e3, aliases: ['spring mass'] }),
  ],
  assumptions: [
    asm('linear', 'The spring is linear (Hooke\'s law).', { why: 'Small deflections', alt: 'A hardening Duffing spring with an added cubic term; the resonance curve bends and can be multi-valued.' }),
    asm('viscous', 'Damping is viscous: force proportional to velocity.', { why: 'Fluid dampers; gives linear equations', alt: 'Dry (Coulomb) friction of constant magnitude opposing the motion.' }),
    asm('force_excited', 'The excitation is a harmonic force applied to the mass.', { why: 'Rotating unbalance, actuator', alt: 'The support moves harmonically (base excitation), as for a vehicle on a rough road or an instrument on a vibrating floor.' }),
    asm('massless_spring', 'The mass of the spring is negligible.', { why: 'Spring much lighter than the mass', alt: 'Rayleigh\'s correction: one third of the spring mass is added to the moving mass.' }),
  ],
  symbols: { x: ['Displacement of the mass', 'm'], t: ['Time', 's'], omega: ['Forcing angular frequency', '1/s'], omega_n: ['Undamped natural angular frequency', '1/s'], omega_d: ['Damped natural angular frequency', '1/s'], zeta: ['Damping ratio', '1'], X: ['Steady-state displacement amplitude', 'm'], TR: ['Transmissibility', '1'], y_b: ['Base displacement', 'm'], m_eff: ['Effective moving mass', 'kg'], delta_l: ['Logarithmic decrement', '1'], g: ['Standard gravity', 'm/s^2'] },
  equations: a => {
    const M = a.massless_spring ? 'm' : 'm_eff', damp = a.viscous ? 'c*d(x,t)' : `mu_f*${M}*g*sign(d(x,t))`, spring = a.linear ? 'k*x' : 'k*x + k_3*x^3';
    return [
      ...(a.massless_spring ? [] : [eq('meff', 'Effective mass', 'm_eff', 'm + m_s/3', { kind: 'derived', origin: 'Rayleigh\'s energy method for a uniform spring' })]),
      eq('mom', 'Equation of motion', `${M}*d2(x,t) + ${damp} + ${spring}`, a.force_excited ? 'F_0*cos(omega*t)' : `k*y_b${a.viscous ? ' + c*d(y_b,t)' : ''}`, { kind: 'law', origin: 'Newton\'s second law for the mass', needs: ['linear', 'viscous'].filter(q => a[q]) }),
      ...(a.force_excited ? [] : [eq('base', 'Base motion', 'y_b', 'Y_b*sin(omega*t)', { kind: 'boundary', origin: 'Prescribed harmonic support motion' })]),
      eq('om', 'Forcing angular frequency', 'omega', '2*pi*f_d', { kind: 'definition' }),
      eq('wn', 'Natural frequency', 'omega_n', `sqrt(k/${M})`, { kind: 'derived', origin: 'Undamped free vibration' }),
      ...(a.viscous ? [
        eq('zeta', 'Damping ratio', 'zeta', `c/(2*sqrt(k*${M}))`, { kind: 'definition', origin: 'Ratio to critical damping' }),
        eq('wd', 'Damped natural frequency', 'omega_d', 'omega_n*sqrt(1 - zeta^2)', { kind: 'derived', origin: 'Roots of the characteristic equation' }),
        eq('dec', 'Logarithmic decrement', 'delta_l', '2*pi*zeta/sqrt(1 - zeta^2)', { kind: 'derived', origin: 'Ratio of successive peaks of the free decay' }),
      ] : []),
      ...(a.linear && a.viscous ? [
        eq('amp', 'Steady-state amplitude', 'X', a.force_excited ? `F_0/sqrt((k - ${M}*omega^2)^2 + (c*omega)^2)` : `Y_b*sqrt((k^2 + (c*omega)^2)/((k - ${M}*omega^2)^2 + (c*omega)^2))`, { kind: 'derived', origin: 'Particular solution of the linear equation', needs: ['linear', 'viscous'] }),
        eq('tr', 'Transmissibility', 'TR', `sqrt((k^2 + (c*omega)^2)/((k - ${M}*omega^2)^2 + (c*omega)^2))`, { kind: 'derived', origin: 'Force through spring and damper over applied force; equal to the base-motion ratio', needs: ['linear', 'viscous'] }),
      ] : []),
      ...(a.linear ? [] : [eq('hb', 'Harmonic-balance amplitude relation', `((k - ${M}*omega^2 + 0.75*k_3*X^2)^2${a.viscous ? ' + (c*omega)^2' : ''})*X^2`, a.force_excited ? 'F_0^2' : `Y_b^2*(k^2${a.viscous ? ' + (c*omega)^2' : ''})`, { kind: 'derived', origin: 'First-harmonic balance for the Duffing oscillator (Nayfeh & Mook 1979)' })]),
    ];
  },
  derivation: a => [
    { text: 'Apply Newton\'s second law to the mass. The spring pulls it back in proportion to displacement and the damper resists in proportion to velocity.', tex: a.force_excited ? 'm\\ddot x + c\\dot x + kx = F_0\\cos\\omega t' : 'm\\ddot x + c(\\dot x-\\dot y) + k(x-y) = 0,\\qquad y = Y\\sin\\omega t' },
    { text: 'Dividing by the mass introduces the two parameters that characterise the system.', tex: '\\ddot x + 2\\zeta\\omega_n\\dot x + \\omega_n^2 x = \\frac{F(t)}{m},\\qquad \\omega_n = \\sqrt{k/m},\\quad \\zeta = \\frac{c}{2\\sqrt{km}}' },
    { text: 'With no forcing and ζ < 1 the solution is a decaying oscillation; successive peaks fall in a fixed ratio whose logarithm is the logarithmic decrement.', tex: 'x = e^{-\\zeta\\omega_n t}\\left(A\\cos\\omega_d t + B\\sin\\omega_d t\\right),\\qquad \\omega_d = \\omega_n\\sqrt{1-\\zeta^2},\\qquad \\delta = \\frac{2\\pi\\zeta}{\\sqrt{1-\\zeta^2}}' },
    { text: 'For harmonic forcing, trying a response at the forcing frequency gives the steady-state amplitude and phase lag in terms of the frequency ratio r = ω/ω_n.', tex: '\\frac{X}{F_0/k} = \\frac{1}{\\sqrt{(1-r^2)^2 + (2\\zeta r)^2}},\\qquad \\tan\\phi = \\frac{2\\zeta r}{1-r^2}' },
    { text: 'The force passed to the support through spring and damper, relative to the applied force, is the transmissibility. It equals 1 at r = √2 whatever the damping and falls below 1 only beyond that.', tex: 'TR = \\sqrt{\\frac{1+(2\\zeta r)^2}{(1-r^2)^2+(2\\zeta r)^2}}' },
    ...(a.linear ? [] : [{ text: 'With a cubic spring term the response is no longer exactly sinusoidal. Keeping the fundamental harmonic (harmonic balance) replaces the stiffness by an amplitude-dependent value, which bends the resonance peak toward higher frequency.', tex: '\\left[\\left(k - m\\omega^2 + \\tfrac34 k_3X^2\\right)^2 + (c\\omega)^2\\right]X^2 = F_0^2' }]),
    ...(a.viscous ? [] : [{ text: 'With dry friction of constant magnitude μN the free decay is linear in time, losing 4μN/k per cycle, and equating the energy lost per cycle to that of an equivalent viscous damper gives the forced amplitude.', tex: 'X = \\frac{F_0}{k}\\,\\frac{\\sqrt{1-\\left(\\dfrac{4\\mu N}{\\pi F_0}\\right)^2}}{|1-r^2|}' }]),
  ],
  solve(v, a) {
    const m = sdofMass(v, a), wn = Math.sqrt(v.k / m), z = v.c / (2 * Math.sqrt(v.k * m)), w = 2 * Math.PI * v.f_d, r = w / wn, Tn = 2 * Math.PI / wn;
    const forced = a.force_excited ? v.F_0 > 0 : v.Y_b > 0, exact = a.linear && a.viscous;
    let tEnd = forced ? N.clamp(6 * 2 * Math.PI / w, 12 * Tn, 60 * Tn) : 12 * Tn;
    if (exact && z > 1) tEnd = Math.max(tEnd, 5 * v.c / v.k);
    const tm = sdofTime(v, a, tEnd, 1201), cf = sdofExact(m, v.c, v.k, tm.Fc, tm.Fs, w, v.x_0, v.v_0);
    let tt, xx; const warnings = [];
    if (exact) { tt = N.linspace(0, tEnd, 1201); xx = tt.map(cf.x); }
    else { const s = tm.run(); tt = s.t; xx = s.y[0]; if (tt.length < 1201) warnings.push('The time integration stopped early at its step limit; the response is shown only up to that time.'); }
    const X = sdofAmp(v, a, w), dk = v.k - m * w * w, cw = a.viscous ? v.c * w : 0, input = a.force_excited ? v.F_0 / v.k : v.Y_b;
    const TR = Math.sqrt((v.k ** 2 + cw * cw) / (dk * dk + cw * cw || 1e-300)), phase = Math.atan2(cw, dk) - (a.force_excited ? 0 : Math.atan2(cw, v.k));
    const under = z < 1, wd = under ? wn * Math.sqrt(1 - z * z) : NaN, dec = under ? 2 * Math.PI * z / Math.sqrt(1 - z * z) : NaN, peak = z < Math.SQRT1_2;
    const na = 'Not oscillatory: damping is at or above critical', nv = 'Not defined without viscous damping';
    const fr = N.linspace(0.05, 3, 120), amps = fr.map(q => sdofAmp(v, a, q * wn));
    const lin = q => Math.sqrt((1 + (2 * z * q) ** 2) / ((1 - q * q) ** 2 + (2 * z * q) ** 2));
    if (exact && forced && Math.abs(r - 1) < 0.1 && z < 0.05) warnings.push('The forcing frequency is within 10 % of the natural frequency of a lightly damped system: the response is large and sensitive to small changes in stiffness, mass or damping.');
    if (!a.linear && X[0] > 1.05 * X[1]) warnings.push('At this forcing frequency the nonlinear spring admits more than one steady amplitude; which is reached depends on the history (jump phenomenon).');
    if (!a.viscous && a.force_excited && v.F_0 <= 4 * v.mu_f * m * G0 / Math.PI && v.F_0 > 0) warnings.push('The forcing amplitude is too small to overcome dry friction continuously; the equivalent-damping estimate gives no sustained motion.');
    if (!a.viscous) warnings.push('Dry friction is regularised with a narrow hyperbolic-tangent transition through zero velocity; sticking is represented approximately.');
    if (!a.viscous && !a.linear) warnings.push('The frequency-response curve for the nonlinear spring neglects dry friction.');
    return {
      scalars: [
        scalar('omega_n', 'Undamped natural angular frequency', wn, '1/s'), scalar('f_n', 'Undamped natural frequency', wn / (2 * Math.PI), 'Hz'),
        scalar('zeta', 'Damping ratio', a.viscous ? z : NaN, '1', { text: a.viscous ? undefined : nv }), scalar('c_cr', 'Critical damping coefficient', 2 * Math.sqrt(v.k * m), 'N s/m'),
        scalar('omega_d', 'Damped natural angular frequency', a.viscous ? wd : NaN, '1/s', { text: !a.viscous ? nv : under ? undefined : na }),
        scalar('delta_l', 'Logarithmic decrement', a.viscous ? dec : NaN, '1', { text: !a.viscous ? nv : under ? undefined : na }),
        scalar('Q', 'Quality factor', a.viscous ? 1 / (2 * z) : NaN, '1', { text: a.viscous ? undefined : nv }),
        scalar('t_s', 'Settling time to 2 % (envelope)', a.viscous ? 4 / (z * wn) : NaN, 's', { text: a.viscous ? undefined : nv }),
        scalar('r', 'Frequency ratio ω/ω_n', r, '1'), scalar('x_st', a.force_excited ? 'Static deflection F₀/k' : 'Base amplitude', input, 'm', { show: 'mm' }),
        scalar('X', 'Steady-state displacement amplitude', X[0], 'm', { show: 'mm' }), scalar('M_f', a.force_excited ? 'Dynamic magnification X/(F₀/k)' : 'Displacement ratio X/Y', input > 0 ? X[0] / input : 0, '1'),
        scalar('phi', a.force_excited ? 'Phase lag of the response behind the force (linear viscous value)' : 'Phase lag of the mass behind the base motion (linear viscous value)', phase, 'rad', { show: 'deg' }),
        scalar('TR', 'Transmissibility (linear viscous value)', TR, '1'), scalar('F_tr', a.force_excited ? 'Force amplitude transmitted to the support' : 'Force amplitude in the mount', a.force_excited ? TR * v.F_0 : m * w * w * X[0], 'N'),
        scalar('f_res', 'Frequency of greatest displacement response', a.viscous && peak ? wn * Math.sqrt(1 - 2 * z * z) / (2 * Math.PI) : NaN, 'Hz', { text: !a.viscous ? nv : peak ? undefined : 'No resonance peak: damping ratio above 0.707' }),
        scalar('M_max', 'Peak dynamic magnification', a.viscous && peak ? 1 / (2 * z * Math.sqrt(1 - z * z)) : NaN, '1', { text: !a.viscous ? nv : peak ? undefined : 'No resonance peak: damping ratio above 0.707' }),
        scalar('x_max', 'Largest displacement in the simulated response', N.maxOf(xx.map(Math.abs)), 'm', { show: 'mm' }),
      ],
      series: [
        line('response', 'Displacement against time', 'Time', 's', tt, [{ label: 'Displacement', data: xx.map(x => x * 1000) }, ...(exact ? [{ label: 'Steady-state part', data: tt.map(t => cf.steady(t) * 1000), dash: true }] : [])], 'Displacement', 'mm'),
        line('resonance', 'Steady-state amplitude against forcing frequency', 'Forcing frequency', 'Hz', fr.map(q => q * wn / (2 * Math.PI)), [{ label: a.linear ? 'Amplitude' : 'Amplitude, upper branch', data: amps.map(q => q[0] * 1000) }, ...(a.linear ? [] : [{ label: 'Amplitude, lower branch', data: amps.map(q => q[1] * 1000), dash: true }])], 'Amplitude', 'mm'),
        line('transmissibility', 'Transmissibility against frequency ratio', 'Frequency ratio ω/ω_n', '–', fr, [{ label: `ζ = ${lab(z)}`, data: fr.map(lin) }, { label: 'Unity', data: fr.map(() => 1), dash: true }], 'Transmissibility', '–', { logy: true, note: 'Isolation (TR < 1) requires a frequency ratio above √2.' }),
        line('phase', 'Phase lag against frequency ratio', 'Frequency ratio ω/ω_n', '–', fr, [{ label: 'Phase lag', data: fr.map(q => (Math.atan2(2 * z * q, 1 - q * q) - (a.force_excited ? 0 : Math.atan2(2 * z * q, 1))) / DEG) }], 'Phase lag', 'deg'),
      ],
      checks: [
        check('Steady-state force balance', exact && forced ? (() => { const Fa = Math.hypot(tm.Fc, tm.Fs); return (X[0] * Math.sqrt(dk * dk + cw * cw) - Fa) / Fa; })() : 0, 1e-10, 'Amplitude times dynamic stiffness against the forcing amplitude'),
        check('Initial conditions reproduced', exact ? (cf.x(0) - v.x_0) / (Math.abs(v.x_0) + cf.amp + 1e-12) : (xx[0] - v.x_0) / (Math.abs(v.x_0) + 1e-12), 1e-10, 'Closed-form solution evaluated at t = 0'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const m = v.m, wn = Math.sqrt(v.k / m), z = v.c / (2 * Math.sqrt(v.k * m)), w = 2 * Math.PI * v.f_d, out = [];
    const tEnd = 12 * 2 * Math.PI / wn, tm = sdofTime(v, SDOF_ON, tEnd, 241), num = tm.run(), cf = sdofExact(m, v.c, v.k, tm.Fc, tm.Fs, w, v.x_0, v.v_0);
    const dev = N.maxOf(num.t.map((t, i) => Math.abs(num.y[0][i] - cf.x(t)))), scale = N.maxOf(num.t.map(t => Math.abs(cf.x(t)))) || 1;
    out.push(bench('RK45 integration vs closed-form response (1 = identical)', 1 + dev / scale, 1, 'Exact solution of the linear equation of motion', 1e-7));
    if (z < 1) {
      const Td = 2 * Math.PI / (wn * Math.sqrt(1 - z * z)), fr = N.rk45((t, y) => [y[1], (-v.c * y[1] - v.k * y[0]) / m], [1, 0], 0, Td, 2, { rtol: 1e-11, atol: 1e-14 }).final[0];
      out.push(bench('Free decay over one damped period vs logarithmic decrement', fr, Math.exp(-2 * Math.PI * z / Math.sqrt(1 - z * z)), 'x(T_d)/x(0) = e^(−δ)', 1e-8));
    }
    if (z < 0.7) {
      const mag = q => 1 / Math.sqrt((1 - q * q) ** 2 + (2 * z * q) ** 2), qp = N.golden(q => -mag(q), 0.01, 2, 1e-10);
      out.push(bench('Peak magnification located numerically vs closed form', mag(qp), 1 / (2 * z * Math.sqrt(1 - z * z)), 'M_max = 1/(2ζ√(1−ζ²))', 1e-9));
    }
    out.push(bench('Transmissibility at a frequency ratio of √2', val(sdof.solve({ ...v, f_d: Math.SQRT2 * wn / (2 * Math.PI) }, SDOF_ON), 'TR'), 1, 'TR = 1 at r = √2 for any damping', 1e-10));
    out.push(bench('Phase lag at the natural frequency', val(sdof.solve({ ...v, f_d: wn / (2 * Math.PI) }, SDOF_ON), 'phi'), Math.PI / 2, 'Response lags the force by 90° at ω = ω_n', 1e-9));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const zig = N.linspace(0, 1, 13).map((u, i) => [(120 + 150 * u).toFixed(1), (150 + (i === 0 || i === 12 ? 0 : (i % 2 ? -12 : 12))).toFixed(1)]);
    return svg(`
      ${S.path('M110 80 L110 280', 'd-ground')} ${S.path('M110 290 L560 290', 'd-ground')}
      ${S.poly(zig, 'd-line')} ${S.text(195, 124, `k = ${lab(v.k, 'N/m')}`)}
      ${a.viscous ? S.line(120, 220, 180, 220) + S.rect(180, 204, 50, 32, 'd-body', 2) + S.line(205, 220, 270, 220) + S.line(205, 208, 205, 232) + S.text(195, 262, `c = ${lab(v.c, 'N s/m')}`) : S.text(195, 262, `dry friction μ = ${lab(v.mu_f)}`)}
      ${S.rect(270, 110, 150, 150, 'd-body')} ${S.text(345, 190, `m = ${lab(sdofMass(v, a), 'kg')}`)}
      ${S.circle(300, 275, 13, 'd-line')} ${S.circle(390, 275, 13, 'd-line')}
      ${a.force_excited ? S.arrow(420, 185, 520, 185) + S.text(470, 172, `F₀ cos ωt, F₀ = ${lab(v.F_0, 'N')}`) : S.arrow(60, 60, 100, 60) + S.text(110, 50, `base motion Y sin ωt, Y = ${lab(v.Y_b * 1000, 'mm')}`, 'd-text', 'start')}
      ${S.arrow(300, 90, 380, 90)} ${S.text(340, 80, 'x')}
      ${S.text(320, 340, `f_n = ${lab(Math.sqrt(v.k / sdofMass(v, a)) / (2 * Math.PI), 'Hz')}    ζ = ${lab(v.c / (2 * Math.sqrt(v.k * sdofMass(v, a))))}    forcing at ${lab(v.f_d, 'Hz')}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Identify the stiffness and damping of a single-degree-of-freedom system from its free decay, then verify the predicted resonance curve and transmissibility by swept-sine testing.',
    apparatus: ['Mass on a linear guide or air track with a coil spring', 'Adjustable viscous damper (dashpot) or eddy-current damper', 'Electrodynamic shaker with power amplifier and signal generator', 'Rigid base with force transducer between shaker and mass or under the mount'],
    instruments: [{ name: 'Accelerometer on the mass', measures: 'Response acceleration', range: '±50 g', resolution: '0.5 %, 10 kHz bandwidth' }, { name: 'Laser displacement sensor', measures: 'Displacement', range: '±25 mm', resolution: '10 µm' }, { name: 'Piezoelectric force transducer', measures: 'Applied and transmitted force', range: '±500 N', resolution: '0.1 N' }, { name: 'Dynamic signal analyser', measures: 'Frequency-response function and phase', range: '0.1–1000 Hz', resolution: '0.01 Hz' }],
    procedure: ['Displace the mass and release; record the free decay and extract the damped period and logarithmic decrement.', 'Compute stiffness from the natural frequency and the measured mass, and damping from the decrement.', 'Drive with a slow sine sweep through resonance, recording amplitude and phase.', 'Measure transmitted force for the transmissibility curve and locate the cross-over at √2 times the natural frequency.'],
    controls: ['Static load–deflection test for an independent stiffness value', 'Sweep up and down in frequency to detect nonlinearity (jump or hysteresis)', 'Repeat at half the forcing level: a linear system gives the same normalised curve'],
    signatures: ['Successive free-decay peaks in constant ratio (straight line on a logarithmic plot)', 'Phase lag of 90° at the natural frequency', 'Transmissibility of 1 at a frequency ratio of √2 regardless of damping'],
    safety: ['Limit shaker stroke and force to protect the fixture at resonance', 'Guard moving parts and secure all fasteners', 'Hearing protection during high-level sweeps'],
  },
  falsify: ['Free-decay peaks that do not fall in a constant ratio for a system claimed to be linear and viscously damped.', 'A phase lag at the measured natural frequency differing from 90° by more than the measurement uncertainty.', 'A normalised resonance curve that changes shape with forcing level.'],
  alternatives: [{ name: 'Hysteretic (structural) damping', text: 'Energy loss per cycle independent of frequency, represented by a complex stiffness k(1 + iη).' }, { name: 'Multi-degree-of-freedom and modal models', text: 'Real structures have many modes; each behaves as a single-degree-of-freedom oscillator near its own resonance.' }, { name: 'Den Hartog\'s exact dry-friction solution', text: 'Gives the forced response with Coulomb friction including stick–slip, where the equivalent-viscous estimate fails.' }],
  hazards: [{ hazard: 'Resonant failure', cause: 'Sustained excitation near the natural frequency', mitigation: 'Detune by changing stiffness or mass, add damping, or pass through resonance quickly' }, { hazard: 'Fatigue', cause: 'Large cyclic stress in the spring or mounts', mitigation: 'Check stress amplitude against the endurance limit' }, { hazard: 'Ineffective isolation', cause: 'Operating below √2 times the mount natural frequency, where the mount amplifies', mitigation: 'Select softer mounts or raise the operating speed' }],
  standards: ['ISO 2041 (mechanical vibration, shock and condition monitoring — vocabulary)', 'ISO 10846 (acoustics and vibration — laboratory measurement of vibro-acoustic transfer properties of resilient elements)', 'ISO 20816-1 (mechanical vibration — measurement and evaluation of machine vibration)'],
  limits: 'One translational degree of freedom with lumped mass, stiffness and damping. The closed forms require a linear spring and viscous damping. The Duffing response uses first-harmonic balance and ignores sub- and super-harmonics; the dry-friction amplitude uses the equivalent-viscous approximation, valid when motion is continuous.',
  numerics: { method: 'Closed-form solution for the linear viscous case; adaptive RK45 for the nonlinear-spring and dry-friction options; bisection for the harmonic-balance roots', order: 5 },
  optimise: { objective: 'TR', sense: 'min', vars: ['k'], note: 'A softer mount lowers the natural frequency and improves isolation, at the cost of larger static deflection.' },
  inverse: { series: 'response', fit: ['k', 'c'] },
  extensions: ['Two-degree-of-freedom tuned vibration absorber', 'Random and shock excitation (response spectra)', 'Rotating unbalance and whirl of shafts'],
};

// ------------------------------------------------------------------ 12. two-body collision
function collide(v, a) {
  const wall = !a.free_target, m1 = v.m_1, m2 = v.m_2, mred = wall ? m1 : m1 * m2 / (m1 + m2), b = a.head_on ? 0 : v.b, urel = v.u_1 - v.u_2;
  const n = [(urel >= 0 ? 1 : -1) * Math.sqrt(1 - b * b), b];          // unit vector from body 1 to body 2 at contact
  const vn = urel * n[0];                                               // closing speed along the line of centres
  const e = a.fixed_e ? v.e_r : Math.min(1, v.e_r * Math.pow(v.v_ref / Math.max(vn, 1e-12), 0.25));
  const J = (1 + e) * mred * vn;
  const v1 = [v.u_1 - J / m1 * n[0], -J / m1 * n[1]], v2 = wall ? [v.u_2, 0] : [v.u_2 + J / m2 * n[0], J / m2 * n[1]];
  const dE = 0.5 * mred * (1 - e * e) * vn * vn;
  // kinetic energy before and after, in the laboratory frame (free target) or in the frame of the wall
  const ke0 = wall ? 0.5 * m1 * urel ** 2 : 0.5 * m1 * v.u_1 ** 2 + 0.5 * m2 * v.u_2 ** 2;
  const ke1 = wall ? 0.5 * m1 * ((v1[0] - v.u_2) ** 2 + v1[1] ** 2) : 0.5 * m1 * (v1[0] ** 2 + v1[1] ** 2) + 0.5 * m2 * (v2[0] ** 2 + v2[1] ** 2);
  return { wall, m1, m2, mred, b, urel, n, vn, e, J, v1, v2, dE, ke0, ke1 };
}
const contactZeta = e => { const l = Math.log(Math.max(e, 1e-3)); return -l / Math.sqrt(Math.PI ** 2 + l * l); };
const collision = {
  id: 'collision-1d-2d',
  title: 'Two-body collision with restitution',
  module: [1, 2], klass: 'I', domains: ['classical', 'mechanical'],
  keywords: ['coefficient of restitution', 'elastic collision', 'inelastic collision', 'collision', 'conservation of momentum', 'impact', 'head-on collision', 'oblique collision', 'billiard', 'impulse', 'bounce', 'two-body collision', 'momentum', 'kinetic energy loss'],
  summary: 'Velocities after a head-on or oblique collision of two smooth bodies from conservation of momentum and Newton\'s law of restitution, with the impulse, the energy lost and an optional finite-duration contact model.',
  background: [
    'During a collision the forces between the bodies are internal, so the total momentum is unchanged whatever happens at the contact. One further piece of information fixes the outcome: Newton\'s experimental law that the relative speed of separation along the line of centres is a fixed fraction — the coefficient of restitution — of the relative speed of approach.',
    'A coefficient of 1 conserves kinetic energy (elastic collision); 0 means the bodies do not separate (perfectly inelastic) and the largest possible amount of kinetic energy, that of the relative motion, is dissipated. For smooth bodies meeting obliquely only the velocity components along the line of centres change.',
  ],
  phenomena: ['Impulsive contact force', 'Momentum exchange', 'Dissipation in deformation', 'Deflection in oblique impact'],
  laws: ['momentum', 'newton3', 'newton2', 'energy'],
  refs: ['Newton, I. (1687). Philosophiæ Naturalis Principia Mathematica, Scholium to the Laws of Motion. Royal Society, London.', 'Goldsmith, W. (1960). Impact: The Theory and Physical Behaviour of Colliding Solids. Edward Arnold.', 'Johnson, K. L. (1985). Contact Mechanics. Cambridge University Press.', 'Stronge, W. J. (2000). Impact Mechanics. Cambridge University Press.', 'Cross, R. (1999). The bounce of a ball. American Journal of Physics 67, 222–227.'],
  inputs: [
    inp('m_1', 'Mass of body 1', 'kg', 1, { min: 0.001, max: 1e4, aliases: ['first mass', 'mass of body 1', 'projectile mass'] }),
    inp('m_2', 'Mass of body 2', 'kg', 2, { min: 0.001, max: 1e4, aliases: ['second mass', 'mass of body 2', 'target mass'] }),
    inp('u_1', 'Velocity of body 1 before impact', 'm/s', 3, { min: -100, max: 100, aliases: ['first velocity', 'velocity of body 1', 'initial velocity', 'approach speed'] }),
    inp('u_2', 'Velocity of body 2 before impact', 'm/s', -1, { min: -100, max: 100, aliases: ['second velocity', 'velocity of body 2', 'target velocity'] }),
    inp('e_r', 'Coefficient of restitution', '1', 0.8, { min: 0, max: 1, kind: 'fluid', aliases: ['coefficient of restitution', 'restitution'], src: 'Hard plastic or steel on steel at low speed is 0.8–0.95; a tennis ball on a hard court about 0.75' }),
    inp('b', 'Impact parameter as a fraction of the sum of radii (oblique impact)', '1', 0.5, { min: 0, max: 0.99, kind: 'geometry', aliases: ['impact parameter', 'offset'] }),
    inp('R_1', 'Radius of body 1', 'm', 0.05, { min: 0.001, max: 5, kind: 'geometry', aliases: ['first radius'] }),
    inp('R_2', 'Radius of body 2', 'm', 0.06, { min: 0.001, max: 5, kind: 'geometry', aliases: ['second radius'] }),
    inp('v_ref', 'Impact speed at which the restitution coefficient was measured', 'm/s', 1, { min: 0.01, max: 100, aliases: ['reference speed'] }),
    inp('k_c', 'Contact stiffness (finite-duration contact)', 'N/m', 1e6, { min: 100, max: 1e10, aliases: ['contact stiffness'] }),
  ],
  assumptions: [
    asm('head_on', 'The impact is central: the velocities lie along the line joining the centres.', { why: 'One-dimensional collision', alt: 'Oblique impact of smooth discs with the stated impact parameter; only the components along the line of centres change.' }),
    asm('fixed_e', 'The coefficient of restitution is a constant.', { why: 'Narrow range of impact speeds', alt: 'It falls with impact speed as v^(−1/4), as for impacts that cause plastic deformation (Johnson 1985), capped at 1.' }),
    asm('free_target', 'Both bodies are free to move.', { why: 'Isolated pair', alt: 'Body 2 is an immovable wall (infinite mass) moving at its stated velocity.' }),
    asm('instantaneous', 'The impact is instantaneous: only the net impulse matters.', { why: 'Contact time far shorter than any other time scale', alt: 'The contact is a linear spring and dashpot, giving a finite contact time and peak force for the same restitution.' }),
  ],
  symbols: { v_n: ['Closing speed along the line of centres', 'm/s'], u_1n: ['Normal velocity of body 1 before impact', 'm/s'], u_2n: ['Normal velocity of body 2 before impact', 'm/s'], v_1n: ['Normal velocity of body 1 after impact', 'm/s'], v_2n: ['Normal velocity of body 2 after impact', 'm/s'], u_1t: ['Tangential velocity of body 1 before impact', 'm/s'], v_1t: ['Tangential velocity of body 1 after impact', 'm/s'], m_red: ['Reduced mass', 'kg'], J: ['Impulse', 'N s'], dE: ['Kinetic energy dissipated', 'J'], e_eff: ['Effective coefficient of restitution', '1'], delta_c: ['Contact compression', 'm'], t: ['Time', 's'], c_c: ['Contact damping coefficient', 'N s/m'], zeta_c: ['Contact damping ratio', '1'], t_c: ['Contact duration', 's'] },
  equations: a => {
    const E = a.fixed_e ? 'e_r' : 'e_eff';
    return [
      eq('vn', 'Closing speed', 'v_n', a.head_on ? 'abs(u_1 - u_2)' : 'abs(u_1 - u_2)*sqrt(1 - b^2)', { kind: 'definition', origin: 'Component of the relative velocity along the line of centres' }),
      ...(a.fixed_e ? [] : [eq('e', 'Speed-dependent restitution', 'e_eff', 'min(1, e_r*(v_ref/v_n)^0.25)', { kind: 'empirical', origin: 'Johnson (1985): fully plastic impact, e ∝ v^(−1/4)' })]),
      a.free_target ? eq('mom', 'Conservation of momentum', 'm_1*v_1n + m_2*v_2n', 'm_1*u_1n + m_2*u_2n', { kind: 'law', origin: 'Newton\'s second and third laws: no external impulse', needs: ['free_target'] })
        : eq('mom', 'Immovable wall', 'v_2n', 'u_2n', { kind: 'boundary', origin: 'Infinite mass: the wall velocity is unchanged' }),
      eq('rest', 'Law of restitution', 'v_2n - v_1n', `${E}*(u_1n - u_2n)`, { kind: 'empirical', origin: 'Newton\'s experimental law of impact' }),
      a.free_target ? eq('mred', 'Reduced mass', 'm_red', 'm_1*m_2/(m_1 + m_2)', { kind: 'definition' }) : eq('mred', 'Reduced mass', 'm_red', 'm_1', { kind: 'definition', origin: 'Limit of infinite target mass' }),
      eq('imp', 'Impulse', 'J', `(1 + ${E})*m_red*v_n`, { kind: 'derived', origin: 'Momentum change of either body' }),
      eq('loss', 'Kinetic energy dissipated', 'dE', `0.5*m_red*(1 - ${E}^2)*v_n^2`, { kind: 'derived', origin: 'Energy of relative motion before and after' }),
      ...(a.head_on ? [] : [eq('tan', 'Tangential velocity unchanged', 'v_1t', 'u_1t', { kind: 'law', origin: 'Smooth surfaces transmit no tangential impulse' })]),
      ...(a.instantaneous ? [] : [
        eq('contact', 'Contact dynamics', 'm_red*d2(delta_c,t)', '-c_c*d(delta_c,t) - k_c*delta_c', { kind: 'closure', origin: 'Linear spring–dashpot contact model' }),
        eq('zc', 'Contact damping ratio', 'zeta_c', `-ln(max(${E}, 0.001))/sqrt(pi^2 + ln(max(${E}, 0.001))^2)`, { kind: 'derived', origin: 'Half-cycle of a damped oscillator reproducing the restitution coefficient', note: 'A linear spring and dashpot cannot give exactly zero restitution, so the coefficient is floored at 0.001.' }),
        eq('cc', 'Contact damping coefficient', 'c_c', '2*zeta_c*sqrt(k_c*m_red)', { kind: 'definition' }),
        eq('tc', 'Contact duration', 't_c', 'pi/sqrt(k_c/m_red*(1 - zeta_c^2))', { kind: 'derived', origin: 'Half the damped period' }),
      ]),
    ];
  },
  derivation: a => [
    { text: 'The contact forces on the two bodies are equal and opposite at every instant, so their impulses cancel and the total momentum is conserved.', tex: 'm_1\\mathbf v_1 + m_2\\mathbf v_2 = m_1\\mathbf u_1 + m_2\\mathbf u_2' },
    { text: 'Newton\'s law of restitution relates the normal relative velocities before and after.', tex: '(\\mathbf v_2-\\mathbf v_1)\\cdot\\mathbf n = -e\\,(\\mathbf u_2-\\mathbf u_1)\\cdot\\mathbf n' },
    { text: 'Solving the two equations gives the impulse along the line of centres in terms of the reduced mass and the closing speed.', tex: 'J = (1+e)\\,\\mu\\,v_n,\\qquad \\mu = \\frac{m_1m_2}{m_1+m_2},\\qquad \\mathbf v_1 = \\mathbf u_1 - \\frac{J}{m_1}\\mathbf n,\\quad \\mathbf v_2 = \\mathbf u_2 + \\frac{J}{m_2}\\mathbf n' },
    { text: 'The kinetic energy of the centre-of-mass motion cannot change; only the energy of relative motion along the normal is reduced, by the factor e².', tex: '\\Delta E = \\tfrac12\\,\\mu\\,(1-e^2)\\,v_n^2' },
    ...(a.head_on ? [] : [{ text: 'For smooth discs with impact parameter b (as a fraction of the sum of radii) the line of centres makes an angle arcsin b with the approach direction, so the closing speed is reduced accordingly.', tex: 'v_n = |u_1-u_2|\\sqrt{1-b^2}' }]),
    ...(a.instantaneous ? [] : [{ text: 'Modelling the contact as a spring and dashpot, the compression follows half a cycle of a damped oscillation. The ratio of rebound to approach speed fixes the damping ratio, and the half-period is the contact time.', tex: 'e = \\exp\\!\\left(-\\frac{\\pi\\zeta}{\\sqrt{1-\\zeta^2}}\\right),\\qquad t_c = \\frac{\\pi}{\\omega_n\\sqrt{1-\\zeta^2}},\\quad \\omega_n = \\sqrt{k_c/\\mu}' }]),
  ],
  solve(v, a) {
    const c = collide(v, a), sp = p => Math.hypot(p[0], p[1]), warnings = [];
    const vcm = c.wall ? v.u_2 : (c.m1 * v.u_1 + c.m2 * v.u_2) / (c.m1 + c.m2);
    const p0 = c.m1 * v.u_1 + c.m2 * v.u_2, p1x = c.m1 * c.v1[0] + c.m2 * c.v2[0], p1y = c.m1 * c.v1[1] + c.m2 * c.v2[1];
    const pscale = c.m1 * Math.abs(v.u_1) + c.m2 * Math.abs(v.u_2) + 1e-12;
    if (c.vn === 0) warnings.push('The bodies have the same velocity and never meet: all outputs equal the inputs.');
    if (!a.fixed_e && c.e >= 1) warnings.push('At this low impact speed the speed-dependent restitution has reached its cap of 1 (elastic).');
    // finite-duration contact
    const z = contactZeta(c.e), wn = Math.sqrt(v.k_c / c.mred), wd = wn * Math.sqrt(1 - z * z), tc = Math.PI / wd, cc = 2 * z * Math.sqrt(v.k_c * c.mred);
    const tcs = N.linspace(0, tc, 121), dl = tcs.map(t => c.vn / wd * Math.exp(-z * wn * t) * Math.sin(wd * t)), dv = tcs.map(t => c.vn * Math.exp(-z * wn * t) * (Math.cos(wd * t) - z * wn / wd * Math.sin(wd * t)));
    const Fc = tcs.map((_, i) => v.k_c * dl[i] + cc * dv[i]), fin = !a.instantaneous, nd = 'Not defined for an instantaneous impact';
    if (fin && N.maxOf(dl) > 0.2 * Math.min(v.R_1, v.R_2)) warnings.push('The computed compression exceeds a fifth of the smaller radius: the contact stiffness is too low for the bodies to be treated as nearly rigid.');
    if (fin && c.e < 1e-3) warnings.push('A linear spring–dashpot contact cannot give exactly zero restitution; a value of 0.001 is used for the contact history.');
    // sweeps
    const es = N.linspace(0, 1, 51), sw = es.map(e => collide({ ...v, e_r: e }, { ...a, fixed_e: true }));
    const mr = N.logspace(0.01, 100, 81), sm = mr.map(q => collide({ ...v, m_2: q * v.m_1 }, { ...a, free_target: true }));
    // animation about the instant of contact
    const span = 4 * (v.R_1 + v.R_2), tw = span / Math.max(Math.abs(c.urel), Math.abs(v.u_1), Math.abs(v.u_2), 1e-9), ts = N.linspace(-tw, tw, 81);
    const c1 = [-v.R_1 * c.n[0], -v.R_1 * c.n[1]], c2 = [v.R_2 * c.n[0], v.R_2 * c.n[1]], hit = c.vn > 0;
    const posAt = t => (t < 0 || !hit ? [[c1[0] + v.u_1 * t, c1[1] + (hit ? 0 : 3 * v.R_1)], [c2[0] + v.u_2 * t, c2[1]]] : [[c1[0] + c.v1[0] * t, c1[1] + c.v1[1] * t], [c2[0] + c.v2[0] * t, c2[1] + c.v2[1] * t]]);
    const frames = ts.map(posAt), ext = 1.2 * N.maxOf(frames.flatMap(f => f.flatMap(p => p.map(Math.abs)))) + v.R_1 + v.R_2;
    return {
      scalars: [
        scalar('v_1x', 'Body 1 after impact: velocity along the approach direction', c.v1[0], 'm/s'), scalar('v_1y', 'Body 1 after impact: transverse velocity', c.v1[1], 'm/s'),
        scalar('v_2x', 'Body 2 after impact: velocity along the approach direction', c.v2[0], 'm/s'), scalar('v_2y', 'Body 2 after impact: transverse velocity', c.v2[1], 'm/s'),
        scalar('w_1', 'Speed of body 1 after impact', sp(c.v1), 'm/s'), scalar('w_2', 'Speed of body 2 after impact', sp(c.v2), 'm/s'),
        scalar('th_1', 'Deflection of body 1 from the approach direction', Math.atan2(c.v1[1] || 0, c.v1[0]), 'rad', { show: 'deg' }), scalar('th_2', 'Direction of body 2 after impact', Math.atan2(c.v2[1] || 0, c.v2[0]), 'rad', { show: 'deg' }),
        scalar('v_n', 'Closing speed along the line of centres', c.vn, 'm/s'), scalar('e_eff', 'Coefficient of restitution used', c.e, '1'),
        scalar('J', 'Impulse exchanged', c.J, 'N s'), scalar('v_cm', c.wall ? 'Velocity of the wall' : 'Velocity of the centre of mass', vcm, 'm/s'),
        scalar('KE_0', c.wall ? 'Kinetic energy before impact (wall frame)' : 'Kinetic energy before impact', c.ke0, 'J'), scalar('dE', 'Kinetic energy dissipated', c.dE, 'J'),
        scalar('f_loss', 'Fraction of kinetic energy dissipated', c.ke0 > 0 ? c.dE / c.ke0 : 0, '1'), scalar('f_max', 'Largest fraction that could be dissipated (e = 0)', c.ke0 > 0 ? 0.5 * c.mred * c.vn ** 2 / c.ke0 : 0, '1'),
        scalar('t_c', 'Contact duration', fin ? tc : NaN, 's', { show: 'ms', text: fin ? undefined : nd }), scalar('F_max', 'Peak contact force', fin ? N.maxOf(Fc) : NaN, 'N', { text: fin ? undefined : nd }),
        scalar('d_max', 'Greatest compression', fin ? N.maxOf(dl) : NaN, 'm', { show: 'mm', text: fin ? undefined : nd }), scalar('F_avg', 'Mean contact force over the contact', fin ? c.J / tc : NaN, 'N', { text: fin ? undefined : nd }),
      ],
      series: [
        line('restitution', 'Outcome against coefficient of restitution', 'Coefficient of restitution', '–', es, [{ label: 'Body 1 velocity along approach', data: sw.map(q => q.v1[0]) }, { label: 'Body 2 velocity along approach', data: sw.map(q => q.v2[0]) }], 'Velocity', 'm/s'),
        line('energy', 'Energy dissipated against coefficient of restitution', 'Coefficient of restitution', '–', es, [{ label: 'Fraction of kinetic energy dissipated', data: sw.map(q => (q.ke0 > 0 ? q.dE / q.ke0 : 0)) }], 'Fraction', '–'),
        line('mass-ratio', 'Outcome against mass ratio', 'Mass ratio m₂/m₁', '–', mr, [{ label: 'Body 1 velocity along approach', data: sm.map(q => q.v1[0]) }, { label: 'Body 2 velocity along approach', data: sm.map(q => q.v2[0]) }], 'Velocity', 'm/s', { logx: true }),
        line('contact', 'Contact force during the impact', 'Time', 'ms', tcs.map(t => t * 1000), [{ label: 'Contact force', data: Fc }], 'Force', 'N', { note: fin ? 'Linear spring–dashpot contact.' : 'Shown for the stated contact stiffness; the instantaneous model uses only the impulse, the area under this curve.' }),
      ],
      anims: [motion('impact', 'Motion through the impact', frames, ts, { trails: true, labels: ['Body 1', c.wall ? 'Wall' : 'Body 2'], radii: [v.R_1, v.R_2], bounds: [-ext, ext, -ext, ext], unit: 'm' })],
      checks: [
        check('Momentum conservation', c.wall ? 0 : Math.hypot(p1x - p0, p1y) / pscale, 1e-12, c.wall ? 'Not applicable: the wall absorbs momentum' : 'Vector sum of momenta before and after'),
        check('Energy accounting', (c.ke0 - c.ke1 - c.dE) / (c.ke0 + 1e-12), 1e-10, 'Kinetic energy before, after and dissipated'),
        check('Impulse equals the area under the contact force', c.J > 0 ? (N.trapz(tcs, Fc) - c.J) / c.J : 0, 2e-3, 'Time integral of the spring–dashpot force against (1 + e)·μ·v_n'),
        check('Kinetic energy does not increase', c.dE < -1e-12 ? 1 : 0, 0, 'Second-law requirement: e ≤ 1'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const on = { head_on: true, fixed_e: true, free_target: true, instantaneous: true };
    const el = collide({ ...v, m_2: v.m_1, e_r: 1 }, on), pl = collide({ ...v, e_r: 0 }, on), vcm = (v.m_1 * v.u_1 + v.m_2 * v.u_2) / (v.m_1 + v.m_2);
    const ob = collide({ ...v, m_2: v.m_1, e_r: 1, u_2: 0 }, { ...on, head_on: false });
    const hv = collide({ ...v, m_1: 1e9, m_2: 1, u_1: 1, u_2: 0, e_r: 1 }, on);
    const e = Math.max(v.e_r, 1e-3), z = contactZeta(e), mred = v.m_1 * v.m_2 / (v.m_1 + v.m_2), wn = Math.sqrt(v.k_c / mred), tc = Math.PI / (wn * Math.sqrt(1 - z * z));
    const fin = N.rk45((t, y) => [y[1], -2 * z * wn * y[1] - wn * wn * y[0]], [0, 1], 0, tc, 2, { rtol: 1e-11, atol: 1e-14 }).final;
    return [
      bench('Elastic head-on collision of equal masses: body 1 takes the velocity of body 2', el.v1[0], v.u_2, 'Velocities are exchanged', 1e-12),
      bench('Elastic head-on collision of equal masses: body 2 takes the velocity of body 1', el.v2[0], v.u_1, 'Velocities are exchanged', 1e-12),
      bench('Perfectly inelastic collision: common velocity', pl.v1[0], vcm, 'Both bodies move with the centre of mass', 1e-12),
      bench('Elastic oblique collision of equal masses, target at rest: outgoing paths at right angles (1 = exact)', 1 + (ob.v1[0] * ob.v2[0] + ob.v1[1] * ob.v2[1]) / (v.u_1 ** 2 + 1e-12), 1, 'v₁ · v₂ = 0', 1e-12),
      bench('Heavy body striking a light one at rest elastically: light body leaves at twice the speed', hv.v2[0], 2, 'Limit m₁ ≫ m₂', 1e-8),
      bench('Spring–dashpot contact: rebound over approach speed vs the restitution coefficient', -fin[1], e, 'e = exp(−πζ/√(1−ζ²))', 1e-8),
    ];
  },
  validation: [],
  diagram(v, a) {
    const c = collide(v, a), sc = 50 / Math.max(v.R_1, v.R_2), r1 = Math.max(v.R_1 * sc, 8), r2 = Math.max(v.R_2 * sc, 8), cx = 320, cy = 190;
    const p1 = [cx - r1 * c.n[0], cy + r1 * c.n[1]], p2 = [cx + r2 * c.n[0], cy - r2 * c.n[1]], vs = 40 / Math.max(Math.abs(v.u_1), Math.abs(v.u_2), Math.hypot(...c.v1), Math.hypot(...c.v2), 1e-9);
    const arr = (p, q, cls) => (Math.hypot(q[0], q[1]) * vs > 4 ? S.arrow(p[0], p[1], p[0] + q[0] * vs, p[1] - q[1] * vs, cls) : '');
    return svg(`
      ${S.circle(p1[0], p1[1], r1, 'd-body')} ${c.wall ? S.rect(p2[0] - 6, cy - 110, 30, 220, 'd-ground', 0) : S.circle(p2[0], p2[1], r2, 'd-body')}
      ${S.line(p1[0], p1[1], p2[0], p2[1], 'd-dim')}
      ${arr([p1[0] - 2.4 * r1, p1[1] - r1 - 26], [v.u_1, 0], 'd-arrow')} ${S.text(p1[0] - 2.4 * r1, p1[1] - r1 - 36, `u₁ = ${lab(v.u_1, 'm/s')}`, 'd-text d-small', 'start')}
      ${c.wall ? '' : arr([p2[0] + 2.4 * r2, p2[1] - r2 - 26], [v.u_2, 0], 'd-arrow') + S.text(p2[0] + 2.4 * r2, p2[1] - r2 - 36, `u₂ = ${lab(v.u_2, 'm/s')}`, 'd-text d-small', 'end')}
      ${arr(p1, c.v1, 'd-arrow d-heat')} ${c.wall ? '' : arr(p2, c.v2, 'd-arrow d-heat')}
      ${S.text(p1[0], p1[1] + r1 + 22, `m₁ = ${lab(v.m_1, 'kg')}`, 'd-text d-small')} ${c.wall ? '' : S.text(p2[0], p2[1] + r2 + 22, `m₂ = ${lab(v.m_2, 'kg')}`, 'd-text d-small')}
      ${S.text(320, 36, `e = ${lab(c.e)}    impulse ${lab(c.J, 'N s')}    energy dissipated ${lab(c.dE, 'J')}`)}
      ${S.text(320, 345, 'thin arrows: before impact    heavy arrows: after impact    dashed: line of centres', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Verify conservation of momentum in collisions on a low-friction track or table and measure the coefficient of restitution and the kinetic energy lost.',
    apparatus: ['Linear air track with two gliders and interchangeable bumpers (spring steel, rubber, hook-and-loop)', 'Or an air table with two pucks for oblique impacts', 'Additional masses to vary the mass ratio', 'Spirit level'],
    instruments: [{ name: 'Two photogate timers with flags', measures: 'Glider speeds before and after impact', range: '0.05–2 m/s', resolution: '±0.5 %' }, { name: 'Overhead camera with tracking (air table)', measures: 'Velocity vectors', range: '1 m field', resolution: '1 mm, 120 frames/s' }, { name: 'Balance', measures: 'Masses', range: '0–2 kg', resolution: '0.1 g' }, { name: 'Piezoelectric force sensor on a bumper (optional)', measures: 'Contact force history', range: '0–500 N', resolution: '50 kHz' }],
    procedure: ['Level the track until a glider at rest stays at rest.', 'Record speeds before and after impact for equal masses with each bumper type, then for mass ratios of 2 and 3.', 'Compute total momentum and kinetic energy before and after and the ratio of separation to approach speed.', 'For the air table, repeat with offset impacts and resolve velocities along and across the line of centres.'],
    controls: ['Single glider passing through both gates to measure residual drag', 'Reverse the roles of projectile and target', 'Vary impact speed to test whether the restitution coefficient is constant'],
    signatures: ['Total momentum unchanged within about 1 % for every bumper type', 'Equal masses exchange velocities with spring bumpers', 'Bodies move off together at the centre-of-mass velocity with hook-and-loop bumpers', 'Equal smooth pucks leave at right angles after an elastic oblique impact on a stationary target'],
    safety: ['Keep fingers clear of colliding gliders', 'Secure the air supply hose; do not exceed the blower rating'],
  },
  falsify: ['Total momentum of an isolated pair changing in a collision by more than the measurement uncertainty.', 'Kinetic energy increasing in a collision with no stored energy released.', 'Tangential velocity components changing in an impact between truly smooth, non-rotating discs.'],
  alternatives: [{ name: 'Poisson and energetic (Stronge) restitution', text: 'Define the coefficient through impulses or work during compression and restitution; they differ from Newton\'s definition when friction and eccentric impact are present.' }, { name: 'Hertzian contact', text: 'Elastic spheres obey a force proportional to compression to the power 3/2, giving a contact time that falls slowly with impact speed.' }, { name: 'Impact with friction and spin', text: 'Rough bodies exchange tangential impulse and angular momentum; a tangential restitution coefficient is then needed.' }],
  hazards: [{ hazard: 'Fragment ejection', cause: 'Brittle bodies colliding at speed', mitigation: 'Screens and eye protection' }, { hazard: 'Pinch and crush', cause: 'Hands between heavy colliding bodies', mitigation: 'Guards and remote release' }],
  standards: ['ISO 6487 (road vehicles — measurement techniques in impact tests — instrumentation)', 'ASTM F1887 (standard test method for measuring the coefficient of restitution of baseballs and softballs)'],
  limits: 'Smooth, non-rotating bodies; a single impact along a well-defined line of centres. The coefficient of restitution is an empirical property of the pair and impact speed. The spring–dashpot contact is a convenience model: real contacts are closer to Hertzian and may involve plastic flow and wave propagation.',
  numerics: { method: 'Closed-form algebra; closed-form damped half-cycle for the contact history; RK45 for the contact benchmark' },
  optimise: { objective: 'w_2', sense: 'max', vars: ['m_2'], note: 'Energy transfer to the target is greatest for equal masses; target speed is greatest for a light target.' },
  inverse: { series: 'restitution', fit: ['m_2'] },
  extensions: ['Friction and spin in oblique impact', 'Hertzian contact time and peak force', 'Chains of collisions (Newton\'s cradle) and granular gases'],
};

// ------------------------------------------------------------------ 13. Newton's cannonball
function cannonOrbit(v, a, vLaunch = v.v_0) {
  const r0 = v.R_p + v.h_m, mu = v.GM, el = a.horizontal ? 0 : v.elev, om = a.non_rotating ? 0 : 2 * Math.PI / v.T_rot;
  const vh = vLaunch * Math.cos(el) + om * r0, vr = vLaunch * Math.sin(el), vi = Math.hypot(vh, vr);
  const eps = vi * vi / 2 - mu / r0, hA = r0 * vh, ecc = Math.sqrt(Math.max(0, 1 + 2 * eps * hA * hA / (mu * mu))), p = hA * hA / mu;
  const bound = eps < 0, rp = p / (1 + ecc), ra = bound ? p / Math.max(1 - ecc, 1e-300) : Infinity, sma = -mu / (2 * eps);
  const outcome = !bound ? 3 : rp < v.R_p ? 0 : ecc < 1e-3 ? 1 : 2;
  // true anomaly swept from launch to the surface, when the conic meets it
  let sweep = NaN;
  if (rp < v.R_p && ecc > 0) { const c0 = N.clamp((p / r0 - 1) / ecc, -1, 1), ci = N.clamp((p / v.R_p - 1) / ecc, -1, 1), nu0 = vr >= 0 ? Math.acos(c0) : 2 * Math.PI - Math.acos(c0); sweep = 2 * Math.PI - Math.acos(ci) - nu0; }
  return { r0, mu, om, vh, vr, vi, eps, hA, ecc, p, bound, rp, ra, sma, outcome, sweep, vc: Math.sqrt(mu / r0), T: bound ? 2 * Math.PI * Math.sqrt(sma ** 3 / mu) : NaN };
}
/** Integrate one shot. Round Earth: state [x, y, vx, vy, swept angle], launch from (0, r0). Flat Earth: y is height. */
function cannonShot(v, a, vLaunch, nOut, rtol, maxSteps = 20000) {
  const o = cannonOrbit(v, a, vLaunch), { r0, mu } = o, R = v.R_p, gs = mu / (R * R), kd = a.vacuum ? 0 : 1 / (2 * v.beta), lim = 6 * r0;
  if (a.round_earth) {
    const f = (t, s) => {
      const r2 = s[0] * s[0] + s[1] * s[1], r = Math.sqrt(r2), g = -mu / (r2 * r), ux = s[2] - o.om * s[1], uy = s[3] + o.om * s[0], q = kd ? kd * v.rho_0 * Math.exp(-(r - R) / v.H_a) * Math.hypot(ux, uy) : 0;
      return [s[2], s[3], g * s[0] - q * ux, g * s[1] - q * uy, (s[1] * s[2] - s[0] * s[3]) / r2];
    };
    const tMax = Math.min(o.bound ? 1.05 * o.T : Infinity, 60 * r0 / o.vc);
    const s = toEvent(f, [0, r0, o.vh, o.vr, 0], tMax, y => { const r = Math.hypot(y[0], y[1]); return Math.min(r / R - 1, 1 - y[4] / (2 * Math.PI), 1 - r / lim); }, null, nOut, { rtol, atol: 1e-6, maxSteps });
    const yf = s.yHit, rf = Math.hypot(yf[0], yf[1]), hit = s.hit && rf - R < 1e-6 * R;
    return { o, s, yf, hit, orbit: s.hit && yf[4] >= 2 * Math.PI * (1 - 1e-9), escaped: s.hit && rf >= lim * (1 - 1e-9), x: s.y[0], y: s.y[1], range: hit ? yf[4] * R : NaN, tf: s.tHit, vf: Math.hypot(yf[2], yf[3]) };
  }
  const f = (t, s) => { const q = kd ? kd * v.rho_0 * Math.exp(-Math.max(s[1], 0) / v.H_a) * Math.hypot(s[2], s[3]) : 0; return [s[2], s[3], -q * s[2], -gs - q * s[3], 0]; };
  const tv = (o.vr + Math.sqrt(o.vr ** 2 + 2 * gs * v.h_m)) / gs, s = toEvent(f, [0, v.h_m, o.vh, o.vr, 0], 50 * tv + 100, y => y[1], y => y[3], nOut, { rtol, atol: 1e-6, maxSteps }), yf = s.yHit;
  return { o, s, yf, hit: s.hit, orbit: false, escaped: false, x: s.y[0], y: s.y[1], range: s.hit ? yf[0] : NaN, tf: s.tHit, vf: Math.hypot(yf[2], yf[3]) };
}
const CANNON_OUT = ['Falls back to the surface', 'Circular orbit', 'Elliptical orbit', 'Escapes: parabolic or hyperbolic trajectory'];
const CANNON_ON = { vacuum: true, round_earth: true, non_rotating: true, horizontal: true };
const cannonball = {
  id: 'newtons-cannonball',
  title: 'Newton\'s cannonball',
  module: 1, klass: ['I', 'II'], domains: ['classical', 'space', 'logic'],
  keywords: ['newton\'s cannonball', 'newtons cannonball', 'newton\'s cannon', 'cannonball', 'cannon on a mountain', 'thought experiment', 'orbital velocity', 'escape velocity', 'circular orbit', 'satellite', 'falling around the earth', 'why satellites do not fall', 'orbit', 'mountain', 'projectile'],
  summary: 'Newton\'s thought experiment: a cannon on a high mountain fires horizontally at ever greater speeds, and the same gravity that brings a slow shot to the ground holds a fast one in orbit or lets a faster one escape.',
  background: [
    'In the Treatise of the System of the World Newton imagined a cannon on a mountain so high that the air offers no resistance. A ball fired slowly lands near the foot of the mountain; fired faster it lands farther off; and at a certain speed the surface curves away beneath it exactly as fast as it falls, so that it never lands but circles the Earth. The argument shows that a projectile and the Moon are the same kind of object: an orbit is continuous free fall.',
    'Quantitatively, the circular speed at distance r from the centre is √(GM/r) and the speed of escape is √2 times greater. Between the two the path is an ellipse with the launch point at its lowest point; just below the circular speed it is an ellipse with the launch point at its highest, and the ball survives only if that ellipse clears the surface.',
  ],
  phenomena: ['Free fall under inverse-square gravity', 'Curvature of the Earth\'s surface', 'Closed orbits', 'Escape'],
  laws: ['gravitation', 'newton2', 'energy', 'angular', 'logic_nc'],
  refs: ['Newton, I. (1728). A Treatise of the System of the World. F. Fayram, London.', 'Newton, I. (1687). Philosophiæ Naturalis Principia Mathematica. Royal Society, London.', 'Feynman, R. P., Leighton, R. B. & Sands, M. (1963). The Feynman Lectures on Physics, Vol. 1, Chapter 7. Addison-Wesley.', 'Bate, R. R., Mueller, D. D. & White, J. E. (1971). Fundamentals of Astrodynamics. Dover.', 'Brown, J. R. (1991). The Laboratory of the Mind: Thought Experiments in the Natural Sciences. Routledge.'],
  inputs: [
    inp('v_0', 'Muzzle speed', 'km/s', 6.5, { min: 0.1, max: 15, aliases: ['muzzle speed', 'launch speed', 'firing speed', 'speed', 'velocity'] }),
    inp('h_m', 'Height of the mountain above the surface', 'km', 300, { min: 1, max: 5000, kind: 'geometry', aliases: ['mountain height', 'height', 'altitude'], src: 'Chosen above the sensible atmosphere, as Newton\'s argument requires' }),
    inp('R_p', 'Radius of the planet', 'km', 6371, { min: 500, max: 80000, kind: 'environment', aliases: ['planet radius', 'earth radius', 'radius'], src: 'Earth mean radius (IAU)' }),
    inp('GM', 'Gravitational parameter of the planet', 'm^3/s^2', 3.986004418e14, { min: 1e10, max: 2e17, kind: 'environment', aliases: ['gravitational parameter', 'gm'], src: 'Earth (IAU)' }),
    inp('elev', 'Elevation of the barrel above the horizontal (when not horizontal)', 'deg', 20, { min: -30, max: 80, kind: 'geometry', aliases: ['elevation', 'barrel angle'] }),
    inp('beta', 'Ballistic coefficient of the ball, m/(C_D A) (with air)', 'kg/m^2', 2200, { min: 50, max: 50000, aliases: ['ballistic coefficient'], src: 'Iron ball 0.2 m in diameter with C_D = 0.47' }),
    inp('rho_0', 'Surface air density (with air)', 'kg/m^3', 1.225, { min: 0.001, max: 100, kind: 'environment', aliases: ['air density'] }),
    inp('H_a', 'Atmospheric scale height (with air)', 'km', 8.5, { min: 3, max: 30, kind: 'environment', aliases: ['scale height'] }),
    inp('T_rot', 'Rotation period of the planet (when rotating)', 'h', 23.9345, { min: 1, max: 10000, kind: 'environment', aliases: ['rotation period', 'day length'], src: 'Sidereal day' }),
  ],
  assumptions: [
    asm('vacuum', 'There is no air resistance.', { why: 'Newton placed the cannon above the atmosphere', alt: 'An exponential atmosphere exerts quadratic drag on the ball.' }),
    asm('round_earth', 'The planet is a sphere attracting as a point mass at its centre.', { why: 'Newton\'s shell theorem', alt: 'Flat ground with uniform gravity (Galileo\'s parabola): every shot lands, however fast.' }),
    asm('non_rotating', 'The planet does not rotate.', { why: 'Simplest statement of the argument', alt: 'The cannon is at the equator firing east: the ground speed of the rotating planet adds to the muzzle speed.' }),
    asm('horizontal', 'The cannon fires exactly horizontally.', { why: 'Newton\'s construction', alt: 'The barrel is elevated by the stated angle.' }),
  ],
  symbols: { x: ['Position, horizontal component', 'm'], y: ['Position, vertical component (height above flat ground)', 'm'], t: ['Time', 's'], r: ['Distance from the planet centre', 'm'], r_0: ['Launch distance from the centre', 'm'], v: ['Speed', 'm/s'], v_x: ['Velocity, horizontal component', 'm/s'], v_i: ['Launch speed in the non-rotating frame', 'm/s'], v_h: ['Horizontal launch velocity in the non-rotating frame', 'm/s'], v_v: ['Vertical launch velocity', 'm/s'], v_c: ['Circular speed at the launch point', 'm/s'], v_e: ['Escape speed at the launch point', 'm/s'], v_min: ['Least horizontal speed that clears the planet', 'm/s'], eps: ['Specific orbital energy', 'J/kg'], h_a: ['Specific angular momentum', 'm^2/s'], a_sm: ['Semi-major axis', 'm'], ecc: ['Eccentricity', '1'], r_p: ['Periapsis distance', 'm'], g_s: ['Surface gravitational acceleration', 'm/s^2'], rho: ['Air density', 'kg/m^3'], x_R: ['Range on flat ground', 'm'] },
  equations: a => {
    const drag = c => (a.vacuum ? '' : ` - rho*v*${c}/(2*beta)`), spin = a.non_rotating ? '' : ' + 2*pi*r_0/T_rot';
    const common = [
      eq('r0', 'Launch distance from the centre', 'r_0', 'R_p + h_m', { kind: 'definition' }),
      ...(a.horizontal ? [eq('vi', 'Launch speed in the non-rotating frame', 'v_i', `v_0${spin}`, { kind: a.non_rotating ? 'definition' : 'derived', origin: a.non_rotating ? undefined : 'Galilean addition of the ground speed at the equator', needs: ['horizontal'] })] : [
        eq('vh', 'Horizontal launch velocity in the non-rotating frame', 'v_h', `v_0*cos(elev)${spin}`, { kind: 'derived', origin: a.non_rotating ? 'Resolution of the muzzle velocity' : 'Resolution of the muzzle velocity plus the ground speed at the equator' }),
        eq('vv', 'Vertical launch velocity', 'v_v', 'v_0*sin(elev)', { kind: 'derived', origin: 'Resolution of the muzzle velocity' }),
        eq('vi', 'Launch speed in the non-rotating frame', 'v_i', 'sqrt(v_h^2 + v_v^2)', { kind: 'definition' }),
      ]),
      ...(a.vacuum ? [] : [eq('rho', 'Air density', 'rho', a.round_earth ? 'rho_0*exp(-(r - R_p)/H_a)' : 'rho_0*exp(-y/H_a)', { kind: 'closure', origin: 'Isothermal atmosphere' })]),
    ];
    if (!a.round_earth) return [...common,
      eq('gs', 'Surface gravity', 'g_s', 'GM/R_p^2', { kind: 'law', origin: 'Newton\'s law of gravitation at the surface' }),
      eq('my', 'Vertical motion', 'd2(y,t)', `-g_s${drag('d(y,t)')}`, { kind: 'law', origin: 'Newton\'s second law in a uniform field' }),
      ...(a.vacuum ? [eq('range', 'Range of a horizontal shot', 'x_R', 'v_i*sqrt(2*h_m/g_s)', { kind: 'derived', origin: 'Galileo\'s parabola: always finite', note: 'For an elevated barrel the time of flight is longer; the range remains finite.' })] : [eq('mx', 'Horizontal motion', 'd2(x,t)', '-rho*v*d(x,t)/(2*beta)', { kind: 'law', origin: 'Newton\'s second law with quadratic drag' })]),
    ];
    return [...common,
      eq('mx', 'Equation of motion', 'd2(x,t)', `-GM*x/r^3${drag('v_x')}`, { kind: 'law', origin: 'Newton\'s second law with universal gravitation', note: `Holds for each Cartesian component.${!a.vacuum && !a.non_rotating ? ' In the drag term the speed and the velocity component are taken relative to the air, which turns with the planet.' : ''}` }),
      eq('vc', 'Circular speed', 'v_c', 'sqrt(GM/r_0)', { kind: 'derived', origin: 'Gravity supplies exactly the centripetal acceleration v²/r' }),
      eq('ve', 'Escape speed', 'v_e', 'sqrt(2*GM/r_0)', { kind: 'derived', origin: 'Zero total energy' }),
      eq('vmin', 'Least speed that clears the planet', 'v_min', 'sqrt(2*GM*R_p/(r_0*(R_p + r_0)))', { kind: 'derived', origin: 'Ellipse with apoapsis at the cannon and periapsis grazing the surface' }),
      eq('en', 'Specific orbital energy', 'eps', 'v_i^2/2 - GM/r_0', { kind: 'law', origin: 'Conservation of energy' }),
      eq('am', 'Specific angular momentum', 'h_a', a.horizontal ? 'r_0*v_i' : 'r_0*v_h', { kind: 'law', origin: 'Conservation of angular momentum' }),
      eq('sma', 'Semi-major axis', 'a_sm', '-GM/(2*eps)', { kind: 'derived', origin: 'Energy of a Kepler orbit' }),
      eq('ecc', 'Eccentricity', 'ecc', 'sqrt(1 + 2*eps*h_a^2/GM^2)', { kind: 'derived', origin: 'Geometry of the conic' }),
      eq('rp', 'Periapsis distance', 'r_p', 'h_a^2/(GM*(1 + ecc))', { kind: 'derived', origin: 'Orbit equation; the shot lands if this is less than the planet radius' }),
    ];
  },
  derivation: a => (a.round_earth ? [
    { text: 'In one second a body near the surface falls a distance ½g below the straight line it would otherwise follow. Over a horizontal distance d the Earth\'s surface drops away by about d²/2R.', tex: '\\text{fall} = \\tfrac12 g t^2,\\qquad \\text{drop of the surface} \\approx \\frac{(vt)^2}{2R}' },
    { text: 'If the two are equal the ball stays at the same height for ever. That fixes the speed, and the same result follows from requiring gravity to supply the centripetal acceleration.', tex: '\\frac{v_c^2}{r} = \\frac{GM}{r^2}\\quad\\Rightarrow\\quad v_c = \\sqrt{\\frac{GM}{r}}' },
    { text: 'More generally the motion conserves energy and angular momentum, and the path is a conic with the Earth\'s centre at a focus.', tex: '\\varepsilon = \\tfrac12 v^2 - \\frac{GM}{r_0},\\qquad h = r_0 v\\cos\\phi,\\qquad e = \\sqrt{1 + \\frac{2\\varepsilon h^2}{(GM)^2}}' },
    { text: 'A horizontal shot slower than v_c starts at the top of its ellipse. It survives only if the lowest point of that ellipse lies above the surface, which sets the least orbital speed from a mountain of given height.', tex: 'r_p = \\frac{h^2}{GM(1+e)} \\ge R\\quad\\Leftrightarrow\\quad v \\ge v_{min} = \\sqrt{\\frac{2GM\\,R}{r_0(R+r_0)}}' },
    { text: 'When the total energy reaches zero the ellipse opens into a parabola and the ball never returns.', tex: 'v_e = \\sqrt{\\frac{2GM}{r_0}} = \\sqrt2\\,v_c' },
  ] : [
    { text: 'On flat ground with uniform gravity the horizontal velocity is constant and the ball falls the height of the mountain in a fixed time.', tex: 't_f = \\sqrt{2h/g}' },
    { text: 'The range grows in proportion to the muzzle speed but is always finite: on a flat Earth nothing can orbit. Newton\'s insight depends on the ground curving away.', tex: 'x_R = v\\sqrt{2h/g}' },
  ]),
  solve(v, a) {
    const o = cannonOrbit(v, a), shot = cannonShot(v, a, v.v_0, 241, 1e-10), R = v.R_p, r0 = o.r0, warnings = [];
    const vmin = Math.sqrt(2 * o.mu * R / (r0 * (R + r0))), ve = Math.SQRT2 * o.vc, exact = a.vacuum && a.round_earth;
    const outcome = !a.round_earth ? 0 : exact ? o.outcome : shot.hit ? 0 : o.outcome === 0 ? 2 : o.outcome;
    // family of shots at fixed multiples of the circular speed (speeds in the non-rotating frame)
    const ks = [0.4, 0.6, 0.8, vmin / o.vc, 1, 1.2, Math.SQRT2], spin = o.om * r0;
    const fam = ks.map(k => cannonShot(v, a, Math.max((k * o.vc - spin) / Math.cos(a.horizontal ? 0 : v.elev), 1), 121, 1e-7, 6000));
    const lbl = k => (Math.abs(k - vmin / o.vc) < 1e-12 ? 'grazing speed' : Math.abs(k - Math.SQRT2) < 1e-12 ? 'escape speed (√2 v_c)' : k === 1 ? 'circular speed v_c' : `${k} v_c`);
    const ring = circlePts(R, 181), top = a.round_earth ? null : N.linspace(-0.05, 1.05, 2).map(u => u * N.maxOf(fam.map(q => N.maxOf(q.x))));
    const paths = [
      a.round_earth ? { label: 'Planet surface', x: ring.map(p => p[0]), y: ring.map(p => p[1]), z: ring.map(() => 0) } : { label: 'Flat ground', x: top, y: top.map(() => 0), z: top.map(() => 0) },
      ...fam.map((q, i) => ({ label: `Shot at ${lbl(ks[i])}`, x: q.x, y: q.y, z: q.x.map(() => 0) })),
      { label: `Your shot, ${lab(v.v_0 / 1000, 'km/s')}`, x: shot.x, y: shot.y, z: shot.x.map(() => 0) },
    ];
    const s = shot.s, rr = s.t.map((_, i) => (a.round_earth ? Math.hypot(s.y[0][i], s.y[1][i]) - R : s.y[1][i])), sp = s.t.map((_, i) => Math.hypot(s.y[2][i], s.y[3][i]));
    const en = s.t.map((_, i) => 0.5 * sp[i] ** 2 - (a.round_earth ? o.mu / (rr[i] + R) : -o.mu / (R * R) * rr[i])), e0 = en[0], es = Math.max(Math.abs(e0), 0.5 * o.vi ** 2);
    const dE = en.map(e => (e - e0) / es);
    const vs = N.linspace(0.05, 1.6, 80).map(k => k * o.vc), rng = vs.map(q => { const c = cannonOrbit(v, CANNON_ON, q); return a.round_earth ? (Number.isFinite(c.sweep) ? c.sweep * R / 1000 : NaN) : q * Math.sqrt(2 * v.h_m * R * R / o.mu) / 1000; });
    if (!a.vacuum && a.round_earth && v.h_m < 100e3) warnings.push('The mountain top is inside the sensible atmosphere, so drag slows the ball on every pass: a lasting orbit is impossible, as Newton recognised when he placed the cannon above the air.');
    if (!a.round_earth) warnings.push('On flat ground with uniform gravity every shot lands: orbiting depends on the curvature of the Earth.');
    if (a.round_earth && outcome === 2 && o.ra > 6 * r0) warnings.push('The orbit reaches beyond six launch radii; the plotted path is cut off there.');
    if (v.v_0 > 0.1 * C.c) warnings.push('The speed is a significant fraction of the speed of light; Newtonian mechanics is no longer adequate.');
    const none = t => ({ text: t }), far = exact && outcome === 0 && !shot.hit && Number.isFinite(o.sweep);
    const fs = every(s.t.length, 200), fi = s.t.map((_, i) => i).filter(i => i % fs === 0), ext = 1.1 * Math.max(N.maxOf(shot.x.map(Math.abs)), N.maxOf(shot.y.map(Math.abs)), a.round_earth ? r0 : v.h_m);
    return {
      scalars: [
        scalar('outcome', 'Outcome of the shot', outcome, '1', { text: CANNON_OUT[outcome] }),
        scalar('v_i', 'Launch speed in the non-rotating frame', o.vi, 'm/s', { show: 'km/s' }), scalar('v_c', 'Circular speed at the cannon', o.vc, 'm/s', { show: 'km/s' }),
        scalar('v_e', 'Escape speed at the cannon', ve, 'm/s', { show: 'km/s' }), scalar('v_min', 'Least horizontal speed that clears the planet', vmin, 'm/s', { show: 'km/s' }),
        scalar('v_ratio', 'Launch speed over circular speed', o.vi / o.vc, '1'),
        scalar('g_s', 'Surface gravitational acceleration', o.mu / (R * R), 'm/s^2'), scalar('T_c', 'Period of the circular orbit at the cannon', 2 * Math.PI * r0 / o.vc, 's', { show: 'min' }),
        scalar('ecc', 'Eccentricity of the path', a.round_earth ? o.ecc : NaN, '1', a.round_earth ? {} : none('Parabola over flat ground')),
        scalar('a_sm', 'Semi-major axis', a.round_earth && o.bound ? o.sma : NaN, 'm', { show: 'km', ...(a.round_earth && o.bound ? {} : none(a.round_earth ? 'Unbound trajectory' : 'Not an orbit')) }),
        scalar('r_p', 'Lowest point of the conic (from the centre)', a.round_earth ? o.rp : NaN, 'm', { show: 'km', ...(a.round_earth ? {} : none('Not an orbit')) }),
        scalar('r_a', 'Highest point of the conic (from the centre)', a.round_earth && o.bound ? o.ra : NaN, 'm', { show: 'km', ...(a.round_earth && o.bound ? {} : none(a.round_earth ? 'None: the ball escapes' : 'Not an orbit')) }),
        scalar('T_orb', 'Orbital period', outcome === 1 || outcome === 2 ? o.T : NaN, 's', { show: 'min', ...(outcome === 1 || outcome === 2 ? {} : none(outcome === 3 ? 'None: the ball escapes' : 'None: the ball lands')) }),
        scalar('s_R', 'Distance along the ground to the point of impact', shot.hit ? shot.range : far ? o.sweep * R : NaN, 'm', { show: 'km', ...(shot.hit ? {} : far ? { note: 'from the conic section; the impact lies beyond the plotted region' } : none('The ball does not land')) }),
        scalar('t_f', 'Time of flight to impact', shot.hit ? shot.tf : NaN, 's', { show: 'min', ...(shot.hit ? {} : none(far ? 'The impact lies beyond the simulated region' : 'The ball does not land')) }),
        scalar('v_f', 'Speed at impact', shot.hit ? shot.vf : far ? Math.sqrt(2 * (o.eps + o.mu / R)) : NaN, 'm/s', { show: 'km/s', ...(shot.hit || far ? {} : none('The ball does not land')) }),
        scalar('drop', 'Fall below the tangent in the first second', 0.5 * o.mu / (r0 * r0), 'm'), scalar('curve', 'Drop of the surface below the tangent over one second of flight at circular speed', o.vc ** 2 / (2 * r0), 'm'),
      ],
      series: [
        line('altitude', 'Altitude of your shot', 'Time', 'min', s.t.map(t => t / 60), [{ label: 'Altitude', data: rr.map(x => x / 1000) }], 'Altitude', 'km'),
        line('speed', 'Speed of your shot', 'Time', 'min', s.t.map(t => t / 60), [{ label: 'Speed', data: sp.map(x => x / 1000) }], 'Speed', 'km/s'),
        line('range-speed', 'Ground range against launch speed (horizontal shot, no air)', 'Launch speed', 'km/s', vs.map(q => q / 1000), [{ label: 'Distance to impact', data: rng }], 'Ground range', 'km', { note: a.round_earth ? 'The curve ends at the grazing speed: faster shots never land.' : 'On flat ground the range grows without limit but is always finite.' }),
      ],
      anims: [motion('shot', 'Flight of the cannonball', fi.map(i => [[shot.x[i], shot.y[i]]]), fi.map(i => s.t[i]), { trails: true, labels: ['Cannonball'], bounds: a.round_earth ? [-ext, ext, -ext, ext] : [0, ext, 0, ext], unit: 'm', backdrop: a.round_earth ? { circle: [0, 0, R] } : undefined })],
      paths: [path3d('family', 'Family of shots at increasing speed', paths, { equal: true, unit: 'm' })],
      checks: [
        a.vacuum ? check('Energy conservation along the path', N.maxOf(dE.map(Math.abs)), 1e-7, 'Largest relative change of specific energy') : check('Energy never increases', Math.max(N.maxOf(dE), 0), 1e-7, 'Drag can only remove mechanical energy'),
        check('Falling matches the curvature at circular speed', (0.5 * o.mu / (r0 * r0) - o.vc ** 2 / (2 * r0)) / (0.5 * o.mu / (r0 * r0)), 1e-12, 'Newton\'s geometric condition for an orbit'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const o = cannonOrbit(v, CANNON_ON), circ = cannonShot(v, CANNON_ON, o.vc, 121, 1e-11), slow = cannonShot(v, CANNON_ON, 0.7 * o.vc, 3, 1e-11), sl = cannonOrbit(v, CANNON_ON, 0.7 * o.vc);
    const vmin = Math.sqrt(2 * o.mu * v.R_p / (o.r0 * (v.R_p + o.r0))), flat = cannonShot(v, { ...CANNON_ON, round_earth: false }, 2000, 3, 1e-11), gs = v.GM / v.R_p ** 2;
    const E = R.BODIES.earth;
    return [
      bench('Shot at circular speed: time for one revolution', circ.tf, 2 * Math.PI * Math.sqrt(o.r0 ** 3 / o.mu), 'Kepler\'s third law for a circular orbit', 1e-8),
      bench('Shot at circular speed: greatest departure from the launch radius (1 = none)', 1 + N.maxOf(circ.x.map((x, i) => Math.abs(Math.hypot(x, circ.y[i]) - o.r0))) / o.r0, 1, 'A circular orbit keeps constant radius', 1e-8),
      bench('Sub-orbital shot: integrated range angle vs conic-section value', slow.yf[4], sl.sweep, 'True-anomaly difference between apoapsis and the surface crossing', 1e-8),
      bench('Grazing speed places the periapsis on the surface', cannonOrbit(v, CANNON_ON, vmin).rp, v.R_p, 'v_min = √(2GM·R/(r₀(R + r₀)))', 1e-10),
      bench('Flat-ground range vs Galileo\'s parabola', flat.range, 2000 * Math.sqrt(2 * v.h_m / gs), 'x = v√(2h/g)', 1e-9),
      bench('Circular speed at the Earth\'s surface', Math.sqrt(E.GM / E.radius), 7910, 'About 7.91 km/s at the mean radius', 1e-3),
      bench('Escape speed from the Earth\'s surface', Math.sqrt(2 * E.GM / E.radius), 11186, 'About 11.2 km/s', 1e-3),
    ];
  },
  validation: [],
  logicPreset: {
    atoms: [
      { k: 'U', text: 'The cannonball and the Moon obey the same laws of motion and the same gravity.' },
      { k: 'F', text: 'The ball is fired fast enough that the ground curves away beneath it as quickly as it falls.' },
      { k: 'B', text: 'The ball is fired below the speed of escape.' },
      { k: 'L', text: 'The ball lands.' },
      { k: 'O', text: 'The ball circles the Earth indefinitely (it is a satellite).' },
      { k: 'M', text: 'The Moon\'s orbit is continual free fall toward the Earth.' },
    ],
    premises: ['F -> ~L', '(~L & B) -> O', '(O & U) -> M'],
    conclusion: '(F & B & U) -> M',
  },
  diagram(v, a) {
    const o = cannonOrbit(v, a), cx = 320, cy = 200, Rp = 95, hm = Math.max(10, Math.min(40, Rp * v.h_m / v.R_p)), r0 = Rp + hm;
    const conic = (k, cls) => { const e = k * k - 1, th = N.linspace(0, 2 * Math.PI, 120), pts = []; for (const t of th) { const den = 1 + e * Math.cos(t), r = den > 0.05 ? r0 * (1 + e) / den : Infinity; if (r < Rp || r > 400) { if (t > 0.1 && r < Rp) break; continue; } pts.push([(cx + r * Math.sin(t)).toFixed(1), (cy - r * Math.cos(t)).toFixed(1)]); } return pts.length > 1 ? S.poly(pts, cls) : ''; };
    return svg(`
      ${S.circle(cx, cy, Rp, 'd-ground')} ${S.path(`M${cx - 9} ${cy - Rp + 2} L${cx} ${cy - r0} L${cx + 9} ${cy - Rp + 2} Z`, 'd-body')}
      ${a.round_earth ? [0.6, 0.8, 0.92].map(k => conic(k, 'd-line')).join('') + conic(1, 'd-line d-heat') + conic(1.2, 'd-line') + conic(Math.SQRT2, 'd-dim') : S.path(`M${cx} ${cy - r0} Q${cx + 120} ${cy - r0} ${cx + 190} ${cy - Rp + 60}`, 'd-line')}
      ${S.arrow(cx, cy - r0, cx + 70, cy - r0)} ${S.text(cx + 76, cy - r0 - 6, `v₀ = ${lab(v.v_0 / 1000, 'km/s')}`, 'd-text', 'start')}
      ${S.text(cx, cy + 4, 'Earth')} ${S.text(cx - 14, cy - r0 - 6, 'cannon', 'd-text d-small', 'end')}
      ${S.text(40, 40, `circular speed ${lab(o.vc / 1000, 'km/s')}`, 'd-text', 'start')} ${S.text(40, 60, `escape speed ${lab(Math.SQRT2 * o.vc / 1000, 'km/s')}`, 'd-text d-small', 'start')}
      ${S.text(600, 40, CANNON_OUT[a.round_earth ? o.outcome : 0], 'd-text', 'end')}
      ${S.text(320, 345, 'slow shots land; at the circular speed the ground curves away as fast as the ball falls', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Realise Newton\'s thought experiment with artificial satellites: confirm that bodies released horizontally above the atmosphere at the predicted speed remain in orbit, and that slower ones re-enter.',
    apparatus: ['Tracking data for satellites and sub-orbital sounding rockets at similar altitude', 'For a classroom analogue: a ball launcher on a table and a curved-surface (gravity-well) demonstrator', 'Numerical orbit propagator for comparison'],
    instruments: [{ name: 'Radar and optical tracking', measures: 'Position and speed of satellites and rocket stages', range: '—', resolution: 'tens of metres; ±1 m/s' }, { name: 'GNSS receiver on board', measures: 'Orbital speed and altitude', range: '—', resolution: '±0.1 m/s' }, { name: 'High-speed camera (classroom analogue)', measures: 'Range against launch speed', range: '3 m', resolution: '2 mm' }],
    procedure: ['Tabulate altitude and speed at engine cut-off for several launches, orbital and sub-orbital.', 'Compare each cut-off speed with the circular, grazing and escape speeds at that altitude.', 'Check that the outcome (re-entry, orbit, escape) matches the predicted class and that the orbital period matches Kepler\'s third law.', 'In the classroom analogue, measure range against launch speed and show it is proportional to speed on a flat table.'],
    controls: ['Launches at the same altitude with different cut-off speeds isolate the role of speed', 'Compare low orbits affected by residual drag with higher ones'],
    signatures: ['Satellites at 300 km altitude moving at about 7.7 km/s with a period near 90 minutes', 'Sub-orbital stages with lower cut-off speed returning to the surface', 'Probes exceeding √2 times the circular speed leaving the Earth'],
    safety: ['Not a bench experiment at full scale: use published tracking data', 'Classroom launcher: eye protection and a cleared landing zone'],
  },
  falsify: ['A body above the atmosphere moving horizontally at the circular speed that nevertheless falls to the ground.', 'A satellite period that disagrees with 2π√(r³/GM) beyond perturbation effects.', 'A projectile and a satellite at the same place and velocity following different paths, which would show that celestial and terrestrial bodies obey different laws.'],
  alternatives: [{ name: 'Aristotelian separation of celestial and terrestrial motion', text: 'Held that heavenly bodies move naturally in circles while earthly ones fall; Newton\'s argument removes the distinction.' }, { name: 'General-relativistic description', text: 'The orbit is a geodesic of curved spacetime; for the Earth the corrections to Newton\'s result are parts in a billion.' }, { name: 'Real launch trajectories', text: 'Rockets climb through the atmosphere and build horizontal speed gradually; no gun can reach orbit because of drag and the need to circularise.' }],
  hazards: [{ hazard: 'Misapplication to guns', cause: 'Treating a ground-level launch as Newton\'s mountain', mitigation: 'Note that a ballistic shot from the surface always returns to its launch radius: an orbit needs a burn at altitude' }],
  standards: ['IAU 2015 Resolution B3 (nominal solar and planetary conversion constants)', 'ISO 24113 (space systems — space debris mitigation requirements)'],
  limits: 'Point-mass planet with no oblateness, no other attracting bodies, Newtonian mechanics. Drag, when enabled, uses a constant ballistic coefficient in an isothermal atmosphere that co-rotates with the planet. The mountain is an idealisation: no real mountain rises above the atmosphere.',
  numerics: { method: 'Closed-form conic-section classification; adaptive RK45 with Newton-located events (impact, completed revolution, departure) for each plotted shot', order: 5 },
  optimise: { objective: 'ecc', sense: 'min', vars: ['v_0'], note: 'The eccentricity is zero at the circular speed.' },
  inverse: { series: 'altitude', fit: ['v_0'] },
  extensions: ['Launch from the rotating Earth at a general latitude', 'Atmospheric drag decay of a low orbit', 'The Moon test: comparing the Moon\'s centripetal acceleration with g scaled by the inverse square'],
};

// ------------------------------------------------------------------ 14. Galileo's falling bodies
function galileoBodies(v, a) {
  const dia = m => Math.cbrt(6 * m / (Math.PI * v.rho_b)), d1 = dia(v.m_1), d2 = a.same_material ? dia(v.m_2) : d1;
  const A = d => Math.PI * d * d / 4, V = d => Math.PI * d ** 3 / 6, eta = a.equivalence ? 0 : v.eta;
  const mk = (m, mg, area, vol) => ({ m, area, vol, g0: v.g * mg / m - (a.no_buoyancy ? 0 : v.rho * v.g * vol / m), k: a.drag ? v.rho * v.C_D * area / (2 * m) : 0 });
  return { d1, d2, bodies: [mk(v.m_1, v.m_1, A(d1), V(d1)), mk(v.m_2, v.m_2 * (1 + eta), A(d2), V(d2)), mk(v.m_1 + v.m_2, v.m_1 + v.m_2 * (1 + eta), A(d1) + A(d2), V(d1) + V(d2))] };
}
/** Fall from rest through height h: closed form in a uniform field, numerical integration otherwise. */
function galileoFall(b, v, a, numeric = false) {
  const h = v.h_d;
  if (!(b.g0 > 0)) return { t: NaN, vf: 0, vt: 0, floats: true, y: () => h, u: () => 0 };
  if (a.uniform_g && !numeric) {
    if (b.k === 0) { const t = Math.sqrt(2 * h / b.g0); return { t, vf: b.g0 * t, vt: Infinity, y: s => Math.max(h - 0.5 * b.g0 * s * s, 0), u: s => b.g0 * Math.min(s, t) }; }
    const vt = Math.sqrt(b.g0 / b.k), u = b.g0 * h / (vt * vt), root = Math.sqrt(1 - Math.exp(-2 * u)), t = vt / b.g0 * (u + Math.log(1 + root));
    const lncosh = z => z + Math.log((1 + Math.exp(-2 * z)) / 2);
    return { t, vf: vt * root, vt, y: s => Math.max(h - vt * vt / b.g0 * lncosh(b.g0 * Math.min(s, t) / vt), 0), u: s => vt * Math.tanh(b.g0 * Math.min(s, t) / vt) };
  }
  const scale = y => (a.uniform_g ? 1 : (R_EARTH / (R_EARTH + Math.max(y, 0))) ** 2), ratio = b.g0 / v.g;
  const f = (t, s) => [-s[1], v.g * ratio * scale(s[0]) - b.k * s[1] * s[1]];
  const q = toEvent(f, [h, 0], 100 * Math.sqrt(2 * h / b.g0) + 100, s => s[0], s => -s[1], 201, { rtol: 1e-11, atol: 1e-12 });
  return { t: q.tHit, vf: q.yHit[1], vt: b.k > 0 ? Math.sqrt(b.g0 / b.k) : Infinity, y: s => (s >= q.tHit ? 0 : Math.max(N.interp1(q.t, q.y[0], s), 0)), u: s => N.interp1(q.t, q.y[1], Math.min(s, q.tHit)) };
}
const GAL_VAC = { drag: false, no_buoyancy: true, same_material: true, uniform_g: true, equivalence: true };
const galileo = {
  id: 'galileo-falling-bodies',
  title: 'Galileo\'s falling bodies',
  module: 1, klass: ['II', 'I'], domains: ['classical', 'logic'],
  keywords: ['galileo', 'falling bodies', 'tied bodies', 'heavier falls faster', 'leaning tower of pisa', 'free fall', 'aristotle', 'thought experiment', 'reductio', 'universality of free fall', 'equivalence principle', 'feather and hammer', 'drop two balls', 'do heavy objects fall faster', 'falling'],
  summary: 'Galileo\'s argument that heavier bodies cannot fall faster simply because they are heavier — the tied-bodies reductio — together with the computed fall of a heavy body, a light body and the two tied together, with and without air.',
  background: [
    'Aristotle held that bodies fall with speeds in proportion to their weights. In the Discorsi Galileo refuted this by pure reasoning. Tie a light stone to a heavy one. If lighter bodies fall more slowly, the light stone must retard the heavy one, so the pair falls more slowly than the heavy stone alone. But the pair is heavier than the heavy stone, so by the same doctrine it must fall faster. The doctrine contradicts itself; the only consistent conclusion is that weight alone does not set the speed of fall.',
    'Newtonian mechanics explains why: gravitational force is proportional to mass, and so is inertia, so in vacuum every body has the same acceleration. In air the fall does depend on the body, through the ratio of drag area to mass — which is why a tied pair of spheres really does fall slightly more slowly than the heavy sphere alone, without any contradiction, because the governing quantity is no longer weight.',
  ],
  phenomena: ['Free fall under uniform gravity', 'Equality of inertial and gravitational mass', 'Aerodynamic drag and terminal velocity', 'Buoyancy'],
  laws: ['newton2', 'gravitation', 'equivalence', 'logic_nc', 'archimedes'],
  refs: ['Galilei, G. (1638). Discorsi e dimostrazioni matematiche intorno a due nuove scienze, First Day. Elzevir, Leiden.', 'Aristotle (4th century BC). Physics, Book IV, and On the Heavens, Book I.', 'Gendler, T. S. (1998). Galileo and the indispensability of scientific thought experiment. British Journal for the Philosophy of Science 49, 397–424.', 'Norton, J. D. (1996). Are thought experiments just what you thought? Canadian Journal of Philosophy 26, 333–366.', 'Will, C. M. (2014). The confrontation between general relativity and experiment. Living Reviews in Relativity 17, 4.', 'Touboul, P. et al. (2017). MICROSCOPE mission: first results of a space test of the equivalence principle. Physical Review Letters 119, 231101.'],
  inputs: [
    inp('m_1', 'Mass of the heavy body', 'kg', 45, { min: 0.01, max: 1e4, aliases: ['heavy mass', 'heavy body', 'cannonball mass'], src: 'A hundred-pound cannonball, as in the Discorsi' }),
    inp('m_2', 'Mass of the light body', 'kg', 0.23, { min: 0.001, max: 1e4, aliases: ['light mass', 'light body', 'musket ball mass'], src: 'A half-pound musket ball, as in the Discorsi' }),
    inp('h_d', 'Height of the drop', 'm', 55, { min: 0.5, max: 5000, kind: 'geometry', aliases: ['height', 'drop height', 'tower height'], src: 'Approximate height of the Leaning Tower of Pisa' }),
    inp('rho_b', 'Density of the bodies', 'kg/m^3', 7870, { min: 100, max: 22000, kind: 'fluid', aliases: ['body density', 'density'], src: 'Iron' }),
    inp('C_D', 'Drag coefficient of a sphere', '1', 0.47, { min: 0.05, max: 2, kind: 'fluid', aliases: ['drag coefficient'], src: 'Smooth sphere at sub-critical Reynolds number' }),
    inp('rho', 'Air density', 'kg/m^3', 1.225, { min: 0.001, max: 2, kind: 'environment', env: 'air_density', aliases: ['air density'] }),
    inp('g', 'Gravitational acceleration', 'm/s^2', 9.80665, { min: 0.1, max: 30, kind: 'environment', env: 'gravity', aliases: ['gravity', 'gravitational acceleration'] }),
    inp('eta', 'Fractional excess of gravitational over inertial mass of the light body (hypothetical)', '1', 0.001, { min: 0, max: 0.1, kind: 'hypothetical', aliases: ['eotvos parameter', 'equivalence violation'], src: 'Invented for the counterfactual; experiments bound any such difference below about 10⁻¹⁴' }),
  ],
  assumptions: [
    asm('drag', 'The bodies fall through air and experience quadratic drag.', { why: 'A real drop from a tower', alt: 'The drop takes place in vacuum.' }),
    asm('no_buoyancy', 'The buoyancy of the air is neglected.', { why: 'Bodies far denser than air', alt: 'Each body is lightened by the weight of the air it displaces (Archimedes).' }),
    asm('same_material', 'Both bodies are solid spheres of the same material, so the lighter is also the smaller.', { why: 'Galileo\'s case of two stones or two iron balls', alt: 'The two bodies have the same diameter and differ only in mass (the lighter one is hollow).' }),
    asm('uniform_g', 'Gravity is uniform over the height of the drop.', { why: 'Height tiny against the Earth\'s radius', alt: 'Gravity varies with height as the inverse square of distance from the Earth\'s centre.' }),
    asm('equivalence', 'Gravitational and inertial mass are equal for every body.', { why: 'Universality of free fall, verified to parts in 10¹⁴', alt: 'Counterfactual: the light body has slightly more gravitational than inertial mass, so it falls faster even in vacuum.' }),
  ],
  symbols: { m: ['Mass of a falling body', 'kg'], v: ['Downward speed', 'm/s'], t: ['Time', 's'], y: ['Height above the ground', 'm'], A: ['Frontal area', 'm^2'], V_b: ['Volume of the body', 'm^3'], d_b: ['Diameter of the body', 'm'], v_t: ['Terminal velocity', 'm/s'], t_f: ['Time of fall', 's'], g_h: ['Gravitational acceleration at height', 'm/s^2'], g_e: ['Net downward acceleration without drag', 'm/s^2'], R_E: ['Earth radius', 'm'], t_A1: ['Aristotelian fall time of the heavy body', 's'], t_A2: ['Aristotelian fall time of the light body', 's'] },
  equations: a => {
    const g = a.uniform_g ? 'g' : 'g_h', plain = a.equivalence && a.no_buoyancy, ge = plain ? 'g' : 'g_e';
    return [
      eq('mom', 'Equation of motion of each body', 'm*d(v,t)', `m*${a.equivalence ? '' : '(1 + eta)*'}${g}${a.no_buoyancy ? '' : ` - rho*V_b*${g}`}${a.drag ? ' - 0.5*rho*C_D*A*v^2' : ''}`, { kind: 'law', origin: 'Newton\'s second law: weight, buoyancy and drag', needs: ['equivalence', 'no_buoyancy'].filter(k => a[k]), note: a.equivalence ? undefined : 'The factor (1 + η) applies to the light body only.' }),
      eq('kin', 'Kinematics', 'd(y,t)', '-v', { kind: 'definition' }),
      eq('mass', 'Mass of a solid sphere', 'm', 'rho_b*pi*d_b^3/6', { kind: 'definition' }),
      ...(a.drag ? [eq('area', 'Frontal area', 'A', 'pi*d_b^2/4', { kind: 'definition' })] : []),
      ...(a.no_buoyancy ? [] : [eq('vol', 'Volume', 'V_b', 'pi*d_b^3/6', { kind: 'definition' })]),
      ...(plain ? [] : [eq('ge', 'Net downward acceleration without drag', 'g_e', `${a.equivalence ? '' : '(1 + eta)*'}g${a.no_buoyancy ? '' : ' - rho*V_b*g/m'}`, { kind: 'derived', origin: a.no_buoyancy ? 'Weight per unit inertial mass' : 'Weight less buoyancy, per unit inertial mass', note: a.equivalence ? undefined : 'The factor (1 + η) applies to the light body only.' })]),
      ...(a.drag ? [eq('vt', 'Terminal velocity', 'v_t', `sqrt(2*m*${ge}/(rho*C_D*A))`, { kind: 'derived', origin: plain ? 'Drag equals weight' : 'Drag equals the net downward force' })] : []),
      ...(a.uniform_g ? [a.drag ? eq('tf', 'Time of fall with quadratic drag', 't_f', `v_t/${ge}*ln(exp(${ge}*h_d/v_t^2) + sqrt(exp(2*${ge}*h_d/v_t^2) - 1))`, { kind: 'derived', origin: 'Closed-form integral of the equation of motion', needs: ['uniform_g'] })
        : eq('tf', 'Time of fall in vacuum', 't_f', `sqrt(2*h_d/${ge})`, { kind: 'derived', origin: plain ? 'Uniform acceleration from rest: independent of mass' : 'Uniform acceleration from rest', needs: ['uniform_g'] })]
        : [eq('grav', 'Gravity with height', 'g_h', 'g*(R_E/(R_E + y))^2', { kind: 'law', origin: 'Newton\'s law of gravitation' })]),
      eq('aris', 'Aristotelian doctrine under test', 't_A2/t_A1', 'm_1/m_2', { kind: 'hypothesis', origin: 'Aristotle: speed of fall proportional to weight. Shown to be self-contradictory by the tied-bodies argument and refuted by experiment.' }),
    ];
  },
  derivation: a => [
    { text: 'Suppose, with Aristotle, that heavier bodies fall faster than lighter ones (A). Tie a light body to a heavy one. The slower light body must hold the heavy one back, so the pair falls more slowly than the heavy body alone (S).', tex: 'A \\Rightarrow S' },
    { text: 'But the pair together weighs more than the heavy body alone, so by the same supposition it must fall faster than the heavy body alone (F).', tex: 'A \\Rightarrow F' },
    { text: 'The pair cannot fall both faster and slower than the heavy body. The supposition has produced a contradiction, so it is false.', tex: '\\lnot(S\\wedge F)\\quad\\therefore\\quad \\lnot A' },
    { text: 'Newton\'s laws give the positive result. The gravitational force is proportional to the mass and so is the inertia, so the mass cancels: in vacuum all bodies have the same acceleration.', tex: 'm\\,\\dot v = m\\,g\\quad\\Rightarrow\\quad \\dot v = g,\\qquad t_f = \\sqrt{2h/g}' },
    ...(a.drag ? [{ text: 'In air a drag force acts that does not scale with mass. The acceleration then depends on the ratio of area to mass, and each body approaches its own terminal velocity. The equation integrates in closed form.', tex: '\\dot v = g\\left(1 - \\frac{v^2}{v_t^2}\\right),\\qquad v_t = \\sqrt{\\frac{2mg}{\\rho C_D A}},\\qquad t_f = \\frac{v_t}{g}\\,\\mathrm{arcosh}\\!\\left(e^{gh/v_t^2}\\right)' },
      { text: 'For the tied pair the masses and the drag areas both add, so its area-to-mass ratio lies between those of the two bodies: it falls slightly more slowly than the heavy body and faster than the light one. There is no contradiction, because what matters is not weight but weight per unit drag area.', tex: 'v_{t,pair}^2 = \\frac{2(m_1+m_2)g}{\\rho C_D(A_1+A_2)}' }] : []),
  ],
  solve(v, a) {
    const gb = galileoBodies(v, a), falls = gb.bodies.map(b => galileoFall(b, v, a)), [f1, f2, fp] = falls, warnings = [];
    const tfin = falls.map(f => f.t).filter(Number.isFinite), tvac = Math.sqrt(2 * v.h_d / v.g), tmax = N.maxOf(tfin), tmin = N.minOf(tfin), ts = N.linspace(0, tmax, 201);
    const fl = f2.floats ? { text: 'The light body is lighter than the air it displaces and does not fall' } : {};
    const tiedSlower = fp.t > f1.t * (1 + 1e-12), tiedFaster = fp.t < f1.t * (1 - 1e-12), heavyFirst = f1.t < f2.t * (1 - 1e-12);
    const verdict = !tiedSlower && !tiedFaster ? 'All three land together: the tied pair is neither faster nor slower than the heavy body, exactly as the reductio requires.'
      : tiedSlower ? `The tied pair lands ${lab((fp.t - f1.t) * 1000, 'ms')} after the heavy body: it is slower, not faster, although it is heavier. Weight alone does not decide the speed of fall.`
        : `The tied pair lands ${lab((f1.t - fp.t) * 1000, 'ms')} before the heavy body.`;
    if (!a.equivalence) warnings.push('The equivalence principle has been switched off as a counterfactual. No such difference between gravitational and inertial mass has been observed; the results are conditional on the invented value.');
    if (a.drag && v.h_d > 1000) warnings.push('Over a drop this high the air density changes appreciably; a constant density is assumed.');
    if (f2.floats) warnings.push('With buoyancy included the light body weighs less than the air it displaces, so it does not fall at all.');
    if (v.m_2 > v.m_1) warnings.push('The body labelled light is heavier than the one labelled heavy; the labels follow the inputs.');
    const fin = x => (Number.isFinite(x) ? x : NaN), nov = a.drag ? {} : { text: 'None: there is no drag in vacuum' };
    const fs = N.linspace(0, tmax, 81);
    return {
      scalars: [
        scalar('t_1', 'Time of fall of the heavy body', f1.t, 's'), scalar('t_2', 'Time of fall of the light body', f2.t, 's', fl), scalar('t_p', 'Time of fall of the two bodies tied together', fp.t, 's'),
        scalar('t_vac', 'Time of fall in vacuum', tvac, 's'), scalar('dt_21', 'Lag of the light body behind the heavy one', f2.t - f1.t, 's', { show: 'ms', ...fl }), scalar('dt_p1', 'Lag of the tied pair behind the heavy body', fp.t - f1.t, 's', { show: 'ms' }),
        scalar('gap', 'Height of the light body when the heavy one lands', f2.y(f1.t), 'm'),
        scalar('v_1', 'Impact speed of the heavy body', f1.vf, 'm/s'), scalar('v_2', 'Impact speed of the light body', f2.vf, 'm/s'),
        scalar('v_t1', 'Terminal velocity of the heavy body', fin(f1.vt), 'm/s', nov), scalar('v_t2', 'Terminal velocity of the light body', fin(f2.vt), 'm/s', nov), scalar('v_tp', 'Terminal velocity of the tied pair', fin(fp.vt), 'm/s', nov),
        scalar('d_1', 'Diameter of the heavy body', gb.d1, 'm', { show: 'mm' }), scalar('d_2', 'Diameter of the light body', gb.d2, 'm', { show: 'mm' }),
        scalar('ratio_A', 'Aristotelian prediction for the ratio of fall times, light to heavy', v.m_1 / v.m_2, '1', { status: 'hypothetical' }), scalar('ratio_obs', 'Computed ratio of fall times, light to heavy', f2.t / f1.t, '1', fl),
        scalar('tied', 'Tied pair compared with the heavy body alone', tiedSlower ? -1 : tiedFaster ? 1 : 0, '1', { text: verdict }),
        scalar('first', 'Which body lands first', heavyFirst ? 1 : f2.t < f1.t * (1 - 1e-12) ? 2 : 0, '1', { text: f2.floats ? 'The heavy body; the light body does not fall' : heavyFirst ? 'The heavy body, by a margin set by air resistance' : f2.t < f1.t * (1 - 1e-12) ? 'The light body' : 'They land together' }),
      ],
      series: [
        line('height', 'Height against time', 'Time', 's', ts, [{ label: 'Heavy body', data: ts.map(f1.y) }, { label: 'Light body', data: ts.map(f2.y) }, { label: 'Tied pair', data: ts.map(fp.y) }, { label: 'Vacuum', data: ts.map(t => Math.max(v.h_d - 0.5 * v.g * t * t, 0)), dash: true }], 'Height', 'm'),
        line('speed', 'Speed against time', 'Time', 's', ts, [{ label: 'Heavy body', data: ts.map(f1.u) }, { label: 'Light body', data: ts.map(f2.u) }, { label: 'Tied pair', data: ts.map(fp.u) }, { label: 'Vacuum', data: ts.map(t => v.g * Math.min(t, tvac)), dash: true }], 'Speed', 'm/s'),
        line('separation', 'Separation between the bodies', 'Time', 's', ts, [{ label: 'Light body above heavy body', data: ts.map(t => f2.y(t) - f1.y(t)) }, { label: 'Tied pair above heavy body', data: ts.map(t => fp.y(t) - f1.y(t)) }], 'Separation', 'm'),
        line('aristotle', 'Ratio of fall times against mass ratio', 'Mass ratio, heavy to light', '–', N.logspace(1, 1000, 40), [{ label: 'Aristotelian doctrine', data: N.logspace(1, 1000, 40) }, { label: 'Computed', data: N.logspace(1, 1000, 40).map(q => { const w = { ...v, m_2: v.m_1 / q }, bb = galileoBodies(w, a).bodies; return a.uniform_g ? galileoFall(bb[1], w, a).t / galileoFall(bb[0], w, a).t : f2.t / f1.t; }) }], 'Fall time of light body / heavy body', '–', { logx: true, logy: true, status: 'hypothetical' }),
      ],
      anims: [motion('drop', 'The three drops side by side', fs.map(t => [[-1, f1.y(t)], [0, f2.y(t)], [1, fp.y(t)]]), fs, { labels: ['Heavy body', 'Light body', 'Tied pair'], bounds: [-2, 2, 0, v.h_d], unit: 'm' })],
      checks: [
        check('Vacuum fall is independent of mass', a.drag || !a.equivalence || !a.no_buoyancy ? 0 : (tmax - tmin) / tvac, 1e-12, a.drag || !a.equivalence || !a.no_buoyancy ? 'Not applicable with the present assumptions' : 'Spread of the three fall times'),
        check('Tied pair lies between its parts', fp.t > Math.max(f1.t, f2.t) * (1 + 1e-9) || fp.t < Math.min(f1.t, f2.t) * (1 - 1e-9) ? 1 : 0, 0, 'The combined body cannot be faster than both or slower than both'),
        check('Energy balance of the heavy body', a.uniform_g ? (gb.bodies[0].g0 * v.h_d - 0.5 * f1.vf ** 2 - (gb.bodies[0].k > 0 ? N.trapz(ts.filter(t => t <= f1.t), ts.filter(t => t <= f1.t).map(t => gb.bodies[0].k * f1.u(t) ** 3)) : 0)) / (gb.bodies[0].g0 * v.h_d) : 0, 5e-3, 'Potential energy released against kinetic energy and drag work'),
      ],
      warnings,
      notes: [verdict],
    };
  },
  benchmarks(v) {
    const vac = galileoBodies(v, GAL_VAC).bodies, air = { ...GAL_VAC, drag: true }, b = galileoBodies(v, air).bodies[1];
    const cf = galileoFall(b, v, air), nm = galileoFall(b, v, air, true), tall = galileoFall(b, { ...v, h_d: 50 * cf.vt ** 2 / v.g }, air);
    return [
      bench('Vacuum fall time of the heavy body', galileoFall(vac[0], v, GAL_VAC, true).t, Math.sqrt(2 * v.h_d / v.g), 't = √(2h/g), integrated numerically', 1e-9),
      bench('Vacuum fall: ratio of light-body to heavy-body time', galileoFall(vac[1], v, GAL_VAC).t / galileoFall(vac[0], v, GAL_VAC).t, 1, 'Universality of free fall', 1e-12),
      bench('Fall with quadratic drag: numerical integration vs closed form (time)', nm.t, cf.t, 't = (v_t/g) arcosh(exp(gh/v_t²))', 1e-8),
      bench('Fall with quadratic drag: numerical integration vs closed form (impact speed)', nm.vf, cf.vf, 'v = v_t √(1 − exp(−2gh/v_t²))', 1e-8),
      bench('Impact speed after a very long fall approaches terminal velocity', tall.vf, cf.vt, 'Limit h ≫ v_t²/g', 1e-9),
    ];
  },
  validation: [],
  logicPreset: {
    atoms: [
      { k: 'A', text: 'Heavier bodies fall faster than lighter ones.' },
      { k: 'S', text: 'The tied pair falls slower than the heavy body alone.' },
      { k: 'Fst', text: 'The tied pair falls faster than the heavy body alone.' },
    ],
    premises: ['A -> S', 'A -> Fst', '~(S & Fst)'],
    conclusion: '~A',
  },
  diagram(v, a) {
    const gb = galileoBodies(v, a), r1 = 16, r2 = Math.max(4, Math.min(16, 16 * gb.d2 / gb.d1));
    return svg(`
      ${S.path('M60 320 L600 320', 'd-ground')}
      ${S.path('M90 320 L110 60 L170 60 L190 320 Z', 'd-body')} ${S.text(140, 50, `tower, ${lab(v.h_d, 'm')}`, 'd-text d-small')}
      ${S.circle(270, 90, r1, 'd-body')} ${S.text(270, 60, 'heavy', 'd-text d-small')} ${S.arrow(270, 112, 270, 170)}
      ${S.circle(370, 90, r2, 'd-body')} ${S.text(370, 60, 'light', 'd-text d-small')} ${S.arrow(370, 112, 370, 170)}
      ${S.circle(480, 96, r1, 'd-body')} ${S.circle(480, 96 - r1 - r2 - 10, r2, 'd-body')} ${S.line(480, 96 - r1, 480, 96 - r1 - 10, 'd-line')} ${S.text(480, 44, 'tied together', 'd-text d-small')} ${S.arrow(480, 118, 480, 170)}
      ${S.text(270, 200, `${lab(v.m_1, 'kg')}`, 'd-text d-small')} ${S.text(370, 200, `${lab(v.m_2, 'kg')}`, 'd-text d-small')} ${S.text(480, 200, `${lab(v.m_1 + v.m_2, 'kg')}`, 'd-text d-small')}
      ${S.rect(220, 232, 330, 58, 'd-hazard', 6)}
      ${S.text(385, 254, 'If heavier fell faster: the pair is heavier, so faster;', 'd-text d-small')} ${S.text(385, 274, 'yet the light body drags, so slower. Contradiction.', 'd-text d-small')}
      ${S.text(320, 345, a.drag ? 'in air the difference comes from drag area per unit mass, not from weight' : 'in vacuum all three land together', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Test whether the time of fall depends on mass, in air and in vacuum, and separate the effect of air resistance from any dependence on weight.',
    apparatus: ['Two spheres of the same material and very different mass, and a third pair of equal diameter but different mass (one hollow)', 'Electromagnetic or pneumatic release dropping both bodies simultaneously', 'Drop tower or stairwell of known height, and an evacuable drop tube about 1.5 m long with a vacuum pump', 'A light cord to tie two bodies together'],
    instruments: [{ name: 'High-speed camera viewing the landing plane', measures: 'Difference in arrival time', range: '—', resolution: '1 ms at 1000 frames/s' }, { name: 'Impact microphones or contact switches', measures: 'Arrival times', range: '0–5 s', resolution: '0.1 ms' }, { name: 'Pirani or capacitance vacuum gauge', measures: 'Residual pressure in the drop tube', range: '1–10⁵ Pa', resolution: '±5 %' }, { name: 'Laser distance meter', measures: 'Drop height', range: '0–60 m', resolution: '±2 mm' }],
    procedure: ['Release the heavy and light spheres together in air from several heights and record the arrival-time difference.', 'Repeat with the equal-diameter pair to show that the difference follows mass per unit area, not mass.', 'Tie the light sphere to the heavy one and compare its time with that of the heavy sphere alone.', 'Repeat in the evacuated tube at decreasing pressure and plot the time difference against pressure.'],
    controls: ['Swap release positions to remove release-mechanism bias', 'Drop two identical bodies to measure the timing scatter', 'Vary drop height: the drag-induced lag must grow faster than linearly with height'],
    signatures: ['A small arrival-time difference in air that shrinks toward zero as the tube is evacuated', 'Equal-diameter bodies of different mass separating more than same-material bodies', 'The tied pair arriving between the times of its two parts'],
    safety: ['Cordon off the landing area; use a sand box to arrest heavy bodies', 'Implosion guard on glass vacuum tubes', 'Secure release gear and personnel working at height'],
  },
  falsify: ['Bodies of different mass falling at different rates in a good vacuum, beyond experimental error, which would violate the universality of free fall.', 'A time difference in air that does not vanish as the air is removed.', 'A tied pair observed to fall faster than both of its parts or slower than both.'],
  alternatives: [{ name: 'Aristotelian dynamics', text: 'Speed of fall proportional to weight and inversely to the resistance of the medium; self-contradictory under the tied-bodies argument and refuted by experiment.' }, { name: 'Philoponus and impetus theory', text: 'Sixth-century observation that bodies of very different weight land almost together; a precursor of Galileo\'s conclusion.' }, { name: 'Equivalence-principle violations', text: 'Some theories beyond general relativity predict composition-dependent free fall at a level far below present bounds of about 10⁻¹⁴–10⁻¹⁵.' }, { name: 'Objection to the reductio', text: 'It has been argued that the argument assumes natural speed is determined by weight alone and that tying bodies makes a single body; the argument rules out that specific doctrine, not every conceivable dependence on properties other than weight.' }],
  hazards: [{ hazard: 'Falling objects', cause: 'Heavy bodies dropped from height', mitigation: 'Exclusion zone, catch box, hard hats' }, { hazard: 'Vacuum-tube implosion', cause: 'Damaged glass under external pressure', mitigation: 'Guard, inspection, safety screen' }],
  standards: ['ISO 80000-3 (quantities and units — space and time)', 'ISO/IEC Guide 98-3 (uncertainty of measurement — guide to the expression of uncertainty in measurement)'],
  limits: 'Rigid spheres falling from rest without rotation; constant drag coefficient and air density; the drag areas of tied bodies are simply added, ignoring the wake of one on the other. The logical argument is propositional: it shows that the doctrine "heavier bodies fall faster" is inconsistent with the two consequences drawn from it.',
  numerics: { method: 'Closed-form solution for quadratic drag in a uniform field; adaptive RK45 with Newton-located landing when gravity varies with height' },
  optimise: { objective: 'dt_21', sense: 'min', vars: ['rho'], note: 'The lag between the bodies vanishes as the air is removed.' },
  inverse: { series: 'height', fit: ['C_D', 'g'] },
  extensions: ['Reynolds-number-dependent drag and the drag crisis', 'Torsion-balance and satellite tests of the equivalence principle', 'Einstein\'s lift: from the universality of free fall to the equivalence principle'],
};

export default [wing, nozzle, rocket, hohmann, entry, twoBody, threeBody, projectile, pendulum, doublePendulum, sdof, collision, cannonball, galileo];
