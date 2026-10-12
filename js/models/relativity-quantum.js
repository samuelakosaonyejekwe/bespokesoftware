// Special and general relativity, cosmology, counterfactual gravity and quantum mechanics.
import { inp, konst, asm, eq, scalar, line, anim, check, bench, svg, S, lab, N, R, C } from './kit.js';

const c = C.c, G = C.G, hbar = C.hbar, kB = C.k_B, c2 = c * c;
const YR = 3.15576e7, LY = 9.4607304725808e15, AU = 1.495978707e11, EV = 1.602176634e-19, AMU = 1.66053906660e-27;
const SUN = R.BODIES.sun, EARTH = R.BODIES.earth;
const ARCSEC = 180 * 3600 / Math.PI; // arcseconds per radian
const val = (r, s) => r.scalars.find(q => q.sym === s).value;
/** Composite Simpson rule on n (even) intervals. */
const simpson = (f, a, b, n = 400) => { const h = (b - a) / n; let s = f(a) + f(b); for (let i = 1; i < n; i++) s += (i % 2 ? 4 : 2) * f(a + i * h); return s * h / 3; };
/** Midpoint rule: avoids the end points, so integrands with removable end-point limits need no special case. */
const midpoint = (f, a, b, n = 400) => { const h = (b - a) / n; let s = 0; for (let i = 0; i < n; i++) s += f(a + (i + 0.5) * h); return s * h; };
/** Final state of an adaptive integration, taken from the last recorded sample (always at the end time). */
const lastState = sol => sol.y.map(q => q[q.length - 1]);

// ================================================================== 1. twin paradox
function twinWorldline(v, a) {
  const L = v.L, rel = a.relativistic, m = 40;
  let beta = Math.min(v.v / c, 0.999999), gam = rel ? 1 / Math.sqrt(1 - beta * beta) : 1;
  let tA = 0, tauA = 0, xA = 0, limited = false;
  const ap = v.a_p;
  if (!a.instant) {
    if (rel) {
      const gMax = 1 + ap * L / (2 * c2);
      if (gam > gMax) { gam = gMax; beta = Math.sqrt(1 - 1 / (gam * gam)); limited = true; }
      tA = gam * beta * c / ap; tauA = c / ap * Math.atanh(beta); xA = c2 / ap * (gam - 1);
    } else {
      const vMax = Math.sqrt(ap * L);
      if (beta * c > vMax) { beta = vMax / c; limited = true; }
      tA = beta * c / ap; tauA = tA; xA = beta * c * tA / 2;
    }
  }
  const vp = beta * c, Lc = Math.max(L - 2 * xA, 0), tC = Lc / vp, tauC = tC / gam;
  const tHalf = 2 * tA + tC, tauHalf = 2 * tauA + tauC;
  const ft = s => (a.instant ? 0 : rel ? c / ap * Math.sinh(ap * s / c) : s);
  const fx = s => (a.instant ? 0 : rel ? c2 / ap * (Math.cosh(ap * s / c) - 1) : 0.5 * ap * s * s);
  const t = [], x = [], tau = [];
  for (let i = 0; i < m; i++) { const s = tauA * i / (m - 1); t.push(ft(s)); x.push(fx(s)); tau.push(s); }
  for (let i = 0; i < m; i++) { const q = i / (m - 1); t.push(tA + tC * q); x.push(xA + Lc * q); tau.push(tauA + tauC * q); }
  for (let i = 0; i < m; i++) { const s = tauA * (1 - i / (m - 1)); t.push(tHalf - ft(s)); x.push(L - fx(s)); tau.push(tauHalf - s); }
  for (let i = 3 * m - 1; i >= 0; i--) { t.push(2 * tHalf - t[i]); x.push(x[i]); tau.push(2 * tauHalf - tau[i]); }
  return { t, x, tau, T: 2 * tHalf, tauT: 2 * tauHalf, beta, gam, limited, tHalf, tauHalf, tauA, tA, xA };
}

const twin = {
  id: 'twin-paradox-time-dilation',
  title: 'Twin paradox and time dilation',
  module: [1, 2], klass: ['I', 'II'], domains: ['relativity'],
  keywords: ['twin paradox', 'twins paradox', 'time dilation', 'travelling twin', 'lorentz factor', 'proper time', 'muon lifetime', 'ageing', 'aging', 'spaceship clock', 'minkowski diagram', 'relativistic doppler', 'special relativity', 'clock paradox', 'round trip'],
  summary: 'An out-and-back journey at relativistic speed: proper time of each twin, the spacetime diagram and the Doppler-signal bookkeeping that removes the apparent paradox.',
  background: [
    'Special relativity assigns to every clock the proper time measured along its own worldline, dτ² = dt² − dx²/c². Two clocks that separate and reunite have followed different worldlines between the same two events and in general record different elapsed times; the straight (inertial) worldline is the longest. This is an established result, confirmed by the lifetimes of fast muons, by atomic clocks flown in aircraft and by every satellite navigation system.',
    'The "paradox" arises from the claim that, since each twin sees the other\'s clock run slow, the situation is symmetric. It is not: the travelling twin changes inertial frame at the turnaround and the stay-at-home twin does not. Counting the light signals each twin receives from the other makes the asymmetry explicit without any appeal to acceleration acting on the clock itself.',
  ],
  phenomena: ['Time dilation', 'Relativity of simultaneity', 'Relativistic Doppler effect', 'Length contraction', 'Hyperbolic motion under constant proper acceleration'],
  laws: ['sr', 'causality'],
  refs: ['Einstein, A. (1905). Zur Elektrodynamik bewegter Körper. Annalen der Physik 17, 891–921.', 'Bailey, J. et al. (1977). Measurements of relativistic time dilatation for positive and negative muons in a circular orbit. Nature 268, 301–305.', 'Hafele, J. C. & Keating, R. E. (1972). Around-the-world atomic clocks: observed relativistic time gains. Science 177, 168–170.', 'Taylor, E. F. & Wheeler, J. A. (1992). Spacetime Physics, 2nd ed., W. H. Freeman.', 'Rindler, W. (2006). Relativity: Special, General, and Cosmological, 2nd ed., Oxford University Press.'],
  inputs: [
    inp('v', 'Cruise speed relative to the stay-at-home twin', 'm/s', 0.8 * c, { min: 3e5, max: 0.9995 * c, aliases: ['speed', 'velocity'], src: '0.8 c, a conventional textbook choice (Lorentz factor 5/3)' }),
    inp('L', 'One-way distance in the home frame', 'ly', 4, { min: 0.01, max: 1000, kind: 'geometry', aliases: ['distance', 'light years', 'light-years', 'away', 'far'] }),
    inp('a_p', 'Proper acceleration during speed changes', 'm/s^2', 9.80665, { min: 0.5, max: 1000, aliases: ['acceleration', 'turnaround acceleration'], src: 'One standard gravity; used only when the instantaneous-turnaround assumption is removed' }),
    inp('f_s', 'Rate at which each twin emits light signals (own clock)', '1/yr', 1, { min: 0.1, max: 100, aliases: ['signal rate', 'signals per year', 'pulses'] }),
    inp('tau_0', 'Rest-frame lifetime of a clock particle carried at the cruise speed', 'us', 2.1969811, { min: 1e-4, max: 1e6, kind: 'material', aliases: ['lifetime', 'mean life', 'muon'], src: 'Muon mean lifetime, Particle Data Group' }),
  ],
  assumptions: [
    asm('relativistic', 'Clocks record proper time along their worldlines, as special relativity requires.', { why: 'Established by experiment', alt: 'Newtonian absolute time: every clock records the same elapsed time whatever its motion.' }),
    asm('instant', 'Departure, turnaround and arrival are instantaneous changes of velocity.', { why: 'Isolates the kinematic effect', alt: 'Every speed change takes place at the finite constant proper acceleration a_p (hyperbolic motion), with coasting in between if the distance allows.' }),
    asm('earth_inertial', 'The stay-at-home twin is inertial: the gravity and orbital motion of the Earth are neglected.', { why: 'These effects are parts in 10⁸', alt: 'The home clock rate is reduced by the gravitational potentials of the Earth and Sun and by the Earth\'s orbital speed (weak-field expression).' }),
  ],
  symbols: { gamma: ['Lorentz factor', '1'], T: ['Trip duration in the home frame', 's'], tau_t: ['Proper time of the travelling twin', 's'], tau_h: ['Proper time of the stay-at-home twin', 's'], tau: ['Proper time', 's'], t: ['Home-frame coordinate time', 's'], x: ['Home-frame position', 'm'], f_r: ['Received signal rate', '1/s'], tau_a: ['Proper time of one acceleration phase', 's'], x_a: ['Distance covered in one acceleration phase', 'm'], tau_lab: ['Dilated lifetime in the home frame', 's'], Phi_E: ['Magnitude of the gravitational potential at the home clock', 'J/kg'], v_E: ['Orbital speed of the Earth', 'm/s'], N_r: ['Signals received over the trip', '1'] },
  equations: a => [
    a.relativistic
      ? eq('interval', 'Proper time along a worldline', 'c^2*d(tau,t)^2', 'c^2 - d(x,t)^2', { kind: 'law', origin: 'Invariance of the spacetime interval (Einstein 1905; Minkowski 1908)' })
      : eq('interval', 'Absolute time', 'd(tau,t)', '1', { kind: 'hypothesis', origin: 'Newtonian kinematics, retained only for contrast; refuted by experiment' }),
    ...(a.relativistic ? [eq('gamma', 'Lorentz factor', 'gamma', '1/sqrt(1 - v^2/c^2)', { kind: 'definition' })] : []),
    a.instant
      ? eq('T', 'Home-frame trip duration', 'T', '2*L/v', { kind: 'derived', origin: 'Uniform motion out and back', needs: ['instant'] })
      : eq('T', 'Home-frame trip duration with four acceleration phases', 'T', '2*(L - 2*x_a)/v + 4*gamma*v/a_p', { kind: 'derived', origin: 'Hyperbolic motion joined to uniform coasting' }),
    ...(a.instant ? [] : [
      eq('taua', 'Proper time of one acceleration phase', 'tau_a', 'c/(2*a_p)*ln((1 + v/c)/(1 - v/c))', { kind: 'derived', origin: 'Rapidity grows linearly with proper time at constant proper acceleration' }),
      eq('xa', 'Distance covered while accelerating', 'x_a', 'c^2/a_p*(gamma - 1)', { kind: 'derived', origin: 'Hyperbolic motion' }),
    ]),
    a.relativistic
      ? (a.instant ? eq('taut', 'Traveller\'s elapsed proper time', 'tau_t', 'T/gamma', { kind: 'derived', origin: 'Integral of the interval along the two straight legs', needs: ['relativistic', 'instant'] })
        : eq('taut', 'Traveller\'s elapsed proper time', 'tau_t', '2*(L - 2*x_a)/(gamma*v) + 4*tau_a', { kind: 'derived', origin: 'Integral of the interval along coasting and accelerated segments', needs: ['relativistic'] }))
      : eq('taut', 'Traveller\'s elapsed time', 'tau_t', 'T', { kind: 'hypothesis', origin: 'Absolute time' }),
    a.earth_inertial
      ? eq('tauh', 'Home twin\'s elapsed proper time', 'tau_h', 'T', { kind: 'derived', origin: 'Inertial clock at rest in the home frame', needs: ['earth_inertial'] })
      : eq('tauh', 'Home twin\'s elapsed proper time', 'tau_h', 'T*(1 - Phi_E/c^2 - v_E^2/(2*c^2))', { kind: 'derived', origin: 'Weak-field clock rate in a gravitational potential (Einstein 1911; Schwarzschild metric to first order)' }),
    ...(a.relativistic ? [
      eq('doppler', 'Received signal rate while receding', 'f_r', 'f_s*sqrt((1 - v/c)/(1 + v/c))', { kind: 'derived', origin: 'Relativistic longitudinal Doppler effect' }),
      eq('life', 'Dilated lifetime of a moving particle', 'tau_lab', 'gamma*tau_0', { kind: 'derived', origin: 'Time dilation' }),
    ] : [eq('doppler', 'Received signal rate while receding', 'f_r', 'f_s/(1 + v/c)', { kind: 'derived', origin: 'Classical Doppler effect for a receding source' })]),
    eq('count', 'Signals received equal signals sent', 'N_r', 'f_s*tau_h', { kind: 'law', origin: 'Every signal emitted is eventually received: counting is frame-independent' }),
  ],
  derivation: a => [
    { text: 'Each clock measures the invariant interval along its own worldline. In the home frame the travelling clock moves at speed v, so its rate is reduced by the Lorentz factor.', tex: '\\mathrm{d}\\tau = \\sqrt{1 - v^2/c^2}\\;\\mathrm{d}t = \\mathrm{d}t/\\gamma' },
    { text: a.instant ? 'With instantaneous speed changes the home-frame duration is the distance out and back divided by the speed, and the traveller\'s proper time is shorter by the factor γ.' : 'Each speed change is hyperbolic motion at proper acceleration a_p. Rapidity increases linearly with proper time, which gives the proper time, coordinate time and distance of each acceleration phase.', tex: a.instant ? 'T = \\frac{2L}{v},\\qquad \\tau_t = \\frac{2L}{\\gamma v}' : '\\tau_a = \\frac{c}{a_p}\\,\\mathrm{artanh}\\frac{v}{c},\\quad t_a = \\frac{\\gamma v}{a_p},\\quad x_a = \\frac{c^2}{a_p}(\\gamma-1)' },
    { text: 'Symmetry of time dilation holds only between two inertial frames. The traveller occupies one inertial frame outbound and a different one inbound; at the turnaround the traveller\'s line of simultaneity sweeps across a stretch of the home twin\'s worldline that neither inertial leg accounts for.', tex: '\\Delta t_{\\text{sweep}} = \\frac{2 v L}{c^2}' },
    { text: 'Signal counting removes any need to discuss simultaneity. The traveller receives home signals at the reduced Doppler rate for half of the journey (own time) and at the raised rate for the other half; the home twin receives the reduced rate until the light from the turnaround arrives, which is most of the trip.', tex: 'k = \\sqrt{\\frac{1+\\beta}{1-\\beta}},\\qquad N_{\\text{traveller receives}} = f_s\\frac{\\tau_t}{2}\\left(\\frac1k + k\\right) = f_s T' },
    { text: 'The home twin therefore sends f_s T signals and receives f_s τ_t; the traveller sends f_s τ_t and receives f_s T. Both agree on both numbers, and on who is younger at the reunion.', tex: '\\tau_h - \\tau_t = T\\left(1 - \\frac{1}{\\gamma}\\right)' },
  ],
  solve(v, a) {
    const w = twinWorldline(v, a), rel = a.relativistic, warnings = [];
    if (w.limited) warnings.push('The distance is too short to reach the requested cruise speed at this acceleration; the journey accelerates to the mid-point of each leg and the peak speed is lower.');
    let kh = 1;
    if (!a.earth_inertial) kh = 1 - (EARTH.GM / EARTH.radius + SUN.GM / AU) / c2 - (SUN.GM / AU) / (2 * c2);
    const tauH = w.T * kh, tauT = w.tauT, beta = w.beta, gam = w.gam;
    const kD = rel ? Math.sqrt((1 + beta) / (1 - beta)) : 1 + beta;
    // signals: a home signal emitted at t_e reaches the traveller when t - x/c = t_e
    const fs = v.f_s, recvT = w.t.map((t, i) => fs * kh * (t - w.x[i] / c)), iTurn = 3 * 40 - 1;
    const nOut = recvT[iTurn], nIn = recvT[recvT.length - 1] - nOut;
    const arrive = w.t.map((t, i) => t + w.x[i] / c); // home time at which a traveller signal emitted at tau arrives
    const fr = N.linspace(0, 1, 101);
    const recvHome = fr.map(q => fs * N.interp1(arrive, w.tau, q * w.T));
    const recvTrav = fr.map(q => N.interp1(w.tau, recvT, q * tauT));
    // proper time by direct summation of the interval along the sampled worldline
    let tauSum = 0;
    for (let i = 1; i < w.t.length; i++) { const dt = w.t[i] - w.t[i - 1], dx = w.x[i] - w.x[i - 1]; tauSum += rel ? Math.sqrt(Math.max(dt * dt - dx * dx / c2, 0)) : dt; }
    const tq = N.linspace(0, w.T, 121), tauOfT = tq.map(t => N.interp1(w.t, w.tau, t));
    // light signals for the diagram: four from home, evenly spaced
    const overlay = [{ label: 'Stay-at-home twin', x: [0, 0], y: [0, w.T / YR] }];
    for (let k = 1; k <= 4; k++) {
      const te = w.T * k / 6, j = recvT.findIndex(nr => nr >= fs * kh * te);
      if (j > 0) overlay.push({ label: k === 1 ? 'Light signals from home' : '', x: [0, w.x[j] / LY], y: [te / YR, w.t[j] / YR], dash: true });
    }
    return {
      scalars: [
        scalar('gamma', 'Lorentz factor at cruise', gam, '1'), scalar('beta', 'Cruise speed as a fraction of c', beta, '1'),
        scalar('T', 'Trip duration in the home frame', w.T, 's', { show: 'yr' }),
        scalar('tau_h', 'Stay-at-home twin ages by', tauH, 's', { show: 'yr' }), scalar('tau_t', 'Travelling twin ages by', tauT, 's', { show: 'yr' }),
        scalar('d_age', 'Age difference at reunion', tauH - tauT, 's', { show: 'yr', note: tauH > tauT ? 'the traveller is younger' : 'no difference' }),
        scalar('ratio', 'Traveller\'s elapsed time over home twin\'s', tauT / tauH, '1'),
        scalar('L_c', 'Distance in the traveller\'s cruise frame', v.L / gam, 'm', { show: 'ly' }),
        scalar('k_D', 'Doppler factor between the twins', kD, '1'),
        scalar('N_h', 'Signals sent by the home twin', fs * tauH, '1'), scalar('N_out', 'Home signals the traveller receives before turning round', nOut, '1'),
        scalar('N_in', 'Home signals the traveller receives on the way back', nIn, '1'), scalar('N_t', 'Signals sent by the traveller (all received at home)', fs * tauT, '1'),
        scalar('t_sweep', 'Home time swept by the change of simultaneity at turnaround', rel ? 2 * beta * v.L / c : 0, 's', { show: 'yr' }),
        scalar('tau_lab', 'Home-frame lifetime of the clock particle', gam * v.tau_0, 's', { show: 'us' }),
        scalar('tau_acc', 'Traveller\'s proper time spent accelerating', 4 * w.tauA, 's', { show: 'yr' }),
      ],
      series: [
        line('ageing', 'Elapsed time on each clock against home-frame time', 'Home-frame time', 'yr', tq.map(t => t / YR), [{ label: 'Stay-at-home twin', data: tq.map(t => t * kh / YR) }, { label: 'Travelling twin', data: tauOfT.map(t => t / YR) }], 'Elapsed proper time', 'yr'),
        line('minkowski', 'Spacetime diagram in the home frame', 'Position', 'ly', w.x.map(x => x / LY), [{ label: 'Travelling twin', data: w.t.map(t => t / YR) }], 'Home-frame time', 'yr', { overlay, note: 'Light travels along lines at 45° when distance is in light-years and time in years.' }),
        line('signals', 'Signals received from the other twin', 'Fraction of own elapsed time', '–', fr, [{ label: 'Received by the traveller', data: recvTrav }, { label: 'Received at home', data: recvHome }], 'Cumulative signals received', '–', { note: 'The traveller sees the rate change half-way through; the home twin sees it change late.' }),
      ],
      checks: [
        check('Proper time: summed interval against closed form', (tauSum - tauT) / tauT, 2e-3, 'Sum of √(Δt² − Δx²/c²) along the sampled worldline'),
        check('Signals from home: received equals sent', (recvT[recvT.length - 1] - fs * tauH) / (fs * tauH), 1e-9, 'Every signal sent during the trip is received before the reunion'),
        check('Traveller no older than the home twin', Math.max(0, tauT / tauH - 1), 1e-12, 'The inertial worldline has the greatest proper time'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], base = { ...v, v: 0.8 * c, L: 4 * LY }, on = { relativistic: true, instant: true, earth_inertial: true };
    const r = this.solve(base, on);
    out.push(bench('Lorentz factor at 0.8 c', val(r, 'gamma'), 5 / 3, 'Exact: γ = 1/√(1 − 0.64)', 1e-12));
    out.push(bench('Traveller\'s time for 4 ly at 0.8 c (years)', val(r, 'tau_t') / YR, 6, 'Exact: 2L/(γv) = 6 yr against 10 yr at home', 1e-9));
    const k = val(r, 'k_D');
    out.push(bench('Signals received by the traveller from Doppler rates', v.f_s * val(r, 'tau_t') / 2 * (1 / k + k), val(r, 'N_h'), 'k-calculus (Bondi): half the trip at rate f/k, half at rate f·k', 1e-9));
    const rf = this.solve(base, { ...on, instant: false }), g = 5 / 3, ap = v.a_p, xa = c2 / ap * (g - 1);
    out.push(bench('Finite-acceleration proper time against closed form', val(rf, 'tau_t'), xa * 2 < 4 * LY ? 2 * (4 * LY - 2 * xa) / (g * 0.8 * c) + 4 * c / ap * Math.atanh(0.8) : val(rf, 'tau_t'), 'Hyperbolic motion joined to coasting', 1e-9));
    return out;
  },
  validation: [
    { name: 'Lifetime of muons in the CERN storage ring', ref: 'Bailey, J. et al. (1977) Nature 268, 301–305', note: 'Muons circulating at γ ≈ 29.33; quoted values rounded. Tests time dilation for the accelerated (circular) case as well.',
      cases: [{ label: 'γ = 29.33', inputs: { v: c * Math.sqrt(1 - 1 / 29.33 ** 2), tau_0: 2.1969811e-6 }, observable: 'tau_lab', observed: 64.4e-6, sigma: 0.1e-6 }] },
  ],
  diagram(v, a) {
    const beta = Math.min(v.v / c, 0.9999), x1 = 150 + 300 * beta * 0.5;
    return svg(`
      ${S.line(150, 320, 150, 30, 'd-line')} ${S.arrow(150, 320, 540, 320)} ${S.arrow(150, 320, 150, 28)}
      ${S.text(548, 338, 'x', 'd-text', 'end')} ${S.text(138, 36, 'ct', 'd-text', 'end')}
      ${S.path(`M150 320 L${150 + 150} ${320 - 150}`, 'd-dim')} ${S.text(310, 180, 'light', 'd-text d-small', 'start')}
      ${a.instant ? S.poly([[150, 320], [x1, 175], [150, 30]], 'd-pipe') : S.path(`M150 320 Q${x1 + 20} 175 150 30`, 'd-pipe')}
      ${[1, 2, 3, 4].map(k => S.path(`M150 ${320 - 58 * k} L${150 + (k <= 2 ? 40 * k : 40 * (5 - k) * 0.6)} ${320 - 58 * k - (k <= 2 ? 40 * k : 40 * (5 - k) * 0.6)}`, 'd-dim')).join('')}
      ${S.circle(150, 320, 4, 'd-body')} ${S.circle(150, 30, 4, 'd-body')} ${S.circle(x1, 175, 4, 'd-hazard')}
      ${S.text(140, 180, 'home twin', 'd-text', 'end')} ${S.text(x1 + 12, 150, 'traveller', 'd-text', 'start')} ${S.text(x1 + 12, 200, 'turnaround', 'd-text d-small', 'start')}
      ${S.text(400, 60, `v = ${lab(beta, 'c')}   L = ${lab(v.L / LY, 'ly')}`, 'd-text', 'start')}
      ${S.text(400, 82, `γ = ${lab(1 / Math.sqrt(1 - beta * beta))}`, 'd-text', 'start')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'H', text: 'The stay-at-home twin remains in one inertial frame' }, { k: 'V', text: 'The travelling twin remains in one inertial frame throughout' }, { k: 'S', text: 'The situations of the two twins are symmetric' }, { k: 'E', text: 'The twins have aged equally at the reunion' }],
    premises: ['S <-> (H & V)', 'S -> E', 'H', '~V'],
    conclusion: '~S',
  },
  experiment: {
    objective: 'Compare the elapsed time of a moving clock with an identical clock at rest and test the factor 1/γ.',
    apparatus: ['Storage ring holding relativistic muons (as at CERN), or', 'Two or more caesium or optical atomic clocks, one flown on an aircraft or satellite and one kept at the ground station', 'Time-transfer link (two-way satellite or optical fibre)'],
    instruments: [{ name: 'Decay-electron counters around the ring', measures: 'Muon decay rate against laboratory time', range: '0–700 µs', resolution: '≈ 10 ns' }, { name: 'Optical-lattice or caesium clocks', measures: 'Accumulated phase (elapsed proper time)', range: 'continuous', resolution: 'fractional 10⁻¹⁸ to 10⁻¹³' }, { name: 'Magnetic-field NMR probes', measures: 'Ring field, hence γ', range: '≈ 1.5 T', resolution: 'parts per million' }],
    procedure: ['Measure the momentum of the stored muons from the ring field and orbit radius to fix γ.', 'Fit an exponential to the decay-electron count against laboratory time to obtain the laboratory lifetime.', 'Compare with γ times the lifetime of muons at rest.', 'For transported clocks: synchronise, separate along a recorded trajectory, reunite, and compare with the integral of proper time along the logged path.'],
    controls: ['Muons stopped in matter give the rest lifetime with the same detectors', 'Both muon charges, to exclude capture effects', 'A third clock that stays with the ground clock, to separate transport effects from clock drift'],
    signatures: ['Laboratory lifetime proportional to γ', 'No dependence on the (very large) centripetal acceleration: the clock hypothesis', 'Clock difference equal to the path integral of dτ, including gravitational terms'],
    safety: ['Radiation protection around accelerators and storage rings', 'Standard aviation and laser safety for transported optical clocks'],
  },
  falsify: ['A moving-clock rate differing from 1/γ by more than the measurement uncertainty at any speed.', 'A dependence of the accumulated time difference on acceleration itself rather than on the speed history.', 'Twins reunited with equal elapsed times after an out-and-back journey at relativistic speed.'],
  alternatives: [{ name: 'Lorentz ether theory', text: 'Predicts the same clock readings as special relativity, attributing them to motion through an undetectable preferred frame; empirically equivalent, distinguished only by economy of assumptions.' }, { name: 'General-relativistic description in the traveller\'s frame', text: 'In the traveller\'s accelerated frame the home clock runs fast during turnaround, as in a gravitational potential; the same numbers follow.' }, { name: 'Newtonian absolute time', text: 'No age difference. Refuted by muon lifetimes and transported atomic clocks.' }],
  limits: 'Flat spacetime with the home twin treated as inertial (or with first-order weak-field corrections). Speeds strictly below c. Ideal clocks whose rate depends only on instantaneous speed (the clock hypothesis), verified up to accelerations of order 10¹⁸ g for muons.',
  numerics: { method: 'Closed-form proper times; worldline sampled parametrically and the interval summed as a consistency check', order: 2 },
  optimise: { objective: 'tau_t', sense: 'min', vars: ['v'], note: 'The traveller\'s elapsed time falls monotonically toward zero as the speed approaches c.' },
  inverse: { series: 'ageing', curve: 1, fit: ['v'] },
  extensions: ['Journeys with unequal outbound and inbound speeds', 'Three-clock (relay) version with no acceleration at all', 'Twin paradox in a spatially closed universe, where topology selects a preferred frame'],
};

// ================================================================== 2. relativistic rocket
function rocketTrip(v, a) {
  const flip = a.flip, legs = flip ? 2 : 1, dLeg = v.D / legs, acc = v.a;
  let gam, phi, tauLeg, tLeg, vmax;
  if (a.relativistic) { gam = 1 + acc * dLeg / c2; phi = Math.acosh(gam); tauLeg = c / acc * phi; tLeg = c / acc * Math.sqrt(gam * gam - 1); vmax = c * Math.sqrt(1 - 1 / (gam * gam)); }
  else { tLeg = Math.sqrt(2 * dLeg / acc); tauLeg = tLeg; vmax = acc * tLeg; gam = 1; phi = vmax / c; }
  const trips = a.one_way || !flip ? 1 : 2;
  return { legs, dLeg, gam, phi, tauLeg, tLeg, vmax, trips, tau: legs * trips * tauLeg, t: legs * trips * tLeg, phiTot: legs * trips * phi };
}

const rocket = {
  id: 'relativistic-rocket',
  title: 'Relativistic rocket at constant proper acceleration',
  module: [1, 2], klass: 'I', domains: ['relativity', 'space'],
  keywords: ['relativistic rocket', 'constant acceleration', 'proper acceleration', 'one g', '1 g', 'interstellar', 'starship', 'rapidity', 'hyperbolic motion', 'flip and burn', 'photon rocket', 'mass ratio', 'alpha centauri', 'trip time', 'spaceship'],
  summary: 'A spacecraft holding constant proper acceleration: rapidity, ship time and Earth time to a given distance, and the propellant mass ratio that the journey implies.',
  background: [
    'A rocket whose crew feel a constant acceleration follows a hyperbola in spacetime. Its rapidity grows linearly with ship time, its speed approaches but never reaches c, and the distance covered grows exponentially with ship time once the motion is relativistic. These closed-form results follow directly from special relativity and are not in doubt.',
    'What is not available is the engineering: by the relativistic rocket equation even a perfect photon rocket needs a launch-to-final mass ratio of exp(Δφ) for a rapidity change Δφ, and any exhaust slower than light needs exponentially more.',
  ],
  phenomena: ['Hyperbolic motion', 'Time dilation', 'Relativistic velocity addition', 'Relativistic rocket equation'],
  laws: ['sr', 'momentum', 'energy'],
  refs: ['Misner, C. W., Thorne, K. S. & Wheeler, J. A. (1973). Gravitation, W. H. Freeman, §6.2.', 'Rindler, W. (2006). Relativity: Special, General, and Cosmological, 2nd ed., Oxford University Press.', 'Ackeret, J. (1946). Zur Theorie der Raketen. Helvetica Physica Acta 19, 103–112.', 'Forward, R. L. (1984). Roundtrip interstellar travel using laser-pushed lightsails. J. Spacecraft and Rockets 21, 187–195.'],
  inputs: [
    inp('a', 'Proper acceleration felt on board', 'm/s^2', 9.80665, { min: 0.1, max: 100, aliases: ['acceleration', 'accelerates', 'thrust acceleration'], src: 'One standard gravity' }),
    inp('D', 'Distance to the destination (Earth frame)', 'ly', 4.37, { min: 0.01, max: 3e6, kind: 'geometry', aliases: ['distance', 'light years', 'light-years', 'away'], src: 'Distance of α Centauri' }),
    inp('m_f', 'Final mass (structure and payload)', 'kg', 1e5, { min: 1, max: 1e9, aliases: ['payload', 'dry mass', 'final mass'] }),
    inp('v_e', 'Exhaust speed (used when the exhaust is not light)', 'm/s', 1e7, { min: 1e4, max: 0.999 * c, aliases: ['exhaust speed', 'exhaust velocity'], src: 'Order of magnitude for an idealised fusion drive, about 0.03 c' }),
  ],
  assumptions: [
    asm('relativistic', 'Motion obeys special relativity.', { why: 'Established', alt: 'Newtonian kinematics: speed grows without limit and all clocks agree.' }),
    asm('flip', 'The ship accelerates to the mid-point, turns over and decelerates to arrive at rest.', { why: 'A rendezvous requires it', alt: 'The ship accelerates all the way and passes the destination at its peak speed.' }),
    asm('photon', 'The exhaust is light (a photon rocket), the most efficient reaction drive possible.', { why: 'Upper bound on performance', alt: 'The exhaust leaves at the finite speed v_e and the relativistic rocket equation is used with that speed.' }),
    asm('one_way', 'The journey is one way.', { why: 'Simplest mission', alt: 'The ship returns the same way, doubling the times and squaring the mass ratio.' }),
  ],
  symbols: { tau: ['Ship (proper) time', 's'], t: ['Earth-frame time', 's'], x: ['Distance from start', 'm'], u: ['Speed in the Earth frame', 'm/s'], phi: ['Rapidity', '1'], gamma: ['Lorentz factor', '1'], m_0: ['Launch mass', 'kg'], phi_tot: ['Total rapidity change of all burns', '1'], dv_tot: ['Total velocity change of all burns', 'm/s'] },
  equations: a => [
    ...(a.relativistic ? [
      eq('rap', 'Rapidity', 'phi', 'a*tau/c', { kind: 'derived', origin: 'Constant proper acceleration adds equal rapidity in equal proper time' }),
      eq('vel', 'Speed', 'u', 'c*tanh(a*tau/c)', { kind: 'derived', origin: 'Definition of rapidity' }),
      eq('pos', 'Distance covered', 'x', 'c^2/a*(cosh(a*tau/c) - 1)', { kind: 'derived', origin: 'Integration of dx = c sinh(φ) dτ', needs: ['relativistic'] }),
      eq('time', 'Earth-frame time', 't', 'c/a*sinh(a*tau/c)', { kind: 'derived', origin: 'Integration of dt = cosh(φ) dτ', needs: ['relativistic'] }),
      a.photon ? eq('mass', 'Photon-rocket mass ratio', 'm_0/m_f', 'exp(phi_tot)', { kind: 'law', origin: 'Conservation of energy and momentum for light exhaust', needs: ['photon'] })
        : eq('mass', 'Relativistic rocket equation', 'm_0/m_f', 'exp(phi_tot*c/v_e)', { kind: 'law', origin: 'Conservation of energy and momentum (Ackeret 1946)' }),
    ] : [
      eq('vel', 'Speed', 'u', 'a*tau', { kind: 'law', origin: 'Newton\'s second law at constant acceleration' }),
      eq('pos', 'Distance covered', 'x', 'a*tau^2/2', { kind: 'derived', origin: 'Uniformly accelerated motion' }),
      eq('time', 'Earth-frame time', 't', 'tau', { kind: 'hypothesis', origin: 'Absolute time; retained for contrast only' }),
      a.photon ? eq('mass', 'Tsiolkovsky rocket equation with light-speed exhaust', 'm_0/m_f', 'exp(dv_tot/c)', { kind: 'law', origin: 'Conservation of momentum' })
        : eq('mass', 'Tsiolkovsky rocket equation', 'm_0/m_f', 'exp(dv_tot/v_e)', { kind: 'law', origin: 'Conservation of momentum' }),
    ]),
  ],
  derivation: a => [
    { text: 'In the instantaneous rest frame the ship gains speed a dτ in proper time dτ. Rapidities add linearly under collinear boosts, so the rapidity is proportional to ship time.', tex: '\\varphi = \\frac{a\\tau}{c},\\qquad u = c\\tanh\\varphi,\\qquad \\gamma = \\cosh\\varphi' },
    { text: 'Integrating dt = γ dτ and dx = u dt gives the hyperbola.', tex: 't = \\frac{c}{a}\\sinh\\frac{a\\tau}{c},\\qquad x = \\frac{c^2}{a}\\left(\\cosh\\frac{a\\tau}{c} - 1\\right),\\qquad \\left(x + \\frac{c^2}{a}\\right)^2 - c^2t^2 = \\frac{c^4}{a^2}' },
    { text: a.flip ? 'For a rendezvous the ship accelerates over half the distance and decelerates over the rest; each half is the same hyperbola.' : 'For a fly-by the whole distance is one acceleration phase.', tex: a.flip ? '\\tau = \\frac{2c}{a}\\,\\mathrm{arcosh}\\!\\left(1 + \\frac{aD}{2c^2}\\right)' : '\\tau = \\frac{c}{a}\\,\\mathrm{arcosh}\\!\\left(1 + \\frac{aD}{c^2}\\right)' },
    { text: 'Energy and momentum conservation for exhaust of speed v_e give a rapidity change proportional to the logarithm of the mass ratio; light exhaust is the limiting case.', tex: '\\frac{m_0}{m_f} = \\exp\\!\\left(\\frac{c\\,\\Delta\\varphi}{v_e}\\right)\\ \\xrightarrow{v_e = c}\\ e^{\\Delta\\varphi}' },
  ],
  solve(v, a) {
    const q = rocketTrip(v, a), acc = v.a, rel = a.relativistic, warnings = [];
    if (!a.flip && !a.one_way) warnings.push('A return journey is not defined for a fly-by that never decelerates; one-way figures are shown.');
    const ve = a.photon ? c : v.v_e;
    const lnMR = rel ? q.phiTot * c / ve : q.legs * q.trips * q.vmax / ve, MR = Math.exp(lnMR), m0 = v.m_f * MR;
    if (!rel && q.vmax > c) warnings.push('The Newtonian calculation gives a peak speed above the speed of light, which is not physical; restore the relativistic assumption.');
    if (lnMR > 30) warnings.push('The required mass ratio exceeds 10¹³: no reaction drive carrying its own propellant can perform this mission.');
    // first leg: closed form against numerical integration in dimensionless variables s = aτ/c
    const sEnd = acc * q.tauLeg / c, n = 200;
    const num = rel ? N.rk45((s, y) => [Math.sinh(s), Math.cosh(s)], [0, 0], 0, sEnd, n, { rtol: 1e-10, atol: 1e-14 }) : null;
    const tau = N.linspace(0, q.tauLeg * q.legs, 201), half = q.tauLeg;
    const state = s => {
      const first = s <= half || !a.flip, ss = first ? s : 2 * half - s;
      const xx = rel ? c2 / acc * (Math.cosh(acc * ss / c) - 1) : 0.5 * acc * ss * ss, uu = rel ? c * Math.tanh(acc * ss / c) : acc * ss, tt = rel ? c / acc * Math.sinh(acc * ss / c) : ss;
      return first ? { x: xx, u: uu, t: tt } : { x: v.D - xx, u: uu, t: 2 * q.tLeg - tt };
    };
    const st = tau.map(state);
    const dd = N.logspace(0.1, 1e5, 60), sweep = dd.map(d => rocketTrip({ ...v, D: d * LY }, a));
    const fin = rel ? lastState(num) : null, xNum = rel ? fin[0] * c2 / acc : q.dLeg, tNum = rel ? fin[1] * c / acc : q.tLeg;
    return {
      scalars: [
        scalar('tau_trip', 'Ship time for the journey', q.tau, 's', { show: 'yr' }), scalar('t_trip', 'Earth-frame time for the journey', q.t, 's', { show: 'yr' }),
        scalar('u_max', 'Peak speed', q.vmax, 'm/s'), scalar('beta_max', 'Peak speed as a fraction of c', q.vmax / c, '1'), scalar('gamma_max', 'Peak Lorentz factor', q.gam, '1'),
        scalar('phi_max', 'Peak rapidity', q.phi, '1'), scalar('phi_tot', 'Total rapidity change of all burns', rel ? q.phiTot : q.legs * q.trips * q.vmax / c, '1'),
        scalar('ln_MR', 'Natural logarithm of the mass ratio', lnMR, '1'),
        scalar('MR', 'Launch mass over final mass', MR, '1', { text: Number.isFinite(MR) ? undefined : `exp(${lab(lnMR)}), beyond floating-point range` }),
        scalar('m_0', 'Launch mass', m0, 'kg', { text: Number.isFinite(m0) ? undefined : 'beyond floating-point range' }),
        scalar('E_prop', 'Rest energy of the propellant', (m0 - v.m_f) * c2, 'J', { text: Number.isFinite(m0) ? undefined : 'beyond floating-point range' }),
        scalar('t_c', 'Characteristic time c/a', c / acc, 's', { show: 'yr' }), scalar('x_c', 'Characteristic length c²/a', c2 / acc, 'm', { show: 'ly' }),
        scalar('x_num', 'First-leg distance by numerical integration', xNum, 'm', { show: 'ly' }),
      ],
      series: [
        line('trip-times', 'Journey time against distance', 'Distance', 'ly', dd, [{ label: 'Ship time', data: sweep.map(s => s.tau / YR) }, { label: 'Earth time', data: sweep.map(s => s.t / YR) }], 'Time', 'yr', { logx: true, logy: true }),
        line('speed', 'Speed against ship time', 'Ship time', 'yr', tau.map(s => s / YR), [{ label: 'Speed', data: st.map(s => s.u / c) }, { label: 'Speed of light', data: tau.map(() => 1), dash: true }], 'Speed', 'c'),
        line('distance', 'Distance against ship time', 'Ship time', 'yr', tau.map(s => s / YR), [{ label: 'Distance', data: st.map(s => s.x / LY) }], 'Distance', 'ly'),
        line('clocks', 'Earth time against ship time', 'Ship time', 'yr', tau.map(s => s / YR), [{ label: 'Earth-frame time', data: st.map(s => s.t / YR) }, { label: 'Equal times', data: tau.map(s => s / YR), dash: true }], 'Earth-frame time', 'yr'),
      ],
      checks: [
        check('Distance: numerical integration against closed form', (xNum - q.dLeg) / q.dLeg, 1e-6, 'dx/dτ = c sinh(aτ/c) integrated with adaptive Runge–Kutta'),
        check('Worldline lies on the hyperbola', rel ? ((q.dLeg + c2 / acc) ** 2 - (c * tNum) ** 2) / (c2 / acc) ** 2 - 1 : 0, 1e-5 * Math.max(1, q.gam * q.gam), '(x + c²/a)² − c²t² = c⁴/a²'),
        check('Peak speed below the speed of light', rel ? Math.max(0, q.vmax / c - 1) : 0, 0, 'u < c'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { relativistic: true, flip: true, photon: true, one_way: true }, out = [];
    const r = this.solve(v, on), q = rocketTrip(v, on);
    out.push(bench('First-leg distance: numerical integration vs closed form', val(r, 'x_num'), q.dLeg, 'x = (c²/a)(cosh(aτ/c) − 1)', 1e-6));
    out.push(bench('Speed after one year of ship time at 1 g (fraction of c)', Math.tanh(9.80665 * YR / c), 0.7747, 'tanh(1.0323); standard textbook value', 1e-3));
    out.push(bench('Photon-rocket mass ratio equals γ(1 + β) per burn', Math.exp(q.phi), q.gam * (1 + q.vmax / c), 'e^φ = γ(1 + β)', 1e-9));
    const near = { ...v, D: 1e9, a: 10 }, rn = rocketTrip(near, on);
    out.push(bench('Newtonian limit of ship time for a short hop', rn.tau, 2 * Math.sqrt(2 * 5e8 / 10), 'τ → 2√(D/a) when aD ≪ c²', 1e-6));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.arrow(70, 310, 580, 310)} ${S.arrow(70, 310, 70, 40)} ${S.text(580, 330, 'x', 'd-text', 'end')} ${S.text(58, 48, 'ct', 'd-text', 'end')}
      ${S.path('M70 310 L330 50', 'd-dim')} ${S.text(336, 60, 'light cone', 'd-text d-small', 'start')}
      ${a.flip ? S.path('M70 310 Q78 220 170 170 Q262 120 270 40', 'd-pipe') : S.path('M70 310 Q80 200 250 60', 'd-pipe')}
      ${S.text(210, 190, a.flip ? 'accelerate, turn over, decelerate' : 'accelerate throughout', 'd-text', 'start')}
      ${S.rect(430, 150, 90, 26, 'd-body', 6)} ${S.path('M520 150 L545 163 L520 176 z', 'd-body')} ${S.arrow(430, 163, 385, 163, 'd-arrow d-heat')}
      ${S.text(475, 140, `a = ${lab(v.a, 'm/s²')}`)} ${S.text(405, 196, a.photon ? 'light exhaust' : `exhaust ${lab(v.v_e / c, 'c')}`, 'd-text d-small')}
      ${S.dim(70, 340, 270, 340, `D = ${lab(v.D / LY, 'ly')}`)}
    `);
  },
  experiment: {
    objective: 'Test the kinematics of constant proper acceleration with particles, since no macroscopic vehicle can approach these speeds.',
    apparatus: ['Linear accelerator with a uniform accelerating gradient', 'Electron or ion source', 'Time-of-flight section and magnetic spectrometer at the exit'],
    instruments: [{ name: 'Beam-position and timing monitors', measures: 'Arrival time against distance along the accelerator', range: 'ps to µs', resolution: '≈ 1 ps' }, { name: 'Magnetic spectrometer', measures: 'Final momentum', range: 'MeV/c to GeV/c', resolution: '10⁻⁴' }, { name: 'Calorimeter', measures: 'Final kinetic energy', range: 'MeV to GeV', resolution: '1 %' }],
    procedure: ['Accelerate particles through a known constant field so that the rest-frame force, hence proper acceleration, is constant.', 'Record time of flight at several stations.', 'Compare position against time with the hyperbola, and final speed with c tanh(aτ/c).'],
    controls: ['Vary the gradient to change a at fixed length', 'Repeat with a species of different mass to confirm that the kinematics depends only on a'],
    signatures: ['Energy gain linear in distance while the speed saturates below c', 'Arrival times following t = (c/a) sinh(aτ/c) rather than √(2x/a)'],
    safety: ['Ionising-radiation shielding and interlocks', 'High-voltage and radio-frequency safety'],
  },
  falsify: ['Any particle accelerated through a known potential arriving earlier than light would.', 'Measured speed against energy departing from u = c tanh(φ).', 'A reaction drive achieving a rapidity change larger than (v_e/c) ln(m₀/m_f).'],
  alternatives: [{ name: 'Externally powered propulsion', text: 'Light sails pushed by a remote laser, or interstellar ramjets, avoid carrying propellant and so escape the rocket equation, at the cost of other severe constraints.' }, { name: 'Newtonian kinematics', text: 'Predicts unbounded speed and equal ship and Earth times; contradicted by every accelerator.' }],
  limits: 'Flat spacetime, constant proper acceleration within each phase, no interstellar drag or radiation hazard. The mass ratio assumes perfect conversion of propellant rest mass into directed exhaust.',
  numerics: { method: 'Closed-form hyperbolic motion; adaptive Dormand–Prince integration as an independent check', order: 5 },
  optimise: { objective: 'tau_trip', sense: 'min', vars: ['a'], note: 'Higher acceleration always shortens the trip; human tolerance limits sustained acceleration to roughly 1 g.' },
  inverse: { series: 'trip-times', curve: 0, fit: ['a'] },
  extensions: ['Staged acceleration profiles limited by power rather than thrust', 'Blue-shifted radiation and dust loads on the hull', 'Signal exchange and the Rindler horizon behind an ever-accelerating ship'],
};

// ================================================================== 3. Einstein's elevator
const elevator = {
  id: 'einstein-elevator',
  title: 'Einstein\'s elevator and the equivalence principle',
  module: 1, klass: ['I', 'II'], domains: ['relativity'],
  keywords: ['einstein elevator', 'elevator', 'lift', 'equivalence principle', 'accelerating rocket', 'gravitational redshift', 'light bending in a cabin', 'pound rebka', 'free fall', 'tidal', 'accelerometer', 'windowless cabin', 'uniform gravitational field'],
  summary: 'Compares what instruments read inside a closed cabin at rest in gravity g and inside a rocket accelerating at g, and shows where the equivalence ends.',
  background: [
    'Einstein\'s equivalence principle states that no local experiment can distinguish a laboratory at rest in a uniform gravitational field from one accelerating uniformly in empty space. An accelerometer reads the same, dropped bodies follow the same paths, a light beam crossing the cabin sags by the same amount, and light climbing the cabin arrives red-shifted by the same fraction. The red-shift was measured by Pound and Rebka in 1960 and to one per cent by Pound and Snider in 1965.',
    'The equivalence is local. A real gravitational field converges on the centre of the attracting body and weakens with height, so two freely falling test bodies drift relative to each other. These tidal accelerations are the genuine, frame-independent signature of spacetime curvature; in a rigid accelerating rocket a different and far smaller non-uniformity appears.',
  ],
  phenomena: ['Equality of inertial and gravitational mass', 'Gravitational red-shift', 'Bending of light', 'Tidal acceleration', 'Rindler (uniformly accelerated) frame'],
  laws: ['equivalence', 'sr', 'newton2', 'gravitation'],
  refs: ['Einstein, A. (1911). Über den Einfluß der Schwerkraft auf die Ausbreitung des Lichtes. Annalen der Physik 35, 898–908.', 'Pound, R. V. & Rebka, G. A. (1960). Apparent weight of photons. Phys. Rev. Lett. 4, 337–341.', 'Pound, R. V. & Snider, J. L. (1965). Effect of gravity on gamma radiation. Phys. Rev. 140, B788–B803.', 'Will, C. M. (2014). The confrontation between general relativity and experiment. Living Rev. Relativity 17, 4.', 'Misner, C. W., Thorne, K. S. & Wheeler, J. A. (1973). Gravitation, W. H. Freeman, chs. 1, 6 and 16.'],
  inputs: [
    inp('g', 'Gravitational acceleration, or rocket acceleration', 'm/s^2', 9.80665, { min: 0.1, max: 100, kind: 'environment', env: 'gravity', aliases: ['gravity', 'acceleration', 'accelerates', 'g-force'] }),
    inp('h', 'Cabin height (drop height and light path for the red-shift)', 'm', 22.5, { min: 0.1, max: 1000, kind: 'geometry', aliases: ['height', 'tall', 'tower'], src: 'Height of the Jefferson Laboratory tower used by Pound and Rebka' }),
    inp('w', 'Cabin width crossed by the light beam', 'm', 3, { min: 0.1, max: 1000, kind: 'geometry', aliases: ['width', 'wide', 'across'] }),
    inp('R_p', 'Distance from the centre of the attracting body', 'km', 6371, { min: 100, max: 1e6, kind: 'environment', aliases: ['planet radius', 'radius'], src: 'Mean radius of the Earth' }),
    inp('v_t', 'Terminal speed of the dropped ball in air', 'm/s', 40, { min: 1, max: 1000, kind: 'material', aliases: ['terminal speed', 'terminal velocity'], src: 'Order of magnitude for a dense ball of a few centimetres; used only when air is admitted' }),
  ],
  assumptions: [
    asm('in_gravity', 'The cabin is at rest on the surface of a planet with local gravity g.', { why: 'The everyday case', alt: 'The cabin is a rocket in empty space accelerating at g; the red-shift is then a Doppler shift and the light beam sags because the floor rises to meet it.' }),
    asm('uniform', 'The field is uniform over the cabin, so the comparison is strictly local.', { why: 'Statement of the equivalence principle', alt: 'The finite size of the cabin is kept: in gravity the field converges and weakens with height (tides); in a rigid rocket the proper acceleration falls with height as g/(1 + gh/c²).' }),
    asm('weak', 'Only terms of first order in gh/c² are kept.', { why: 'gh/c² is about 10⁻¹⁵ in a laboratory', alt: 'The exact red-shift of a uniformly accelerated (Rindler) frame, gh/c² ÷ (1 + gh/c²), is used.' }),
    asm('vacuum', 'The cabin is evacuated, so the dropped ball feels no drag.', { why: 'Isolates gravity', alt: 'Quadratic air drag with terminal speed v_t acts on the ball (identically in both cabins).' }),
  ],
  symbols: { a_acc: ['Accelerometer reading', 'm/s^2'], y: ['Height of the ball above the floor', 'm'], t: ['Time', 's'], delta_L: ['Sag of the light beam across the cabin', 'm'], z: ['Fractional frequency shift', '1'], da_v: ['Vertical tidal acceleration over the cabin height', 'm/s^2'], da_h: ['Horizontal tidal acceleration over the cabin width', 'm/s^2'], t_f: ['Fall time', 's'], dv: ['Speed gained by the receiver during the light travel time', 'm/s'] },
  equations: a => [
    eq('acc', 'Accelerometer reading', 'a_acc', 'g', { kind: 'law', origin: 'Equality of inertial and gravitational mass (Eötvös; Einstein equivalence principle)' }),
    a.vacuum
      ? eq('ball', 'Dropped ball relative to the floor', 'd2(y,t)', '-g', { kind: 'law', origin: a.in_gravity ? 'Newton\'s second law with weight mg' : 'The ball is force-free; the floor accelerates upward at g' })
      : eq('ball', 'Dropped ball with air drag', 'd2(y,t)', '-g*(1 - (d(y,t)/v_t)^2)', { kind: 'law', origin: 'Newton\'s second law with quadratic drag' }),
    eq('light', 'Sag of a light beam crossing the cabin', 'delta_L', 'g*w^2/(2*c^2)', { kind: 'derived', origin: a.in_gravity ? 'Equivalence principle applied to light' : 'The floor rises ½g t² during the light crossing time w/c' }),
    ...(a.in_gravity ? [] : [eq('dv', 'Speed gained while the light climbs', 'dv', 'g*h/c', { kind: 'derived', origin: 'Uniform acceleration over the light travel time h/c' })]),
    a.weak
      ? (a.in_gravity ? eq('red', 'Gravitational red-shift over height h', 'z', 'g*h/c^2', { kind: 'derived', origin: 'Energy conservation for a photon climbing a potential difference gh (Einstein 1911)', needs: ['weak'] })
        : eq('red', 'Doppler shift over height h', 'z', 'dv/c', { kind: 'derived', origin: 'First-order Doppler effect', needs: ['weak'] }))
      : eq('red', 'Red-shift in a uniformly accelerated frame', 'z', 'g*h/c^2/(1 + g*h/c^2)', { kind: 'derived', origin: 'Rindler metric: clock rates scale as 1 + gx/c²' }),
    ...(a.uniform ? [] : a.in_gravity ? [
      eq('tidev', 'Vertical tidal acceleration', 'da_v', '2*g*h/R_p', { kind: 'derived', origin: 'Gradient of the inverse-square field' }),
      eq('tideh', 'Horizontal tidal acceleration', 'da_h', 'g*w/R_p', { kind: 'derived', origin: 'Convergence of field lines toward the centre' }),
    ] : [eq('tidev', 'Variation of proper acceleration with height in a rigid rocket', 'da_v', 'g^2*h/c^2', { kind: 'derived', origin: 'Born-rigid acceleration: g(h) = g/(1 + gh/c²)' })]),
  ],
  derivation: a => [
    { text: 'Because inertial and gravitational mass are equal, every body falls with the same acceleration; an observer in a closed cabin cannot tell a downward gravitational pull from an upward acceleration of the cabin.', tex: 'm_i\\,\\ddot y = -m_g\\,g,\\quad m_i = m_g\\ \\Rightarrow\\ \\ddot y = -g' },
    { text: 'A light beam sent horizontally across a rocket cabin travels straight in the inertial frame, while the floor rises ½g t² during the crossing time t = w/c. By equivalence the same sag occurs in gravity.', tex: '\\delta = \\tfrac12\\,g\\left(\\frac{w}{c}\\right)^2' },
    { text: 'Light emitted at the floor of the rocket reaches the ceiling after a time h/c, by which time the ceiling moves faster by gh/c: the light is Doppler-shifted to the red. By equivalence light climbing in gravity is red-shifted by the same fraction.', tex: 'z = \\frac{\\Delta v}{c} = \\frac{g\\,h}{c^2}' },
    { text: 'Over a finite cabin a real field is not uniform. Expanding the inverse-square field about the cabin gives a stretching along the vertical and a squeezing across it, which no choice of accelerated frame removes.', tex: '\\Delta a_{\\parallel} = \\frac{2 g h}{R},\\qquad \\Delta a_{\\perp} = \\frac{g\\,w}{R}' },
  ],
  solve(v, a) {
    const g = v.g, h = v.h, eps = g * h / c2;
    const z = a.weak ? eps : eps / (1 + eps);
    const sag = g * v.w * v.w / (2 * c2), angle = g * v.w / c2;
    const tf = a.vacuum ? Math.sqrt(2 * h / g) : v.v_t / g * Math.acosh(Math.exp(Math.min(g * h / (v.v_t * v.v_t), 700)));
    const vi = a.vacuum ? g * tf : v.v_t * Math.tanh(g * tf / v.v_t);
    let daV = 0, daH = 0;
    if (!a.uniform) { if (a.in_gravity) { daV = 2 * g * h / v.R_p; daH = g * v.w / v.R_p; } else { daV = g * g * h / c2; } }
    const drift = 0.5 * daH * tf * tf;
    // ball: numerical integration in the cabin frame
    const sol = N.rk45((t, y) => [y[1], -g * (a.vacuum ? 1 : 1 - (y[1] / v.v_t) ** 2)], [h, 0], 0, tf, 120, { rtol: 1e-10, atol: 1e-12 });
    const yEnd = lastState(sol)[0];
    const tt = sol.t, yAn = tt.map(t => (a.vacuum ? h - 0.5 * g * t * t : h - v.v_t * v.v_t / g * Math.log(Math.cosh(g * t / v.v_t))));
    const xs = N.linspace(0, v.w, 60), hs = N.linspace(0, h, 60), sizes = N.logspace(0.1, 1000, 50);
    const warnings = [];
    if (!a.uniform && a.in_gravity && h > 0.1 * v.R_p) warnings.push('The cabin height is not small compared with the distance to the centre; the first-order tidal expressions are then only indicative.');
    return {
      scalars: [
        scalar('a_acc', 'Accelerometer reading', g, 'm/s^2', { note: 'identical in both cabins' }),
        scalar('t_f', 'Fall time of the dropped ball', tf, 's'), scalar('v_i', 'Impact speed relative to the floor', vi, 'm/s'),
        scalar('delta_L', 'Sag of the light beam across the cabin', sag, 'm'), scalar('theta_L', 'Deflection angle of the light beam', angle, 'rad'),
        scalar('z', a.in_gravity ? 'Gravitational red-shift over the cabin height' : 'Doppler red-shift over the cabin height', z, '1'),
        scalar('dv', 'Speed gained by the ceiling during the light travel time', g * h / c, 'm/s'),
        scalar('dt_day', 'Clock at the ceiling gains on the floor clock, per day', z * 86400, 's', { show: 'ns' }),
        scalar('da_v', a.in_gravity ? 'Vertical tidal acceleration over the cabin height' : 'Change of proper acceleration over the cabin height', daV, 'm/s^2'),
        scalar('da_h', 'Horizontal tidal acceleration over the cabin width', daH, 'm/s^2'),
        scalar('drift', 'Approach of two balls dropped a cabin-width apart, over one fall', drift, 'm'),
        scalar('local', 'Relative size of the non-uniformity (Δa/g)', Math.max(daV, daH) / g, '1'),
      ],
      series: [
        line('ball', 'Dropped ball: height above the floor', 'Time', 's', tt, [{ label: 'Lab at rest in gravity', data: sol.y[0] }, { label: 'Accelerating rocket', data: yAn, dash: true }], 'Height', 'm', { note: 'The two curves coincide: the experiment cannot tell the cabins apart.' }),
        line('beam', 'Light beam crossing the cabin', 'Horizontal distance', 'm', xs, [{ label: 'Sag below a straight line', data: xs.map(x => g * x * x / (2 * c2)) }], 'Sag', 'm'),
        line('redshift', 'Frequency shift against height', 'Height', 'm', hs, [{ label: 'First order, gh/c²', data: hs.map(x => g * x / c2) }, { label: 'Uniformly accelerated frame, exact', data: hs.map(x => g * x / c2 / (1 + g * x / c2)), dash: true }], 'Fractional shift', '–'),
        line('tides', 'Non-uniformity against cabin size', 'Cabin size', 'm', sizes, [{ label: 'Planet: vertical tide 2gL/R', data: sizes.map(s => 2 * g * s / v.R_p) }, { label: 'Planet: horizontal tide gL/R', data: sizes.map(s => g * s / v.R_p) }, { label: 'Rigid rocket: g²L/c²', data: sizes.map(s => g * g * s / c2), dash: true }], 'Relative acceleration', 'm/s²', { logx: true, logy: true }),
      ],
      checks: [
        check('Ball reaches the floor at the computed fall time', yEnd / h, 1e-6, 'Numerical trajectory against the closed-form fall time'),
        check('Red-shift equals Doppler shift of the accelerating cabin', a.weak ? z - (g * h / c) / c : 0, 1e-30, 'gh/c² = Δv/c to first order'),
        check('Readings identical in the two cabins when the field is uniform', a.uniform ? daV + daH : 0, 0, 'No internal measurement distinguishes them'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { in_gravity: true, uniform: true, weak: true, vacuum: true };
    const r = this.solve({ ...v, g: 9.80665, h: 22.5 }, on), out = [];
    out.push(bench('Red-shift over 22.5 m at standard gravity', val(r, 'z'), 2.455e-15, 'gh/c² = 2.455 × 10⁻¹⁵', 1e-3));
    out.push(bench('Fall time over 22.5 m in vacuum', val(r, 't_f'), Math.sqrt(2 * 22.5 / 9.80665), 't = √(2h/g)', 1e-12));
    const rd = this.solve({ ...v, v_t: 1e6 }, { ...on, vacuum: false });
    out.push(bench('Drag solution tends to the vacuum result for large terminal speed', val(rd, 't_f'), Math.sqrt(2 * v.h / v.g), 'Limit v_t → ∞', 1e-6));
    return out;
  },
  validation: [
    { name: 'Gravitational red-shift of 14.4 keV gamma rays', ref: 'Pound & Rebka (1960) Phys. Rev. Lett. 4, 337; Pound & Snider (1965) Phys. Rev. 140, B788', note: 'One-way shift over the 22.56 m (74 ft) tower. The 1960 figure is half the measured up-minus-down difference (5.13 ± 0.51) × 10⁻¹⁵; the 1965 figure is the reported ratio 0.9990 ± 0.0076 applied to the prediction.',
      cases: [
        { label: 'Pound & Rebka 1960', inputs: { g: 9.804, h: 22.56 }, observable: 'z', observed: 2.565e-15, sigma: 0.255e-15 },
        { label: 'Pound & Snider 1965', inputs: { g: 9.804, h: 22.56 }, observable: 'z', observed: 2.459e-15, sigma: 0.019e-15 },
      ] },
  ],
  diagram(v, a) {
    return svg(`
      ${S.rect(70, 60, 200, 230, 'd-body', 6)} ${S.rect(370, 60, 200, 230, 'd-body', 6)}
      ${S.path('M40 290 L300 290', 'd-ground')} ${S.text(170, 316, 'at rest in gravity g')}
      ${S.path('M400 290 L430 330 L510 330 L540 290', 'd-line')} ${S.arrow(470, 345, 470, 300, 'd-arrow d-heat')} ${S.text(470, 358, 'accelerating at g in empty space', 'd-text d-small')}
      ${S.circle(120, 110, 7, 'd-hazard')} ${S.arrow(120, 122, 120, 180)} ${S.circle(420, 110, 7, 'd-hazard')} ${S.arrow(420, 122, 420, 180)}
      ${S.path('M72 150 Q170 152 268 170', 'd-dim')} ${S.path('M372 150 Q470 152 568 170', 'd-dim')}
      ${S.text(200, 142, 'light beam', 'd-text d-small')} ${S.text(500, 142, 'light beam', 'd-text d-small')}
      ${S.arrow(240, 280, 240, 80, 'd-arrow')} ${S.text(232, 200, 'red-shift', 'd-text d-small', 'end')} ${S.arrow(540, 280, 540, 80, 'd-arrow')} ${S.text(532, 200, 'Doppler', 'd-text d-small', 'end')}
      ${S.text(320, 36, `h = ${lab(v.h, 'm')}   w = ${lab(v.w, 'm')}   gh/c² = ${lab(v.g * v.h / c2)}`)}
      ${a.uniform ? '' : S.text(170, 82, 'field lines converge: tides', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'L', text: 'The experiment is local: the cabin is small and the duration short' }, { k: 'D', text: 'Tidal relative accelerations are detectable inside the cabin' }, { k: 'E', text: 'No internal experiment distinguishes gravity from uniform acceleration' }, { k: 'C', text: 'Spacetime curvature is detected' }],
    premises: ['L -> ~D', '~D -> E', 'D <-> C', 'L'],
    conclusion: 'E & ~C',
  },
  experiment: {
    objective: 'Measure the frequency shift of radiation between two heights and the universality of free fall, the two pillars of the equivalence principle.',
    apparatus: ['Vertical evacuated or helium-filled path of 20 m or more', 'Mössbauer source (⁵⁷Fe) and resonant absorber, or two optical clocks linked by fibre', 'Velocity transducer to scan the source', 'Drop tube or torsion balance with test bodies of different composition'],
    instruments: [{ name: 'Mössbauer spectrometer', measures: 'Fractional frequency shift through the compensating Doppler velocity', range: '±1 mm/s', resolution: 'fractional 10⁻¹⁶' }, { name: 'Optical-lattice clock pair', measures: 'Fractional frequency difference', range: 'continuous', resolution: '10⁻¹⁸ (height resolution of about 1 cm)' }, { name: 'Laser interferometer on dropped corner cubes', measures: 'Differential acceleration', range: 'µm', resolution: '10⁻⁹ g' }],
    procedure: ['Send radiation upward and record the Doppler velocity needed to restore resonance.', 'Exchange source and absorber and repeat with the radiation travelling downward.', 'Take half the difference to remove fixed offsets.', 'Separately, drop or balance bodies of different composition and bound any differential acceleration.'],
    controls: ['Temperature difference between source and absorber held below 0.03 K or monitored (second-order Doppler shift)', 'Interchange of source and absorber', 'Null run with a horizontal path'],
    signatures: ['Shift proportional to height and to g', 'Shift independent of the radiation frequency', 'Differential acceleration of different materials consistent with zero'],
    safety: ['Sealed radioactive source handling', 'Working at height', 'Laser safety for optical clocks'],
  },
  falsify: ['A red-shift that is not gh/c² within experimental uncertainty.', 'Bodies of different composition falling at measurably different rates in the same field.', 'A local, non-tidal experiment inside a freely falling cabin that reveals the external field.'],
  alternatives: [{ name: 'Photon-energy argument', text: 'The red-shift follows from energy conservation alone (a photon of energy E has weight E/c²) and does not by itself test curved spacetime.' }, { name: 'Theories violating the equivalence principle', text: 'Composition-dependent fifth forces or varying constants would make the red-shift or free-fall rate depend on the kind of clock or body; current bounds are near 10⁻¹⁵ for free fall (MICROSCOPE).' }, { name: 'Strong-field corrections', text: 'Near compact objects the full Schwarzschild red-shift replaces gh/c².' }],
  limits: 'Weak fields and cabins small compared with the scale over which the field changes. Tidal expressions are first order in cabin size over distance to the centre. The exact option applies to a rigidly accelerated frame in flat spacetime, not to a planetary field.',
  numerics: { method: 'Closed forms; adaptive Runge–Kutta for the ball trajectory', order: 5 },
  inverse: { series: 'redshift', curve: 0, fit: ['g'] },
  extensions: ['Full Schwarzschild red-shift between two radii', 'Geodesic deviation for a cloud of test particles', 'Charged particle in the cabin: does it radiate?'],
};

// ================================================================== 4. Schwarzschild orbits
function schwOrbit(v, a) {
  const GM = G * (a.test_particle ? v.M : v.M + v.m_2), rg = GM / c2, rs = 2 * rg, e = v.e;
  let p = v.a * (1 - e * e), clamped = false;
  const pMin = 1.05 * (6 + 2 * e) * rg;
  if (a.gr && p < pMin) { p = pMin; clamped = true; }
  const u1 = (1 - e) / p, u2 = (1 + e) / p, eps = a.gr ? rg / p : 0;
  // GM/h² from the turning points of the first integral (u')² = r_s(u − u1)(u − u2)(u − u3)
  const A = a.gr ? 0.5 * p * (rs * u1 * u2 + (1 - rs * (u1 + u2)) * (u1 + u2)) : 1;
  const h2 = GM * p / A;
  // exact advance per radial period by quadrature (integrand written to avoid cancellation)
  const exact = a.gr ? midpoint(th => { const d = rs * (2 * u1 + u2) + rs * (u2 - u1) * Math.sin(th) ** 2, s = Math.sqrt(1 - d); return 4 * d / (s * (1 + s)); }, 0, Math.PI / 2, 200) : 0;
  const formula = a.gr ? 6 * Math.PI * rg / p : 0;
  return { GM, rg, rs, e, p, clamped, u1, u2, eps, A, h2, exact, formula, aEff: p / (1 - e * e) };
}
/** RK4 for w'' = F(w) in the angle; returns the new [w, w']. */
function stepOrbit(F, w, dw, h) {
  const k1 = F(w), w2 = w + 0.5 * h * dw, d2 = dw + 0.5 * h * k1, k2 = F(w2), w3 = w + 0.5 * h * d2, d3 = dw + 0.5 * h * k2, k3 = F(w3), w4 = w + h * d3, d4 = dw + h * k3, k4 = F(w4);
  return [w + h / 6 * (dw + 2 * d2 + 2 * d3 + d4), dw + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)];
}
function integrateOrbit(o, nOrb) {
  const F = w => o.A - w + 3 * o.eps * w * w, h = 2 * Math.PI / 4000;
  const phiEnd = nOrb * (2 * Math.PI + o.exact), nSteps = Math.min(Math.ceil(phiEnd / h), 400000), every = Math.max(1, Math.ceil(nSteps / 1500));
  let w = 1 + o.e, dw = 0, phi = 0, peri = null, passedApo = false;
  const xs = [], ys = [];
  for (let k = 0; k <= nSteps; k++) {
    if (k % every === 0) { const r = 1 / w; xs.push(r * Math.cos(phi)); ys.push(r * Math.sin(phi)); }
    const [wn, dn] = stepOrbit(F, w, dw, h);
    if (peri == null && o.e >= 1e-3) {
      if (dw < 0 && dn >= 0) passedApo = true;
      else if (passedApo && dw > 0 && dn <= 0) { let lo = 0, hi = h; for (let i = 0; i < 50; i++) { const mid = 0.5 * (lo + hi); if (stepOrbit(F, w, dw, mid)[1] > 0) lo = mid; else hi = mid; } peri = phi + 0.5 * (lo + hi); }
    }
    w = wn; dw = dn; phi += h;
  }
  return { xs, ys, advance: peri == null ? NaN : peri - 2 * Math.PI };
}
function lightDeflection(rg, b) {
  const k = 3 * rg / b, F = w => -w + k * w * w, h = Math.PI / 4000;
  let w = 0, dw = 1, phi = 0; const xs = [], ys = [];
  for (let i = 0; i < 80000; i++) {
    if (i % 20 === 0 && w > 0.04) { xs.push(Math.cos(phi) / w); ys.push(Math.sin(phi) / w); }
    const [wn, dn] = stepOrbit(F, w, dw, h);
    if (wn <= 0 && i > 0) { let lo = 0, hi = h; for (let j = 0; j < 50; j++) { const mid = 0.5 * (lo + hi); if (stepOrbit(F, w, dw, mid)[0] > 0) lo = mid; else hi = mid; } return { delta: phi + 0.5 * (lo + hi) - Math.PI, xs, ys }; }
    if (wn > 1e3) break;
    w = wn; dw = dn; phi += h;
  }
  return { delta: NaN, xs, ys };
}

const schwarzschild = {
  id: 'schwarzschild-orbits',
  title: 'Orbits and light deflection in Schwarzschild spacetime',
  module: [1, 2], klass: 'I', domains: ['relativity', 'space'],
  keywords: ['perihelion precession', 'perihelion advance', 'mercury', 'schwarzschild', 'geodesic', 'light deflection', 'light bending', 'bending of starlight', 'isco', 'photon sphere', 'effective potential', 'general relativity orbit', 'relativistic orbit', 'eddington', 'precession'],
  summary: 'Timelike and null geodesics around a spherical mass: perihelion advance by formula, exact quadrature and direct integration of the orbit equation; innermost stable orbit, photon sphere and the bending of light.',
  background: [
    'Outside a spherical, non-rotating mass the geometry of spacetime is the Schwarzschild solution of Einstein\'s equations. A freely falling body follows the Newtonian orbit equation with one extra term, 3GMu²/c², which makes bound orbits precess. For Mercury the advance is 43 arcseconds per century, the anomaly that general relativity explained in 1915.',
    'The same extra term doubles the Newtonian deflection of light grazing the Sun to 1.75 arcseconds, first tested at the 1919 eclipse and now confirmed to parts in 10⁴ by radio interferometry. Close to a compact object the term dominates: there are no stable circular orbits inside 6GM/c² and light can circle at 3GM/c².',
  ],
  phenomena: ['Geodesic motion', 'Perihelion advance', 'Gravitational bending of light', 'Innermost stable circular orbit', 'Photon sphere'],
  laws: ['efe', 'equivalence', 'angular', 'energy', 'gravitation'],
  refs: ['Einstein, A. (1915). Erklärung der Perihelbewegung des Merkur aus der allgemeinen Relativitätstheorie. Sitzungsber. Preuss. Akad. Wiss., 831–839.', 'Schwarzschild, K. (1916). Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen Theorie. Sitzungsber. Preuss. Akad. Wiss., 189–196.', 'Clemence, G. M. (1947). The relativity effect in planetary motions. Rev. Mod. Phys. 19, 361–364.', 'Dyson, F. W., Eddington, A. S. & Davidson, C. (1920). A determination of the deflection of light by the Sun\'s gravitational field. Phil. Trans. R. Soc. A 220, 291–333.', 'Shapiro, S. S., Davis, J. L., Lebach, D. E. & Gregory, J. S. (2004). Measurement of the solar gravitational deflection of radio waves using geodetic VLBI data, 1979–1999. Phys. Rev. Lett. 92, 121101.', 'Will, C. M. (2014). The confrontation between general relativity and experiment. Living Rev. Relativity 17, 4.', 'Misner, C. W., Thorne, K. S. & Wheeler, J. A. (1973). Gravitation, W. H. Freeman, ch. 25.'],
  inputs: [
    inp('M', 'Central mass', 'Msun', 1, { min: 0.01, max: 1e9, kind: 'environment', aliases: ['mass', 'solar mass', 'solar masses', 'star mass', 'black hole mass'] }),
    inp('a', 'Semi-major axis of the orbit', 'AU', 0.38709893, { min: 0.001, max: 1e4, kind: 'geometry', aliases: ['semi-major axis', 'orbital radius', 'orbit radius'], src: 'Mercury, NASA planetary fact sheet' }),
    inp('e', 'Orbital eccentricity', '1', 0.20563, { min: 0, max: 0.95, kind: 'geometry', aliases: ['eccentricity'], src: 'Mercury, NASA planetary fact sheet' }),
    inp('b', 'Impact parameter of the light ray', 'km', 695700, { min: 10, max: 1e10, kind: 'geometry', aliases: ['impact parameter', 'closest approach', 'limb'], src: 'Nominal solar radius, IAU 2015' }),
    inp('m_2', 'Mass of the orbiting body', 'Mearth', 0.0553, { min: 0, max: 1e6, aliases: ['planet mass', 'companion mass'], src: 'Mercury; used only when the test-particle assumption is removed' }),
    inp('J_2', 'Quadrupole moment of the central body', '1', 2.2e-7, { min: 0, max: 0.05, kind: 'environment', src: 'Solar J₂ from helioseismology, about 2.2 × 10⁻⁷; used only when the spherical assumption is removed' }),
    inp('R_b', 'Equatorial radius of the central body', 'km', 695700, { min: 1, max: 1e9, kind: 'environment', src: 'Nominal solar radius, IAU 2015' }),
    inp('n_orb', 'Number of orbits integrated for the plot', '1', 3, { min: 1, max: 20, kind: 'numerical' }),
  ],
  assumptions: [
    asm('gr', 'Motion follows geodesics of the Schwarzschild metric.', { why: 'Established theory of gravitation', alt: 'Newtonian gravity: closed Kepler ellipses, and light treated as a particle moving at c (half the deflection).' }),
    asm('weak_field', 'The reported advance uses the first-order formula 6πGM/(c²a(1−e²)).', { why: 'Excellent in the solar system', alt: 'The reported advance is the exact value from quadrature of the first integral, valid for any bound orbit.' }),
    asm('test_particle', 'The orbiting body is a test particle of negligible mass.', { why: 'Planet-to-star mass ratios are tiny', alt: 'The total mass M + m₂ replaces M in the relative orbit (leading two-body correction).' }),
    asm('spherical', 'The central body is spherical and non-rotating.', { why: 'Schwarzschild geometry', alt: 'The Newtonian quadrupole (J₂) advance of an equatorial orbit is added.' }),
  ],
  symbols: { u: ['Inverse radius 1/r', '1/m'], phi: ['Orbital angle', 'rad'], h_L: ['Specific angular momentum', 'm^2/s'], dphi: ['Perihelion advance per orbit', 'rad'], delta: ['Deflection angle of light', 'rad'], r_s: ['Schwarzschild radius', 'm'], r_isco: ['Innermost stable circular orbit', 'm'], r_ph: ['Photon-sphere radius', 'm'], V_eff: ['Effective potential per unit mass', 'J/kg'], r: ['Radial coordinate', 'm'], dphi_J: ['Quadrupole advance per orbit', 'rad'], M_t: ['Total mass', 'kg'] },
  equations: a => [
    a.gr
      ? eq('orbit', 'Orbit equation', 'd2(u,phi) + u', 'G*M/h_L^2 + 3*G*M*u^2/c^2', { kind: 'law', origin: 'Geodesic equation in the Schwarzschild metric', needs: ['gr'] })
      : eq('orbit', 'Orbit equation (Binet)', 'd2(u,phi) + u', 'G*M/h_L^2', { kind: 'law', origin: 'Newton\'s law of gravitation with conserved angular momentum' }),
    ...(a.gr ? [
      eq('veff', 'Effective potential', 'V_eff', '-G*M/r + h_L^2/(2*r^2) - G*M*h_L^2/(c^2*r^3)', { kind: 'derived', origin: 'First integral of the geodesic equation' }),
      eq('prec', 'Perihelion advance per orbit', 'dphi', a.test_particle ? '6*pi*G*M/(c^2*a*(1 - e^2))' : '6*pi*G*(M + m_2)/(c^2*a*(1 - e^2))', { kind: 'derived', origin: 'First-order perturbation of the Kepler ellipse (Einstein 1915)', needs: ['weak_field'] }),
      eq('null', 'Light-ray equation', 'd2(u,phi) + u', '3*G*M*u^2/c^2', { kind: 'law', origin: 'Null geodesic of the Schwarzschild metric' }),
      eq('defl', 'Deflection of light', 'delta', '4*G*M/(c^2*b)', { kind: 'derived', origin: 'First-order solution of the null geodesic (Einstein 1915)' }),
      eq('rs', 'Schwarzschild radius', 'r_s', '2*G*M/c^2', { kind: 'definition' }),
      eq('isco', 'Innermost stable circular orbit', 'r_isco', '6*G*M/c^2', { kind: 'derived', origin: 'Marginal stability of the effective potential' }),
      eq('rph', 'Photon sphere', 'r_ph', '3*G*M/c^2', { kind: 'derived', origin: 'Circular null geodesic' }),
    ] : [
      eq('veff', 'Effective potential', 'V_eff', '-G*M/r + h_L^2/(2*r^2)', { kind: 'derived', origin: 'Energy conservation in a central field' }),
      eq('defl', 'Deflection of a particle moving at c', 'delta', '2*G*M/(c^2*b)', { kind: 'derived', origin: 'Newtonian hyperbolic orbit (Soldner 1801)' }),
    ]),
    ...(a.spherical ? [] : [eq('j2', 'Quadrupole advance per orbit', 'dphi_J', '3*pi*J_2*(R_b/(a*(1 - e^2)))^2', { kind: 'derived', origin: 'Secular perturbation by an oblate primary, equatorial orbit' })]),
  ],
  derivation: a => [
    { text: 'The Schwarzschild metric has conserved energy and angular momentum per unit mass. Eliminating proper time in favour of the orbital angle and writing u = 1/r gives the orbit equation.', tex: '\\frac{\\mathrm{d}^2u}{\\mathrm{d}\\varphi^2} + u = \\frac{GM}{h^2} + \\frac{3GM}{c^2}\\,u^2' },
    { text: 'Its first integral is a cubic in u. The two smaller roots are the turning points, so the angle swept between successive perihelia is an elliptic integral, evaluated here without approximation.', tex: '\\left(\\frac{\\mathrm{d}u}{\\mathrm{d}\\varphi}\\right)^2 = r_s\\,(u-u_1)(u-u_2)(u-u_3),\\qquad \\Delta\\varphi = 2\\!\\int_{u_1}^{u_2}\\!\\frac{\\mathrm{d}u}{\\sqrt{r_s (u-u_1)(u_2-u)(u_3-u)}} - 2\\pi' },
    { text: 'When the orbit is much larger than GM/c² the integral reduces to Einstein\'s formula.', tex: '\\Delta\\varphi \\simeq \\frac{6\\pi G M}{c^2 a\\,(1-e^2)}' },
    { text: 'For light the constant term is absent. The straight line u = sin φ / b is the zeroth-order solution; the quadratic term bends it through a total angle of twice the Newtonian value.', tex: '\\delta \\simeq \\frac{4GM}{c^2 b}' },
    { text: 'Circular orbits sit at extrema of the effective potential. They are stable only outside 6GM/c², and the circular light orbit lies at 3GM/c².', tex: 'r_{\\rm ISCO} = \\frac{6GM}{c^2},\\qquad r_{\\rm ph} = \\frac{3GM}{c^2},\\qquad b_{\\rm crit} = 3\\sqrt3\\,\\frac{GM}{c^2}' },
  ],
  solve(v, a) {
    const o = schwOrbit(v, a), warnings = [];
    if (o.clamped) warnings.push('No bound orbit with these elements exists: the periapsis lies inside the limit p = (6 + 2e)GM/c². Results are shown for the smallest stable orbit of the same eccentricity.');
    const ode = integrateOrbit(o, Math.round(N.clamp(v.n_orb, 1, 20)));
    const Torb = 2 * Math.PI * Math.sqrt(o.aEff ** 3 / o.GM), perCentury = 36525 * 86400 / Torb;
    const dJ = a.spherical ? 0 : 3 * Math.PI * v.J_2 * (v.R_b / o.p) ** 2;
    const head = (a.gr ? (a.weak_field ? o.formula : o.exact) : 0) + dJ;
    // light
    const bCrit = 3 * Math.sqrt(3) * o.rg; let b = v.b;
    if (a.gr && b < 1.02 * bCrit) { b = 1.02 * bCrit; warnings.push('The impact parameter is inside the critical value 3√3 GM/c²: the ray is captured. The deflection is shown for a ray just outside the critical value.'); }
    let defl, lx, ly;
    if (a.gr) { const q = lightDeflection(o.rg, b); defl = q.delta; lx = q.xs; ly = q.ys; }
    else { defl = 2 * Math.atan(o.rg / b); const ph = N.linspace(0.05, Math.PI + defl - 0.05, 200), uu = ph.map(f => Math.sin(f) + o.rg / b * (1 - Math.cos(f))); lx = ph.map((f, i) => Math.cos(f) / uu[i]); ly = ph.map((f, i) => Math.sin(f) / uu[i]); }
    const deflF = (a.gr ? 4 : 2) * o.rg / b;
    // sweeps
    const aMin = a.gr ? Math.max(o.aEff / 10, 1.2 * (6 + 2 * o.e) * o.rg / (1 - o.e * o.e)) : o.aEff / 10;
    const as = N.logspace(aMin, Math.max(o.aEff * 10, aMin * 10), 50);
    const sw = as.map(x => { const q = schwOrbit({ ...v, a: x }, a), n = 36525 * 86400 / (2 * Math.PI * Math.sqrt(x ** 3 / q.GM)); return [q.formula * n * ARCSEC, q.exact * n * ARCSEC]; });
    const rr = N.logspace(a.gr ? 2.2 * o.rg : 0.2 * o.p, 6 * o.p / (1 - o.e), 160);
    const vGR = rr.map(r => (-o.GM / r + o.h2 / (2 * r * r) - (a.gr ? o.GM * o.h2 / (c2 * r ** 3) : 0)) / c2), vN = rr.map(r => (-o.GM / r + o.h2 / (2 * r * r)) / c2);
    const bs = N.logspace(a.gr ? 1.5 * bCrit : b / 10, Math.max(b * 100, 150 * bCrit), 50);
    const Eorb = -o.GM / (2 * o.aEff);
    return {
      scalars: [
        scalar('dphi', 'Perihelion advance per orbit', head, 'rad', { show: 'deg' }),
        scalar('prec_arcsec', 'Perihelion advance per Julian century (arcseconds)', head * perCentury * ARCSEC, '1'),
        scalar('dphi_formula', 'Advance per orbit, first-order formula', o.formula, 'rad'), scalar('dphi_exact', 'Advance per orbit, exact quadrature', o.exact, 'rad'),
        scalar('dphi_ode', 'Advance per orbit, direct integration of the orbit equation', ode.advance, 'rad', { text: Number.isFinite(ode.advance) ? undefined : 'Not defined: the orbit is circular to within 0.1 %' }),
        scalar('dphi_J', 'Quadrupole advance per orbit', dJ, 'rad'),
        scalar('T_orb', 'Orbital period (Kepler)', Torb, 's', { show: 'd' }),
        scalar('r_p', 'Periapsis distance', o.p / (1 + o.e), 'm', { show: 'AU' }), scalar('r_a', 'Apoapsis distance', o.p / (1 - o.e), 'm', { show: 'AU' }),
        scalar('h_L', 'Specific angular momentum', Math.sqrt(o.h2), 'm^2/s'), scalar('E_orb', 'Newtonian specific orbital energy', Eorb, 'J/kg'),
        scalar('delta', 'Deflection of light', defl, 'rad'), scalar('defl_arcsec', 'Deflection of light (arcseconds)', defl * ARCSEC, '1'),
        scalar('defl_formula', 'Deflection by the first-order formula (arcseconds)', deflF * ARCSEC, '1'),
        scalar('r_s', 'Schwarzschild radius', o.rs, 'm', { show: 'km' }), scalar('r_isco', 'Innermost stable circular orbit', 6 * o.rg, 'm', { show: 'km' }),
        scalar('r_ph', 'Photon-sphere radius', 3 * o.rg, 'm', { show: 'km' }), scalar('b_crit', 'Critical impact parameter for capture of light', bCrit, 'm', { show: 'km' }),
        scalar('f_isco', 'Orbital frequency at the innermost stable orbit (distant observer)', c ** 3 / (2 * Math.PI * Math.pow(6, 1.5) * o.GM), 'Hz'),
        scalar('eps_gr', 'Relativistic parameter GM/(c²p)', o.rg / o.p, '1'),
      ],
      series: [
        line('precession-sweep', 'Perihelion advance against orbit size', 'Semi-major axis', 'AU', as.map(x => x / AU), [{ label: 'First-order formula', data: sw.map(s => s[0]) }, { label: 'Exact quadrature', data: sw.map(s => s[1]), dash: true }], 'Advance per century', 'arcsec', { logx: true, logy: true }),
        line('veff', 'Effective potential', 'Radius', 'GM/c²', rr.map(r => r / o.rg), [{ label: a.gr ? 'Schwarzschild' : 'Newtonian', data: vGR }, { label: 'Newtonian', data: vN, dash: true }, { label: 'Orbital energy', data: rr.map(() => Eorb / c2), dash: true }], 'Effective potential', 'c²', { logx: true }),
        line('orbit', 'Orbit in the orbital plane', 'x', 'p', ode.xs, [{ label: 'Orbit', data: ode.ys }], 'y', 'p', { equal: true, note: 'Lengths in units of the semi-latus rectum. The advance is invisible on this scale unless the orbit is close to the central mass.' }),
        line('light-path', 'Path of the light ray', 'x', 'b', lx, [{ label: 'Light ray', data: ly }], 'y', 'b', { note: 'Lengths in units of the impact parameter; the mass sits at the origin.' }),
        line('deflection-sweep', 'Light deflection against impact parameter', 'Impact parameter', 'km', bs.map(x => x / 1000), [{ label: 'First-order formula', data: bs.map(x => (a.gr ? 4 : 2) * o.rg / x * ARCSEC) }], 'Deflection', 'arcsec', { logx: true, logy: true }),
      ],
      checks: [
        check('Orbit integration reproduces the exact advance', a.gr && Number.isFinite(ode.advance) && o.exact > 0 ? (ode.advance - o.exact) / o.exact : 0, 5e-3, 'Fourth-order Runge–Kutta in the orbital angle against quadrature of the first integral'),
        check('Bound orbit lies outside the stability limit', a.gr ? Math.max(0, (6 + 2 * o.e) * o.rg / o.p - 1) : 0, 0, 'p > (6 + 2e) GM/c²'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { gr: true, weak_field: true, test_particle: true, spherical: true }, out = [];
    const merc = { ...v, M: SUN.mass, a: 0.38709893 * AU, e: 0.20563, b: 6.957e8 };
    const r = this.solve(merc, on);
    out.push(bench('Mercury: exact quadrature vs Einstein\'s formula', val(r, 'dphi_exact'), val(r, 'dphi_formula'), 'Δφ = 6πGM/(c²a(1−e²)); agreement to first order in GM/(c²p)', 1e-5));
    out.push(bench('Mercury: direct integration vs exact quadrature', val(r, 'dphi_ode'), val(r, 'dphi_exact'), 'Orbit equation integrated over one radial period', 2e-3));
    out.push(bench('Solar-limb light deflection: numerical null geodesic vs 4GM/(c²b)', val(r, 'delta'), 4 * SUN.GM / (c2 * 6.957e8), 'First-order formula; second-order term is (15π/16)·GM/(c²b) relative', 1e-4));
    const o = schwOrbit({ ...merc, a: 20 * G * SUN.mass / c2, e: 0 }, on);
    out.push(bench('Circular orbit at r = 20 GM/c²: exact advance', o.exact, 2 * Math.PI * (1 / Math.sqrt(1 - 6 / 20) - 1), 'Δφ = 2π[(1 − 6GM/(c²r))^(−1/2) − 1]', 1e-9));
    out.push(bench('Innermost-stable-orbit frequency for one solar mass (Hz)', c ** 3 / (2 * Math.PI * Math.pow(6, 1.5) * SUN.GM), 2198, 'f = c³/(2π·6^{3/2}·GM) ≈ 2.2 kHz', 2e-3));
    return out;
  },
  validation: [
    { name: 'Anomalous perihelion advance of Mercury', ref: 'Clemence, G. M. (1947) Rev. Mod. Phys. 19, 361', note: 'Observed advance after subtracting planetary perturbations and precession of the equinoxes.',
      cases: [{ label: 'Mercury', inputs: { M: SUN.mass, a: 0.38709893 * AU, e: 0.20563 }, observable: 'prec_arcsec', observed: 43.11, sigma: 0.45 }] },
    { name: 'Deflection of radio waves by the Sun', ref: 'Shapiro, S. S. et al. (2004) Phys. Rev. Lett. 92, 121101', note: 'VLBI result γ = 0.9998 ± 0.0004 expressed as the equivalent deflection at the solar limb, (1 + γ)/2 × 1.7512″.',
      cases: [{ label: 'Ray grazing the solar limb', inputs: { M: SUN.mass, b: 6.957e8 }, observable: 'defl_arcsec', observed: 1.7510, sigma: 0.0004 }] },
  ],
  diagram(v, a) {
    const e = Math.min(v.e, 0.9), rx = 150, ry = rx * Math.sqrt(1 - e * e), cx = 200 - rx * e;
    return svg(`
      <ellipse cx="${cx}" cy="190" rx="${rx}" ry="${ry.toFixed(1)}" class="d-line"/>
      ${a.gr ? `<ellipse cx="${cx}" cy="190" rx="${rx}" ry="${ry.toFixed(1)}" class="d-dim" transform="rotate(14 200 190)"/>` : ''}
      ${S.circle(200, 190, 12, 'd-hazard')} ${S.text(200, 222, 'M')}
      ${S.circle(cx + rx, 190, 5, 'd-body')} ${S.text(cx + rx - 4, 176, 'perihelion', 'd-text d-small', 'end')}
      ${a.gr ? S.text(cx + rx - 30, 250, 'Δφ per orbit', 'd-text d-small') : ''}
      ${S.circle(500, 190, 16, 'd-hazard')} ${S.path('M400 120 Q500 150 610 105', 'd-pipe')} ${S.path('M400 120 L610 176', 'd-dim')}
      ${S.text(500, 100, 'light ray')} ${S.text(606, 150, 'δ', 'd-text', 'end')} ${S.dim(500, 172, 500, 140, '')} ${S.text(512, 160, 'b', 'd-text', 'start')}
      ${S.text(200, 40, `a = ${lab(v.a / AU, 'AU')}   e = ${lab(v.e)}`)} ${S.text(500, 40, `b = ${lab(v.b / 1000, 'km')}`)}
      ${S.text(320, 335, `r_s = 2GM/c² = ${lab(2 * G * v.M / c2 / 1000, 'km')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the secular advance of a planetary perihelion and the deflection of electromagnetic waves passing a massive body.',
    apparatus: ['Planetary radar or spacecraft ranging (for example to a Mercury orbiter)', 'Very-long-baseline radio interferometer observing quasars near the Sun', 'Optical astrometry during total solar eclipses, or space astrometry'],
    instruments: [{ name: 'Radar and transponder ranging', measures: 'Planet–Earth distance against time', range: '0.5–1.5 AU', resolution: 'metres' }, { name: 'VLBI group-delay measurement', measures: 'Angular position of radio sources', range: 'whole sky', resolution: '≈ 0.1 milliarcsecond' }, { name: 'Astrometric camera', measures: 'Apparent star positions near the solar limb', range: 'few solar radii', resolution: '≈ 0.1 arcsecond (ground), microarcseconds (space)' }],
    procedure: ['Fit an ephemeris including Newtonian perturbations of all planets to ranging data spanning many orbits.', 'Solve for the residual perihelion rate and compare with 6πGM/(c²a(1−e²)) per orbit.', 'Observe sources as the Sun passes near the line of sight and fit the deflection as a function of elongation to the 1/b law.'],
    controls: ['Solar-corona plasma delay removed with dual-frequency observations', 'Solar quadrupole moment bounded independently by helioseismology', 'Night-time comparison plates of the same star field for eclipse work'],
    signatures: ['Advance proportional to 1/(a(1−e²)) across the inner planets', 'Deflection proportional to 1/b and independent of frequency'],
    safety: ['Eye and instrument protection for solar observation', 'High-power radar transmitter exclusion zones'],
  },
  falsify: ['A perihelion advance of Mercury differing from 42.98″ per century by more than the uncertainty after planetary perturbations and solar oblateness are removed.', 'A light deflection at the solar limb different from 1.75″, or one that depends on wavelength in vacuum.', 'Stable circular orbits observed inside 6GM/c² of a non-rotating compact object.'],
  alternatives: [{ name: 'Newtonian gravity', text: 'No advance for a two-body orbit and half the light deflection; refuted.' }, { name: 'Parametrised post-Newtonian family', text: 'Advance scales as (2 + 2γ − β)/3 and deflection as (1 + γ)/2; observations constrain γ − 1 and β − 1 to about 10⁻⁵ and 10⁻⁴.' }, { name: 'Kerr geometry', text: 'Rotation of the central body adds frame dragging, shifts the innermost stable orbit and makes it depend on the sense of the orbit.' }, { name: 'Solar oblateness (Dicke)', text: 'A large solar quadrupole could mimic part of the advance; helioseismology shows it contributes under 0.1 %.' }],
  limits: 'Non-rotating, uncharged, spherically symmetric central mass; orbiting body treated as a test particle (or with the leading total-mass correction). Bound orbits must satisfy p > (6 + 2e)GM/c². Gravitational-radiation losses are neglected.',
  numerics: { method: 'Exact advance by midpoint quadrature of the transformed elliptic integral; orbit and light ray by fixed-step fourth-order Runge–Kutta in the angle with bisection to locate turning points', order: 4, stability: 'Step of 2π/4000 in angle', resolution: 'n_orb' },
  inverse: { series: 'precession-sweep', curve: 0, fit: ['M'] },
  extensions: ['Kerr geodesics with frame dragging', 'Shapiro time delay along the same ray', 'Orbital decay by gravitational radiation (binary pulsars)', 'Strong-field lensing and the black-hole shadow'],
};

// ================================================================== 5. GPS clock offsets
function clockRates(v, a, rOverride) {
  const GM = v.GM, Re = v.R_E, r = rOverride ?? (Re + v.h), om = 2 * Math.PI / v.T_rot;
  const J2 = EARTH.J2;
  // the geoid is an equipotential of gravity plus rotation, so the ground term is evaluated on the equator
  const phiG = GM / Re * (a.spherical ? 1 : 1 + J2 / 2), vG = om * Re * (a.spherical ? Math.cos(v.lat) : 1);
  const vS2 = GM / r;
  const gr = a.gr_term ? (phiG - GM / r) / c2 : 0;
  const sr = a.sr_term ? -(vS2 - vG * vG) / (2 * c2) : 0;
  return { gr, sr, net: gr + sr, r, vS: Math.sqrt(vS2), vG, phiG };
}

const gps = {
  id: 'gravitational-time-dilation-gps',
  title: 'Relativistic clock offsets in satellite navigation',
  module: [1, 2], klass: 'I', domains: ['relativity', 'space'],
  keywords: ['gps clock', 'gps', 'satellite clock', 'gravitational time dilation', 'gnss', 'navigation satellite', 'microseconds per day', 'clock offset', 'clock drift', 'galileo satellite', 'atomic clock in orbit', 'time dilation in orbit', 'positioning error'],
  summary: 'Rate offset of an orbiting clock relative to one on the ground: the gravitational and velocity terms, their sum, and the ranging error that accumulates if the offset is not corrected.',
  background: [
    'A clock higher in a gravitational potential runs fast and a moving clock runs slow. For a navigation satellite at about 20 200 km altitude the first effect is +45.7 microseconds per day and the second −7.2, a net gain near 38.5 microseconds per day relative to a clock on the rotating geoid. This is engineering fact: satellite oscillators are deliberately set low by 4.4647 parts in 10¹⁰ before launch so that they appear on frequency from the ground.',
    'Because position is obtained from signal travel times, an uncorrected timing error becomes a ranging error at the speed of light: roughly 11 kilometres per day.',
  ],
  phenomena: ['Gravitational time dilation', 'Special-relativistic time dilation', 'Eccentricity (periodic) clock term', 'Sagnac effect in the rotating frame'],
  laws: ['equivalence', 'sr', 'efe', 'gravitation'],
  refs: ['Ashby, N. (2003). Relativity in the Global Positioning System. Living Rev. Relativity 6, 1.', 'Hafele, J. C. & Keating, R. E. (1972). Around-the-world atomic clocks: predicted relativistic time gains. Science 177, 166–168.', 'Vessot, R. F. C. et al. (1980). Test of relativistic gravitation with a space-borne hydrogen maser. Phys. Rev. Lett. 45, 2081–2084.', 'Delva, P. et al. (2018). Gravitational redshift test using eccentric Galileo satellites. Phys. Rev. Lett. 121, 231101.', 'Kaplan, E. D. & Hegarty, C. J. (eds.) (2017). Understanding GPS/GNSS: Principles and Applications, 3rd ed., Artech House.'],
  inputs: [
    inp('h', 'Satellite altitude above the equatorial radius', 'km', 20184, { min: 200, max: 1e5, kind: 'geometry', aliases: ['altitude', 'orbit altitude', 'orbital altitude', 'height'], src: 'GPS semi-major axis 26 562 km less the equatorial radius' }),
    inp('GM', 'Gravitational parameter of the planet', 'm^3/s^2', 3.986004418e14, { min: 1e12, max: 2e17, kind: 'environment', src: 'Earth, IERS Conventions (2010)' }),
    inp('R_E', 'Equatorial radius of the planet', 'km', 6378.137, { min: 1000, max: 80000, kind: 'environment', src: 'WGS-84' }),
    inp('T_rot', 'Rotation period of the planet', 'h', 23.9344696, { min: 5, max: 1000, kind: 'environment', src: 'Sidereal day' }),
    inp('lat', 'Latitude of the ground clock', 'deg', 0, { min: -90, max: 90, kind: 'environment', env: 'latitude', aliases: ['latitude'] }),
    inp('e', 'Orbital eccentricity', '1', 0.01, { min: 0, max: 0.2, kind: 'geometry', aliases: ['eccentricity'], src: 'Typical GPS value; used only when the circular-orbit assumption is removed' }),
    inp('t_el', 'Elapsed time without correction', 'd', 1, { min: 0.01, max: 365, aliases: ['elapsed', 'after', 'per day'] }),
  ],
  assumptions: [
    asm('gr_term', 'The gravitational (potential) term is included.', { why: 'Required by the equivalence principle', alt: 'Only special-relativistic time dilation is applied.' }),
    asm('sr_term', 'The velocity (time-dilation) term is included.', { why: 'Required by special relativity', alt: 'Only the gravitational term is applied.' }),
    asm('circular', 'The orbit is circular, so the rate offset is constant.', { why: 'Navigation orbits are nearly circular', alt: 'An eccentric orbit adds a periodic term of amplitude 2e√(GMa)/c².' }),
    asm('spherical', 'The planet\'s potential is that of a point mass; the ground clock moves with the rotation at its latitude.', { why: 'Leading-order estimate', alt: 'The ground clock sits on the geoid, an equipotential of gravity plus rotation including the J₂ term, so its rate is the same at every latitude.' }),
  ],
  symbols: { r: ['Orbital radius', 'm'], x_gr: ['Fractional rate offset, gravitational', '1'], x_sr: ['Fractional rate offset, velocity', '1'], x_net: ['Net fractional rate offset', '1'], v_s: ['Satellite speed', 'm/s'], v_g: ['Ground-clock speed', 'm/s'], dt: ['Accumulated clock offset', 's'], dx: ['Ranging error', 'm'], dt_e: ['Amplitude of the eccentricity term', 's'], tau: ['Proper time of a clock', 's'], t: ['Coordinate time', 's'], Phi: ['Newtonian potential (negative)', 'J/kg'], u: ['Clock speed', 'm/s'] },
  equations: a => [
    eq('rate', 'Clock rate in a weak field', 'd(tau,t)', '1 + Phi/c^2 - u^2/(2*c^2)', { kind: 'law', origin: 'Schwarzschild metric to first order in Φ/c² and v²/c²' }),
    eq('rad', 'Orbital radius', 'r', 'R_E + h', { kind: 'definition' }),
    eq('vs', 'Circular orbital speed', 'v_s', 'sqrt(GM/r)', { kind: 'law', origin: 'Newton\'s law of gravitation' }),
    ...(a.gr_term ? [eq('gr', 'Gravitational offset', 'x_gr', 'GM/c^2*(1/R_E - 1/r)', { kind: 'derived', origin: 'Difference of potentials between orbit and ground', needs: ['gr_term'] })] : []),
    ...(a.sr_term ? [eq('sr', 'Velocity offset', 'x_sr', '-(v_s^2 - v_g^2)/(2*c^2)', { kind: 'derived', origin: 'Second-order Doppler (time dilation) of both clocks', needs: ['sr_term'] })] : []),
    eq('net', 'Net fractional offset', 'x_net', a.gr_term && a.sr_term ? 'x_gr + x_sr' : a.gr_term ? 'x_gr' : a.sr_term ? 'x_sr' : '0*x_gr', { kind: 'derived' }),
    eq('acc', 'Accumulated time offset', 'dt', 'x_net*t_el', { kind: 'derived' }),
    eq('rng', 'Ranging error', 'dx', 'c*dt', { kind: 'derived', origin: 'Pseudorange = c × travel time' }),
    ...(a.circular ? [] : [eq('ecc', 'Eccentricity term amplitude', 'dt_e', '2*e*sqrt(GM*r)/c^2', { kind: 'derived', origin: 'Periodic variation of potential and speed around an eccentric orbit (Ashby 2003)' })]),
  ],
  derivation: a => [
    { text: 'To first order the proper time of a clock at Newtonian potential Φ moving at speed v advances relative to coordinate time at the rate below.', tex: '\\frac{\\mathrm{d}\\tau}{\\mathrm{d}t} = 1 + \\frac{\\Phi}{c^2} - \\frac{v^2}{2c^2}' },
    { text: 'Taking the difference between the satellite and the ground clock gives a gravitational term, positive because the satellite is higher, and a velocity term, negative because it moves faster.', tex: '\\frac{\\Delta f}{f} = \\frac{GM}{c^2}\\left(\\frac{1}{R_E} - \\frac{1}{r}\\right) - \\frac{v_s^2 - v_g^2}{2c^2}' },
    { text: 'For a circular orbit v_s² = GM/r. The two terms cancel at r = 3R_E/2 (ignoring the slow ground rotation); below that altitude orbiting clocks lose time, above it they gain.', tex: '\\frac{\\Delta f}{f} = \\frac{GM}{c^2}\\left(\\frac{1}{R_E} - \\frac{3}{2r}\\right)' },
    { text: 'Navigation receivers convert time to distance at the speed of light, so the accumulated offset maps directly into range.', tex: '\\Delta x = c\\,\\frac{\\Delta f}{f}\\,t' },
  ],
  solve(v, a) {
    const q = clockRates(v, a), t = v.t_el;
    const Torb = 2 * Math.PI * Math.sqrt(q.r ** 3 / v.GM);
    const dtE = a.circular ? 0 : 2 * v.e * Math.sqrt(v.GM * q.r) / c2;
    const f0 = r => clockRates({ ...v, lat: Math.PI / 2 }, { ...a, spherical: true }, r).net;
    let rZero = NaN;
    if (a.gr_term && a.sr_term) { try { rZero = N.findRoot(f0, v.R_E * 1.0001, v.R_E * 50); } catch { rZero = NaN; } }
    const hs = N.logspace(200e3, 1e8, 80), sw = hs.map(x => clockRates(v, a, v.R_E + x));
    const tt = N.linspace(0, t, 200), day = 1e-6 / 86400; // one microsecond per day as a pure fraction
    const per = tt.map(x => dtE * Math.sin(2 * Math.PI * x / Torb));
    return {
      scalars: [
        scalar('x_net', 'Net fractional rate offset (satellite minus ground)', q.net, '1', { show: 'us/d' }),
        scalar('x_gr', 'Gravitational contribution', q.gr, '1', { show: 'us/d' }), scalar('x_sr', 'Velocity contribution', q.sr, '1', { show: 'us/d' }),
        scalar('dt', 'Accumulated clock offset', q.net * t, 's', { show: 'us' }), scalar('dx', 'Ranging error if uncorrected', c * q.net * t, 'm', { show: 'km' }),
        scalar('dx_rate', 'Growth rate of the ranging error', c * q.net, 'm/s', { show: 'km/d' }),
        scalar('r', 'Orbital radius', q.r, 'm', { show: 'km' }), scalar('v_s', 'Satellite speed', q.vS, 'm/s', { show: 'km/s' }), scalar('v_g', 'Ground-clock speed', q.vG, 'm/s'),
        scalar('T_orb', 'Orbital period', Torb, 's', { show: 'h' }),
        scalar('h_zero', 'Altitude at which the two effects cancel', rZero - v.R_E, 'm', { show: 'km', text: Number.isFinite(rZero) ? undefined : 'Not defined with one term removed' }),
        scalar('dt_e', 'Amplitude of the periodic eccentricity term', dtE, 's', { show: 'ns' }),
        scalar('df', 'Offset of a 10.23 MHz oscillator needed to compensate', -q.net * 10.23e6, 'Hz'),
      ],
      series: [
        line('rate-altitude', 'Rate offset against altitude', 'Altitude', 'km', hs.map(x => x / 1000), [{ label: 'Net', data: sw.map(s => s.net / day) }, { label: 'Gravitational', data: sw.map(s => s.gr / day), dash: true }, { label: 'Velocity', data: sw.map(s => s.sr / day), dash: true }], 'Rate offset', 'µs/day', { logx: true }),
        line('offset-time', 'Accumulated clock offset', 'Elapsed time', 'd', tt.map(x => x / 86400), [{ label: 'Net', data: tt.map((x, i) => (q.net * x + per[i]) * 1e6) }, { label: 'Gravitational only', data: tt.map(x => q.gr * x * 1e6), dash: true }, { label: 'Velocity only', data: tt.map(x => q.sr * x * 1e6), dash: true }], 'Clock offset', 'µs'),
        line('range-error', 'Ranging error if uncorrected', 'Elapsed time', 'd', tt.map(x => x / 86400), [{ label: 'Ranging error', data: tt.map((x, i) => c * (q.net * x + per[i]) / 1000) }], 'Error', 'km'),
      ],
      checks: [
        check('Net offset equals the sum of its parts', q.net - q.gr - q.sr, 1e-20, 'Additivity at first order'),
        check('Weak-field expansion is valid', Math.max(0, v.GM / (v.R_E * c2) - 1e-3), 0, 'GM/(Rc²) ≪ 1'),
      ],
      warnings: [],
    };
  },
  benchmarks(v, a) {
    const on = { gr_term: true, sr_term: true, circular: true, spherical: true }, e = { ...v, h: 20184e3, GM: 3.986004418e14, R_E: 6378137, T_rot: 86164.0905, lat: 0 }, out = [];
    const r = this.solve(e, on), d = 1e-6 / 86400;
    out.push(bench('GPS gravitational term (µs/day)', val(r, 'x_gr') / d, 45.7, 'Ashby (2003): about +45.7 µs/day', 3e-3));
    out.push(bench('GPS velocity term against a non-rotating ground clock (µs/day)', val(this.solve({ ...e, lat: Math.PI / 2 }, on), 'x_sr') / d, -7.2, 'Ashby (2003): about −7.2 µs/day', 3e-3));
    out.push(bench('Cancellation radius with a non-rotating ground clock', (val(r, 'h_zero') + e.R_E) / e.R_E, 1.5, 'r = 3R/2 from GM/c²(1/R − 3/(2r)) = 0', 1e-9));
    const rj = this.solve(e, { ...on, spherical: false });
    out.push(bench('Net fractional offset with the geoid potential', val(rj, 'x_net'), 4.4647e-10, 'Factory frequency offset of GPS clocks (Ashby 2003)', 2e-3));
    return out;
  },
  validation: [
    { name: 'Frequency offset of the first GPS caesium clock in orbit', ref: 'Ashby, N. (2003) Living Rev. Relativity 6, 1, §5 (NTS-2 satellite, 1977)', note: 'The clock was run uncorrected for 20 days; the measured offset was 442.5 parts in 10¹² against a prediction of 446.5.',
      cases: [{ label: 'NTS-2, 1977', inputs: { h: 20184e3, lat: 0 }, assumptions: { spherical: false }, observable: 'x_net', observed: 4.425e-10, sigma: 0.05e-10 }] },
  ],
  diagram(v) {
    const R = 60, ro = Math.min(150, R * (1 + v.h / v.R_E) * 0.5 + 40);
    return svg(`
      ${S.circle(220, 190, R, 'd-liquid')} ${S.text(220, 194, 'planet')}
      <circle cx="220" cy="190" r="${ro}" class="d-dim" fill="none"/>
      ${S.rect(220 + ro - 12, 178, 24, 14, 'd-body', 2)} ${S.arrow(220 + ro, 172, 220 + ro, 120)} ${S.text(220 + ro + 8, 132, 'v_s', 'd-text', 'start')}
      ${S.circle(220 + R, 190, 4, 'd-hazard')} ${S.text(220 + R - 8, 180, 'ground clock', 'd-text d-small', 'end')}
      ${S.path(`M${220 + ro - 12} 190 L${220 + R + 4} 190`, 'd-arrow')}
      ${S.text(470, 110, 'higher potential: clock runs fast', 'd-text', 'start')} ${S.text(470, 134, 'faster motion: clock runs slow', 'd-text', 'start')}
      ${S.text(470, 180, `altitude ${lab(v.h / 1000, 'km')}`, 'd-text', 'start')} ${S.text(470, 204, `radius ratio r/R = ${lab(1 + v.h / v.R_E)}`, 'd-text', 'start')}
    `);
  },
  experiment: {
    objective: 'Measure the frequency of an orbiting atomic clock against identical clocks on the ground before any relativistic correction is applied.',
    apparatus: ['Caesium, rubidium or hydrogen-maser clock on a satellite or sounding rocket', 'Ground station with a reference clock ensemble', 'Two-way microwave or optical link to cancel first-order Doppler shift'],
    instruments: [{ name: 'Dual-frequency carrier-phase receiver', measures: 'Clock phase against ground time', range: 'continuous', resolution: '≈ 20 ps' }, { name: 'Satellite laser ranging', measures: 'Orbit radius and eccentricity', range: '10³–10⁵ km', resolution: 'centimetres' }, { name: 'Hydrogen-maser reference', measures: 'Stable ground time scale', range: 'continuous', resolution: 'fractional 10⁻¹⁵ per day' }],
    procedure: ['Compare the clocks side by side before launch.', 'In orbit, track the clock phase for several weeks with the on-board frequency synthesiser uncorrected.', 'Fit a linear drift (net offset) and a once-per-orbit term (eccentricity) and compare with prediction.', 'Enable the correction and confirm the residual is consistent with zero.'],
    controls: ['Ionospheric delay removed with two frequencies', 'Independent orbit determination by laser ranging', 'Comparison among several satellites at different eccentricities'],
    signatures: ['Linear gain of about 38 µs/day for GPS orbits', 'Periodic term proportional to eccentricity with the orbital period', 'Sign reversal for clocks in low orbit (below about 3200 km)'],
    safety: ['Radio-frequency exposure limits at uplink antennas', 'Laser-ranging aircraft-avoidance procedures'],
  },
  falsify: ['An orbiting clock whose rate, compared through a link free of first-order Doppler shift, does not differ from ground clocks by the predicted fraction within the measurement uncertainty.', 'A gravitational red-shift that depends on the type of atomic clock.', 'Navigation solutions that remain accurate with the relativistic corrections switched off.'],
  alternatives: [{ name: 'Local-position-invariance violation', text: 'Parametrised as a red-shift of (1 + α)ΔΦ/c²; Gravity Probe A and eccentric Galileo satellites bound |α| to a few parts in 10⁵.' }, { name: 'Full post-Newtonian treatment', text: 'Adds the Sagnac correction for signal propagation in the rotating frame, Shapiro delay (millimetres to centimetres) and tidal potentials of the Sun and Moon.' }],
  limits: 'First order in GM/(rc²) and v²/c². Ground clock on the equatorial radius (or the geoid when the J₂ option is selected). Signal-propagation effects (Sagnac, Shapiro, atmosphere) are not included.',
  numerics: { method: 'Closed-form weak-field rates; safeguarded secant root for the cancellation altitude' },
  optimise: { objective: 'x_net', sense: 'min', vars: ['h'], note: 'The net offset is most negative for the lowest orbits and crosses zero near half a planetary radius of altitude.' },
  inverse: { series: 'rate-altitude', curve: 0, fit: ['GM'] },
  extensions: ['Sagnac correction for receivers on the rotating Earth', 'Inter-satellite links and relativistic geodesy with optical clocks', 'Clock offsets for lunar and Mars navigation systems'],
};

// ================================================================== 6. black-hole properties
const kretschSchw = (rs, r) => 12 * rs * rs / r ** 6;
function hayward(rs, ell, r) {
  const A = rs * ell * ell, D = r ** 3 + A;
  const q = rs * r * r / D, q1 = rs * (2 * r * A - r ** 4) / (D * D), q2 = rs * (2 * A * A - 14 * A * r ** 3 + 2 * r ** 6) / D ** 3;
  // Kretschmann scalar of a static metric with g_tt = -(1 - q): K = q''² + 4q'²/r² + 4q²/r⁴
  return { f: 1 - q, K: q2 * q2 + 4 * (q1 / r) ** 2 + 4 * (q / (r * r)) ** 2 };
}

const blackHole = {
  id: 'black-hole-properties',
  title: 'Black-hole properties, Hawking radiation and the central singularity',
  module: [1, 2], klass: ['I', 'III'], domains: ['relativity', 'thermal', 'quantum'],
  keywords: ['black hole', 'event horizon', 'schwarzschild radius', 'hawking radiation', 'hawking temperature', 'bekenstein', 'black hole entropy', 'evaporation', 'singularity', 'spaghettification', 'tidal force at horizon', 'kretschmann', 'regular black hole', 'surface gravity'],
  summary: 'Horizon size, surface gravity, Hawking temperature, entropy, evaporation time and tidal stretching for a non-rotating black hole, with the curvature singularity reported as a breakdown of the classical theory.',
  background: [
    'A non-rotating, uncharged black hole of mass M has an event horizon at the Schwarzschild radius 2GM/c². Classical general relativity is well tested outside the horizon. Applying quantum field theory on that background, Hawking showed that the hole radiates as a black body of temperature ħc³/(8πGMk_B) and carries the Bekenstein–Hawking entropy k_Bc³A/(4Għ). These semiclassical results are widely accepted on theoretical grounds but have not been observed: for astrophysical holes the temperature is far below that of the cosmic background.',
    'Inside the horizon the classical solution ends in a singularity where the curvature invariant K = 48G²M²/(c⁴r⁶) diverges. This is not a prediction about nature but the point at which the classical theory ceases to apply; a quantum theory of gravity is expected to replace it. For illustration only, the model offers a regularised metric of Hayward type with an invented core length, in which the curvature stays finite. That alternative is hypothetical.',
  ],
  phenomena: ['Event horizon', 'Hawking radiation', 'Black-hole thermodynamics', 'Tidal stretching', 'Curvature singularity'],
  laws: ['efe', 'second', 'stefan', 'energy'],
  refs: ['Schwarzschild, K. (1916). Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen Theorie. Sitzungsber. Preuss. Akad. Wiss., 189–196.', 'Hawking, S. W. (1975). Particle creation by black holes. Commun. Math. Phys. 43, 199–220.', 'Bekenstein, J. D. (1973). Black holes and entropy. Phys. Rev. D 7, 2333–2346.', 'Penrose, R. (1965). Gravitational collapse and space-time singularities. Phys. Rev. Lett. 14, 57–59.', 'Hayward, S. A. (2006). Formation and evaporation of nonsingular black holes. Phys. Rev. Lett. 96, 031103.', 'Page, D. N. (1976). Particle emission rates from a black hole: massless particles from an uncharged, nonrotating hole. Phys. Rev. D 13, 198–206.', 'Wald, R. M. (1984). General Relativity, University of Chicago Press.'],
  inputs: [
    inp('M', 'Black-hole mass', 'Msun', 10, { min: 1e-19, max: 1e11, aliases: ['mass', 'solar mass', 'solar masses'], src: 'Typical stellar-mass black hole' }),
    inp('L_b', 'Length of the infalling body', 'm', 2, { min: 0.01, max: 1e6, kind: 'geometry', aliases: ['body length', 'height', 'tall', 'astronaut'] }),
    inp('x_r', 'Radius at which local quantities are evaluated, in Schwarzschild radii', '1', 1, { min: 1e-3, max: 1e3, kind: 'geometry', aliases: ['radius', 'schwarzschild radii'] }),
    inp('T_bg', 'Temperature of the surrounding radiation', 'K', 2.725, { min: 0, max: 1e4, kind: 'environment', aliases: ['background temperature', 'cmb'], src: 'Cosmic microwave background; used only when the hole is not isolated' }),
    inp('ell', 'Core length scale of the regularised metric', 'm', 3000, { min: 1e-35, max: 1e9, kind: 'hypothetical', aliases: ['core length', 'regularisation length'], src: 'Invented for illustration. A Planck-scale value (1.6 × 10⁻³⁵ m) is the usual conjecture; a large value is used so the effect is visible on a plot.' }),
  ],
  assumptions: [
    asm('classical', 'The Schwarzschild solution is used all the way to r → 0, where the curvature diverges.', { why: 'It is the classical prediction; its divergence marks the limit of the theory', alt: 'A hypothetical Hayward-type regular metric with core length ℓ replaces it: the centre becomes a region of finite curvature. No evidence supports this particular form.' }),
    asm('hawking', 'The hole emits Hawking radiation as a black body of its horizon area.', { why: 'Semiclassical prediction (Hawking 1975)', alt: 'A purely classical hole: zero temperature, no emission, area can never decrease.' }),
    asm('isolated', 'The hole is isolated in empty space at zero temperature.', { why: 'Defines the intrinsic evaporation time', alt: 'The hole absorbs ambient black-body radiation at T_bg over its capture cross-section 27πG²M²/c⁴ and evaporates only if hotter than its surroundings.' }),
  ],
  symbols: { r_s: ['Schwarzschild radius', 'm'], A_h: ['Horizon area', 'm^2'], kappa: ['Surface gravity', 'm/s^2'], T_H: ['Hawking temperature', 'K'], S_BH: ['Bekenstein–Hawking entropy', 'J/K'], P_H: ['Hawking luminosity', 'W'], t_ev: ['Evaporation time', 's'], K: ['Kretschmann curvature scalar', '1/m^4'], r: ['Radial coordinate', 'm'], da: ['Tidal acceleration across the body', 'm/s^2'], f_m: ['Metric function −g_tt', '1'], t: ['Time', 's'], M_0: ['Initial mass', 'kg'], P_abs: ['Power absorbed from the surroundings', 'W'] },
  equations: a => [
    eq('rs', 'Schwarzschild radius', 'r_s', '2*G*M/c^2', { kind: 'derived', origin: 'Schwarzschild solution of the Einstein field equations' }),
    eq('area', 'Horizon area', 'A_h', '4*pi*r_s^2', { kind: 'definition' }),
    eq('kap', 'Surface gravity', 'kappa', 'c^4/(4*G*M)', { kind: 'derived', origin: 'Killing-horizon surface gravity' }),
    eq('tide', 'Tidal acceleration across a body', 'da', '2*G*M*L_b/r^3', { kind: 'derived', origin: 'Geodesic deviation, radial component' }),
    a.classical
      ? eq('K', 'Kretschmann scalar', 'K', '48*G^2*M^2/(c^4*r^6)', { kind: 'derived', origin: 'Riemann tensor of the Schwarzschild metric; diverges as r → 0', needs: ['classical'] })
      : eq('K', 'Regularised metric function (Hayward type)', 'f_m', '1 - r_s*r^2/(r^3 + r_s*ell^2)', { kind: 'hypothesis', origin: 'Invented regular metric (Hayward 2006); not derived from an established theory' }),
    ...(a.hawking ? [
      eq('TH', 'Hawking temperature', 'T_H', 'hbar*c^3/(8*pi*G*M*k_B)', { kind: 'law', origin: 'Quantum field theory on the Schwarzschild background (Hawking 1975)', needs: ['hawking'] }),
      eq('S', 'Bekenstein–Hawking entropy', 'S_BH', 'k_B*c^3*A_h/(4*G*hbar)', { kind: 'law', origin: 'First law of black-hole mechanics with the Hawking temperature' }),
      eq('P', 'Hawking luminosity', 'P_H', 'hbar*c^6/(15360*pi*G^2*M^2)', { kind: 'derived', origin: 'Stefan–Boltzmann law over the horizon area' }),
      a.isolated ? eq('ev', 'Mass loss', 'c^2*d(M,t)', '-P_H', { kind: 'law', origin: 'Conservation of energy', needs: ['isolated'] })
        : eq('ev', 'Mass loss with absorption', 'c^2*d(M,t)', '-P_H + P_abs', { kind: 'law', origin: 'Conservation of energy' }),
      eq('tev', 'Evaporation time', 't_ev', '5120*pi*G^2*M^3/(hbar*c^4)', { kind: 'derived', origin: 'Integration of the mass-loss equation' }),
      ...(a.isolated ? [] : [eq('abs', 'Absorbed power', 'P_abs', '27*pi*G^2*M^2/c^4*sigma_SB*T_bg^4', { kind: 'derived', origin: 'Black-body flux over the photon capture cross-section' })]),
    ] : [eq('ev', 'Mass is constant', 'M', 'M_0', { kind: 'law', origin: 'Classical area theorem: no emission' })]),
  ],
  derivation: a => [
    { text: 'The Schwarzschild metric function vanishes at the horizon radius.', tex: 'f(r) = 1 - \\frac{2GM}{c^2 r} = 0\\ \\Rightarrow\\ r_s = \\frac{2GM}{c^2}' },
    { text: 'A quantum field on this background is in a thermal state when viewed from far away, at a temperature fixed by the surface gravity.', tex: 'T_H = \\frac{\\hbar\\,\\kappa}{2\\pi c\\,k_B} = \\frac{\\hbar c^3}{8\\pi G M k_B}' },
    { text: 'The first law dE = T dS with E = Mc² then gives an entropy proportional to the horizon area.', tex: 'S_{BH} = \\frac{k_B c^3 A}{4 G \\hbar} = \\frac{4\\pi G k_B M^2}{\\hbar c}' },
    { text: 'Treating the horizon as a black body gives the luminosity; integrating the mass loss gives the lifetime.', tex: 'P = \\frac{\\hbar c^6}{15360\\,\\pi G^2 M^2},\\qquad t_{ev} = \\frac{5120\\,\\pi G^2 M^3}{\\hbar c^4}' },
    { text: a.classical ? 'The curvature invariant built from the full Riemann tensor is finite at the horizon and diverges at the centre. The divergence signals that the classical theory has been pushed beyond its domain.' : 'In the hypothetical regular metric the mass function is smoothed over a length ℓ; near the centre the geometry is de Sitter and the curvature tends to a constant.', tex: a.classical ? 'K = R_{\\alpha\\beta\\gamma\\delta}R^{\\alpha\\beta\\gamma\\delta} = \\frac{48\\,G^2M^2}{c^4 r^6}\\ \\xrightarrow{r\\to 0}\\ \\infty' : 'f(r) = 1 - \\frac{r_s r^2}{r^3 + r_s\\ell^2},\\qquad K(0) = \\frac{24}{\\ell^4}' },
  ],
  solve(v, a) {
    const M = v.M, rs = 2 * G * M / c2, A = 4 * Math.PI * rs * rs, kappa = c ** 4 / (4 * G * M), r = v.x_r * rs, warnings = [];
    const TH = a.hawking ? hbar * c ** 3 / (8 * Math.PI * G * M * kB) : 0;
    const Sof = m => 4 * Math.PI * G * kB * m * m / (hbar * c), S = Sof(M);
    const PH = a.hawking ? hbar * c ** 6 / (15360 * Math.PI * G * G * M * M) : 0;
    const Pabs = a.isolated ? 0 : 27 * Math.PI * G * G * M * M / c ** 4 * C.sigma_SB * v.T_bg ** 4;
    const tev = 5120 * Math.PI * G * G * M ** 3 / (hbar * c ** 4);
    const grows = !a.hawking || (!a.isolated && Pabs >= PH);
    const Mcrit = v.T_bg > 0 ? hbar * c ** 3 / (8 * Math.PI * G * kB * v.T_bg) : Infinity;
    if (a.hawking && !a.isolated && grows) warnings.push('The hole is colder than its surroundings and gains mass faster than it radiates; it will not evaporate until the background has cooled below its Hawking temperature.');
    const tidal = x => 2 * G * M * v.L_b / x ** 3;
    let Kr, K0, rH = rs, noHorizon = false;
    if (a.classical) { Kr = kretschSchw(rs, r); K0 = Infinity; }
    else {
      Kr = hayward(rs, v.ell, r).K; K0 = 24 / v.ell ** 4;
      // outer horizon of the regular metric exists only if ℓ ≤ (4/(3√3))·GM/c²
      if (v.ell > 4 / (3 * Math.sqrt(3)) * rs / 2) { noHorizon = true; rH = NaN; warnings.push('The core length exceeds 0.77 GM/c²: the hypothetical regular metric then has no horizon at all and describes a horizonless compact object.'); }
      else { const rMin = Math.cbrt(2 * rs * v.ell * v.ell); try { rH = N.findRoot(x => hayward(rs, v.ell, x).f, rMin, 2 * rs); } catch { rH = rs; } }
      warnings.push('The regularised interior is a hypothetical construction. Quantities outside the horizon are unaffected for ℓ ≪ r_s; nothing is known observationally about the interior.');
    }
    const xs = N.logspace(1e-3, 10, 120), rr = xs.map(x => x * rs);
    const Ks = rr.map(x => kretschSchw(rs, x) * rs ** 4), Kh = rr.map(x => hayward(rs, v.ell, x).K * rs ** 4);
    const fS = xs.map(x => 1 - 1 / x), fH = rr.map(x => hayward(rs, v.ell, x).f);
    const ms = N.logspace(1e8, 1e41, 100);
    const dM = 1e-4 * M, firstLaw = a.hawking ? TH * (Sof(M + dM) - Sof(M - dM)) / (2 * dM * c2) - 1 : 0;
    return {
      scalars: [
        scalar('r_s', 'Schwarzschild radius', rs, 'm', { show: 'km' }), scalar('A_h', 'Horizon area', A, 'm^2'),
        scalar('kappa', 'Surface gravity', kappa, 'm/s^2'), scalar('rho_m', 'Mean density inside the horizon', M / (4 / 3 * Math.PI * rs ** 3), 'kg/m^3'),
        scalar('T_H', 'Hawking temperature', TH, 'K'), scalar('S_BH', 'Bekenstein–Hawking entropy', S, 'J/K'), scalar('S_kB', 'Entropy in units of the Boltzmann constant', S / kB, '1'),
        scalar('P_H', 'Hawking luminosity', PH, 'W'),
        scalar('P_net', 'Net power radiated', PH - Pabs, 'W'),
        scalar('t_ev', 'Evaporation time', grows ? Infinity : tev, 's', { show: 'yr', text: grows ? (a.hawking ? 'Does not evaporate while colder than its surroundings' : 'Never: a classical black hole does not radiate') : undefined }),
        scalar('M_crit', 'Mass below which the hole is hotter than its surroundings', Mcrit, 'kg', { text: Number.isFinite(Mcrit) ? undefined : 'Any mass (zero background temperature)' }),
        scalar('da_h', 'Tidal acceleration across the body at the horizon', tidal(rs), 'm/s^2'), scalar('da_r', 'Tidal acceleration across the body at the chosen radius', tidal(r), 'm/s^2'),
        scalar('K_h', 'Kretschmann scalar at the horizon', 12 / rs ** 4, '1/m^4'), scalar('K_r', 'Kretschmann scalar at the chosen radius', Kr, '1/m^4', a.classical ? {} : { status: 'hypothetical' }),
        scalar('K_0', 'Kretschmann scalar at the centre', K0, '1/m^4', a.classical ? { text: 'Diverges: the classical theory breaks down at r = 0' } : { status: 'hypothetical' }),
        scalar('r_H', 'Outer horizon radius', rH, 'm', { show: 'km', text: noHorizon ? 'No horizon for this core length' : undefined, ...(a.classical ? {} : { status: 'hypothetical' }) }),
        scalar('lambda_pk', 'Wavelength of peak Hawking emission', a.hawking ? 2.897771955e-3 / TH : Infinity, 'm', { text: a.hawking ? undefined : 'No emission' }),
      ],
      series: [
        line('curvature', 'Curvature invariant against radius', 'Radius', 'r_s', xs, [{ label: 'Schwarzschild: K r_s⁴ = 12 (r_s/r)⁶', data: Ks }, ...(a.classical ? [] : [{ label: 'Hypothetical regular core', data: Kh, dash: true }])], 'K r_s⁴', '–', { logx: true, logy: true, note: a.classical ? 'The classical curve rises without limit toward r = 0: the theory fails there.' : 'The dashed curve is a hypothetical alternative, not an established result.' }),
        line('metric', 'Metric function f(r) = −g_tt', 'Radius', 'r_s', xs, [{ label: 'Schwarzschild', data: fS.map(x => Math.max(x, -20)) }, ...(a.classical ? [] : [{ label: 'Hypothetical regular core', data: fH, dash: true }])], 'f', '–', { logx: true, note: 'The horizon is where f = 0. The Schwarzschild curve is truncated at −20.' }),
        line('mass-sweep', 'Hawking temperature and lifetime against mass', 'Mass', 'kg', ms, [{ label: 'Temperature (K)', data: ms.map(m => hbar * c ** 3 / (8 * Math.PI * G * m * kB)) }, { label: 'Evaporation time (yr)', data: ms.map(m => 5120 * Math.PI * G * G * m ** 3 / (hbar * c ** 4) / YR), dash: true }], 'Value', 'K or yr', { logx: true, logy: true }),
        line('tidal', 'Tidal acceleration across the body', 'Radius', 'r_s', xs, [{ label: 'Tidal acceleration', data: rr.map(tidal) }], 'Acceleration', 'm/s²', { logx: true, logy: true }),
      ],
      checks: [
        check('First law: T dS = c² dM', firstLaw, 1e-6, 'Numerical derivative of the entropy against the Hawking temperature'),
        check('Entropy equals a quarter of the horizon area in Planck units', S / (kB * c ** 3 * A / (4 * G * hbar)) - 1, 1e-12, 'S = k_B c³A/(4Għ) against 4πGk_BM²/(ħc)'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { classical: true, hawking: true, isolated: true }, r = this.solve({ ...v, M: SUN.mass }, on), out = [];
    out.push(bench('Schwarzschild radius of one solar mass (km)', val(r, 'r_s') / 1000, 2.953, '2GM/c² = 2.953 km', 1e-3));
    out.push(bench('Hawking temperature of one solar mass (K)', val(r, 'T_H'), 6.17e-8, 'ħc³/(8πGMk_B) ≈ 6.17 × 10⁻⁸ K', 2e-3));
    out.push(bench('Entropy of one solar mass in units of k_B', val(r, 'S_kB'), 1.049e77, '4πGM²/(ħc) ≈ 1.05 × 10⁷⁷', 2e-3));
    out.push(bench('Luminosity equals Stefan–Boltzmann law over the horizon', val(r, 'P_H'), C.sigma_SB * val(r, 'A_h') * val(r, 'T_H') ** 4, 'P = σ A T⁴ with σ = π²k_B⁴/(60ħ³c²)', 1e-6));
    out.push(bench('Regular metric: central curvature tends to the de Sitter value', hayward(2953, 100, 1e-3).K, 24 / 100 ** 4, 'K(0) = 24/ℓ⁴', 1e-6));
    out.push(bench('Regular metric reduces to Schwarzschild far outside the core', hayward(2953, 1, 2953).K, kretschSchw(2953, 2953), 'ℓ ≪ r', 1e-5));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.circle(220, 185, 90, 'd-hazard')} ${S.circle(220, 185, 135, 'd-dim')}
      ${a.classical ? S.circle(220, 185, 3, 'd-body') : S.circle(220, 185, 22, 'd-liquid')}
      ${S.text(220, 172, a.classical ? 'singularity: K → ∞' : 'regular core (hypothetical)', 'd-text d-small')}
      ${S.text(220, 290, 'event horizon r_s')} ${S.text(220, 338, 'photon sphere 1.5 r_s', 'd-text d-small')}
      ${S.rect(388, 170, 12, 34, 'd-body', 2)} ${S.arrow(394, 168, 394, 140)} ${S.arrow(394, 206, 394, 234)} ${S.text(410, 190, 'tidal stretch', 'd-text d-small', 'start')}
      ${a.hawking ? [0, 1, 2].map(i => S.arrow(290 + 8 * i, 110 - 14 * i, 330 + 12 * i, 70 - 18 * i, 'd-arrow d-heat')).join('') + S.text(380, 50, 'Hawking radiation', 'd-text', 'start') : ''}
      ${S.text(470, 250, `M = ${lab(v.M / SUN.mass, 'M☉')}`, 'd-text', 'start')} ${S.text(470, 274, `r_s = ${lab(2 * G * v.M / c2 / 1000, 'km')}`, 'd-text', 'start')}
    `);
  },
  experiment: {
    objective: 'Test the exterior geometry and horizon-scale structure observationally, and the thermal-emission mechanism in laboratory analogues, since Hawking radiation from astrophysical holes is unobservably weak.',
    apparatus: ['Gravitational-wave interferometers recording binary mergers and ring-down', 'Millimetre-wave very-long-baseline array imaging the shadow of a supermassive black hole', 'Analogue horizons: flowing Bose–Einstein condensate or water-tank flow with a trans-critical region'],
    instruments: [{ name: 'Laser interferometer', measures: 'Strain waveform; ring-down frequency and damping fix mass and spin', range: '10 Hz–5 kHz', resolution: 'strain 10⁻²³ /√Hz' }, { name: 'VLBI correlator', measures: 'Angular diameter of the shadow, 3√3·GM/c² in radius', range: 'tens of microarcseconds', resolution: '≈ 20 µas' }, { name: 'Density–density correlation imaging of a condensate', measures: 'Correlated phonon pairs across the sonic horizon', range: 'µm', resolution: 'single-shot atom-number noise' }],
    procedure: ['Fit merger waveforms and check that the final area is not smaller than the sum of the initial areas.', 'Compare the measured shadow diameter with the value predicted from the independently known mass and distance.', 'In the analogue system, measure the emission spectrum and compare its temperature with the analogue surface gravity.'],
    controls: ['Independent mass estimates from stellar or gas dynamics', 'Analogue runs without a horizon (sub-critical flow)'],
    signatures: ['Ring-down spectrum fixed by mass and spin alone', 'Shadow diameter of 2 × 3√3 GM/c²', 'Thermal spectrum with T proportional to surface gravity in analogue systems'],
    safety: ['Standard laser, cryogenic and vacuum precautions'],
  },
  falsify: ['A merger remnant whose horizon area is smaller than the total initial area (violating the area theorem at the classical level).', 'A shadow size or ring-down spectrum inconsistent with the Kerr–Schwarzschild family for the measured mass.', 'Detection of evaporating primordial holes with a final burst inconsistent with T ∝ 1/M.', 'For the hypothetical regular core: any observable exterior effect would have to scale with ℓ/r_s; none is predicted for Planck-scale ℓ, so the alternative is at present untestable.'],
  alternatives: [{ name: 'Kerr black hole', text: 'Real holes rotate; the horizon, temperature and entropy then depend on spin and the singularity is a ring.' }, { name: 'Regular black holes (Bardeen, Hayward)', text: 'Replace the singular centre by a de Sitter-like core; require matter violating the strong energy condition.' }, { name: 'Horizonless compact objects', text: 'Gravastars, fuzzballs and similar proposals remove the horizon; constrained by the absence of surface emission and of ring-down echoes.' }, { name: 'Grey-body corrected emission', text: 'Page (1976) computed species-dependent emission rates that differ from the simple black-body estimate used here by factors of order unity.' }],
  limits: 'Non-rotating, uncharged hole. Luminosity and lifetime use the black-body estimate for photons only and ignore grey-body factors and additional particle species, so the lifetime is an upper estimate of order of magnitude. Semiclassical results require M far above the Planck mass. The interior description is not established physics.',
  numerics: { method: 'Closed forms; analytic derivatives of the regular metric function; safeguarded secant root for its horizon' },
  inverse: { series: 'mass-sweep', curve: 0, fit: ['M'] },
  extensions: ['Kerr–Newman family with spin and charge', 'Grey-body factors and emission of massive species', 'Penrose diagram and infalling-observer proper time to the centre', 'Information-loss problem and the Page curve'],
};

// ================================================================== 7. FRW cosmology
function frw(v, a) {
  const H0 = v.H_0, Or = a.radiation ? v.Omega_r : 0, Om = v.Omega_m, w = a.lambda ? -1 : v.w_0;
  const OL = a.flat ? 1 - Om - Or : v.Omega_L, Ok = a.flat ? 0 : 1 - Om - Or - OL;
  // R(a) = a⁴E²(a); the substitution a = x² removes the square-root singularity at the big bang
  const Rf = s => Math.max(Or + Om * s + Ok * s * s + OL * Math.pow(s, 1 - 3 * w), 1e-12);
  const E = s => Math.sqrt(Rf(s)) / (s * s);
  const fT = x => (x === 0 ? 0 : 2 * x ** 3 / Math.sqrt(Rf(x * x)));
  const fD = x => (x === 0 ? (Or > 0 ? 0 : 2 / Math.sqrt(Om)) : 2 * x / Math.sqrt(Rf(x * x)));
  const tOf = (s, n = 800) => simpson(fT, 0, Math.sqrt(s), n) / H0;
  const chi = s => simpson(fD, Math.sqrt(s), 1, 400) * c / H0;
  const DM = s => { const x = chi(s), k = Math.sqrt(Math.abs(Ok)) * H0 / c; return Ok > 1e-9 ? Math.sinh(k * x) / k : Ok < -1e-9 ? Math.sin(k * x) / k : x; };
  return { H0, Or, Om, OL, Ok, w, Rf, E, fT, tOf, chi, DM, q0: Or + Om / 2 + OL * (1 + 3 * w) / 2 };
}
const GYR = 3.15576e16, MPC = 3.0856775814913673e22;

const cosmology = {
  id: 'frw-cosmology',
  title: 'Expansion history of a Friedmann universe',
  module: [1, 2], klass: 'I', domains: ['relativity', 'space'],
  keywords: ['age of the universe', 'friedmann', 'cosmology', 'hubble constant', 'expansion of the universe', 'scale factor', 'dark energy', 'lookback time', 'luminosity distance', 'redshift distance', 'lambda cdm', 'deceleration parameter', 'big bang', 'cosmological constant', 'universe'],
  summary: 'Integrates the Friedmann equation for given matter, radiation and dark-energy densities: scale factor against time, age, lookback time and distances against redshift.',
  background: [
    'A universe that is homogeneous and isotropic on large scales is described by the Friedmann–Lemaître–Robertson–Walker metric, and Einstein\'s equations reduce to the Friedmann equation for the scale factor. Each component dilutes at its own rate as space expands: radiation as a⁻⁴, matter as a⁻³, curvature as a⁻², while a cosmological constant does not dilute at all.',
    'With the densities inferred from the cosmic microwave background, baryon acoustic oscillations and supernovae (the flat ΛCDM model), the age of the universe is 13.8 billion years and the expansion has been accelerating for roughly the last six billion. The framework is well established; the nature of dark matter and dark energy is not, and the value of the Hubble constant is currently disputed at the level of several per cent between early- and late-universe methods.',
  ],
  phenomena: ['Cosmic expansion', 'Cosmological redshift', 'Matter–radiation equality', 'Late-time acceleration', 'Spatial curvature'],
  laws: ['efe', 'energy', 'mass'],
  refs: ['Friedmann, A. (1922). Über die Krümmung des Raumes. Zeitschrift für Physik 10, 377–386.', 'Planck Collaboration (2020). Planck 2018 results. VI. Cosmological parameters. Astron. Astrophys. 641, A6.', 'Riess, A. G. et al. (1998). Observational evidence from supernovae for an accelerating universe and a cosmological constant. Astron. J. 116, 1009–1038.', 'Perlmutter, S. et al. (1999). Measurements of Ω and Λ from 42 high-redshift supernovae. Astrophys. J. 517, 565–586.', 'Hogg, D. W. (1999). Distance measures in cosmology. arXiv:astro-ph/9905116.', 'Weinberg, S. (2008). Cosmology, Oxford University Press.'],
  inputs: [
    inp('H_0', 'Hubble constant', 'km/s/Mpc', 67.4, { min: 40, max: 100, kind: 'environment', aliases: ['hubble constant', 'hubble parameter', 'h0'], src: 'Planck 2018, TT,TE,EE+lowE+lensing' }),
    inp('Omega_m', 'Matter density parameter', '1', 0.315, { min: 0.05, max: 1, kind: 'environment', aliases: ['matter density', 'omega matter', 'omega_m'], src: 'Planck 2018' }),
    inp('Omega_r', 'Radiation density parameter (photons and relativistic neutrinos)', '1', 9.2e-5, { min: 0, max: 0.01, kind: 'environment', aliases: ['radiation density', 'omega radiation'], src: 'CMB temperature 2.7255 K with three neutrino species, h = 0.674' }),
    inp('Omega_L', 'Dark-energy density parameter (used when the universe is not assumed flat)', '1', 0.685, { min: 0, max: 1, kind: 'environment', aliases: ['dark energy density', 'omega lambda', 'cosmological constant'], src: 'Planck 2018' }),
    inp('w_0', 'Dark-energy equation of state (used when it is not a cosmological constant)', '1', -0.9, { min: -2, max: -0.4, kind: 'hypothetical', aliases: ['equation of state'], src: 'Illustrative departure from w = −1; observations are consistent with −1 to within a few per cent' }),
    inp('z', 'Redshift of interest', '1', 1, { min: 0.001, max: 1100, aliases: ['redshift'] }),
  ],
  assumptions: [
    asm('flat', 'Space is flat: the density parameters sum to one and the dark-energy density is fixed by the others.', { why: 'Curvature is measured to be below about 0.2 %', alt: 'The dark-energy density is taken from its own input and the remainder is spatial curvature.' }),
    asm('lambda', 'Dark energy is a cosmological constant (w = −1).', { why: 'Simplest form consistent with all data', alt: 'Dark energy has a constant equation of state w₀ and density varying as a^(−3(1+w₀)).' }),
    asm('radiation', 'Radiation (photons and relativistic neutrinos) is included.', { why: 'It dominates before a redshift of about 3400', alt: 'Radiation is neglected, which permits closed-form solutions and shifts the age by under 0.1 %.' }),
  ],
  symbols: { a_s: ['Scale factor (1 today)', '1'], t: ['Cosmic time', 's'], H: ['Hubble rate', '1/s'], Omega_k: ['Curvature density parameter', '1'], t_0: ['Age of the universe', 's'], D_C: ['Comoving distance', 'm'], D_M: ['Transverse comoving distance', 'm'], D_L: ['Luminosity distance', 'm'], D_A: ['Angular-diameter distance', 'm'], q_0: ['Deceleration parameter', '1'], rho_c: ['Critical density', 'kg/m^3'], t_L: ['Lookback time', 's'], w_de: ['Dark-energy equation of state', '1'] },
  equations: a => {
    const de = a.lambda ? 'Omega_L' : 'Omega_L*a_s^(-3*(1 + w_0))', rad = a.radiation ? 'Omega_r/a_s^4 + ' : '', curv = a.flat ? '' : 'Omega_k/a_s^2 + ';
    return [
      eq('fried', 'Friedmann equation', '(d(a_s,t)/a_s)^2', `H_0^2*(${rad}Omega_m/a_s^3 + ${curv}${de})`, { kind: 'law', origin: 'Einstein field equations for a homogeneous, isotropic universe (Friedmann 1922)' }),
      eq('hub', 'Hubble rate', 'H', 'd(a_s,t)/a_s', { kind: 'definition' }),
      a.flat ? eq('close', 'Flatness', 'Omega_L', a.radiation ? '1 - Omega_m - Omega_r' : '1 - Omega_m', { kind: 'closure', origin: 'Zero spatial curvature', needs: ['flat'] })
        : eq('close', 'Curvature parameter', 'Omega_k', a.radiation ? '1 - Omega_m - Omega_r - Omega_L' : '1 - Omega_m - Omega_L', { kind: 'definition' }),
      eq('z', 'Redshift', '1 + z', '1/a_s', { kind: 'derived', origin: 'Stretching of wavelengths with the scale factor' }),
      eq('age', 'Age of the universe', 't_0', 'int(1/(a_s*H), a_s)', { kind: 'derived', origin: 'Integration of the Friedmann equation from a = 0 to 1' }),
      eq('dc', 'Comoving distance', 'D_C', 'c*int(1/H, z)', { kind: 'derived', origin: 'Null geodesic of the FLRW metric' }),
      eq('dl', 'Luminosity distance', 'D_L', '(1 + z)*D_M', { kind: 'derived', origin: 'Flux conservation with redshift of photon energy and arrival rate' }),
      eq('da', 'Angular-diameter distance', 'D_A', 'D_M/(1 + z)', { kind: 'derived', origin: 'Etherington reciprocity' }),
      eq('q', 'Deceleration parameter today', 'q_0', `${a.radiation ? 'Omega_r + ' : ''}Omega_m/2 + ${a.lambda ? '-Omega_L' : '(1 + 3*w_0)/2*Omega_L'}`, { kind: 'derived', origin: 'Acceleration (second Friedmann) equation' }),
      eq('rhoc', 'Critical density', 'rho_c', '3*H_0^2/(8*pi*G)', { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'For the FLRW metric the time–time component of Einstein\'s equations relates the expansion rate to the total energy density and curvature.', tex: 'H^2 \\equiv \\left(\\frac{\\dot a}{a}\\right)^2 = \\frac{8\\pi G}{3}\\rho - \\frac{k c^2}{a^2} + \\frac{\\Lambda c^2}{3}' },
    { text: 'Energy conservation for each component fixes how it dilutes. Dividing by the present critical density gives the dimensionless form.', tex: `\\frac{H^2}{H_0^2} = \\Omega_r a^{-4} + \\Omega_m a^{-3} + \\Omega_k a^{-2} + \\Omega_\\Lambda${a.lambda ? '' : ' a^{-3(1+w)}'}` },
    { text: 'Separating variables gives cosmic time as an integral over the scale factor; the age is its value at a = 1.', tex: 't(a) = \\int_0^a \\frac{\\mathrm{d}a\'}{a\'\\,H(a\')}' },
    { text: 'Light travels on null geodesics, so the comoving distance to redshift z is an integral of c/H. Curvature converts it into the transverse distance that sets apparent sizes and fluxes.', tex: 'D_C = c\\int_0^z \\frac{\\mathrm{d}z\'}{H(z\')},\\qquad D_L = (1+z)\\,D_M,\\qquad D_A = \\frac{D_M}{1+z}' },
    { text: 'Two closed forms serve as benchmarks: the matter-only (Einstein–de Sitter) universe and the flat universe with matter and a cosmological constant.', tex: 't_0^{\\rm EdS} = \\frac{2}{3H_0},\\qquad t_0^{\\Lambda{\\rm CDM}} = \\frac{2}{3H_0\\sqrt{\\Omega_\\Lambda}}\\,\\mathrm{arsinh}\\sqrt{\\frac{\\Omega_\\Lambda}{\\Omega_m}}' },
  ],
  solve(v, a) {
    const m = frw(v, a), H0 = m.H0, warnings = [];
    const t0 = m.tOf(1), t0c = m.tOf(1, 400), az = 1 / (1 + v.z), tz = m.tOf(az);
    const dc = m.chi(az), dm = m.DM(az), dl = (1 + v.z) * dm, da = dm / (1 + v.z);
    if (m.OL < 0) warnings.push('The dark-energy density implied by flatness is negative for these inputs.');
    // a(t): cumulative integral on a grid in x = √a, into the future as far as a = 2
    const xg = N.linspace(0, Math.SQRT2, 241), tg = [0];
    for (let i = 1; i < xg.length; i++) tg.push(tg[i - 1] + simpson(m.fT, xg[i - 1], xg[i], 8) / H0);
    const zs = N.logspace(0.01, 20, 60), ds = zs.map(zz => { const s = 1 / (1 + zz), d = m.DM(s); return [m.chi(s), d * (1 + zz), d / (1 + zz), t0 - m.tOf(s, 200)]; });
    const zEq = m.Or > 0 ? m.Om / m.Or - 1 : NaN;
    const acc = s => 2 * m.Or / s ** 4 + m.Om / s ** 3 + (1 + 3 * m.w) * m.OL * Math.pow(s, -3 * (1 + m.w));
    let zAcc = NaN;
    if (acc(1) < 0 && acc(1e-3) > 0) zAcc = 1 / N.findRoot(acc, 1e-3, 1) - 1;
    const rhoC = 3 * H0 * H0 / (8 * Math.PI * G);
    return {
      scalars: [
        scalar('t_0', 'Age of the universe', t0, 's', { show: 'Gyr' }), scalar('t_H', 'Hubble time 1/H₀', 1 / H0, 's', { show: 'Gyr' }),
        scalar('Omega_L', 'Dark-energy density parameter used', m.OL, '1'), scalar('Omega_k', 'Curvature density parameter', m.Ok, '1'),
        scalar('q_0', 'Deceleration parameter today', m.q0, '1', { note: m.q0 < 0 ? 'expansion is accelerating' : 'expansion is decelerating' }),
        scalar('rho_c', 'Critical density today', rhoC, 'kg/m^3'),
        scalar('z_eq', 'Redshift of matter–radiation equality', zEq, '1', { text: Number.isFinite(zEq) ? undefined : 'Not defined without radiation' }),
        scalar('z_acc', 'Redshift at which acceleration began', zAcc, '1', { text: Number.isFinite(zAcc) ? undefined : 'No transition to acceleration between z = 999 and today' }),
        scalar('t_z', 'Age of the universe at the chosen redshift', tz, 's', { show: 'Gyr' }), scalar('t_L', 'Lookback time to the chosen redshift', t0 - tz, 's', { show: 'Gyr' }),
        scalar('H_z', 'Hubble rate at the chosen redshift', H0 * m.E(az), '1/s', { show: 'km/s/Mpc' }),
        scalar('D_C', 'Comoving distance', dc, 'm', { show: 'Mpc' }), scalar('D_L', 'Luminosity distance', dl, 'm', { show: 'Mpc' }), scalar('D_A', 'Angular-diameter distance', da, 'm', { show: 'Mpc' }),
        scalar('mu_d', 'Distance modulus', 5 * Math.log10(dl / (10 * MPC / 1e6)), '1'),
        scalar('D_H', 'Hubble distance c/H₀', c / H0, 'm', { show: 'Mpc' }),
      ],
      series: [
        line('distance', 'Distances against redshift', 'Redshift', '–', zs, [{ label: 'Luminosity distance', data: ds.map(d => d[1] / MPC) }, { label: 'Comoving distance', data: ds.map(d => d[0] / MPC), dash: true }, { label: 'Angular-diameter distance', data: ds.map(d => d[2] / MPC), dash: true }], 'Distance', 'Mpc', { logx: true, logy: true }),
        line('scale-factor', 'Scale factor against cosmic time', 'Cosmic time', 'Gyr', tg.map(t => t / GYR), [{ label: 'Scale factor', data: xg.map(x => x * x) }, { label: 'Today', data: xg.map(() => 1), dash: true }], 'Scale factor', '–'),
        line('lookback', 'Lookback time against redshift', 'Redshift', '–', zs, [{ label: 'Lookback time', data: ds.map(d => d[3] / GYR) }, { label: 'Age of the universe', data: zs.map(() => t0 / GYR), dash: true }], 'Time', 'Gyr', { logx: true }),
        line('hubble', 'Expansion rate against redshift', 'Redshift', '–', zs, [{ label: 'H(z)', data: zs.map(zz => H0 * m.E(1 / (1 + zz)) * MPC / 1000) }], 'Hubble rate', 'km/s/Mpc', { logx: true, logy: true }),
      ],
      checks: [
        check('Density parameters sum to one', m.Or + m.Om + m.Ok + m.OL - 1, 1e-12, 'Definition of the curvature parameter'),
        check('Age integral converged', (t0 - t0c) / t0, 1e-5, 'Simpson rule with 800 against 400 intervals'),
        check('Distance duality', dl / ((1 + v.z) ** 2 * da) - 1, 1e-12, 'D_L = (1 + z)² D_A'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], H0 = v.H_0;
    const eds = this.solve({ ...v, Omega_m: 1 }, { flat: true, lambda: true, radiation: false });
    out.push(bench('Einstein–de Sitter age × H₀', val(eds, 't_0') * H0, 2 / 3, 't₀ = 2/(3H₀)', 1e-6));
    out.push(bench('Einstein–de Sitter comoving distance', val(eds, 'D_C'), 2 * c / H0 * (1 - 1 / Math.sqrt(1 + v.z)), 'D_C = (2c/H₀)(1 − 1/√(1+z))', 1e-6));
    const Om = N.clamp(v.Omega_m, 0.05, 0.95), lc = this.solve({ ...v, Omega_m: Om }, { flat: true, lambda: true, radiation: false }), OL = 1 - Om;
    out.push(bench('Flat ΛCDM age against the closed form', val(lc, 't_0'), 2 / (3 * H0 * Math.sqrt(OL)) * Math.asinh(Math.sqrt(OL / Om)), 't₀ = 2/(3H₀√Ω_Λ) arsinh√(Ω_Λ/Ω_m)', 1e-6));
    out.push(bench('Flat ΛCDM onset of acceleration', val(lc, 'z_acc'), Math.cbrt(2 * OL / Om) - 1, '1 + z_acc = (2Ω_Λ/Ω_m)^{1/3}', 1e-8));
    return out;
  },
  validation: [
    { name: 'Age of the universe in the base ΛCDM model', ref: 'Planck Collaboration (2020) Astron. Astrophys. 641, A6, Table 2: 13.797 ± 0.023 Gyr', note: 'Not an independent measurement: the age is inferred from the same parameters used as inputs here, so this checks the integration against the collaboration\'s own. A looser uncertainty is used to reflect the spread between analyses.',
      cases: [{ label: 'H₀ = 67.4, Ω_m = 0.315, flat', inputs: { H_0: 67.4e3 / MPC, Omega_m: 0.315, Omega_r: 9.2e-5 }, observable: 't_0', observed: 13.797 * GYR, sigma: 0.1 * GYR }] },
  ],
  diagram(v, a) {
    return svg(`
      ${S.arrow(70, 300, 590, 300)} ${S.arrow(70, 300, 70, 40)} ${S.text(590, 322, 'cosmic time', 'd-text', 'end')} ${S.text(60, 48, 'a', 'd-text', 'end')}
      ${S.path('M70 300 Q110 230 200 200 Q330 160 420 110 Q500 66 560 44', 'd-pipe')}
      ${S.line(420, 300, 420, 110, 'd-dim')} ${S.text(420, 318, 'today', 'd-text d-small')} ${S.circle(420, 110, 4, 'd-hazard')}
      ${S.text(120, 280, 'radiation', 'd-text d-small')} ${S.text(260, 215, 'matter: decelerating', 'd-text d-small')} ${S.text(500, 110, 'dark energy:', 'd-text d-small')} ${S.text(500, 126, 'accelerating', 'd-text d-small')}
      ${[0, 1, 2].map(i => S.circle(130 + 180 * i, 70, 10 + 9 * i, 'd-dim')).join('')} ${S.text(310, 30, 'space expands; wavelengths stretch with a')}
      ${S.text(330, 345, `H₀ = ${lab(v.H_0 * MPC / 1000, 'km/s/Mpc')}   Ω_m = ${lab(v.Omega_m)}   ${a.flat ? 'flat' : `Ω_Λ = ${lab(v.Omega_L)}`}`)}
    `);
  },
  experiment: {
    objective: 'Determine the expansion history from standard candles and standard rulers and test whether one set of density parameters fits all of them.',
    apparatus: ['Wide-field imaging survey to discover type Ia supernovae', 'Multi-object spectrograph for redshifts of supernova hosts and of millions of galaxies', 'Microwave radiometers or bolometers mapping the cosmic background'],
    instruments: [{ name: 'Calibrated photometry of supernova light curves', measures: 'Distance modulus, hence luminosity distance', range: 'z = 0.01–2', resolution: '≈ 0.1 mag per object' }, { name: 'Galaxy redshift survey', measures: 'Baryon-acoustic-oscillation scale along and across the line of sight, giving D_M and H', range: 'z = 0.1–2.5', resolution: '≈ 1 % per redshift bin' }, { name: 'CMB power spectrum', measures: 'Angular size of the sound horizon at z ≈ 1090', range: 'multipoles 2–2500', resolution: '0.03 % on the acoustic scale' }],
    procedure: ['Measure distance modulus against redshift for supernovae and fit D_L(z).', 'Measure the acoustic scale in galaxy clustering in several redshift bins.', 'Fit the CMB acoustic peaks for the physical densities and the angular scale.', 'Check that a single parameter set reproduces all three and derive the age.'],
    controls: ['Low-redshift anchor sample for the supernova absolute magnitude', 'Independent distance ladders (Cepheids, tip of the red-giant branch)', 'Ages of the oldest stars as a lower bound on t₀'],
    signatures: ['Supernovae at z ≈ 0.5 fainter than in a decelerating universe', 'Acoustic scale consistent between CMB and galaxy surveys', 'Oldest stellar ages below the computed age'],
    safety: ['Observatory and cryogenic-detector safety procedures'],
  },
  falsify: ['Stars or globular clusters reliably older than the computed age.', 'Distance–redshift data that no choice of density parameters can fit simultaneously with the CMB acoustic scale.', 'A measured violation of the distance-duality relation D_L = (1+z)² D_A.'],
  alternatives: [{ name: 'Dynamical dark energy', text: 'An equation of state that differs from −1 or evolves in time; recent acoustic-oscillation data have been read as mild hints, not yet conclusive.' }, { name: 'Curved models', text: 'Open or closed geometry; tightly bounded when CMB and acoustic-oscillation data are combined.' }, { name: 'Modified gravity', text: 'Alters the Friedmann equation itself rather than adding a component; constrained by the growth of structure and gravitational-wave propagation speed.' }, { name: 'Hubble tension', text: 'Local distance-ladder measurements give H₀ near 73 km/s/Mpc against 67 from the early universe; whether this signals new physics or systematics is unresolved.' }],
  limits: 'Homogeneous, isotropic universe with non-interacting matter, radiation and dark energy of constant equation of state. Massive-neutrino effects, the radiation-era particle content and inhomogeneities are not modelled. Closed models that recollapse or never had a big bang lie outside the declared input ranges.',
  numerics: { method: 'Composite Simpson quadrature in the variable √a, which removes the integrable singularity at a = 0', order: 4 },
  inverse: { series: 'distance', curve: 0, fit: ['H_0', 'Omega_m'] },
  extensions: ['Growth of density perturbations and the growth factor', 'Sound horizon and acoustic-peak positions', 'Evolving equation of state w(a) = w₀ + w_a(1 − a)', 'Thermal history: neutrino decoupling, nucleosynthesis, recombination'],
};

// ================================================================== 8. traversable wormhole
function wormhole(v, a) {
  const b0 = v.b_0, n = a.ellis ? 1 : 0, K = c ** 4 / (8 * Math.PI * G), del = a.zero_tidal ? 0 : v.phi_0;
  const b = r => b0 * Math.pow(b0 / r, n), bp = r => -n * Math.pow(b0 / r, n + 1);
  const lOf = r => (r <= b0 ? 0 : n === 1 ? Math.sqrt(r * r - b0 * b0) : Math.sqrt(r * (r - b0)) + b0 * Math.log(Math.sqrt(r / b0) + Math.sqrt(r / b0 - 1)));
  const lNum = r => (r <= b0 ? 0 : midpoint(s => { const x = b0 + s * s; return 2 * s / Math.sqrt(1 - b(x) / x); }, 0, Math.sqrt(r - b0), 600));
  const zOf = r => (r <= b0 ? 0 : n === 1 ? b0 * Math.acosh(r / b0) : 2 * Math.sqrt(b0 * (r - b0)));
  const rOf = l => (l <= 0 ? b0 : n === 1 ? Math.sqrt(b0 * b0 + l * l) : N.findRoot(r => lOf(r) - l, b0, b0 + l + 1e-9 * b0));
  const Phi = r => -del * b0 * b0 / (r * r), dPhi = r => 2 * del * b0 * b0 / r ** 3;
  const rho = r => K * bp(r) / (r * r);                                    // energy density, J/m³
  const tau = r => K * (b(r) / r ** 3 - 2 * (1 - b(r) / r) * dPhi(r) / r); // radial tension, Pa
  return { b0, n, K, del, b, bp, lOf, lNum, zOf, rOf, Phi, dPhi, rho, tau };
}

const wormholeModel = {
  id: 'traversable-wormhole',
  title: 'Traversable wormhole of Morris–Thorne type',
  module: 1, klass: ['III', 'I'], domains: ['relativity'], hypothetical: true,
  keywords: ['wormhole', 'traversable wormhole', 'morris thorne', 'einstein rosen bridge', 'exotic matter', 'negative energy', 'null energy condition', 'throat', 'embedding diagram', 'shortcut through spacetime', 'ellis wormhole'],
  summary: 'Geometry, traversal conditions and matter requirements of a static spherically symmetric wormhole: embedding surface, proper distance, crossing time, tidal accelerations and the violation of the null energy condition that the throat demands.',
  background: [
    'What is established: the Einstein field equations can be read in reverse, from a chosen geometry to the stress-energy needed to support it. Morris and Thorne (1988) did this for a static, spherically symmetric tunnel between two asymptotically flat regions and showed that any such throat requires matter whose radial tension exceeds its energy density, violating the null energy condition. That conclusion is a theorem of general relativity.',
    'What is hypothetical: that such matter can exist in the required amounts. Quantum field theory permits small, constrained negative energy densities (the Casimir effect is the standard example), but no known material or field configuration supplies the macroscopic quantities computed here, and quantum inequalities severely restrict it. The throat radius, the shape function and the redshift function in this model are therefore invented inputs. Every result is conditional on them and none describes a known object.',
  ],
  phenomena: ['Flare-out of the throat', 'Violation of the null energy condition', 'Tidal acceleration on a traveller', 'Embedding of a curved spatial slice'],
  laws: ['efe', 'equivalence', 'energy', 'causality'],
  refs: ['Morris, M. S. & Thorne, K. S. (1988). Wormholes in spacetime and their use for interstellar travel: a tool for teaching general relativity. Am. J. Phys. 56, 395–412.', 'Ellis, H. G. (1973). Ether flow through a drainhole: a particle model in general relativity. J. Math. Phys. 14, 104–118.', 'Morris, M. S., Thorne, K. S. & Yurtsever, U. (1988). Wormholes, time machines, and the weak energy condition. Phys. Rev. Lett. 61, 1446–1449.', 'Visser, M. (1995). Lorentzian Wormholes: From Einstein to Hawking, AIP Press.', 'Ford, L. H. & Roman, T. A. (1996). Quantum field theory constrains traversable wormhole geometries. Phys. Rev. D 53, 5496–5507.', 'Einstein, A. & Rosen, N. (1935). The particle problem in the general theory of relativity. Phys. Rev. 48, 73–77.'],
  inputs: [
    inp('b_0', 'Throat radius', 'm', 1000, { min: 1, max: 1e9, kind: 'hypothetical', aliases: ['throat radius', 'throat', 'wormhole radius'], src: 'Invented. No wormhole is known; the value sets the scale of every result.' }),
    inp('v', 'Traveller\'s speed through the throat, measured by static observers', 'm/s', 2000, { min: 1, max: 0.9 * c, aliases: ['speed', 'velocity'] }),
    inp('l_1', 'Proper distance of each station from the throat', 'km', 10000, { min: 1, max: 1e9, kind: 'geometry', aliases: ['station distance', 'distance'] }),
    inp('xi', 'Height of the traveller', 'm', 2, { min: 0.1, max: 100, kind: 'geometry', aliases: ['height', 'body length', 'tall'] }),
    inp('phi_0', 'Depth of the redshift function at the throat', '1', 0.01, { min: 1e-6, max: 0.3, kind: 'hypothetical', aliases: ['redshift function'], src: 'Invented; used only when the zero-tidal-force assumption is removed' }),
    inp('a_c', 'Acceleration of the traveller (used when not coasting)', 'm/s^2', 9.80665, { min: 0.1, max: 100, aliases: ['acceleration'] }),
  ],
  assumptions: [
    asm('ellis', 'The shape function is b(r) = b₀²/r.', { why: 'Simplest smooth choice (Ellis 1973; Morris & Thorne 1988)', alt: 'The shape function is constant, b(r) = b₀: the energy density vanishes everywhere and the exotic character lies entirely in the radial tension.' }),
    asm('zero_tidal', 'The redshift function vanishes (Φ = 0): static observers feel no gravity and there is no radial tide.', { why: 'Most benign case for a traveller', alt: 'A redshift function Φ = −φ₀b₀²/r² is added: clocks run slow near the throat, static observers must thrust, and a radial tide appears.' }),
    asm('coast', 'The traveller coasts at constant speed v between the stations.', { why: 'Simplest crossing', alt: 'The traveller accelerates at a_c from rest to the throat and decelerates symmetrically to rest at the far station.' }),
  ],
  symbols: { b_s: ['Shape function', 'm'], r: ['Circumferential radius', 'm'], l: ['Proper radial distance from the throat', 'm'], z_e: ['Embedding height', 'm'], rho_e: ['Mass density of the supporting matter', 'kg/m^3'], tau_r: ['Radial tension', 'Pa'], w_nec: ['Null-energy combination ρc² + p_r', 'Pa'], a_lat: ['Lateral tidal acceleration at the throat', 'm/s^2'], a_rad: ['Radial tidal acceleration at the throat', 'm/s^2'], dtau: ['Traveller\'s proper crossing time', 's'], gamma: ['Lorentz factor of the traveller', '1'], Phi: ['Redshift function', '1'], M_ex: ['Integrated mass of the supporting matter', 'kg'], g_m: ['Peak Lorentz factor', '1'] },
  equations: a => [
    a.ellis ? eq('shape', 'Shape function', 'b_s', 'b_0^2/r', { kind: 'hypothesis', origin: 'Chosen geometry (Morris & Thorne 1988); not derived from any matter model' })
      : eq('shape', 'Shape function', 'b_s', 'b_0', { kind: 'hypothesis', origin: 'Chosen geometry; not derived from any matter model' }),
    ...(a.zero_tidal ? [] : [eq('phi', 'Redshift function', 'Phi', '-phi_0*b_0^2/r^2', { kind: 'hypothesis', origin: 'Chosen for illustration' })]),
    eq('prop', 'Proper radial distance', 'd(l,r)', '1/sqrt(1 - b_s/r)', { kind: 'derived', origin: 'Spatial part of the Morris–Thorne metric' }),
    eq('emb', 'Embedding surface', 'd(z_e,r)', '1/sqrt(r/b_s - 1)', { kind: 'derived', origin: 'Equatorial slice embedded in Euclidean space' }),
    eq('rho', 'Energy density required', 'rho_e*c^2', 'c^4/(8*pi*G)*d(b_s,r)/r^2', { kind: 'law', origin: 'Einstein field equations, tt component' }),
    a.zero_tidal ? eq('tau', 'Radial tension required', 'tau_r', 'c^4/(8*pi*G)*b_s/r^3', { kind: 'law', origin: 'Einstein field equations, rr component', needs: ['zero_tidal'] })
      : eq('tau', 'Radial tension required', 'tau_r', 'c^4/(8*pi*G)*(b_s/r^3 - 2*(1 - b_s/r)*d(Phi,r)/r)', { kind: 'law', origin: 'Einstein field equations, rr component' }),
    eq('nec', 'Null-energy combination', 'w_nec', 'rho_e*c^2 - tau_r', { kind: 'definition', note: 'Negative values violate the null energy condition' }),
    eq('lat', 'Lateral tidal acceleration at the throat', 'a_lat', a.ellis ? 'gamma^2*v^2*xi/b_0^2' : 'gamma^2*v^2*xi/(2*b_0^2)', { kind: 'derived', origin: 'Geodesic deviation in the traveller\'s frame (Morris & Thorne 1988)' }),
    ...(a.zero_tidal ? [] : [eq('radt', 'Radial tidal acceleration at the throat', 'a_rad', a.ellis ? '2*phi_0*c^2*xi/b_0^2' : 'phi_0*c^2*xi/b_0^2', { kind: 'derived', origin: 'Geodesic deviation for a static observer' })]),
    ...(a.coast ? [eq('time', 'Proper crossing time', 'dtau', '2*l_1/(gamma*v)', { kind: 'derived', origin: 'Uniform motion in proper distance', needs: ['coast'] })]
      : [eq('gm', 'Peak Lorentz factor', 'g_m', '1 + a_c*l_1/c^2', { kind: 'derived', origin: 'Hyperbolic motion over proper distance l₁' }), eq('time', 'Proper crossing time', 'dtau', '2*c/a_c*ln(g_m + sqrt(g_m^2 - 1))', { kind: 'derived', origin: 'Hyperbolic motion' })]),
    ...(a.ellis ? [eq('mex', 'Integrated mass of the supporting matter', 'M_ex', '-pi*c^2*b_0/(2*G)', { kind: 'derived', origin: 'Proper-volume integral of the energy density over both sides of the throat' })] : []),
  ],
  derivation: a => [
    { text: 'Start from the general static, spherically symmetric metric with a redshift function Φ(r) and a shape function b(r). A throat exists where b(r₀) = r₀, and the tunnel flares outward only if b\'(r₀) < 1.', tex: '\\mathrm{d}s^2 = -e^{2\\Phi}c^2\\mathrm{d}t^2 + \\frac{\\mathrm{d}r^2}{1 - b(r)/r} + r^2\\mathrm{d}\\Omega^2' },
    { text: 'The Einstein equations then give the energy density and radial tension that the geometry requires.', tex: '\\rho c^2 = \\frac{c^4}{8\\pi G}\\,\\frac{b\'}{r^2},\\qquad \\tau = \\frac{c^4}{8\\pi G}\\left[\\frac{b}{r^3} - \\frac{2}{r}\\left(1-\\frac{b}{r}\\right)\\Phi\'\\right]' },
    { text: 'At the throat the flare-out condition forces the tension to exceed the energy density. A light ray passing radially would measure negative energy density: the null energy condition fails. No classical matter behaves this way.', tex: '\\left.(\\rho c^2 - \\tau)\\right|_{r_0} = \\frac{c^4}{8\\pi G}\\,\\frac{b\'(r_0) - 1}{r_0^2} < 0' },
    { text: 'A traveller of height ξ moving at speed v feels a lateral tide set by the flare of the throat. Requiring it to stay near one Earth gravity limits the speed.', tex: 'a_{\\perp} = \\frac{\\gamma^2 v^2}{2 r_0^2}\\,\\bigl|b\'(r_0) - 1\\bigr|\\,\\xi' },
    { text: a.ellis ? 'For b = b₀²/r the embedding surface is a catenoid, proper distance is l = √(r² − b₀²), and the energy density integrates to a finite negative mass.' : 'For constant b the embedding surface is a paraboloid and the energy density is zero; only the tension is anomalous.', tex: a.ellis ? 'z(r) = b_0\\,\\mathrm{arcosh}\\frac{r}{b_0},\\qquad M_{\\rm ex} = -\\frac{\\pi c^2 b_0}{2G}' : 'z(r) = 2\\sqrt{b_0\\,(r - b_0)}' },
  ],
  solve(v, a) {
    const m = wormhole(v, a), b0 = m.b0, warnings = [];
    const tau0 = m.tau(b0), rho0 = m.rho(b0), nec0 = rho0 - tau0, flare = Math.abs(m.bp(b0) - 1);
    const l1 = v.l_1, r1 = m.rOf(l1);
    // crossing
    let vT = v.v, gam, dtau, dt;
    if (a.coast) {
      gam = 1 / Math.sqrt(1 - (vT / c) ** 2); dtau = 2 * l1 / (gam * vT);
      // coordinate time includes the redshift factor exp(−Φ) along the path
      dt = m.del > 0 ? 2 / vT * midpoint(s => { const x = b0 + s * s; return 2 * s / Math.sqrt(1 - m.b(x) / x) * Math.exp(-m.Phi(x)); }, 0, Math.sqrt(Math.max(r1 - b0, 0)), 600) : 2 * l1 / vT;
    } else {
      gam = 1 + v.a_c * l1 / c2; vT = c * Math.sqrt(1 - 1 / (gam * gam)); dtau = 2 * c / v.a_c * Math.acosh(gam); dt = 2 * c / v.a_c * Math.sqrt(gam * gam - 1);
    }
    const aLat = flare * gam * gam * vT * vT * v.xi / (2 * b0 * b0), aRad = flare * m.del * c2 * v.xi / (b0 * b0);
    const Kt = 9.80665 * 2 * b0 * b0 / (flare * v.xi * c2), vTol = c * Math.sqrt(Kt / (1 + Kt));
    const aStat = c2 * m.dPhi(r1) * Math.sqrt(Math.max(1 - m.b(r1) / r1, 0));
    const Mex = m.n === 1 ? -Math.PI * c2 * b0 / (2 * G) : 0;
    // numerical proper-volume integral of the energy density out to R = 200 b0, both sides of the throat
    const Rm = 200 * b0, Mnum = 2 * midpoint(s => { const x = b0 + s * s; return 4 * Math.PI * x * x * m.rho(x) / c2 * 2 * s / Math.sqrt(1 - m.b(x) / x); }, 0, Math.sqrt(Rm - b0), 4000);
    const Mpart = m.n === 1 ? -(c2 / G) * b0 * (Math.PI / 2 - Math.asin(b0 / Rm)) : 0;
    if (aLat > 9.80665) warnings.push(`The lateral tidal acceleration exceeds one Earth gravity. For this throat a traveller of this height would need to cross more slowly than about ${lab(vTol, 'm/s')}.`);
    warnings.push('Conditional result: the geometry requires matter violating the null energy condition in macroscopic quantities. No such matter is known.');
    const rr = N.logspace(1, 20, 120).map(x => x * b0), rE = N.linspace(1, Math.min(Math.max(r1 / b0, 2), 12), 120).map(x => x * b0);
    return {
      scalars: [
        scalar('tau_0', 'Radial tension required at the throat', tau0, 'Pa', { status: 'hypothetical' }),
        scalar('rho_0', 'Mass density required at the throat', rho0 / c2, 'kg/m^3', { status: 'hypothetical' }),
        scalar('w_nec', 'Null-energy combination ρc² + p_r at the throat', nec0, 'Pa', { status: 'hypothetical', note: nec0 < 0 ? 'negative: null energy condition violated' : 'not violated' }),
        scalar('M_ex', 'Integrated mass of the supporting matter', Mex, 'kg', { status: 'hypothetical', show: 'Msun' }),
        scalar('M_num', 'Same, by numerical integration out to 200 throat radii', Mnum, 'kg', { status: 'hypothetical' }),
        scalar('M_eq', 'Mass whose Schwarzschild radius equals the throat radius', c2 * b0 / (2 * G), 'kg', { show: 'Msun' }),
        scalar('r_1', 'Circumferential radius at the stations', r1, 'm', { show: 'km' }), scalar('z_1', 'Embedding height at the stations', m.zOf(r1), 'm', { show: 'km' }),
        scalar('dtau', 'Traveller\'s proper crossing time', dtau, 's', { status: 'hypothetical' }), scalar('dt', 'Crossing time by station clocks', dt, 's', { status: 'hypothetical' }),
        scalar('v_th', 'Speed at the throat', vT, 'm/s'), scalar('gamma', 'Lorentz factor at the throat', gam, '1'),
        scalar('a_lat', 'Lateral tidal acceleration at the throat', aLat, 'm/s^2', { status: 'hypothetical' }), scalar('a_rad', 'Radial tidal acceleration at the throat', aRad, 'm/s^2', { status: 'hypothetical' }),
        scalar('v_tol', 'Greatest throat speed keeping the lateral tide below one Earth gravity', vTol, 'm/s', { status: 'hypothetical' }),
        scalar('a_stat', 'Thrust acceleration needed to hover at a station', aStat, 'm/s^2', { status: 'hypothetical' }),
        scalar('z_th', 'Redshift of light climbing from the throat to infinity', Math.exp(m.del) - 1, '1', { status: 'hypothetical' }),
      ],
      series: [
        line('embedding', 'Embedding diagram of the equatorial slice', 'Circumferential radius', 'b₀', rE.map(r => r / b0), [{ label: 'Upper universe', data: rE.map(r => m.zOf(r) / b0) }, { label: 'Lower universe', data: rE.map(r => -m.zOf(r) / b0) }], 'Embedding height', 'b₀', { status: 'hypothetical', note: 'Rotate about the vertical axis to obtain the familiar funnel surface.' }),
        line('stress', 'Stress-energy required, in units of the throat tension', 'Circumferential radius', 'b₀', rr.map(r => r / b0), [{ label: 'Energy density ρc²', data: rr.map(r => m.rho(r) / tau0) }, { label: 'Radial pressure p_r = −τ', data: rr.map(r => -m.tau(r) / tau0), dash: true }, { label: 'ρc² + p_r', data: rr.map(r => (m.rho(r) - m.tau(r)) / tau0) }], 'Stress', 'τ₀', { logx: true, status: 'hypothetical', note: 'Wherever the last curve is negative the null energy condition is violated.' }),
        line('proper', 'Proper distance from the throat', 'Circumferential radius', 'b₀', rr.map(r => r / b0), [{ label: 'Wormhole', data: rr.map(r => m.lOf(r) / b0) }, { label: 'Flat space, r − b₀', data: rr.map(r => r / b0 - 1), dash: true }], 'Proper distance', 'b₀', { status: 'hypothetical' }),
      ],
      checks: [
        check('Flare-out condition at the throat', m.bp(b0) < 1 ? 0 : 1, 0, 'b\'(r₀) < 1'),
        check('Null energy condition is violated at the throat', Math.max(0, nec0 / tau0), 0, 'ρc² − τ < 0, as the theorem requires'),
        check('Proper distance: quadrature against closed form', (m.lNum(r1) - l1) / l1, 1e-5, 'l(r) = ∫ dr/√(1 − b/r)'),
        check('Energy-density integral: quadrature against closed form', m.n === 1 ? (Mnum - Mpart) / Mpart : Mnum, 1e-5, 'Partial integral to 200 b₀'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { ellis: true, zero_tidal: true, coast: true }, r = this.solve({ ...v, b_0: 10 }, on), out = [];
    out.push(bench('Throat tension for a 10 m throat (Pa)', val(r, 'tau_0'), 4.82e40, 'c⁴/(8πGb₀²); Morris & Thorne quote ≈ 5 × 10⁴¹ dyn/cm²', 2e-3));
    const m = wormhole(v, on), rT = 7.3 * v.b_0;
    out.push(bench('Ellis proper distance: quadrature vs closed form', m.lNum(rT), Math.sqrt(rT * rT - v.b_0 ** 2), 'l = √(r² − b₀²)', 1e-6));
    const mc = wormhole(v, { ...on, ellis: false });
    out.push(bench('Constant shape function: quadrature vs closed form', mc.lNum(rT), mc.lOf(rT), 'l = √(r(r−b₀)) + b₀ ln(√(r/b₀) + √(r/b₀−1))', 1e-6));
    out.push(bench('Ellis embedding slope at r = 2b₀', (m.zOf(2.001 * v.b_0) - m.zOf(1.999 * v.b_0)) / (0.002 * v.b_0), 1 / Math.sqrt(3), 'dz/dr = (r²/b₀² − 1)^(−1/2)', 1e-5));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.path('M60 70 Q250 80 290 180 Q250 280 60 290', 'd-line')} ${S.path('M580 70 Q390 80 350 180 Q390 280 580 290', 'd-line')}
      <ellipse cx="320" cy="180" rx="30" ry="9" class="d-hazard"/> <ellipse cx="320" cy="75" rx="260" ry="16" class="d-dim" fill="none"/> <ellipse cx="320" cy="287" rx="260" ry="16" class="d-dim" fill="none"/>
      ${S.text(320, 40, 'upper universe')} ${S.text(320, 335, 'lower universe (or a distant region of the same one)')}
      ${S.dim(290, 205, 350, 205, 'throat 2b₀')} ${S.arrow(470, 90, 372, 168)} ${S.text(480, 104, 'traveller', 'd-text', 'start')}
      ${S.text(150, 184, 'exotic matter:', 'd-text d-small')} ${S.text(150, 200, 'tension > energy density', 'd-text d-small')}
      ${S.text(520, 184, `b₀ = ${lab(v.b_0, 'm')}`)} ${S.text(520, 204, 'hypothetical', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'No wormhole is available to test. The proposed work tests the two ingredients on which the conclusion rests: the reality and limits of negative energy density, and astrophysical signatures that a wormhole mouth would produce.',
    apparatus: ['Casimir cavity with parallel plates at sub-micrometre separation', 'Squeezed-light source with homodyne detection', 'Microlensing survey telescope with high-cadence photometry'],
    instruments: [{ name: 'Torsion balance or micro-cantilever', measures: 'Casimir pressure, implying a negative vacuum energy density between the plates', range: '0.1–1 µm separation', resolution: '≈ 1 %' }, { name: 'Balanced homodyne detector', measures: 'Sub-vacuum field fluctuations and their duration', range: 'MHz bandwidth', resolution: 'fraction of a decibel' }, { name: 'Survey photometer', measures: 'Light curves of lensing events', range: 'days to months', resolution: 'millimagnitude' }],
    procedure: ['Measure the magnitude and spatial extent of negative energy density attainable in the laboratory and compare with the quantum-inequality bounds.', 'Scale to the density c⁴/(8πGb₀²) required at a throat of radius b₀ to quantify the shortfall.', 'Search survey data for lensing light curves with the central dip characteristic of a negative-mass or wormhole lens.'],
    controls: ['Ordinary positive-mass lensing events as the reference light-curve shape', 'Plate-separation scan to verify the Casimir distance law'],
    signatures: ['Laboratory negative energy densities shorter-lived and smaller than the bound', 'Absence, so far, of wormhole-type lensing events'],
    safety: ['Standard optical-laboratory and vacuum precautions'],
  },
  falsify: ['The claim that a throat needs null-energy-violating matter would be refuted by a static, traversable, asymptotically flat wormhole solution of the Einstein equations supported by ordinary matter; the topological censorship theorem says none exists.', 'The practical possibility would be ruled out further by a proof that quantum inequalities forbid the required macroscopic negative energy for every field theory.', 'Conversely, detection of a compact object with the lensing or orbital signature of a throat would overturn the working assumption that none exist.'],
  alternatives: [{ name: 'Einstein–Rosen bridge', text: 'The maximally extended Schwarzschild solution contains a bridge, but it pinches off faster than light can cross: not traversable.' }, { name: 'Thin-shell wormholes', text: 'Visser\'s construction confines the exotic matter to a thin shell at the throat, minimising its amount but not removing it.' }, { name: 'Wormholes in modified gravity', text: 'In some higher-curvature or scalar–tensor theories the effective stress-energy violating the condition is supplied by the gravitational sector rather than matter; these theories are themselves speculative.' }, { name: 'Quantum (ER = EPR) wormholes', text: 'Non-traversable or only marginally traversable connections associated with entanglement; they do not permit faster-than-light travel.' }],
  limits: 'Static, spherically symmetric, non-rotating geometry in classical general relativity with prescribed shape and redshift functions. Stability, formation, the back-reaction of the traveller and the conversion of a wormhole into a time machine are not treated. The integrated mass is a simple proper-volume integral of the energy density and is one of several inequivalent measures of the amount of exotic matter.',
  numerics: { method: 'Closed forms with midpoint quadrature in the variable √(r − b₀), which removes the coordinate singularity at the throat', order: 2 },
  inverse: { series: 'embedding', curve: 0, fit: ['b_0'] },
  extensions: ['Volume-integral quantifier of null-energy violation (Visser, Kar & Dadhich)', 'Rotating (Teo) wormholes', 'Light deflection and shadow of a wormhole mouth', 'Relative motion of the mouths and the chronology-protection conjecture'],
};

// ================================================================== 9. modified-gravity orbits
function powerOrbit(n, f) {
  // units: r in r0, time in √(r0³/GM); attraction r^(−n); start at r = 1 with tangential speed f
  const U = r => (Math.abs(n - 1) < 1e-12 ? Math.log(r) : Math.pow(r, 1 - n) / (1 - n));
  const E = 0.5 * f * f + U(1), h = f, Q = r => 2 * (E - U(r)) - h * h / (r * r);
  const out = { E, h, U, Q, r1: 1, r2: 1, psi: NaN, state: 'bound' };
  if (Math.abs(f - 1) < 1e-6) { out.psi = n < 3 ? Math.PI / Math.sqrt(3 - n) : NaN; out.state = n < 3 ? 'circular' : 'unstable'; return out; }
  // r = 1 is one turning point; step into the allowed region, then march until Q changes sign
  const inward = f < 1, sgn = inward ? -1 : 1; let d0 = 0.25 * Math.abs(1 - f), prev = 1 + sgn * d0;
  for (let k = 0; k < 40 && !(Q(prev) > 0); k++) { d0 /= 2; prev = 1 + sgn * d0; }
  if (!(Q(prev) > 0)) { out.psi = n < 3 ? Math.PI / Math.sqrt(3 - n) : NaN; out.state = n < 3 ? 'circular' : 'unstable'; return out; }
  const step = inward ? 0.98 : 1.02; let r = prev * step, found = false;
  for (let k = 0; k < 720; k++) { if (Q(r) < 0) { found = true; break; } prev = r; r *= step; }
  if (!found) { out.state = inward ? 'plunge' : 'unbound'; out.r1 = inward ? 0 : 1; out.r2 = inward ? 1 : Infinity; return out; }
  const other = N.bisect(Q, Math.min(prev, r), Math.max(prev, r), 1e-14);
  const r1 = Math.min(1, other), r2 = Math.max(1, other), mid = 0.5 * (r1 + r2), d = 0.5 * (r2 - r1);
  out.r1 = r1; out.r2 = r2;
  out.psi = midpoint(th => { const x = mid + d * Math.sin(th), q = Q(x); return q > 0 ? h / (x * x) * Math.sqrt((x - r1) * (r2 - x) / q) : 0; }, -Math.PI / 2, Math.PI / 2, 400);
  return out;
}

/** Planar orbit by fourth-order Runge–Kutta, sub-stepped in proportion to the local dynamical time r^((n+1)/2). */
function powerTrajectory(n, f, tEnd, nOut) {
  let x = 1, y = 0, u = 0, w = f, alive = true; const xs = new Array(nOut).fill(NaN), ys = new Array(nOut).fill(NaN), dT = tEnd / (nOut - 1);
  let last = [x, y, u, w];
  for (let i = 0; i < nOut; i++) {
    if (!alive) break;
    xs[i] = x; ys[i] = y; last = [x, y, u, w];
    if (i === nOut - 1) break;
    let done = 0;
    while (done < dT - 1e-15 * dT) {
      const r = Math.hypot(x, y);
      if (r < 1e-3 || r > 1e3) { alive = false; break; }
      const h = Math.min(dT - done, 0.01 * Math.pow(r, Math.max(n + 1, 0) / 2));
      const e = -(n + 1) / 2, q1 = -Math.pow(x * x + y * y, e), a1x = q1 * x, a1y = q1 * y;
      const x2 = x + 0.5 * h * u, y2 = y + 0.5 * h * w, u2 = u + 0.5 * h * a1x, w2 = w + 0.5 * h * a1y, q2 = -Math.pow(x2 * x2 + y2 * y2, e), a2x = q2 * x2, a2y = q2 * y2;
      const x3 = x + 0.5 * h * u2, y3 = y + 0.5 * h * w2, u3 = u + 0.5 * h * a2x, w3 = w + 0.5 * h * a2y, q3 = -Math.pow(x3 * x3 + y3 * y3, e), a3x = q3 * x3, a3y = q3 * y3;
      const x4 = x + h * u3, y4 = y + h * w3, u4 = u + h * a3x, w4 = w + h * a3y, q4 = -Math.pow(x4 * x4 + y4 * y4, e), a4x = q4 * x4, a4y = q4 * y4;
      x += h / 6 * (u + 2 * u2 + 2 * u3 + u4); y += h / 6 * (w + 2 * w2 + 2 * w3 + w4);
      u += h / 6 * (a1x + 2 * a2x + 2 * a3x + a4x); w += h / 6 * (a1y + 2 * a2y + 2 * a3y + a4y);
      done += h;
    }
  }
  return { xs, ys, last };
}

const modGravity = {
  id: 'modified-gravity-orbits',
  title: 'Orbits under a modified force law F ∝ 1/rⁿ',
  module: 1, klass: ['III', 'I'], domains: ['classical', 'relativity'], hypothetical: true,
  keywords: ['modified gravity', 'inverse cube', 'force law exponent', 'different power law', 'bertrand theorem', 'bertrand', 'apsidal angle', 'closed orbits', 'extra dimensions', 'extra spatial dimension', 'gravity fell off', 'inverse square law were different', 'precessing orbit', 'four spatial dimensions', 'stability of orbits'],
  summary: 'Integrates orbits in a central attraction proportional to 1/rⁿ and tests them against Bertrand\'s theorem, the apsidal-angle formula and the stability limit n < 3.',
  background: [
    'What is established: in our universe gravity follows the inverse-square law to high precision from sub-millimetre laboratory scales to the size of the solar system, apart from the small relativistic corrections. Classical mechanics also proves, independently of what nature chose, how orbits would behave under any other power law. Bertrand\'s theorem (1873) states that only the inverse-square and the linear (harmonic) force laws make every bound orbit closed; circular orbits are stable only if the attraction falls off more slowly than 1/r³; and a nearly circular orbit turns through π/√(3−n) between successive closest and farthest points.',
    'What is hypothetical: the exponent n itself. Setting it to anything other than 2 describes a counterfactual world, for example one with D = n + 1 spatial dimensions, in which Gauss\'s law gives a force proportional to 1/r^(D−1). The results show why stable planetary systems single out three dimensions; they do not describe any observed deviation.',
  ],
  phenomena: ['Central-force motion', 'Apsidal precession', 'Orbital stability', 'Closed orbits and hidden symmetry'],
  laws: ['newton2', 'angular', 'energy', 'gravitation'],
  refs: ['Bertrand, J. (1873). Théorème relatif au mouvement d\'un point attiré vers un centre fixe. C. R. Acad. Sci. Paris 77, 849–853.', 'Goldstein, H., Poole, C. & Safko, J. (2002). Classical Mechanics, 3rd ed., Addison-Wesley, §3.6.', 'Ehrenfest, P. (1917). In what way does it become manifest in the fundamental laws of physics that space has three dimensions? Proc. Amsterdam Acad. 20, 200–209.', 'Tangherlini, F. R. (1963). Schwarzschild field in n dimensions and the dimensionality of space problem. Nuovo Cimento 27, 636–651.', 'Adelberger, E. G., Heckel, B. R. & Nelson, A. E. (2003). Tests of the gravitational inverse-square law. Annu. Rev. Nucl. Part. Sci. 53, 77–121.', 'Newton, I. (1687). Philosophiæ Naturalis Principia Mathematica, Book I, Section IX (revolving orbits).'],
  inputs: [
    inp('n', 'Exponent of the force law, F ∝ 1/rⁿ', '1', 2, { min: -1, max: 3.5, kind: 'hypothetical', aliases: ['exponent', 'power', 'power law', 'falls off as'], src: 'n = 2 is the measured value; any other value is counterfactual' }),
    inp('D_s', 'Number of spatial dimensions (used in the extra-dimension reading)', '1', 4, { min: 1, max: 4.5, kind: 'hypothetical', aliases: ['dimensions', 'spatial dimensions'], src: 'Counterfactual; three in our universe' }),
    inp('M', 'Central mass', 'Msun', 1, { min: 0.01, max: 1e6, kind: 'environment', aliases: ['mass', 'solar mass', 'star mass'] }),
    inp('r_0', 'Starting radius, at which the force equals its Newtonian value', 'AU', 1, { min: 0.01, max: 1000, kind: 'geometry', aliases: ['radius', 'distance', 'orbital radius'] }),
    inp('f_v', 'Initial tangential speed as a fraction of the circular speed', '1', 0.8, { min: 0.3, max: 1.3, aliases: ['speed fraction', 'fraction of circular speed'] }),
    inp('q_m', 'Mass of the orbiting body as a fraction of the central mass', '1', 0.001, { min: 0, max: 1, aliases: ['mass ratio'], src: 'Roughly Jupiter to Sun; used only when the centre is not fixed' }),
    inp('n_orb', 'Circular-orbit periods integrated', '1', 6, { min: 1, max: 30, kind: 'numerical' }),
  ],
  assumptions: [
    asm('free_n', 'The exponent n is a free parameter of the force law.', { why: 'Most general reading', alt: 'The exponent follows from Gauss\'s law in D spatial dimensions: n = D − 1.' }),
    asm('small_ecc', 'The reported apsidal angle is the nearly-circular result π/√(3−n).', { why: 'Classical closed form', alt: 'The reported apsidal angle is the exact value for the actual orbit, by quadrature between its turning points.' }),
    asm('fixed_centre', 'The central mass is fixed.', { why: 'Planet much lighter than star', alt: 'Both bodies move; the relative orbit sees the total mass M(1 + q).' }),
  ],
  symbols: { a_r: ['Radial acceleration due to the force', 'm/s^2'], r: ['Orbital radius', 'm'], t: ['Time', 's'], theta: ['Orbital angle', 'rad'], h_L: ['Specific angular momentum', 'm^2/s'], psi: ['Apsidal angle', 'rad'], kappa_e: ['Radial (epicyclic) frequency', '1/s'], Omega_c: ['Circular orbital frequency', '1/s'], v_c: ['Circular speed at the starting radius', 'm/s'] },
  equations: a => {
    const mass = a.fixed_centre ? 'G*M' : 'G*M*(1 + q_m)', ex = a.free_n ? 'n' : '(D_s - 1)';
    return [
      eq('force', 'Force law', 'a_r', `-${mass}/r_0^2*(r_0/r)^${ex}`, { kind: 'hypothesis', origin: a.free_n ? 'Postulated power law; reduces to Newtonian gravitation at n = 2' : 'Gauss\'s law for a point source in D spatial dimensions; reduces to Newtonian gravitation at D = 3' }),
      eq('ang', 'Conservation of angular momentum', 'h_L', 'r^2*d(theta,t)', { kind: 'law', origin: 'Central force exerts no torque' }),
      eq('rad', 'Radial equation of motion', 'd2(r,t)', 'h_L^2/r^3 + a_r', { kind: 'law', origin: 'Newton\'s second law in polar coordinates' }),
      eq('vc', 'Circular speed at the starting radius', 'v_c', `sqrt(${mass}/r_0)`, { kind: 'derived', origin: 'Centripetal balance' }),
      eq('epi', 'Radial oscillation frequency about a circular orbit', 'kappa_e^2', `(3 - ${ex})*Omega_c^2`, { kind: 'derived', origin: 'Linearised radial equation; stability requires a positive right-hand side' }),
      ...(a.small_ecc ? [eq('aps', 'Apsidal angle of a nearly circular orbit', 'psi', `pi/sqrt(3 - ${ex})`, { kind: 'derived', origin: 'Ratio of orbital to radial frequency (Newton, Principia I.IX)', needs: ['small_ecc'] })] : []),
    ];
  },
  derivation: a => [
    { text: 'A central force conserves angular momentum, so the motion reduces to one dimension in an effective potential.', tex: '\\ddot r = \\frac{h^2}{r^3} - \\frac{GM}{r_0^2}\\left(\\frac{r_0}{r}\\right)^{n}' },
    { text: 'A circular orbit of radius r_c has h² = GM r_0^{n−2} r_c^{3−n}. Perturbing it, r = r_c + x, gives a harmonic equation for x.', tex: '\\ddot x = -(3-n)\\,\\Omega_c^2\\,x,\\qquad \\kappa^2 = (3-n)\\,\\Omega_c^2' },
    { text: 'The orbit is stable only if κ² > 0, that is n < 3. For n ≥ 3 the smallest disturbance sends the body spiralling inward or away.', tex: 'n < 3' },
    { text: 'During half a radial oscillation the body turns through the apsidal angle. The orbit closes only if this is a rational multiple of π for every amplitude, which Bertrand showed happens for n = 2 (ψ = π) and n = −1 (ψ = π/2) alone.', tex: '\\psi = \\frac{\\pi\\,\\Omega_c}{\\kappa} = \\frac{\\pi}{\\sqrt{3-n}}' },
    { text: 'In D spatial dimensions the flux of the field through a sphere is spread over an area proportional to r^{D−1}, so the exponent is n = D − 1. Stable orbits then require D < 4.', tex: 'F \\propto \\frac{1}{r^{D-1}}\\ \\Rightarrow\\ D < 4' },
  ],
  solve(v, a) {
    const n = a.free_n ? v.n : v.D_s - 1, GM = G * v.M * (a.fixed_centre ? 1 : 1 + v.q_m), r0 = v.r_0, f = v.f_v;
    const vc = Math.sqrt(GM / r0), tU = Math.sqrt(r0 ** 3 / GM), o = powerOrbit(n, f), warnings = [];
    const stable = n < 3, closed = Math.abs(n - 2) < 1e-9 || Math.abs(n + 1) < 1e-9;
    const psiSmall = stable ? Math.PI / Math.sqrt(3 - n) : NaN;
    const psi = a.small_ecc ? psiSmall : o.psi;
    if (!stable) warnings.push('With n ≥ 3 there are no stable circular orbits: the body either spirals into the centre or escapes.');
    if (o.state === 'plunge') warnings.push('This orbit has no inner turning point and falls to the centre.');
    if (o.state === 'unbound') warnings.push('This orbit is unbound: the body escapes and no apsidal angle is defined.');
    if (a.small_ecc && o.state === 'bound' && Math.abs(o.psi - psiSmall) > 0.01 * psiSmall) warnings.push('The orbit is far from circular, so the nearly-circular apsidal angle differs noticeably from the exact value for this orbit; remove that assumption to report the exact one.');
    // trajectory
    const nP = Math.round(N.clamp(v.n_orb, 1, 30)), nOut = 1500, tEnd = 2 * Math.PI * nP;
    const tr = powerTrajectory(n, f, tEnd, nOut), xs = tr.xs, ys = tr.ys, ts = N.linspace(0, tEnd, nOut), rs = xs.map((x, i) => Math.hypot(x, ys[i]));
    const [xe, ye, ue, we] = tr.last, Ek = 0.5 * (ue * ue + we * we) + o.U(Math.hypot(xe, ye)), hk = xe * we - ye * ue;
    const ns = N.linspace(-1, 2.9, 79), sw = ns.map(q => powerOrbit(q, f).psi);
    const rr = N.logspace(0.15, 6, 140);
    return {
      scalars: [
        scalar('n_eff', 'Force-law exponent in use', n, '1', { status: Math.abs(n - 2) < 1e-12 ? undefined : 'hypothetical' }),
        scalar('stable', 'Circular orbits are stable', stable ? 1 : 0, '1', { text: stable ? 'Yes (n < 3)' : 'No (n ≥ 3)' }),
        scalar('closed', 'All bound orbits close', closed ? 1 : 0, '1', { text: closed ? 'Yes: this is one of the two cases of Bertrand\'s theorem' : 'No: bound orbits precess as rosettes' }),
        scalar('psi', 'Apsidal angle', psi, 'rad', { show: 'deg', text: Number.isFinite(psi) ? undefined : (stable ? `Not defined: the orbit is ${o.state === 'plunge' ? 'a plunge' : 'unbound'}` : 'Not defined: no stable orbit') }),
        scalar('psi_small', 'Apsidal angle, nearly-circular formula', psiSmall, 'rad', { show: 'deg', text: stable ? undefined : 'Not defined for n ≥ 3' }),
        scalar('psi_exact', 'Apsidal angle of this orbit, by quadrature', o.psi, 'rad', { show: 'deg', text: Number.isFinite(o.psi) ? undefined : 'Not defined for this orbit' }),
        scalar('prec', 'Advance of the closest point per radial period', 2 * o.psi - 2 * Math.PI, 'rad', { show: 'deg', text: Number.isFinite(o.psi) ? undefined : 'Not defined for this orbit' }),
        scalar('kappa_ratio', 'Radial over orbital frequency, √(3−n)', stable ? Math.sqrt(3 - n) : NaN, '1', { text: stable ? undefined : 'Imaginary: unstable' }),
        scalar('r_min', 'Closest approach', o.r1 * r0, 'm', { show: 'AU' }), scalar('r_max', 'Farthest distance', o.r2 * r0, 'm', { show: 'AU', text: Number.isFinite(o.r2) ? undefined : 'Unbounded' }),
        scalar('v_c', 'Circular speed at the starting radius', vc, 'm/s', { show: 'km/s' }), scalar('T_c', 'Circular-orbit period at the starting radius', 2 * Math.PI * tU, 's', { show: 'yr' }),
        scalar('h_L', 'Specific angular momentum', f * vc * r0, 'm^2/s'), scalar('E_s', 'Specific orbital energy', o.E * vc * vc, 'J/kg'),
      ],
      series: [
        line('apsidal-sweep', 'Apsidal angle against the exponent', 'Exponent n', '–', ns, [{ label: 'Nearly circular: π/√(3−n)', data: ns.map(q => 180 / Math.sqrt(3 - q)) }, { label: 'This starting speed, exact', data: sw.map(p => p * 180 / Math.PI), dash: true }], 'Apsidal angle', '°', { note: 'The two curves agree for every amplitude only at n = −1 (90°) and n = 2 (180°).' }),
        line('orbit', 'Orbit', 'x', 'r₀', xs, [{ label: 'Trajectory', data: ys }], 'y', 'r₀', { equal: true, status: 'hypothetical' }),
        line('radius', 'Radius against time', 'Time', 'circular periods', ts.map(t => t / (2 * Math.PI)), [{ label: 'r/r₀', data: rs }], 'Radius', 'r₀', { status: 'hypothetical' }),
        line('veff', 'Effective potential', 'Radius', 'r₀', rr, [{ label: 'Effective potential', data: rr.map(r => N.clamp(o.U(r) + o.h * o.h / (2 * r * r), -1e3, 1e3)) }, { label: 'Orbital energy', data: rr.map(() => o.E), dash: true }], 'Energy', 'v_c²', { logx: true, status: 'hypothetical' }),
      ],
      checks: [
        check('Energy conserved along the trajectory', (Ek - o.E) / Math.max(Math.abs(o.E), 0.1), 1e-6, 'Fourth-order Runge–Kutta, relative drift'),
        check('Angular momentum conserved along the trajectory', (hk - o.h) / o.h, 1e-6, 'Relative drift'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [];
    out.push(bench('Inverse-square law: apsidal angle of an eccentric orbit', powerOrbit(2, 0.8).psi, Math.PI, 'Bertrand: Kepler ellipses close, ψ = π', 1e-8));
    out.push(bench('Harmonic law (n = −1): apsidal angle of an eccentric orbit', powerOrbit(-1, 0.8).psi, Math.PI / 2, 'Bertrand: centred ellipses close, ψ = π/2', 1e-8));
    out.push(bench('n = 2.5, nearly circular: apsidal angle', powerOrbit(2.5, 0.999).psi, Math.PI / Math.sqrt(0.5), 'ψ = π/√(3−n)', 1e-4));
    out.push(bench('n = 1, nearly circular: apsidal angle', powerOrbit(1, 0.999).psi, Math.PI / Math.SQRT2, 'ψ = π/√2 for a logarithmic potential', 1e-4));
    out.push(bench('Kepler periapsis for a start at 0.8 of circular speed', powerOrbit(2, 0.8).r1, 0.64 / (2 - 0.64), 'r_min/r₀ = f²/(2 − f²)', 1e-10));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const n = a.free_n ? v.n : v.D_s - 1, petals = [0, 1, 2, 3, 4];
    const rosette = Math.abs(n - 2) < 1e-9 ? '<ellipse cx="290" cy="185" rx="130" ry="95" class="d-pipe" fill="none"/>' : petals.map(i => `<ellipse cx="290" cy="185" rx="130" ry="95" class="d-line" fill="none" transform="rotate(${i * 24} 330 185)"/>`).join('');
    return svg(`
      ${rosette} ${S.circle(330, 185, 10, 'd-hazard')} ${S.text(330, 215, 'M')}
      ${S.circle(420, 185, 5, 'd-body')} ${S.arrow(420, 180, 420, 120)} ${S.text(430, 130, 'f · v_c', 'd-text', 'start')} ${S.dim(330, 240, 420, 240, 'r₀')}
      ${S.text(120, 50, `F ∝ 1/r^${lab(n)}`, 'd-text', 'start')} ${S.text(120, 74, Math.abs(n - 2) < 1e-9 ? 'closed ellipse' : n < 3 ? 'precessing rosette' : 'no stable orbit', 'd-text d-small', 'start')}
      ${S.text(500, 320, a.free_n ? 'n is hypothetical unless equal to 2' : `D = ${lab(v.D_s)} spatial dimensions (hypothetical)`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Bound any departure of the gravitational exponent from 2 using the absence of anomalous precession and direct laboratory tests.',
    apparatus: ['Lunar laser ranging stations and retro-reflectors on the Moon', 'Planetary ranging to spacecraft orbiting Mercury and Mars', 'Torsion pendulum with a rotating attractor for sub-millimetre separations', 'Analogue demonstration: charged or magnetic pucks on an air table with an engineered central force'],
    instruments: [{ name: 'Lunar laser ranging', measures: 'Earth–Moon distance, hence precession of the lunar perigee', range: '3.6–4.1 × 10⁵ km', resolution: 'millimetres' }, { name: 'Radio-science ranging', measures: 'Planetary perihelion precession', range: '0.3–2.5 AU', resolution: 'metres' }, { name: 'Torsion-balance autocollimator', measures: 'Torque from a source mass against separation', range: '50 µm–10 mm', resolution: '10⁻¹⁷ N m' }],
    procedure: ['Fit the orbit including all known Newtonian and relativistic perturbations.', 'Attribute any residual apsidal advance δφ per orbit to a change of exponent using δφ ≈ π(n − 2) for nearly circular orbits.', 'In the laboratory, compare the torque against separation with the inverse-square prediction.'],
    controls: ['Relativistic and tidal contributions modelled independently', 'Null geometry in the torsion experiment that cancels the Newtonian torque'],
    signatures: ['An anomalous precession common to all bodies and scaling with orbit number rather than with GM/(c²a)', 'A torque–distance law with a slope different from that of 1/r²'],
    safety: ['Laser safety for ranging stations', 'Standard laboratory practice for suspended masses and vacuum systems'],
  },
  falsify: ['For the mathematics: a numerically integrated bound orbit for n other than 2 or −1 that closes for arbitrary starting speed would contradict Bertrand\'s theorem.', 'A stable circular orbit found for n ≥ 3 would contradict the linear stability analysis.', 'For the counterfactual premise: observation already excludes it. Lunar and planetary ranging bound |n − 2| to roughly 10⁻¹⁰ or below at solar-system scales.'],
  alternatives: [{ name: 'General relativity', text: 'Produces precession through an additional 1/r⁴ term rather than a changed exponent; the advance scales with GM/(c²a), which distinguishes it.' }, { name: 'Yukawa-type corrections', text: 'A short-range addition to the inverse-square law, the form used in most experimental searches.' }, { name: 'Compact extra dimensions', text: 'Gravity would follow 1/r^(D−1) only below the compactification radius and 1/r² above it, evading the orbital-stability argument.' }, { name: 'Modified Newtonian dynamics', text: 'Changes the response at very low accelerations rather than the exponent everywhere; motivated by galaxy rotation curves.' }],
  limits: 'Non-relativistic point masses under a pure power-law attraction between n = −1 and 3.5. The extra-dimension reading assumes the same Newtonian dynamics in D flat, non-compact dimensions. Orbits that reach r < 10⁻³ r₀ or r > 10³ r₀ are stopped.',
  numerics: { method: 'Fourth-order Runge–Kutta in Cartesian coordinates with the step scaled to the local dynamical time; apsidal angle by midpoint quadrature after a sine substitution that removes the turning-point singularities', order: 4, resolution: 'n_orb' },
  inverse: { series: 'apsidal-sweep', curve: 1, fit: ['f_v'] },
  extensions: ['Add a small 1/r⁴ relativistic term and compare the two kinds of precession', 'Quantum analogue: stability of the hydrogen atom in D dimensions', 'Three-body dynamics under a modified exponent'],
};

// ================================================================== 10. counterfactual constants
function constantsWorld(k, a) {
  const alpha = k.e_c ** 2 / (4 * Math.PI * k.eps_0 * k.hbar * k.c);
  const mu = a.inf_nucleus ? k.m_e : k.m_e * k.m_p / (k.m_e + k.m_p);
  const a0 = 4 * Math.PI * k.eps_0 * k.hbar ** 2 / (mu * k.e_c ** 2);
  const ER = a.nonrel_atom ? mu * k.c ** 2 * alpha ** 2 / 2 : (alpha < 1 ? mu * k.c ** 2 * (1 - Math.sqrt(1 - alpha * alpha)) : NaN);
  const lP = Math.sqrt(k.hbar * k.G / k.c ** 3), tP = lP / k.c, mP = Math.sqrt(k.hbar * k.c / k.G);
  const kCh = a.chandra_lane ? 2.018236 * Math.sqrt(3 * Math.PI) / 2 / 4 : 1;
  return {
    alpha, inv_alpha: 1 / alpha, a_0: a0, E_R: ER, lambda_C: 2 * Math.PI * k.hbar / (k.m_e * k.c), r_e: alpha * k.hbar / (k.m_e * k.c),
    l_P: lP, t_P: tP, m_P: mP, T_P: mP * k.c ** 2 / k.k_B, alpha_G: k.G * k.m_p ** 2 / (k.hbar * k.c),
    M_Ch: kCh * Math.pow(k.hbar * k.c / k.G, 1.5) / k.m_p ** 2, r_S: 2 * k.G * SUN.mass / k.c ** 2, eps_b: ER / (k.m_p * k.c ** 2),
    beta_m: k.m_e / k.m_p, T_ion: ER / k.k_B, lambda_La: 2 * Math.PI * k.hbar * k.c / (0.75 * ER), sigma_SB: Math.PI ** 2 * k.k_B ** 4 / (60 * k.hbar ** 3 * k.c ** 2),
  };
}
const CONST_KEYS = ['c', 'G', 'hbar', 'e_c', 'm_e', 'm_p', 'eps_0', 'k_B'];
const REAL_K = Object.fromEntries(CONST_KEYS.map(k => [k, C[k]]));
const CW_ROWS = [
  ['alpha', 'Fine-structure constant', '1'], ['inv_alpha', 'Inverse fine-structure constant', '1'], ['a_0', 'Bohr radius', 'm', 'pm'], ['E_R', 'Hydrogen ground-state binding energy', 'J', 'eV'],
  ['lambda_C', 'Electron Compton wavelength', 'm', 'pm'], ['r_e', 'Classical electron radius', 'm', 'fm'], ['lambda_La', 'Lyman-α wavelength', 'm', 'nm'], ['T_ion', 'Ionisation temperature E_R/k_B', 'K'],
  ['l_P', 'Planck length', 'm'], ['t_P', 'Planck time', 's'], ['m_P', 'Planck mass', 'kg', 'ug'], ['T_P', 'Planck temperature', 'K'],
  ['alpha_G', 'Gravitational coupling of two protons, Gm_p²/(ħc)', '1'], ['M_Ch', 'Chandrasekhar mass', 'kg', 'Msun'], ['r_S', 'Schwarzschild radius of 1.988 × 10³⁰ kg', 'm', 'km'],
  ['eps_b', 'Hydrogen binding energy over proton rest energy', '1'], ['beta_m', 'Electron-to-proton mass ratio', '1'], ['sigma_SB', 'Stefan–Boltzmann constant', 'W/(m^2 K^4)'],
];

const constants = {
  id: 'varying-constants-world',
  title: 'A world with different constants of nature',
  module: 1, klass: 'III', domains: ['quantum', 'relativity', 'space'], hypothetical: true,
  keywords: ['constants of nature', 'fundamental constants', 'varying constants', 'different constants', 'fine-structure constant', 'fine structure constant', 'speed of light were', 'planck constant were', 'gravitational constant were', 'if the electron mass', 'another universe', 'planck length', 'bohr radius', 'chandrasekhar mass', 'anthropic', 'counterfactual universe'],
  summary: 'Recomputes atomic, Planck and stellar scales from standard formulae after the constants of nature are changed, and reports each as a ratio to its real-world value.',
  background: [
    'What is established: the formulae. The fine-structure constant, Bohr radius, Rydberg energy, Compton wavelength, Planck units and the Chandrasekhar mass are fixed combinations of c, G, ħ, e, the electron and proton masses, the vacuum permittivity and the Boltzmann constant. Laboratory clocks, quasar spectra and the Oklo natural reactor show that the dimensionless combinations have not changed by more than parts in 10⁵ over billions of years, and far less today.',
    'What is hypothetical: any change to the inputs. This model describes a counterfactual world, assuming that the form of every law is unchanged and only the constants differ. Only dimensionless combinations (such as α, the mass ratio m_e/m_p, and Gm_p²/ħc) have physical meaning: a change in c alone with all dimensionless numbers held fixed would be undetectable, because rulers and clocks would change with it. The stability statements are order-of-magnitude heuristics, labelled as such.',
  ],
  phenomena: ['Atomic structure', 'Electromagnetic coupling strength', 'Quantum-gravity (Planck) scales', 'Degeneracy-pressure support of stars', 'Dimensional analysis'],
  laws: ['schrodinger', 'sr', 'gravitation', 'pauli', 'uncertainty'],
  refs: ['Uzan, J.-P. (2003). The fundamental constants and their variation: observational and theoretical status. Rev. Mod. Phys. 75, 403–455.', 'Duff, M. J., Okun, L. B. & Veneziano, G. (2002). Trialogue on the number of fundamental constants. JHEP 03, 023.', 'Barrow, J. D. & Tipler, F. J. (1986). The Anthropic Cosmological Principle, Oxford University Press.', 'Carr, B. J. & Rees, M. J. (1979). The anthropic principle and the structure of the physical world. Nature 278, 605–612.', 'Tegmark, M. (1998). Is "the theory of everything" merely the ultimate ensemble theory? Ann. Phys. 270, 1–51.', 'Rosenband, T. et al. (2008). Frequency ratio of Al⁺ and Hg⁺ single-ion optical clocks; metrology at the 17th decimal place. Science 319, 1808–1812.', 'Webb, J. K. et al. (1999). Search for time variation of the fine structure constant. Phys. Rev. Lett. 82, 884–887.', 'Damour, T. & Dyson, F. (1996). The Oklo bound on the time variation of the fine-structure constant revisited. Nucl. Phys. B 480, 37–54.', 'Chandrasekhar, S. (1931). The maximum mass of ideal white dwarfs. Astrophys. J. 74, 81–82.'],
  inputs: CONST_KEYS.map(k => konst(k, { aliases: { c: ['speed of light'], G: ['gravitational constant', 'newton constant', 'big g'], hbar: ['planck constant', 'reduced planck constant'], e_c: ['elementary charge', 'electron charge'], m_e: ['electron mass'], m_p: ['proton mass'], eps_0: ['vacuum permittivity', 'permittivity'], k_B: ['boltzmann constant'] }[k] })),
  assumptions: [
    asm('nonrel_atom', 'Hydrogen is treated non-relativistically (Bohr–Schrödinger energy ½α²mc²).', { why: 'Accurate while α ≪ 1', alt: 'The Dirac ground-state energy mc²(1 − √(1−α²)) is used; it ceases to exist at α = 1.' }),
    asm('inf_nucleus', 'The proton is infinitely heavy compared with the electron.', { why: 'm_e/m_p ≈ 1/1836', alt: 'The reduced mass m_e m_p/(m_e + m_p) is used.' }),
    asm('chandra_lane', 'The Chandrasekhar mass includes the Lane–Emden factor for an n = 3 polytrope with two nucleons per electron.', { why: 'Gives the familiar 1.4 solar masses', alt: 'Only the dimensional scaling (ħc/G)^{3/2}/m_p² is reported.' }),
  ],
  symbols: { alpha: ['Fine-structure constant', '1'], a_0: ['Bohr radius', 'm'], E_R: ['Hydrogen binding energy', 'J'], lambda_C: ['Compton wavelength', 'm'], l_P: ['Planck length', 'm'], t_P: ['Planck time', 's'], m_P: ['Planck mass', 'kg'], M_Ch: ['Chandrasekhar mass', 'kg'], k_Ch: ['Numerical factor in the Chandrasekhar mass', '1'], r_S: ['Schwarzschild radius of a solar mass', 'm'], M_sun: ['Solar mass, as a fixed number of kilograms', 'kg'], alpha_G: ['Gravitational coupling of two protons', '1'], Z_max: ['Largest stable nuclear charge (heuristic)', '1'], mu_r: ['Reduced mass', 'kg'] },
  equations: a => {
    const m = a.inf_nucleus ? 'm_e' : 'mu_r';
    return [
      eq('alpha', 'Fine-structure constant', 'alpha', 'e_c^2/(4*pi*eps_0*hbar*c)', { kind: 'definition', origin: 'Strength of the electromagnetic interaction' }),
      ...(a.inf_nucleus ? [] : [eq('mu', 'Reduced mass', 'mu_r', 'm_e*m_p/(m_e + m_p)', { kind: 'derived', origin: 'Two-body problem' })]),
      eq('a0', 'Bohr radius', 'a_0', `4*pi*eps_0*hbar^2/(${m}*e_c^2)`, { kind: 'law', origin: 'Ground state of the Schrödinger equation with a Coulomb potential' }),
      a.nonrel_atom ? eq('ER', 'Hydrogen binding energy', 'E_R', `${m}*c^2*alpha^2/2`, { kind: 'law', origin: 'Schrödinger equation', needs: ['nonrel_atom'] })
        : eq('ER', 'Hydrogen binding energy (Dirac)', 'E_R', `${m}*c^2*(1 - sqrt(1 - alpha^2))`, { kind: 'law', origin: 'Dirac equation with a Coulomb potential' }),
      eq('lc', 'Compton wavelength', 'lambda_C', '2*pi*hbar/(m_e*c)', { kind: 'definition' }),
      eq('lp', 'Planck length', 'l_P', 'sqrt(hbar*G/c^3)', { kind: 'definition', origin: 'Dimensional analysis (Planck 1899)' }),
      eq('tp', 'Planck time', 't_P', 'sqrt(hbar*G/c^5)', { kind: 'definition' }),
      eq('mp', 'Planck mass', 'm_P', 'sqrt(hbar*c/G)', { kind: 'definition' }),
      eq('ag', 'Gravitational coupling', 'alpha_G', 'G*m_p^2/(hbar*c)', { kind: 'definition' }),
      eq('mch', 'Chandrasekhar mass', 'M_Ch', 'k_Ch*(hbar*c/G)^(3/2)/m_p^2', { kind: 'law', origin: 'Balance of relativistic electron degeneracy pressure and gravity (Chandrasekhar 1931)' }),
      eq('rs', 'Schwarzschild radius of a solar mass', 'r_S', '2*G*M_sun/c^2', { kind: 'derived', origin: 'Schwarzschild solution' }),
      eq('zmax', 'Largest stable nuclear charge', 'Z_max', '1/alpha', { kind: 'hypothesis', origin: 'Heuristic: the Dirac ground state of a point nucleus collapses when Zα reaches 1' }),
    ];
  },
  derivation: () => [
    { text: 'The only dimensionless measure of electromagnetic strength that can be built from e, ε₀, ħ and c is the fine-structure constant.', tex: '\\alpha = \\frac{e^2}{4\\pi\\varepsilon_0\\hbar c}' },
    { text: 'Balancing the electron\'s kinetic energy ħ²/(2ma²) against its Coulomb energy fixes the size and binding energy of hydrogen.', tex: 'a_0 = \\frac{\\hbar}{\\alpha\\,m_e c},\\qquad E_R = \\tfrac12\\alpha^2 m_e c^2' },
    { text: 'Combining ħ, G and c gives unique scales of length, time and mass at which quantum effects of gravity are expected.', tex: '\\ell_P = \\sqrt{\\frac{\\hbar G}{c^3}},\\qquad t_P = \\frac{\\ell_P}{c},\\qquad m_P = \\sqrt{\\frac{\\hbar c}{G}}' },
    { text: 'A star supported by relativistic degenerate electrons has a pressure that scales with density in the same way as gravity, so there is a unique mass at which they balance.', tex: 'M_{Ch} \\propto \\left(\\frac{\\hbar c}{G}\\right)^{3/2}\\frac{1}{m_p^2} = \\alpha_G^{-3/2}\\,m_p' },
    { text: 'Physical consequences depend only on dimensionless ratios. Each result is therefore also given relative to its value in our world.', tex: '\\frac{X_{\\text{world}}}{X_{\\text{real}}}' },
  ],
  solve(v, a) {
    const w = constantsWorld(v, a), r0 = constantsWorld(REAL_K, a), warnings = [];
    const changed = CONST_KEYS.filter(k => Math.abs(v[k] / C[k] - 1) > 1e-12);
    const scalars = [];
    CW_ROWS.forEach(([sym, name, unit, show]) => {
      const x = w[sym], ok = Number.isFinite(x);
      scalars.push(scalar(sym, name, x, unit, { ...(show ? { show } : {}), status: changed.length ? 'hypothetical' : undefined, text: ok ? undefined : 'No bound ground state exists (α ≥ 1)' }));
      scalars.push(scalar(`${sym}_rel`, `${name}: ratio to the real-world value`, x / r0[sym], '1', { text: ok ? undefined : 'Not defined' }));
    });
    if (changed.length) warnings.push(`Counterfactual world: ${changed.join(', ')} differ${changed.length === 1 ? 's' : ''} from the measured value. All results are conditional on the laws keeping their form.`);
    if (w.alpha >= 1) warnings.push('α ≥ 1: the Dirac ground state of hydrogen does not exist and perturbative electrodynamics fails. Atoms as we know them would not exist. (Rigorous for the point-nucleus Dirac equation; what replaces it is not established.)');
    else if (w.alpha > 1 / 6) warnings.push('Heuristic: with α above about 1/6 a nucleus of charge 6 would exceed Zα = 1, so carbon would have no stable inner-shell electrons. This is an order-of-magnitude argument, not a calculation.');
    if (w.beta_m > 0.01) warnings.push('Heuristic: with m_e/m_p above roughly 10⁻² nuclei are no longer well localised relative to electron clouds, and stable molecular structure is doubtful (Born–Oppenheimer argument; Barrow & Tipler 1986).');
    if (w.alpha_G > 1e-30) warnings.push('Heuristic: stars contain about α_G^(−3/2) nucleons. With gravity this strong, stars are far smaller and shorter-lived than the Sun (Carr & Rees 1979).');
    if (changed.length && Math.abs(w.alpha / r0.alpha - 1) < 1e-9 && Math.abs(w.beta_m / r0.beta_m - 1) < 1e-9 && Math.abs(w.alpha_G / r0.alpha_G - 1) < 1e-9) warnings.push('The dimensionless numbers α, m_e/m_p and Gm_p²/ħc are unchanged: inhabitants of this world could not detect the difference with any experiment built from atoms.');
    const names = CW_ROWS.filter(q => Number.isFinite(w[q[0]])).map(q => q[1]), logs = CW_ROWS.filter(q => Number.isFinite(w[q[0]])).map(q => Math.log10(w[q[0]] / r0[q[0]]));
    const nu = [3, 4, 5, 6, 7, 8, 9], balmer = x => nu.map(n => 2 * Math.PI * v.hbar * v.c / (x.E_R * (0.25 - 1 / (n * n))) * 1e9);
    const balReal = nu.map(n => 2 * Math.PI * C.hbar * C.c / (r0.E_R * (0.25 - 1 / (n * n))) * 1e9);
    const as = N.linspace(0.001, 1, 200);
    const scales = [w.l_P, w.r_e, w.lambda_C, w.a_0, w.r_S];
    return {
      scalars,
      series: [
        line('ratios', 'Change of each quantity relative to the real world', 'Quantity', '–', names.map((_, i) => i), [{ label: 'log₁₀(world / real)', data: logs }], 'log₁₀ ratio', '–', { kind: 'bar', categories: names, status: changed.length ? 'hypothetical' : undefined }),
        line('balmer', 'Balmer series of hydrogen', 'Upper level n', '–', nu, [{ label: 'This world', data: Number.isFinite(w.E_R) ? balmer(w) : nu.map(() => NaN) }, { label: 'Real world', data: balReal, dash: true }], 'Wavelength', 'nm', { kind: 'scatter' }),
        line('binding', 'Hydrogen ground-state binding energy against α', 'Fine-structure constant α', '–', as, [{ label: 'Schrödinger: α²/2', data: as.map(x => x * x / 2) }, { label: 'Dirac: 1 − √(1−α²)', data: as.map(x => 1 - Math.sqrt(1 - x * x)), dash: true }], 'Binding energy', 'm c²', { marker: [w.alpha, w.alpha < 1 ? w.alpha ** 2 / 2 : NaN], note: 'The Dirac curve ends at α = 1, where the point-nucleus ground state ceases to exist.' }),
        line('scales', 'Hierarchy of length scales', 'Scale', '–', [0, 1, 2, 3, 4], [{ label: 'log₁₀(length / m)', data: scales.map(x => Math.log10(x)) }], 'log₁₀ length', '–', { kind: 'bar', categories: ['Planck length', 'Classical electron radius', 'Compton wavelength', 'Bohr radius', 'Schwarzschild radius of a solar mass'] }),
      ],
      checks: [
        check('Bohr radius × α equals the reduced Compton wavelength', a.inf_nucleus ? w.a_0 * w.alpha * v.m_e * v.c / v.hbar - 1 : 0, 1e-12, 'a₀ = ħ/(α m_e c)'),
        check('Planck length over Planck time equals c', w.l_P / w.t_P / v.c - 1, 1e-12, 'Consistency of the Planck units'),
        check('Chandrasekhar mass scales as α_G^(−3/2) m_p', w.M_Ch / (Math.pow(w.alpha_G, -1.5) * v.m_p) / (a.chandra_lane ? 2.018236 * Math.sqrt(3 * Math.PI) / 8 : 1) - 1, 1e-9, 'Dimensionless form of the stellar mass scale'),
      ],
      warnings,
    };
  },
  benchmarks() {
    const on = { nonrel_atom: true, inf_nucleus: true, chandra_lane: true }, w = constantsWorld(REAL_K, on), out = [];
    out.push(bench('Inverse fine-structure constant', w.inv_alpha, 1 / C.alpha_fs, 'CODATA 2018: 137.035 999 084', 1e-8));
    out.push(bench('Bohr radius', w.a_0, C.a_0, 'CODATA 2018: 5.291 772 109 × 10⁻¹¹ m', 1e-8));
    out.push(bench('Rydberg energy (eV)', w.E_R / EV, 13.605693, 'CODATA 2018: 13.605 693 eV', 1e-7));
    out.push(bench('Planck length (m)', w.l_P, 1.616255e-35, 'CODATA 2018: 1.616 255 × 10⁻³⁵ m', 1e-5));
    out.push(bench('Chandrasekhar mass (solar masses)', w.M_Ch / SUN.mass, 1.435, '5.74/μ_e² solar masses with μ_e = 2 (hydrogen-free composition, m_p for the nucleon mass)', 5e-3));
    out.push(bench('Stefan–Boltzmann constant', w.sigma_SB, C.sigma_SB, 'π²k_B⁴/(60ħ³c²)', 1e-8));
    return out;
  },
  validation: [],
  diagram(v) {
    const w = constantsWorld(v, { nonrel_atom: true, inf_nucleus: true, chandra_lane: true });
    const items = [['Planck length', w.l_P], ['electron radius', w.r_e], ['Compton', w.lambda_C], ['Bohr radius', w.a_0], ['r_S (1 M☉)', w.r_S]].filter(q => Number.isFinite(q[1]) && q[1] > 0);
    const X = x => 60 + 520 * N.clamp((Math.log10(x) + 40) / 50, 0, 1);
    return svg(`
      ${S.arrow(50, 200, 600, 200)} ${S.text(600, 222, 'length (log scale)', 'd-text d-small', 'end')}
      ${[-40, -30, -20, -10, 0, 10].map(e => S.line(X(10 ** e), 194, X(10 ** e), 206, 'd-line') + S.text(X(10 ** e), 226, `10^${e} m`, 'd-text d-small')).join('')}
      ${items.map((q, i) => S.circle(X(q[1]), 200, 5, 'd-hazard') + S.line(X(q[1]), 195, X(q[1]), 170 - 26 * (i % 3), 'd-dim') + S.text(X(q[1]), 162 - 26 * (i % 3), q[0], 'd-text d-small')).join('')}
      ${S.text(320, 60, `α = 1/${lab(1 / w.alpha, '', 6)}    m_e/m_p = 1/${lab(1 / w.beta_m, '', 5)}    Gm_p²/ħc = ${lab(w.alpha_G)}`)}
      ${S.text(320, 300, 'Only the dimensionless numbers decide what such a world would be like.', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Test whether the dimensionless constants are in fact constant in time and space, the empirical premise against which any counterfactual is set.',
    apparatus: ['Two optical atomic clocks based on transitions with different sensitivity to α', 'High-resolution spectrograph on a large telescope observing quasar absorption systems', 'Samples from the Oklo natural fission reactor'],
    instruments: [{ name: 'Optical frequency comb', measures: 'Ratio of two clock frequencies over years', range: 'continuous', resolution: 'fractional 10⁻¹⁸' }, { name: 'Echelle spectrograph with laser-comb calibration', measures: 'Relative wavelengths of many-multiplet absorption lines', range: 'redshift 0.5–4', resolution: '≈ 10⁻⁶ in Δα/α' }, { name: 'Isotope-ratio mass spectrometer', measures: 'Samarium-149 depletion, fixing a neutron-capture resonance energy two billion years ago', range: 'isotopic ratios', resolution: '≈ 1 %' }],
    procedure: ['Record the ratio of two clock frequencies for several years and fit a linear drift.', 'Convert the drift into a rate of change of α using calculated sensitivity coefficients.', 'Compare line spacings in distant absorbers with laboratory values to bound changes over cosmological time.'],
    controls: ['Third clock species to separate a change in α from one in the mass ratio', 'Wavelength-calibration checks with asteroid or solar-twin spectra'],
    signatures: ['A non-zero drift common to independent clock pairs with the predicted sensitivity pattern', 'Line shifts with the distinctive many-multiplet signature across species'],
    safety: ['Laser safety', 'Radiological controls for reactor-zone samples'],
  },
  falsify: ['A confirmed drift or spatial variation of α or of m_e/m_p would show that the "constants" are dynamical fields, changing the status of this model from counterfactual to physical.', 'For the formulae themselves: a hydrogen spectrum that did not scale as α²m_ec² under a controlled change of an effective constant (for example in a medium or analogue system).', 'The heuristic stability limits are not sharp predictions and cannot be falsified individually; they are order-of-magnitude guides only.'],
  alternatives: [{ name: 'Dynamical constants', text: 'Scalar fields (dilaton, quintessence, Bekenstein\'s varying-α theory) make the couplings vary in space and time and generally violate the equivalence principle.' }, { name: 'Landscape and multiverse', text: 'The constants take different values in different regions; anthropic selection then accounts for the observed values. Not directly testable at present.' }, { name: 'Derived constants', text: 'A deeper theory might fix the dimensionless numbers uniquely, leaving nothing to vary.' }],
  limits: 'Assumes all laws keep their form. Nuclear physics (quark masses, the strong coupling) is not varied, so nuclear binding, stellar burning and element synthesis are outside the model. Stability statements are heuristic. The solar mass is held fixed as a number of kilograms.',
  numerics: { method: 'Closed-form evaluation' },
  extensions: ['Add the strong coupling and quark masses to follow nuclear binding (deuteron, Hoyle state)', 'Stellar lifetimes and the habitable window in the (α, α_G) plane', 'Running of α with energy'],
};

// ================================================================== 11. Yukawa fifth force
/** Φ(x)·exp(−x) for a uniform sphere of radius R = xλ, where Φ(x) = 3(x cosh x − sinh x)/x³; stable for all x ≥ 0. */
const sphereForm = x => (x < 0.05 ? (1 + x * x / 10 + x ** 4 / 280) * Math.exp(-x) : 3 / (2 * x ** 3) * ((x - 1) + (x + 1) * Math.exp(-2 * x)));
function fifthForce(v, a, rIn) {
  const R1 = Math.cbrt(3 * v.m_1 / (4 * Math.PI * v.rho_m)), R2 = Math.cbrt(3 * v.m_2 / (4 * Math.PI * v.rho_m));
  const rMin = a.point ? 0 : (R1 + R2) * 1.0001, r = Math.max(rIn ?? v.r, rMin), lam = v.lambda_Y, al = v.alpha_Y;
  const FN = G * v.m_1 * v.m_2 / (r * r);
  let ratio;
  if (a.yukawa) {
    const x = r / lam;
    ratio = a.point ? al * (1 + x) * Math.exp(-x) : al * (1 + x) * sphereForm(R1 / lam) * sphereForm(R2 / lam) * Math.exp(-(r - R1 - R2) / lam);
  } else ratio = 3 * al * (lam / r) ** 2;
  return { R1, R2, r, FN, ratio, F: FN * (1 + ratio), clamped: (rIn ?? v.r) < rMin };
}

const yukawa = {
  id: 'yukawa-fifth-force',
  title: 'Hypothetical short-range fifth force of Yukawa form',
  module: [1, 2], klass: ['III', 'I'], domains: ['classical', 'relativity'], hypothetical: true,
  keywords: ['fifth force', 'yukawa', 'new force', 'short-range force', 'inverse-square law test', 'non-newtonian gravity', 'torsion balance', 'modified gravity at short range', 'new interaction', 'new particle', 'eot-wash', 'cavendish', 'deviation from newtonian gravity', 'light scalar'],
  summary: 'Adds a hypothetical Yukawa interaction of strength α and range λ to Newtonian gravity: force against separation, the signal it would produce in a torsion balance, and the recovery of α and λ from force–distance data.',
  background: [
    'What is established: Newton\'s inverse-square law, measured with torsion balances since Cavendish and confirmed in dedicated modern experiments down to separations of tens of micrometres. No deviation has been found.',
    'What is hypothetical: the additional interaction. Exchange of a new light boson of mass m would add a potential of Yukawa form with range λ = ħ/(mc); theories with extra dimensions, light scalars (moduli, dilatons) or new gauge bosons predict such terms. The strength α relative to gravity and the range λ are free, invented parameters here. Experiments exclude gravitational-strength couplings (α of order one) for ranges from below a tenth of a millimetre up to astronomical scales, with far tighter limits at laboratory and planetary ranges; only much weaker or much shorter-range interactions remain possible.',
  ],
  phenomena: ['Newtonian gravitation', 'Massive-boson exchange', 'Torsion-balance response', 'Thermal (Brownian) rotation noise'],
  laws: ['gravitation', 'newton2', 'newton3', 'angular'],
  refs: ['Adelberger, E. G., Heckel, B. R. & Nelson, A. E. (2003). Tests of the gravitational inverse-square law. Annu. Rev. Nucl. Part. Sci. 53, 77–121.', 'Kapner, D. J. et al. (2007). Tests of the gravitational inverse-square law below the dark-energy length scale. Phys. Rev. Lett. 98, 021101.', 'Fischbach, E. & Talmadge, C. L. (1999). The Search for Non-Newtonian Gravity, Springer.', 'Fischbach, E. et al. (1986). Reanalysis of the Eötvös experiment. Phys. Rev. Lett. 56, 3–6.', 'Arkani-Hamed, N., Dimopoulos, S. & Dvali, G. (1998). The hierarchy problem and new dimensions at a millimeter. Phys. Lett. B 429, 263–272.', 'Cavendish, H. (1798). Experiments to determine the density of the Earth. Phil. Trans. R. Soc. 88, 469–526.', 'Yukawa, H. (1935). On the interaction of elementary particles. I. Proc. Phys.-Math. Soc. Japan 17, 48–57.'],
  inputs: [
    inp('alpha_Y', 'Strength of the new interaction relative to gravity', '1', 1, { min: 1e-6, max: 1e6, kind: 'hypothetical', aliases: ['strength', 'coupling', 'alpha'], src: 'Invented. Gravitational strength is used as the default for visibility; it is excluded by experiment at this range.' }),
    inp('lambda_Y', 'Range of the new interaction', 'mm', 5, { min: 1e-3, max: 1e3, kind: 'hypothetical', aliases: ['range', 'lambda', 'interaction range'], src: 'Invented' }),
    inp('m_1', 'Source (attractor) mass', 'g', 10, { min: 0.01, max: 1e5, aliases: ['source mass', 'attractor mass', 'first mass'] }),
    inp('m_2', 'Test mass on the pendulum', 'g', 1, { min: 0.001, max: 1e4, aliases: ['test mass', 'second mass'] }),
    inp('r', 'Centre-to-centre separation', 'mm', 20, { min: 0.01, max: 1000, kind: 'geometry', aliases: ['separation', 'distance', 'apart'] }),
    inp('rho_m', 'Density of both bodies', 'kg/m^3', 19300, { min: 500, max: 23000, kind: 'material', aliases: ['density'], src: 'Tungsten; used when the bodies are finite spheres' }),
    inp('L_arm', 'Lever arm of the torsion pendulum', 'cm', 2, { min: 0.1, max: 50, kind: 'geometry', aliases: ['lever arm', 'arm length'] }),
    inp('kappa_t', 'Torsion constant of the fibre', 'N m', 3e-9, { min: 1e-11, max: 1e-5, kind: 'material', aliases: ['torsion constant', 'fibre stiffness'], src: 'Order of magnitude for a 20 µm tungsten fibre about 1 m long (per radian)' }),
    inp('T', 'Temperature of the pendulum', 'K', 293, { min: 0.01, max: 400, kind: 'environment', env: 'air_temp', aliases: ['temperature'] }),
  ],
  assumptions: [
    asm('yukawa', 'The new interaction has Yukawa form, as for exchange of a single massive boson.', { why: 'Generic prediction of a new light particle', alt: 'A power-law correction to the potential, 1 + α(λ/r)², as for two large extra dimensions; equally hypothetical.' }),
    asm('point', 'Both bodies are treated as point masses.', { why: 'Simplest geometry', alt: 'Both are uniform spheres: the Yukawa term acquires a form factor for each sphere and the separation cannot be less than the sum of the radii.' }),
    asm('noise_free', 'The angular read-out is ideal: any deflection can be resolved.', { why: 'Shows the signal alone', alt: 'Thermal (Brownian) rotation of the pendulum, rms √(k_BT/κ), sets the scale against which the signal is compared.' }),
  ],
  symbols: { F: ['Total force between the bodies', 'N'], F_N: ['Newtonian force', 'N'], V: ['Interaction potential energy', 'J'], dtheta: ['Anomalous deflection of the pendulum', 'rad'], E_med: ['Rest energy of the mediating boson', 'J'], theta_th: ['Thermal rms angle', 'rad'], x_1: ['Radius of the source sphere over the range', '1'], Phi_1: ['Form factor of the source sphere', '1'] },
  equations: a => [
    eq('newton', 'Newtonian force', 'F_N', 'G*m_1*m_2/r^2', { kind: 'law', origin: 'Newton\'s law of universal gravitation' }),
    ...(a.yukawa ? [
      eq('pot', 'Potential with a Yukawa term', 'V', '-G*m_1*m_2/r*(1 + alpha_Y*exp(-r/lambda_Y))', { kind: 'hypothesis', origin: 'Postulated exchange of a boson of mass ħ/(λc); α and λ are free parameters' }),
      eq('force', 'Force with a Yukawa term', 'F', 'G*m_1*m_2/r^2*(1 + alpha_Y*(1 + r/lambda_Y)*exp(-r/lambda_Y))', { kind: 'hypothesis', origin: 'Negative gradient of the postulated potential' }),
      eq('med', 'Rest energy of the mediator', 'E_med', 'hbar*c/lambda_Y', { kind: 'hypothesis', origin: 'Range of a force carried by a massive boson (Yukawa 1935)' }),
      ...(a.point ? [] : [eq('form', 'Yukawa form factor of a uniform sphere', 'Phi_1', '3*(x_1*cosh(x_1) - sinh(x_1))/x_1^3', { kind: 'derived', origin: 'Integration of the Yukawa potential over a uniform sphere' })]),
    ] : [
      eq('pot', 'Potential with a power-law term', 'V', '-G*m_1*m_2/r*(1 + alpha_Y*(lambda_Y/r)^2)', { kind: 'hypothesis', origin: 'Postulated; of the form expected below the size of two extra dimensions' }),
      eq('force', 'Force with a power-law term', 'F', 'G*m_1*m_2/r^2*(1 + 3*alpha_Y*(lambda_Y/r)^2)', { kind: 'hypothesis', origin: 'Negative gradient of the postulated potential' }),
    ]),
    eq('defl', 'Anomalous deflection of the pendulum', 'dtheta', '2*(F - F_N)*L_arm/kappa_t', { kind: 'derived', origin: 'Torque balance for two source–test pairs on opposite arms (Cavendish geometry)' }),
    ...(a.noise_free ? [] : [eq('noise', 'Thermal rms angle', 'theta_th', 'sqrt(k_B*T/kappa_t)', { kind: 'law', origin: 'Equipartition theorem for the torsional mode' })]),
  ],
  derivation: a => [
    { text: 'A static field carried by a boson of mass m obeys the screened Poisson equation, whose point-source solution falls off exponentially over the range λ = ħ/(mc).', tex: '\\left(\\nabla^2 - \\lambda^{-2}\\right)\\phi = 4\\pi G\\alpha\\,\\rho\\ \\Rightarrow\\ \\phi = -\\frac{G\\alpha m}{r}\\,e^{-r/\\lambda}' },
    { text: 'Adding this to the Newtonian potential and differentiating gives the force. For r ≪ λ gravity appears stronger by the factor 1 + α; for r ≫ λ it is Newtonian.', tex: 'F(r) = \\frac{G m_1 m_2}{r^2}\\left[1 + \\alpha\\left(1 + \\frac{r}{\\lambda}\\right)e^{-r/\\lambda}\\right]' },
    { text: 'The anomaly is largest, relative to gravity, at separations comparable with the range; this is why each experiment constrains α best near its own length scale.', tex: '\\frac{\\Delta F}{F_N} = \\alpha\\left(1 + \\frac{r}{\\lambda}\\right)e^{-r/\\lambda}' },
    { text: 'In a torsion balance with lever arm L and fibre constant κ the extra force on the two test masses twists the pendulum through a small angle.', tex: '\\Delta\\theta = \\frac{2\\,\\Delta F\\,L}{\\kappa}' },
    ...(a.point ? [] : [{ text: 'For a uniform sphere of radius R the exterior Yukawa field is that of a point mass multiplied by a form factor greater than one.', tex: '\\Phi(x) = \\frac{3\\,(x\\cosh x - \\sinh x)}{x^3},\\qquad x = R/\\lambda' }]),
  ],
  solve(v, a) {
    const q = fifthForce(v, a), warnings = [], lam = v.lambda_Y;
    if (q.clamped) warnings.push('The requested separation is less than the sum of the sphere radii; the spheres are placed in contact instead.');
    warnings.push('Conditional result: the additional interaction is hypothetical. Torsion-balance experiments exclude gravitational-strength Yukawa couplings at millimetre ranges; see the falsification section.');
    const dF = q.F - q.FN, tauN = 2 * q.FN * v.L_arm, dtau = 2 * dF * v.L_arm, dth = dtau / v.kappa_t;
    const thTh = Math.sqrt(kB * v.T / v.kappa_t);
    const rLo = Math.max(Math.min(q.r, lam) / 20, a.point ? 0 : (q.R1 + q.R2) * 1.0001), rs = N.logspace(rLo, Math.max(q.r, lam) * 20, 100);
    const fs = rs.map(x => fifthForce(v, a, x));
    const ls = N.logspace(lam / 100, lam * 100, 80), lsw = ls.map(x => fifthForce({ ...v, lambda_Y: x }, a).ratio);
    // magnitude of the attraction equals dV/dr for the point-mass Yukawa case; checked by central difference
    const Vp = x => -G * v.m_1 * v.m_2 / x * (1 + v.alpha_Y * Math.exp(-x / lam)), h = 1e-5 * q.r;
    const dV = a.yukawa && a.point ? ((Vp(q.r + h) - Vp(q.r - h)) / (2 * h) - q.F) / q.F : 0;
    return {
      scalars: [
        scalar('F', 'Total attractive force', q.F, 'N', { status: 'hypothetical' }), scalar('F_N', 'Newtonian force', q.FN, 'N'),
        scalar('dF', 'Force due to the new interaction', dF, 'N', { status: 'hypothetical' }), scalar('dF_rel', 'Fractional anomaly ΔF/F_N', q.ratio, '1', { status: 'hypothetical' }),
        scalar('tau_N', 'Newtonian torque on the pendulum', tauN, 'N m'), scalar('dtau', 'Anomalous torque', dtau, 'N m', { status: 'hypothetical' }),
        scalar('theta_N', 'Newtonian deflection', tauN / v.kappa_t, 'rad'), scalar('dtheta', 'Anomalous deflection', dth, 'rad', { status: 'hypothetical' }),
        scalar('theta_th', 'Thermal rms angle of the pendulum', thTh, 'rad'),
        scalar('snr', 'Anomalous deflection over thermal rms angle', a.noise_free ? Infinity : dth / thTh, '1', { status: 'hypothetical', text: a.noise_free ? 'Not limited: ideal read-out assumed' : undefined }),
        scalar('E_med', 'Rest energy of the mediating boson', hbar * c / lam, 'J', { show: 'eV', status: 'hypothetical' }),
        scalar('m_med', 'Mass of the mediating boson', hbar / (lam * c), 'kg', { status: 'hypothetical' }),
        scalar('r_eff', 'Separation used', q.r, 'm', { show: 'mm' }), scalar('R_1', 'Radius of the source sphere', q.R1, 'm', { show: 'mm' }), scalar('R_2', 'Radius of the test sphere', q.R2, 'm', { show: 'mm' }),
        scalar('r_lam', 'Separation over range', q.r / lam, '1'),
      ],
      series: [
        line('force', 'Force against separation', 'Separation', 'mm', rs.map(x => x * 1e3), [{ label: 'Inverse-square law', data: fs.map(f => f.FN), dash: true }, { label: 'With the hypothetical interaction', data: fs.map(f => f.F) }], 'Force', 'N', { logx: true, logy: true, status: 'hypothetical' }),
        line('anomaly', 'Fractional anomaly against separation', 'Separation', 'mm', rs.map(x => x * 1e3), [{ label: 'ΔF/F_N', data: fs.map(f => f.ratio) }], 'Fractional anomaly', '–', { logx: true, logy: true, status: 'hypothetical' }),
        line('range-sweep', 'Fractional anomaly at this separation against range', 'Range λ', 'mm', ls.map(x => x * 1e3), [{ label: 'ΔF/F_N', data: lsw }], 'Fractional anomaly', '–', { logx: true, logy: true, status: 'hypothetical' }),
      ],
      checks: [
        check('Attraction equals the gradient of the potential energy', dV, 1e-6, 'Central difference of V(r) for the point-mass Yukawa case'),
        check('Anomaly has the sign of α', q.ratio < 0 ? 1 : 0, 0, 'A positive coupling strengthens the attraction'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { yukawa: true, point: true, noise_free: true }, out = [];
    out.push(bench('Long-range limit: force tends to Newtonian', fifthForce({ ...v, r: 60 * v.lambda_Y }, on).F / fifthForce({ ...v, r: 60 * v.lambda_Y }, on).FN, 1, 'r ≫ λ', 1e-12 * Math.max(1, v.alpha_Y * 1e3)));
    out.push(bench('Short-range limit: gravity strengthened by 1 + α', 1 + fifthForce({ ...v, r: 1e-4 * v.lambda_Y }, on).ratio, 1 + v.alpha_Y, 'r ≪ λ', 1e-6));
    // form factor against direct numerical integration of the Yukawa potential over a uniform sphere
    const Rs = 1, lam = 0.7, d = 3, nI = 80;
    let sum = 0;
    for (let i = 0; i < nI; i++) for (let j = 0; j < nI; j++) { const s = (i + 0.5) / nI * Rs, mu = -1 + 2 * (j + 0.5) / nI, dist = Math.sqrt(d * d + s * s - 2 * d * s * mu); sum += s * s * Math.exp(-dist / lam) / dist; }
    const phiNum = 2 * Math.PI * sum * (Rs / nI) * (2 / nI) / (4 / 3 * Math.PI * Rs ** 3) * d * Math.exp(d / lam);
    out.push(bench('Sphere form factor against direct integration', sphereForm(Rs / lam) * Math.exp(Rs / lam), phiNum, 'Φ(x) = 3(x cosh x − sinh x)/x³', 1e-3));
    out.push(bench('Form factor tends to one for a small sphere', sphereForm(1e-3) * Math.exp(1e-3), 1, 'x → 0', 1e-6));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.line(320, 30, 320, 150, 'd-dim')} ${S.text(332, 80, 'torsion fibre κ', 'd-text d-small', 'start')}
      ${S.line(200, 150, 440, 150, 'd-pipe')} ${S.circle(200, 150, 12, 'd-body')} ${S.circle(440, 150, 12, 'd-body')} ${S.text(200, 126, 'm₂')} ${S.text(440, 126, 'm₂')}
      ${S.circle(200, 240, 24, 'd-hazard')} ${S.circle(440, 60, 24, 'd-hazard')} ${S.text(200, 284, 'm₁')} ${S.text(486, 64, 'm₁', 'd-text', 'start')}
      ${S.arrow(200, 166, 200, 210)} ${S.arrow(440, 134, 440, 90)} ${S.dim(150, 150, 150, 240, '')} ${S.text(140, 200, 'r', 'd-text', 'end')}
      ${S.dim(320, 180, 440, 180, 'L')} ${S.path('M300 150 A20 20 0 0 1 320 130', 'd-arrow')} ${S.text(292, 132, 'θ', 'd-text', 'end')}
      ${S.text(480, 250, `α = ${lab(v.alpha_Y)}   λ = ${lab(v.lambda_Y * 1e3, 'mm')}`, 'd-text')} ${S.text(480, 272, 'hypothetical interaction', 'd-text d-small')}
      ${S.text(480, 300, a.yukawa ? 'F = F_N [1 + α(1 + r/λ) e^(−r/λ)]' : 'F = F_N [1 + 3α(λ/r)²]', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the force between laboratory masses as a function of separation and bound any departure from the inverse-square law.',
    apparatus: ['Torsion pendulum carrying a test body with an azimuthal pattern of holes or density contrast', 'Rotating attractor with a matching pattern, on a precision stage that sets the separation', 'Thin conducting membrane between pendulum and attractor to block electrostatic forces', 'Vacuum chamber, magnetic shielding and temperature-stabilised enclosure'],
    instruments: [{ name: 'Autocollimator on the pendulum mirror', measures: 'Twist angle', range: '±1 mrad', resolution: '≈ 1 nrad/√Hz' }, { name: 'Capacitive or interferometric gap sensor', measures: 'Pendulum–attractor separation', range: '50 µm–10 mm', resolution: '≈ 1 µm' }, { name: 'Rotary encoder on the attractor', measures: 'Attractor phase for lock-in detection of the torque harmonic', range: '0–360°', resolution: 'arcseconds' }],
    procedure: ['Rotate the attractor slowly so that the gravitational torque appears at a known multiple of the rotation frequency, away from the pendulum resonance.', 'Record the torque amplitude at that harmonic for a range of separations.', 'Compute the Newtonian torque for the exact geometry by numerical integration and subtract it.', 'Fit the residual against separation with a Yukawa term to obtain limits on α for each λ.'],
    controls: ['Second attractor layer designed so that the Newtonian torque nearly cancels while a short-range torque would not', 'Runs with the electrostatic shield at several potentials', 'Magnetic and thermal-gradient modulation tests', 'Calibration with a known gravitational torque from external spheres'],
    signatures: ['A residual torque that falls exponentially with separation with a single decay length', 'Sign and magnitude independent of the electrostatic and magnetic environment'],
    safety: ['Heavy source masses on motor-driven stages: guard against pinch and crush', 'Vacuum and high-voltage precautions for the electrostatic controls'],
  },
  falsify: ['The hypothesis of a Yukawa interaction with given (α, λ) is refuted by a measured torque–distance curve consistent with pure Newtonian gravity at the corresponding sensitivity.', 'Torsion-balance tests of the inverse-square law by the Eöt-Wash group and others find no deviation: gravitational-strength couplings are excluded for ranges down to the sub-tenth-of-a-millimetre scale, and the allowed α falls steeply at longer laboratory ranges (Adelberger, Heckel & Nelson 2003; Kapner et al. 2007). The default α = 1 at λ = 5 mm used here is therefore already excluded.', 'Lunar laser ranging and planetary ephemerides exclude far weaker couplings at ranges from 10⁸ to 10¹² m.', 'A composition-dependent version is tested by Eötvös-type experiments and the MICROSCOPE satellite, which find no differential acceleration.'],
  alternatives: [{ name: 'Pure Newtonian gravity', text: 'α = 0; consistent with all data to date.' }, { name: 'Large extra dimensions', text: 'Gravity changes from 1/r² to 1/r^(2+k) below the compactification radius; near that radius the leading correction is itself of Yukawa form.' }, { name: 'Chameleon and symmetron scalars', text: 'Fields whose range depends on the ambient matter density, suppressing the force in dense laboratory environments; they require dedicated experimental geometries.' }, { name: 'Casimir and patch-potential backgrounds', text: 'At micrometre separations electromagnetic forces between surfaces dominate and can mimic or mask a short-range anomaly.' }],
  hazards: [{ hazard: 'Crushing or pinching by source masses', cause: 'Motor-driven stages carrying dense bodies near the pendulum', mitigation: 'Interlocked enclosure and travel limits' }, { hazard: 'Implosion or electric shock', cause: 'Vacuum chamber and biased shields', mitigation: 'Rated viewports, guarded feed-throughs, discharge procedure' }],
  limits: 'Static, non-relativistic point masses or uniform spheres with a composition-independent coupling. Real experiments use planar or patterned geometries that need numerical integration. The power-law alternative is evaluated for point masses only. Thermal noise is quoted as the equipartition rms angle without averaging or frequency selectivity.',
  numerics: { method: 'Closed-form forces with an overflow-safe evaluation of the sphere form factor' },
  optimise: { objective: 'dtheta', sense: 'max', vars: ['r'], note: 'The anomalous deflection grows as the bodies approach; the practical limit is set by electrostatic and Casimir backgrounds.' },
  inverse: { series: 'force', curve: 1, fit: ['alpha_Y', 'lambda_Y'] },
  extensions: ['Planar and patterned attractor geometries by numerical integration', 'Composition-dependent coupling to baryon number and the Eötvös parameter', 'Exclusion plot in the (α, λ) plane from a stated torque sensitivity', 'Casimir and electrostatic patch backgrounds at micrometre separations'],
};

// ================================================================== 12. tunnelling through a barrier
/** Exact transmission of a rectangular barrier of height V0 and width L, with the far side lowered by Vb. Returns {T, lnT}. */
function rectBarrier(E, V0, L, m, Vb = 0) {
  const k1 = Math.sqrt(2 * m * E) / hbar, k3 = Math.sqrt(2 * m * (E + Vb)) / hbar, d = V0 - E;
  if (Math.abs(d) < 1e-12 * V0) { const T = 4 * k1 * k3 / ((k1 + k3) ** 2 + (k1 * k3 * L) ** 2); return { T, lnT: Math.log(T) }; }
  if (d > 0) {
    const ka = Math.sqrt(2 * m * d) / hbar, x = ka * L, pre = (ka * ka + k1 * k1) * (ka * ka + k3 * k3);
    if (x > 20) { const lnT = Math.log(16 * k1 * k3 * ka * ka / pre) - 2 * x; return { T: Math.exp(lnT), lnT }; }
    const T = 4 * k1 * k3 * ka * ka / ((k1 + k3) ** 2 * ka * ka + pre * Math.sinh(x) ** 2); return { T, lnT: Math.log(T) };
  }
  const q = Math.sqrt(-2 * m * d) / hbar, T = 4 * k1 * k3 * q * q / ((k1 + k3) ** 2 * q * q + (k1 * k1 - q * q) * (k3 * k3 - q * q) * Math.sin(q * L) ** 2);
  return { T, lnT: Math.log(T) };
}
/**
 * Transfer-matrix solution for an arbitrary barrier V(x) on 0 ≤ x ≤ L, built from slices of constant potential.
 * Integrates (ψ, ψ') backward from the transmitted wave exp(i k3 x); rescales to avoid overflow. Returns {T, R, lnT, xs, dens}.
 */
function transferMatrix(E, Vfun, L, m, Vb, nSl) {
  const k1 = Math.sqrt(2 * m * E) / hbar, k3 = Math.sqrt(2 * m * (E + Vb)) / hbar, d = L / nSl;
  let pr = 1, pi = 0, dr = 0, di = k3, logS = 0; const xs = [L], amp = [0], lg = [0];
  amp[0] = 1;
  for (let j = nSl - 1; j >= 0; j--) {
    const K2 = 2 * m * (E - Vfun((j + 0.5) * d)) / (hbar * hbar);
    let m11, m12, m21;
    if (K2 > 0) { const K = Math.sqrt(K2); m11 = Math.cos(K * d); m12 = -Math.sin(K * d) / K; m21 = K * Math.sin(K * d); }
    else if (K2 < 0) { const K = Math.sqrt(-K2), z = Math.min(K * d, 600); m11 = Math.cosh(z); m12 = -Math.sinh(z) / K; m21 = -K * Math.sinh(z); }
    else { m11 = 1; m12 = -d; m21 = 0; }
    const npr = m11 * pr + m12 * dr, ndr = m21 * pr + m11 * dr, npi = m11 * pi + m12 * di, ndi = m21 * pi + m11 * di;
    pr = npr; dr = ndr; pi = npi; di = ndi;
    const mag = Math.hypot(pr, pi);
    if (mag > 1e100) { pr *= 1e-100; pi *= 1e-100; dr *= 1e-100; di *= 1e-100; logS += 100 * Math.LN10; }
    xs.push(j * d); amp.push(pr * pr + pi * pi); lg.push(logS);
  }
  const ar = 0.5 * (pr + di / k1), ai = 0.5 * (pi - dr / k1), br = 0.5 * (pr - di / k1), bi = 0.5 * (pi + dr / k1);
  const A2 = ar * ar + ai * ai, B2 = br * br + bi * bi, lnT = Math.log(k3 / k1) - Math.log(A2) - 2 * logS;
  // probability density relative to the incident wave, on the barrier and on both sides
  const X = [], D = [], lnA2 = Math.log(A2) + 2 * logS;
  for (let i = 40; i >= 1; i--) { const x = -L * i / 40, ph = 2 * k1 * x, cr = ar * br + ai * bi, ci = ai * br - ar * bi; X.push(x); D.push(1 + B2 / A2 + 2 * (cr * Math.cos(ph) - ci * Math.sin(ph)) / A2); }
  for (let i = xs.length - 1; i >= 0; i--) { X.push(xs[i]); D.push(Math.exp(Math.log(Math.max(amp[i], 1e-300)) + 2 * lg[i] - lnA2)); }
  for (let i = 1; i <= 40; i++) { X.push(L + L * i / 40); D.push(Math.exp(-lnA2)); }
  return { T: Math.exp(lnT), R: B2 / A2, lnT, xs: X, dens: D };
}

const tunnelling = {
  id: 'quantum-tunnelling-barrier',
  title: 'Quantum tunnelling through a potential barrier',
  module: [1, 2], klass: 'I', domains: ['quantum'],
  keywords: ['tunnelling', 'tunneling', 'potential barrier', 'rectangular barrier', 'transmission coefficient', 'transmission probability', 'wkb', 'barrier penetration', 'scanning tunnelling microscope', 'stm', 'tunnel junction', 'alpha decay', 'quantum barrier', 'evanescent'],
  summary: 'Transmission of a particle through a one-dimensional barrier: the exact rectangular-barrier result below and above the barrier top, a transfer-matrix solution for other shapes, and the WKB estimate.',
  background: [
    'A quantum particle meeting a barrier higher than its energy is not wholly reflected: its wavefunction decays exponentially inside the barrier and emerges on the far side with reduced amplitude. The transmission probability for a rectangular barrier follows exactly from matching the wavefunction and its slope at the two edges. For thick barriers it falls as exp(−2κL), which is why the tunnel current in a scanning tunnelling microscope changes by about a factor of ten for each ångström of gap.',
    'Above the barrier top the transmission oscillates and reaches unity whenever a whole number of half-wavelengths fits in the barrier. Tunnelling is established physics, underlying alpha decay, tunnel diodes, Josephson junctions, flash memory and field emission.',
  ],
  phenomena: ['Evanescent decay inside the barrier', 'Probability-current conservation', 'Transmission resonances', 'Semiclassical (WKB) penetration'],
  laws: ['schrodinger', 'born', 'uncertainty'],
  refs: ['Gamow, G. (1928). Zur Quantentheorie des Atomkernes. Zeitschrift für Physik 51, 204–212.', 'Griffiths, D. J. & Schroeter, D. F. (2018). Introduction to Quantum Mechanics, 3rd ed., Cambridge University Press, §2.6 and ch. 9.', 'Landau, L. D. & Lifshitz, E. M. (1977). Quantum Mechanics: Non-Relativistic Theory, 3rd ed., Pergamon, §§25 and 50.', 'Hill, D. L. & Wheeler, J. A. (1953). Nuclear constitution and the interpretation of fission phenomena. Phys. Rev. 89, 1102–1145.', 'Binnig, G., Rohrer, H., Gerber, Ch. & Weibel, E. (1982). Surface studies by scanning tunneling microscopy. Phys. Rev. Lett. 49, 57–61.', 'Simmons, J. G. (1963). Generalized formula for the electric tunnel effect between similar electrodes separated by a thin insulating film. J. Appl. Phys. 34, 1793–1803.'],
  inputs: [
    inp('E', 'Particle energy', 'eV', 5, { min: 0.01, max: 100, aliases: ['energy', 'particle energy', 'kinetic energy'] }),
    inp('V_0', 'Barrier height', 'eV', 10, { min: 0.1, max: 100, kind: 'material', aliases: ['barrier height', 'barrier', 'potential', 'work function'] }),
    inp('L', 'Barrier width', 'nm', 0.3, { min: 0.01, max: 5, kind: 'geometry', aliases: ['width', 'thickness', 'barrier width', 'gap', 'wide', 'thick'] }),
    inp('m_r', 'Particle mass in electron masses', '1', 1, { min: 0.01, max: 2000, kind: 'material', aliases: ['effective mass', 'mass ratio', 'electron masses'], src: 'Free electron; 1836 for a proton' }),
    inp('V_b', 'Potential drop on the far side (used when the two sides differ)', 'eV', 1, { min: 0, max: 20, aliases: ['bias', 'potential drop'] }),
  ],
  assumptions: [
    asm('exact', 'The Schrödinger equation is solved exactly by matching at the barrier edges.', { why: 'Available in closed form for a rectangular barrier', alt: 'The WKB estimate exp(−2∫κ dx) is used instead: adequate for thick barriers, wrong near and above the barrier top.' }),
    asm('rect', 'The barrier is rectangular.', { why: 'Standard idealisation', alt: 'The barrier is an inverted parabola of the same height and base width, solved by transfer matrix and compared with the Hill–Wheeler formula.' }),
    asm('symmetric', 'The potential is the same on both sides of the barrier.', { why: 'Unbiased junction', alt: 'The far side is lower by V_b, as in a biased junction; the transmitted wavenumber changes.' }),
  ],
  symbols: { T: ['Transmission probability', '1'], R: ['Reflection probability', '1'], kappa: ['Decay constant inside the barrier', '1/m'], k_b: ['Wavenumber above the barrier', '1/m'], k_1: ['Incident wavenumber', '1/m'], k_3: ['Transmitted wavenumber', '1/m'], psi: ['Wavefunction (arbitrary normalisation)', '1'], x: ['Position', 'm'], V: ['Potential energy', 'J'], omega_b: ['Curvature frequency of the parabolic barrier', '1/s'] },
  equations: (a, v) => {
    const below = !v || v.E < v.V_0;
    return [
      eq('tise', 'Time-independent Schrödinger equation', '-hbar^2/(2*m_r*m_e)*d2(psi,x) + V*psi', 'E*psi', { kind: 'law', origin: 'Schrödinger (1926)' }),
      eq('k1', 'Incident wavenumber', 'k_1', 'sqrt(2*m_r*m_e*E)/hbar', { kind: 'definition' }),
      below ? eq('kap', 'Decay constant inside the barrier', 'kappa', 'sqrt(2*m_r*m_e*(V_0 - E))/hbar', { kind: 'derived', origin: 'Schrödinger equation in the classically forbidden region' })
        : eq('kap', 'Wavenumber above the barrier', 'k_b', 'sqrt(2*m_r*m_e*(E - V_0))/hbar', { kind: 'derived', origin: 'Schrödinger equation above the barrier top' }),
      ...(a.symmetric ? [] : [eq('k3', 'Transmitted wavenumber', 'k_3', 'sqrt(2*m_r*m_e*(E + V_b))/hbar', { kind: 'definition' })]),
      ...(!a.exact ? [below ? eq('T', 'WKB transmission', 'T', a.rect ? 'exp(-2*kappa*L)' : 'exp(-2*pi*(V_0 - E)/(hbar*omega_b))', { kind: 'closure', origin: 'Semiclassical approximation (Wentzel, Kramers, Brillouin 1926)' }) : eq('T', 'WKB transmission above the barrier', 'T', '1', { kind: 'closure', origin: 'Semiclassical approximation: no classically forbidden region' })]
        : !a.rect ? [eq('T', 'Transmission of a parabolic barrier', 'T', '1/(1 + exp(2*pi*(V_0 - E)/(hbar*omega_b)))', { kind: 'derived', origin: 'Exact solution for an inverted parabola (Kemble 1935; Hill & Wheeler 1953)' })]
          : a.symmetric ? [below ? eq('T', 'Transmission below the barrier top', 'T', '1/(1 + V_0^2*sinh(kappa*L)^2/(4*E*(V_0 - E)))', { kind: 'derived', origin: 'Continuity of ψ and ψ′ at both edges', needs: ['exact', 'rect', 'symmetric'] })
            : eq('T', 'Transmission above the barrier top', 'T', '1/(1 + V_0^2*sin(k_b*L)^2/(4*E*(E - V_0)))', { kind: 'derived', origin: 'Continuity of ψ and ψ′ at both edges', needs: ['exact', 'rect', 'symmetric'] })]
            : [below ? eq('T', 'Transmission with unequal sides', 'T', '4*k_1*k_3*kappa^2/((k_1 + k_3)^2*kappa^2 + (kappa^2 + k_1^2)*(kappa^2 + k_3^2)*sinh(kappa*L)^2)', { kind: 'derived', origin: 'Continuity of ψ and ψ′ at both edges' })
              : eq('T', 'Transmission with unequal sides', 'T', '4*k_1*k_3*k_b^2/((k_1 + k_3)^2*k_b^2 + (k_1^2 - k_b^2)*(k_3^2 - k_b^2)*sin(k_b*L)^2)', { kind: 'derived', origin: 'Continuity of ψ and ψ′ at both edges' })]),
      ...(a.rect ? [] : [eq('wb', 'Curvature frequency of the parabolic barrier', 'omega_b', 'sqrt(8*V_0/(m_r*m_e*L^2))', { kind: 'definition' })]),
      eq('flux', 'Conservation of probability current', 'R + T', '1', { kind: 'law', origin: 'Continuity equation for the probability density' }),
    ];
  },
  derivation: a => [
    { text: 'Outside the barrier the solutions are travelling waves; inside, where V₀ > E, they are real exponentials with decay constant κ.', tex: '\\psi_{\\rm I} = e^{ikx} + r\\,e^{-ikx},\\quad \\psi_{\\rm II} = A e^{\\kappa x} + B e^{-\\kappa x},\\quad \\psi_{\\rm III} = t\\,e^{ikx},\\qquad \\kappa = \\frac{\\sqrt{2m(V_0-E)}}{\\hbar}' },
    { text: 'Requiring ψ and its derivative to be continuous at x = 0 and x = L gives four equations for r, A, B and t. Eliminating the others yields the transmission probability.', tex: 'T = |t|^2 = \\left[1 + \\frac{V_0^2\\,\\sinh^2(\\kappa L)}{4E\\,(V_0 - E)}\\right]^{-1}' },
    { text: 'For an opaque barrier, κL ≫ 1, the hyperbolic sine is a pure exponential.', tex: 'T \\simeq 16\\,\\frac{E}{V_0}\\left(1 - \\frac{E}{V_0}\\right)e^{-2\\kappa L}' },
    { text: 'Above the barrier top κ becomes imaginary: the hyperbolic sine turns into a sine and the transmission is perfect whenever k_b L is a multiple of π.', tex: 'T = \\left[1 + \\frac{V_0^2\\,\\sin^2(k_b L)}{4E\\,(E - V_0)}\\right]^{-1}' },
    { text: a.exact ? 'The semiclassical estimate keeps only the exponential of the action under the barrier and drops the prefactor.' : 'The WKB estimate used here keeps only the exponential of the action under the barrier; it omits the prefactor and all reflection above the barrier.', tex: 'T_{\\rm WKB} = \\exp\\!\\left(-\\frac{2}{\\hbar}\\int_{x_1}^{x_2}\\!\\sqrt{2m\\,(V(x)-E)}\\;\\mathrm{d}x\\right)' },
  ],
  solve(v, a) {
    const m = v.m_r * C.m_e, E = v.E, V0 = v.V_0, L = v.L, Vb = a.symmetric ? 0 : v.V_b, warnings = [];
    const shape = a.rect ? (() => V0) : (x => V0 * (1 - (2 * x / L - 1) ** 2));
    const nSl = a.rect ? 60 : 300, wb = Math.sqrt(8 * V0 / (m * L * L));
    const kap = E < V0 ? Math.sqrt(2 * m * (V0 - E)) / hbar : 0, kb = E > V0 ? Math.sqrt(2 * m * (E - V0)) / hbar : 0;
    const wkbLn = e => (e >= V0 ? 0 : a.rect ? -2 * Math.sqrt(2 * m * (V0 - e)) / hbar * L : -2 * Math.PI * (V0 - e) / (hbar * wb));
    const exactLn = e => (a.rect ? rectBarrier(e, V0, L, m, Vb).lnT : transferMatrix(e, shape, L, m, Vb, nSl).lnT);
    const tm = transferMatrix(E, shape, L, m, Vb, nSl), rc = rectBarrier(E, V0, L, m, Vb);
    const lnT = a.exact ? (a.rect ? rc.lnT : tm.lnT) : wkbLn(E), T = Math.exp(lnT);
    const opaque = E < V0 ? Math.log(16 * (E / V0) * (1 - E / V0)) - 2 * kap * L : NaN;
    const hw = 1 / (1 + Math.exp(Math.min(2 * Math.PI * (V0 - E) / (hbar * wb), 700)));
    if (!a.exact && E >= 0.8 * V0) warnings.push('The WKB estimate is unreliable near and above the barrier top, where the action under the barrier is not large compared with ħ.');
    if (!a.exact && E < V0 && kap * L < 1.5 && a.rect) warnings.push('κL is of order one: the barrier is thin and the neglected prefactor of the WKB estimate matters.');
    if (v.m_r * C.m_e * c2 < 20 * Math.max(E, V0)) warnings.push('The energies are not small compared with the rest energy; a relativistic treatment would be needed.');
    const Es = N.linspace(0.02 * V0, 3 * V0, 200), Ls = N.linspace(0.1 * L, 3 * L, 80), fl = x => Math.max(x, 1e-300);
    const TE = Es.map(e => Math.exp(exactLn(e))), TW = Es.map(e => Math.exp(wkbLn(e)));
    const TL = Ls.map(l => { const sh = a.rect ? shape : (x => V0 * (1 - (2 * x / l - 1) ** 2)); return fl(Math.exp(a.rect ? rectBarrier(E, V0, l, m, Vb).lnT : transferMatrix(E, sh, l, m, Vb, 120).lnT)); });
    const TLw = Ls.map(l => fl(Math.exp(E >= V0 ? 0 : a.rect ? -2 * kap * l : -2 * Math.PI * (V0 - E) / (hbar * Math.sqrt(8 * V0 / (m * l * l))))));
    const k1 = Math.sqrt(2 * m * E) / hbar;
    return {
      scalars: [
        scalar('T', 'Transmission probability', T, '1'), scalar('R', 'Reflection probability', 1 - T, '1'),
        scalar('log10_T', 'log₁₀ of the transmission probability', lnT / Math.LN10, '1'),
        scalar('kappa', 'Decay constant inside the barrier', kap, '1/m', { text: E < V0 ? undefined : 'Not applicable: the energy is above the barrier top' }),
        scalar('d_pen', 'Penetration depth 1/κ', E < V0 ? 1 / kap : Infinity, 'm', { show: 'nm', text: E < V0 ? undefined : 'Not applicable: the energy is above the barrier top' }),
        scalar('kL', 'Barrier opacity κL (or phase k_bL above the top)', E < V0 ? kap * L : kb * L, '1'),
        scalar('T_rect', 'Exact rectangular-barrier transmission', rc.T, '1'), scalar('T_tm', 'Transfer-matrix transmission for the chosen shape', tm.T, '1'), scalar('R_tm', 'Transfer-matrix reflection for the chosen shape', tm.R, '1'),
        scalar('T_wkb', 'WKB estimate', Math.exp(wkbLn(E)), '1'),
        scalar('T_opq', 'Opaque-barrier approximation', Math.exp(opaque), '1', { text: E < V0 ? undefined : 'Not applicable above the barrier top' }),
        scalar('T_hw', 'Hill–Wheeler transmission of a full parabolic barrier', hw, '1'),
        scalar('lambda_dB', 'Incident de Broglie wavelength', 2 * Math.PI / k1, 'm', { show: 'nm' }),
        scalar('E_res', 'First transmission resonance above the barrier', V0 + (Math.PI * hbar / L) ** 2 / (2 * m), 'J', { show: 'eV' }),
        scalar('dec_A', 'Change of transmission per ångström of extra width (factor)', E < V0 ? Math.exp(-2 * kap * 1e-10) : 1, '1'),
      ],
      series: [
        line('T-energy', 'Transmission against energy', 'Energy', 'eV', Es.map(e => e / EV), [{ label: a.rect ? 'Exact' : 'Transfer matrix', data: TE }, { label: 'WKB', data: TW, dash: true }, { label: 'Classical', data: Es.map(e => (e > V0 ? 1 : 0)), dash: true }], 'Transmission', '–'),
        line('T-width', 'Transmission against barrier width', 'Width', 'nm', Ls.map(l => l * 1e9), [{ label: a.rect ? 'Exact' : 'Transfer matrix', data: TL }, { label: 'WKB', data: TLw, dash: true }], 'Transmission', '–', { logy: true }),
        line('density', 'Probability density across the barrier', 'Position', 'nm', tm.xs.map(x => x * 1e9), [{ label: '|ψ|² relative to the incident wave', data: tm.dens }], '|ψ|²', '–', { note: 'Standing-wave ripple on the left comes from interference of incident and reflected waves; the barrier occupies 0 to L.' }),
      ],
      checks: [
        check('Probability current conserved', tm.T < 1e-12 ? tm.R - 1 : (tm.R + tm.T - 1), 1e-8, 'R + T = 1 from the transfer-matrix amplitudes'),
        check('Transmission within physical bounds', T < 0 || T > 1 + 1e-12 ? 1 : 0, 0, '0 ≤ T ≤ 1'),
        check('Transfer matrix reproduces the closed form', a.rect ? (tm.lnT - rc.lnT) / Math.max(1, Math.abs(rc.lnT)) : 0, 1e-8, 'Rectangular barrier'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const m = C.m_e, out = [], V0 = 10 * EV, E = 4 * EV, ka = Math.sqrt(2 * m * (V0 - E)) / hbar, L = 10 / ka;
    out.push(bench('Opaque-barrier limit at κL = 10', rectBarrier(E, V0, L, m).T, 16 * 0.4 * 0.6 * Math.exp(-20), 'T ≈ 16(E/V₀)(1 − E/V₀)e^(−2κL)', 1e-6));
    const kb = Math.sqrt(2 * m * 5 * EV) / hbar;
    out.push(bench('Perfect transmission at the first resonance', rectBarrier(15 * EV, V0, Math.PI / kb, m).T, 1, 'k_bL = π', 1e-12));
    out.push(bench('Energy equal to the barrier height', rectBarrier(V0, V0, 3e-10, m).T, 1 / (1 + m * V0 * 9e-20 / (2 * hbar * hbar)), 'T = [1 + mV₀L²/(2ħ²)]⁻¹', 1e-9));
    out.push(bench('Decay constant for a 4.5 eV barrier (per nm)', Math.sqrt(2 * m * 4.5 * EV) / hbar * 1e-9, 10.87, 'κ = 0.5123 Å⁻¹ × √(φ/eV): about a decade of current per ångström', 1e-3));
    const tm = transferMatrix(E, () => V0, 3e-10, m, 0, 60);
    out.push(bench('Transfer matrix against the closed form', tm.T, rectBarrier(E, V0, 3e-10, m).T, 'Rectangular barrier, 60 slices', 1e-9));
    const wb = Math.sqrt(8 * V0 / (m * 4e-18)), Ep = 9.5 * EV, par = transferMatrix(Ep, x => V0 * (1 - (2 * x / 2e-9 - 1) ** 2), 2e-9, m, 0, 2000);
    out.push(bench('Parabolic barrier near the top against Hill–Wheeler', par.T, 1 / (1 + Math.exp(2 * Math.PI * (V0 - Ep) / (hbar * wb))), 'Exact for an untruncated parabola; truncation at the base matters little near the top', 2e-2));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const below = v.E < v.V_0, yE = below ? 190 : 100, top = 130;
    const barrier = a.rect ? S.rect(260, top, 120, 280 - top, 'd-body', 0) : S.path(`M260 280 Q320 ${2 * top - 280} 380 280`, 'd-body');
    return svg(`
      ${S.line(60, 280, 580, 280, 'd-line')} ${barrier} ${S.text(320, top - 12, `V₀ = ${lab(v.V_0 / EV, 'eV')}`)}
      ${S.line(60, yE, 580, yE, 'd-dim')} ${S.text(70, yE - 8, `E = ${lab(v.E / EV, 'eV')}`, 'd-text', 'start')}
      ${S.path(`M70 ${yE + 40} q15 -30 30 0 t30 0 t30 0 t30 0 t30 0 t30 0`, 'd-pipe')}
      ${below ? S.path(`M260 ${yE + 24} Q300 ${yE + 44} 380 ${yE + 50}`, 'd-pipe') : S.path(`M260 ${yE + 40} q20 -24 40 0 t40 0 t40 0`, 'd-pipe')}
      ${S.path(`M380 ${yE + 50} q15 -10 30 0 t30 0 t30 0 t30 0 t30 0 t30 0`, 'd-liquid-line')}
      ${S.arrow(90, yE + 70, 170, yE + 70)} ${S.text(130, yE + 90, 'incident')} ${S.arrow(470, yE + 70, 550, yE + 70)} ${S.text(510, yE + 90, 'transmitted')}
      ${S.dim(260, 310, 380, 310, `L = ${lab(v.L * 1e9, 'nm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure tunnel current against gap width and bias and extract the decay constant and barrier height.',
    apparatus: ['Scanning tunnelling microscope with a metal tip over a clean conducting surface in ultra-high vacuum', 'Piezoelectric positioner calibrated against atomic steps', 'Alternatively a planar metal–oxide–metal junction with oxide thickness varied across a wafer'],
    instruments: [{ name: 'Transimpedance amplifier', measures: 'Tunnel current', range: '1 pA–100 nA', resolution: '≈ 10 fA/√Hz' }, { name: 'Piezo displacement (interferometer-calibrated)', measures: 'Change of gap', range: '0–1 nm', resolution: '≈ 1 pm' }, { name: 'Lock-in amplifier', measures: 'dI/dV and d ln I/dz', range: 'audio frequencies', resolution: '10⁻⁴ of signal' }],
    procedure: ['Stabilise the tip at a set current, open the feedback loop and ramp the gap while recording current.', 'Plot ln I against gap: the slope is −2κ.', 'Convert κ to an apparent barrier height and compare with the work functions of tip and sample.', 'For planar junctions, compare current density against oxide thickness measured by ellipsometry or electron microscopy.'],
    controls: ['Repeat at several biases well below the barrier height', 'Temperature sweep: tunnelling is nearly temperature-independent, unlike thermionic emission', 'Different tip and sample materials to vary the barrier'],
    signatures: ['ln I linear in gap width', 'About one decade of current per ångström for barriers of 4–5 eV', 'Weak temperature dependence'],
    safety: ['High-voltage piezo drivers', 'Ultra-high-vacuum and bake-out precautions', 'Cryogen handling for low-temperature instruments'],
  },
  falsify: ['A tunnel current that does not fall exponentially with barrier width at fixed bias well below the barrier.', 'A decay constant inconsistent with √(2mφ)/ħ for an independently measured barrier height and effective mass.', 'Reflection and transmission probabilities that do not sum to one in a loss-free barrier.'],
  alternatives: [{ name: 'Classical mechanics', text: 'No transmission below the barrier top and complete transmission above it; contradicted by experiment.' }, { name: 'Thermionic (over-barrier) emission', text: 'Dominates at high temperature and low barriers; distinguished by its strong temperature dependence.' }, { name: 'Fowler–Nordheim field emission', text: 'A strong field turns the barrier triangular and the current follows exp(−const/F).' }, { name: 'Image-force and band-structure corrections', text: 'Real barriers are rounded and lowered by the image potential, and the effective mass inside an insulator differs from the free value (Simmons 1963).' }],
  limits: 'One dimension, single non-relativistic particle of constant effective mass, elastic and coherent transport, no image-force rounding. The Hill–Wheeler formula is exact only for an untruncated parabola. Above about 5 % of the rest energy a relativistic equation is required.',
  numerics: { method: 'Closed-form matching for the rectangle; transfer matrix over slices of constant potential with rescaling against overflow for other shapes', order: 2, stability: 'Unconditionally stable; logarithms carried explicitly for opaque barriers' },
  optimise: { objective: 'T', sense: 'max', vars: ['L'], note: 'Transmission rises monotonically as the barrier thins when E < V₀.' },
  inverse: { series: 'T-width', curve: 0, fit: ['V_0', 'm_r'] },
  extensions: ['Double barrier and resonant tunnelling', 'Triangular barrier and Fowler–Nordheim emission', 'Tunnelling time and the Hartman effect', 'Gamow factor for alpha decay through a Coulomb barrier'],
};

// ================================================================== 13. quantum harmonic oscillator
/** Number of eigenvalues below x of the symmetric tridiagonal matrix (diag d, constant off-diagonal e): Sturm sequence. */
function sturmCount(d, e2, x) {
  let cnt = 0, q = d[0] - x; if (q < 0) cnt++;
  for (let i = 1; i < d.length; i++) { q = d[i] - x - e2 / (Math.abs(q) < 1e-300 ? 1e-300 : q); if (q < 0) cnt++; }
  return cnt;
}
/** k-th eigenvalue (0-based) of the tridiagonal matrix by bisection on the Sturm count. */
function tridiagEig(d, e2, k) {
  let lo = N.minOf(d) - 2 * Math.sqrt(e2), hi = N.maxOf(d) + 2 * Math.sqrt(e2);
  for (let i = 0; i < 80; i++) { const mid = 0.5 * (lo + hi); if (sturmCount(d, e2, mid) > k) hi = mid; else lo = mid; }
  return 0.5 * (lo + hi);
}
/** Finite-difference oscillator in units of ħω and x₀ = √(ħ/mω): H = −½ d²/dξ² + ½ξ² + λξ⁴. */
function oscillatorGrid(nGrid, lam) {
  const Lg = 10, h = 2 * Lg / (nGrid + 1), xi = Array.from({ length: nGrid }, (_, i) => -Lg + (i + 1) * h);
  const V = xi.map(x => 0.5 * x * x + lam * x ** 4), d = V.map(u => 1 / (h * h) + u), e = -1 / (2 * h * h);
  const level = k => tridiagEig(d, e * e, k);
  const vector = Ek => {
    // inverse iteration with the Thomas algorithm
    const sh = Ek + 1e-9 * (1 + Math.abs(Ek)), sub = new Array(nGrid).fill(e), dia = d.map(q => q - sh);
    let y = xi.map((x, i) => Math.exp(-0.5 * x * x) * (1 + 0.3 * Math.sin(1.7 * i)));
    for (let it = 0; it < 4; it++) { y = N.tridiag(sub, dia, sub, y); const nrm = Math.sqrt(N.sum(y.map(q => q * q)) * h); y = y.map(q => q / nrm); }
    const big = N.maxOf(y.map(Math.abs)); let j = nGrid - 1; while (j > 0 && Math.abs(y[j]) < 1e-3 * big) j--;
    return y[j] < 0 ? y.map(q => -q) : y;
  };
  return { xi, h, V, level, vector };
}
/** Normalised Hermite functions ψ_0..ψ_n at ξ by the stable three-term recurrence. */
function hermiteFn(n, x) {
  let p0 = Math.pow(Math.PI, -0.25) * Math.exp(-0.5 * x * x); if (n === 0) return p0;
  let p1 = Math.SQRT2 * x * p0;
  for (let k = 1; k < n; k++) { const p2 = Math.sqrt(2 / (k + 1)) * x * p1 - Math.sqrt(k / (k + 1)) * p0; p0 = p1; p1 = p2; }
  return p1;
}

const oscillator = {
  id: 'harmonic-oscillator-quantum',
  title: 'Quantum harmonic oscillator',
  module: [1, 2], klass: 'I', domains: ['quantum', 'waves'],
  keywords: ['quantum harmonic oscillator', 'harmonic oscillator', 'zero-point energy', 'zero point energy', 'energy levels', 'hermite', 'coherent state', 'ladder operators', 'molecular vibration', 'phonon', 'quantised oscillator', 'correspondence principle', 'anharmonic'],
  summary: 'Energy levels, wavefunctions, uncertainty products and coherent-state motion of a quantised oscillator, with eigenvalues computed numerically from the discretised Hamiltonian and compared with ħω(n + ½).',
  background: [
    'Any system near a stable equilibrium behaves as a harmonic oscillator, so its quantum version appears throughout physics: molecular vibrations, lattice phonons, modes of the electromagnetic field, trapped ions and superconducting resonators. The Schrödinger equation with a quadratic potential has equally spaced levels E_n = ħω(n + ½); the lowest has non-zero energy because position and momentum cannot both be sharp.',
    'A coherent state is a displaced ground state. Its probability density oscillates without changing shape, with centre following the classical trajectory exactly. For large quantum numbers the probability density of an energy eigenstate, averaged over its rapid oscillations, approaches the time a classical particle spends at each position.',
  ],
  phenomena: ['Quantised energy levels', 'Zero-point motion', 'Tunnelling beyond the classical turning points', 'Coherent states', 'Thermal occupation (Planck distribution)'],
  laws: ['schrodinger', 'uncertainty', 'born', 'energy'],
  refs: ['Schrödinger, E. (1926). Der stetige Übergang von der Mikro- zur Makromechanik. Naturwissenschaften 14, 664–666.', 'Planck, M. (1900). Zur Theorie des Gesetzes der Energieverteilung im Normalspectrum. Verh. Dtsch. Phys. Ges. 2, 237–245.', 'Glauber, R. J. (1963). Coherent and incoherent states of the radiation field. Phys. Rev. 131, 2766–2788.', 'Griffiths, D. J. & Schroeter, D. F. (2018). Introduction to Quantum Mechanics, 3rd ed., Cambridge University Press, §2.3.', 'Bender, C. M. & Wu, T. T. (1969). Anharmonic oscillator. Phys. Rev. 184, 1231–1260.', 'Leibfried, D., Blatt, R., Monroe, C. & Wineland, D. (2003). Quantum dynamics of single trapped ions. Rev. Mod. Phys. 75, 281–324.'],
  inputs: [
    inp('m', 'Oscillating mass', 'u', 1, { min: 5e-4, max: 500, kind: 'material', aliases: ['mass', 'reduced mass', 'atomic mass'], src: 'One atomic mass unit' }),
    inp('f', 'Oscillation frequency', 'THz', 50, { min: 1e-6, max: 1000, aliases: ['frequency', 'vibration frequency', 'trap frequency'], src: 'Typical molecular stretch, tens of terahertz' }),
    inp('n', 'Quantum number of the level examined', '1', 2, { min: 0, max: 12, aliases: ['quantum number', 'level', 'excited state'] }),
    inp('alpha_c', 'Coherent-state amplitude |α|', '1', 2, { min: 0, max: 5, aliases: ['coherent amplitude', 'displacement'] }),
    inp('lambda_4', 'Quartic anharmonicity in units of ħω', '1', 0.02, { min: 0, max: 0.2, kind: 'material', aliases: ['anharmonicity', 'quartic'], src: 'Illustrative; used only when the potential is not purely quadratic' }),
    inp('T', 'Temperature (used for thermal occupation)', 'K', 300, { min: 1, max: 1e4, kind: 'environment', env: 'air_temp', aliases: ['temperature'] }),
    inp('n_grid', 'Grid points of the discretised Hamiltonian', '1', 600, { min: 100, max: 2000, kind: 'numerical' }),
  ],
  assumptions: [
    asm('harmonic', 'The potential is exactly quadratic.', { why: 'Leading term near any minimum', alt: 'A quartic term λħω(x/x₀)⁴ is added; levels are no longer equally spaced and are found numerically and by first-order perturbation theory.' }),
    asm('one_d', 'The oscillator has one degree of freedom.', { why: 'Simplest case', alt: 'An isotropic three-dimensional oscillator: E = ħω(N + 3/2) with degeneracy (N+1)(N+2)/2.' }),
    asm('pure', 'The oscillator is in a single energy eigenstate.', { why: 'Isolated system', alt: 'The oscillator is in thermal equilibrium at temperature T, with Planck mean occupation.' }),
  ],
  symbols: { omega: ['Angular frequency', '1/s'], E_n: ['Energy of level n', 'J'], x_0: ['Oscillator length', 'm'], psi: ['Wavefunction (arbitrary normalisation)', '1'], x: ['Position', 'm'], dx: ['Position uncertainty', 'm'], dp: ['Momentum uncertainty', 'kg m/s'], n_bar: ['Mean thermal occupation', '1'], x_c: ['Centre of the coherent state', 'm'], t: ['Time', 's'] },
  equations: a => [
    eq('om', 'Angular frequency', 'omega', '2*pi*f', { kind: 'definition' }),
    a.harmonic
      ? eq('tise', 'Schrödinger equation', '-hbar^2/(2*m)*d2(psi,x) + m*omega^2*x^2/2*psi', 'E_n*psi', { kind: 'law', origin: 'Schrödinger (1926)', needs: ['harmonic'] })
      : eq('tise', 'Schrödinger equation with a quartic term', '-hbar^2/(2*m)*d2(psi,x) + m*omega^2*x^2/2*psi + lambda_4*hbar*omega*(x/x_0)^4*psi', 'E_n*psi', { kind: 'law', origin: 'Schrödinger (1926)' }),
    eq('x0', 'Oscillator length', 'x_0', 'sqrt(hbar/(m*omega))', { kind: 'definition' }),
    a.harmonic
      ? eq('En', 'Energy levels', 'E_n', a.one_d ? 'hbar*omega*(n + 1/2)' : 'hbar*omega*(n + 3/2)', { kind: 'derived', origin: 'Ladder-operator or series solution of the Schrödinger equation', needs: ['harmonic'] })
      : eq('En', 'Energy levels to first order in the quartic term', 'E_n', a.one_d ? 'hbar*omega*(n + 1/2 + 3*lambda_4/4*(2*n^2 + 2*n + 1))' : 'hbar*omega*(n + 3/2 + 3*lambda_4/4*(2*n^2 + 2*n + 3))', { kind: 'derived', origin: 'First-order perturbation theory' }),
    ...(a.harmonic ? [eq('unc', 'Uncertainty product of level n', 'dx*dp', 'hbar*(n + 1/2)', { kind: 'derived', origin: 'Expectation values in the energy eigenstate' })] : []),
    eq('coh', 'Centre of a coherent state', 'x_c', 'sqrt(2)*alpha_c*x_0*cos(omega*t)', { kind: 'derived', origin: 'Ehrenfest theorem; exact for a quadratic potential' }),
    ...(a.pure ? [] : [eq('nbar', 'Mean thermal occupation', 'n_bar', '1/(exp(hbar*omega/(k_B*T)) - 1)', { kind: 'law', origin: 'Planck distribution (Bose–Einstein statistics of oscillator quanta)' })]),
  ],
  derivation: a => [
    { text: 'Measure length in units of x₀ = √(ħ/mω) and energy in units of ħω. The Schrödinger equation becomes dimensionless.', tex: '-\\tfrac12\\,\\frac{\\mathrm{d}^2\\psi}{\\mathrm{d}\\xi^2} + \\tfrac12\\,\\xi^2\\,\\psi = \\varepsilon\\,\\psi' },
    { text: 'Writing the Hamiltonian with ladder operators shows that the spectrum is a ladder of equal steps bounded below.', tex: '\\hat H = \\hbar\\omega\\left(\\hat a^{\\dagger}\\hat a + \\tfrac12\\right)\\ \\Rightarrow\\ E_n = \\hbar\\omega\\left(n + \\tfrac12\\right)' },
    { text: 'The eigenfunctions are Hermite polynomials times a Gaussian; they extend beyond the classical turning points ξ = ±√(2n+1).', tex: '\\psi_n(\\xi) = \\frac{1}{\\sqrt{2^n n!\\sqrt\\pi}}\\,H_n(\\xi)\\,e^{-\\xi^2/2}' },
    { text: 'For the numerical solution the second derivative is replaced by a central difference on a uniform grid, giving a symmetric tridiagonal matrix whose lowest eigenvalues are found by Sturm-sequence bisection.', tex: 'H_{ii} = \\frac{1}{h^2} + V(\\xi_i),\\qquad H_{i,i\\pm1} = -\\frac{1}{2h^2}' },
    { text: 'A coherent state |α⟩ is a Gaussian of the ground-state width whose centre follows the classical motion.', tex: '|\\psi(\\xi,t)|^2 = \\frac{1}{\\sqrt\\pi}\\exp\\!\\left[-\\left(\\xi - \\sqrt2\\,|\\alpha|\\cos\\omega t\\right)^2\\right],\\qquad \\langle n\\rangle = |\\alpha|^2' },
    ...(a.harmonic ? [] : [{ text: 'A quartic term shifts each level by its expectation value in the unperturbed state.', tex: '\\Delta E_n = \\lambda\\hbar\\omega\\,\\langle n|\\xi^4|n\\rangle = \\tfrac34\\lambda\\hbar\\omega\\,(2n^2 + 2n + 1)' }]),
  ],
  solve(v, a) {
    const n = Math.round(N.clamp(v.n, 0, 12)), m = v.m, om = 2 * Math.PI * v.f, hw = hbar * om, x0 = Math.sqrt(hbar / (m * om));
    const lam = a.harmonic ? 0 : v.lambda_4, dim = a.one_d ? 1 : 3, nG = Math.round(N.clamp(v.n_grid, 100, 2000));
    const g = oscillatorGrid(nG, lam), ks = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], lev = ks.map(k => g.level(k));
    const e1 = n < 10 ? lev[n] : g.level(n), psi = g.vector(e1), psiNext = g.vector(n + 1 < 10 ? lev[n + 1] : g.level(n + 1));
    const zero = (dim - 1) * lev[0], eNum = e1 + zero;
    const pt = k => k + 0.5 + 0.75 * lam * (2 * k * k + 2 * k + 1);
    const eAn = a.harmonic ? n + dim / 2 : pt(n) + (dim - 1) * pt(0);
    // expectation values from the numerical eigenfunction
    const h = g.h, w = psi.map(q => q * q * h), x2 = N.sum(w.map((q, i) => q * g.xi[i] ** 2)), Vexp = N.sum(w.map((q, i) => q * g.V[i])), p2 = 2 * (e1 - Vexp);
    const xt = Math.sqrt(2 * n + 1), pOut = N.sum(w.filter((_, i) => Math.abs(g.xi[i]) > xt));
    const ortho = N.sum(psi.map((q, i) => q * psiNext[i])) * h, unc = Math.sqrt(Math.max(x2 * p2, 0));
    const xb = Math.min(hw / (kB * v.T), 700), nbar = Math.exp(-xb) / (1 - Math.exp(-xb));
    const al = v.alpha_c, warnings = [];
    if (!a.harmonic && al > 0) warnings.push('The coherent-state animation shows the purely harmonic motion; with a quartic term the packet would additionally spread and revive.');
    if (!a.one_d) warnings.push('The three-dimensional levels are sums of three one-dimensional levels; the numerical value shown is for the state (n, 0, 0).');
    const keep = g.xi.map((x, i) => i).filter(i => Math.abs(g.xi[i]) <= 7 && i % Math.max(1, Math.round(nG / 400)) === 0), xs = keep.map(i => g.xi[i]);
    const cls = xs.map(x => (Math.abs(x) < xt ? 1 / (Math.PI * Math.sqrt(xt * xt - x * x)) : NaN));
    const times = N.linspace(0, 1, 48), xa = N.linspace(-10, 10, 201);
    const frames = times.map(t => xa.map(x => Math.exp(-((x - Math.SQRT2 * al * Math.cos(2 * Math.PI * t)) ** 2)) / Math.sqrt(Math.PI)));
    return {
      scalars: [
        scalar('E_n', `Energy of level ${n}`, eAn * hw, 'J', { show: 'meV' }), scalar('E_num', 'Same, from the discretised Hamiltonian', eNum * hw, 'J', { show: 'meV' }),
        scalar('err_E', 'Relative difference, numerical against analytical', eNum / eAn - 1, '1'),
        scalar('E_0', 'Zero-point energy', (a.harmonic ? dim / 2 : dim * pt(0)) * hw, 'J', { show: 'meV' }), scalar('dE', 'Quantum of energy ħω', hw, 'J', { show: 'meV' }),
        scalar('omega', 'Angular frequency', om, '1/s'), scalar('lambda_ph', 'Wavelength of a photon of energy ħω', 2 * Math.PI * c / om, 'm', { show: 'um' }),
        scalar('x_0', 'Oscillator length √(ħ/mω)', x0, 'm', { show: 'pm' }), scalar('x_tp', 'Classical turning point of the level', xt * x0, 'm', { show: 'pm' }),
        scalar('dx', 'Position uncertainty of the level', Math.sqrt(x2) * x0, 'm', { show: 'pm' }), scalar('dp', 'Momentum uncertainty of the level', Math.sqrt(Math.max(p2, 0)) * hbar / x0, 'kg m/s'),
        scalar('unc', 'Uncertainty product Δx·Δp in units of ħ', unc, '1'),
        scalar('P_out', 'Probability of finding the particle beyond the classical turning points', pOut, '1'),
        scalar('g_n', 'Degeneracy of the level', a.one_d ? 1 : (n + 1) * (n + 2) / 2, '1'),
        scalar('N_coh', 'Mean excitation number of the coherent state', al * al, '1'), scalar('x_amp', 'Oscillation amplitude of the coherent state', Math.SQRT2 * al * x0, 'm', { show: 'pm' }),
        scalar('E_coh', 'Mean energy of the coherent state', (al * al + 0.5) * hw, 'J', { show: 'meV' }), scalar('T_osc', 'Oscillation period', 1 / v.f, 's', { show: 'fs' }),
        scalar('n_bar', 'Mean thermal occupation at temperature T', nbar, '1'), scalar('E_th', 'Mean thermal energy per mode', (nbar + 0.5) * hw * dim, 'J', { show: 'meV' }),
        scalar('C_v', 'Heat capacity per oscillator (Einstein)', dim * kB * xb * xb * Math.exp(-xb) / (1 - Math.exp(-xb)) ** 2, 'J/K'),
      ],
      series: [
        line('levels', 'Energy levels', 'Quantum number', '–', ks, [{ label: 'Discretised Hamiltonian', data: lev }, { label: a.harmonic ? 'ħω(n + ½)' : 'First-order perturbation theory', data: ks.map(pt), dash: true }, ...(a.harmonic ? [] : [{ label: 'Harmonic, n + ½', data: ks.map(k => k + 0.5), dash: true }])], 'Energy', 'ħω', { kind: 'scatter' }),
        line('wavefunction', `Wavefunction of level ${n}`, 'Position', 'x₀', xs, [{ label: 'Numerical eigenvector', data: keep.map(i => psi[i]) }, ...(a.harmonic ? [{ label: 'Hermite function', data: xs.map(x => hermiteFn(n, x)), dash: true }] : [])], 'ψ', 'x₀^(−½)'),
        line('density', 'Probability density against the classical distribution', 'Position', 'x₀', xs, [{ label: '|ψ|²', data: keep.map(i => psi[i] ** 2) }, { label: 'Classical, same energy', data: cls, dash: true }], 'Probability density', '1/x₀', { note: 'For large n the quantum density, averaged over its oscillations, follows the classical curve.' }),
      ],
      anims: [anim('coherent', 'Coherent state over one period', 'Position', 'x₀', xa, frames, times, '|ψ|²', '1/x₀', { yRange: [0, 0.6], fill: true })],
      checks: [
        check('Numerical eigenvalue against the analytical level', a.harmonic ? eNum / eAn - 1 : 0, 3e-3, 'Second-order finite differences'),
        check('Orthogonality of neighbouring eigenvectors', ortho, 1e-6, '⟨ψ_n|ψ_{n+1}⟩ = 0'),
        check('Virial theorem', a.harmonic ? Vexp / e1 - 0.5 : 0, 2e-3, '⟨V⟩ = E/2 for a quadratic potential'),
        check('Uncertainty principle', Math.max(0, 0.5 - unc - 1e-3), 0, 'Δx·Δp ≥ ħ/2 (within discretisation error)'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const g = oscillatorGrid(600, 0), n = Math.round(N.clamp(v.n, 0, 12)), out = [];
    out.push(bench('Ground-state energy of the discretised Hamiltonian (ħω)', g.level(0), 0.5, 'E₀ = ħω/2', 5e-4));
    out.push(bench(`Level ${n} of the discretised Hamiltonian (ħω)`, g.level(n), n + 0.5, 'E_n = ħω(n + ½)', 3e-3));
    const p0 = g.vector(g.level(0)), pOut = N.sum(p0.map((q, i) => (Math.abs(g.xi[i]) > 1 ? q * q * g.h : 0)));
    out.push(bench('Ground-state probability beyond the turning points', pOut, 0.157299, 'erfc(1) = 0.1573', 2e-2));
    const ga = oscillatorGrid(600, 0.01);
    out.push(bench('Quartic oscillator, λ = 0.01: ground state (ħω)', ga.level(0), 0.5 + 0.0075 - 21 / 8 * 1e-4 + 333 / 16 * 1e-6, 'Perturbation series ½ + ¾λ − (21/8)λ² + (333/16)λ³ (Bender & Wu 1969)', 5e-4));
    out.push(bench('Hermite function ψ₃ is normalised', simpson(x => hermiteFn(3, x) ** 2, -10, 10, 2000), 1, '∫ψ² dξ = 1', 1e-9));
    return out;
  },
  validation: [],
  diagram(v) {
    const n = Math.round(N.clamp(v.n, 0, 12)), Y = k => 300 - 22 * (k + 0.5), X = k => 60 * Math.sqrt(22 * (k + 0.5) / 22) * 1.15;
    return svg(`
      ${S.path('M90 40 Q320 560 550 40', 'd-line')} ${S.arrow(320, 310, 320, 30)} ${S.arrow(60, 300, 590, 300)} ${S.text(590, 320, 'x', 'd-text', 'end')} ${S.text(332, 40, 'E', 'd-text', 'start')}
      ${[0, 1, 2, 3, 4, 5, 6, 7].map(k => S.line(320 - X(k) - 20, Y(k), 320 + X(k) + 20, Y(k), k === n ? 'd-pipe' : 'd-dim')).join('')}
      ${[0, 1, 2, 3].map(k => S.text(560, Y(k) + 4, `n = ${k}`, 'd-text d-small', 'start')).join('')}
      ${S.path(`M240 ${Y(0) - 2} Q320 ${Y(0) - 26} 400 ${Y(0) - 2}`, 'd-liquid-line')}
      ${S.dim(150, Y(1), 150, Y(0), '')} ${S.text(140, Y(0) - 6, 'ħω', 'd-text', 'end')}
      ${S.text(110, 330, `ħω = ${lab(hbar * 2 * Math.PI * v.f / EV * 1000, 'meV')}`, 'd-text', 'start')} ${S.text(110, 350, `zero-point energy ħω/2`, 'd-text d-small', 'start')}
    `);
  },
  experiment: {
    objective: 'Resolve the level spacing and zero-point energy of a quantised oscillator.',
    apparatus: ['Single ion in a radio-frequency trap with resolved-sideband laser cooling, or', 'Gas cell of a diatomic molecule with an infrared spectrometer, or', 'Superconducting microwave resonator coupled to a qubit in a dilution refrigerator'],
    instruments: [{ name: 'Sideband spectroscopy laser', measures: 'Red and blue motional sideband strengths, giving the mean occupation', range: 'MHz detuning', resolution: 'kHz' }, { name: 'Fourier-transform infrared spectrometer', measures: 'Fundamental and overtone vibrational frequencies', range: '400–8000 cm⁻¹', resolution: '0.1 cm⁻¹' }, { name: 'Qubit-state-dependent readout', measures: 'Photon-number-resolved resonator spectrum', range: '4–8 GHz', resolution: 'below the dispersive shift' }],
    procedure: ['Cool the oscillator toward its ground state.', 'Drive transitions that add or remove one quantum and record their frequencies and strengths.', 'Verify equal spacing of the low-lying levels, and measure the asymmetry of red and blue sidebands, which vanishes for the red sideband in the ground state.', 'Prepare a displaced (coherent) state and follow its oscillation.'],
    controls: ['Thermometry from the sideband ratio', 'Overtone frequencies to quantify anharmonicity', 'Isotope substitution: frequency scales as (reduced mass)^(−½)'],
    signatures: ['Equally spaced absorption ladder for a harmonic potential; decreasing or increasing spacing with anharmonicity', 'Red sideband vanishing at n̄ → 0', 'Isotope shift of the zero-point energy visible in dissociation energies'],
    safety: ['Laser safety', 'Cryogen and high-vacuum handling', 'Toxic or corrosive sample gases where applicable'],
  },
  falsify: ['Low-lying levels of a demonstrably quadratic potential that are not equally spaced.', 'A ground state with Δx·Δp below ħ/2.', 'A coherent state in a harmonic potential whose density changes shape as it oscillates.'],
  alternatives: [{ name: 'Classical oscillator', text: 'Continuous energies and no zero-point motion; fails for heat capacities at low temperature and for spectra.' }, { name: 'Morse and other anharmonic potentials', text: 'Realistic molecular potentials have levels that converge toward a dissociation limit.' }, { name: 'Squeezed states', text: 'Minimum-uncertainty states with unequal position and momentum spreads, whose width oscillates at 2ω.' }],
  limits: 'Non-relativistic, isolated oscillator. The quartic option is perturbative in presentation but the numerical levels are valid for any λ in the declared range. The grid spans ±10 x₀, adequate for n ≤ 12. Second-order finite differences give eigenvalue errors of order (h²/32)(2n² + 2n + 1) ħω.',
  numerics: { method: 'Central-difference Hamiltonian on a uniform grid; eigenvalues by Sturm-sequence bisection; eigenvectors by inverse iteration with the Thomas algorithm', order: 2, stability: 'Bisection is unconditionally stable', resolution: 'n_grid' },
  inverse: { series: 'levels', curve: 0, fit: ['lambda_4'] },
  extensions: ['Morse potential and dissociation', 'Squeezed and cat states and their Wigner functions', 'Driven and damped oscillator (master equation)', 'Two coupled oscillators and normal-mode splitting'],
};

// ================================================================== 14. wave-packet spreading
/**
 * Crank–Nicolson solution of i ∂ψ/∂τ = −∂²ψ/∂ξ² + U(ξ)ψ on a uniform grid with ψ = 0 at the ends.
 * Lengths are in units of σ₀ and time in units of 2mσ₀²/ħ. Complex arithmetic is carried as separate real and imaginary arrays.
 */
function crankNicolson({ tEnd, wTau = 0, cat = false, nx = 601, nt = 400, frames = 40 }) {
  const sMax = Math.sqrt(1 + tEnd * tEnd), X = Math.max(12, 6 * sMax + (cat ? 4 : 0)), dx = 2 * X / (nx - 1), dt = tEnd / nt, r = dt / (2 * dx * dx);
  const x = N.linspace(-X, X, nx), U = x.map(q => (wTau / 2) ** 2 * q * q), g0 = q => Math.pow(2 * Math.PI, -0.25) * Math.exp(-q * q / 4);
  let re = Float64Array.from(x, q => (cat ? g0(q - 3) + g0(q + 3) : g0(q))), im = new Float64Array(nx);
  const nrm0 = Math.sqrt(re.reduce((s, q) => s + q * q, 0) * dx); re = re.map(q => q / nrm0); re[0] = re[nx - 1] = 0;
  // Thomas factorisation of (1 + i dt H/2): diagonal 1 + i(2r + dt U/2), off-diagonals −i r
  const cr = new Float64Array(nx), ci = new Float64Array(nx), ir = new Float64Array(nx), ii = new Float64Array(nx);
  for (let j = 1; j < nx - 1; j++) {
    // denominator = b_j − a·c'_{j−1}, with a = −i r
    const br = 1 - r * ci[j - 1], bi = 2 * r + dt * U[j] / 2 + r * cr[j - 1], den = br * br + bi * bi;
    ir[j] = br / den; ii[j] = -bi / den;
    cr[j] = r * ii[j]; ci[j] = -r * ir[j];          // c'_j = (−i r)/denominator
  }
  const stats = () => { let n0 = 0, m1 = 0, m2 = 0; for (let j = 0; j < nx; j++) { const p = re[j] * re[j] + im[j] * im[j]; n0 += p; m1 += p * x[j]; m2 += p * x[j] * x[j]; } m1 /= n0; return { norm: n0 * dx, sigma: Math.sqrt(Math.max(m2 / n0 - m1 * m1, 0)) }; };
  const dr = new Float64Array(nx), di = new Float64Array(nx), every = Math.max(1, Math.round(nt / frames));
  const times = [], dens = [], sig = [], norms = [];
  for (let k = 0; k <= nt; k++) {
    if (k % every === 0) { const s = stats(); times.push(k * dt); sig.push(s.sigma); norms.push(s.norm); dens.push(Array.from(re, (q, j) => q * q + im[j] * im[j])); }
    if (k === nt) break;
    // right-hand side (1 − i dt H/2)ψ, then forward elimination and back substitution
    for (let j = 1; j < nx - 1; j++) {
      const lr = re[j + 1] - 2 * re[j] + re[j - 1], li = im[j + 1] - 2 * im[j] + im[j - 1], u = dt * U[j] / 2;
      const rr = re[j] - r * li + u * im[j], ri = im[j] + r * lr - u * re[j];
      // d'_j = (d_j − a d'_{j−1})/denominator, a = −i r  ⇒  d_j + i r d'_{j−1}
      const tr = rr - r * di[j - 1], ti = ri + r * dr[j - 1];
      dr[j] = tr * ir[j] - ti * ii[j]; di[j] = tr * ii[j] + ti * ir[j];
    }
    for (let j = nx - 2; j >= 1; j--) { const nr = dr[j] - (cr[j] * re[j + 1] - ci[j] * im[j + 1]), ni = di[j] - (cr[j] * im[j + 1] + ci[j] * re[j + 1]); re[j] = nr; im[j] = ni; }
  }
  return { x, times, dens, sig, norms, dx, dt };
}
/** Analytic |ψ|² of a freely spreading Gaussian (or two of them, ±3σ₀ apart) at dimensionless time τ. */
function freeDensity(x, tau, cat) {
  const s2 = 1 + tau * tau, amp = Math.pow(2 * Math.PI, -0.25) * Math.pow(s2, -0.25), ph0 = -0.5 * Math.atan(tau);
  const g = q => { const mag = amp * Math.exp(-q * q / (4 * s2)), ph = ph0 + q * q * tau / (4 * s2); return [mag * Math.cos(ph), mag * Math.sin(ph)]; };
  if (!cat) return x.map(q => g(q)[0] ** 2 + g(q)[1] ** 2);
  const nrm = 2 * (1 + Math.exp(-36 / 8));
  return x.map(q => { const a1 = g(q - 3), a2 = g(q + 3); return ((a1[0] + a2[0]) ** 2 + (a1[1] + a2[1]) ** 2) / nrm; });
}

const wavePacket = {
  id: 'wave-packet-spreading',
  title: 'Spreading of a free quantum wave packet',
  module: [1, 2], klass: 'I', domains: ['quantum', 'waves'],
  keywords: ['wave packet', 'wavepacket', 'gaussian packet', 'spreading', 'dispersion of a wave packet', 'time-dependent schrödinger', 'time dependent schrodinger', 'crank-nicolson', 'free particle', 'group velocity', 'localised particle', 'position uncertainty grows'],
  summary: 'Evolution of a Gaussian wave packet: the analytic width σ(t), a Crank–Nicolson solution of the time-dependent Schrödinger equation, and the check that probability is conserved.',
  background: [
    'A particle localised to within σ₀ has, by the uncertainty principle, a spread of momenta of at least ħ/(2σ₀). Because the phase velocity of matter waves depends on momentum, the components drift apart and the packet broadens. For a free Gaussian the result is exact: the width grows as σ₀√(1 + (t/τ)²) with τ = 2mσ₀²/ħ, while the centre moves at the group velocity.',
    'The spreading time is a few femtoseconds for an electron localised to an atom and far longer than the age of the universe for a dust grain, which is part of the reason macroscopic bodies do not visibly delocalise. In a harmonic trap the width does not grow without limit but breathes at twice the trap frequency.',
  ],
  phenomena: ['Dispersion of matter waves', 'Group and phase velocity', 'Uncertainty principle', 'Unitary evolution', 'Interference of overlapping packets'],
  laws: ['schrodinger', 'uncertainty', 'born'],
  refs: ['Schrödinger, E. (1926). Quantisierung als Eigenwertproblem (Vierte Mitteilung). Annalen der Physik 81, 109–139.', 'Crank, J. & Nicolson, P. (1947). A practical method for numerical evaluation of solutions of partial differential equations of the heat-conduction type. Proc. Camb. Phil. Soc. 43, 50–67.', 'Goldberg, A., Schey, H. M. & Schwartz, J. L. (1967). Computer-generated motion pictures of one-dimensional quantum-mechanical transmission and reflection phenomena. Am. J. Phys. 35, 177–186.', 'Griffiths, D. J. & Schroeter, D. F. (2018). Introduction to Quantum Mechanics, 3rd ed., Cambridge University Press, §2.4.', 'Kennard, E. H. (1927). Zur Quantenmechanik einfacher Bewegungstypen. Zeitschrift für Physik 44, 326–352.'],
  inputs: [
    inp('m_r', 'Particle mass in electron masses', '1', 1, { min: 0.01, max: 1e6, kind: 'material', aliases: ['mass ratio', 'electron masses', 'mass'] }),
    inp('sigma_0', 'Initial position uncertainty', 'nm', 1, { min: 0.01, max: 1000, kind: 'geometry', aliases: ['initial width', 'width', 'localised to', 'position uncertainty'] }),
    inp('E_k', 'Mean kinetic energy', 'eV', 0.1, { min: 0, max: 10, aliases: ['kinetic energy', 'energy'] }),
    inp('t', 'Elapsed time', 'fs', 50, { min: 0.01, max: 1e6, aliases: ['time', 'after', 'elapsed'] }),
    inp('f_t', 'Trap frequency (used when the particle is not free)', 'THz', 10, { min: 1e-3, max: 1000, aliases: ['trap frequency'] }),
  ],
  assumptions: [
    asm('free', 'No force acts on the particle.', { why: 'Isolates dispersion', alt: 'The particle sits in a harmonic trap of frequency f_t: the width oscillates instead of growing without limit.' }),
    asm('gaussian', 'The initial state is a single minimum-uncertainty Gaussian.', { why: 'Closed-form evolution', alt: 'The initial state is a superposition of two such Gaussians 6σ₀ apart, which interfere once they overlap.' }),
    asm('massive', 'The particle is massive and non-relativistic: ω(k) = ħk²/2m.', { why: 'Schrödinger dynamics', alt: 'Linear dispersion ω = ck, as for light in vacuum: every component travels at the same speed and the packet keeps its shape.' }),
  ],
  symbols: { psi: ['Wavefunction', '1'], x: ['Position', 'm'], sigma_t: ['Position uncertainty at time t', 'm'], tau_s: ['Spreading time', 's'], v_g: ['Group velocity', 'm/s'], k_0: ['Mean wavenumber', '1/m'], dp: ['Momentum uncertainty', 'kg m/s'], omega_t: ['Trap angular frequency', '1/s'], omega_k: ['Angular frequency of a plane-wave component', '1/s'], k: ['Wavenumber', '1/m'], m_p0: ['Particle mass', 'kg'] },
  equations: a => [
    ...(a.massive ? [
      a.free ? eq('tdse', 'Time-dependent Schrödinger equation', 'hbar*pd(psi,t)', 'hbar^2/(2*m_r*m_e)*pd2(psi,x)', { kind: 'law', origin: 'Schrödinger (1926); the factor i is omitted in this real-valued notation', note: 'iħ ∂ψ/∂t = −(ħ²/2m) ∂²ψ/∂x²' })
        : eq('tdse', 'Time-dependent Schrödinger equation in a trap', 'hbar*pd(psi,t)', 'hbar^2/(2*m_r*m_e)*pd2(psi,x) - m_r*m_e*omega_t^2*x^2/2*psi', { kind: 'law', origin: 'Schrödinger (1926); the factor i is omitted in this real-valued notation' }),
      eq('disp', 'Dispersion relation', 'omega_k', 'hbar*k^2/(2*m_r*m_e)', { kind: 'derived', origin: 'Plane-wave solution of the Schrödinger equation' }),
      eq('taus', 'Spreading time', 'tau_s', '2*m_r*m_e*sigma_0^2/hbar', { kind: 'definition' }),
      a.free ? eq('sig', 'Width of the packet', 'sigma_t', 'sigma_0*sqrt(1 + (t/tau_s)^2)', { kind: 'derived', origin: 'Exact Gaussian solution (Kennard 1927)', needs: ['free', 'gaussian'] })
        : eq('sig', 'Width of the packet in a trap', 'sigma_t', 'sigma_0*sqrt(cos(omega_t*t)^2 + sin(omega_t*t)^2/(omega_t*tau_s)^2)', { kind: 'derived', origin: 'Exact Gaussian solution in a harmonic potential' }),
      eq('vg', 'Group velocity', 'v_g', 'hbar*k_0/(m_r*m_e)', { kind: 'derived', origin: 'dω/dk at the mean wavenumber' }),
    ] : [
      eq('disp', 'Dispersion relation', 'omega_k', 'c*k', { kind: 'law', origin: 'Wave equation for light in vacuum' }),
      eq('sig', 'Width of the packet', 'sigma_t', 'sigma_0', { kind: 'derived', origin: 'Non-dispersive propagation' }),
      eq('vg', 'Group velocity', 'v_g', 'c', { kind: 'derived', origin: 'dω/dk' }),
    ]),
    eq('dp', 'Momentum uncertainty', 'dp', 'hbar/(2*sigma_0)', { kind: 'law', origin: 'Minimum-uncertainty Gaussian' }),
  ],
  derivation: a => [
    { text: 'Write the initial Gaussian as a superposition of plane waves. Its momentum distribution is also Gaussian, with the minimum spread allowed.', tex: '\\psi(x,0) = (2\\pi\\sigma_0^2)^{-1/4}\\,e^{-x^2/4\\sigma_0^2}\\,e^{ik_0x},\\qquad \\Delta p = \\frac{\\hbar}{2\\sigma_0}' },
    { text: 'Each plane wave evolves with phase exp(−iħk²t/2m). Carrying out the Gaussian integral gives the packet at later times.', tex: '|\\psi(x,t)|^2 = \\frac{1}{\\sqrt{2\\pi}\\,\\sigma(t)}\\exp\\!\\left[-\\frac{(x - v_g t)^2}{2\\sigma(t)^2}\\right]' },
    { text: 'The width combines the initial spread with the drift of components of different momentum.', tex: '\\sigma(t) = \\sigma_0\\sqrt{1 + \\left(\\frac{\\hbar t}{2m\\sigma_0^2}\\right)^2},\\qquad \\tau_s = \\frac{2m\\sigma_0^2}{\\hbar}' },
    { text: 'For the numerical solution the equation is advanced with the Crank–Nicolson scheme, the Cayley form of the evolution operator, which is unitary and therefore conserves the norm exactly.', tex: '\\left(1 + \\tfrac{i\\,\\Delta t}{2\\hbar}\\hat H\\right)\\psi^{n+1} = \\left(1 - \\tfrac{i\\,\\Delta t}{2\\hbar}\\hat H\\right)\\psi^{n}' },
    { text: 'The simulation is carried out in the frame moving with the packet (and, in a trap, following the classical trajectory of its centre). The shape of the packet evolves identically in that frame, so the centre is restored afterwards from classical mechanics.', tex: '\\langle x\\rangle(t) = v_g\\,t' },
  ],
  solve(v, a) {
    const m = v.m_r * C.m_e, s0 = v.sigma_0, tauS = 2 * m * s0 * s0 / hbar, warnings = [];
    const p0 = Math.sqrt(2 * m * v.E_k), vg = a.massive ? p0 / m : c, om = 2 * Math.PI * v.f_t, wTau = a.free ? 0 : om * tauS;
    const sigAn = t => (!a.massive ? s0 : a.free ? s0 * Math.sqrt(1 + (t / tauS) ** 2) : s0 * Math.sqrt(Math.cos(om * t) ** 2 + (Math.sin(om * t) / wTau) ** 2));
    const tNum = Math.min(v.t, 4 * tauS), tp = tNum / tauS;
    if (v.t > 4 * tauS && a.massive) warnings.push('The numerical run covers the first four spreading times; beyond that the analytical width is reported and the grid would have to grow with the packet.');
    if (vg > 0.1 * c && a.massive) warnings.push('The group velocity exceeds a tenth of the speed of light; the non-relativistic equation is then only approximate.');
    if (!a.massive) warnings.push('With linear dispersion there is nothing to integrate: the packet translates rigidly at c.');
    let sim, sigNum, normErr, densAn = null, sigRef;
    if (a.massive) {
      sim = crankNicolson({ tEnd: Math.max(tp, 1e-9), wTau, cat: !a.gaussian });
      sigNum = sim.sig.at(-1) * s0; normErr = N.maxOf(sim.norms.map(q => Math.abs(q - 1)));
      if (a.free) { densAn = freeDensity(sim.x, tp, !a.gaussian); const nn = N.sum(densAn), m2 = N.sum(densAn.map((q, i) => q * sim.x[i] ** 2)); sigRef = Math.sqrt(m2 / nn) * s0; }
      else if (a.gaussian) { const s = sigAn(tNum) / s0; densAn = sim.x.map(q => Math.exp(-q * q / (2 * s * s)) / (Math.sqrt(2 * Math.PI) * s)); sigRef = s * s0; }
      else sigRef = NaN;
    } else {
      const x = N.linspace(-12, 12, 601), d0 = x.map(q => Math.exp(-q * q / 2) / Math.sqrt(2 * Math.PI)), times = N.linspace(0, tp, 41);
      sim = { x, times, dens: times.map(() => d0), sig: times.map(() => 1), norms: times.map(() => 1) }; sigNum = s0; normErr = 0; densAn = d0; sigRef = s0;
    }
    const sigT = a.gaussian ? sigAn(v.t) : (a.free && a.massive ? s0 * Math.sqrt(9 + 1 + (v.t / tauS) ** 2) : NaN);
    const xc = a.massive && !a.free ? vg / om * Math.sin(om * v.t) : vg * v.t;
    const tAx = sim.times.map(q => q * tauS * 1e15), sAn = sim.times.map(q => { const t = q * tauS; return a.gaussian ? sigAn(t) / s0 : (a.free ? Math.sqrt(10 + q * q) : NaN); });
    const xnm = sim.x.map(q => q * s0 * 1e9), dp = hbar / (2 * s0);
    return {
      scalars: [
        scalar('sigma_t', 'Position uncertainty at the elapsed time', sigT, 'm', { show: 'nm', text: Number.isFinite(sigT) ? undefined : 'No closed form for two packets in a trap; see the numerical value' }),
        scalar('spread', 'Growth factor σ(t)/σ₀', sigT / (a.gaussian ? s0 : s0 * Math.sqrt(10)), '1', { text: Number.isFinite(sigT) ? undefined : 'Not available in closed form' }),
        scalar('tau_s', 'Spreading time 2mσ₀²/ħ', tauS, 's', { show: 'fs' }),
        scalar('t_num', 'Duration covered by the numerical run', tNum, 's', { show: 'fs' }),
        scalar('sigma_num', 'Width from the Crank–Nicolson solution at that time', sigNum, 'm', { show: 'nm' }),
        scalar('sigma_ref', 'Analytical width at that time', sigRef, 'm', { show: 'nm', text: Number.isFinite(sigRef) ? undefined : 'Not available in closed form' }),
        scalar('err_sigma', 'Relative difference, numerical against analytical', Number.isFinite(sigRef) ? sigNum / sigRef - 1 : 0, '1'),
        scalar('norm_err', 'Largest departure of the norm from one', normErr, '1'),
        scalar('v_g', 'Group velocity', vg, 'm/s'), scalar('v_ph', 'Phase velocity', a.massive ? vg / 2 : c, 'm/s'),
        scalar('x_c', 'Displacement of the packet centre', xc, 'm', { show: 'nm' }),
        scalar('v_sp', 'Asymptotic spreading speed ħ/(2mσ₀)', a.massive ? hbar / (2 * m * s0) : 0, 'm/s'),
        scalar('dp', 'Momentum uncertainty', dp, 'kg m/s'), scalar('unc', 'Uncertainty product σ(t)·Δp in units of ħ', (Number.isFinite(sigT) ? sigT : sigNum) * dp / hbar, '1'),
        scalar('lambda_dB', 'Mean de Broglie wavelength', p0 > 0 ? 2 * Math.PI * hbar / p0 : Infinity, 'm', { show: 'nm', text: p0 > 0 ? undefined : 'Infinite: the packet is at rest' }),
      ],
      series: [
        line('sigma-t', 'Width against time', 'Time', 'fs', tAx, [{ label: 'Crank–Nicolson', data: sim.sig }, ...(sAn.some(Number.isFinite) ? [{ label: 'Analytical', data: sAn, dash: true }] : [])], 'Width', 'σ₀'),
        line('density', 'Probability density at the end of the run', 'Position relative to the classical centre', 'nm', xnm, [{ label: 'Crank–Nicolson', data: sim.dens.at(-1) }, ...(densAn ? [{ label: 'Analytical', data: densAn, dash: true }] : []), { label: 'Initial', data: sim.dens[0], dash: true }], 'Probability density', '1/σ₀'),
        line('norm', 'Norm of the numerical wavefunction', 'Time', 'fs', tAx, [{ label: '∫|ψ|² dx', data: sim.norms }], 'Norm', '–'),
      ],
      anims: [anim('packet', 'Evolution of the probability density', 'Position relative to the classical centre', 'nm', xnm, sim.dens, sim.times.map(q => q * tauS), 'Probability density', '1/σ₀', { fill: true })],
      checks: [
        check('Norm conserved', normErr, 1e-8, 'Crank–Nicolson is unitary'),
        check('Numerical width against the analytical result', Number.isFinite(sigRef) ? sigNum / sigRef - 1 : 0, 1e-2, 'Second-order accurate in space and time'),
        check('Uncertainty principle', Math.max(0, 0.5 - sigNum * dp / hbar - 1e-3), 0, 'σ·Δp ≥ ħ/2'),
      ],
      warnings,
    };
  },
  benchmarks() {
    const out = [], s1 = crankNicolson({ tEnd: 1 });
    out.push(bench('Width after one spreading time', s1.sig.at(-1), Math.SQRT2, 'σ(τ_s) = √2 σ₀', 2e-3));
    out.push(bench('Norm after one spreading time', s1.norms.at(-1), 1, 'Unitary evolution', 1e-10));
    const s2 = crankNicolson({ tEnd: 3 });
    out.push(bench('Width after three spreading times', s2.sig.at(-1), Math.sqrt(10), 'σ = σ₀√(1 + 9)', 3e-3));
    const s3 = crankNicolson({ tEnd: 2.3, wTau: 1 });
    out.push(bench('Ground state of a matched trap keeps its width', s3.sig.at(-1), 1, 'ω_tτ_s = 1 makes the Gaussian the trap ground state', 2e-3));
    const s4 = crankNicolson({ tEnd: 2, cat: true }), d = freeDensity(s4.x, 2, true), l2 = Math.sqrt(N.sum(d.map((q, i) => (q - s4.dens.at(-1)[i]) ** 2)) / N.sum(d.map(q => q * q)));
    out.push(bench('Two interfering packets: numerical against analytical density', 1 + l2, 1, 'Relative L² difference of |ψ|²', 2e-2));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.arrow(50, 280, 600, 280)} ${S.text(600, 300, 'x', 'd-text', 'end')}
      ${S.path('M90 280 Q120 280 135 180 Q150 60 165 180 Q180 280 210 280', 'd-pipe')} ${S.text(150, 50, 't = 0')}
      ${S.path('M300 280 Q370 278 410 200 Q440 140 470 200 Q510 278 580 280', 'd-liquid-line')} ${S.text(440, 124, `t = ${lab(v.t * 1e15, 'fs')}`)}
      ${S.dim(120, 310, 180, 310, '2σ₀')} ${S.dim(370, 310, 510, 310, '2σ(t)')}
      ${S.arrow(210, 170, 330, 170)} ${S.text(270, 160, a.massive ? 'group velocity ħk₀/m' : 'speed c')}
      ${S.text(320, 345, a.massive ? (a.free ? 'σ(t) = σ₀ √(1 + (t/τ_s)²),   τ_s = 2mσ₀²/ħ' : 'width breathes at twice the trap frequency') : 'no dispersion: shape preserved', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Observe the ballistic broadening of a matter wave packet released from confinement and compare with σ₀√(1 + (t/τ)²).',
    apparatus: ['Ultracold atoms held in a tight optical or magnetic trap that can be switched off abruptly', 'Resonant imaging beam and camera for absorption imaging after a variable time of flight', 'Alternatively an ultrafast electron pulse and streak camera'],
    instruments: [{ name: 'Absorption imaging on a CCD or CMOS camera', measures: 'Density profile after time of flight', range: '1–50 ms', resolution: '≈ 2 µm' }, { name: 'Trap-frequency measurement by parametric heating', measures: 'Initial confinement, hence σ₀', range: 'Hz–kHz', resolution: '≈ 1 %' }, { name: 'Streak camera or THz streaking', measures: 'Duration of an electron pulse', range: 'fs–ps', resolution: '≈ 10 fs' }],
    procedure: ['Prepare atoms near the ground state of the trap so that the initial state is close to a minimum-uncertainty Gaussian.', 'Switch the trap off within a time short compared with its period.', 'Image the cloud after a series of expansion times and fit Gaussian widths.', 'Plot σ² against t² and compare the slope with (ħ/2mσ₀)².'],
    controls: ['Reduce the atom number to make interaction-driven expansion negligible', 'Compare a thermal cloud, whose expansion measures temperature instead', 'Vary the trap frequency to change σ₀'],
    signatures: ['σ² linear in t² with slope fixed by the initial confinement', 'Tighter initial confinement giving faster expansion'],
    safety: ['Laser safety', 'High-current magnetic coils and vacuum hazards'],
  },
  falsify: ['An expansion rate of a non-interacting ground-state packet different from ħ/(2mσ₀).', 'A measured width smaller than the uncertainty limit ħ/(2Δp).', 'Loss of total probability in a closed system.'],
  alternatives: [{ name: 'Classical ensemble', text: 'A cloud of classical particles with the same position and momentum spreads follows the same σ(t), so spreading alone does not prove coherence; interference of two packets does.' }, { name: 'Interacting gas', text: 'In a Bose–Einstein condensate the mean-field energy drives a faster, self-similar expansion described by the Gross–Pitaevskii equation.' }, { name: 'Relativistic packets', text: 'The Klein–Gordon or Dirac equation bounds the spreading speed by c.' }],
  limits: 'One dimension, single non-relativistic particle, no interactions or decoherence. The numerical run is limited to four spreading times on a fixed grid of 601 points with reflecting ends placed well outside the packet.',
  numerics: { method: 'Crank–Nicolson (Cayley) scheme with a complex tridiagonal Thomas solve carried in real and imaginary arrays; co-moving frame', order: 2, stability: 'Unconditionally stable and exactly norm-conserving' },
  inverse: { series: 'sigma-t', curve: 0, fit: ['sigma_0', 'm_r'] },
  extensions: ['Scattering of the packet from a barrier or step', 'Split-operator Fourier method for higher accuracy', 'Wigner-function view of the shearing phase-space distribution', 'Gross–Pitaevskii equation for an interacting condensate'],
};

export default [twin, rocket, elevator, schwarzschild, gps, blackHole, cosmology, wormholeModel, modGravity, constants, yukawa, tunnelling, oscillator, wavePacket];
