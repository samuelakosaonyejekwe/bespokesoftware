// Thermodynamics and heat transfer, process and desalination engineering, computational fluid dynamics
// and nuclear engineering.
import { inp, asm, eq, scalar, line, field, anim, check, bench, svg, S, lab, N, C, R } from './kit.js';

const g = 9.80665;
const val = (r, s) => r.scalars.find(q => q.sym === s).value;
/** The environment connector reports salinity in g/kg; inputs declared in g/kg arrive as a mass fraction. Accept either. */
const massFrac = s => (s > 1 ? s / 1000 : s);
const erfc = x => 1 - erfFn(x);
/** Error function, Abramowitz & Stegun 7.1.26 (absolute error below 1.5e-7). */
function erfFn(x) {
  const s = Math.sign(x), z = Math.abs(x), t = 1 / (1 + 0.3275911 * z);
  return s * (1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-z * z));
}

// ------------------------------------------------------------------ transient conduction in a slab
/** Fourier-series solution for a wall heated at ξ = 0 with an adiabatic plane at ξ = 1. Returns (T − T_inf)/(T_i − T_inf). */
function slabRoots(Bi, terms = 40) {
  const z = [];
  for (let n = 1; n <= terms; n++) z.push(Number.isFinite(Bi) ? N.bisect(q => q * Math.sin(q) - Bi * Math.cos(q), (n - 1) * Math.PI + 1e-12, (n - 0.5) * Math.PI - 1e-12, 1e-13) : (n - 0.5) * Math.PI);
  return z;
}
function slabSeries(Bi, Fo, xi, roots = slabRoots(Bi)) {
  let s = 0;
  for (const z of roots) {
    if (z * z * Fo > 45) break;
    s += 4 * Math.sin(z) / (2 * z + Math.sin(2 * z)) * Math.exp(-z * z * Fo) * Math.cos(z * (1 - xi));
  }
  return s;
}

const conduction = {
  id: 'transient-conduction-1d',
  title: 'Transient heat conduction in a slab',
  module: 2, klass: 'I', domains: ['thermal'],
  keywords: ['transient conduction', 'heat conduction', 'slab', 'plane wall', 'biot number', 'fourier number', 'heisler', 'quenching', 'thermal diffusivity', 'heating time', 'cool-down', 'unsteady conduction', 'heat equation', 'conduction'],
  summary: 'Temperature history through a slab whose surface is suddenly exposed to a fluid or held at a fixed temperature, solved with the one-dimensional heat equation.',
  background: [
    'When the surface of a solid is suddenly exposed to a different temperature, heat diffuses inward at a rate set by the thermal diffusivity α = k/(ρ c_p). Two dimensionless groups organise the problem: the Fourier number α t/L², which measures elapsed time against the diffusion time, and the Biot number h L/k, which compares the resistance of the solid with that of the surface film.',
    'For a wall with one adiabatic face and constant properties the exact solution is an infinite series in cosines whose eigenvalues satisfy ζ tan ζ = Bi. The first term dominates once the Fourier number exceeds about 0.2, which is the basis of the Heisler charts. At very small Biot number the solid is nearly isothermal and the lumped-capacitance model applies.',
  ],
  phenomena: ['Heat diffusion', 'Surface convection', 'Thermal penetration', 'Approach to steady state'],
  laws: ['energy', 'fourier'],
  refs: ['Carslaw, H. S. & Jaeger, J. C. (1959). Conduction of Heat in Solids, 2nd ed., Oxford University Press.', 'Incropera, F. P., DeWitt, D. P., Bergman, T. L. & Lavine, A. S. (2007). Fundamentals of Heat and Mass Transfer, 6th ed., Wiley.', 'Heisler, M. P. (1947). Temperature charts for induction and constant-temperature heating. Trans. ASME 69, 227–236.', 'Crank, J. & Nicolson, P. (1947). A practical method for numerical evaluation of solutions of partial differential equations of the heat-conduction type. Proc. Cambridge Phil. Soc. 43, 50–67.'],
  inputs: [
    inp('L', 'Slab thickness (heated face to back face)', 'mm', 50, { min: 1, max: 1000, kind: 'geometry', aliases: ['thickness', 'thick', 'slab', 'wall'] }),
    inp('k', 'Thermal conductivity', 'W/(m K)', 16, { min: 0.05, max: 400, kind: 'fluid', aliases: ['conductivity'], src: 'Austenitic stainless steel near 100 °C' }),
    inp('rho', 'Density', 'kg/m^3', 7900, { min: 100, max: 20000, kind: 'fluid', aliases: ['density'] }),
    inp('cp', 'Specific heat capacity', 'J/(kg K)', 500, { min: 100, max: 5000, kind: 'fluid', aliases: ['specific heat', 'heat capacity'] }),
    inp('T_i', 'Initial temperature', '°C', 20, { min: -200, max: 1500, aliases: ['initial temperature', 'initially'] }),
    inp('T_inf', 'Fluid (or imposed surface) temperature', '°C', 200, { min: -200, max: 1500, aliases: ['fluid temperature', 'surface temperature', 'ambient temperature', 'furnace'] }),
    inp('h', 'Surface heat-transfer coefficient', 'W/(m^2 K)', 500, { min: 1, max: 20000, aliases: ['heat transfer coefficient', 'film coefficient', 'convection coefficient'] }),
    inp('q_gen', 'Volumetric heat generation (used when the source is switched on)', 'kW/m^3', 200, { min: 0, max: 1e5, aliases: ['heat generation', 'source'] }),
    inp('t_end', 'Elapsed time', 's', 600, { min: 1, max: 1e6, aliases: ['time', 'after', 'duration'] }),
    inp('n_x', 'Number of grid points', '1', 81, { min: 21, max: 401, kind: 'numerical' }),
  ],
  assumptions: [
    asm('convective', 'The heated face exchanges heat with a fluid through a constant film coefficient.', { why: 'Usual engineering boundary condition', alt: 'The heated face is held at the imposed temperature (infinite Biot number).' }),
    asm('insulated', 'The back face is adiabatic (or is a plane of symmetry).', { why: 'Half of a wall heated on both sides, or an insulated backing', alt: 'The back face is held at the initial temperature.' }),
    asm('no_source', 'There is no internal heat generation.', { why: 'Passive solid', alt: 'A uniform volumetric source q_gen is added to the heat equation.' }),
    asm('const_props', 'Conductivity, density and specific heat are constant.', { why: 'Moderate temperature range', alt: 'Not resolved here: a warning is issued and the temperature swing is reported so the user can judge the error.' }),
  ],
  symbols: { T: ['Temperature', 'K'], t: ['Time', 's'], x: ['Distance from the heated face', 'm'], alpha: ['Thermal diffusivity', 'm^2/s'], Bi: ['Biot number', '1'], Fo: ['Fourier number', '1'], tau_d: ['Diffusion time', 's'], q_s: ['Surface heat flux', 'W/m^2'] },
  equations: a => [
    eq('heat', 'Heat equation', 'rho*cp*pd(T,t)', a.no_source ? 'k*pd2(T,x)' : 'k*pd2(T,x) + q_gen', { kind: 'law', origin: 'First law of thermodynamics with Fourier’s law', needs: ['const_props'] }),
    a.convective
      ? eq('bc0', 'Heated-face condition', '-k*pd(T,x)', 'h*(T_inf - T)', { kind: 'boundary', origin: 'Newton’s law of cooling at x = 0', needs: ['convective'] })
      : eq('bc0', 'Heated-face condition', 'T', 'T_inf', { kind: 'boundary', origin: 'Imposed temperature at x = 0', exportable: false, note: 'Holds only on the heated face x = 0, not throughout the slab.' }),
    a.insulated
      ? eq('bcL', 'Back-face condition', 'k*pd(T,x)', '0*q_s', { kind: 'boundary', origin: 'Adiabatic surface at x = L', needs: ['insulated'] })
      : eq('bcL', 'Back-face condition', 'T', 'T_i', { kind: 'boundary', origin: 'Imposed temperature at x = L', exportable: false, note: 'Holds only on the back face x = L, not throughout the slab.' }),
    eq('alpha', 'Thermal diffusivity', 'alpha', 'k/(rho*cp)', { kind: 'definition' }),
    eq('bi', 'Biot number', 'Bi', 'h*L/k', { kind: 'definition' }),
    eq('fo', 'Fourier number', 'Fo', 'alpha*t_end/L^2', { kind: 'definition' }),
    eq('qs', 'Surface heat flux', 'q_s', a.convective ? 'h*(T_inf - T)' : '-k*pd(T,x)', { kind: 'law', origin: a.convective ? 'Newton’s law of cooling' : 'Fourier’s law', exportable: false, note: 'Evaluated with the temperature (or its gradient) on the heated face, which comes from the solution of the heat equation.' }),
  ],
  derivation: a => [
    { text: 'Apply the first law to a slice of thickness dx: the rate of energy storage equals the net conduction into the slice' + (a.no_source ? '.' : ' plus the heat generated within it.'), tex: '\\rho c_p\\,\\frac{\\partial T}{\\partial t}\\,\\mathrm{d}x = q(x) - q(x+\\mathrm{d}x)' + (a.no_source ? '' : ' + \\dot q\\,\\mathrm{d}x') },
    { text: 'Fourier’s law relates the flux to the temperature gradient, giving the heat equation.', tex: '\\frac{\\partial T}{\\partial t} = \\alpha\\,\\frac{\\partial^2 T}{\\partial x^2}' + (a.no_source ? '' : ' + \\frac{\\dot q}{\\rho c_p}') + ',\\qquad \\alpha = \\frac{k}{\\rho c_p}' },
    { text: 'Scaling distance by L and time by L²/α leaves two parameters, the Fourier and Biot numbers.', tex: '\\mathrm{Fo} = \\frac{\\alpha t}{L^2},\\qquad \\mathrm{Bi} = \\frac{hL}{k}' },
    { text: 'Separation of variables for an adiabatic back face gives a cosine series; ξ = x/L is measured from the heated face.', tex: '\\frac{T-T_\\infty}{T_i-T_\\infty} = \\sum_{n=1}^{\\infty}\\frac{4\\sin\\zeta_n}{2\\zeta_n+\\sin 2\\zeta_n}\\,e^{-\\zeta_n^2\\mathrm{Fo}}\\cos\\big(\\zeta_n(1-\\xi)\\big),\\qquad \\zeta_n\\tan\\zeta_n = \\mathrm{Bi}' },
    { text: 'At early times the wall behaves as a semi-infinite solid; for an imposed surface temperature the profile is a complementary error function.', tex: '\\frac{T-T_i}{T_\\infty-T_i} = \\operatorname{erfc}\\!\\left(\\frac{x}{2\\sqrt{\\alpha t}}\\right)' },
  ],
  solve(v, a) {
    const nx = Math.max(11, Math.round(v.n_x)), L = v.L, dx = L / (nx - 1), alpha = v.k / (v.rho * v.cp);
    const Bi = v.h * L / v.k, Fo = alpha * v.t_end / (L * L), tauD = L * L / alpha;
    // beyond roughly eight relaxation times the profile is steady; do not waste steps integrating a steady state
    const tauEq = tauD * (0.5 + (a.convective ? 1 / Bi : 0)), tSim = Math.min(v.t_end, 8 * tauEq);
    const src = a.no_source ? 0 : v.q_gen / (v.rho * v.cp), source = src ? () => src : undefined;
    const right = a.insulated ? { type: 'neumann', value: 0 } : { type: 'dirichlet', value: v.T_i };
    const x = N.linspace(0, L, nx), w = x.map((_, i) => (i === 0 || i === nx - 1 ? 0.5 : 1) * dx);
    const meanOf = arr => arr.reduce((s, q, i) => s + q * w[i], 0) / L;
    let u = new Array(nx).fill(v.T_i), qIn = 0, snaps = [], times = [];
    if (a.convective) {
      // Crank–Nicolson with the film coefficient built into the energy balance of the wall half-cell (N.diffusion1D
      // offers only Dirichlet and prescribed-gradient ends, so the Robin row is assembled here and solved with N.tridiag)
      // The steps grow geometrically from a small fraction of the cell diffusion time. With uniform large steps Crank–Nicolson
      // barely damps the short-wavelength modes excited by the sudden surface change, and the profile rings on fine grids.
      const nt = 600, bc = v.h * dx / v.k, kap = Math.max(Math.log(Math.max(alpha * tSim / (dx * dx), 1)), 1e-6), den = Math.expm1(kap);
      const lo = new Array(nx), di = new Array(nx), up = new Array(nx), d = new Array(nx);
      let tk = 0, nextSnap = 0;
      for (let n = 0; n < nt; n++) {
        const tn = tSim * Math.expm1(kap * (n + 1) / nt) / den, dt = tn - tk, r = alpha * dt / (dx * dx);
        if (tk >= nextSnap) { snaps.push(u.slice()); times.push(tk); nextSnap = tk + tSim / 40; }
        lo.fill(-r / 2); di.fill(1 + r); up.fill(-r / 2);
        lo[0] = 0; di[0] = 1 + r + r * bc; up[0] = -r;
        if (a.insulated) { lo[nx - 1] = -r; up[nx - 1] = 0; } else { lo[nx - 1] = 0; di[nx - 1] = 1; up[nx - 1] = 0; }
        for (let i = 1; i < nx - 1; i++) d[i] = u[i] + r / 2 * (u[i + 1] - 2 * u[i] + u[i - 1]) + src * dt;
        d[0] = u[0] + r * (u[1] - u[0]) + r * bc * (2 * v.T_inf - u[0]) + src * dt;
        d[nx - 1] = a.insulated ? u[nx - 1] + r * (u[nx - 2] - u[nx - 1]) + src * dt : v.T_i;
        const un = N.tridiag(lo, di, up, d);
        qIn += v.h * dt * (v.T_inf - 0.5 * (u[0] + un[0]));
        u = un; tk = tn;
      }
      snaps.push(u.slice()); times.push(tSim);
    } else {
      const st = N.diffusion1D({ D: alpha, L, nx, tEnd: tSim, nt: 800, u0: v.T_i, frames: 40, left: { type: 'dirichlet', value: v.T_inf }, right, source });
      snaps = st.snaps; times = st.times; u = st.final;
    }
    const frames = snaps.map(q => q.map(z => z - 273.15));
    const hist = { t: times, s: frames.map(q => q[0]), b: frames.map(q => q[nx - 1]), m: frames.map(q => meanOf(q)) };
    const Tm = meanOf(u), stored = v.rho * v.cp * L * (Tm - v.T_i);
    const qs = a.convective ? v.h * (v.T_inf - u[0]) : -v.k * (-3 * u[0] + 4 * u[1] - u[2]) / (2 * dx);
    const exactOK = a.insulated && a.no_source;
    const FoSim = alpha * tSim / (L * L);
    const roots = exactOK ? slabRoots(a.convective ? Bi : Infinity) : null;
    const exact = exactOK ? x.map(xx => v.T_inf + (v.T_i - v.T_inf) * slabSeries(a.convective ? Bi : Infinity, FoSim, xx / L, roots) - 273.15) : null;
    const pick = [0.05, 0.2, 0.5, 1].map(f => Math.min(frames.length - 1, Math.round(f * (frames.length - 1))));
    const warnings = [];
    if (!a.const_props) warnings.push(`Variable properties are not resolved. The temperature swing is ${lab(Math.abs(v.T_inf - v.T_i), 'K')}; if conductivity or specific heat change by more than a few per cent over that range, treat the result as approximate.`);
    if (tSim < v.t_end) warnings.push('The elapsed time is many diffusion times: the profile shown is the steady state reached well before the requested time.');
    if (a.convective && Bi < 0.1) warnings.push('Biot number below 0.1: the slab is nearly isothermal and a lumped-capacitance model would be adequate.');
    const balance = a.convective && a.insulated ? (stored - qIn - (a.no_source ? 0 : v.q_gen * L * tSim)) / Math.max(Math.abs(stored), Math.abs(qIn), 1) : 0;
    return {
      scalars: [
        scalar('alpha', 'Thermal diffusivity', alpha, 'm^2/s'), scalar('Bi', 'Biot number', Bi, '1', { note: a.convective ? '' : 'not used: surface temperature imposed' }), scalar('Fo', 'Fourier number', Fo, '1'),
        scalar('tau_d', 'Diffusion time L²/α', tauD, 's'), scalar('T_s', 'Heated-face temperature', u[0], 'K', { show: '°C' }),
        scalar('T_b', 'Back-face temperature', u[nx - 1], 'K', { show: '°C' }), scalar('T_m', 'Mean temperature', Tm, 'K', { show: '°C' }),
        scalar('q_s', 'Heat flux into the heated face', qs, 'W/m^2', { show: 'kW/m^2' }), scalar('E_st', 'Energy stored per unit face area', stored, 'J/m^2', { show: 'MJ/m^2' }),
        scalar('delta_p', 'Thermal penetration depth √(π α t)', Math.sqrt(Math.PI * alpha * v.t_end), 'm', { show: 'mm' }),
      ],
      series: [
        line('profiles', 'Temperature profiles', 'Distance from heated face', 'mm', x.map(q => q * 1000), [...pick.map(i => ({ label: `t = ${lab(times[i], 's')}`, data: frames[i] })), ...(exact ? [{ label: 'Exact series, final time', data: exact, dash: true }] : [])], 'Temperature', '°C'),
        line('history', 'Temperature history', 'Time', 's', hist.t, [{ label: 'Heated face', data: hist.s }, { label: 'Back face', data: hist.b }, { label: 'Mean', data: hist.m, dash: true }], 'Temperature', '°C'),
      ],
      anims: [anim('T-anim', 'Temperature through the slab', 'Distance from heated face', 'mm', x.map(q => q * 1000), frames, times, 'Temperature', '°C')],
      checks: [check('Energy balance residual', balance, 2e-2, 'Stored energy against time-integrated surface heat input (evaluated when the back face is adiabatic and the face is convective)')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const alpha = v.k / (v.rho * v.cp), Bi = v.h * v.L / v.k, out = [];
    const base = { convective: true, insulated: true, no_source: true, const_props: true };
    const t1 = 0.5 * v.L * v.L / alpha;
    const r1 = this.solve({ ...v, t_end: t1 }, base);
    out.push(bench('Back-face temperature at Fo = 0.5 vs Fourier series', (val(r1, 'T_b') - v.T_inf) / (v.T_i - v.T_inf), slabSeries(Bi, 0.5, 1), 'Carslaw & Jaeger (1959), plane wall with convection', 5e-3));
    const r2 = this.solve({ ...v, t_end: t1 }, { ...base, convective: false });
    out.push(bench('Mean temperature rise at Fo = 0.5, imposed surface temperature', (val(r2, 'T_m') - v.T_i) / (v.T_inf - v.T_i), 1 - 8 / Math.PI ** 2 * [0, 1, 2, 3, 4].reduce((s, n) => s + Math.exp(-((2 * n + 1) ** 2) * Math.PI ** 2 * 0.5 / 4) / (2 * n + 1) ** 2, 0), 'Exact series for the mean temperature', 5e-3));
    const r3 = this.solve({ ...v, t_end: 0.02 * v.L * v.L / alpha, n_x: 201 }, { ...base, convective: false });
    const i = 20, xq = i * v.L / 200;
    out.push(bench('Early-time profile vs semi-infinite erfc solution', (r3.series[0].y[3].data[i] + 273.15 - v.T_i) / (v.T_inf - v.T_i), erfc(xq / (2 * Math.sqrt(alpha * 0.02 * v.L * v.L / alpha))), 'Semi-infinite solid, Carslaw & Jaeger (1959)', 1e-2));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(250, 70, 160, 220, 'd-body', 2)}
      ${a.convective ? [0, 1, 2, 3].map(i => S.arrow(150, 100 + i * 54, 240, 100 + i * 54, 'd-arrow d-heat')).join('') : S.line(250, 70, 250, 290, 'd-line d-heat')}
      ${S.text(140, 60, a.convective ? `fluid ${lab(v.T_inf - 273.15, '°C')}, h = ${lab(v.h, 'W/m²K')}` : `face held at ${lab(v.T_inf - 273.15, '°C')}`)}
      ${S.path('M250 90 Q300 240 410 262', 'd-line d-heat')} ${S.text(330, 180, 'T(x, t)')}
      ${a.insulated ? S.path('M414 70 L414 290', 'd-ground') : ''} ${S.text(500, 180, a.insulated ? 'adiabatic' : `held at ${lab(v.T_i - 273.15, '°C')}`)}
      ${S.dim(250, 320, 410, 320, `L = ${lab(v.L * 1000, 'mm')}`)}
      ${S.arrow(250, 50, 300, 50)} ${S.text(312, 54, 'x')}
    `);
  },
  experiment: {
    objective: 'Record the temperature history at several depths in a slab after a step change in surface conditions and compare with the heat-equation prediction.',
    apparatus: ['Flat plate of known material, edges insulated so conduction is one-dimensional', 'Stirred constant-temperature bath or air stream to impose the step', 'Insulating backing on the rear face'],
    instruments: [{ name: 'Fine-wire thermocouples (type K, 0.25 mm) at four depths', measures: 'Local temperature', range: '−50 to 400 °C', resolution: '±0.5 K, response below 0.1 s' }, { name: 'Data logger', measures: 'Temperature against time', range: '—', resolution: '10 Hz' }, { name: 'Heat-flux gauge on the heated face', measures: 'Surface flux', range: '0–200 kW/m²', resolution: '±3 %' }],
    procedure: ['Equilibrate the plate at the initial temperature.', 'Immerse it rapidly in the bath and log temperatures until they are within 1 % of the bath temperature.', 'Plot ln[(T − T∞)/(T_i − T∞)] against time; the late-time slope gives ζ₁²α/L².', 'Repeat with a different stirring rate to change the Biot number.'],
    controls: ['Repeat with a plate of twice the thickness: times should scale with L² at fixed Biot number.', 'Check thermocouple lag in a step test in the bath alone.'],
    signatures: ['Late-time decay exponential with a single time constant', 'Collapse of data from different thicknesses when plotted against Fourier number', 'Early-time penetration depth growing as √t'],
    safety: ['Hot liquid and surfaces: gloves and face shield', 'Avoid water baths above 90 °C; use oil with a lid'],
  },
  falsify: ['Late-time temperature decay that is not exponential when properties and film coefficient are constant.', 'Characteristic times that do not scale with the square of the thickness at fixed Biot number.'],
  alternatives: [{ name: 'Lumped capacitance', text: 'For Bi < 0.1 the solid is treated as isothermal: (T − T∞)/(T_i − T∞) = exp(−h t/(ρ c_p L)).' }, { name: 'Semi-infinite solid', text: 'For Fo < 0.05 the back face is not felt and the similarity solution in x/√(αt) applies.' }, { name: 'Hyperbolic (Cattaneo) conduction', text: 'Adds a relaxation time so that heat propagates at finite speed; relevant only at picosecond scales or cryogenic temperatures.' }],
  hazards: [{ hazard: 'Thermal shock cracking', cause: 'Steep surface gradient at high Biot number in brittle materials', mitigation: 'Limit the quench severity or pre-heat' }, { hazard: 'Burns', cause: 'Contact with hot surfaces', mitigation: 'Guarding and insulation' }],
  standards: ['ISO 22007 (determination of thermal conductivity and diffusivity of plastics)', 'ASTM E1461 (thermal diffusivity by the flash method)', 'EN ISO 10456 (design thermal values of building materials)'],
  limits: 'One-dimensional conduction in a homogeneous solid with constant properties and a constant film coefficient. Not valid with phase change, strongly temperature-dependent properties, or significant radiation exchange.',
  numerics: { method: 'Crank–Nicolson in time (steps growing geometrically from the start when the face is convective), second-order central differences in space; the convective face is a half-cell energy balance', order: 2, stability: 'Unconditionally stable', resolution: 'n_x' },
  optimise: { objective: 'T_b', sense: 'max', vars: ['h'], note: 'Raising the film coefficient speeds heating only until the Biot number is large; beyond that conduction controls.' },
  inverse: { series: 'history', curve: 1, fit: ['k', 'h'] },
  extensions: ['Temperature-dependent conductivity and specific heat', 'Radiative exchange at the surface', 'Phase change with a moving front (Stefan problem)', 'Cylindrical and spherical geometries'],
};

// ------------------------------------------------------------------ heat exchanger, effectiveness–NTU
const effect = (ntu, cr, counter) => {
  if (!counter) return (1 - Math.exp(-ntu * (1 + cr))) / (1 + cr);
  if (Math.abs(1 - cr) < 1e-9) return ntu / (1 + ntu);
  const e = Math.exp(-ntu * (1 - cr));
  return (1 - e) / (1 - cr * e);
};
const lmtd = (d1, d2) => (!(d1 > 0 && d2 > 0) ? 0 : Math.abs(d1 - d2) < 1e-9 * Math.max(Math.abs(d1), Math.abs(d2), 1e-30) ? 0.5 * (d1 + d2) : (d1 - d2) / Math.log(d1 / d2));

const exchanger = {
  id: 'heat-exchanger-ntu',
  title: 'Heat exchanger rating by the effectiveness–NTU method',
  module: 2, klass: 'I', domains: ['thermal', 'chemical'],
  keywords: ['heat exchanger', 'ntu', 'effectiveness', 'lmtd', 'log mean temperature', 'counterflow', 'parallel flow', 'fouling', 'shell and tube', 'duty', 'outlet temperature', 'condenser', 'exchanger'],
  summary: 'Outlet temperatures, duty and effectiveness of a counterflow or parallel-flow heat exchanger of known area, with fouling and a log-mean-temperature cross-check.',
  background: [
    'A heat exchanger of given area and overall coefficient transfers a fraction ε of the maximum duty that thermodynamics allows, C_min (T_h,in − T_c,in). The effectiveness depends only on the number of transfer units NTU = UA/C_min, the capacity-rate ratio and the flow arrangement. The method avoids the iteration that the log-mean-temperature-difference approach needs when outlet temperatures are unknown; the two are algebraically equivalent.',
    'Deposits on the heat-transfer surfaces add a thermal resistance in series with the clean coefficient. Counterflow gives the highest effectiveness for a given NTU and is the only simple arrangement in which the cold outlet can be hotter than the hot outlet.',
  ],
  phenomena: ['Convective heat transfer between two streams', 'Fouling resistance', 'Temperature pinch', 'Entropy generation by heat transfer across a finite temperature difference'],
  laws: ['energy', 'second', 'fourier'],
  refs: ['Kays, W. M. & London, A. L. (1984). Compact Heat Exchangers, 3rd ed., McGraw-Hill.', 'Incropera, F. P., DeWitt, D. P., Bergman, T. L. & Lavine, A. S. (2007). Fundamentals of Heat and Mass Transfer, 6th ed., Wiley.', 'Shah, R. K. & Sekulić, D. P. (2003). Fundamentals of Heat Exchanger Design, Wiley.'],
  inputs: [
    inp('m_h', 'Hot-stream mass flow rate', 'kg/s', 2.5, { min: 0.01, max: 500, aliases: ['hot flow', 'hot stream'] }),
    inp('cp_h', 'Hot-stream specific heat', 'J/(kg K)', 2100, { min: 500, max: 15000, kind: 'fluid', aliases: ['hot specific heat'], src: 'Light oil' }),
    inp('T_hi', 'Hot-stream inlet temperature', '°C', 120, { min: 30, max: 600, aliases: ['hot inlet', 'hot temperature'] }),
    inp('m_c', 'Cold-stream mass flow rate', 'kg/s', 3, { min: 0.01, max: 500, aliases: ['cold flow', 'cold stream', 'cooling water'] }),
    inp('cp_c', 'Cold-stream specific heat', 'J/(kg K)', 4180, { min: 500, max: 15000, kind: 'fluid', aliases: ['cold specific heat'], src: 'Water' }),
    inp('T_ci', 'Cold-stream inlet temperature', '°C', 20, { min: -40, max: 25, aliases: ['cold inlet', 'cold temperature'] }),
    inp('U', 'Clean overall heat-transfer coefficient', 'W/(m^2 K)', 500, { min: 5, max: 10000, aliases: ['overall coefficient', 'u-value', 'u value'] }),
    inp('A', 'Heat-transfer area', 'm^2', 25, { min: 0.05, max: 5000, kind: 'geometry', aliases: ['area', 'surface'] }),
    inp('R_f', 'Total fouling resistance', 'm^2 K/W', 0.0002, { min: 0, max: 0.005, aliases: ['fouling', 'fouling factor'], src: 'Order of magnitude for treated cooling water plus light hydrocarbon (TEMA tables)' }),
  ],
  assumptions: [
    asm('counterflow', 'The streams flow in opposite directions (pure counterflow).', { why: 'Highest effectiveness for a given area', alt: 'The streams flow in the same direction (parallel flow).' }),
    asm('fouled', 'Fouling adds a series resistance R_f to the clean coefficient.', { why: 'Design for end-of-run performance', alt: 'Surfaces are clean: the clean coefficient applies.' }),
    asm('sensible', 'Both streams change temperature without phase change.', { why: 'Liquid–liquid service', alt: 'The hot stream condenses at constant temperature (capacity-rate ratio zero).' }),
    asm('adiabatic', 'No heat is exchanged with the surroundings.', { why: 'Insulated shell', alt: 'Five per cent of the heat given up by the hot stream is lost to the surroundings and does not reach the cold stream.' }),
  ],
  symbols: { C_h: ['Hot capacity rate', 'W/K'], C_c: ['Cold capacity rate', 'W/K'], C_min: ['Smaller capacity rate', 'W/K'], C_r: ['Capacity-rate ratio', '1'], U_f: ['Service overall coefficient', 'W/(m^2 K)'], NTU: ['Number of transfer units', '1'], eps: ['Effectiveness', '1'], Q: ['Duty', 'W'], T_ho: ['Hot outlet temperature', 'K'], T_co: ['Cold outlet temperature', 'K'], dT_lm: ['Log-mean temperature difference', 'K'], dT_1: ['Terminal temperature difference, end 1', 'K'], dT_2: ['Terminal temperature difference, end 2', 'K'], f_loss: ['Fraction of duty lost', '1'], S_gen: ['Entropy generation rate', 'W/K'] },
  equations: a => [
    eq('ch', 'Hot capacity rate', 'C_h', 'm_h*cp_h', { kind: 'definition' }),
    eq('cc', 'Cold capacity rate', 'C_c', 'm_c*cp_c', { kind: 'definition' }),
    a.sensible ? eq('cr', 'Capacity-rate ratio', 'C_r', 'C_min/max(C_h, C_c)', { kind: 'definition', needs: ['sensible'] }) : eq('cr', 'Capacity-rate ratio', 'C_r', '0', { kind: 'closure', origin: 'Isothermal condensation: infinite capacity rate on the hot side' }),
    a.fouled ? eq('uf', 'Service coefficient', '1/U_f', '1/U + R_f', { kind: 'law', origin: 'Thermal resistances in series', needs: ['fouled'] }) : eq('uf', 'Service coefficient', 'U_f', 'U', { kind: 'closure', origin: 'Clean surfaces' }),
    eq('ntu', 'Number of transfer units', 'NTU', 'U_f*A/C_min', { kind: 'definition' }),
    a.counterflow
      ? eq('eps', 'Counterflow effectiveness', 'eps', '(1 - exp(-NTU*(1 - C_r)))/(1 - C_r*exp(-NTU*(1 - C_r)))', { kind: 'derived', origin: 'Integration of the two stream energy balances', needs: ['counterflow'] })
      : eq('eps', 'Parallel-flow effectiveness', 'eps', '(1 - exp(-NTU*(1 + C_r)))/(1 + C_r)', { kind: 'derived', origin: 'Integration of the two stream energy balances' }),
    eq('q', 'Duty', 'Q', 'eps*C_min*(T_hi - T_ci)', { kind: 'law', origin: 'First law; definition of effectiveness' }),
    eq('tco', 'Cold outlet temperature', 'T_co', a.adiabatic ? 'T_ci + Q/C_c' : 'T_ci + (1 - f_loss)*Q/C_c', { kind: 'law', origin: 'Cold-stream energy balance', needs: a.adiabatic ? ['adiabatic'] : [] }),
    ...(a.sensible ? [eq('tho', 'Hot outlet temperature', 'T_ho', 'T_hi - Q/C_h', { kind: 'law', origin: 'Hot-stream energy balance' })] : []),
    eq('lmtd', 'Log-mean temperature difference', 'dT_lm', '(dT_1 - dT_2)/ln(dT_1/dT_2)', { kind: 'derived', origin: 'Integration of the local rate equation' }),
    eq('rate', 'Rate equation (cross-check)', 'Q', 'U_f*A*dT_lm', { kind: 'law', origin: 'Newton’s law of cooling integrated over the area' }),
  ],
  derivation: a => [
    { text: 'Energy balances on a differential area dA relate the change of each stream temperature to the local heat flow.', tex: '\\mathrm{d}q = -C_h\\,\\mathrm{d}T_h = \\pm C_c\\,\\mathrm{d}T_c = U\\,(T_h - T_c)\\,\\mathrm{d}A' },
    { text: 'Subtracting the two balances gives a first-order equation for the local temperature difference, which decays (or grows) exponentially with area.', tex: '\\frac{\\mathrm{d}(T_h-T_c)}{T_h-T_c} = -U\\left(\\frac{1}{C_h} ' + (a.counterflow ? '-' : '+') + ' \\frac{1}{C_c}\\right)\\mathrm{d}A' },
    { text: 'Integrating over the whole area and eliminating the outlet temperatures with the overall balances gives the effectiveness.', tex: a.counterflow ? '\\varepsilon = \\frac{1-e^{-\\mathrm{NTU}(1-C_r)}}{1-C_r\\,e^{-\\mathrm{NTU}(1-C_r)}}' : '\\varepsilon = \\frac{1-e^{-\\mathrm{NTU}(1+C_r)}}{1+C_r}' },
    { text: 'The same integration written in terms of the terminal differences is the log-mean form; the two must agree.', tex: 'Q = U A\\,\\Delta T_{lm},\\qquad \\Delta T_{lm} = \\frac{\\Delta T_1-\\Delta T_2}{\\ln(\\Delta T_1/\\Delta T_2)}' },
    { text: 'Fouling layers act as resistances in series with the clean wall and films.', tex: '\\frac{1}{U_f} = \\frac{1}{U} + R_f' },
  ],
  solve(v, a) {
    const Ch = v.m_h * v.cp_h, Cc = v.m_c * v.cp_c, invCh = a.sensible ? 1 / Ch : 0;
    const Cmin = a.sensible ? Math.min(Ch, Cc) : Cc, Cr = a.sensible ? Cmin / Math.max(Ch, Cc) : 0;
    const Uf = a.fouled ? 1 / (1 / v.U + v.R_f) : v.U, ntu = Uf * v.A / Cmin, counter = a.counterflow;
    const eps = effect(ntu, Cr, counter), Qmax = Cmin * (v.T_hi - v.T_ci), Q = eps * Qmax;
    const fl = a.adiabatic ? 0 : 0.05;
    const Tho = v.T_hi - Q * invCh, Tco = v.T_ci + Q / Cc, TcoNet = v.T_ci + (1 - fl) * Q / Cc;
    // terminal differences as ΔT_max·(1 − ε) and ΔT_max·(1 − ε C_r) written without the subtraction: at large NTU the pinched end is
    // far below the rounding of a difference of two outlet temperatures, and the profile is built from it
    const eN = Math.exp(-ntu * (counter ? 1 - Cr : 1 + Cr)), bal = counter && Math.abs(1 - Cr) < 1e-9, dT0 = v.T_hi - v.T_ci;
    const pin = dT0 * (!counter ? eN : bal ? 1 / (1 + ntu) : (1 - Cr) * eN / (1 - Cr * eN)), wide = dT0 * (!counter ? 1 : bal ? 1 / (1 + ntu) : (1 - Cr) / (1 - Cr * eN));
    const d1 = !counter ? wide : !a.sensible || Cc <= Ch ? pin : wide, d2 = !counter ? pin : !a.sensible || Cc <= Ch ? wide : pin;
    const dTlm = lmtd(d1, d2), Qlm = Uf * v.A * dTlm;
    // profiles from the hot inlet (s = 0) to the hot outlet (s = 1), integrated from the end with the larger temperature difference
    // towards the pinch, so that the exponential always decays and no rounding error is amplified
    const s = N.linspace(0, 1, 101), m = Uf * v.A * (invCh + (counter ? -1 : 1) / Cc), back = m < 0;
    const Th = s.map(q => (back ? Tho + d2 * invCh * Uf * v.A * Math.expm1(m * (1 - q)) / m : v.T_hi - d1 * invCh * Uf * v.A * (Math.abs(m) < 1e-12 ? q : -Math.expm1(-m * q) / m)));
    const Tc = s.map((q, i) => Th[i] - (back ? d2 * Math.exp(m * (1 - q)) : d1 * Math.exp(-m * q)));
    const Sgen = (a.sensible ? Ch * Math.log(Tho / v.T_hi) : -Q / v.T_hi) + Cc * Math.log(Tco / v.T_ci);
    const nn = N.logspace(0.05, 10, 60);
    const warnings = [];
    if (Math.min(d1, d2) < 3) warnings.push('A terminal temperature difference is below 3 K: the exchanger is pinched and extra area buys almost no extra duty.');
    if (!a.adiabatic) warnings.push('Heat loss is applied as a fixed 5 % of the hot-side duty; the cold outlet temperature reported is after that loss.');
    return {
      scalars: [
        scalar('C_h', 'Hot capacity rate', a.sensible ? Ch : Infinity, 'W/K', { text: a.sensible ? undefined : 'Unbounded (condensing)' }), scalar('C_c', 'Cold capacity rate', Cc, 'W/K'),
        scalar('C_r', 'Capacity-rate ratio', Cr, '1'), scalar('U_f', 'Service overall coefficient', Uf, 'W/(m^2 K)'), scalar('NTU', 'Number of transfer units', ntu, '1'),
        scalar('eps', 'Effectiveness', eps, '1', { show: '%' }), scalar('Q', 'Duty given up by the hot stream', Q, 'W', { show: 'kW' }), scalar('Q_max', 'Maximum possible duty', Qmax, 'W', { show: 'kW' }),
        scalar('T_ho', 'Hot outlet temperature', Tho, 'K', { show: '°C' }), scalar('T_co', 'Cold outlet temperature', TcoNet, 'K', { show: '°C' }),
        scalar('dT_lm', 'Log-mean temperature difference', dTlm, 'K'), scalar('dT_min', 'Smallest terminal temperature difference', Math.min(d1, d2), 'K'),
        scalar('S_gen', 'Entropy generation rate', Sgen, 'W/K'), scalar('dU', 'Loss of coefficient to fouling', 1 - Uf / v.U, '1', { show: '%' }),
      ],
      series: [
        line('profile', 'Stream temperatures along the exchanger', 'Fraction of area from the hot inlet', '–', s, [{ label: 'Hot stream', data: Th.map(q => q - 273.15) }, { label: 'Cold stream', data: Tc.map(q => q - 273.15) }], 'Temperature', '°C'),
        line('eps-ntu', 'Effectiveness against NTU at this capacity-rate ratio', 'NTU', '–', nn, [{ label: 'Counterflow', data: nn.map(q => effect(q, Cr, true)) }, { label: 'Parallel flow', data: nn.map(q => effect(q, Cr, false)), dash: true }], 'Effectiveness', '–', { logx: true, marker: [ntu, eps] }),
      ],
      checks: [
        check('LMTD cross-check residual', Math.min(d1, d2) > 1e-4 ? (Qlm - Q) / Q : 0, 1e-8, 'Duty from U·A·ΔT_lm against duty from ε·C_min·ΔT_max (not evaluated when a terminal difference is below 0.0001 K, where the logarithm is lost to rounding)'),
        check('Second law: entropy generation not negative', Math.min(Sgen, 0), 1e-9, 'Heat flows from hot to cold only'),
        check('Profile end-point consistency', (back ? Th[0] - v.T_hi : Th[100] - Tho) / (v.T_hi - v.T_ci), 1e-9, back ? 'Hot-stream profile integrated back from the outlet reaches the inlet temperature' : 'Integrated hot-stream profile reaches the outlet temperature from the overall balance'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { counterflow: true, fouled: false, sensible: true, adiabatic: true };
    const one = { ...v, m_h: 1, cp_h: 1000, m_c: 1, cp_c: 1000, U: 100, A: 10 };
    return [
      bench('Balanced counterflow at NTU = 1', val(this.solve(one, b), 'eps'), 0.5, 'ε = NTU/(1 + NTU)', 1e-12),
      bench('Balanced parallel flow at NTU = 1', val(this.solve(one, { ...b, counterflow: false }), 'eps'), (1 - Math.exp(-2)) / 2, 'ε = (1 − e^{−2NTU})/2', 1e-12),
      bench('Condenser (C_r = 0) at NTU = 1', val(this.solve(one, { ...b, sensible: false }), 'eps'), 1 - Math.exp(-1), 'ε = 1 − e^{−NTU}', 1e-12),
      ...(() => { const r = this.solve(v, a); return val(r, 'dT_min') > 1e-4 ? [bench('Duty from the log-mean form at the current inputs', val(r, 'U_f') * v.A * val(r, 'dT_lm'), val(r, 'Q'), 'Equivalence of the LMTD and ε–NTU methods', 1e-8)] : []; })(),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(120, 120, 400, 110, 'd-body', 8)} ${S.rect(90, 155, 460, 40, 'd-liquid', 4)}
      ${S.arrow(40, 175, 88, 175, 'd-arrow d-heat')} ${S.arrow(552, 175, 600, 175, 'd-arrow d-heat')}
      ${S.text(60, 160, `hot in ${lab(v.T_hi - 273.15, '°C')}`, 'd-text d-small')} ${S.text(585, 160, 'hot out', 'd-text d-small')}
      ${a.counterflow ? S.arrow(480, 60, 480, 118) + S.arrow(160, 232, 160, 290) : S.arrow(160, 60, 160, 118) + S.arrow(480, 232, 480, 290)}
      ${S.text(a.counterflow ? 480 : 160, 50, `cold in ${lab(v.T_ci - 273.15, '°C')}`)} ${S.text(a.counterflow ? 160 : 480, 310, 'cold out')}
      ${[0, 1, 2, 3, 4].map(i => S.arrow(180 + i * 70, 158, 180 + i * 70, 132, 'd-arrow d-heat')).join('')}
      ${S.text(320, 260, `${a.counterflow ? 'counterflow' : 'parallel flow'},  U = ${lab(v.U, 'W/m²K')},  A = ${lab(v.A, 'm²')}`)}
      ${a.fouled ? S.text(320, 340, `fouling resistance ${lab(v.R_f, 'm²K/W')}`, 'd-text d-small') : ''}
    `);
  },
  experiment: {
    objective: 'Measure the duty and outlet temperatures of a double-pipe exchanger in both flow arrangements and compare the effectiveness with the ε–NTU prediction.',
    apparatus: ['Double-pipe or plate heat exchanger with reversible flow connections', 'Hot and cold water circuits with independent flow control', 'Insulation over the outer pipe'],
    instruments: [{ name: 'Four Pt100 probes with mixing elbows', measures: 'Inlet and outlet temperature of each stream', range: '0–150 °C', resolution: '±0.1 K' }, { name: 'Two Coriolis or electromagnetic flow meters', measures: 'Stream flow rates', range: '0–5 kg/s', resolution: '±0.2 %' }, { name: 'Differential pressure transmitters', measures: 'Pressure drop (fouling indicator)', range: '0–1 bar', resolution: '±0.1 %' }],
    procedure: ['Establish steady flow and wait until all four temperatures are steady to 0.1 K.', 'Record flows and temperatures; compute the duty from each stream and check that they agree within 3 %.', 'Repeat over a range of flow rates to vary NTU and the capacity-rate ratio.', 'Reverse one stream and repeat.'],
    controls: ['Energy balance closure between the two streams as a data-quality gate', 'A Wilson-plot series to separate the film coefficients'],
    signatures: ['Counterflow effectiveness above parallel-flow effectiveness at the same NTU', 'Parallel-flow effectiveness saturating at 1/(1 + C_r)', 'Gradual fall of the service coefficient with running time as fouling builds'],
    safety: ['Hot water above 60 °C: lagging and guarding', 'Relief valve on any circuit that can be isolated and heated'],
  },
  falsify: ['Measured effectiveness above the counterflow value at the same NTU and capacity-rate ratio (within uncertainty).', 'Stream energy balances that do not close for an insulated exchanger.'],
  alternatives: [{ name: 'LMTD method with correction factor F', text: 'Preferred for sizing multi-pass shell-and-tube units when all four terminal temperatures are specified.' }, { name: 'Cell or finite-volume models', text: 'Needed when the overall coefficient varies strongly along the exchanger or with phase change over part of the area.' }, { name: 'P–NTU charts', text: 'The same theory expressed per stream, convenient for shell-and-tube configurations.' }],
  hazards: [{ hazard: 'Tube rupture and overpressure of the low-pressure side', cause: 'Corrosion, vibration or thermal fatigue', mitigation: 'Relief sized for tube rupture; material selection' }, { hazard: 'Thermal stress', cause: 'Large differential expansion between shell and tubes', mitigation: 'Expansion joint or floating head' }],
  standards: ['TEMA Standards (Tubular Exchanger Manufacturers Association)', 'API Standard 660 (shell-and-tube heat exchangers)', 'ASME Boiler and Pressure Vessel Code, Section VIII'],
  limits: 'Constant overall coefficient and specific heats, pure counterflow or parallel flow, steady state. Multi-pass and cross-flow arrangements need their own effectiveness relations.',
  numerics: { method: 'Closed-form effectiveness relations and analytical temperature profiles' },
  optimise: { objective: 'Q', sense: 'max', vars: ['A', 'm_c'], note: 'Duty rises with area with diminishing returns as the pinch closes; in practice minimise total annual cost.' },
  inverse: { series: 'profile', curve: 0, fit: ['U', 'R_f'] },
  extensions: ['Multi-pass shell-and-tube and cross-flow effectiveness relations', 'Film coefficients from Dittus–Boelter or Gnielinski correlations', 'Fouling growth with time and cleaning-cycle optimisation'],
};

// ------------------------------------------------------------------ simple two-phase working-fluid model
// Incompressible liquid (constant c_l, v_l) and ideal-gas vapour (constant c_p). Saturation follows from equality of the
// Gibbs energies of the two phases, so the model is a single consistent fundamental relation and cannot violate the second law.
const WORKING_FLUIDS = {
  water: { name: 'Water', M: 0.018015, Tref: 373.15, pref: 101325, hfg0: 2.257e6, cl: 4186, cpv: 2000, vl: 1.04e-3, Tcrit: 647.1 },
  pentane: { name: 'n-Pentane', M: 0.07215, Tref: 309.2, pref: 101325, hfg0: 3.576e5, cl: 2317, cpv: 1667, vl: 1.6e-3, Tcrit: 469.7 },
  r134a: { name: 'R134a', M: 0.10203, Tref: 247.08, pref: 101325, hfg0: 2.170e5, cl: 1340, cpv: 850, vl: 7.7e-4, Tcrit: 374.2 },
  ammonia: { name: 'Ammonia', M: 0.017031, Tref: 239.82, pref: 101325, hfg0: 1.369e6, cl: 4600, cpv: 2200, vl: 1.47e-3, Tcrit: 405.4 },
};
function fluidModel(f) {
  const Rs = C.R_u / f.M, h0 = f.hfg0 + f.vl * f.pref, s0 = f.hfg0 / f.Tref;
  const hl = (T, p) => f.cl * (T - f.Tref) + f.vl * p, sl = T => f.cl * Math.log(T / f.Tref);
  const hv = T => f.cpv * (T - f.Tref) + h0, sv = (T, p) => f.cpv * Math.log(T / f.Tref) - Rs * Math.log(p / f.pref) + s0;
  const psat = T => {
    let p = f.pref;
    for (let i = 0; i < 40; i++) {
      const pn = f.pref * Math.exp((hl(T, p) - T * sl(T) - hv(T) + T * (f.cpv * Math.log(T / f.Tref) + s0)) / (Rs * T));
      if (Math.abs(pn - p) < 1e-13 * p) { p = pn; break; }
      p = pn;
    }
    return p;
  };
  /** State reached at saturation temperature Ts (pressure ps) with entropy s: wet mixture or superheated vapour. */
  const atEntropy = (s, Ts, ps) => {
    const sg = sv(Ts, ps), sf = sl(Ts);
    if (s <= sg) { const x = (s - sf) / (sg - sf); return { T: Ts, x, h: hl(Ts, ps) + x * (hv(Ts) - hl(Ts, ps)), s }; }
    const T = Ts * Math.exp((s - sg) / f.cpv); return { T, x: 1, h: hv(T), s, superheated: true };
  };
  /** State at pressure ps (saturation temperature Ts) with enthalpy h. */
  const atEnthalpy = (h, Ts, ps) => {
    const hf = hl(Ts, ps), hg = hv(Ts);
    if (h <= hg) { const x = (h - hf) / (hg - hf); return { T: Ts, x, h, s: sl(Ts) + x * (sv(Ts, ps) - sl(Ts)) }; }
    const T = f.Tref + (h - h0) / f.cpv; return { T, x: 1, h, s: sv(T, ps), superheated: true };
  };
  return { ...f, Rs, hl, sl, hv, sv, psat, atEntropy, atEnthalpy };
}
const FM = Object.fromEntries(Object.entries(WORKING_FLUIDS).map(([k, f]) => [k, fluidModel(f)]));
/** Saturation dome as a closed parametric curve in the T–s plane. */
function dome(F, Tlo, Thi, n = 40) {
  const Ts = N.linspace(Tlo, Thi, n), sL = Ts.map(F.sl), sV = Ts.map(T => F.sv(T, F.psat(T)));
  return { s: [...sL, ...sV.slice().reverse()], T: [...Ts, ...Ts.slice().reverse()] };
}

// ------------------------------------------------------------------ Rankine / organic Rankine cycle
function rankineCycle(F, Tb, dTsh, Tc, etaT, etaP, pumpFactor) {
  const pb = F.psat(Tb), pc = F.psat(Tc), T3 = Tb + dTsh, pp = pb * pumpFactor;
  const h1 = F.hl(Tc, pc), s1 = F.sl(Tc), wp = F.vl * (pp - pc) / etaP, h2 = h1 + wp, T2 = Tc + (wp - F.vl * (pp - pc)) / F.cl;
  const h3 = F.hv(T3), s3 = F.sv(T3, pb), st4s = F.atEntropy(s3, Tc, pc), wt = etaT * (h3 - st4s.h), st4 = F.atEnthalpy(h3 - wt, Tc, pc);
  const qin = h3 - h2, qout = st4.h - h1, eta = (wt - wp) / qin;
  return { pb, pc, pp, T2, T3, h1, h2, h3, s1, s3, st4s, st4, wt, wp, qin, qout, eta };
}

const rankine = {
  id: 'rankine-cycle',
  title: 'Rankine and organic Rankine power cycle',
  module: 2, klass: 'I', domains: ['thermal', 'mechanical'],
  keywords: ['rankine cycle', 'rankine', 'steam cycle', 'steam turbine', 'organic rankine', 'orc', 'binary cycle', 'binary power', 'power plant', 'thermal efficiency', 'carnot', 'back work ratio', 'boiler', 'condenser', 'geothermal'],
  summary: 'Thermal efficiency, net work and back-work ratio of an ideal or non-ideal Rankine cycle on water or an organic working fluid, compared with the Carnot limit.',
  background: [
    'The Rankine cycle is the basis of steam and binary (organic) power plants. Liquid is pumped to high pressure, evaporated and optionally superheated by the heat source, expanded through a turbine and condensed. Because the liquid is nearly incompressible the pump absorbs only a small fraction of the turbine output, which is the practical advantage of a condensing cycle over a gas cycle.',
    'The second law limits any engine working between a source at T_H and a sink at T_L to the Carnot efficiency 1 − T_L/T_H. A Rankine cycle falls below that limit even with ideal machines because much of the heat is added at temperatures below the peak temperature. Organic fluids with low boiling points allow useful pressures at source temperatures of 80–200 °C, as in geothermal binary plants.',
    'Fluid properties here come from a deliberately simple model: an incompressible liquid and an ideal-gas vapour with constant specific heats, with the saturation line obtained from equality of the Gibbs energies. It reproduces trends and magnitudes but not steam-table accuracy, particularly near the critical point.',
  ],
  phenomena: ['Evaporation and condensation', 'Isentropic and irreversible expansion', 'Heat addition at varying temperature', 'Moisture at turbine exhaust'],
  laws: ['energy', 'second', 'ideal_gas', 'mass'],
  refs: ['Moran, M. J., Shapiro, H. N., Boettner, D. D. & Bailey, M. B. (2014). Fundamentals of Engineering Thermodynamics, 8th ed., Wiley.', 'Çengel, Y. A. & Boles, M. A. (2015). Thermodynamics: An Engineering Approach, 8th ed., McGraw-Hill.', 'DiPippo, R. (2016). Geothermal Power Plants, 4th ed., Butterworth-Heinemann.', 'Wagner, W. & Pruß, A. (2002). The IAPWS formulation 1995 for the thermodynamic properties of ordinary water substance. J. Phys. Chem. Ref. Data 31, 387–535.'],
  inputs: [
    inp('T_b', 'Evaporation (boiler saturation) temperature', '°C', 285, { min: 80, max: 360, aliases: ['boiler temperature', 'evaporation temperature', 'evaporator temperature', 'saturation temperature'] }),
    inp('dT_sh', 'Superheat above saturation', 'K', 215, { min: 0, max: 350, aliases: ['superheat'] }),
    inp('T_c', 'Condensing temperature', '°C', 40, { min: 15, max: 60, aliases: ['condenser temperature', 'condensing temperature', 'sink temperature'] }),
    inp('eta_t', 'Turbine isentropic efficiency', '1', 0.87, { min: 0.4, max: 1, aliases: ['turbine efficiency', 'isentropic efficiency'] }),
    inp('eta_p', 'Pump isentropic efficiency', '1', 0.8, { min: 0.3, max: 1, aliases: ['pump efficiency'] }),
    inp('P_net', 'Net power output', 'MW', 50, { min: 0.01, max: 2000, aliases: ['net power', 'power output', 'capacity'] }),
    inp('dT_app', 'Approach temperature difference to source and sink', 'K', 15, { min: 0, max: 100, aliases: ['approach', 'pinch'] }),
  ],
  assumptions: [
    asm('water', 'The working fluid is water.', { why: 'Conventional steam plant', alt: 'The working fluid is n-pentane, as in a geothermal binary (organic Rankine) plant.' }),
    asm('real_machines', 'Turbine and pump have the stated isentropic efficiencies.', { why: 'Realistic machines', alt: 'Turbine and pump are isentropic (the ideal Rankine cycle).' }),
    asm('no_dp', 'There are no pressure losses in the boiler, condenser or piping.', { why: 'Small against the cycle pressure ratio', alt: 'The pump must deliver 10 % above turbine-inlet pressure to overcome boiler and piping losses.' }),
    asm('ideal_ht', 'The heat source is at the peak cycle temperature and the sink at the condensing temperature.', { why: 'Isolates internal irreversibility', alt: 'Source and sink are separated from the cycle by the approach temperature difference; the Carnot limit is then evaluated between the reservoirs.' }),
    asm('simple_props', 'Properties follow an incompressible-liquid, ideal-gas-vapour model with constant specific heats.', { why: 'Closed-form and thermodynamically consistent', alt: 'No alternative property model is built in: a warning recommends steam tables or a reference equation of state for design work.' }),
  ],
  symbols: { p_b: ['Boiler pressure', 'Pa'], p_c: ['Condenser pressure', 'Pa'], p_p: ['Pump delivery pressure', 'Pa'], v_l: ['Liquid specific volume', 'm^3/kg'], w_p: ['Pump work', 'J/kg'], w_t: ['Turbine work', 'J/kg'], h_1: ['Enthalpy, condenser outlet', 'J/kg'], h_2: ['Enthalpy, pump outlet', 'J/kg'], h_3: ['Enthalpy, turbine inlet', 'J/kg'], h_4: ['Enthalpy, turbine outlet', 'J/kg'], h_4s: ['Enthalpy after isentropic expansion', 'J/kg'], s_3: ['Entropy, turbine inlet', 'J/(kg K)'], s_4s: ['Entropy after isentropic expansion', 'J/(kg K)'], q_in: ['Heat added', 'J/kg'], q_out: ['Heat rejected', 'J/kg'], eta: ['Thermal efficiency', '1'], eta_C: ['Carnot efficiency', '1'], T_H: ['Source temperature', 'K'], T_L: ['Sink temperature', 'K'], bwr: ['Back-work ratio', '1'], mdot: ['Working-fluid mass flow rate', 'kg/s'], p_sat: ['Saturation pressure', 'Pa'], T: ['Temperature', 'K'], h_fg: ['Enthalpy of vaporisation', 'J/kg'], R_s: ['Specific gas constant', 'J/(kg K)'] },
  equations: a => [
    eq('cc', 'Clausius–Clapeyron relation', 'd(p_sat,T)', 'h_fg*p_sat/(R_s*T^2)', { kind: 'law', origin: 'Phase equilibrium with ideal-gas vapour and negligible liquid volume', needs: ['simple_props'] }),
    ...(a.no_dp ? [eq('pp', 'Pump delivery pressure', 'p_p', 'p_b', { kind: 'closure', needs: ['no_dp'] })] : [eq('pp', 'Pump delivery pressure', 'p_p', '1.1*p_b', { kind: 'closure', origin: 'Allowance for boiler and piping pressure loss' })]),
    a.real_machines ? eq('wp', 'Pump work', 'w_p', 'v_l*(p_p - p_c)/eta_p', { kind: 'law', origin: 'First law for an incompressible liquid', needs: ['real_machines'] }) : eq('wp', 'Pump work', 'w_p', 'v_l*(p_p - p_c)', { kind: 'law', origin: 'Isentropic compression of an incompressible liquid' }),
    eq('h2', 'Pump outlet enthalpy', 'h_2', 'h_1 + w_p', { kind: 'law', origin: 'First law, adiabatic pump' }),
    eq('s', 'Isentropic expansion', 's_4s', 's_3', { kind: 'law', origin: 'Second law for a reversible adiabatic process' }),
    a.real_machines ? eq('wt', 'Turbine work', 'w_t', 'eta_t*(h_3 - h_4s)', { kind: 'law', origin: 'First law with the definition of isentropic efficiency', needs: ['real_machines'] }) : eq('wt', 'Turbine work', 'w_t', 'h_3 - h_4s', { kind: 'law', origin: 'First law, isentropic turbine' }),
    eq('qin', 'Heat added', 'q_in', 'h_3 - h_2', { kind: 'law', origin: 'First law, boiler' }),
    eq('qout', 'Heat rejected', 'q_out', 'h_4 - h_1', { kind: 'law', origin: 'First law, condenser' }),
    eq('eta', 'Thermal efficiency', 'eta', '(w_t - w_p)/q_in', { kind: 'definition' }),
    eq('carnot', 'Carnot limit', 'eta_C', '1 - T_L/T_H', { kind: 'law', origin: 'Second law of thermodynamics' }),
    eq('bwr', 'Back-work ratio', 'bwr', 'w_p/w_t', { kind: 'definition' }),
    eq('m', 'Mass flow rate', 'mdot', 'P_net/(w_t - w_p)', { kind: 'derived', origin: 'Definition of net specific work' }),
  ],
  derivation: a => [
    { text: 'Each component is a steady-flow device. Neglecting kinetic and potential energy, the first law for each reduces to an enthalpy difference.', tex: 'q - w = h_{out} - h_{in}' },
    { text: 'The liquid is nearly incompressible, so the pump work is the specific volume times the pressure rise' + (a.real_machines ? ', divided by the pump efficiency.' : '.'), tex: a.real_machines ? 'w_p = \\frac{v_l\\,(p_p - p_c)}{\\eta_p}' : 'w_p = v_l\\,(p_p - p_c)' },
    { text: 'An ideal turbine is isentropic; a real one delivers a fraction η_t of the isentropic enthalpy drop.', tex: 'w_t = ' + (a.real_machines ? '\\eta_t\\,' : '') + '(h_3 - h_{4s}),\\qquad s_{4s} = s_3' },
    { text: 'The efficiency is net work over heat added. Applying the first law around the loop shows it also equals 1 − q_out/q_in.', tex: '\\eta = \\frac{w_t - w_p}{q_{in}} = 1 - \\frac{q_{out}}{q_{in}}' },
    { text: 'The Clausius inequality for the cycle, with all heat added below T_H and rejected above T_L, bounds the efficiency.', tex: '\\oint\\frac{\\delta q}{T} \\le 0 \;\\Rightarrow\; \\eta \\le 1 - \\frac{T_L}{T_H}' },
    { text: 'The saturation line of the property model follows from equal Gibbs energies of liquid and vapour, which for an ideal-gas vapour and small liquid volume is the Clausius–Clapeyron relation.', tex: '\\frac{\\mathrm{d}p_{sat}}{\\mathrm{d}T} = \\frac{h_{fg}\\,p_{sat}}{R_s T^2}' },
  ],
  solve(v, a) {
    const F = a.water ? FM.water : FM.pentane;
    const etaT = a.real_machines ? v.eta_t : 1, etaP = a.real_machines ? v.eta_p : 1, pf = a.no_dp ? 1 : 1.1;
    const cy = rankineCycle(F, v.T_b, v.dT_sh, v.T_c, etaT, etaP, pf);
    const TH = cy.T3 + (a.ideal_ht ? 0 : v.dT_app), TL = v.T_c - (a.ideal_ht ? 0 : v.dT_app);
    const etaC = 1 - TL / TH, wnet = cy.wt - cy.wp, mdot = v.P_net / wnet;
    const sgen = cy.qout / TL - cy.qin / TH;
    const d = dome(F, v.T_c - 15, v.T_b + 25);
    const sup = N.linspace(v.T_b, cy.T3, 12);
    const cs = [cy.s1, F.sl(cy.T2), F.sl(v.T_b), ...sup.map(T => F.sv(T, cy.pb)), cy.st4.s, ...(cy.st4.superheated ? [F.sv(v.T_c, cy.pc)] : []), cy.s1];
    const cT = [v.T_c, cy.T2, v.T_b, ...sup, cy.st4.T, ...(cy.st4.superheated ? [v.T_c] : []), v.T_c];
    const Tbs = N.linspace(Math.max(v.T_c + 25, 333.15), 633.15, 40);
    const sweep = Tbs.map(T => rankineCycle(F, T, v.dT_sh, v.T_c, etaT, etaP, pf).eta);
    const warnings = [];
    if (v.T_b > 0.9 * F.Tcrit) warnings.push(`The evaporation temperature is ${v.T_b > F.Tcrit ? 'above' : 'within 10 % of'} the critical temperature of ${F.name.toLowerCase()} (${lab(F.Tcrit - 273.15, '°C')}). The simple property model has no critical point; results here are an extrapolation.`);
    if (!cy.st4.superheated && cy.st4.x < 0.88) warnings.push(`Turbine exhaust quality is ${lab(cy.st4.x, '', 2)}: moisture above about 12 % erodes the last-stage blades. Raise the superheat or add reheat.`);
    if (!a.simple_props) warnings.push('No reference equation of state is built in. For design work use the IAPWS-IF97 steam tables or a Helmholtz-energy equation of state; the simple model typically misses condenser pressure by a few per cent, and boiler pressure and high-pressure enthalpies by considerably more (about 18 % in the saturation pressure of water at 285 °C).');
    return {
      scalars: [
        scalar('p_b', 'Boiler pressure', cy.pb, 'Pa', { show: 'bar' }), scalar('p_c', 'Condenser pressure', cy.pc, 'Pa', { show: 'kPa' }),
        scalar('T_3', 'Turbine inlet temperature', cy.T3, 'K', { show: '°C' }), scalar('w_t', 'Turbine specific work', cy.wt, 'J/kg', { show: 'kJ/kg' }),
        scalar('w_p', 'Pump specific work', cy.wp, 'J/kg', { show: 'kJ/kg' }), scalar('w_net', 'Net specific work', wnet, 'J/kg', { show: 'kJ/kg' }),
        scalar('q_in', 'Heat added', cy.qin, 'J/kg', { show: 'kJ/kg' }), scalar('q_out', 'Heat rejected', cy.qout, 'J/kg', { show: 'kJ/kg' }),
        scalar('eta', 'Thermal efficiency', cy.eta, '1', { show: '%' }), scalar('eta_C', 'Carnot efficiency between source and sink', etaC, '1', { show: '%' }),
        scalar('eta_II', 'Second-law efficiency η/η_Carnot', cy.eta / etaC, '1', { show: '%' }), scalar('bwr', 'Back-work ratio', cy.wp / cy.wt, '1', { show: '%' }),
        scalar('x_4', 'Turbine exhaust quality', cy.st4.x, '1', { text: cy.st4.superheated ? `Superheated, ${lab(cy.st4.T - 273.15, '°C')}` : undefined }),
        scalar('mdot', 'Working-fluid mass flow rate', mdot, 'kg/s'), scalar('Q_in', 'Heat input rate', mdot * cy.qin, 'W', { show: 'MW' }), scalar('Q_out', 'Heat rejection rate', mdot * cy.qout, 'W', { show: 'MW' }),
        scalar('s_gen', 'Entropy generated per kilogram of working fluid', sgen, 'J/(kg K)'),
      ],
      series: [
        line('ts', 'Temperature–entropy diagram', 'Specific entropy', 'kJ/(kg K)', d.s.map(q => q / 1000), [{ label: 'Saturation dome', data: d.T.map(q => q - 273.15), dash: true }], 'Temperature', '°C', { overlay: [{ label: 'Cycle 1–2–3–4', x: cs.map(q => q / 1000), y: cT.map(q => q - 273.15) }], note: 'Entropy is measured from saturated liquid at the normal boiling point.' }),
        line('eta-sweep', 'Efficiency against evaporation temperature', 'Evaporation temperature', '°C', Tbs.map(q => q - 273.15), [{ label: 'Cycle', data: sweep }, { label: 'Carnot limit', data: Tbs.map(T => 1 - TL / (T + v.dT_sh + (a.ideal_ht ? 0 : v.dT_app))), dash: true }], 'Efficiency', '–'),
      ],
      checks: [
        check('First law around the cycle', (cy.qin - cy.qout - wnet) / cy.qin, 1e-10, 'Net heat equals net work'),
        check('Second law: efficiency does not exceed the Carnot limit', Math.max(cy.eta / etaC - 1, 0), 1e-12, `η = ${lab(cy.eta * 100, '%')} against η_Carnot = ${lab(etaC * 100, '%')}`),
        check('Entropy generation not negative', Math.min(sgen, 0), 0, 'q_out/T_L − q_in/T_H ≥ 0'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const F = FM.water, T = 450, dT = 0.01, p = F.psat(T);
    const slope = (F.psat(T + dT) - F.psat(T - dT)) / (2 * dT), clap = (F.hv(T) - F.hl(T, p)) / (T * (F.Rs * T / p - F.vl));
    const near = rankineCycle(F, 400.5, 0, 400, 1, 1, 1);
    // reversible cycle: net work must equal ∮T ds, with the heat added evaluated from entropies rather than enthalpies
    const rev = rankineCycle(F, 500, 80, 310, 1, 1, 1);
    const qInTds = F.cl * (500 - rev.T2) + 500 * (F.sv(500, rev.pb) - F.sl(500)) + F.cpv * 80, qOutTds = 310 * (rev.s3 - rev.s1);
    return [
      bench('Saturation slope vs the Clapeyron equation', slope, clap, 'dp/dT = h_fg/[T (v_g − v_l)], exact for any consistent property model', 1e-6),
      bench('Net work of the ideal cycle vs the enclosed area ∮T ds', rev.wt - rev.wp, qInTds - qOutTds, 'First and second laws for a reversible cycle (wet exhaust): w_net = ∮T ds', 1e-9),
      bench('Cycle efficiency over Carnot as the temperature difference tends to zero', near.eta / (1 - 400 / 400.5), 1, 'Reversible limit: all heat exchanged at essentially two temperatures', 5e-3),
    ];
  },
  validation: [
    { name: 'Saturation pressure of water', ref: 'IAPWS-IF97 steam tables: p_sat(40 °C) = 7.38 kPa, p_sat(285 °C) = 6.91 MPa', note: 'Tests the simple property model only. The uncertainty quoted is a 5 % band for judging the model, far wider than that of the reference data; the model is close near the condenser and about 18 % low at 285 °C.',
      cases: [{ label: '40 °C', inputs: { T_c: 313.15 }, observable: 'p_c', observed: 7384, sigma: 400 }, { label: '285 °C', inputs: { T_b: 558.15 }, observable: 'p_b', observed: 6.915e6, sigma: 3.5e5 }] },
  ],
  diagram(v, a) {
    return svg(`
      ${S.rect(70, 60, 130, 70, 'd-body')} ${S.text(135, 100, 'boiler')}
      ${S.path('M440 70 L520 50 L520 150 L440 130 Z', 'd-body')} ${S.text(480, 104, 'turbine')}
      ${S.rect(410, 240, 140, 60, 'd-body')} ${S.text(480, 275, 'condenser')}
      ${S.circle(135, 270, 26)} ${S.text(135, 275, 'pump')}
      ${S.path('M200 80 L440 80', 'd-pipe')} ${S.path('M500 146 L500 240', 'd-pipe')} ${S.path('M410 270 L161 270', 'd-pipe')} ${S.path('M135 244 L135 130', 'd-pipe')}
      ${S.arrow(300, 66, 360, 66)} ${S.text(320, 56, `3: ${lab(v.T_b + v.dT_sh - 273.15, '°C')}`)}
      ${S.text(540, 200, '4', 'd-text')} ${S.text(290, 262, `1: ${lab(v.T_c - 273.15, '°C')}`)} ${S.text(120, 190, '2', 'd-text')}
      ${S.arrow(30, 95, 68, 95, 'd-arrow d-heat')} ${S.text(34, 82, 'Q in', 'd-text d-small')}
      ${S.arrow(552, 270, 600, 270, 'd-arrow d-heat')} ${S.text(590, 258, 'Q out', 'd-text d-small')}
      ${S.arrow(522, 100, 590, 100)} ${S.text(575, 90, 'W', 'd-text d-small')}
      ${S.text(320, 340, `working fluid: ${a.water ? 'water' : 'n-pentane'}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the heat input, heat rejection and shaft power of a small Rankine or organic Rankine rig and compare the efficiency with the cycle prediction and the Carnot limit.',
    apparatus: ['Electrically heated evaporator with superheater', 'Small turbine or scroll expander coupled to a dynamometer or generator', 'Water-cooled condenser and feed pump', 'Lagged pipework'],
    instruments: [{ name: 'Pressure transducers at the four state points', measures: 'Cycle pressures', range: '0–100 bar', resolution: '±0.1 %' }, { name: 'Pt100 probes at the four state points', measures: 'Cycle temperatures', range: '0–550 °C', resolution: '±0.2 K' }, { name: 'Coriolis flow meter on the liquid line', measures: 'Working-fluid flow', range: '0–1 kg/s', resolution: '±0.1 %' }, { name: 'Torque and speed transducer', measures: 'Shaft power', range: '0–50 kW', resolution: '±0.5 %' }, { name: 'Cooling-water flow and temperature rise', measures: 'Heat rejected', range: '—', resolution: '±2 %' }],
    procedure: ['Bring the rig to steady state at a fixed evaporation pressure and superheat.', 'Record all pressures, temperatures, flow, electrical heat input and shaft power.', 'Close the energy balance: heat in minus heat out against shaft power plus measured losses.', 'Repeat at several evaporation temperatures and condenser temperatures.'],
    controls: ['Energy-balance closure within 3 % before accepting a point', 'Electrical heater calibration with the loop bypassed'],
    signatures: ['Efficiency rising with evaporation temperature and falling with condenser temperature', 'Back-work ratio of order one per cent for water, several per cent for organic fluids', 'Efficiency always below 1 − T_L/T_H'],
    safety: ['Pressure system: relief valves, written scheme of examination', 'Steam and hot-surface burns', 'Flammable organic fluids: leak detection, ventilation and ignition control'],
  },
  falsify: ['A measured efficiency above the Carnot value for the measured source and sink temperatures.', 'An energy balance that fails to close by more than the measurement uncertainty.'],
  alternatives: [{ name: 'Reheat and regenerative cycles', text: 'Reheat limits exhaust moisture; feed-water heating raises the mean temperature of heat addition and the efficiency.' }, { name: 'Supercritical cycles', text: 'Above the critical pressure there is no boiling plateau; a real-fluid equation of state is essential.' }, { name: 'Kalina cycle', text: 'An ammonia–water mixture boils over a temperature range, matching a sensible heat source more closely than a pure fluid.' }],
  hazards: [{ hazard: 'Loss of containment of high-pressure steam', cause: 'Tube failure, overpressure', mitigation: 'Relief valves, inspection, water-chemistry control' }, { hazard: 'Turbine overspeed', cause: 'Loss of load', mitigation: 'Independent overspeed trip' }, { hazard: 'Fire and explosion with organic fluids', cause: 'Leak of flammable vapour', mitigation: 'Hazardous-area classification, gas detection' }],
  standards: ['ASME Boiler and Pressure Vessel Code, Section I (power boilers)', 'ASME PTC 6 (steam turbine performance test code)', 'EN 12952 (water-tube boilers)', 'IAPWS-IF97 (industrial formulation for water and steam properties)'],
  limits: 'Simple subcritical cycle without reheat or regeneration. The property model assumes ideal-gas vapour and constant specific heats: for water its saturation pressure is within a few per cent at condenser temperatures but about 18 % low at 285 °C, so boiler pressures and high-pressure enthalpies are indicative only, and it is invalid near the critical point.',
  numerics: { method: 'Closed-form state-point evaluation; fixed-point iteration for the saturation pressure' },
  optimise: { objective: 'eta', sense: 'max', vars: ['T_b', 'dT_sh'], note: 'Efficiency rises monotonically with peak temperature; material limits set the practical optimum.' },
  inverse: { series: 'eta-sweep', curve: 0, fit: ['eta_t'] },
  extensions: ['Reheat and open or closed feed-water heaters', 'Real-fluid properties from a reference equation of state', 'Heat-source matching and pinch analysis for binary plants', 'Part-load turbine performance'],
};

// ------------------------------------------------------------------ vapour-compression refrigeration
function vcCycle(F, Te, Tk, etaC, expander) {
  const pe = F.psat(Te), pk = F.psat(Tk);
  const h1 = F.hv(Te), s1 = F.sv(Te, pe), st2s = F.atEntropy(s1, Tk, pk), wc = (st2s.h - h1) / etaC, st2 = F.atEnthalpy(h1 + wc, Tk, pk);
  const h3 = F.hl(Tk, pk), s3 = F.sl(Tk), st4 = expander ? F.atEntropy(s3, Te, pe) : F.atEnthalpy(h3, Te, pe);
  const wx = h3 - st4.h, qL = h1 - st4.h, qH = st2.h - h3, w = wc - wx;
  return { pe, pk, h1, s1, st2, st2s, h3, s3, st4, wc, wx, w, qL, qH, cop: qL / w };
}

const refrigeration = {
  id: 'refrigeration-cycle',
  title: 'Vapour-compression refrigeration cycle',
  module: 2, klass: 'I', domains: ['thermal'],
  keywords: ['refrigeration cycle', 'vapour compression', 'vapor compression', 'refrigeration', 'refrigerator', 'heat pump', 'cop', 'coefficient of performance', 'compressor', 'evaporator', 'condenser', 'cascade', 'chiller', 'r134a', 'ammonia'],
  summary: 'Coefficient of performance, compressor power and state points of a single-stage or cascade vapour-compression cycle, compared with the Carnot limit.',
  background: [
    'A vapour-compression refrigerator moves heat from a cold space to warmer surroundings by evaporating a refrigerant at low pressure, compressing the vapour, condensing it at high pressure and throttling the liquid back to the evaporator. Its coefficient of performance (COP) is the heat removed per unit of work supplied.',
    'The second law bounds the COP of any refrigerator working between T_L and T_H by the Carnot value T_L/(T_H − T_L). Real cycles fall short because of compressor losses, the superheat of the compressor discharge and the irreversible throttling process. When the temperature lift is large, two cycles in cascade each work over a smaller pressure ratio and recover part of that loss.',
  ],
  phenomena: ['Evaporation at low pressure', 'Compression of vapour', 'Desuperheating and condensation', 'Throttling (Joule–Thomson expansion with flashing)'],
  laws: ['energy', 'second', 'ideal_gas'],
  refs: ['Moran, M. J., Shapiro, H. N., Boettner, D. D. & Bailey, M. B. (2014). Fundamentals of Engineering Thermodynamics, 8th ed., Wiley.', 'Stoecker, W. F. & Jones, J. W. (1982). Refrigeration and Air Conditioning, 2nd ed., McGraw-Hill.', 'ASHRAE (2021). ASHRAE Handbook — Fundamentals. American Society of Heating, Refrigerating and Air-Conditioning Engineers.'],
  inputs: [
    inp('T_e', 'Evaporating temperature', '°C', -10, { min: -40, max: 10, aliases: ['evaporator temperature', 'evaporating temperature', 'cold temperature'] }),
    inp('T_k', 'Condensing temperature', '°C', 40, { min: 25, max: 70, aliases: ['condenser temperature', 'condensing temperature', 'hot temperature'] }),
    inp('eta_c', 'Compressor isentropic efficiency', '1', 0.75, { min: 0.4, max: 1, aliases: ['compressor efficiency', 'isentropic efficiency'] }),
    inp('Q_L', 'Cooling capacity', 'kW', 10, { min: 0.05, max: 5000, aliases: ['cooling capacity', 'refrigeration capacity', 'cooling load', 'duty'] }),
    inp('dT_casc', 'Temperature difference in the cascade heat exchanger', 'K', 5, { min: 1, max: 15, aliases: ['cascade approach'] }),
  ],
  assumptions: [
    asm('r134a', 'The refrigerant is R134a.', { why: 'Common medium-temperature refrigerant', alt: 'The refrigerant is ammonia (R717).' }),
    asm('single_stage', 'The cycle has a single stage of compression.', { why: 'Moderate temperature lift', alt: 'Two cycles in cascade share the lift, meeting in a heat exchanger at the geometric-mean temperature.' }),
    asm('real_comp', 'The compressor has the stated isentropic efficiency.', { why: 'Realistic machine', alt: 'Compression is isentropic.' }),
    asm('throttle', 'Expansion is through a throttling valve at constant enthalpy.', { why: 'Universal practice: cheap and reliable', alt: 'An ideal isentropic expander replaces the valve and its work offsets the compressor work.' }),
  ],
  symbols: { p_e: ['Evaporating pressure', 'Pa'], p_k: ['Condensing pressure', 'Pa'], h_1: ['Enthalpy, compressor suction', 'J/kg'], h_2: ['Enthalpy, compressor discharge', 'J/kg'], h_2s: ['Enthalpy after isentropic compression', 'J/kg'], h_3: ['Enthalpy, condenser outlet', 'J/kg'], h_4: ['Enthalpy, evaporator inlet', 'J/kg'], s_3: ['Entropy, condenser outlet', 'J/(kg K)'], s_4: ['Entropy, evaporator inlet', 'J/(kg K)'], w_c: ['Compressor work', 'J/kg'], w_x: ['Expander work', 'J/kg'], q_L: ['Refrigerating effect', 'J/kg'], q_H: ['Heat rejected', 'J/kg'], COP: ['Coefficient of performance', '1'], COP_C: ['Carnot coefficient of performance', '1'], COP_lo: ['COP of the low stage', '1'], COP_hi: ['COP of the high stage', '1'], mdot: ['Refrigerant mass flow rate', 'kg/s'], T_m: ['Cascade intermediate temperature', 'K'] },
  equations: a => [
    a.real_comp ? eq('wc', 'Compressor work', 'w_c', '(h_2s - h_1)/eta_c', { kind: 'law', origin: 'First law with the definition of isentropic efficiency', needs: ['real_comp'] }) : eq('wc', 'Compressor work', 'w_c', 'h_2s - h_1', { kind: 'law', origin: 'First law, isentropic compressor' }),
    eq('h2', 'Discharge enthalpy', 'h_2', 'h_1 + w_c', { kind: 'law', origin: 'First law, adiabatic compressor' }),
    a.throttle ? eq('exp', 'Throttling', 'h_4', 'h_3', { kind: 'law', origin: 'First law for an adiabatic valve with no work', needs: ['throttle'] }) : eq('exp', 'Isentropic expansion', 's_4', 's_3', { kind: 'law', origin: 'Second law for a reversible adiabatic expander' }),
    ...(a.throttle ? [] : [eq('wx', 'Expander work', 'w_x', 'h_3 - h_4', { kind: 'law', origin: 'First law, adiabatic expander' })]),
    eq('ql', 'Refrigerating effect', 'q_L', 'h_1 - h_4', { kind: 'law', origin: 'First law, evaporator' }),
    eq('qh', 'Heat rejected', 'q_H', 'h_2 - h_3', { kind: 'law', origin: 'First law, condenser' }),
    ...(a.single_stage
      ? [eq('cop', 'Coefficient of performance', 'COP', a.throttle ? 'q_L/w_c' : 'q_L/(w_c - w_x)', { kind: 'definition', needs: ['single_stage'] })]
      : [eq('tm', 'Cascade intermediate temperature', 'T_m', 'sqrt(T_e*T_k)', { kind: 'closure', origin: 'Equal temperature ratio per stage' }), eq('cop', 'Cascade coefficient of performance', 'COP', '1/(1/COP_lo + (1 + 1/COP_lo)/COP_hi)', { kind: 'derived', origin: 'Energy balance across the cascade heat exchanger' })]),
    eq('carnot', 'Carnot limit', 'COP_C', 'T_e/(T_k - T_e)', { kind: 'law', origin: 'Second law of thermodynamics' }),
    eq('m', 'Refrigerant flow', 'mdot', 'Q_L/q_L', { kind: 'derived' }),
  ],
  derivation: a => [
    { text: 'The evaporator absorbs heat at T_e; the first law gives the refrigerating effect as the enthalpy rise of the refrigerant.', tex: 'q_L = h_1 - h_4' },
    { text: 'The compressor raises the vapour from p_e to p_k. An ideal machine is isentropic; a real one needs more work in the ratio of its isentropic efficiency.', tex: 'w_c = \\frac{h_{2s}-h_1}{\\eta_c}' },
    { text: a.throttle ? 'Throttling is adiabatic and does no work, so enthalpy is conserved; part of the liquid flashes and that part does no useful cooling.' : 'An isentropic expander recovers work from the liquid, lowering both the net work and the flash fraction.', tex: a.throttle ? 'h_4 = h_3' : 's_4 = s_3,\\quad w_x = h_3 - h_4' },
    { text: 'The coefficient of performance is the ratio of heat removed to net work.', tex: '\\mathrm{COP} = \\frac{q_L}{w}' },
    ...(a.single_stage ? [] : [{ text: 'In a cascade the low stage rejects q_L(1 + 1/COP_lo) to the high stage, which needs work in proportion.', tex: '\\mathrm{COP} = \\left[\\frac{1}{\\mathrm{COP}_{lo}} + \\frac{1 + 1/\\mathrm{COP}_{lo}}{\\mathrm{COP}_{hi}}\\right]^{-1}' }]),
    { text: 'For a cyclic device exchanging heat only at T_L and T_H the Clausius inequality gives the Carnot bound.', tex: '\\frac{q_L}{T_L} - \\frac{q_H}{T_H} \\le 0 \;\\Rightarrow\; \\mathrm{COP} \\le \\frac{T_L}{T_H - T_L}' },
  ],
  solve(v, a) {
    const F = a.r134a ? FM.r134a : FM.ammonia, etaC = a.real_comp ? v.eta_c : 1, ex = !a.throttle;
    const one = vcCycle(F, v.T_e, v.T_k, etaC, ex);
    const copOf = (Te, Tk) => {
      if (a.single_stage) return vcCycle(F, Te, Tk, etaC, ex).cop;
      const Tm = Math.sqrt(Te * Tk), lo = vcCycle(F, Te, Tm + v.dT_casc / 2, etaC, ex).cop, hi = vcCycle(F, Tm - v.dT_casc / 2, Tk, etaC, ex).cop;
      return 1 / (1 / lo + (1 + 1 / lo) / hi);
    };
    const Tm = Math.sqrt(v.T_e * v.T_k);
    const lo = a.single_stage ? one : vcCycle(F, v.T_e, Tm + v.dT_casc / 2, etaC, ex), hi = a.single_stage ? null : vcCycle(F, Tm - v.dT_casc / 2, v.T_k, etaC, ex);
    const cop = copOf(v.T_e, v.T_k), copC = v.T_e / (v.T_k - v.T_e), W = v.Q_L / cop, mdot = v.Q_L / lo.qL;
    const mHi = hi ? mdot * lo.qH / hi.qL : 0, QH = hi ? mHi * hi.qH : mdot * lo.qH;
    const d = dome(F, v.T_e - 15, v.T_k + 20);
    const path = (c, Te, Tk) => {
      const des = c.st2.superheated ? N.linspace(c.st2.T, Tk, 8) : [Tk];
      return { s: [c.s1, ...des.map((T, i) => (c.st2.superheated ? F.sv(T, c.pk) : c.st2.s)), c.s3, c.st4.s, c.s1], T: [Te, ...des, Tk, Te, Te] };
    };
    const p1 = path(lo, v.T_e, a.single_stage ? v.T_k : Tm + v.dT_casc / 2), p2 = hi ? path(hi, Tm - v.dT_casc / 2, v.T_k) : null;
    const Tes = N.linspace(233.15, Math.min(283.15, v.T_k - 12), 40);
    const warnings = [];
    if (lo.pe < 101325) warnings.push(`The evaporating pressure (${lab(lo.pe / 1000, 'kPa')}) is below atmospheric: air and moisture can leak into the low side.`);
    if (lo.st2.T > 393.15 || (hi && hi.st2.T > 393.15)) warnings.push('Compressor discharge temperature exceeds 120 °C: oil breakdown is likely. Consider two stages or a different refrigerant.');
    if (v.T_k > 0.9 * F.Tcrit) warnings.push('The condensing temperature approaches the critical temperature; the simple property model is unreliable there.');
    return {
      scalars: [
        scalar('p_e', 'Evaporating pressure', lo.pe, 'Pa', { show: 'bar' }), scalar('p_k', 'Condensing pressure', (hi || lo).pk, 'Pa', { show: 'bar' }),
        scalar('r_p', a.single_stage ? 'Pressure ratio' : 'Pressure ratio of the low stage', lo.pk / lo.pe, '1'),
        scalar('T_2', 'Compressor discharge temperature' + (a.single_stage ? '' : ' (high stage)'), (hi || lo).st2.T, 'K', { show: '°C' }),
        scalar('x_4', 'Flash-gas fraction at evaporator inlet', lo.st4.x, '1', { show: '%' }),
        scalar('q_L', 'Refrigerating effect', lo.qL, 'J/kg', { show: 'kJ/kg' }), scalar('w_c', 'Compressor specific work' + (a.single_stage ? '' : ' (low stage)'), lo.wc, 'J/kg', { show: 'kJ/kg' }),
        scalar('COP', 'Coefficient of performance', cop, '1'), scalar('COP_C', 'Carnot coefficient of performance', copC, '1'), scalar('eta_II', 'Second-law efficiency COP/COP_Carnot', cop / copC, '1', { show: '%' }),
        scalar('W', 'Net power input', W, 'W', { show: 'kW' }), scalar('Q_H', 'Heat rejected', QH, 'W', { show: 'kW' }), scalar('mdot', 'Refrigerant mass flow rate' + (a.single_stage ? '' : ' (low stage)'), mdot, 'kg/s'),
        scalar('COP_hp', 'Heating COP if used as a heat pump', QH / W, '1'),
      ],
      series: [
        line('cop-sweep', 'COP against evaporating temperature', 'Evaporating temperature', '°C', Tes.map(q => q - 273.15), [{ label: a.single_stage ? 'Cycle' : 'Cascade cycle', data: Tes.map(T => copOf(T, v.T_k)) }, { label: 'Carnot limit', data: Tes.map(T => T / (v.T_k - T)), dash: true }], 'COP', '–'),
        line('ts', 'Temperature–entropy diagram', 'Specific entropy', 'kJ/(kg K)', d.s.map(q => q / 1000), [{ label: 'Saturation dome', data: d.T.map(q => q - 273.15), dash: true }], 'Temperature', '°C', { overlay: [{ label: a.single_stage ? 'Cycle 1–2–3–4' : 'Low stage', x: p1.s.map(q => q / 1000), y: p1.T.map(q => q - 273.15) }, ...(p2 ? [{ label: 'High stage', x: p2.s.map(q => q / 1000), y: p2.T.map(q => q - 273.15) }] : [])] }),
      ],
      checks: [
        check('First law: heat rejected equals heat absorbed plus work', (QH - v.Q_L - W) / QH, 1e-10, 'Q_H = Q_L + W'),
        check('Second law: COP does not exceed the Carnot COP', Math.max(cop / copC - 1, 0), 1e-12, `COP = ${lab(cop)} against COP_Carnot = ${lab(copC)}`),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const F = FM.r134a, T = 270, dT = 0.01, p = F.psat(T);
    const near = vcCycle(F, 280, 280.5, 1, true);
    return [
      bench('Saturation slope vs the Clapeyron equation', (F.psat(T + dT) - F.psat(T - dT)) / (2 * dT), (F.hv(T) - F.hl(T, p)) / (T * (F.Rs * T / p - F.vl)), 'dp/dT = h_fg/[T (v_g − v_l)]', 1e-6),
      bench('Reversible cycle COP over Carnot as the lift tends to zero', near.cop / (280 / 0.5), 1, 'Reversible limit with isentropic compressor and expander', 5e-3),
      bench('Normal boiling point of the refrigerant model', F.psat(247.08), 101325, 'Reference state of the property model', 1e-10),
    ];
  },
  validation: [
    { name: 'Saturation pressure of R134a', ref: 'Tillner-Roth, R. & Baehr, H. D. (1994). J. Phys. Chem. Ref. Data 23, 657–729, as tabulated in the ASHRAE Handbook — Fundamentals: 200.6 kPa at −10 °C and 1016.6 kPa at 40 °C', note: 'Tests the simple property model only. The uncertainty quoted is a 5 % band for judging the model, far wider than that of the reference data; the model is close at the evaporator and about 15 % low at 40 °C.',
      cases: [{ label: '−10 °C', inputs: { T_e: 263.15 }, observable: 'p_e', observed: 2.006e5, sigma: 1.0e4 }, { label: '40 °C', inputs: { T_k: 313.15 }, observable: 'p_k', observed: 1.0166e6, sigma: 5.1e4 }] },
  ],
  diagram(v, a) {
    return svg(`
      ${S.rect(220, 50, 200, 50, 'd-body')} ${S.text(320, 80, `condenser ${lab(v.T_k - 273.15, '°C')}`)}
      ${S.rect(220, 250, 200, 50, 'd-body')} ${S.text(320, 280, `evaporator ${lab(v.T_e - 273.15, '°C')}`)}
      ${S.circle(500, 175, 30)} ${S.text(500, 180, 'comp.')}
      ${S.path('M120 160 L150 190 L120 190 L150 160 Z', 'd-body')} ${S.text(135, 215, a.throttle ? 'valve' : 'expander', 'd-text d-small')}
      ${S.path('M420 275 L500 275 L500 205', 'd-pipe')} ${S.path('M500 145 L500 75 L420 75', 'd-pipe')} ${S.path('M220 75 L135 75 L135 160', 'd-pipe')} ${S.path('M135 190 L135 275 L220 275', 'd-pipe')}
      ${S.text(515, 262, '1')} ${S.text(515, 96, '2')} ${S.text(120, 96, '3')} ${S.text(120, 262, '4')}
      ${[0, 1, 2].map(i => S.arrow(270 + i * 50, 48, 270 + i * 50, 14, 'd-arrow d-heat')).join('')} ${S.text(450, 30, 'Q_H')}
      ${[0, 1, 2].map(i => S.arrow(270 + i * 50, 340, 270 + i * 50, 304, 'd-arrow d-heat')).join('')} ${S.text(450, 330, 'Q_L')}
      ${S.arrow(590, 175, 534, 175)} ${S.text(585, 162, 'W')}
      ${S.text(320, 180, `${a.r134a ? 'R134a' : 'ammonia'}${a.single_stage ? '' : ', cascade'}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the cooling capacity, compressor power and state points of a refrigeration test rig and compare the COP with the cycle prediction and the Carnot limit.',
    apparatus: ['Instrumented vapour-compression rig with electrically heated evaporator (calorimeter)', 'Water-cooled condenser with metered flow', 'Variable-speed compressor', 'Sight glasses before the expansion device'],
    instruments: [{ name: 'Pressure transducers at suction and discharge', measures: 'Evaporating and condensing pressure', range: '0–30 bar', resolution: '±0.25 %' }, { name: 'Thermocouples or Pt100 at the four state points', measures: 'Refrigerant temperatures', range: '−50 to 150 °C', resolution: '±0.3 K' }, { name: 'Coriolis flow meter in the liquid line', measures: 'Refrigerant flow', range: '0–0.2 kg/s', resolution: '±0.2 %' }, { name: 'Power analyser', measures: 'Compressor electrical input', range: '0–10 kW', resolution: '±0.5 %' }],
    procedure: ['Run to steady state at a set evaporating and condensing pressure.', 'Record pressures, temperatures, flow, evaporator heater power and compressor power.', 'Compute the COP from the heater power and compressor shaft power; cross-check with the refrigerant-side enthalpy balance.', 'Repeat over a range of evaporating temperatures.'],
    controls: ['Condenser-side heat balance as an independent check of Q_L + W', 'Check for liquid at the valve inlet through the sight glass'],
    signatures: ['COP falling as the temperature lift increases', 'COP below T_L/(T_H − T_L) at every point', 'Discharge temperature rising with pressure ratio'],
    safety: ['Refrigerant release: ventilation and leak detection', 'Ammonia is toxic and mildly flammable: gas detection and emergency ventilation', 'High-pressure cut-out and relief valve on the high side'],
  },
  falsify: ['A measured COP above the Carnot value for the measured evaporating and condensing temperatures.', 'Heat rejected not equal to heat absorbed plus work within the measurement uncertainty.'],
  alternatives: [{ name: 'Absorption refrigeration', text: 'Uses heat instead of shaft work to drive the cycle, with a lower COP based on heat input.' }, { name: 'Transcritical CO₂ cycle', text: 'Heat rejection takes place above the critical pressure in a gas cooler; the COP then depends on an optimum high-side pressure.' }, { name: 'Two-stage compression with flash intercooling', text: 'A single refrigerant with an economiser between stages; simpler than a cascade when one fluid spans the whole lift.' }],
  hazards: [{ hazard: 'Refrigerant release', cause: 'Leak or relief-valve discharge', mitigation: 'Leak detection, ventilation, charge limits' }, { hazard: 'Liquid slugging of the compressor', cause: 'Wet suction', mitigation: 'Suction superheat control, accumulator' }, { hazard: 'Overpressure on standstill', cause: 'High ambient temperature with trapped liquid', mitigation: 'Relief devices on every isolable section' }],
  standards: ['EN 378 (refrigerating systems and heat pumps — safety and environmental requirements)', 'ISO 5149 (refrigerating systems and heat pumps — safety and environmental requirements)', 'ASHRAE Standard 15 (safety standard for refrigeration systems)', 'ISO 817 (refrigerants — designation and safety classification)'],
  limits: 'Saturated suction and saturated liquid at the condenser outlet, no pressure drops. The property model assumes ideal-gas vapour and constant specific heats; expect errors of several per cent in COP, condensing pressures up to about 15 % low at 40 °C, and larger errors near the critical temperature. Because the model vapour of R134a is an ideal gas, isentropic compression from saturation ends slightly wet instead of superheated, so its discharge temperatures are under-predicted; the ammonia model superheats as the real fluid does.',
  numerics: { method: 'Closed-form state-point evaluation; fixed-point iteration for the saturation pressure' },
  optimise: { objective: 'COP', sense: 'max', vars: ['T_e', 'T_k'], note: 'COP is highest at the smallest lift; the practical limits are the required cold-space temperature and the available heat sink.' },
  inverse: { series: 'cop-sweep', curve: 0, fit: ['eta_c'] },
  extensions: ['Suction superheat and liquid subcooling', 'Liquid–suction heat exchanger', 'Real-fluid properties from a reference equation of state', 'Compressor volumetric efficiency and displacement sizing'],
};

// ------------------------------------------------------------------ compressed-air vehicle
const AIR = { Rs: 287.05, gamma: 1.4, cp: 1004.7, cv: 717.6, M: 0.0289647, vdwA: 0.1358, vdwB: 3.64e-5 };
/** Maximum useful work of a tank of gas at ambient temperature discharging to the atmosphere (its exergy). */
const tankExergy = (p, p0, V) => p * V * Math.log(p / p0) - (p - p0) * V;
/** Shaft work when tank and expander are both adiabatic and reversible: every parcel leaves at T_0 (p_0/p)^κ. */
function tankAdiabaticWork(p, p0, V, T0, m) {
  const kap = (AIR.gamma - 1) / AIR.gamma, Te = T0 * Math.pow(p0 / p, kap);
  return { W: m * AIR.cv * (T0 - Te) - m * AIR.Rs * Te + p0 * V, Te };
}
/** Stored mass from the van der Waals equation for air. */
function vdwMass(p, T, V) {
  const f = vm => (p + AIR.vdwA / (vm * vm)) * (vm - AIR.vdwB) - C.R_u * T;
  const vm = N.findRoot(f, AIR.vdwB * (1 + 1e-9), 10 * C.R_u * T / p + 2 * AIR.vdwB, 1e-13);
  return V / vm * AIR.M;
}

const airCar = {
  id: 'compressed-air-vehicle',
  title: 'Vehicle driven by stored compressed air',
  module: [1, 2], klass: ['I', 'II'], domains: ['mechanical', 'thermal'],
  keywords: ['compressed air vehicle', 'compressed air car', 'air car', 'air powered', 'air-powered', 'pneumatic vehicle', 'compressed air', 'air engine', 'air tank', 'self-recharging', 'recompress', 'runs on air', 'pneumatic motor', 'range', 'top speed'],
  summary: 'Stored energy, range and top speed of a vehicle whose only on-board energy store is a tank of compressed air, with a thermodynamic audit of the claim that it can recharge itself while driving.',
  background: [
    'A compressed-air vehicle carries a pressure vessel charged by an external compressor and expands the air through a piston or vane motor. The most work a tank at ambient temperature can deliver is its exergy, p V ln(p/p₀) − (p − p₀) V, obtained only if the expansion is slow enough to stay isothermal. In a fast, adiabatic expansion the air cools steeply, delivers much less work and can ice the motor.',
    'Ambient air is the working fluid of such a vehicle, not its energy source. Air at atmospheric pressure and temperature is in equilibrium with the surroundings and has zero exergy: no work can be extracted from it. During an isothermal expansion the motor does draw heat from the surroundings, but only as much as the compressor rejected when the tank was filled; the work originates in the compressor’s energy supply.',
    'It follows that a vehicle which recompresses its own air while driving cannot sustain itself. Each joule of work taken from the tank returns less than a joule of stored exergy after expander and compressor losses, and even with ideal machines the return is exactly one joule with nothing left to overcome drag and rolling resistance. The first law forbids a net gain; the second law guarantees a net loss.',
  ],
  phenomena: ['Isothermal and adiabatic gas expansion', 'Cooling on expansion', 'Aerodynamic drag', 'Rolling resistance', 'Irreversibility of compression and expansion'],
  laws: ['energy', 'second', 'ideal_gas', 'newton2'],
  refs: ['Moran, M. J., Shapiro, H. N., Boettner, D. D. & Bailey, M. B. (2014). Fundamentals of Engineering Thermodynamics, 8th ed., Wiley.', 'Creutzig, F., Papson, A., Schipper, L. & Kammen, D. M. (2009). Economic and environmental evaluation of compressed-air cars. Environmental Research Letters 4, 044011.', 'Bossel, U. (2005). Thermodynamic analysis of compressed air vehicle propulsion. European Fuel Cell Forum report.', 'MacKay, D. J. C. (2009). Sustainable Energy — Without the Hot Air. UIT Cambridge.', 'Gillespie, T. D. (1992). Fundamentals of Vehicle Dynamics. SAE International.'],
  inputs: [
    inp('V_tank', 'Tank volume', 'L', 300, { min: 50, max: 2000, kind: 'geometry', aliases: ['tank volume', 'tank', 'litre', 'litres'] }),
    inp('p_tank', 'Tank pressure when full', 'bar', 300, { min: 20, max: 450, aliases: ['tank pressure', 'storage pressure', 'pressure'] }),
    inp('p_0', 'Atmospheric pressure', 'bar', 1.01325, { min: 0.6, max: 1.1, kind: 'environment', env: 'air_pressure', aliases: ['atmospheric pressure', 'ambient pressure'] }),
    inp('T_0', 'Ambient temperature', '°C', 20, { min: -30, max: 50, kind: 'environment', env: 'air_temp', aliases: ['ambient temperature', 'air temperature'] }),
    inp('rho_air', 'Ambient air density', 'kg/m^3', 1.2, { min: 0.7, max: 1.5, kind: 'environment', env: 'air_density', aliases: ['air density'] }),
    inp('eta_exp', 'Expander efficiency, tank exergy to wheels', '1', 0.55, { min: 0.1, max: 0.95, aliases: ['expander efficiency', 'motor efficiency', 'engine efficiency'], src: 'Typical of piston air motors including drivetrain; Creutzig et al. (2009)' }),
    inp('eta_comp', 'Compressor efficiency, work to stored exergy', '1', 0.6, { min: 0.2, max: 0.95, aliases: ['compressor efficiency', 'compression efficiency'], src: 'Multi-stage intercooled compressor to 300 bar, typical 50–65 %' }),
    inp('m_veh', 'Vehicle mass including occupants', 'kg', 900, { min: 200, max: 3000, kind: 'geometry', aliases: ['mass', 'weight', 'vehicle mass'] }),
    inp('CdA', 'Drag area C_d·A', 'm^2', 0.6, { min: 0.2, max: 2, kind: 'geometry', aliases: ['drag area', 'cda'] }),
    inp('C_rr', 'Rolling-resistance coefficient', '1', 0.01, { min: 0.004, max: 0.03, aliases: ['rolling resistance'] }),
    inp('v_c', 'Cruise speed', 'kph', 60, { min: 10, max: 150, aliases: ['cruise speed', 'speed', 'cruising'] }),
    inp('P_max', 'Rated motor power at the wheels', 'kW', 25, { min: 2, max: 200, aliases: ['motor power', 'rated power', 'engine power'] }),
    inp('phi', 'Fraction of wheel power diverted to an on-board compressor (self-recharging case)', '1', 0.3, { min: 0, max: 0.95, aliases: ['recompression fraction'] }),
  ],
  assumptions: [
    asm('isothermal', 'Expansion is isothermal: heat exchangers keep the air at ambient temperature.', { why: 'Upper bound on work; approached with multi-stage expansion and reheating', alt: 'Tank and expander are adiabatic: the air cools as it expands and delivers less work.' }),
    asm('ideal_gas', 'Air in the tank is an ideal gas.', { why: 'Simple and adequate below about 100 bar', alt: 'Stored mass comes from the van der Waals equation; stored work is scaled in proportion to mass.' }),
    asm('external_recharge', 'The tank is recharged only from an external compressor while the vehicle is stationary.', { why: 'The only arrangement that works', alt: 'An on-board compressor driven from the wheels recompresses air while driving (the self-recharging claim).' }),
    asm('steady_cruise', 'Range is evaluated at constant speed on a level road.', { why: 'Standard comparison basis', alt: 'A stop every 500 m with no energy recovery adds the kinetic energy lost in each stop.' }),
  ],
  symbols: { X: ['Tank exergy (maximum work)', 'J'], W_gas: ['Gross isothermal expansion work', 'J'], W_ad: ['Adiabatic expansion work', 'J'], m_air: ['Mass of stored air', 'kg'], R_s: ['Specific gas constant of air', 'J/(kg K)'], c_v: ['Specific heat of air at constant volume', 'J/(kg K)'], T_e: ['Exhaust temperature after adiabatic expansion', 'K'], E_w: ['Work delivered at the wheels', 'J'], F_r: ['Road load', 'N'], R_range: ['Range', 'm'], v_top: ['Top speed', 'm/s'], E_in: ['External energy to recharge', 'J'], W_loop: ['Net work of an expand–recompress loop', 'J'], d_stop: ['Distance between stops', 'm'], Z: ['Compressibility factor', '1'] },
  equations: a => [
    eq('mass', 'Stored mass', 'm_air', a.ideal_gas ? 'p_tank*V_tank/(R_s*T_0)' : 'p_tank*V_tank/(Z*R_s*T_0)', { kind: 'closure', origin: a.ideal_gas ? 'Ideal-gas equation of state' : 'van der Waals equation of state, expressed through Z', needs: a.ideal_gas ? ['ideal_gas'] : [] }),
    eq('gross', 'Gross isothermal expansion work', 'W_gas', a.ideal_gas ? 'p_tank*V_tank*ln(p_tank/p_0)' : 'p_tank*V_tank*ln(p_tank/p_0)/Z', { kind: 'derived', origin: a.ideal_gas ? 'Integral of p dV at constant temperature' : 'Ideal-gas integral of p dV at constant temperature, scaled by the stored mass' }),
    eq('exergy', 'Tank exergy', 'X', a.ideal_gas ? 'p_tank*V_tank*ln(p_tank/p_0) - (p_tank - p_0)*V_tank' : '(p_tank*V_tank*ln(p_tank/p_0) - (p_tank - p_0)*V_tank)/Z', { kind: 'law', origin: 'First and second laws: maximum work relative to the atmosphere' + (a.ideal_gas ? '' : ', scaled by the stored mass') }),
    ...(a.isothermal ? [eq('ew', 'Work at the wheels', 'E_w', 'eta_exp*X', { kind: 'definition', needs: ['isothermal'] })] : [
      eq('te', 'Adiabatic exhaust temperature', 'T_e', 'T_0*(p_0/p_tank)^0.2857', { kind: 'law', origin: 'Isentropic relation for air, (γ − 1)/γ = 0.2857' }),
      eq('wad', 'Adiabatic expansion work', 'W_ad', a.ideal_gas ? 'm_air*c_v*(T_0 - T_e) - m_air*R_s*T_e + p_0*V_tank' : 'm_air*c_v*(T_0 - T_e) - m_air*R_s*T_e + p_0*V_tank/Z', { kind: 'law', origin: 'First law for the tank contents expanding to atmospheric pressure' + (a.ideal_gas ? '' : '; ideal-gas result scaled by the stored mass') }),
      eq('ew', 'Work at the wheels', 'E_w', 'eta_exp*W_ad', { kind: 'definition' })]),
    eq('road', 'Road load', 'F_r', a.steady_cruise ? '0.5*rho_air*CdA*v_c^2 + C_rr*m_veh*g' : '0.5*rho_air*CdA*v_c^2 + C_rr*m_veh*g + 0.5*m_veh*v_c^2/d_stop', { kind: 'law', origin: 'Force balance at constant speed' + (a.steady_cruise ? '' : ' plus kinetic energy dissipated per stop'), needs: a.steady_cruise ? ['steady_cruise'] : [] }),
    eq('range', 'Range', 'R_range', a.external_recharge ? 'E_w/F_r' : '(1 - phi)*E_w/(F_r*(1 - eta_exp*eta_comp*phi))', { kind: 'derived', origin: a.external_recharge ? 'Work equals force times distance' : 'Energy balance with a fraction of wheel work returned to the tank through the compressor' }),
    eq('top', 'Top speed', 'P_max', '(0.5*rho_air*CdA*v_top^2 + C_rr*m_veh*g)*v_top', { kind: 'law', origin: 'Power balance at the wheels' }),
    eq('ein', 'External recharge energy', 'E_in', 'X/eta_comp', { kind: 'definition' }),
    eq('loop', 'Net work of an expand–recompress loop', 'W_loop', 'eta_exp*X - X/eta_comp', { kind: 'law', origin: 'First and second laws applied to the closed loop' }),
  ],
  derivation: a => [
    { text: 'Let the tank bleed down slowly at ambient temperature while each parcel expands isothermally from the current tank pressure to atmospheric pressure. Summing the parcel work gives the exergy of the tank.', tex: 'X = V\\!\\int_{p_0}^{p}\\ln\\frac{p\'}{p_0}\\,\\mathrm{d}p\' = pV\\ln\\frac{p}{p_0} - (p-p_0)V' },
    { text: 'The first term is the work done by the gas; the second is the part spent pushing back the atmosphere, which is not available at the shaft.', tex: 'W_{gas} = pV\\ln\\frac{p}{p_0}' },
    ...(a.isothermal ? [] : [{ text: 'If no heat enters, every parcel expands isentropically and leaves at T_e. An energy balance on the original tank contents gives the shaft work.', tex: 'T_e = T_0\\left(\\frac{p_0}{p}\\right)^{(\\gamma-1)/\\gamma},\\qquad W_{ad} = m c_v (T_0 - T_e) - m R T_e + p_0 V' }]),
    { text: 'At constant speed the motor works against aerodynamic drag and rolling resistance; the range is the wheel work divided by that force.', tex: 'F_r = \\tfrac12\\rho\\,C_dA\\,v^2 + C_{rr}\\,m g,\\qquad R = \\frac{\\eta_{exp} X}{F_r}' },
    { text: 'Now close the loop. Expanding the tank yields η_exp X at the shaft; restoring the tank needs X/η_comp. The net work of the loop is never positive, and is strictly negative for real machines.', tex: 'W_{loop} = X\\left(\\eta_{exp} - \\frac{1}{\\eta_{comp}}\\right) \\le 0' },
    { text: 'If a fraction φ of the wheel work drives an on-board compressor, the range becomes shorter, not longer, because η_exp η_comp < 1.', tex: 'R(\\varphi) = \\frac{(1-\\varphi)\\,\\eta_{exp}X}{F_r\\,(1-\\eta_{exp}\\eta_{comp}\\varphi)} \\le R(0)' },
  ],
  solve(v, a) {
    const mIdeal = v.p_tank * v.V_tank / (AIR.Rs * v.T_0), m = a.ideal_gas ? mIdeal : vdwMass(v.p_tank, v.T_0, v.V_tank), Z = mIdeal / m;
    const scale = m / mIdeal, X = tankExergy(v.p_tank, v.p_0, v.V_tank) * scale, Wgas = v.p_tank * v.V_tank * Math.log(v.p_tank / v.p_0) * scale;
    const ad = tankAdiabaticWork(v.p_tank, v.p_0, v.V_tank, v.T_0, mIdeal), Wad = ad.W * scale;
    const Wavail = a.isothermal ? X : Wad, Ew = v.eta_exp * Wavail;
    const dStop = 500, road = u => 0.5 * v.rho_air * v.CdA * u * u + v.C_rr * v.m_veh * g + (a.steady_cruise ? 0 : 0.5 * v.m_veh * u * u / dStop);
    const loopGain = v.eta_exp * v.eta_comp, self = a.external_recharge ? 1 : (1 - v.phi) / (1 - loopGain * v.phi);
    const Fr = road(v.v_c), range = self * Ew / Fr, range0 = Ew / Fr, Pc = Fr * v.v_c;
    const vTop = N.findRoot(u => (0.5 * v.rho_air * v.CdA * u * u + v.C_rr * v.m_veh * g) * u - v.P_max, 0, 400, 1e-12);
    const Ein = X / v.eta_comp, Wloop = v.eta_exp * X - X / v.eta_comp;
    const us = N.linspace(10 / 3.6, 150 / 3.6, 50);
    // adiabatic blow-down history against fraction of mass discharged
    const fr = N.linspace(0, 1 - Math.pow(v.p_0 / v.p_tank, 1 / AIR.gamma), 60);
    const pT = fr.map(q => v.p_tank * Math.pow(1 - q, AIR.gamma)), TT = fr.map(q => v.T_0 * Math.pow(1 - q, AIR.gamma - 1));
    const warnings = [];
    if (!a.isothermal && ad.Te < 150) warnings.push(`Fully adiabatic expansion would chill the exhaust to ${lab(ad.Te - 273.15, '°C')}, below the temperature at which air liquefies and far below the frost point. Real motors must reheat the air between stages; the adiabatic figure is a lower bound on work, not an operating condition.`);
    if (!a.external_recharge) warnings.push(`On-board recompression shortens the range from ${lab(range0 / 1000, 'km')} to ${lab(range / 1000, 'km')}. Each joule taken from the tank returns only ${lab(loopGain, 'J', 2)} of stored exergy; the vehicle cannot keep moving indefinitely.`);
    if (a.ideal_gas && v.p_tank > 1.5e7) warnings.push('Above about 150 bar air departs from ideal-gas behaviour by several per cent; switch off the ideal-gas assumption to see the effect on stored mass.');
    if (Pc > v.P_max) warnings.push('The cruise speed needs more power than the motor rating; the vehicle cannot hold this speed.');
    return {
      scalars: [
        scalar('m_air', 'Mass of stored air', m, 'kg'), scalar('Z', 'Compressibility factor in the tank', Z, '1'),
        scalar('W_gas', 'Gross isothermal expansion work p V ln(p/p₀)', Wgas, 'J', { show: 'kWh' }), scalar('X', 'Tank exergy (maximum shaft work)', X, 'J', { show: 'kWh' }),
        scalar('W_ad', 'Adiabatic expansion work', Wad, 'J', { show: 'kWh' }), scalar('e_m', 'Exergy per kilogram of air', X / m, 'J/kg', { show: 'Wh/kg' }),
        scalar('E_w', 'Work delivered at the wheels', Ew, 'J', { show: 'kWh' }), scalar('F_r', 'Road load at cruise', Fr, 'N'), scalar('P_c', 'Wheel power at cruise', Pc, 'W', { show: 'kW' }),
        scalar('R_range', 'Range at cruise speed', range, 'm', { show: 'km' }), scalar('t_run', 'Running time at cruise speed', range / v.v_c, 's', { show: 'min' }),
        scalar('v_top', 'Top speed on the level', vTop, 'm/s', { show: 'kph' }),
        scalar('T_e', 'Exhaust temperature', a.isothermal ? v.T_0 : ad.Te, 'K', { show: '°C' }), scalar('T_tank', 'Tank temperature when empty', a.isothermal ? v.T_0 : ad.Te, 'K', { show: '°C' }),
        scalar('Q_amb', 'Heat drawn from the surroundings during expansion', a.isothermal ? Wgas : 0, 'J', { show: 'kWh', note: 'Equal to the heat rejected by an ideal isothermal compressor when the tank was filled' }),
        scalar('E_in', 'Energy that must be supplied externally to recharge', Ein, 'J', { show: 'kWh' }), scalar('eta_rt', 'Round-trip efficiency, recharge energy to wheels', Ew / Ein, '1', { show: '%' }),
        scalar('W_loop', 'Net work of one expand–recompress loop', Wloop, 'J', { show: 'kWh' }), scalar('W_short', 'Shortfall of the self-recharging loop', -Wloop, 'J', { show: 'kWh' }),
        scalar('g_loop', 'Exergy returned per joule extracted (loop gain)', loopGain, '1'),
      ],
      series: [
        line('range-speed', 'Range against cruise speed', 'Speed', 'km/h', us.map(u => u * 3.6), [{ label: 'Isothermal expansion', data: us.map(u => self * v.eta_exp * X / road(u) / 1000) }, { label: 'Adiabatic expansion', data: us.map(u => self * v.eta_exp * Wad / road(u) / 1000), dash: true }], 'Range', 'km'),
        line('power-speed', 'Power required against speed', 'Speed', 'km/h', us.map(u => u * 3.6), [{ label: 'Road-load power', data: us.map(u => road(u) * u / 1000) }, { label: 'Rated motor power', data: us.map(() => v.P_max / 1000), dash: true }], 'Power', 'kW'),
        line('blowdown', 'Adiabatic tank blow-down', 'Fraction of air discharged', '–', fr, [{ label: 'Tank pressure (bar)', data: pT.map(q => q / 1e5) }, { label: 'Tank temperature (K)', data: TT }], 'Pressure, temperature', 'bar, K'),
        line('self', 'Range against the fraction of wheel power sent to an on-board compressor', 'Diverted fraction', '–', N.linspace(0, 0.95, 40), [{ label: 'Range', data: N.linspace(0, 0.95, 40).map(f => (1 - f) / (1 - loopGain * f) * range0 / 1000) }], 'Range', 'km'),
      ],
      checks: [
        check('First and second law: closed expand–recompress loop yields no net work', Math.max(Wloop, 0), 0, `Net work of the loop is ${lab(Wloop / 3.6e6, 'kWh')}; the shortfall must come from outside`),
        check('Wheel work does not exceed tank exergy', Math.max(Ew - X, 0), 0, 'η_exp ≤ 1 and adiabatic work ≤ isothermal exergy'),
        check('Adiabatic work below isothermal exergy', Math.max(Wad - X, 0), 0, 'Without heat from the surroundings less work is available'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const n = 4000, ps = N.linspace(v.p_0, v.p_tank, n), kap = (AIR.gamma - 1) / AIR.gamma;
    const numIso = v.V_tank * N.trapz(ps, ps.map(q => Math.log(q / v.p_0)));
    const m0 = v.p_tank * v.V_tank / (AIR.Rs * v.T_0);
    // parcel-by-parcel adiabatic work: dm leaves at tank state (p_t, T_t) and expands isentropically to p_0
    const numAd = N.trapz(ps, ps.map(q => { const Tt = v.T_0 * Math.pow(q / v.p_tank, kap), dmdp = m0 / (AIR.gamma * v.p_tank) * Math.pow(q / v.p_tank, 1 / AIR.gamma - 1); return AIR.cp * Tt * (1 - Math.pow(v.p_0 / q, kap)) * dmdp; }));
    const r = this.solve(v, { ...a, ideal_gas: true }), vt = val(r, 'v_top');
    return [
      bench('Tank exergy vs numerical integration of parcel work', tankExergy(v.p_tank, v.p_0, v.V_tank), numIso, 'X = V∫ln(p/p₀)dp', 1e-5),
      bench('Adiabatic work vs parcel-by-parcel integration', tankAdiabaticWork(v.p_tank, v.p_0, v.V_tank, v.T_0, m0).W, numAd, 'First law for an isentropic blow-down', 1e-4),
      bench('Top speed satisfies the power balance', (0.5 * v.rho_air * v.CdA * vt * vt + v.C_rr * v.m_veh * g) * vt, v.P_max, 'P = F v', 1e-9),
      bench('Exergy of 300 L at 300 bar', tankExergy(3e7, 101325, 0.3) / 3.6e6, 11.73, 'Hand calculation: pV[ln(p/p₀) − 1 + p₀/p]', 2e-3),
    ];
  },
  validation: [],
  logicPreset: {
    atoms: [{ k: 'E', text: 'The vehicle draws no energy from outside' }, { k: 'L', text: 'Compression and expansion involve losses' }, { k: 'R', text: 'The vehicle recompresses its own air while driving' }, { k: 'M', text: 'The vehicle keeps moving indefinitely' }],
    premises: ['E & R & L -> ~M', 'E', 'R', 'L'],
    conclusion: '~M',
  },
  diagram(v, a) {
    return svg(`
      ${S.path('M90 230 L120 170 L250 150 L330 110 L470 110 L530 170 L570 180 L570 230 Z', 'd-body')}
      ${S.circle(180, 235, 30)} ${S.circle(480, 235, 30)} ${S.path('M40 266 L600 266', 'd-ground')}
      ${S.rect(250, 165, 150, 44, 'd-liquid', 20)} ${S.text(325, 192, `${lab(v.V_tank * 1000, 'L')}, ${lab(v.p_tank / 1e5, 'bar')}`, 'd-text d-small')}
      ${S.rect(430, 165, 60, 40, 'd-body')} ${S.text(460, 190, 'motor', 'd-text d-small')} ${S.path('M400 187 L430 187', 'd-pipe')}
      ${S.arrow(492, 180, 560, 150)} ${S.text(585, 140, 'exhaust', 'd-text d-small')}
      ${a.isothermal ? S.arrow(460, 90, 460, 160, 'd-arrow d-heat') + S.text(520, 84, 'heat from surroundings', 'd-text d-small') : ''}
      ${a.external_recharge ? S.arrow(170, 60, 255, 160) + S.text(160, 50, 'external compressor (stationary)', 'd-text d-small') : S.path('M460 205 Q400 250 325 212', 'd-line d-hazard') + S.text(390, 256, 'on-board recompression', 'd-text d-small')}
      ${S.arrow(88, 200, 30, 200)} ${S.text(46, 190, 'drag', 'd-text d-small')}
      ${S.arrow(250, 310, 330, 310)} ${S.text(290, 300, `v = ${lab(v.v_c * 3.6, 'km/h')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the shaft work delivered by a compressed-air motor from a tank of known charge, the electrical energy used to recharge it, and hence the round-trip efficiency.',
    apparatus: ['Pressure vessel with regulator and air motor on a dynamometer', 'Multi-stage compressor with an electricity meter', 'Optional heat exchanger between regulator and motor'],
    instruments: [{ name: 'Tank pressure transducer and thermocouple', measures: 'Tank state during blow-down', range: '0–350 bar, −80 to 60 °C', resolution: '±0.25 %, ±1 K' }, { name: 'Dynamometer (torque and speed)', measures: 'Shaft power, integrated to work', range: '0–30 kW', resolution: '±0.5 %' }, { name: 'Thermal mass flow meter on the exhaust', measures: 'Air consumption', range: '0–0.2 kg/s', resolution: '±1 %' }, { name: 'Energy meter on the compressor supply', measures: 'Recharge energy', range: '0–50 kWh', resolution: '±1 %' }],
    procedure: ['Charge the tank, let it return to ambient temperature and record pressure.', 'Run the motor at constant load until the tank reaches regulator pressure, logging torque, speed, pressures and temperatures.', 'Integrate shaft power to obtain work; compare with the exergy of the charge.', 'Recharge to the starting pressure and record the electricity used.', 'Repeat with a driven compressor coupled to the motor shaft to demonstrate that the tank pressure still falls.'],
    controls: ['Leak-down test with the motor isolated', 'Repeat at a second discharge rate to separate thermal effects from mechanical losses'],
    signatures: ['Shaft work always below p V ln(p/p₀) − (p − p₀) V', 'Exhaust and tank temperatures falling during fast discharge', 'Recharge energy several times the shaft work recovered', 'Tank pressure falling monotonically even with on-board recompression'],
    safety: ['Pressure vessel and fittings rated and inspected for the working pressure; the energy released if a 300 L tank at 300 bar bursts is about 18 MJ, comparable to several kilograms of high explosive', 'Whip restraints on hoses', 'Hearing protection for exhaust noise', 'Cold burns from exhaust and frosted components'],
  },
  falsify: ['Shaft work from a tank blow-down exceeding the tank exergy computed from its initial state.', 'A vehicle whose tank pressure does not fall over a closed driving circuit with no external energy input.'],
  alternatives: [{ name: 'Polytropic expansion with index 1 < n < γ', text: 'Real motors lie between the isothermal and adiabatic limits; multi-stage expansion with inter-stage reheating approaches the isothermal value.' }, { name: 'Hybrid with fuel-fired air heating', text: 'Burning fuel to heat the air before expansion raises the work per kilogram, but the vehicle is then partly fuel-powered.' }, { name: 'Battery-electric storage', text: 'Stores roughly ten times more energy per unit mass and returns 70–90 % of the charging energy to the wheels.' }],
  hazards: [{ hazard: 'Tank rupture', cause: 'Impact, fatigue or overfilling', mitigation: 'Composite vessels designed to leak before burst, relief devices, periodic inspection' }, { hazard: 'Icing of motor and valves', cause: 'Expansion cooling with humid air', mitigation: 'Dry the charge air; reheat between stages' }, { hazard: 'Noise', cause: 'High-velocity exhaust', mitigation: 'Silencers' }],
  standards: ['ISO 11439 (high-pressure cylinders for on-board storage of natural gas — analogous vessel requirements)', 'UN ECE Regulation No. 110 (compressed-gas vehicle components)', 'EN 12245 (transportable gas cylinders — fully wrapped composite cylinders)', 'ISO 8573-1 (compressed-air purity classes)'],
  limits: 'Quasi-steady cruise on a level road. Tank at ambient temperature when full. The isothermal and adiabatic cases bound real behaviour. The van der Waals correction is qualitative above 300 bar.',
  numerics: { method: 'Closed-form energy relations; bracketed root-finding for top speed and van der Waals molar volume' },
  optimise: { objective: 'R_range', sense: 'max', vars: ['v_c', 'p_tank'], note: 'Range rises with tank pressure and falls with speed squared once drag dominates.' },
  inverse: { series: 'range-speed', curve: 0, fit: ['eta_exp', 'CdA'] },
  extensions: ['Multi-stage expansion with inter-stage heat exchange', 'Regulator throttling loss between tank and motor', 'Driving-cycle simulation with regenerative braking into the tank', 'Life-cycle comparison with battery-electric vehicles'],
};

// ------------------------------------------------------------------ perpetual-motion / free-energy claim tester
const VERDICTS = ['Consistent with the first and second laws', 'Violates the second law (exceeds the Carnot limit or needs a single-reservoir engine)', 'Violates the first law (creates energy)', 'Admissible only in the counterfactual world with a relaxed second law'];

const freeEnergy = {
  id: 'self-powered-cycle-claim',
  title: 'Test of a self-powered or over-unity device claim',
  module: 1, klass: ['II', 'III'], domains: ['thermal', 'logic'], hypothetical: true,
  keywords: ['perpetual motion', 'free energy', 'over-unity', 'overunity', 'self-powered', 'self powered', 'self-sustaining', 'more energy out than in', 'runs forever', 'zero-point', 'carnot limit', 'second law violation', 'energy from nothing', 'perpetuum mobile'],
  summary: 'Audits a claimed input and output power against conservation of energy and the Carnot limit, and reports the entropy that would have to be destroyed and the hidden input that would reconcile the claim.',
  background: [
    'Claims of “free energy” fall into two classes. A perpetual-motion machine of the first kind delivers more energy than it receives and so contradicts conservation of energy. A machine of the second kind conserves energy but converts heat into work more completely than the Carnot limit allows — in the extreme case drawing work from a single reservoir such as the atmosphere or the sea — and so contradicts the second law.',
    'Both laws are among the most thoroughly tested in physics. Conservation of energy follows, by Noether’s theorem, from the invariance of physical law under translation in time. The second law is statistical: a macroscopic violation would require an overwhelmingly improbable fluctuation. No reproducible exception to either has been observed.',
    'When a device appears to exceed these limits, experience shows that the explanation is an unmeasured input (mains pick-up, a concealed battery, a draining internal store, ambient heat counted as “free”), or a measurement error such as confusing apparent with real electrical power. This model quantifies how large such a hidden input must be.',
    'A counterfactual input lets the Carnot bound be multiplied by a “violation factor”. With any value other than one the model describes a world whose physics differs from ours; results are then conditional on that invented premise and are labelled as such.',
  ],
  phenomena: ['Energy conservation', 'Heat-to-work conversion', 'Entropy generation', 'Depletion of an internal energy store'],
  laws: ['energy', 'second', 'noether', 'logic_nc'],
  refs: ['Carnot, S. (1824). Réflexions sur la puissance motrice du feu. Bachelier, Paris.', 'Clausius, R. (1865). Über verschiedene für die Anwendung bequeme Formen der Hauptgleichungen der mechanischen Wärmetheorie. Annalen der Physik 125, 353–400.', 'Planck, M. (1903). Treatise on Thermodynamics. Longmans, Green & Co.', 'Ord-Hume, A. W. J. G. (1977). Perpetual Motion: The History of an Obsession. George Allen & Unwin.', 'Noether, E. (1918). Invariante Variationsprobleme. Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen, 235–257.'],
  inputs: [
    inp('P_in', 'Claimed input power', 'W', 100, { min: 1, max: 1e6, aliases: ['input power', 'power in', 'consumes', 'draws'] }),
    inp('P_out', 'Claimed output power', 'W', 300, { min: 1, max: 1e6, aliases: ['output power', 'power out', 'produces', 'delivers', 'generates'] }),
    inp('T_h', 'Heat-source temperature', '°C', 80, { min: 30, max: 2000, aliases: ['source temperature', 'hot temperature', 'hot side'] }),
    inp('T_c', 'Heat-sink (ambient) temperature', '°C', 20, { min: -50, max: 29, kind: 'environment', env: 'air_temp', aliases: ['sink temperature', 'cold temperature', 'ambient temperature', 'cold side'] }),
    inp('E_store', 'Energy of any internal store (battery, flywheel, spring, gas)', 'kJ', 500, { min: 1, max: 1e6, aliases: ['battery', 'internal store', 'stored energy', 'flywheel'] }),
    inp('f_viol', 'Second-law violation factor (multiplies the Carnot limit; 1 in our world)', '1', 1, { min: 1, max: 10, kind: 'hypothetical', aliases: ['violation factor'], src: 'Counterfactual parameter with no physical basis; any value other than 1 describes an invented world' }),
  ],
  assumptions: [
    asm('heat_input', 'The claimed input is heat taken from the source at T_h.', { why: 'Typical of “ambient heat” and low-grade-heat engine claims', alt: 'The claimed input is work (electrical or mechanical); only the first-law limit of 100 % applies.' }),
    asm('closed', 'No energy other than the declared input crosses the boundary of the device.', { why: 'The claim as usually stated', alt: 'The shortfall is drawn as heat from the ambient at T_c, satisfying the first law but making the device a single-reservoir engine.' }),
    asm('steady', 'The device operates steadily with no internal store being run down.', { why: 'Required for a genuine continuous source', alt: 'An internal store supplies the shortfall, and the device stops when it is exhausted.' }),
    asm('measured_true', 'The claimed powers are true time-averaged real powers.', { why: 'Takes the claim at face value', alt: 'Output was inferred from volt-amperes with a power factor of 0.3, a common measurement error; real output is 30 % of the claim.' }),
  ],
  symbols: { eta: ['Claimed efficiency', '1'], eta_C: ['Carnot efficiency', '1'], eta_lim: ['Applicable efficiency limit', '1'], P_allow: ['Largest admissible output', 'W'], P_hid: ['Hidden input needed to reconcile the claim', 'W'], S_gen: ['Entropy generation rate implied by the claim', 'W/K'], Q_amb: ['Heat drawn from the ambient', 'W'], t_run: ['Running time on the internal store', 's'], P_real: ['Real output power', 'W'] },
  equations: a => [
    ...(a.measured_true ? [] : [eq('pf', 'Real output power', 'P_real', '0.3*P_out', { kind: 'definition', origin: 'Real power = apparent power × power factor' })]),
    eq('eta', 'Claimed efficiency', 'eta', a.measured_true ? 'P_out/P_in' : 'P_real/P_in', { kind: 'definition' }),
    eq('carnot', 'Carnot efficiency', 'eta_C', '1 - T_c/T_h', { kind: 'law', origin: 'Second law of thermodynamics' }),
    a.heat_input ? eq('lim', 'Efficiency limit', 'eta_lim', 'min(1, f_viol*eta_C)', { kind: 'hypothesis', origin: 'Carnot limit, multiplied by the counterfactual violation factor (1 in the real world), capped by the first law', needs: ['heat_input'] }) : eq('lim', 'Efficiency limit', 'eta_lim', '1', { kind: 'law', origin: 'First law of thermodynamics' }),
    eq('allow', 'Largest admissible output', 'P_allow', 'eta_lim*P_in', { kind: 'law', origin: 'First and second laws' }),
    eq('hid', 'Hidden input that would reconcile the claim', 'P_hid', a.measured_true ? 'max(P_out - P_allow, 0)' : 'max(P_real - P_allow, 0)', { kind: 'derived', origin: 'Energy balance with the admissible conversion' }),
    ...(a.closed ? [] : [eq('qamb', 'Heat drawn from the ambient', 'Q_amb', `max(${a.measured_true ? 'P_out' : 'P_real'} - P_in, 0)`, { kind: 'law', origin: 'First law with an undeclared ambient heat intake' })]),
    eq('sgen', 'Entropy generation rate implied by the claim', 'S_gen', `max(P_in - ${a.measured_true ? 'P_out' : 'P_real'}, 0)/T_c${a.heat_input ? ' - P_in/T_h' : ''}${a.closed ? '' : ' - Q_amb/T_c'}`, { kind: 'law', origin: 'Entropy balance on a steady device', needs: ['steady'] }),
    ...(a.steady ? [] : [eq('trun', 'Running time on the internal store', 't_run', 'E_store/P_hid', { kind: 'derived', origin: 'Energy balance on the store' })]),
  ],
  derivation: a => [
    { text: 'For a device in steady operation the first law requires the power leaving to equal the power entering. Any claimed excess must come from somewhere.', tex: 'P_{out} + \\dot Q_{rej} = P_{in} + P_{hidden}' },
    { text: 'The entropy balance for a steady device taking heat at T_h and rejecting heat at T_c defines the entropy generation rate, which the second law requires to be non-negative.', tex: '\\dot S_{gen} = \\frac{\\dot Q_c}{T_c} - \\frac{\\dot Q_h}{T_h} \\ge 0' },
    { text: 'Eliminating the rejected heat with the first law turns the entropy condition into the Carnot limit on efficiency.', tex: '\\eta = \\frac{P_{out}}{\\dot Q_h} \\le 1 - \\frac{T_c}{T_h}' },
    { text: 'If the claimed output exceeds the admissible output, the difference is the smallest undeclared work input that would make the account balance.', tex: 'P_{hidden} = \\max\\big(P_{out} - \\eta_{lim} P_{in},\\ 0\\big)' },
    ...(a.steady ? [] : [{ text: 'A finite internal store can supply that difference only for a limited time.', tex: 't_{run} = \\frac{E_{store}}{P_{hidden}}' }]),
    { text: 'In the counterfactual world the Carnot bound is multiplied by a factor f; this is a stipulation, not a consequence of any known physics.', tex: '\\eta_{lim} = \\min\\big(1,\\ f\\,\\eta_C\\big)' },
  ],
  solve(v, a) {
    const Pout = a.measured_true ? v.P_out : 0.3 * v.P_out, eta = Pout / v.P_in, etaC = 1 - v.T_c / v.T_h;
    const etaLimReal = a.heat_input ? etaC : 1, etaLim = a.heat_input ? Math.min(1, v.f_viol * etaC) : 1;
    const Pallow = etaLim * v.P_in, PallowReal = etaLimReal * v.P_in, Phid = Math.max(Pout - Pallow, 0), PhidReal = Math.max(Pout - PallowReal, 0);
    const excess = Math.max(Pout - v.P_in, 0), Qamb = a.closed ? 0 : excess, created = a.closed ? excess : 0;
    const Qrej = Math.max(v.P_in - Pout, 0);
    const Sgen = Qrej / v.T_c - (a.heat_input ? v.P_in / v.T_h : 0) - Qamb / v.T_c;
    const Sdestroyed = Math.max(-Sgen, 0);
    let verdict = 0;
    if (created > 0) verdict = 2; else if (Sgen < -1e-12 * v.P_in / v.T_c) verdict = Pout <= Pallow && v.f_viol > 1 ? 3 : 1;
    const tRun = Phid > 0 ? v.E_store / Phid : Infinity;
    // reconciled account: admissible conversion of the declared input plus the hidden work input
    const SgenRec = (v.P_in * (1 - etaLimReal)) / v.T_c - (a.heat_input ? v.P_in / v.T_h : 0);
    const Ths = N.linspace(v.T_c + 5, Math.max(v.T_h * 1.5, v.T_c + 200), 80), Pos = N.linspace(0, Math.max(1.5 * Pout, 1.2 * v.P_in), 80);
    const sOf = Po => { const ex = Math.max(Po - v.P_in, 0); return Math.max(v.P_in - Po, 0) / v.T_c - (a.heat_input ? v.P_in / v.T_h : 0) - ex / v.T_c; };
    const warnings = [];
    if (v.f_viol > 1) warnings.push(`Counterfactual world: the Carnot bound has been multiplied by ${lab(v.f_viol)}. No known physics permits this; every result that depends on the relaxed limit is conditional on an invented premise.`);
    if (verdict === 2) warnings.push(`The claim requires ${lab(created, 'W')} to appear from nothing. Conservation of energy has no known exception; look for an unmeasured input of at least ${lab(PhidReal, 'W')}.`);
    if (verdict === 1) warnings.push(`The claim conserves energy but would destroy entropy at ${lab(Sdestroyed, 'W/K')}. That is a perpetual-motion machine of the second kind.`);
    if (!a.steady && Phid > 0) warnings.push(`An internal store of ${lab(v.E_store / 1000, 'kJ')} could supply the shortfall for ${lab(tRun / 60, 'min')}; a demonstration shorter than this proves nothing.`);
    if (!a.measured_true) warnings.push('With a power factor of 0.3 the real output is 30 % of the volt-ampere figure. Use a true-power analyser on both input and output.');
    return {
      scalars: [
        scalar('verdict', 'Verdict', verdict, '1', { text: VERDICTS[verdict], status: v.f_viol > 1 ? 'hypothetical' : undefined }),
        scalar('eta', 'Claimed efficiency', eta, '1', { show: '%' }), scalar('eta_C', 'Carnot efficiency between source and sink', etaC, '1', { show: '%' }),
        scalar('eta_lim', 'Applicable efficiency limit', etaLim, '1', { show: '%', status: v.f_viol > 1 ? 'hypothetical' : undefined }),
        scalar('P_allow', 'Largest admissible output', Pallow, 'W', { status: v.f_viol > 1 ? 'hypothetical' : undefined }),
        scalar('P_hid', 'Hidden input needed to reconcile the claim', Phid, 'W', { status: v.f_viol > 1 ? 'hypothetical' : undefined }),
        scalar('P_hid_real', 'Hidden input needed under real-world physics', PhidReal, 'W'),
        scalar('Q_hid', 'Equivalent hidden heat input at the source temperature', a.heat_input ? PhidReal / etaC : PhidReal, 'W'),
        scalar('P_created', 'Energy that would be created from nothing', created, 'W'), scalar('Q_amb', 'Undeclared heat drawn from the ambient', Qamb, 'W'),
        scalar('S_gen', 'Entropy generation rate implied by the claim', Sgen, 'W/K'), scalar('S_destroyed', 'Entropy that would have to be destroyed each second', Sdestroyed, 'W/K'),
        scalar('ratio', 'Claimed output over admissible output', Pout / Pallow, '1'),
        scalar('t_run', 'Time an internal store could sustain the shortfall', tRun, 's', { show: 'h', text: Number.isFinite(tRun) ? undefined : 'No shortfall to supply' }),
        scalar('E_day', 'Unexplained energy per day', PhidReal * 86400, 'J', { show: 'kWh' }),
      ],
      series: [
        line('eta-T', 'Claimed efficiency against the limits', 'Source temperature', '°C', Ths.map(q => q - 273.15), [{ label: 'Carnot limit', data: Ths.map(T => 1 - v.T_c / T) }, ...(v.f_viol > 1 ? [{ label: 'Counterfactual limit', data: Ths.map(T => Math.min(1, v.f_viol * (1 - v.T_c / T))), dash: true }] : []), { label: 'First-law limit', data: Ths.map(() => 1), dash: true }, { label: 'Claim', data: Ths.map(() => eta) }], 'Efficiency', '–', { marker: [v.T_h - 273.15, eta] }),
        line('sgen-P', 'Entropy generation implied by a claimed output', 'Claimed output power', 'W', Pos, [{ label: 'Entropy generation rate', data: Pos.map(sOf) }, { label: 'Zero (second-law boundary)', data: Pos.map(() => 0), dash: true }], 'Entropy generation', 'W/K', { marker: [Pout, Sgen], note: 'Outputs for which the curve is negative are forbidden by the second law.' }),
      ],
      checks: [
        check('Reconciled account rejects non-negative heat', Math.min(v.P_in + PhidReal - Pout, 0) / v.P_in, 1e-12, 'Declared input plus hidden input covers the output; the remainder is rejected heat'),
        check('Reconciled account generates no negative entropy', Math.min(SgenRec, 0), 1e-12, 'With the hidden input included, real-world physics is satisfied'),
      ],
      warnings,
      notes: ['The verdict tests the claim as stated. It does not show that the device does nothing, only that the stated account of its energy flows cannot be complete.'],
    };
  },
  benchmarks(v, a) {
    const b = { heat_input: true, closed: true, steady: true, measured_true: true };
    const atCarnot = this.solve({ ...v, P_in: 1000, P_out: 1000 * (1 - 300 / 600), T_h: 600, T_c: 300, f_viol: 1 }, b);
    const over = this.solve({ ...v, P_in: 100, P_out: 300, f_viol: 1 }, { ...b, heat_input: false });
    return [
      bench('Entropy generation of a Carnot engine', val(atCarnot, 'S_gen') + 1, 1, 'Reversible engine: Ṡ_gen = 0', 1e-12),
      bench('Hidden input for a 300 W output from 100 W of work', val(over, 'P_hid'), 200, 'First law: P_hidden = P_out − P_in', 1e-12),
      bench('Carnot efficiency between 600 K and 300 K', val(atCarnot, 'eta_C'), 0.5, 'η_C = 1 − T_c/T_h', 1e-12),
    ];
  },
  validation: [],
  logicPreset: {
    atoms: [{ k: 'F', text: 'Energy is conserved (first law)' }, { k: 'K', text: 'No cyclic device converts heat from a single reservoir entirely into work (second law)' }, { k: 'C', text: 'The device receives no energy other than its declared input' }, { k: 'H', text: 'The only heat available to the device is at ambient temperature' }, { k: 'O', text: 'The device delivers more energy than its declared input' }, { k: 'W', text: 'The device runs continuously on ambient heat alone' }],
    premises: ['F & C -> ~O', 'K & H -> ~W', 'F', 'K', 'C', 'H'],
    conclusion: '~O & ~W',
  },
  diagram(v, a) {
    return svg(`
      ${S.rect(240, 120, 160, 120, 'd-body', 10)} ${S.text(320, 175, 'claimed device')} ${S.text(320, 198, '?', 'd-text')}
      ${S.arrow(110, 180, 236, 180, a.heat_input ? 'd-arrow d-heat' : 'd-arrow')} ${S.text(170, 168, `${a.heat_input ? 'heat' : 'work'} in ${lab(v.P_in, 'W')}`)}
      ${S.arrow(404, 180, 530, 180)} ${S.text(470, 168, `work out ${lab(v.P_out, 'W')}`)}
      ${S.rect(60, 40, 100, 40, 'd-body')} ${S.text(110, 65, `source ${lab(v.T_h - 273.15, '°C')}`, 'd-text d-small')}
      ${S.rect(270, 300, 100, 40, 'd-body')} ${S.text(320, 325, `sink ${lab(v.T_c - 273.15, '°C')}`, 'd-text d-small')}
      ${S.arrow(320, 244, 320, 296, 'd-arrow d-heat')} ${S.text(372, 275, 'rejected heat', 'd-text d-small')}
      ${S.path('M320 60 L320 116', 'd-line d-hazard')} ${S.text(320, 50, 'hidden input?', 'd-text d-small')}
      ${a.heat_input ? S.path('M110 80 L110 180', 'd-line d-heat') : ''}
    `);
  },
  experiment: {
    objective: 'Establish a complete, independently verified energy account of a device claimed to deliver more than it receives.',
    apparatus: ['The device inside a calorimetric enclosure with every electrical, mechanical, fluid and thermal connection passing through a metered boundary', 'A resistive dummy load', 'Faraday-cage or screened enclosure to exclude radio-frequency pick-up'],
    instruments: [{ name: 'True-power analyser on every electrical port', measures: 'Real (not apparent) input and output power', range: 'DC–1 MHz, 0–10 kW', resolution: '±0.1 %' }, { name: 'Flow calorimeter on the enclosure coolant', measures: 'Net heat released', range: '0–5 kW', resolution: '±1 %' }, { name: 'Thermocouples on source, sink and casing', measures: 'Reservoir temperatures', range: '−50 to 1000 °C', resolution: '±0.5 K' }, { name: 'Balance or load cells under the device', measures: 'Mass change (consumed fuel or reactants)', range: '0–100 kg', resolution: '±1 g' }],
    procedure: ['Define the system boundary and list every path by which energy could cross it.', 'Calibrate the calorimeter with a resistor of known dissipation.', 'Run the device for at least ten times the period for which any internal store could supply the claimed excess.', 'Integrate all inputs and outputs and compare; repeat with the device replaced by an inert dummy of the same mass and geometry.', 'Have the test repeated by an independent laboratory.'],
    controls: ['Blank run with the device unpowered', 'Calibration run with a known heater', 'Batteries removed or their state of charge measured before and after'],
    signatures: ['Energy account closing within the measurement uncertainty', 'Any apparent excess scaling with measurement bandwidth or lead arrangement (a sign of instrument error)', 'Output decaying as an internal store runs down'],
    safety: ['Treat an unknown device as a potential electrical, chemical and stored-energy hazard', 'Isolate and lock off mains supplies when reconfiguring'],
  },
  falsify: ['A device that, inside a closed calorimetric boundary and over a period far longer than any internal store could sustain, delivers more energy than crosses the boundary — reproducibly and in independent laboratories.', 'A cyclic device producing net work while exchanging heat with a single reservoir.'],
  alternatives: [{ name: 'Undeclared energy input', text: 'Mains or radio-frequency pick-up, a concealed battery, chemical reaction of the materials or ambient heat counted as free.' }, { name: 'Measurement error', text: 'Apparent power mistaken for real power, peak values mistaken for averages, or neglected phase shifts with pulsed waveforms.' }, { name: 'Transient release of stored energy', text: 'Springs, flywheels, magnets being rearranged, or thermal mass cooling down can exceed the input for a limited time.' }, { name: 'Heat pump misread as a source', text: 'A coefficient of performance above one moves more heat than the work supplied; it is not an efficiency above 100 %.' }],
  hazards: [{ hazard: 'Financial loss', cause: 'Investment in a device that cannot work as claimed', mitigation: 'Independent calorimetric testing before commitment' }, { hazard: 'Electric shock and fire', cause: 'Improvised high-voltage or high-current apparatus', mitigation: 'Standard electrical safety practice' }],
  standards: ['ISO/IEC 17025 (competence of testing and calibration laboratories)', 'IEC 61000-4-30 (power-quality measurement methods)', 'JCGM 100 (Guide to the expression of uncertainty in measurement)'],
  limits: 'A steady-state audit of time-averaged powers between two reservoirs. It tests the internal consistency of a claim; it cannot identify which hidden input is present. With a violation factor other than one the results describe an invented world.',
  numerics: { method: 'Algebraic energy and entropy balances' },
  inverse: { series: 'sgen-P', curve: 0, fit: ['T_h'] },
  extensions: ['Transient audit with a measured discharge curve of the internal store', 'Uncertainty propagation on the measured powers', 'Fluctuation-theorem estimate of the probability of a spontaneous violation at a given scale'],
};

// ------------------------------------------------------------------ reverse-osmosis desalination
const M_NACL = 0.05844;
/** March along the membrane area solving the local solution–diffusion and film-model equations. */
function roMarch({ A, B, k, kap, cf, Qf, Pf, dp, Am, n, polarise }) {
  const dA = Am / n, x = [], flux = [], cbs = [], cms = [], cps = [];
  let Q = Qf, c = cf, Qp = 0, salt = 0, cpfMax = 1;
  for (let i = 0; i < n; i++) {
    const P = Pf - dp * (i + 0.5) / n;
    const local = Jw => { const E = polarise ? Math.exp(Math.min(Jw / k, 50)) : 1; return { E, dpi: kap * c * E * Jw / (Jw + B * E + 1e-300) }; };
    const Jmax = A * Math.max(P, 0);
    const Jw = Jmax > 0 ? N.bisect(J => J - A * (P - local(J).dpi), 0, Jmax, 1e-13) : 0;
    const E = local(Jw).E, cm = c * E * (Jw + B) / (Jw + B * E + 1e-300), cp = B * cm / (Jw + B + 1e-300);
    const dQ = Math.min(Jw * dA, 0.5 * Q), ms = Math.min(cp * dQ, 0.5 * Q * c);
    x.push((i + 0.5) / n); flux.push(Jw); cbs.push(c); cms.push(cm); cps.push(cp); cpfMax = Math.max(cpfMax, cm / c);
    const Qn = Q - dQ; c = (Q * c - ms) / Qn; Q = Qn; Qp += dQ; salt += ms;
  }
  return { x, flux, cbs, cms, cps, Qp, Qb: Q, cb: c, cp: Qp > 0 ? salt / Qp : 0, salt, cpfMax, Pb: Pf - dp };
}
/** Least work of separation per unit permeate volume for a van 't Hoff solution (linear osmotic pressure). */
function roLeastWork(kap, Qf, cf, Qp, cp, Qb, cb) {
  const xlnx = c => (c > 0 ? c * Math.log(c) : 0);
  return Qp > 0 ? kap * (Qp * xlnx(cp) + Qb * xlnx(cb) - Qf * xlnx(cf)) / Qp : 0;
}

const reverseOsmosis = {
  id: 'reverse-osmosis-desalination',
  title: 'Seawater reverse-osmosis stage',
  module: 2, klass: 'I', domains: ['desalination', 'chemical'],
  keywords: ['reverse osmosis', 'swro', 'desalination', 'osmotic pressure', 'membrane', 'permeate', 'recovery', 'salt rejection', 'specific energy consumption', 'energy recovery', 'concentration polarisation', 'concentration polarization', 'brine', 'water flux', 'solution-diffusion'],
  summary: 'Single-stage seawater reverse osmosis by the solution–diffusion model: flux, recovery, permeate quality, concentration polarisation and specific energy against the thermodynamic minimum.',
  background: [
    'In reverse osmosis a pressure greater than the osmotic pressure is applied to saline water on one side of a dense polymer membrane. Water dissolves in and diffuses through the membrane in proportion to the net driving pressure, while salt diffuses in proportion to its concentration difference; the two fluxes are nearly independent, which is why permeate quality improves as flux rises.',
    'Rejected salt accumulates in a boundary layer at the membrane surface. This concentration polarisation raises the osmotic pressure the pump must overcome and is described by film theory, in which the wall concentration grows exponentially with the ratio of water flux to the feed-side mass-transfer coefficient. Along a pressure vessel the bulk feed becomes more concentrated as permeate is withdrawn, so the flux falls from inlet to outlet.',
    'The brine leaves at almost feed pressure. Isobaric energy-recovery devices return most of that hydraulic energy to the incoming feed, which brought the specific energy of seawater plants to within a factor of about two of the least work of separation.',
  ],
  phenomena: ['Osmosis and osmotic pressure', 'Solution–diffusion transport', 'Concentration polarisation', 'Longitudinal concentration of the feed', 'Hydraulic energy recovery'],
  laws: ['mass', 'species', 'fick', 'energy', 'second'],
  refs: ['Lonsdale, H. K., Merten, U. & Riley, R. L. (1965). Transport properties of cellulose acetate osmotic membranes. J. Applied Polymer Science 9, 1341–1362.', 'Wijmans, J. G. & Baker, R. W. (1995). The solution-diffusion model: a review. J. Membrane Science 107, 1–21.', 'Elimelech, M. & Phillip, W. A. (2011). The future of seawater desalination: energy, technology, and the environment. Science 333, 712–717.', 'Mistry, K. H., McGovern, R. K., Thiel, G. P., Summers, E. K., Zubair, S. M. & Lienhard V, J. H. (2011). Entropy generation analysis of desalination technologies. Entropy 13, 1829–1864.', 'Millero, F. J. & Poisson, A. (1981). International one-atmosphere equation of state of seawater. Deep-Sea Research 28A, 625–629.'],
  inputs: [
    inp('S_f', 'Feed salinity', 'g/kg', 35, { min: 1, max: 50, kind: 'environment', env: 'salinity', aliases: ['salinity', 'feed salinity', 'tds'] }),
    inp('T', 'Feed temperature', '°C', 25, { min: 5, max: 40, kind: 'environment', env: 'sea_surface_temp', aliases: ['temperature', 'feed temperature', 'water temperature'] }),
    inp('P_f', 'Feed pressure above permeate pressure', 'bar', 60, { min: 20, max: 85, aliases: ['feed pressure', 'operating pressure', 'pressure'] }),
    inp('Q_f', 'Feed flow to the pressure vessel', 'm^3/h', 8, { min: 1, max: 20, aliases: ['feed flow', 'flow rate', 'feed rate'] }),
    inp('A_m', 'Membrane area in the vessel', 'm^2', 260, { min: 20, max: 330, kind: 'geometry', aliases: ['membrane area', 'area'], src: 'Seven 8-inch elements of about 37 m² each' }),
    inp('A_w', 'Water permeability', 'L/(m^2 h bar)', 1.2, { min: 0.3, max: 4, kind: 'fluid', aliases: ['water permeability', 'permeability'], src: 'Typical seawater polyamide thin-film composite membrane' }),
    inp('B_s', 'Salt permeability', 'm/s', 2.5e-8, { min: 2e-9, max: 5e-7, kind: 'fluid', aliases: ['salt permeability'], src: 'Typical seawater membrane, about 0.1 L/(m² h)' }),
    inp('k_m', 'Feed-side mass-transfer coefficient', 'm/s', 6e-5, { min: 1e-5, max: 2e-4, aliases: ['mass transfer coefficient'], src: 'Spacer-filled channel at typical cross-flow velocity' }),
    inp('dp_f', 'Feed-channel pressure drop', 'bar', 1.5, { min: 0, max: 5, aliases: ['pressure drop'] }),
    inp('phi_o', 'Osmotic coefficient', '1', 0.9, { min: 0.85, max: 1, kind: 'fluid', aliases: ['osmotic coefficient'], src: 'Seawater-strength NaCl solutions, Robinson & Stokes (1959)' }),
    inp('eta_p', 'High-pressure pump efficiency', '1', 0.82, { min: 0.5, max: 0.95, aliases: ['pump efficiency'] }),
    inp('eta_erd', 'Energy-recovery device efficiency', '1', 0.95, { min: 0.5, max: 0.99, aliases: ['erd efficiency', 'energy recovery', 'pressure exchanger'] }),
    inp('n_seg', 'Number of marching segments', '1', 100, { min: 20, max: 1000, kind: 'numerical' }),
  ],
  assumptions: [
    asm('cp_film', 'Concentration polarisation follows the stagnant-film model.', { why: 'Standard design treatment', alt: 'Polarisation is neglected: the wall concentration equals the bulk concentration.' }),
    asm('salt_passage', 'Salt crosses the membrane by diffusion with permeability B.', { why: 'Real membranes are not perfectly selective', alt: 'The membrane rejects salt completely (B = 0).' }),
    asm('erd', 'An energy-recovery device returns brine pressure energy to the feed.', { why: 'Universal in modern seawater plants', alt: 'Brine is throttled to atmosphere and its pressure energy is lost.' }),
    asm('temp_ref', 'The stated permeabilities apply at the operating temperature.', { why: 'Membrane data supplied at site conditions', alt: 'Permeabilities are given at 25 °C and are corrected with an Arrhenius-type temperature factor (activation temperature 2640 K above 25 °C, 3020 K below, as used in manufacturers’ design manuals).' }),
  ],
  symbols: { c: ['Salt mass concentration', 'kg/m^3'], c_f: ['Feed concentration', 'kg/m^3'], c_b: ['Bulk concentration', 'kg/m^3'], c_m: ['Concentration at the membrane wall', 'kg/m^3'], c_p: ['Permeate concentration', 'kg/m^3'], pi_o: ['Osmotic pressure', 'Pa'], pi_m: ['Osmotic pressure at the wall', 'Pa'], pi_p: ['Osmotic pressure of permeate', 'Pa'], pi_f: ['Osmotic pressure of feed', 'Pa'], i_v: ['van ’t Hoff factor (2 for NaCl)', '1'], M_s: ['Molar mass of salt', 'kg/mol'], P: ['Local feed pressure', 'Pa'], P_b: ['Brine pressure', 'Pa'], J_w: ['Water flux', 'm/s'], J_s: ['Salt flux', 'kg/(m^2 s)'], Q: ['Local feed-side flow', 'm^3/s'], Q_p: ['Permeate flow', 'm^3/s'], Q_b: ['Brine flow', 'm^3/s'], A_x: ['Cumulative membrane area', 'm^2'], r: ['Recovery', '1'], Rej: ['Salt rejection', '1'], SEC: ['Specific energy consumption', 'J/m^3'], w_min: ['Least work of separation', 'J/m^3'], A_T: ['Water permeability at the operating temperature', 'm/(s Pa)'], B_T: ['Salt permeability at the operating temperature', 'm/s'], E_T: ['Activation temperature (2640 K at or above 25 °C, 3020 K below)', 'K'], T_25: ['Reference temperature 298.15 K', 'K'], w_min0: ['Least work of separation for salt-free permeate', 'J/m^3'] },
  equations: a => [
    eq('pi', 'Osmotic pressure', 'pi_o', 'phi_o*i_v*c*R_u*T/M_s', { kind: 'law', origin: 'van ’t Hoff relation with an osmotic coefficient' }),
    eq('jw', 'Water flux', 'J_w', `${a.temp_ref ? 'A_w' : 'A_T'}*(P - (pi_m - pi_p))`, { kind: 'law', origin: 'Solution–diffusion model; Lonsdale, Merten & Riley (1965)' }),
    a.salt_passage ? eq('js', 'Salt flux', 'J_s', `${a.temp_ref ? 'B_s' : 'B_T'}*(c_m - c_p)`, { kind: 'law', origin: 'Fickian diffusion of salt through the membrane', needs: ['salt_passage'] }) : eq('js', 'Salt flux', 'J_s', '0*B_s*c_m', { kind: 'closure', origin: 'Perfectly selective membrane' }),
    eq('cp', 'Permeate concentration', 'c_p', 'J_s/J_w', { kind: 'law', origin: 'Steady salt balance across the membrane' }),
    a.cp_film ? eq('film', 'Concentration polarisation', '(c_m - c_p)/(c_b - c_p)', 'exp(J_w/k_m)', { kind: 'derived', origin: 'Film theory: convection toward the wall balanced by back-diffusion', needs: ['cp_film'] }) : eq('film', 'Wall concentration', 'c_m', 'c_b', { kind: 'closure', origin: 'Polarisation neglected' }),
    eq('wbal', 'Water balance along the vessel', 'pd(Q,A_x)', '-J_w', { kind: 'law', origin: 'Conservation of mass' }),
    eq('sbal', 'Salt balance along the vessel', 'pd(Q*c_b,A_x)', '-J_s', { kind: 'law', origin: 'Conservation of species' }),
    eq('rec', 'Recovery', 'r', 'Q_p/Q_f', { kind: 'definition' }),
    eq('rej', 'Salt rejection', 'Rej', '1 - c_p/c_f', { kind: 'definition' }),
    a.erd ? eq('sec', 'Specific energy consumption', 'SEC', '(Q_f*P_f - eta_erd*Q_b*P_b)/(eta_p*Q_p)', { kind: 'law', origin: 'First law: pump work less recovered brine energy', needs: ['erd'] }) : eq('sec', 'Specific energy consumption', 'SEC', 'Q_f*P_f/(eta_p*Q_p)', { kind: 'law', origin: 'First law: all feed is pumped to full pressure' }),
    eq('wmin', 'Least work of separation for salt-free permeate', 'w_min0', '(pi_f/r)*ln(1/(1 - r))', { kind: 'law', origin: 'Second law: reversible separation of a van ’t Hoff solution; the solver evaluates the same free-energy difference with the actual permeate salinity' }),
    ...(a.temp_ref ? [] : [eq('tcf', 'Temperature correction of water permeability', 'A_T', 'A_w*exp(E_T*(1/T_25 - 1/T))', { kind: 'empirical', origin: 'Arrhenius-type correction factor from membrane manufacturers’ design manuals; A_w is then the value at 25 °C' }),
      ...(a.salt_passage ? [eq('tcb', 'Temperature correction of salt permeability', 'B_T', 'B_s*exp(E_T*(1/T_25 - 1/T))', { kind: 'empirical', origin: 'Same correction factor applied to the salt permeability; B_s is then the value at 25 °C' })] : [])]),
  ],
  derivation: a => [
    { text: 'For a dilute salt solution the chemical potential of water is lowered in proportion to the number of dissolved particles. The pressure that restores equilibrium with pure water is the osmotic pressure.', tex: '\\pi = \\phi\\,i\\,\\frac{c}{M_s}\\,R\\,T' },
    { text: 'In the solution–diffusion picture water permeates in proportion to its chemical-potential difference, which is the applied pressure less the osmotic-pressure difference across the membrane.', tex: 'J_w = A\\,\\big(\\Delta P - (\\pi_m - \\pi_p)\\big)' },
    { text: 'Salt permeates by diffusion, driven by its concentration difference. The permeate concentration is the ratio of the two fluxes.', tex: 'J_s = B\\,(c_m - c_p),\\qquad c_p = \\frac{J_s}{J_w}' },
    ...(a.cp_film ? [{ text: 'In the boundary layer, convection of salt toward the wall is balanced by diffusion back to the bulk. Integrating across a film of thickness δ = D/k gives the wall concentration.', tex: '\\frac{c_m - c_p}{c_b - c_p} = \\exp\\!\\left(\\frac{J_w}{k}\\right)' }] : []),
    { text: 'Water and salt balances over an element of membrane area describe how the feed concentrates along the vessel.', tex: '\\frac{\\mathrm{d}Q}{\\mathrm{d}A} = -J_w,\\qquad \\frac{\\mathrm{d}(Q c_b)}{\\mathrm{d}A} = -J_s' },
    { text: 'The pump raises the feed to P_f' + (a.erd ? '; the energy-recovery device returns a fraction η_erd of the brine’s hydraulic energy.' : '; the brine energy is discarded.'), tex: a.erd ? '\\mathrm{SEC} = \\frac{Q_f P_f - \\eta_{erd} Q_b P_b}{\\eta_p\\,Q_p}' : '\\mathrm{SEC} = \\frac{Q_f P_f}{\\eta_p\\,Q_p}' },
    { text: 'A reversible process would apply, at each instant, exactly the local osmotic pressure. Integrating over the recovery gives the least work per unit of pure permeate.', tex: 'w_{min} = \\frac{\\pi_f}{r}\\,\\ln\\frac{1}{1-r}' },
  ],
  solve(v, a) {
    const S = massFrac(v.S_f), tC = v.T - 273.15, rho = R.seawaterDensity(tC, S * 1000), cf = rho * S;
    const kap = v.phi_o * 2 * C.R_u * v.T / M_NACL;
    const tcf = a.temp_ref ? 1 : Math.exp((v.T >= 298.15 ? 2640 : 3020) * (1 / 298.15 - 1 / v.T));
    const base = { A: v.A_w * tcf, B: a.salt_passage ? v.B_s * tcf : 0, k: v.k_m, kap, cf, Qf: v.Q_f, Pf: v.P_f, dp: v.dp_f, Am: v.A_m, n: Math.round(v.n_seg), polarise: a.cp_film };
    const m = roMarch(base), rec = m.Qp / v.Q_f, piF = kap * cf, piB = kap * m.cb;
    const secOf = q => (q.Qp > 0 ? (a.erd ? (v.Q_f * q.Pf - v.eta_erd * q.Qb * q.Pb) : v.Q_f * q.Pf) / (v.eta_p * q.Qp) : Infinity);
    const sec = secOf({ ...m, Pf: v.P_f }), wmin = roLeastWork(kap, v.Q_f, cf, m.Qp, m.cp, m.Qb, m.cb);
    const rej = 1 - m.cp / cf, Javg = m.Qp / v.A_m, power = sec * m.Qp;
    const Ps = N.linspace(Math.max(2e6, 0.6 * v.P_f), 8.5e6, 24);
    const sw = Ps.map(P => { const q = roMarch({ ...base, Pf: P, n: 40 }); return { sec: secOf({ ...q, Pf: P }), rec: q.Qp / v.Q_f, wmin: roLeastWork(kap, v.Q_f, cf, q.Qp, q.cp, q.Qb, q.cb) }; });
    const warnings = [];
    if (v.P_f - v.dp_f < 1.02 * kap * (m.cms.at(-1) - m.cps.at(-1))) warnings.push('The net driving pressure at the brine end is close to zero: the last elements produce almost no water. Lower the recovery or raise the pressure.');
    if (v.P_f < piF) warnings.push('The feed pressure is below the osmotic pressure of the feed. Only a trickle of poor-quality permeate is produced.');
    if (Javg > 25e-3 / 3600) warnings.push(`Average flux of ${lab(Javg * 3.6e6, 'L/(m² h)')} is above the range usually accepted for open-intake seawater (about 12–17 L/(m² h)); fouling would be rapid.`);
    if (m.cpfMax > 1.2 && a.cp_film) warnings.push(`The concentration-polarisation factor reaches ${lab(m.cpfMax)}; membrane suppliers typically limit it to 1.2 to control scaling.`);
    if (m.cp > 0.5) warnings.push(`Permeate salinity of ${lab(m.cp * 1000, 'mg/L')} exceeds the usual drinking-water guideline of about 500 mg/L total dissolved solids.`);
    return {
      scalars: [
        scalar('pi_f', 'Osmotic pressure of the feed', piF, 'Pa', { show: 'bar' }), scalar('pi_b', 'Osmotic pressure of the brine', piB, 'Pa', { show: 'bar' }),
        scalar('NDP', 'Net driving pressure at the inlet (bulk)', v.P_f - piF, 'Pa', { show: 'bar' }),
        scalar('J_w', 'Average water flux', Javg, 'm/s', { show: 'L/(m^2 h)' }), scalar('r', 'Recovery', rec, '1', { show: '%' }),
        scalar('Q_p', 'Permeate flow', m.Qp, 'm^3/s', { show: 'm^3/h' }), scalar('c_p', 'Permeate salinity', m.cp, 'kg/m^3', { show: 'mg/L' }), scalar('Rej', 'Salt rejection', rej, '1', { show: '%' }),
        scalar('Q_b', 'Brine flow', m.Qb, 'm^3/s', { show: 'm^3/h' }), scalar('c_b', 'Brine salinity', m.cb, 'kg/m^3', { show: 'g/L' }), scalar('CF', 'Concentration factor of the brine', m.cb / cf, '1'),
        scalar('CPF', 'Largest concentration-polarisation factor', m.cpfMax, '1'),
        scalar('SEC', 'Specific energy consumption', sec, 'J/m^3', { show: 'kWh/m^3' }), scalar('w_min', 'Least work of separation at this recovery', wmin, 'J/m^3', { show: 'kWh/m^3' }),
        scalar('eta_II', 'Second-law efficiency w_min/SEC', wmin / sec, '1', { show: '%' }), scalar('P_el', 'Pumping power', power, 'W', { show: 'kW' }),
      ],
      series: [
        line('flux', 'Water flux along the pressure vessel', 'Fraction of membrane area', '–', m.x, [{ label: 'Water flux', data: m.flux.map(q => q * 3.6e6) }], 'Flux', 'L/(m² h)'),
        line('conc', 'Salt concentration along the pressure vessel', 'Fraction of membrane area', '–', m.x, [{ label: 'Bulk feed', data: m.cbs }, { label: 'Membrane wall', data: m.cms, dash: true }, { label: 'Local permeate × 100', data: m.cps.map(q => q * 100) }], 'Concentration', 'g/L'),
        line('sec-p', 'Specific energy against feed pressure', 'Feed pressure', 'bar', Ps.map(q => q / 1e5), [{ label: 'Specific energy consumption', data: sw.map(q => (Number.isFinite(q.sec) ? q.sec / 3.6e6 : NaN)) }, { label: 'Least work of separation', data: sw.map(q => q.wmin / 3.6e6), dash: true }], 'Energy', 'kWh/m³'),
        line('rec-p', 'Recovery against feed pressure', 'Feed pressure', 'bar', Ps.map(q => q / 1e5), [{ label: 'Recovery', data: sw.map(q => q.rec * 100) }], 'Recovery', '%'),
      ],
      checks: [
        check('Water balance', (v.Q_f - m.Qp - m.Qb) / v.Q_f, 1e-10, 'Feed = permeate + brine (constant density)'),
        check('Salt balance', (v.Q_f * cf - m.Qp * m.cp - m.Qb * m.cb) / (v.Q_f * cf), 1e-10, 'Salt in feed = salt in permeate + salt in brine'),
        check('Second law: specific energy not below the least work of separation', Math.max(wmin - sec, 0) / piF, 0, `SEC = ${lab(sec / 3.6e6, 'kWh/m³')} against w_min = ${lab(wmin / 3.6e6, 'kWh/m³')}`),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const kap = 0.9 * 2 * C.R_u * 298.15 / M_NACL, cf = 35.8;
    const tiny = roMarch({ A: 3e-12, B: 0, k: 1e-4, kap, cf, Qf: 1, Pf: 6e6, dp: 0, Am: 1, n: 10, polarise: false });
    const q = roMarch({ A: 3e-12, B: 0, k: 1e-4, kap, cf, Qf: 2e-3, Pf: 6e6, dp: 0, Am: 400, n: 400, polarise: false }), rr = q.Qp / 2e-3;
    const film = roMarch({ A: 3e-12, B: 1e-12, k: 2e-5, kap, cf, Qf: 1, Pf: 6e6, dp: 0, Am: 1, n: 1, polarise: true });
    return [
      bench('Flux in the limit of zero recovery and perfect rejection', tiny.flux[0], 3e-12 * (6e6 - kap * cf), 'J_w = A (ΔP − π_f)', 1e-6),
      bench('Least work from stream free energies vs closed form', roLeastWork(kap, 2e-3, cf, q.Qp, 0, q.Qb, q.cb), kap * cf / rr * Math.log(1 / (1 - rr)), 'w_min = (π_f/r) ln[1/(1 − r)]', 1e-9),
      bench('Film-model wall concentration', (film.cms[0] - film.cps[0]) / (film.cbs[0] - film.cps[0]), Math.exp(film.flux[0] / 2e-5), '(c_m − c_p)/(c_b − c_p) = exp(J_w/k)', 1e-8),
      bench('Osmotic pressure of 35.8 g/L NaCl-equivalent at 25 °C', kap * cf / 1e5, 27.3, 'van ’t Hoff with φ = 0.9; seawater is about 27 bar', 1e-2),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(170, 120, 330, 90, 'd-body', 40)} ${S.path('M190 165 L480 165', 'd-liquid-line')} ${S.text(335, 150, 'feed channel', 'd-text d-small')} ${S.text(335, 190, 'permeate side', 'd-text d-small')}
      ${S.circle(90, 150, 24)} ${S.text(90, 155, 'HP', 'd-text d-small')} ${S.path('M20 150 L66 150', 'd-pipe')} ${S.path('M114 150 L172 150', 'd-pipe')}
      ${S.text(40, 135, 'feed', 'd-text d-small')} ${S.text(142, 136, lab(v.P_f / 1e5, 'bar'), 'd-text d-small')}
      ${S.path('M500 150 L600 150', 'd-pipe')} ${S.text(560, 136, 'brine', 'd-text d-small')}
      ${S.path('M335 210 L335 290 L600 290', 'd-pipe')} ${S.text(520, 278, 'permeate', 'd-text d-small')}
      ${[0, 1, 2, 3].map(i => S.arrow(230 + i * 70, 156, 230 + i * 70, 178)).join('')}
      ${a.erd ? S.rect(380, 40, 110, 40, 'd-body') + S.text(435, 65, 'ERD', 'd-text d-small') + S.path('M560 150 L560 60 L490 60', 'd-line') + S.path('M380 60 L140 60 L140 148', 'd-line') : S.text(560, 110, 'throttled', 'd-text d-small')}
      ${S.text(320, 330, `${lab(v.A_m, 'm²')} of membrane,  feed ${lab(massFrac(v.S_f) * 1000, 'g/kg')} at ${lab(v.T - 273.15, '°C')}`)}
    `);
  },
  experiment: {
    objective: 'Determine the water and salt permeabilities of a membrane and the feed-side mass-transfer coefficient, then verify predicted recovery and permeate quality for a full element.',
    apparatus: ['Cross-flow flat-sheet cell or single spiral-wound element in a pressure vessel', 'High-pressure positive-displacement pump with pulsation damper', 'Temperature-controlled feed tank with NaCl solution or pre-treated seawater', 'Back-pressure regulator on the concentrate line'],
    instruments: [{ name: 'Pressure transducers on feed, concentrate and permeate', measures: 'Trans-membrane and channel pressure drop', range: '0–100 bar', resolution: '±0.1 %' }, { name: 'Conductivity meters on feed, concentrate and permeate', measures: 'Salinity', range: '1 µS/cm–100 mS/cm', resolution: '±0.5 %' }, { name: 'Flow meters or timed mass collection', measures: 'Permeate and concentrate flow', range: '0.01–10 m³/h', resolution: '±0.5 %' }, { name: 'Pt100 in the feed', measures: 'Temperature', range: '0–50 °C', resolution: '±0.1 K' }],
    procedure: ['Compact the membrane with pure water at operating pressure until flux is steady; the slope of flux against pressure gives A.', 'Run with salt solution at several pressures and cross-flow velocities; record flux and permeate conductivity.', 'Extrapolate observed rejection to infinite cross-flow velocity to separate B from polarisation; the velocity dependence gives k.', 'Run the full element at design conditions and compare recovery, permeate salinity and pressure drop with the prediction.'],
    controls: ['Pure-water flux before and after each salt run to detect fouling or compaction', 'Salt and water balances closing within 2 %'],
    signatures: ['Flux linear in net driving pressure', 'Permeate concentration falling as flux rises', 'Flux declining along the element as bulk concentration rises'],
    safety: ['High-pressure liquid: rated fittings, shields and relief valve', 'Stored energy in pulsation dampers', 'Chemical handling for cleaning and preservation solutions'],
  },
  falsify: ['Water flux not proportional to net driving pressure at fixed temperature for a clean membrane.', 'Specific energy consumption measured below the least work of separation for the measured recovery and salinities.'],
  alternatives: [{ name: 'Spiegler–Kedem (irreversible thermodynamics) model', text: 'Adds a reflection coefficient to describe coupled convective salt transport; needed for nanofiltration and loose membranes.' }, { name: 'Pitzer or TEOS-10 osmotic pressure', text: 'Replaces the van ’t Hoff relation with a measured activity model; important above about 70 g/kg.' }, { name: 'Multi-stage or closed-circuit designs', text: 'Staging the pressure brings the applied pressure closer to the local osmotic pressure and lowers the energy use.' }],
  hazards: [{ hazard: 'High-pressure release', cause: 'Vessel end-cap or coupling failure', mitigation: 'Rated vessels, retaining rings checked, relief valves' }, { hazard: 'Membrane scaling and fouling', cause: 'Supersaturation at the wall, biological growth', mitigation: 'Antiscalant dosing, pre-treatment, recovery limits' }, { hazard: 'Brine discharge impact', cause: 'Dense saline effluent on the seabed', mitigation: 'Diffuser design and monitoring' }],
  standards: ['ASTM D4516 (standardising reverse-osmosis performance data)', 'ASTM D4194 (operating characteristics of reverse-osmosis devices)', 'ASME BPVC Section X (fibre-reinforced plastic pressure vessels)', 'WHO Guidelines for Drinking-water Quality'],
  limits: 'Single pass, single stage, steady state, sodium-chloride-equivalent salinity with a constant osmotic coefficient and constant density. Permeate-side pressure drop, fouling and the dependence of the mass-transfer coefficient on local cross-flow are neglected.',
  numerics: { method: 'Explicit marching in membrane area with a bracketed root solve for the local flux', order: 1, stability: 'Stable while each segment removes less than half the local flow', resolution: 'n_seg' },
  optimise: { objective: 'SEC', sense: 'min', vars: ['P_f', 'Q_f'], note: 'Specific energy has a minimum in recovery: too low wastes pumping on brine, too high raises the osmotic pressure.' },
  inverse: { series: 'flux', curve: 0, fit: ['A_w', 'k_m'] },
  extensions: ['Two-stage and two-pass configurations', 'Local mass-transfer coefficient from a Sherwood correlation', 'Boron rejection and pH dependence', 'Fouling and cleaning-cycle modelling'],
};

// ------------------------------------------------------------------ brine outfall: near-field dense jet and far-field plume
const brinePlume = {
  id: 'brine-discharge-plume',
  title: 'Brine outfall: inclined dense jet and far-field plume',
  module: 2, klass: 'I', domains: ['desalination', 'cfd', 'marine'],
  keywords: ['brine discharge', 'brine plume', 'brine outfall', 'outfall', 'dense jet', 'negatively buoyant jet', 'diffuser', 'dilution', 'mixing zone', 'densimetric froude', 'salinity excess', 'concentrate disposal', 'desalination brine', 'plume'],
  summary: 'Near-field dilution of a 60° inclined dense brine jet from published laboratory correlations, followed by a bottom-attached far-field plume advected and dispersed by the ambient current, tested against a mixing-zone salinity limit.',
  background: [
    'Reverse-osmosis concentrate is roughly twice as saline as seawater and therefore denser. Discharged through upward-inclined nozzles it rises, loses its vertical momentum, and falls back to the seabed, entraining ambient water throughout. Laboratory studies show that for a single jet in still water every geometric and dilution quantity scales with the port diameter multiplied by the densimetric Froude number; a 60° inclination gives close to the longest trajectory and the highest dilution.',
    'Beyond the near field the diluted brine spreads as a thin, stably stratified layer on the seabed. Vertical mixing is suppressed by the density difference, so further dilution comes mainly from lateral turbulent diffusion while the layer is carried by the current. Regulators commonly require the salinity excess to fall below a stated value at the edge of a mixing zone of the order of 100 m.',
  ],
  phenomena: ['Negatively buoyant jet', 'Turbulent entrainment', 'Density current on the seabed', 'Advection by ambient current', 'Lateral turbulent diffusion'],
  laws: ['mass', 'momentum', 'species', 'fick', 'archimedes'],
  refs: ['Roberts, P. J. W., Ferrier, A. & Daviero, G. (1997). Mixing in inclined dense jets. J. Hydraulic Engineering 123(8), 693–699.', 'Zeitoun, M. A., McIlhenny, W. F. & Reid, R. O. (1970). Conceptual designs of outfall systems for desalination plants. Research and Development Progress Report No. 550, Office of Saline Water, U.S. Department of the Interior.', 'Fischer, H. B., List, E. J., Koh, R. C. Y., Imberger, J. & Brooks, N. H. (1979). Mixing in Inland and Coastal Waters. Academic Press.', 'Brooks, N. H. (1960). Diffusion of sewage effluent in an ocean current. In Proc. 1st Int. Conf. on Waste Disposal in the Marine Environment, Pergamon, 246–267.', 'Millero, F. J. & Poisson, A. (1981). International one-atmosphere equation of state of seawater. Deep-Sea Research 28A, 625–629.'],
  inputs: [
    inp('Q_b', 'Total brine flow', 'm^3/s', 1, { min: 0.05, max: 20, aliases: ['brine flow', 'discharge', 'flow rate', 'effluent flow'] }),
    inp('S_b', 'Brine salinity', 'g/kg', 65, { min: 50, max: 90, kind: 'fluid', aliases: ['brine salinity', 'effluent salinity', 'concentrate salinity'] }),
    inp('S_a', 'Ambient salinity', 'g/kg', 35, { min: 30, max: 45, kind: 'environment', env: 'salinity', aliases: ['ambient salinity', 'seawater salinity', 'salinity'] }),
    inp('T_a', 'Water temperature', '°C', 22, { min: 5, max: 35, kind: 'environment', env: 'sea_surface_temp', aliases: ['water temperature', 'sea temperature', 'temperature'] }),
    inp('d', 'Port diameter', 'm', 0.15, { min: 0.05, max: 1, kind: 'geometry', aliases: ['port diameter', 'nozzle diameter', 'nozzle'] }),
    inp('n_p', 'Number of ports', '1', 20, { min: 1, max: 200, kind: 'geometry', aliases: ['ports', 'nozzles', 'number of ports'] }),
    inp('s_p', 'Port spacing', 'm', 6, { min: 1, max: 30, kind: 'geometry', aliases: ['port spacing', 'spacing'] }),
    inp('H', 'Water depth at the diffuser', 'm', 15, { min: 3, max: 100, kind: 'environment', env: 'water_depth', aliases: ['water depth', 'depth'] }),
    inp('U_a', 'Ambient current speed', 'm/s', 0.1, { min: 0.01, max: 1.5, kind: 'environment', env: 'current_speed', aliases: ['current', 'current speed', 'ambient current'] }),
    inp('K_y', 'Lateral turbulent diffusivity at the source scale', 'm^2/s', 0.05, { min: 0.001, max: 1, kind: 'environment', aliases: ['lateral diffusivity', 'eddy diffusivity'], src: 'Order of magnitude for coastal waters at scales of tens of metres; Fischer et al. (1979)' }),
    inp('D_x', 'Longitudinal dispersion coefficient', 'm^2/s', 1, { min: 0.01, max: 20, kind: 'environment', aliases: ['longitudinal dispersion', 'dispersion coefficient'] }),
    inp('x_mz', 'Mixing-zone radius', 'm', 100, { min: 10, max: 2000, aliases: ['mixing zone', 'mixing zone radius', 'compliance distance'] }),
    inp('dS_lim', 'Permitted salinity excess at the mixing-zone edge', 'g/kg', 2, { min: 0.2, max: 10, aliases: ['salinity limit', 'permitted excess', 'limit'], src: 'Site-specific permit value; limits of 1–2 g/kg or 5 % above ambient are common' }),
  ],
  assumptions: [
    asm('roberts', 'Near-field dilution follows Roberts, Ferrier & Daviero (1997), ending at the return point.', { why: 'Most widely used data set for 60° jets', alt: 'The more conservative impact-point dilution of Zeitoun et al. (1970) is used and no further near-field mixing is credited.' }),
    asm('eos', 'Densities come from the one-atmosphere seawater equation of state.', { why: 'Accurate for brine up to about 70 g/kg', alt: 'Density varies linearly with salinity with a haline contraction coefficient of 7.6 × 10⁻⁴ per g/kg.' }),
    asm('const_K', 'Lateral diffusivity is constant with distance.', { why: 'Conservative for a plume much narrower than the largest eddies', alt: 'Diffusivity grows with plume width to the four-thirds power (Brooks 1960).' }),
    asm('independent', 'Adjacent jets do not merge before they return to the seabed.', { why: 'Design intent of a well-spaced diffuser', alt: 'No correction is available here: a warning is raised and the single-jet dilution is reduced by the ratio of spacing to required spacing.' }),
  ],
  symbols: { rho_b: ['Brine density', 'kg/m^3'], rho_a: ['Ambient density', 'kg/m^3'], g_r: ['Reduced gravity', 'm/s^2'], u_j: ['Jet exit velocity', 'm/s'], F: ['Densimetric Froude number', '1'], y_t: ['Terminal rise height', 'm'], x_i: ['Impact-point distance', 'm'], S_i: ['Impact-point dilution', '1'], x_n: ['Return-point (end of near field) distance', 'm'], S_n: ['Near-field dilution', '1'], y_L: ['Thickness of the bottom layer', 'm'], b: ['Initial plume width', 'm'], M: ['Laterally integrated salinity excess', 'm'], x: ['Distance down-current', 'm'], t: ['Time', 's'], dS: ['Centre-line salinity excess', '1'], beta_S: ['Haline contraction coefficient', '1'] },
  equations: a => [
    a.eos ? eq('gr', 'Reduced gravity', 'g_r', 'g*(rho_b - rho_a)/rho_a', { kind: 'definition', needs: ['eos'] }) : eq('gr', 'Reduced gravity', 'g_r', 'g*beta_S*(S_b - S_a)', { kind: 'closure', origin: 'Linearised equation of state' }),
    eq('uj', 'Jet exit velocity', 'u_j', 'Q_b/(n_p*pi*d^2/4)', { kind: 'law', origin: 'Conservation of mass' }),
    eq('fr', 'Densimetric Froude number', 'F', 'u_j/sqrt(g_r*d)', { kind: 'definition' }),
    eq('yt', 'Terminal rise height', 'y_t', '2.2*d*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997), 60° jet in still water' }),
    eq('xi', 'Impact-point distance', 'x_i', '2.4*d*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997)' }),
    a.roberts ? eq('si', 'Impact-point dilution', 'S_i', '1.6*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997)', needs: ['roberts'] }) : eq('si', 'Impact-point dilution', 'S_i', '1.12*F', { kind: 'empirical', origin: 'Zeitoun et al. (1970)' }),
    ...(a.roberts ? [eq('xn', 'Return-point distance', 'x_n', '9*d*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997)' }), eq('sn', 'Near-field dilution', 'S_n', '2.6*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997)' })] : [eq('sn', 'Near-field dilution', 'S_n', 'S_i', { kind: 'closure', origin: 'No mixing credited beyond the impact point' })]),
    eq('yl', 'Bottom-layer thickness', 'y_L', '0.7*d*F', { kind: 'empirical', origin: 'Roberts, Ferrier & Daviero (1997)' }),
    eq('ade', 'Far-field transport of the laterally integrated excess', 'pd(M,t) + U_a*pd(M,x)', 'D_x*pd2(M,x)', { kind: 'law', origin: 'Conservation of salt, integrated across the plume' }),
    a.const_K ? eq('lat', 'Centre-line excess with lateral diffusion', 'dS', 'M/b*erf(b/(4*sqrt(K_y*x/U_a)))', { kind: 'derived', origin: 'Exact solution for a finite line source with constant diffusivity', needs: ['const_K'] }) : eq('lat', 'Centre-line excess with lateral diffusion', 'dS', 'M/b*erf(sqrt(1.5/((1 + 8*K_y*x/(U_a*b^2))^3 - 1)))', { kind: 'derived', origin: 'Brooks (1960) four-thirds-law solution' }),
  ],
  derivation: a => [
    { text: 'For a round dense jet in still water the only parameters are the kinematic fluxes of volume, momentum and buoyancy. Far from the nozzle the volume flux is unimportant, leaving one length scale, proportional to d·F.', tex: 'F = \\frac{u_j}{\\sqrt{g\'d}},\\qquad g\' = g\\,\\frac{\\rho_b-\\rho_a}{\\rho_a}' },
    { text: 'Dimensional analysis then requires every length to be a constant times d·F and every dilution to be a constant times F; the constants are measured.', tex: '\\frac{y_t}{dF} = 2.2,\\quad \\frac{x_i}{dF} = 2.4,\\quad \\frac{S_i}{F} = ' + (a.roberts ? '1.6,\\quad \\frac{x_n}{dF} = 9,\\quad \\frac{S_n}{F} = 2.6' : '1.12') },
    { text: 'In the far field, integrating the salt balance across the plume removes lateral diffusion and leaves a one-dimensional advection–dispersion equation for the integrated excess M.', tex: '\\frac{\\partial M}{\\partial t} + U\\frac{\\partial M}{\\partial x} = D_x\\frac{\\partial^2 M}{\\partial x^2},\\qquad M = \\int \\Delta S\\,\\mathrm{d}y' },
    { text: 'Lateral diffusion widens the plume and lowers the centre-line value. For a source of width b and ' + (a.const_K ? 'constant diffusivity' : 'diffusivity growing as the four-thirds power of plume width') + ':', tex: a.const_K ? '\\frac{\\Delta S_{max}}{\\Delta S_0} = \\operatorname{erf}\\!\\left(\\frac{b}{4\\sqrt{K_y x/U}}\\right)' : '\\frac{\\Delta S_{max}}{\\Delta S_0} = \\operatorname{erf}\\sqrt{\\frac{3/2}{\\left(1+\\tfrac{2}{3}\\beta x/b\\right)^3-1}},\\qquad \\beta = \\frac{12K_y}{Ub}' },
    { text: 'The salinity excess at any point is the initial excess divided by the product of near-field and far-field dilutions.', tex: '\\Delta S(x) = \\frac{S_b - S_a}{S_n\\,S_{ff}(x)}' },
  ],
  solve(v, a) {
    const Sb = massFrac(v.S_b), Sa = massFrac(v.S_a), tC = v.T_a - 273.15, np = Math.max(1, Math.round(v.n_p));
    const rhoA = R.seawaterDensity(tC, Sa * 1000), rhoB = a.eos ? R.seawaterDensity(tC, Sb * 1000) : rhoA * (1 + 0.76 * (Sb - Sa));
    const gr = g * (rhoB - rhoA) / rhoA, uj = v.Q_b / (np * Math.PI * v.d ** 2 / 4), F = uj / Math.sqrt(gr * v.d), dF = v.d * F;
    const yt = 2.2 * dF, xi = 2.4 * dF, Si0 = (a.roberts ? 1.6 : 1.12) * F, xn = a.roberts ? 9 * dF : xi, yL = 0.7 * dF;
    // jets merge if the spacing is less than about the plume width at impact (≈ 2 d F); used only for the warning and penalty
    const sReq = 2 * dF, merge = np > 1 && v.s_p < sReq, pen = !a.independent && merge ? v.s_p / sReq : 1;
    const Si = Math.max(1, Si0 * pen), Sn = Math.max(1, (a.roberts ? 2.6 : 1.12) * F * pen);
    const dS0 = Sb - Sa, dSn = dS0 / Sn, b = (np - 1) * v.s_p + dF;
    const latOf = x => { if (x <= 0) return 1; return a.const_K ? erfFn(b / (4 * Math.sqrt(v.K_y * x / v.U_a))) : erfFn(Math.sqrt(1.5 / (Math.pow(1 + 8 * v.K_y * x / (v.U_a * b * b), 3) - 1))); };
    const excessAt = r => (r <= xi ? dS0 / (1 + (Si - 1) * r / xi) : r <= xn ? dS0 / (Si + (Sn - Si) * (r - xi) / Math.max(xn - xi, 1e-9)) : dSn * latOf(r - xn));
    // far field: laterally integrated excess from the 1-D advection–dispersion solver, started with clean water
    const Lff = Math.max(3 * v.x_mz, 20 * dF, 200), nx = Math.round(N.clamp(Lff * v.U_a / (2 * v.D_x) + 1, 41, 201));
    const dxx = Lff / (nx - 1), dtEst = 0.4 * Math.min(dxx / v.U_a, dxx * dxx / (2 * v.D_x)), tEnd = Math.min(1.5 * Lff / v.U_a, 20000 * dtEst);
    const ff = N.advectDiffuse1D({ u: v.U_a, D: v.D_x, L: Lff, nx, tEnd, c0: () => 0, inlet: dSn * b, frames: 40 });
    const xr = ff.x.map(q => q + xn), lat = ff.x.map(latOf);
    const frames = ff.snaps.map(sn => sn.map((M, i) => M / b * lat[i] * 1000));
    const iq = Math.min(nx - 1, Math.round(0.2 * (nx - 1))), established = tEnd >= 1.4 * Lff / v.U_a;
    const dSmz = excessAt(v.x_mz), margin = v.dS_lim - dSmz, ok = margin >= 0;
    const rs = N.logspace(Math.max(0.2 * xi, 0.1), Math.max(10 * v.x_mz, 5 * xn), 80), ex = rs.map(r => excessAt(r) * 1000);
    // schematic centre-line trajectory through the measured top and impact points
    const tj = N.linspace(0, 1, 40), xt = tj.map(q => q * xi), zt = tj.map(q => 4 * yt * q * (1 - q));
    const xLimit = (() => { if (excessAt(rs[0]) <= v.dS_lim) return rs[0]; const far = 1e3 * Math.max(v.x_mz, xn); if (excessAt(far) > v.dS_lim) return Infinity; return N.bisect(r => excessAt(r) - v.dS_lim, rs[0], far, 1e-9); })();
    const warnings = [];
    if (F < 10) warnings.push(`Densimetric Froude number ${lab(F)} is below about 10–20: the correlations were established at higher values and the jet may attach to the bed near the nozzle. Use smaller or more ports.`);
    if (yt > 0.75 * v.H) warnings.push(`The jet rises ${lab(yt, 'm')} in ${lab(v.H, 'm')} of water and will interact with the surface, reducing dilution. Deeper water or a lower exit velocity is needed.`);
    if (merge) warnings.push(`Port spacing of ${lab(v.s_p, 'm')} is less than the ${lab(sReq, 'm')} needed to keep adjacent jets separate; single-jet dilution will not be achieved.`);
    if (!ok) warnings.push(`Salinity excess at the mixing-zone edge is ${lab(dSmz * 1000, 'g/kg')}, above the permitted ${lab(v.dS_lim * 1000, 'g/kg')}.`);
    if (!established) warnings.push('The far-field simulation was stopped before the plume front crossed the whole domain; the animation shows the early development only.');
    return {
      scalars: [
        scalar('rho_a', 'Ambient density', rhoA, 'kg/m^3'), scalar('rho_b', 'Brine density', rhoB, 'kg/m^3'), scalar('g_r', 'Reduced gravity', gr, 'm/s^2'),
        scalar('u_j', 'Jet exit velocity', uj, 'm/s'), scalar('F', 'Densimetric Froude number', F, '1'),
        scalar('y_t', 'Terminal rise height', yt, 'm'), scalar('x_i', 'Impact-point distance', xi, 'm'), scalar('S_i', 'Impact-point dilution', Si, '1'),
        scalar('x_n', 'End of the near field', xn, 'm'), scalar('S_n', 'Near-field dilution', Sn, '1'), scalar('y_L', 'Bottom-layer thickness', yL, 'm'),
        scalar('dS_n', 'Salinity excess at the end of the near field', dSn, '1', { show: 'g/kg' }), scalar('b', 'Initial far-field plume width', b, 'm'),
        scalar('dS_mz', 'Salinity excess at the mixing-zone edge', dSmz, '1', { show: 'g/kg' }), scalar('S_mz', 'Total dilution at the mixing-zone edge', dS0 / dSmz, '1'),
        scalar('margin', 'Margin to the permitted excess', margin, '1', { show: 'g/kg', text: ok ? undefined : `Limit exceeded by ${lab(-margin * 1000, 'g/kg')}` }),
        scalar('x_lim', 'Distance at which the excess falls to the permitted value', xLimit, 'm', { text: Number.isFinite(xLimit) ? undefined : 'Not reached within the modelled range' }),
        scalar('t_adv', 'Travel time to the mixing-zone edge', v.x_mz / v.U_a, 's', { show: 'min' }),
      ],
      series: [
        line('excess', 'Centre-line salinity excess against distance', 'Distance from the diffuser', 'm', rs, [{ label: 'Salinity excess', data: ex }, { label: 'Permitted excess', data: rs.map(() => v.dS_lim * 1000), dash: true }], 'Salinity excess', 'g/kg', { logx: true, logy: true, marker: [v.x_mz, dSmz * 1000], note: 'Near-field values are interpolated between the nozzle, the impact point and the return point.' }),
        line('dilution', 'Total dilution against distance', 'Distance from the diffuser', 'm', rs, [{ label: 'Dilution', data: rs.map(r => dS0 / excessAt(r)) }], 'Dilution', '–', { logx: true, logy: true }),
        line('trajectory', 'Schematic jet trajectory', 'Horizontal distance', 'm', xt, [{ label: 'Upper edge of the jet (parabola through the measured rise height and impact point)', data: zt }, { label: 'Water surface', data: xt.map(() => v.H), dash: true }], 'Height above port', 'm'),
      ],
      anims: [anim('plume', 'Far-field salinity excess developing down-current', 'Distance from the diffuser', 'm', xr, frames, ff.times, 'Centre-line salinity excess', 'g/kg')],
      checks: [
        check('Far-field salt flux conserved', established ? (ff.final[iq] - dSn * b) / (dSn * b) : 0, 2e-2, 'Laterally integrated excess a short way down-current equals the source value once the plume is established'),
        check('Volume flux through the ports', (uj * np * Math.PI * v.d ** 2 / 4 - v.Q_b) / v.Q_b, 1e-12, 'Port velocity consistent with total flow'),
        check('Dilution increases monotonically with distance', rs.some((r, i) => i > 0 && ex[i] > ex[i - 1] * (1 + 1e-9)) ? 1 : 0, 0, 'Salinity excess never rises away from the source'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const r = this.solve(v, a), F = val(r, 'F');
    const b = 50, K = 0.05, U = 0.1, x = 500, sig = Math.sqrt(2 * K * x / U);
    // superposition of point-source Gaussians across a finite line source, evaluated numerically
    const ys = N.linspace(-b / 2, b / 2, 2001), num = N.trapz(ys, ys.map(y => Math.exp(-y * y / (2 * sig * sig)) / (sig * Math.sqrt(2 * Math.PI))));
    const adv = N.advectDiffuse1D({ u: 0.2, D: 0.5, L: 200, nx: 201, tEnd: 2000, c0: () => 0, inlet: 1, frames: 2 });
    return [
      bench('Rise height over d·F', val(r, 'y_t') / (v.d * F), 2.2, 'Roberts, Ferrier & Daviero (1997)', 1e-12),
      bench('Finite line-source centre-line factor vs Gaussian superposition', erfFn(b / (4 * Math.sqrt(K * x / U))), num, 'Exact solution of the lateral diffusion equation', 1e-5),
      bench('Far-field solver reaches the conservative steady state', adv.final[100], 1, 'Steady solution of the advection–dispersion equation with constant inlet', 1e-3),
      bench('Seawater density at 5 °C and salinity 35', R.seawaterDensity(5, 35), 1027.675, 'Check value of the one-atmosphere equation of state, Millero & Poisson (1981)', 1e-6),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.path('M30 50 L610 50', 'd-liquid-line')} ${S.text(600, 40, 'sea surface', 'd-text d-small', 'end')}
      ${S.path('M30 290 L610 290', 'd-ground')}
      ${S.rect(60, 270, 60, 20, 'd-pipe-fill', 3)} ${S.path('M110 270 L128 240', 'd-pipe')}
      ${S.path('M128 240 Q190 60 260 150 Q300 210 320 284', 'd-line d-hazard')}
      ${S.path('M320 286 L600 286 L600 268 Q450 262 320 270 Z', 'd-hazard')}
      ${S.text(170, 262, '60°', 'd-text d-small')} ${S.dim(215, 110, 215, 288, 'y_t')}
      ${S.dim(128, 320, 320, 320, 'x_i')} ${S.text(460, 258, 'bottom-attached plume', 'd-text d-small')}
      ${S.arrow(430, 120, 520, 120)} ${S.text(475, 108, `current ${lab(v.U_a, 'm/s')}`)}
      ${S.dim(40, 52, 40, 288, `H = ${lab(v.H, 'm')}`)}
      ${S.text(320, 24, `${Math.round(v.n_p)} ports of ${lab(v.d * 1000, 'mm')},  brine ${lab(massFrac(v.S_b) * 1000, 'g/kg')} into ${lab(massFrac(v.S_a) * 1000, 'g/kg')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the trajectory and dilution of an inclined dense jet in a laboratory tank, and survey the salinity field around an operating outfall to verify compliance at the mixing-zone edge.',
    apparatus: ['Glass-walled tank at least 60 nozzle-Froude lengths long with a false floor', 'Constant-head supply of dyed salt solution through a 60° nozzle', 'For field work: survey vessel with towed or profiling CTD and a bottom-mounted current meter'],
    instruments: [{ name: 'Laser-induced fluorescence system (laser sheet, camera, Rhodamine tracer)', measures: 'Instantaneous and mean concentration field', range: 'Dilution 1–200', resolution: '±5 %' }, { name: 'Micro-conductivity probes', measures: 'Point salinity at the impact point and in the bottom layer', range: '0–80 g/kg', resolution: '±0.05 g/kg' }, { name: 'CTD profiler (field)', measures: 'Salinity, temperature and depth', range: '0–70 g/kg', resolution: '±0.01 g/kg' }, { name: 'Acoustic Doppler current profiler (field)', measures: 'Ambient current profile', range: '0–3 m/s', resolution: '±0.01 m/s' }],
    procedure: ['Set the density difference and flow to give Froude numbers between 20 and 60.', 'Record at least 300 s of concentration images after the flow is established; average to obtain the mean field.', 'Extract rise height, impact distance and minimum dilution at the bed; normalise by d·F and by F.', 'In the field, run radial CTD transects within 1 m of the bed at slack and at peak current.'],
    controls: ['Verify nozzle Reynolds number above about 2000 so the jet is turbulent', 'Background salinity transects up-current of the outfall'],
    signatures: ['Rise height and impact distance proportional to d·F', 'Dilution proportional to F', 'A thin saline layer on the bed with a sharp upper interface'],
    safety: ['Class 3B/4 laser controls for fluorescence work', 'Vessel and over-side working procedures in the field'],
  },
  falsify: ['Normalised rise height or impact dilution that varies systematically with Froude number above about 20 in still water.', 'Field salinity excess at the mixing-zone edge persistently above the prediction under currents no weaker than assumed.'],
  alternatives: [{ name: 'Integral jet models (CORJET, VISJET, UM3)', text: 'Solve entrainment equations along the trajectory and handle ambient current and stratification directly.' }, { name: 'Three-dimensional CFD with a buoyancy-modified turbulence model', text: 'Resolves bed interaction, merging jets and bathymetry at much greater cost.' }, { name: 'Density-current models for the far field', text: 'On a sloping bed the layer flows down-slope under gravity; a gravity-current model then replaces passive advection.' }],
  hazards: [{ hazard: 'Hypersaline layer on the seabed', cause: 'Insufficient dilution or weak currents', mitigation: 'Diffuser redesign, pre-dilution with cooling water, monitoring' }, { hazard: 'Recirculation into the intake', cause: 'Intake located down-current or down-slope of the outfall', mitigation: 'Separation distance and intake elevation' }, { hazard: 'Toxicity of process chemicals', cause: 'Antiscalants, coagulants and cleaning residues in the concentrate', mitigation: 'Treatment before discharge and effluent limits' }],
  standards: ['California Ocean Plan, desalination amendment (State Water Resources Control Board)', 'UNEP guidance on desalination: resource and guidance manual for environmental impact assessments', 'WHO guidance on desalination for safe water supply', 'ISO 5667-9 (water quality — sampling from marine waters)'],
  limits: 'Near field: single round jets at 60° in deep, unstratified, stagnant water with Froude numbers above about 20. Far field: flat bed, steady uniform current, no vertical mixing or gravitational spreading. Tidal reversal and re-entrainment of earlier discharge are not represented.',
  numerics: { method: 'Algebraic near-field correlations; first-order upwind advection with explicit diffusion for the far-field front', order: 1, stability: 'Time step limited to 0.4 of the advective and diffusive limits' },
  optimise: { objective: 'dS_mz', sense: 'min', vars: ['d', 'n_p'], note: 'Smaller, more numerous ports raise the Froude number and the dilution at the cost of head loss.' },
  inverse: { series: 'excess', curve: 0, fit: ['K_y'] },
  extensions: ['Ambient cross-flow effects on the near field', 'Merging of adjacent jets from a multiport diffuser', 'Sloping-bed gravity current', 'Tidal cycling and build-up of background salinity'],
};

// ------------------------------------------------------------------ scaling potential of RO concentrate
const KSP_GYPSUM = Math.pow(10, -4.58), K_CASO4 = Math.pow(10, 2.30), M_CA = 0.040078, M_SO4 = 0.09606;
const daviesLog = (z, I) => -0.509 * z * z * (Math.sqrt(I) / (1 + Math.sqrt(I)) - 0.3 * I);
/** Gypsum saturation ratio from total molar concentrations (mol/L) and ionic strength (mol/L). */
function gypsumSR(mCa, mSO4, I, pairing) {
  const g2 = Math.pow(10, 2 * daviesLog(2, Math.min(I, 2)));
  let p = 0;
  if (pairing) { const q = K_CASO4 * g2, bq = mCa + mSO4 + 1 / q; p = 0.5 * (bq - Math.sqrt(Math.max(bq * bq - 4 * mCa * mSO4, 0))); }
  return { SR: g2 * (mCa - p) * (mSO4 - p) / KSP_GYPSUM, gamma: Math.sqrt(g2), paired: mCa > 0 ? p / mCa : 0 };
}
/** Langelier saturation pH from concentrations in mg/L and temperature in kelvin. */
const langelierPHs = (tds, T, caHard, alk) => 9.3 + (Math.log10(tds) - 1) / 10 + (-13.12 * Math.log10(T) + 34.55) - (Math.log10(caHard) - 0.4) - Math.log10(alk);

const scaling = {
  id: 'scaling-saturation-index',
  title: 'Scaling potential of reverse-osmosis concentrate',
  module: 2, klass: 'I', domains: ['desalination', 'chemical'],
  keywords: ['scaling', 'saturation index', 'langelier', 'lsi', 'gypsum', 'calcium sulphate', 'calcium sulfate', 'calcium carbonate', 'scale formation', 'antiscalant', 'solubility product', 'concentrate', 'recovery limit', 'supersaturation'],
  summary: 'Langelier saturation index for calcium carbonate and saturation ratio for gypsum in membrane concentrate as functions of recovery, with the recovery at which each scale becomes possible.',
  background: [
    'As a membrane system withdraws permeate, sparingly soluble salts in the remaining concentrate can exceed their solubility and deposit on the membrane. The two most common scales in brackish-water plants are calcium carbonate and gypsum (calcium sulphate dihydrate).',
    'Calcium carbonate scaling is conventionally assessed with the Langelier saturation index, the difference between the actual pH and the pH at which the water would be just saturated. A positive index indicates a tendency to deposit. The index is reliable only at moderate salinity; for sea-water-strength concentrates the Stiff and Davis index is used instead.',
    'Gypsum scaling is assessed from the ratio of the ion activity product to the solubility product. Activity coefficients are estimated here with the Davies equation and the neutral CaSO₄ ion pair is accounted for explicitly; both are adequate up to an ionic strength of about 0.5 mol/L.',
  ],
  phenomena: ['Concentration of rejected ions', 'Carbonate equilibrium and pH shift', 'Ion activity and ion pairing', 'Supersaturation and nucleation'],
  laws: ['mass', 'species'],
  refs: ['Langelier, W. F. (1936). The analytical control of anti-corrosion water treatment. J. American Water Works Association 28, 1500–1521.', 'Stiff, H. A. & Davis, L. E. (1952). A method for predicting the tendency of oil field waters to deposit calcium carbonate. Petroleum Transactions AIME 195, 213–216.', 'Davies, C. W. (1962). Ion Association. Butterworths, London.', 'Stumm, W. & Morgan, J. J. (1996). Aquatic Chemistry, 3rd ed., Wiley.', 'Parkhurst, D. L. & Appelo, C. A. J. (2013). Description of input and examples for PHREEQC version 3. U.S. Geological Survey Techniques and Methods 6-A43.'],
  inputs: [
    inp('Ca', 'Calcium in the feed (as Ca²⁺)', 'mg/L', 150, { min: 1, max: 1500, kind: 'fluid', aliases: ['calcium'] }),
    inp('SO4', 'Sulphate in the feed (as SO₄²⁻)', 'mg/L', 600, { min: 1, max: 5000, kind: 'fluid', aliases: ['sulphate', 'sulfate'] }),
    inp('Alk', 'Alkalinity of the feed (as CaCO₃)', 'mg/L', 180, { min: 5, max: 1000, kind: 'fluid', aliases: ['alkalinity', 'bicarbonate'] }),
    inp('TDS', 'Total dissolved solids of the feed', 'mg/L', 2000, { min: 100, max: 12000, kind: 'fluid', aliases: ['tds', 'total dissolved solids', 'salinity'] }),
    inp('pH', 'Feed pH', '1', 7.5, { min: 5.5, max: 9, kind: 'fluid', aliases: ['ph'] }),
    inp('T', 'Temperature', '°C', 25, { min: 5, max: 45, aliases: ['temperature'] }),
    inp('r', 'System recovery', '%', 75, { min: 0, max: 92, aliases: ['recovery'] }),
    inp('Rej', 'Salt rejection of the membrane', '%', 99, { min: 90, max: 99.9, aliases: ['rejection'] }),
    inp('CPF', 'Concentration-polarisation factor at the membrane wall', '1', 1.13, { min: 1, max: 2, aliases: ['polarisation factor', 'beta factor'], src: 'Typical design value; suppliers recommend a maximum of about 1.2' }),
  ],
  assumptions: [
    asm('co2_free', 'Carbon dioxide passes the membrane freely while bicarbonate is rejected, so concentrate pH rises with the logarithm of the concentration factor.', { why: 'Standard approximation for un-acidified feed', alt: 'Concentrate pH is taken equal to feed pH.' }),
    asm('ion_pair', 'Part of the calcium and sulphate is bound in the neutral CaSO₄ ion pair.', { why: 'Needed to reproduce the measured solubility of gypsum', alt: 'Ion pairing is ignored, which typically raises the computed gypsum saturation ratio by a factor of about 1.5 to 2.' }),
    asm('wall', 'Saturation is evaluated at the membrane wall, where concentration is raised by the polarisation factor.', { why: 'Scale forms where the concentration is highest', alt: 'Saturation is evaluated in the bulk concentrate.' }),
    asm('real_rej', 'A small fraction of the salt passes into the permeate.', { why: 'Slightly lowers the concentration factor', alt: 'Rejection is complete: the concentration factor is 1/(1 − r).' }),
  ],
  symbols: { f_w: ['Concentration factor where saturation is evaluated', '1'], CF: ['Concentration factor', '1'], LSI: ['Langelier saturation index', '1'], pH_c: ['Concentrate pH', '1'], pH_s: ['Saturation pH', '1'], A_L: ['Langelier solids term', '1'], B_L: ['Langelier temperature term', '1'], C_L: ['Langelier calcium term', '1'], D_L: ['Langelier alkalinity term', '1'], c_ref: ['Reference concentration 1 mg/L', 'kg/m^3'], T_ref: ['Reference temperature 1 K', 'K'], Ca_h: ['Calcium hardness of concentrate as CaCO₃', 'kg/m^3'], I_s: ['Ionic strength over 1 mol/L', '1'], gamma: ['Activity coefficient of a divalent ion', '1'], m_Ca: ['Free calcium over 1 mol/L', '1'], m_SO4: ['Free sulphate over 1 mol/L', '1'], m_pair: ['CaSO₄ ion pair over 1 mol/L', '1'], K_sp: ['Solubility product of gypsum', '1'], K_a: ['Association constant of the CaSO₄ ion pair', '1'], SR: ['Gypsum saturation ratio', '1'] },
  equations: a => [
    a.real_rej ? eq('cf', 'Concentration factor', 'CF', '(1 - r*(1 - Rej))/(1 - r)', { kind: 'law', origin: 'Salt balance over the membrane system', needs: ['real_rej'] }) : eq('cf', 'Concentration factor', 'CF', '1/(1 - r)', { kind: 'law', origin: 'Salt balance with complete rejection' }),
    a.co2_free ? eq('phc', 'Concentrate pH', 'pH_c', 'pH + log10(CF)', { kind: 'derived', origin: 'Carbonate equilibrium with bicarbonate concentrated and CO₂ unchanged', needs: ['co2_free'] }) : eq('phc', 'Concentrate pH', 'pH_c', 'pH', { kind: 'closure' }),
    ...(a.wall ? [eq('fw', 'Concentration factor at the membrane wall', 'f_w', 'CF*CPF', { kind: 'derived', origin: 'Bulk concentration factor raised by concentration polarisation', needs: ['wall'] })] : [eq('fw', 'Concentration factor where saturation is evaluated', 'f_w', 'CF', { kind: 'closure', origin: 'Bulk concentrate' })]),
    eq('al', 'Solids term', 'A_L', '(log10(f_w*TDS/c_ref) - 1)/10', { kind: 'empirical', origin: 'Langelier (1936), simplified form' }),
    eq('bl', 'Temperature term', 'B_L', '34.55 - 13.12*log10(T/T_ref)', { kind: 'empirical', origin: 'Langelier (1936), simplified form' }),
    eq('cah', 'Calcium hardness', 'Ca_h', '2.497*f_w*Ca', { kind: 'definition', origin: 'Ratio of the molar masses of CaCO₃ and Ca' }),
    eq('cl', 'Calcium term', 'C_L', 'log10(Ca_h/c_ref) - 0.4', { kind: 'empirical', origin: 'Langelier (1936), simplified form' }),
    eq('dl', 'Alkalinity term', 'D_L', 'log10(f_w*Alk/c_ref)', { kind: 'empirical', origin: 'Langelier (1936), simplified form' }),
    eq('phs', 'Saturation pH', 'pH_s', '9.3 + A_L + B_L - C_L - D_L', { kind: 'empirical', origin: 'Langelier (1936)' }),
    eq('lsi', 'Langelier saturation index', 'LSI', 'pH_c - pH_s', { kind: 'definition' }),
    eq('is', 'Ionic strength', 'I_s', '2.5e-5*f_w*TDS/c_ref', { kind: 'empirical', origin: 'Langelier’s approximation from total dissolved solids' }),
    eq('dav', 'Davies activity coefficient', 'log10(gamma)', '-0.509*4*(sqrt(I_s)/(1 + sqrt(I_s)) - 0.3*I_s)', { kind: 'empirical', origin: 'Davies (1962), 25 °C, divalent ion' }),
    ...(a.ion_pair ? [eq('pair', 'Ion-pair equilibrium', 'm_pair', 'K_a*gamma^2*m_Ca*m_SO4', { kind: 'law', origin: 'Mass action for Ca²⁺ + SO₄²⁻ ⇌ CaSO₄⁰', needs: ['ion_pair'] })] : []),
    eq('sr', 'Gypsum saturation ratio', 'SR', 'gamma^2*m_Ca*m_SO4/K_sp', { kind: 'law', origin: 'Ion activity product over solubility product' }),
  ],
  derivation: a => [
    { text: 'A salt balance over the system gives the factor by which rejected ions are concentrated.', tex: a.real_rej ? '\\mathrm{CF} = \\frac{1 - r\\,(1-R)}{1-r}' : '\\mathrm{CF} = \\frac{1}{1-r}' },
    { text: 'Calcium carbonate is in equilibrium when the pH equals the saturation pH. In Langelier’s simplified form this depends on dissolved solids, temperature, calcium hardness and alkalinity.', tex: '\\mathrm{pH}_s = 9.3 + A + B - C - D' },
    { text: 'The index is the distance of the actual pH from saturation; positive values indicate a tendency to deposit calcium carbonate.', tex: '\\mathrm{LSI} = \\mathrm{pH} - \\mathrm{pH}_s' },
    ...(a.co2_free ? [{ text: 'With bicarbonate concentrated by CF and dissolved CO₂ unchanged, the first dissociation equilibrium of carbonic acid raises the pH.', tex: '\\mathrm{pH}_c = \\mathrm{pH}_f + \\log_{10}\\mathrm{CF}' }] : []),
    { text: 'For gypsum the driving force is the ion activity product relative to the solubility product. Activity coefficients come from the Davies equation.', tex: '\\mathrm{SR} = \\frac{\\gamma_\\pm^2\\,[\\mathrm{Ca^{2+}}][\\mathrm{SO_4^{2-}}]}{K_{sp}},\\qquad \\log_{10}\\gamma = -0.509\\,z^2\\left(\\frac{\\sqrt I}{1+\\sqrt I} - 0.3I\\right)' },
    ...(a.ion_pair ? [{ text: 'Free-ion concentrations are reduced by formation of the neutral ion pair, found from a quadratic mass-action equation.', tex: '[\\mathrm{CaSO_4^0}] = K_a\\,\\gamma_\\pm^2\\,[\\mathrm{Ca^{2+}}][\\mathrm{SO_4^{2-}}]' }] : []),
  ],
  solve(v, a) {
    const mg = q => q * 1000; // kg/m³ → mg/L
    const cfOf = r => (a.real_rej ? (1 - r * (1 - v.Rej)) / (1 - r) : 1 / (1 - r));
    const state = r => {
      const CF = cfOf(r), f = CF * (a.wall ? v.CPF : 1);
      const tds = mg(v.TDS) * f, I = 2.5e-5 * tds, pHc = a.co2_free ? v.pH + Math.log10(CF) : v.pH;
      const pHs = langelierPHs(tds, v.T, 2.497 * mg(v.Ca) * f, mg(v.Alk) * f);
      const gy = gypsumSR(v.Ca * f / M_CA / 1000, v.SO4 * f / M_SO4 / 1000, I, a.ion_pair);
      return { CF, f, tds, I, pHc, pHs, LSI: pHc - pHs, ...gy };
    };
    const now = state(v.r), feed = state(0);
    const limit = fn => { if (fn(0) >= 0) return 0; if (fn(0.95) < 0) return 0.95; return N.bisect(fn, 0, 0.95, 1e-10); };
    const rL = limit(r => state(r).LSI), rG = limit(r => state(r).SR - 1), rG2 = limit(r => state(r).SR - 2.3);
    const rs = N.linspace(0, 0.92, 70), sw = rs.map(state);
    const warnings = [];
    if (now.tds > 10000) warnings.push(`Concentrate dissolved solids of ${lab(now.tds, 'mg/L')} are beyond the range of the Langelier index (about 10 000 mg/L). Use the Stiff and Davis index for calcium carbonate at this salinity.`);
    if (now.I > 0.5) warnings.push(`Ionic strength of ${lab(now.I, 'mol/L')} is beyond the validity of the Davies equation (about 0.5 mol/L); the gypsum ratio is then overstated. A Pitzer model is needed for sea-water-strength concentrates.`);
    if (now.LSI > 0) warnings.push(`The concentrate has a positive Langelier index (${lab(now.LSI)}): calcium carbonate can deposit unless acid or antiscalant is dosed. Antiscalants are typically effective up to an index of about 1.8–2.5.`);
    if (now.SR > 1) warnings.push(`Gypsum is supersaturated (ratio ${lab(now.SR)}). Antiscalants typically control gypsum up to a ratio of about 2.3; beyond that, lower the recovery.`);
    return {
      scalars: [
        scalar('CF', 'Concentration factor of the bulk concentrate', now.CF, '1'), scalar('TDS_c', 'Dissolved solids where saturation is evaluated', now.tds / 1000, 'kg/m^3', { show: 'mg/L' }),
        scalar('pH_c', 'Concentrate pH', now.pHc, '1'), scalar('pH_s', 'Saturation pH of the concentrate', now.pHs, '1'),
        scalar('LSI_f', 'Langelier index of the feed', feed.LSI, '1'), scalar('LSI', 'Langelier index of the concentrate', now.LSI, '1', { note: now.LSI > 0 ? 'scale-forming' : 'not scale-forming' }),
        scalar('I_s', 'Ionic strength (mol/L)', now.I, '1'), scalar('gamma', 'Activity coefficient of a divalent ion', now.gamma, '1'), scalar('f_pair', 'Fraction of calcium in the CaSO₄ ion pair', now.paired, '1', { show: '%' }),
        scalar('SR_f', 'Gypsum saturation ratio of the feed', feed.SR, '1'), scalar('SR', 'Gypsum saturation ratio of the concentrate', now.SR, '1', { note: now.SR > 1 ? 'supersaturated' : 'undersaturated' }),
        scalar('SI_g', 'Gypsum saturation index log₁₀(SR)', Math.log10(Math.max(now.SR, 1e-300)), '1'),
        scalar('r_LSI', 'Recovery at which the Langelier index reaches zero', rL, '1', { show: '%', text: rL === 0 ? 'Feed is already scale-forming' : rL >= 0.95 ? 'Above 95 %: not limiting' : undefined }),
        scalar('r_gyp', 'Recovery at which gypsum becomes saturated', rG, '1', { show: '%', text: rG === 0 ? 'Feed is already saturated' : rG >= 0.95 ? 'Above 95 %: not limiting' : undefined }),
        scalar('r_gyp_as', 'Recovery limit for gypsum with antiscalant (ratio 2.3)', rG2, '1', { show: '%', text: rG2 >= 0.95 ? 'Above 95 %: not limiting' : undefined }),
      ],
      series: [
        line('lsi-r', 'Langelier index against recovery', 'Recovery', '%', rs.map(q => q * 100), [{ label: 'Langelier saturation index', data: sw.map(q => q.LSI) }, { label: 'Saturation', data: rs.map(() => 0), dash: true }], 'Index', '–', { marker: [v.r * 100, now.LSI] }),
        line('sr-r', 'Gypsum saturation ratio against recovery', 'Recovery', '%', rs.map(q => q * 100), [{ label: 'Gypsum saturation ratio', data: sw.map(q => q.SR) }, { label: 'Saturation', data: rs.map(() => 1), dash: true }, { label: 'Typical antiscalant limit', data: rs.map(() => 2.3), dash: true }], 'Saturation ratio', '–', { logy: true, marker: [v.r * 100, now.SR] }),
        line('ph-r', 'Concentrate pH and saturation pH against recovery', 'Recovery', '%', rs.map(q => q * 100), [{ label: 'Concentrate pH', data: sw.map(q => q.pHc) }, { label: 'Saturation pH', data: sw.map(q => q.pHs), dash: true }], 'pH', '–'),
      ],
      checks: [
        check('Salt balance behind the concentration factor', (1 - (v.r * (a.real_rej ? 1 - v.Rej : 0) + (1 - v.r) * now.CF)), 1e-12, 'Feed salt = permeate salt + concentrate salt'),
        check('Ion-pair mass action', a.ion_pair ? (() => { const mCa = v.Ca * now.f / M_CA / 1000, mS = v.SO4 * now.f / M_SO4 / 1000, p = now.paired * mCa, g2 = now.gamma ** 2; return (K_CASO4 * g2 * (mCa - p) * (mS - p) - p) / Math.max(p, 1e-30); })() : 0, 1e-8, 'Free ions and ion pair satisfy the association equilibrium'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    let pure = gypsumSR(0.0153, 0.0153, 4 * 0.0153, true);
    for (let i = 0; i < 30; i++) pure = gypsumSR(0.0153, 0.0153, 4 * 0.0153 * (1 - pure.paired), true);
    return [
      bench('Saturation pH of the standard worked example', langelierPHs(320, 298.15, 150, 34), 8.2, 'TDS 320 mg/L, Ca 150 and alkalinity 34 mg/L as CaCO₃, 25 °C: pH_s = 8.2 (widely reproduced example of the simplified Langelier formula)', 1e-2),
      bench('Davies coefficient for a divalent ion at I = 0.1 mol/L', Math.pow(10, daviesLog(2, 0.1)), 0.3732, 'Hand evaluation of the Davies (1962) equation', 1e-3),
      bench('Gypsum saturation ratio at its measured solubility in pure water', pure.SR, 1, 'Solubility 15.3 mmol/kg at 25 °C; log K_sp = −4.58, log K_a = 2.30', 0.12),
      bench('Concentration factor at 75 % recovery, complete rejection', val(this.solve({ ...v, r: 0.75 }, { ...a, real_rej: false }), 'CF'), 4, 'CF = 1/(1 − r)', 1e-12),
    ];
  },
  validation: [
    { name: 'Solubility of gypsum in pure water at 25 °C', ref: 'About 2.08 g/L as CaSO₄ (15.3 mmol/kg); Stumm & Morgan (1996) and standard solubility tables', note: 'A saturated gypsum solution should give a saturation ratio of one. Polarisation factor switched off.',
      cases: [{ label: 'Saturated solution', inputs: { Ca: 0.613, SO4: 1.470, TDS: 2.083, r: 0 }, assumptions: { wall: false }, observable: 'SR_f', observed: 1.0, sigma: 0.15 }] },
  ],
  diagram(v, a) {
    return svg(`
      ${S.rect(180, 110, 280, 100, 'd-body', 10)} ${S.path('M190 160 L450 160', 'd-liquid-line')}
      ${S.arrow(60, 135, 178, 135)} ${S.text(110, 122, 'feed')} ${S.text(110, 152, `Ca ${lab(v.Ca * 1000, 'mg/L')}`, 'd-text d-small')}
      ${S.arrow(462, 135, 590, 135, 'd-arrow d-hazard')} ${S.text(530, 122, 'concentrate')} ${S.text(530, 152, `× ${lab(1 / (1 - v.r))}`, 'd-text d-small')}
      ${S.arrow(320, 212, 320, 290)} ${S.text(380, 260, `permeate, ${lab(v.r * 100, '%')}`)}
      ${[0, 1, 2, 3, 4].map(i => S.rect(330 + i * 24, 152, 14, 7, 'd-hazard', 2)).join('')}
      ${S.text(390, 100, 'scale forms first at the tail end', 'd-text d-small')}
      ${S.text(320, 40, `pH ${lab(v.pH)},  alkalinity ${lab(v.Alk * 1000, 'mg/L')},  sulphate ${lab(v.SO4 * 1000, 'mg/L')}`)}
    `);
  },
  experiment: {
    objective: 'Determine the recovery at which calcium carbonate and gypsum begin to precipitate from a given feed water, with and without antiscalant.',
    apparatus: ['Stirred, thermostatted beaker or a bench cross-flow membrane cell operated in concentrate-recycle mode', 'Synthetic or site feed water', 'Antiscalant dosing stock'],
    instruments: [{ name: 'pH electrode with temperature compensation', measures: 'pH drift on precipitation', range: '2–12', resolution: '±0.01' }, { name: 'Turbidimeter or laser scattering probe', measures: 'Onset of nucleation', range: '0–100 NTU', resolution: '±0.02 NTU' }, { name: 'Ion chromatograph or titration', measures: 'Calcium, sulphate and alkalinity', range: '1–5000 mg/L', resolution: '±2 %' }, { name: 'Conductivity meter', measures: 'Concentration factor', range: '0.1–200 mS/cm', resolution: '±0.5 %' }],
    procedure: ['Concentrate the feed stepwise by withdrawing permeate (or by evaporation at constant temperature), holding at each step for a fixed induction time.', 'Record pH, turbidity and calcium at each step.', 'Identify the concentration factor at which turbidity rises and calcium falls; identify the solid by X-ray diffraction or microscopy.', 'Repeat with antiscalant at the supplier’s recommended dose.'],
    controls: ['Blank with calcium-free water', 'Seeded run with added gypsum crystals to remove the nucleation barrier'],
    signatures: ['pH fall and calcium loss at the onset of carbonate precipitation', 'Sulphate and calcium falling in equimolar proportion for gypsum', 'Induction time shortening rapidly as the saturation ratio rises above one'],
    safety: ['Acid and antiscalant handling: gloves and eye protection', 'Pressurised membrane cell precautions'],
  },
  falsify: ['Gypsum precipitating from seeded solutions at a computed saturation ratio well below one within the ionic-strength range of validity.', 'Calcium carbonate depositing at a clearly negative Langelier index in water below 10 000 mg/L dissolved solids.'],
  alternatives: [{ name: 'Stiff and Davis stability index', text: 'Replaces Langelier’s solids and temperature terms with an empirical ionic-strength function; the usual choice above about 10 000 mg/L.' }, { name: 'Pitzer ion-interaction model', text: 'Accurate activity coefficients to very high ionic strength; used in geochemical codes for sea-water concentrates.' }, { name: 'Ryznar and Puckorius indices', text: 'Empirical re-weightings of pH and saturation pH intended to correlate better with observed scale in cooling systems.' }],
  hazards: [{ hazard: 'Irreversible membrane scaling', cause: 'Operating above the saturation limits without antiscalant', mitigation: 'Recovery limits, acid or antiscalant dosing, flushing on shut-down' }, { hazard: 'Chemical handling', cause: 'Concentrated acid for pH control', mitigation: 'Closed dosing systems, bunding, protective equipment' }],
  standards: ['ASTM D3739 (calculation and adjustment of the Langelier saturation index for reverse osmosis)', 'ASTM D4582 (calculation and adjustment of the Stiff and Davis stability index for reverse osmosis)', 'ASTM D4692 (calculation and adjustment of sulphate scaling salts for reverse osmosis)'],
  limits: 'Langelier index: dissolved solids below about 10 000 mg/L. Gypsum ratio: ionic strength below about 0.5 mol/L, temperature near 25 °C (the solubility product is not temperature-corrected). Other scales — barium and strontium sulphate, silica, calcium phosphate and fluoride — are not assessed.',
  numerics: { method: 'Algebraic equilibrium relations; bisection for limiting recoveries' },
  optimise: { objective: 'SR', sense: 'min', vars: ['r'], note: 'In practice recovery is maximised subject to the saturation limits.' },
  inverse: { series: 'lsi-r', curve: 0, fit: ['Alk', 'Ca'] },
  extensions: ['Stiff and Davis index for sea-water concentrates', 'Barium and strontium sulphate, silica and calcium fluoride', 'Temperature-dependent solubility products', 'Acid dosing required to reach a target index'],
};

// ------------------------------------------------------------------ CSTR and PFR
/** Build the kinetics for the chosen assumptions. rate(X) is in 1/s: dX/dτ for a PFR, X/τ for a CSTR. */
function reactorKinetics(v, a) {
  const n = a.first_order ? 1 : 2, eps = a.liquid ? 0 : 1;
  const dTad = a.isothermal ? 0 : -v.dH_r * v.C_A0 / (v.rho * v.cp);
  const Tof = X => Math.max(v.T_0 + dTad * X, 100);
  const kof = T => v.A_f * Math.exp(-v.E_a / (C.R_u * T));
  const rate = X => { const T = Tof(X), vol = a.liquid ? 1 : (1 + eps * X) * T / v.T_0; return kof(T) * Math.pow(Math.max(1 - X, 0) / vol, n); };
  return { n, eps, dTad, Tof, kof, rate };
}
/** PFR: tabulate τ(X) = ∫dX/r on a grid clustered toward X = 1, which avoids integrating a stiff ODE in τ. */
function pfrTable(kin, nPts = 2400) {
  const xi = N.linspace(0, 27, nPts), X = xi.map(q => -Math.expm1(-q)), g = q => Math.exp(-q) / kin.rate(-Math.expm1(-q)), f = xi.map(g);
  const tau = [0];
  // composite Simpson's rule on each interval, with more panels where the integrand changes steeply (ignition of an adiabatic reactor)
  const simpson = (q0, q1, f0, f1) => {
    const m = Math.min(64, Math.max(1, Math.ceil(4 * Math.abs(Math.log(f1 / f0))) || 1)), hq = (q1 - q0) / m; let sum = f0 + f1;
    for (let k = 0; k < m; k++) sum += 4 * g(q0 + (k + 0.5) * hq) + (k > 0 ? 2 * g(q0 + k * hq) : 0);
    return sum * hq / 6;
  };
  for (let i = 1; i < nPts; i++) tau.push(tau[i - 1] + simpson(xi[i - 1], xi[i], f[i - 1], f[i]));
  // within a table interval the same rule is applied to the part of the interval covered, so that small conversions and
  // steep thermal feedback are not lost to linear interpolation; ξ = −ln(1 − X) is found by bisection on the monotonic τ(ξ)
  const part = (i, q) => tau[i] + simpson(xi[i], q, f[i], g(q));
  const at = t => {
    if (!(t < tau[nPts - 1])) return X[nPts - 1];
    if (!(t > 0)) return 0;
    let i0 = 0, i1 = nPts - 1; while (i1 - i0 > 1) { const im = (i0 + i1) >> 1; if (tau[im] <= t) i0 = im; else i1 = im; }
    let lo = xi[i0], hi = xi[i0 + 1];
    for (let k = 0; k < 1100 && hi - lo > 1e-15 * hi; k++) { const mid = 0.5 * (lo + hi); if (part(i0, mid) > t) hi = mid; else lo = mid; }
    return -Math.expm1(-0.5 * (lo + hi));
  };
  const tauAt = x => { const q = Math.min(-Math.log1p(-Math.min(Math.max(x, 0), X[nPts - 1])), xi[nPts - 1]), i = Math.min(Math.floor(q / (xi[1] - xi[0])), nPts - 2); return part(i, q); };
  return { X, tau, at, tauAt };
}
/** CSTR steady states leaving a tank fed at conversion Xin: roots of X − Xin − τ r(X) = 0 on [Xin, 1]. */
function cstrRoots(kin, tau, Xin = 0, nScan = 500) {
  const G = X => X - Xin - tau * kin.rate(X), roots = [];
  let x0 = Xin, g0 = G(x0);
  for (let i = 1; i <= nScan; i++) {
    const s = i / nScan, x1 = Xin + (1 - Xin) * (1 - Math.pow(1 - s, 3)), g1 = G(x1);
    if (g0 === 0) roots.push(x0);
    else if (g0 * g1 < 0) {
      // bisection, then Newton steps kept inside the bracket: the bisection tolerance is absolute, which is too coarse for very small conversions
      let x = N.bisect(G, x0, x1, 1e-14);
      for (let q = 0; q < 3; q++) { const hh = Math.max(1e-7 * (x1 - x0), 1e-300), dG = (G(x + hh) - G(x - hh)) / (2 * hh), xn = x - G(x) / dG; if (Number.isFinite(xn) && xn >= x0 && xn <= x1) x = xn; else break; }
      roots.push(x);
    }
    x0 = x1; g0 = g1;
  }
  if (!roots.length) roots.push(Xin);
  return roots;
}

const reactors = {
  id: 'reactor-kinetics-cstr-pfr',
  title: 'Conversion in stirred-tank and plug-flow reactors',
  module: 2, klass: 'I', domains: ['chemical'],
  keywords: ['cstr', 'pfr', 'plug flow reactor', 'stirred tank', 'chemical reactor', 'conversion', 'residence time', 'arrhenius', 'damkohler', 'reaction kinetics', 'first order', 'second order', 'adiabatic reactor', 'space time', 'reactor'],
  summary: 'Conversion of a first- or second-order reaction in an ideal continuous stirred tank and an ideal plug-flow reactor, isothermal or adiabatic, with Arrhenius kinetics.',
  background: [
    'The two ideal continuous reactors bracket real behaviour. In a continuous stirred-tank reactor (CSTR) the contents are perfectly mixed, so the reaction proceeds everywhere at the low concentration of the outlet. In a plug-flow reactor (PFR) there is no axial mixing and each element of fluid reacts as in a batch for a time equal to the residence time. For any reaction of positive order at constant temperature the PFR therefore needs less volume for the same conversion.',
    'The rate constant rises steeply with temperature according to the Arrhenius law. In an adiabatic reactor an exothermic reaction heats the mixture in proportion to conversion, which accelerates the reaction; in a CSTR this feedback can produce several steady states for the same feed, with ignition and extinction as the residence time is varied.',
  ],
  phenomena: ['Chemical reaction with Arrhenius temperature dependence', 'Back-mixing', 'Thermal feedback and multiple steady states', 'Volume change on reaction in gases'],
  laws: ['mass', 'species', 'energy', 'ideal_gas'],
  refs: ['Levenspiel, O. (1999). Chemical Reaction Engineering, 3rd ed., Wiley.', 'Fogler, H. S. (2016). Elements of Chemical Reaction Engineering, 5th ed., Prentice Hall.', 'Aris, R. (1969). Elementary Chemical Reactor Analysis. Prentice-Hall.', 'van Heerden, C. (1953). Autothermic processes: properties and reactor design. Industrial & Engineering Chemistry 45, 1242–1247.'],
  inputs: [
    inp('A_f', 'Frequency factor (first-order equivalent at feed concentration)', '1/s', 3e6, { min: 1e3, max: 1e12, kind: 'fluid', aliases: ['frequency factor', 'pre-exponential'] }),
    inp('E_a', 'Activation energy', 'kJ/mol', 60, { min: 20, max: 150, kind: 'fluid', aliases: ['activation energy'] }),
    inp('T_0', 'Feed temperature', '°C', 57, { min: 0, max: 200, aliases: ['feed temperature', 'inlet temperature', 'temperature'] }),
    inp('tau', 'Space time V/v₀', 's', 1000, { min: 1, max: 1e5, aliases: ['residence time', 'space time'] }),
    inp('C_A0', 'Feed concentration of the reactant', 'mol/m^3', 1000, { min: 10, max: 2e4, aliases: ['feed concentration', 'inlet concentration', 'concentration'] }),
    inp('dH_r', 'Heat of reaction (negative when exothermic)', 'kJ/mol', -80, { min: -200, max: 50, kind: 'fluid', aliases: ['heat of reaction', 'enthalpy of reaction'] }),
    inp('rho', 'Mixture density', 'kg/m^3', 1000, { min: 500, max: 1500, kind: 'fluid', aliases: ['density'] }),
    inp('cp', 'Mixture specific heat', 'J/(kg K)', 4000, { min: 1500, max: 4500, kind: 'fluid', aliases: ['specific heat', 'heat capacity'] }),
  ],
  assumptions: [
    asm('isothermal', 'The reactor is held at the feed temperature.', { why: 'Good heat removal or a dilute feed', alt: 'The reactor is adiabatic: temperature rises (or falls) in proportion to conversion.' }),
    asm('first_order', 'The reaction A → products is first order in A.', { why: 'Simplest kinetics', alt: 'The reaction is second order in A.' }),
    asm('liquid', 'Density is constant (liquid phase).', { why: 'Volumetric flow does not change', alt: 'Ideal-gas reaction A → 2B at constant pressure: the volumetric flow grows with conversion and temperature.' }),
    asm('single_tank', 'The stirred reactor is a single tank.', { why: 'Limit of complete back-mixing', alt: 'Three equal tanks in series with the same total volume, which moves the behaviour toward plug flow.' }),
  ],
  symbols: { k: ['Rate constant', '1/s'], Da: ['Damköhler number', '1'], X: ['Conversion', '1'], X_cstr: ['Conversion in the stirred tank', '1'], X_pfr: ['Conversion in the plug-flow reactor', '1'], T: ['Reactor temperature', 'K'], dT_ad: ['Adiabatic temperature rise at full conversion', 'K'], r_X: ['Rate of conversion', '1/s'], t: ['Space-time coordinate', 's'], eps_v: ['Fractional volume change at full conversion', '1'] },
  equations: a => {
    const conc = a.liquid ? '(1 - X)' : (a.isothermal ? '((1 - X)/(1 + eps_v*X))' : '((1 - X)*T_0/((1 + eps_v*X)*T))');
    return [
      eq('arr', 'Arrhenius law', 'k', 'A_f*exp(-E_a/(R_u*T))', { kind: 'law', origin: 'Arrhenius (1889); transition-state theory' }),
      eq('rate', 'Rate of conversion', 'r_X', a.first_order ? `k*${conc}` : `k*${conc}^2`, { kind: 'law', origin: 'Mass-action kinetics' + (a.liquid ? '' : ' with ideal-gas volume change'), needs: [a.first_order ? 'first_order' : 'liquid'].filter(q => a[q]) }),
      eq('pfr', 'Plug-flow design equation', 'd(X,t)', 'r_X', { kind: 'law', origin: 'Species balance on a differential volume' }),
      eq('cstr', 'Stirred-tank design equation', 'X_cstr', a.single_tank ? 'tau*r_X' : 'tau*r_X/3 + X', { kind: 'law', origin: a.single_tank ? 'Species balance on a perfectly mixed tank' : 'Species balance on each of three tanks, written for one tank with inlet conversion X', needs: a.single_tank ? ['single_tank'] : [] }),
      a.isothermal ? eq('en', 'Energy balance', 'T', 'T_0', { kind: 'closure', needs: ['isothermal'] }) : eq('en', 'Adiabatic energy balance', 'rho*cp*(T - T_0)', '-dH_r*C_A0*X', { kind: 'law', origin: 'First law with no heat exchange' }),
      eq('da', 'Damköhler number', 'Da', 'k*tau', { kind: 'definition' }),
      ...(a.isothermal ? [] : [eq('dtad', 'Adiabatic temperature rise', 'dT_ad', '-dH_r*C_A0/(rho*cp)', { kind: 'derived' })]),
    ];
  },
  derivation: a => [
    { text: 'A steady species balance on a perfectly mixed tank equates the reactant consumed to the rate evaluated at outlet conditions times the volume.', tex: 'v_0 C_{A0} X = (-r_A)\\big|_{out} V \;\\Rightarrow\; X = \\tau\\,r_X(X)' },
    { text: 'The same balance on a differential slice of a plug-flow reactor gives an ordinary differential equation in space time.', tex: '\\frac{\\mathrm{d}X}{\\mathrm{d}\\tau} = r_X(X) \;\\Rightarrow\; \\tau = \\int_0^X \\frac{\\mathrm{d}X\'}{r_X(X\')}' },
    { text: a.first_order ? 'For first-order isothermal kinetics in a liquid both integrate in closed form.' : 'For second-order isothermal kinetics in a liquid, with Da = k τ:', tex: a.first_order ? 'X_{PFR} = 1 - e^{-k\\tau},\\qquad X_{CSTR} = \\frac{k\\tau}{1+k\\tau}' : 'X_{PFR} = \\frac{\\mathrm{Da}}{1+\\mathrm{Da}},\\qquad X_{CSTR} = \\frac{1+2\\mathrm{Da}-\\sqrt{1+4\\mathrm{Da}}}{2\\mathrm{Da}}' },
    { text: 'The rate constant follows the Arrhenius law.', tex: 'k = A\\,\\exp\\!\\left(-\\frac{E_a}{RT}\\right)' },
    ...(a.isothermal ? [] : [{ text: 'With no heat exchange, the enthalpy released by reaction appears as sensible heat, so temperature is linear in conversion.', tex: 'T = T_0 + \\Delta T_{ad}\\,X,\\qquad \\Delta T_{ad} = \\frac{(-\\Delta H_r)\\,C_{A0}}{\\rho c_p}' }]),
    ...(a.liquid ? [] : [{ text: 'For a gas at constant pressure the volumetric flow changes with moles and temperature, diluting the reactant.', tex: 'C_A = C_{A0}\\,\\frac{1-X}{1+\\varepsilon X}\\,\\frac{T_0}{T}' }]),
  ],
  solve(v, a) {
    const kin = reactorKinetics(v, a), k0 = kin.kof(v.T_0), Da = k0 * v.tau, tab = pfrTable(kin);
    const Xp = tab.at(v.tau);
    const tanks = a.single_tank ? 1 : 3;
    const cstr = tau => { let lo = 0, hi = 0, multi = 1; for (let j = 0; j < tanks; j++) { const rl = cstrRoots(kin, tau / tanks, lo), rh = j === 0 ? rl : cstrRoots(kin, tau / tanks, hi); multi = Math.max(multi, rl.length, rh.length); lo = rl[0]; hi = rh[rh.length - 1]; } return { lo, hi, multi }; };
    const c = cstr(v.tau), Xc = c.hi;
    const taus = N.logspace(Math.max(v.tau / 100, 1e-3), v.tau * 100, 70), cs = taus.map(cstr);
    const Xg = N.linspace(0, 0.99, 100), inv = Xg.map(x => 1 / kin.rate(x));
    // independent quadrature of the PFR design equation (Simpson on a uniform grid in −ln(1 − X))
    const zq = N.linspace(0, -Math.log1p(-Math.min(Xp, 1 - 1e-12)), 2001), fq = zq.map(z => Math.exp(-z) / kin.rate(-Math.expm1(-z)));
    let simp = fq[0] + fq[2000]; for (let i = 1; i < 2000; i++) simp += (i % 2 ? 4 : 2) * fq[i]; simp *= (zq[1] - zq[0]) / 3;
    const tauEq = tab.tauAt(Xc);
    const warnings = [];
    if (c.multi > 1) warnings.push(`The adiabatic stirred tank has ${c.multi} steady states at this space time (conversions from ${lab(c.lo)} to ${lab(c.hi)}). Which one is reached depends on start-up; the middle state is unstable.`);
    if (!a.isothermal && kin.Tof(1) > 1500) warnings.push(`The adiabatic temperature at full conversion (${lab(kin.Tof(1) - 273.15, '°C')}) is unrealistically high: a real system would boil, decompose or run away. Dilute the feed or remove heat.`);
    if (!a.isothermal && v.T_0 + kin.dTad < 100) warnings.push('The endothermic temperature fall has been limited at 100 K to keep the rate law defined.');
    if (!a.liquid && v.rho > 100) warnings.push('The gas-phase option uses the stated density only in the energy balance; check that it is a gas density if the adiabatic option is also selected.');
    return {
      scalars: [
        scalar('k', 'Rate constant at feed temperature', k0, '1/s'), scalar('Da', 'Damköhler number k τ', Da, '1'),
        scalar('X_pfr', 'Conversion in the plug-flow reactor', Xp, '1', { show: '%' }), scalar('X_cstr', a.single_tank ? 'Conversion in the stirred tank' : 'Conversion after three tanks in series', Xc, '1', { show: '%', note: c.multi > 1 ? 'ignited (upper) steady state' : '' }),
        scalar('X_cstr_lo', 'Lowest stirred-tank steady state', c.lo, '1', { show: '%' }), scalar('n_ss', 'Number of stirred-tank steady states', c.multi, '1'),
        scalar('T_pfr', 'Plug-flow outlet temperature', kin.Tof(Xp), 'K', { show: '°C' }), scalar('T_cstr', 'Stirred-tank temperature', kin.Tof(Xc), 'K', { show: '°C' }),
        scalar('dT_ad', 'Adiabatic temperature change at full conversion', kin.dTad, 'K'),
        scalar('C_A_pfr', 'Reactant leaving the plug-flow reactor per unit feed volume', v.C_A0 * (1 - Xp), 'mol/m^3'), scalar('C_A_cstr', 'Reactant leaving the stirred tank per unit feed volume', v.C_A0 * (1 - Xc), 'mol/m^3'),
        scalar('V_ratio', 'Stirred-tank volume over plug-flow volume for the stirred-tank conversion', v.tau / Math.max(tauEq, 1e-300), '1'),
      ],
      series: [
        line('X-tau', 'Conversion against space time', 'Space time', 's', taus, [{ label: 'Plug flow', data: taus.map(tab.at) }, { label: a.single_tank ? 'Stirred tank' : 'Three tanks in series', data: cs.map(q => q.hi) }, ...(a.isothermal ? [] : [{ label: 'Stirred tank, lower steady state', data: cs.map(q => q.lo), dash: true }])], 'Conversion', '–', { logx: true, marker: [v.tau, Xp] }),
        line('levenspiel', 'Levenspiel plot', 'Conversion', '–', Xg, [{ label: 'Reciprocal rate 1/r_X', data: inv }], 'Reciprocal rate', 's', { logy: true, note: 'Plug-flow space time is the area under the curve; stirred-tank space time is the rectangle X/r_X(X).' }),
        line('T-X', 'Temperature and rate constant along the reaction path', 'Conversion', '–', Xg, [{ label: 'Temperature (°C)', data: Xg.map(x => kin.Tof(x) - 273.15) }, { label: 'log₁₀ of the rate constant (1/s)', data: Xg.map(x => Math.log10(kin.kof(kin.Tof(x)))), dash: true }], 'Temperature, log₁₀ k', '°C, –'),
      ],
      checks: [
        check('Plug-flow design equation by independent quadrature', (simp - Math.min(v.tau, tab.tau[tab.tau.length - 1])) / v.tau, 2e-4, 'τ = ∫dX/r_X evaluated by Simpson’s rule up to the computed conversion'),
        check('Stirred-tank design equation residual', tanks === 1 ? (Xc - v.tau * kin.rate(Xc)) / (1 + v.tau * Math.abs(kin.rate(Math.min(Xc + 1e-7, 1)) - kin.rate(Math.max(Xc - 1e-7, 0))) / 2e-7) : 0, 1e-9, 'X = τ r_X(X) at the reported steady state, expressed as the equivalent error in conversion'),
        check('Conversion within physical bounds', (Xp < 0 || Xp > 1 || Xc < 0 || Xc > 1) ? 1 : 0, 0, '0 ≤ X ≤ 1'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { isothermal: true, first_order: true, liquid: true, single_tank: true }, k = v.A_f * Math.exp(-v.E_a / (C.R_u * v.T_0)), Da = k * v.tau;
    const r1 = this.solve(v, b), r2 = this.solve(v, { ...b, first_order: false }), r3 = this.solve(v, { ...b, single_tank: false }), r4 = this.solve(v, { ...b, liquid: false });
    // The closed forms are written so that they keep their precision at both ends of the Damköhler range: expm1 and log1p where kτ is minute
    // (1 − e^{−kτ} and 1 + 2Da − √(1 + 4Da) otherwise cancel to rounding error), and conversion compared with conversion where kτ is large.
    // First-order gas with ε = 1: kτ = −2 ln(1 − X) − X. Read backwards from X it magnifies any error in X by 2/(1 − X), without limit as X → 1,
    // so it is solved for X instead: with y = −ln(1 − X), 2y − (1 − e^{−y}) = kτ has slope between 1 and 2 and Newton's method converges from y = kτ/2.
    let yg = Da / 2; for (let i = 0; i < 60; i++) { const dy = (2 * yg + Math.expm1(-yg) - Da) / (2 - Math.exp(-yg)); yg -= dy; if (Math.abs(dy) <= 1e-16 * yg) break; }
    return [
      bench('First-order PFR', val(r1, 'X_pfr'), -Math.expm1(-Da), 'X = 1 − e^{−kτ}', 1e-5),
      bench('First-order CSTR', val(r1, 'X_cstr'), Da / (1 + Da), 'X = kτ/(1 + kτ)', 1e-9),
      bench('Second-order PFR', val(r2, 'X_pfr'), Da / (1 + Da), 'X = Da/(1 + Da)', 1e-4),
      bench('Second-order CSTR', val(r2, 'X_cstr'), 2 * Da / (1 + 2 * Da + Math.sqrt(1 + 4 * Da)), 'X = [1 + 2Da − √(1 + 4Da)]/(2Da) = 2Da/[1 + 2Da + √(1 + 4Da)]', 1e-9),
      bench('Three first-order tanks in series', val(r3, 'X_cstr'), -Math.expm1(-3 * Math.log1p(Da / 3)), 'X = 1 − (1 + kτ/N)^{−N}', 1e-9),
      bench('First-order gas-phase PFR with ε = 1', val(r4, 'X_pfr'), -Math.expm1(-yg), 'kτ = (1 + ε) ln[1/(1 − X)] − εX, solved for X', 1e-4),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(90, 80, 130, 150, 'd-body', 10)} ${S.rect(92, 130, 126, 98, 'd-liquid', 8)} ${S.path('M155 60 L155 190 M130 190 L180 190', 'd-line')}
      ${S.text(155, 255, a.single_tank ? 'stirred tank' : 'tank 1 of 3')} ${S.arrow(30, 110, 88, 110)} ${S.arrow(222, 200, 280, 200)}
      ${S.rect(360, 135, 230, 40, 'd-pipe-fill', 6)} ${[0, 1, 2, 3, 4, 5].map(i => S.line(390 + i * 34, 137, 390 + i * 34, 173, 'd-line')).join('')}
      ${S.text(475, 200, 'plug-flow reactor')} ${S.arrow(310, 155, 358, 155)} ${S.arrow(592, 155, 630, 155)}
      ${S.text(320, 40, `feed ${lab(v.C_A0, 'mol/m³')} at ${lab(v.T_0 - 273.15, '°C')},  τ = ${lab(v.tau, 's')}`)}
      ${S.text(320, 320, `${a.first_order ? 'first' : 'second'}-order, ${a.isothermal ? 'isothermal' : 'adiabatic'}, ${a.liquid ? 'liquid' : 'gas A → 2B'}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure conversion against residence time for the same reaction in a laboratory stirred tank and a tubular reactor, and extract the rate constant and activation energy.',
    apparatus: ['Jacketed stirred-tank reactor with overflow', 'Coiled tubular reactor immersed in a thermostat bath', 'Metering pumps for reactant feeds', 'A well-characterised reaction such as the saponification of ethyl acetate with sodium hydroxide'],
    instruments: [{ name: 'Conductivity probe at each outlet', measures: 'Hydroxide concentration, hence conversion', range: '0–20 mS/cm', resolution: '±0.5 %' }, { name: 'Pt100 probes', measures: 'Reactor and bath temperature', range: '0–100 °C', resolution: '±0.1 K' }, { name: 'Balance and stopwatch or Coriolis meter', measures: 'Feed flow rates', range: '1–500 mL/min', resolution: '±0.5 %' }],
    procedure: ['Calibrate conductivity against known mixtures of reactant and product.', 'At fixed temperature, run each reactor at five or more flow rates, waiting at least five residence times for steady state.', 'Plot X/(1 − X)ⁿ against τ for the tank and the integrated form for the tube; the slopes give k.', 'Repeat at three temperatures; the slope of ln k against 1/T gives E_a/R.', 'Inject a tracer pulse to verify that the residence-time distributions approach the ideal limits.'],
    controls: ['Tracer test for dead volume and bypassing', 'Blank run without one reactant to check the conductivity baseline'],
    signatures: ['Plug-flow conversion above stirred-tank conversion at equal residence time', 'ln k linear in 1/T', 'Stirred-tank data linear in the appropriate rearranged form'],
    safety: ['Caustic solutions: eye protection and gloves', 'For exothermic systems, a tested emergency cooling and quench procedure'],
  },
  falsify: ['Isothermal stirred-tank conversion exceeding plug-flow conversion at the same space time for a reaction of positive order.', 'Rate constants that do not follow a straight line in ln k against 1/T over a moderate temperature range.'],
  alternatives: [{ name: 'Axial-dispersion and tanks-in-series models', text: 'One-parameter descriptions of real reactors between the two ideal limits, fitted to a measured residence-time distribution.' }, { name: 'Segregated-flow and maximum-mixedness models', text: 'Bound the effect of micromixing for non-first-order reactions with a given residence-time distribution.' }, { name: 'Non-adiabatic reactor with heat exchange', text: 'Adds a heat-removal line to the stirred-tank energy balance; the intersections with the heat-generation curve give the steady states.' }],
  hazards: [{ hazard: 'Thermal runaway', cause: 'Exothermic reaction with insufficient heat removal', mitigation: 'Reaction calorimetry, dilution, emergency cooling, relief sizing' }, { hazard: 'Over-pressure', cause: 'Gas generation or boiling on runaway', mitigation: 'Relief system designed for two-phase flow' }],
  standards: ['IEC 61511 (safety instrumented systems for the process industry)', 'API Standard 520/521 (pressure-relieving and depressuring systems)', 'DIERS methodology for emergency relief system design (AIChE)'],
  limits: 'Single irreversible reaction with power-law kinetics, ideal mixing or ideal plug flow, constant physical properties. Reversible reactions, catalyst deactivation, mass-transfer limitation and heat exchange with a jacket are not included.',
  numerics: { method: 'Quadrature of the plug-flow design equation in conversion; bracketed root search for stirred-tank steady states', order: 2, stability: 'No time stepping; stiffness of ignited states is avoided by integrating in conversion' },
  optimise: { objective: 'X_pfr', sense: 'max', vars: ['T_0', 'tau'], note: 'Conversion rises monotonically with temperature and space time for an irreversible reaction; cost and selectivity set the practical optimum.' },
  inverse: { series: 'X-tau', curve: 0, fit: ['A_f', 'E_a'] },
  extensions: ['Reversible and parallel reactions with selectivity', 'Jacket cooling and the van Heerden stability diagram', 'Residence-time distribution with axial dispersion', 'Dynamic start-up and oscillation of a cooled CSTR'],
};

// ------------------------------------------------------------------ three-component isothermal flash
// Antoine constants, log10(p/mmHg) = A − B/(C + t/°C); critical constants for the Wilson correlation.
const BTX = [
  { name: 'Benzene', A: 6.90565, B: 1211.033, Cc: 220.790, Tc: 562.05, pc: 48.95e5, w: 0.2103, Tb: 80.10 },
  { name: 'Toluene', A: 6.95464, B: 1344.800, Cc: 219.482, Tc: 591.75, pc: 41.08e5, w: 0.2640, Tb: 110.63 },
  { name: 'o-Xylene', A: 6.99891, B: 1474.679, Cc: 213.686, Tc: 630.30, pc: 37.32e5, w: 0.3120, Tb: 144.41 },
];
const MMHG = 133.322368421;
const antoine = (c, T) => MMHG * Math.pow(10, c.A - c.B / (c.Cc + T - 273.15));
const kValues = (T, p, raoult, eff) => BTX.map(c => { const K = raoult ? antoine(c, T) / p : c.pc / p * Math.exp(5.373 * (1 + c.w) * (1 - c.Tc / T)); return 1 + eff * (K - 1); });
const rrFun = (z, K, psi) => z.reduce((s, zi, i) => s + zi * (K[i] - 1) / (1 + psi * (K[i] - 1)), 0);
function flashTP(z, K) {
  const f0 = rrFun(z, K, 0), f1 = rrFun(z, K, 1);
  const psi = f0 <= 0 ? 0 : f1 >= 0 ? 1 : N.bisect(q => rrFun(z, K, q), 0, 1, 1e-15);
  let x = z.map((zi, i) => zi / (1 + psi * (K[i] - 1))), y = x.map((xi, i) => K[i] * xi);
  // single-phase feeds: the absent phase is reported at its incipient composition, normalised
  const sx = N.sum(x), sy = N.sum(y); x = x.map(q => q / sx); y = y.map(q => q / sy);
  return { psi, x, y, f0, f1, state: f0 <= 0 ? 0 : f1 >= 0 ? 2 : 1 };
}
const FLASH_STATES = ['Subcooled liquid (below the bubble point)', 'Two-phase', 'Superheated vapour (above the dew point)'];

const flash = {
  id: 'flash-rachford-rice',
  title: 'Isothermal flash of a benzene–toluene–xylene mixture',
  module: 2, klass: 'I', domains: ['chemical'],
  keywords: ['flash', 'rachford-rice', 'rachford rice', 'vapour-liquid equilibrium', 'vapor-liquid equilibrium', 'vle', 'k-value', 'raoult', 'antoine', 'bubble point', 'dew point', 'flash drum', 'phase split', 'benzene', 'toluene', 'xylene', 'vapour fraction'],
  summary: 'Vapour fraction and phase compositions for an isothermal flash of a benzene–toluene–o-xylene feed, with K-values from Raoult’s law and the Antoine equation or from the Wilson correlation.',
  background: [
    'When a liquid mixture is brought to a temperature and pressure between its bubble and dew points it splits into a vapour enriched in the more volatile components and a liquid enriched in the heavier ones. If the two phases leave in equilibrium, each component’s vapour and liquid mole fractions are related by its K-value.',
    'Combining the component balances with the requirement that mole fractions in each phase sum to one gives a single equation in the vapour fraction, due to Rachford and Rice. It is monotonic in the vapour fraction, which makes it robust to solve. Benzene, toluene and the xylenes form nearly ideal solutions, so Raoult’s law with Antoine vapour pressures is accurate at low pressure.',
  ],
  phenomena: ['Vapour–liquid equilibrium', 'Relative volatility', 'Partial vaporisation'],
  laws: ['mass', 'species', 'second'],
  refs: ['Rachford, H. H. & Rice, J. D. (1952). Procedure for use of electronic digital computers in calculating flash vaporization hydrocarbon equilibrium. J. Petroleum Technology 4(10), 19–20.', 'Wilson, G. M. (1969). A modified Redlich–Kwong equation of state, application to general physical data calculations. Paper 15C, 65th National AIChE Meeting, Cleveland, Ohio.', 'Poling, B. E., Prausnitz, J. M. & O’Connell, J. P. (2001). The Properties of Gases and Liquids, 5th ed., McGraw-Hill.', 'Smith, J. M., Van Ness, H. C. & Abbott, M. M. (2005). Introduction to Chemical Engineering Thermodynamics, 7th ed., McGraw-Hill.', 'Seader, J. D., Henley, E. J. & Roper, D. K. (2011). Separation Process Principles, 3rd ed., Wiley.'],
  inputs: [
    inp('z_1', 'Benzene mole fraction in the feed', '1', 0.4, { min: 0.05, max: 0.6, kind: 'fluid', aliases: ['benzene'] }),
    inp('z_2', 'Toluene mole fraction in the feed', '1', 0.35, { min: 0.05, max: 0.35, kind: 'fluid', aliases: ['toluene'] }),
    inp('T', 'Flash temperature', '°C', 105, { min: 60, max: 160, aliases: ['temperature', 'flash temperature'] }),
    inp('p', 'Flash pressure', 'bar', 1.01325, { min: 0.2, max: 5, aliases: ['pressure', 'flash pressure'] }),
    inp('F', 'Feed rate', 'kmol/h', 100, { min: 1, max: 1e4, aliases: ['feed rate', 'feed'] }),
    inp('psi_s', 'Specified vapour fraction (used when temperature is not specified)', '1', 0.5, { min: 0.02, max: 0.98, aliases: ['vapour fraction', 'vapor fraction'] }),
  ],
  assumptions: [
    asm('raoult', 'K-values follow Raoult’s law with Antoine vapour pressures.', { why: 'Nearly ideal aromatic mixture at low pressure', alt: 'K-values come from the Wilson correlation based on critical constants and acentric factors.' }),
    asm('tp_spec', 'Temperature and pressure are specified.', { why: 'Isothermal flash', alt: 'Pressure and vapour fraction are specified and the temperature is found.' }),
    asm('equilibrium', 'Vapour and liquid leave in equilibrium.', { why: 'Adequate residence time in the drum', alt: 'Approach to equilibrium is 80 %: each K-value is moved 20 % of the way back toward one.' }),
  ],
  symbols: { z_3: ['o-Xylene mole fraction in the feed', '1'], K_1: ['K-value of benzene', '1'], K_2: ['K-value of toluene', '1'], K_3: ['K-value of o-xylene', '1'], psi: ['Vapour fraction V/F', '1'], x_1: ['Benzene in the liquid', '1'], y_1: ['Benzene in the vapour', '1'], V: ['Vapour rate', 'mol/s'], L: ['Liquid rate', 'mol/s'], p_s1: ['Vapour pressure of benzene', 'Pa'], p_mm: ['Reference pressure 1 mmHg', 'Pa'], A_1: ['Antoine A of benzene', '1'], B_1: ['Antoine B of benzene', 'K'], C_1: ['Antoine C of benzene', 'K'], T_z: ['Ice-point temperature 273.15 K', 'K'], p_c1: ['Critical pressure of benzene', 'Pa'], T_c1: ['Critical temperature of benzene', 'K'], omega_1: ['Acentric factor of benzene', '1'], E_s: ['Stage efficiency', '1'], K_e1: ['Equilibrium K-value of benzene', '1'] },
  equations: a => [
    eq('z3', 'Feed composition closure', 'z_3', '1 - z_1 - z_2', { kind: 'law', origin: 'Mole fractions sum to one' }),
    ...(a.raoult
      ? [eq('ant', 'Antoine vapour pressure (shown for benzene)', 'log10(p_s1/p_mm)', 'A_1 - B_1/(C_1 + T - T_z)', { kind: 'empirical', origin: 'Antoine (1888); constants from standard compilations' }), eq('k', 'Raoult’s law (shown for benzene)', a.equilibrium ? 'K_1' : 'K_e1', 'p_s1/p', { kind: 'law', origin: 'Equal fugacities with ideal liquid and vapour', needs: ['raoult'] })]
      : [eq('k', 'Wilson correlation (shown for benzene)', a.equilibrium ? 'K_1' : 'K_e1', '(p_c1/p)*exp(5.373*(1 + omega_1)*(1 - T_c1/T))', { kind: 'empirical', origin: 'Wilson (1969)' })]),
    ...(a.equilibrium ? [] : [eq('eff', 'Approach to equilibrium', 'K_1', '1 + E_s*(K_e1 - 1)', { kind: 'closure', origin: 'Stage-efficiency closure with E = 0.8' })]),
    eq('rr', 'Rachford–Rice equation', 'z_1*(K_1 - 1)/(1 + psi*(K_1 - 1)) + z_2*(K_2 - 1)/(1 + psi*(K_2 - 1)) + z_3*(K_3 - 1)/(1 + psi*(K_3 - 1))', '0', { kind: 'law', origin: 'Component balances with Σy − Σx = 0', needs: a.tp_spec ? ['tp_spec'] : [] }),
    eq('x', 'Liquid composition (shown for benzene)', 'x_1', 'z_1/(1 + psi*(K_1 - 1))', { kind: 'law', origin: 'Component balance' }),
    eq('y', 'Vapour composition (shown for benzene)', 'y_1', 'K_1*x_1', { kind: 'law', origin: 'Definition of the K-value' }),
    eq('v', 'Vapour rate', 'V', 'psi*F', { kind: 'definition' }),
    eq('l', 'Liquid rate', 'L', '(1 - psi)*F', { kind: 'law', origin: 'Overall balance' }),
  ],
  derivation: a => [
    { text: 'Write a mole balance for each component over the drum, with ψ the fraction of the feed leaving as vapour.', tex: 'z_i = \\psi\\,y_i + (1-\\psi)\\,x_i' },
    { text: 'Equilibrium relates the two compositions through the K-value. Substituting gives each liquid mole fraction in terms of ψ.', tex: 'y_i = K_i x_i \;\\Rightarrow\; x_i = \\frac{z_i}{1+\\psi\\,(K_i-1)}' },
    { text: 'Both sets of mole fractions must sum to one. Subtracting the two sums gives the Rachford–Rice equation, which decreases monotonically in ψ.', tex: '\\sum_i \\frac{z_i\\,(K_i-1)}{1+\\psi\\,(K_i-1)} = 0' },
    { text: 'A two-phase solution exists only between the bubble and dew points, where the function is positive at ψ = 0 and negative at ψ = 1.', tex: '\\sum_i z_i K_i > 1 \\quad\\text{and}\\quad \\sum_i \\frac{z_i}{K_i} > 1' },
    { text: a.raoult ? 'For an ideal mixture the K-value is the ratio of the pure-component vapour pressure to the total pressure.' : 'The Wilson correlation estimates K-values from corresponding states.', tex: a.raoult ? 'K_i = \\frac{p_i^{sat}(T)}{p},\\qquad \\log_{10} p_i^{sat} = A_i - \\frac{B_i}{C_i + t}' : 'K_i = \\frac{p_{c,i}}{p}\\exp\\!\\left[5.373\\,(1+\\omega_i)\\left(1-\\frac{T_{c,i}}{T}\\right)\\right]' },
  ],
  solve(v, a) {
    const z = [v.z_1, v.z_2, Math.max(1 - v.z_1 - v.z_2, 1e-9)], eff = a.equilibrium ? 1 : 0.8;
    const Kof = T => kValues(T, v.p, a.raoult, eff);
    const Tbub = N.bisect(T => N.sum(Kof(T).map((K, i) => z[i] * K)) - 1, 200, 700, 1e-12), Tdew = N.bisect(T => 1 - N.sum(Kof(T).map((K, i) => z[i] / K)), 200, 700, 1e-12);
    const T = a.tp_spec ? v.T : N.bisect(q => rrFun(z, Kof(q), v.psi_s), Tbub - 1e-6, Tdew + 1e-6, 1e-13);
    const K = Kof(T), fl = flashTP(z, K), V = fl.psi * v.F, L = v.F - V;
    const Kp1 = kValues(T, 1, a.raoult, 1), pBub = N.sum(z.map((zi, i) => zi * Kp1[i])), pDew = 1 / N.sum(z.map((zi, i) => zi / Kp1[i]));
    const Ts = N.linspace(Tbub - 10, Tdew + 10, 81), sw = Ts.map(q => flashTP(z, Kof(q)));
    const bal = BTX.map((_, i) => (v.F * z[i] - L * fl.x[i] - V * fl.y[i]) / v.F);
    const warnings = [];
    if (fl.state !== 1) warnings.push(`At these conditions the feed is a ${FLASH_STATES[fl.state].toLowerCase()}; no phase split occurs. The bubble point is ${lab(Tbub - 273.15, '°C')} and the dew point ${lab(Tdew - 273.15, '°C')} at this pressure.`);
    if (a.raoult && v.p > 3e5) warnings.push('Above about 3 bar the vapour is noticeably non-ideal; Raoult’s law then over-predicts K-values by a few per cent.');
    if (!a.raoult) warnings.push('The Wilson correlation is intended for initial estimates; it is typically within 10–20 % of measured K-values for hydrocarbons at low pressure.');
    return {
      scalars: [
        scalar('state', 'Phase state', fl.state, '1', { text: FLASH_STATES[fl.state] }), scalar('T_f', 'Flash temperature', T, 'K', { show: '°C' }),
        scalar('psi', 'Vapour fraction V/F', fl.psi, '1'), scalar('V', 'Vapour rate', V, 'mol/s', { show: 'kmol/h' }), scalar('L', 'Liquid rate', L, 'mol/s', { show: 'kmol/h' }),
        ...BTX.map((c, i) => scalar(`K_${i + 1}`, `K-value of ${c.name.toLowerCase()}`, K[i], '1')),
        ...BTX.map((c, i) => scalar(`x_${i + 1}`, `${c.name} in the liquid`, fl.x[i], '1')),
        ...BTX.map((c, i) => scalar(`y_${i + 1}`, `${c.name} in the vapour`, fl.y[i], '1')),
        scalar('alpha_13', 'Relative volatility, benzene to o-xylene', K[0] / K[2], '1'),
        scalar('T_bub', 'Bubble-point temperature at this pressure', Tbub, 'K', { show: '°C' }), scalar('T_dew', 'Dew-point temperature at this pressure', Tdew, 'K', { show: '°C' }),
        scalar('p_bub', 'Bubble-point pressure at this temperature', pBub, 'Pa', { show: 'bar' }), scalar('p_dew', 'Dew-point pressure at this temperature', pDew, 'Pa', { show: 'bar' }),
        scalar('rec_1', 'Fraction of the benzene recovered in the vapour', V * fl.y[0] / (v.F * z[0]), '1', { show: '%' }),
      ],
      series: [
        line('psi-T', 'Vapour fraction against temperature', 'Temperature', '°C', Ts.map(q => q - 273.15), [{ label: 'Vapour fraction', data: sw.map(q => q.psi) }], 'Vapour fraction', '–', { marker: [T - 273.15, fl.psi] }),
        line('comp-T', 'Benzene content of each phase against temperature', 'Temperature', '°C', Ts.map(q => q - 273.15), [{ label: 'Vapour', data: sw.map(q => q.y[0]) }, { label: 'Liquid', data: sw.map(q => q.x[0]) }, { label: 'Feed', data: Ts.map(() => z[0]), dash: true }], 'Benzene mole fraction', '–'),
        line('rr', 'Rachford–Rice function', 'Vapour fraction', '–', N.linspace(0, 1, 51), [{ label: 'f(ψ)', data: N.linspace(0, 1, 51).map(q => rrFun(z, K, q)) }, { label: 'Zero', data: N.linspace(0, 1, 51).map(() => 0), dash: true }], 'f(ψ)', '–'),
        line('psat', 'Vapour pressures', 'Temperature', '°C', Ts.map(q => q - 273.15), BTX.map(c => ({ label: c.name, data: Ts.map(q => antoine(c, q) / 1e5) })), 'Vapour pressure', 'bar', { logy: true }),
      ],
      checks: [
        check('Liquid mole fractions sum to one', N.sum(fl.x) - 1, 1e-10, 'Σx = 1'), check('Vapour mole fractions sum to one', N.sum(fl.y) - 1, 1e-10, 'Σy = 1'),
        check('Component balances', fl.state === 1 ? N.maxOf(bal.map(Math.abs)) : 0, 1e-10, 'F z_i = L x_i + V y_i for each component'),
        check('Equilibrium relation', fl.state === 1 ? N.maxOf(fl.y.map((y, i) => Math.abs(y - K[i] * fl.x[i]))) : 0, 1e-10, 'y_i = K_i x_i'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const nb = c => N.bisect(T => antoine(c, T) - 101325, 300, 500, 1e-13) - 273.15;
    // binary check: for two components the Rachford–Rice equation has the closed form ψ = [z1(K1 − 1) + z2(K2 − 1)] / [−(K1 − 1)(K2 − 1)]
    const K = [2.2, 0.6, 1], z = [0.45, 0.55, 0], exact = -(z[0] * (K[0] - 1) + z[1] * (K[1] - 1)) / ((K[0] - 1) * (K[1] - 1));
    return [
      bench('Normal boiling point of benzene from the Antoine constants', nb(BTX[0]), 80.10, 'Accepted value 80.1 °C', 1e-3),
      bench('Normal boiling point of toluene from the Antoine constants', nb(BTX[1]), 110.63, 'Accepted value 110.6 °C', 1e-3),
      bench('Normal boiling point of o-xylene from the Antoine constants', nb(BTX[2]), 144.41, 'Accepted value 144.4 °C', 1e-3),
      bench('Binary flash vs closed-form vapour fraction', flashTP(z, K).psi, exact, 'Analytical solution of the two-component Rachford–Rice equation', 1e-10),
      bench('Wilson K-value equals p_c/p at the critical temperature', kValues(BTX[0].Tc, 1e5, false, 1)[0], 48.95, 'Limit of the Wilson correlation: benzene at 1 bar and its critical temperature', 1e-12),
      bench('Wilson constant: K p/p_c at a reduced temperature of 0.7 and zero acentric factor', Math.exp(5.373 * (1 - 1 / 0.7)), 0.1, 'Definition of the acentric factor: p_sat/p_c = 0.1 at T_r = 0.7 when ω = 0, so the constant is (7/3) ln 10', 2e-3),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(270, 60, 110, 240, 'd-body', 50)} ${S.rect(272, 200, 106, 98, 'd-liquid', 40)} ${S.path('M272 200 L378 200', 'd-liquid-line')}
      ${S.arrow(90, 180, 268, 180)} ${S.text(170, 168, `feed ${lab(v.F * 3.6, 'kmol/h')}`)} ${S.text(170, 198, `z = ${lab(v.z_1, '', 2)} / ${lab(v.z_2, '', 2)} / ${lab(1 - v.z_1 - v.z_2, '', 2)}`, 'd-text d-small')}
      ${S.path('M325 60 L325 30 L520 30', 'd-pipe')} ${S.arrow(520, 30, 590, 30)} ${S.text(520, 20, 'vapour V, y')}
      ${S.path('M325 300 L325 330 L520 330', 'd-pipe')} ${S.arrow(520, 330, 590, 330)} ${S.text(520, 320, 'liquid L, x')}
      ${S.text(470, 170, `${lab(v.T - 273.15, '°C')}, ${lab(v.p / 1e5, 'bar')}`)} ${S.text(470, 192, 'benzene / toluene / o-xylene', 'd-text d-small')}
      ${[0, 1, 2].map(i => S.arrow(300 + i * 25, 195, 300 + i * 25, 150)).join('')}
    `);
  },
  experiment: {
    objective: 'Measure equilibrium vapour and liquid compositions of the ternary mixture at fixed temperature and pressure and compare with the flash prediction.',
    apparatus: ['Recirculating vapour–liquid equilibrium still (Othmer or Gillespie type) with pressure control', 'Heating mantle and condenser', 'Sampling ports on the liquid and condensed-vapour loops'],
    instruments: [{ name: 'Gas chromatograph with flame-ionisation detector', measures: 'Mole fractions in each phase', range: '0–1', resolution: '±0.002' }, { name: 'Pt100 in the equilibrium chamber', measures: 'Equilibrium temperature', range: '0–200 °C', resolution: '±0.05 K' }, { name: 'Absolute pressure transducer', measures: 'System pressure', range: '0–5 bar', resolution: '±0.05 %' }],
    procedure: ['Charge a mixture of known composition and bring it to steady boiling at the set pressure.', 'Recirculate until the temperature is constant to 0.05 K for 30 minutes.', 'Sample both phases and analyse by gas chromatography.', 'Repeat over a range of charge compositions and pressures.', 'Check thermodynamic consistency of the data before comparing with the model.'],
    controls: ['Pure-component boiling points to verify the thermometer and pressure gauge', 'Replicate injections for chromatographic repeatability'],
    signatures: ['Vapour richer in benzene than the liquid at every condition', 'K-values close to p_sat/p for each component', 'Vapour fraction rising from zero at the bubble point to one at the dew point'],
    safety: ['Benzene is a carcinogen: closed handling, extraction and exposure monitoring', 'Flammable vapours: ignition control and inert purging', 'Hot surfaces and glassware under pressure'],
  },
  falsify: ['Measured K-values differing from p_sat/p by much more than experimental uncertainty at low pressure for this nearly ideal system.', 'A two-phase region observed outside the computed bubble and dew temperatures.'],
  alternatives: [{ name: 'Activity-coefficient models (Wilson, NRTL, UNIQUAC)', text: 'Needed for non-ideal liquids such as alcohol–water mixtures, where K-values depend on composition.' }, { name: 'Cubic equations of state (Peng–Robinson, Soave–Redlich–Kwong)', text: 'Give K-values from fugacity coefficients of both phases; required at high pressure and near critical conditions.' }, { name: 'Adiabatic (enthalpy-specified) flash', text: 'Adds an energy balance so that temperature is an outcome; relevant to flashing across a valve.' }],
  hazards: [{ hazard: 'Toxic exposure', cause: 'Benzene vapour', mitigation: 'Containment, ventilation, monitoring' }, { hazard: 'Fire and explosion', cause: 'Flammable aromatic vapours', mitigation: 'Hazardous-area equipment, inerting, relief to a safe location' }, { hazard: 'Liquid carry-over', cause: 'Excess vapour velocity in the drum', mitigation: 'Drum sizing by the Souders–Brown criterion, demister' }],
  standards: ['API Standard 521 (pressure-relieving and depressuring systems)', 'API RP 12J (specification for oil and gas separators)', 'ASME BPVC Section VIII (pressure vessels)'],
  limits: 'Low to moderate pressure, nearly ideal liquid mixtures. K-values are independent of composition. Not valid near critical conditions or for polar or associating components.',
  numerics: { method: 'Bisection on the monotonic Rachford–Rice function; bisection for bubble and dew temperatures' },
  optimise: { objective: 'rec_1', sense: 'max', vars: ['T', 'p'], note: 'Recovery rises with temperature at the cost of purity; a single flash gives limited separation.' },
  inverse: { series: 'psi-T', curve: 0, fit: ['p'] },
  extensions: ['Adiabatic flash with an enthalpy balance', 'Composition-dependent K-values from an equation of state', 'Multistage distillation built from linked flashes', 'Drum sizing from the Souders–Brown velocity'],
};

// ------------------------------------------------------------------ produced-water separation
/** Stokes velocity, optionally with the Schiller–Naumann drag correction solved by fixed-point iteration. */
function settlingVelocity(d, drho, mu, rhoC, acc, stokes) {
  const vs = acc * d * d * Math.abs(drho) / (18 * mu);
  if (stokes) return vs;
  let u = vs;
  for (let i = 0; i < 60; i++) { const Re = rhoC * u * d / mu, un = vs / (1 + 0.15 * Math.pow(Re, 0.687)); if (Math.abs(un - u) < 1e-12 * vs) { u = un; break; } u = 0.5 * (u + un); }
  return u;
}
/** Volume-weighted log-normal size distribution on a logarithmic grid. */
function lognormalGrid(d50, sg, n = 161) {
  const s = Math.log(sg), u = N.linspace(-4.5, 4.5, n), d = u.map(q => d50 * Math.exp(q * s)), w = u.map(q => Math.exp(-q * q / 2) / Math.sqrt(2 * Math.PI));
  const du = u[1] - u[0], wt = w.map((q, i) => q * du * (i === 0 || i === n - 1 ? 0.5 : 1)), tot = N.sum(wt);
  return { d, wt: wt.map(q => q / tot) };
}

const producedWater = {
  id: 'produced-water-separation',
  title: 'Produced-water treatment: gravity and hydrocyclone separation',
  module: 2, klass: 'I', domains: ['chemical', 'offshore'],
  keywords: ['produced water', 'oil-water separation', 'oil water separator', 'oil in water', 'hydrocyclone', 'deoiling', 'skim tank', 'gravity separator', 'stokes', 'settling velocity', 'cut size', 'grade efficiency', 'discharge limit', 'sand', 'api separator'],
  summary: 'Removal of dispersed oil and solids from produced water by gravity settling or a deoiling hydrocyclone: Stokes velocities, cut size, grade efficiency and outlet oil content against a discharge limit.',
  background: [
    'Water produced with oil and gas carries dispersed oil droplets and solid particles that must be removed before discharge or reinjection. Droplets rise and solids settle at a terminal velocity given by Stokes’ law, proportional to the density difference and to the square of the diameter and inversely proportional to the water viscosity.',
    'In an ideal horizontal separator a droplet is captured if it can cross the liquid depth within the residence time, which reduces to a comparison of its rise velocity with the overflow rate Q/A (Hazen’s principle); depth cancels out. A hydrocyclone applies the same principle with gravity replaced by a centrifugal acceleration of the order of a thousand times larger, allowing residence times of a few seconds. Because capture depends on the square of the diameter, performance is controlled by the fine end of the droplet-size distribution, which is in turn set by upstream shear in valves and pumps.',
  ],
  phenomena: ['Buoyant rise of droplets and settling of solids', 'Creeping flow drag', 'Centrifugal separation', 'Polydisperse size distribution'],
  laws: ['mass', 'momentum', 'archimedes', 'newton2'],
  refs: ['Stokes, G. G. (1851). On the effect of the internal friction of fluids on the motion of pendulums. Trans. Cambridge Phil. Soc. 9, 8–106.', 'Hazen, A. (1904). On sedimentation. Trans. American Society of Civil Engineers 53, 45–71.', 'Schiller, L. & Naumann, A. (1933). Über die grundlegenden Berechnungen bei der Schwerkraftaufbereitung. Zeitschrift des Vereines Deutscher Ingenieure 77, 318–320.', 'Arnold, K. & Stewart, M. (2008). Surface Production Operations, Vol. 1, 3rd ed., Gulf Professional Publishing.', 'Colman, D. A. & Thew, M. T. (1983). Correlation of separation results from light dispersion hydrocyclones. Chemical Engineering Research and Design 61, 233–240.'],
  inputs: [
    inp('Q', 'Produced-water flow rate', 'm^3/h', 200, { min: 5, max: 2000, aliases: ['flow rate', 'water rate', 'throughput'] }),
    inp('L_sep', 'Separator effective length', 'm', 12, { min: 2, max: 40, kind: 'geometry', aliases: ['separator length', 'length'] }),
    inp('W_sep', 'Separator width', 'm', 3, { min: 0.5, max: 10, kind: 'geometry', aliases: ['separator width', 'width'] }),
    inp('rho_w', 'Water density', 'kg/m^3', 1030, { min: 980, max: 1200, kind: 'fluid', aliases: ['water density'] }),
    inp('mu_w', 'Water viscosity', 'cP', 0.6, { min: 0.2, max: 2, kind: 'fluid', aliases: ['water viscosity', 'viscosity'], src: 'Brine near 50 °C' }),
    inp('rho_o', 'Oil density', 'kg/m^3', 850, { min: 700, max: 950, kind: 'fluid', aliases: ['oil density'] }),
    inp('d_50', 'Volume-median oil droplet diameter', 'um', 60, { min: 5, max: 500, kind: 'fluid', aliases: ['droplet size', 'droplet diameter', 'median droplet'] }),
    inp('sigma_g', 'Geometric standard deviation of the droplet sizes', '1', 2, { min: 1.2, max: 3.5, kind: 'fluid', aliases: ['geometric standard deviation'] }),
    inp('C_in', 'Oil-in-water concentration at the inlet', 'mg/L', 800, { min: 50, max: 5000, aliases: ['inlet oil', 'oil in water', 'oil concentration'] }),
    inp('C_lim', 'Discharge limit for oil in water', 'mg/L', 30, { min: 5, max: 100, aliases: ['discharge limit', 'limit'], src: 'OSPAR Recommendation 2001/1: 30 mg/L monthly average' }),
    inp('rho_s', 'Solids density', 'kg/m^3', 2650, { min: 1500, max: 4500, kind: 'fluid', aliases: ['sand density', 'solids density'] }),
    inp('d_s', 'Median solids diameter', 'um', 60, { min: 5, max: 500, kind: 'fluid', aliases: ['sand size', 'particle size'] }),
    inp('C_s', 'Solids concentration at the inlet', 'mg/L', 150, { min: 1, max: 2000, aliases: ['solids concentration', 'sand concentration'] }),
    inp('D_c', 'Hydrocyclone liner diameter', 'mm', 35, { min: 20, max: 80, kind: 'geometry', aliases: ['liner diameter', 'cyclone diameter'] }),
    inp('L_c', 'Hydrocyclone liner active length', 'm', 1.2, { min: 0.5, max: 2, kind: 'geometry', aliases: ['liner length'] }),
    inp('n_c', 'Number of hydrocyclone liners', '1', 40, { min: 4, max: 400, kind: 'geometry', aliases: ['liners', 'number of liners'] }),
    inp('a_c', 'Centrifugal acceleration in the hydrocyclone', 'g0', 1000, { min: 100, max: 3000, aliases: ['centrifugal acceleration', 'g-force'] }),
  ],
  assumptions: [
    asm('gravity', 'Separation is by gravity in a horizontal skim vessel or plate-free API separator.', { why: 'Simple primary treatment', alt: 'Separation is in deoiling hydrocyclone liners, where centrifugal acceleration replaces gravity and solids are not removed.' }),
    asm('stokes', 'Droplets and particles move at the Stokes velocity.', { why: 'Particle Reynolds number well below one for fine droplets', alt: 'The Schiller–Naumann drag correction is applied for finite Reynolds number.' }),
    asm('plug_flow', 'Flow through the separator is ideal plug flow.', { why: 'Hazen’s ideal basin', alt: 'The vessel is fully back-mixed, which lowers the capture of every size.' }),
    asm('no_coalescence', 'Droplets neither coalesce nor break up inside the separator.', { why: 'Conservative for dilute dispersions', alt: 'Not resolved: a warning notes that coalescence would improve, and shear would worsen, the result.' }),
  ],
  symbols: { v_t: ['Rise velocity of the median droplet', 'm/s'], v_o: ['Overflow rate, or required radial migration velocity in a hydrocyclone', 'm/s'], v_p: ['Terminal velocity of a droplet of diameter d_p', 'm/s'], d_100: ['Smallest droplet fully captured (cut size)', 'm'], d_p: ['Droplet diameter', 'm'], eta_d: ['Grade efficiency', '1'], E_T: ['Total oil-removal efficiency', '1'], C_out: ['Oil in water at the outlet', 'kg/m^3'], m_rec: ['Oil recovered', 'kg/s'], t_res: ['Residence time in a liner', 's'], Re_p: ['Particle Reynolds number', '1'] },
  equations: a => [
    eq('stokes', 'Terminal velocity', 'v_t', a.gravity ? (a.stokes ? 'g*d_50^2*(rho_w - rho_o)/(18*mu_w)' : 'g*d_50^2*(rho_w - rho_o)/(18*mu_w*(1 + 0.15*Re_p^0.687))') : (a.stokes ? 'a_c*d_50^2*(rho_w - rho_o)/(18*mu_w)' : 'a_c*d_50^2*(rho_w - rho_o)/(18*mu_w*(1 + 0.15*Re_p^0.687))'), { kind: 'law', origin: a.stokes ? 'Stokes (1851): balance of buoyancy and creeping-flow drag' : 'Stokes drag with the Schiller–Naumann (1933) correction', needs: a.stokes ? ['stokes'] : [] }),
    eq('rep', 'Particle Reynolds number', 'Re_p', 'rho_w*v_t*d_50/mu_w', { kind: 'definition' }),
    ...(a.gravity
      ? [eq('vo', 'Overflow rate', 'v_o', 'Q/(L_sep*W_sep)', { kind: 'definition', origin: 'Hazen (1904)', needs: ['gravity'] }),
        a.stokes ? eq('d100', 'Cut size', 'd_100', 'sqrt(18*mu_w*v_o/(g*(rho_w - rho_o)))', { kind: 'derived', origin: 'Rise velocity equal to overflow rate', needs: ['stokes'] })
          : eq('d100', 'Cut size (implicit)', 'g*d_100^2*(rho_w - rho_o)/(18*mu_w*(1 + 0.15*(rho_w*v_o*d_100/mu_w)^0.687))', 'v_o', { kind: 'derived', origin: 'Drag-corrected rise velocity equal to overflow rate' })]
      : [eq('tres', 'Liner residence time', 't_res', 'n_c*pi*D_c^2*L_c/(4*Q)', { kind: 'definition' }),
        eq('vo', 'Required radial migration velocity', 'v_o', 'D_c/(2*t_res)', { kind: 'closure', origin: 'Liner radius crossed within the residence time; a simplified model of a deoiling hydrocyclone' }),
        a.stokes ? eq('d100', 'Cut size', 'd_100', 'sqrt(18*mu_w*v_o/(a_c*(rho_w - rho_o)))', { kind: 'derived', origin: 'Migration velocity equal to the required velocity', needs: ['stokes'] })
          : eq('d100', 'Cut size (implicit)', 'a_c*d_100^2*(rho_w - rho_o)/(18*mu_w*(1 + 0.15*(rho_w*v_o*d_100/mu_w)^0.687))', 'v_o', { kind: 'derived', origin: 'Drag-corrected migration velocity equal to the required velocity' })]),
    ...(a.stokes
      ? [a.plug_flow ? eq('grade', 'Grade efficiency', 'eta_d', 'min(1, (d_p/d_100)^2)', { kind: 'derived', origin: 'Uniform inlet distribution in ideal plug flow; velocity proportional to the square of diameter', needs: ['plug_flow', 'stokes'] }) : eq('grade', 'Grade efficiency', 'eta_d', '(d_p/d_100)^2/(1 + (d_p/d_100)^2)', { kind: 'derived', origin: 'Fully mixed basin, Hazen (1904)', needs: ['stokes'] })]
      : [a.plug_flow ? eq('grade', 'Grade efficiency', 'eta_d', 'min(1, v_p/v_o)', { kind: 'derived', origin: 'Uniform inlet distribution in ideal plug flow', needs: ['plug_flow'] }) : eq('grade', 'Grade efficiency', 'eta_d', '(v_p/v_o)/(1 + v_p/v_o)', { kind: 'derived', origin: 'Fully mixed basin, Hazen (1904)' })]),
    eq('cout', 'Outlet oil content', 'C_out', 'C_in*(1 - E_T)', { kind: 'law', origin: 'Oil mass balance' }),
    eq('mrec', 'Oil recovered', 'm_rec', 'Q*C_in*E_T', { kind: 'law', origin: 'Oil mass balance' }),
  ],
  derivation: a => [
    { text: 'A small sphere reaches terminal velocity when its net buoyancy equals the Stokes drag.', tex: '\\frac{\\pi d^3}{6}\\,\\Delta\\rho\\,g = 3\\pi\\mu\\,d\\,v_t \;\\Rightarrow\; v_t = \\frac{g\\,d^2\\,\\Delta\\rho}{18\\,\\mu}' },
    ...(a.gravity
      ? [{ text: 'In plug flow of depth H a droplet entering at the bottom is captured if it rises H within the residence time L W H/Q. Depth cancels, leaving a comparison with the overflow rate.', tex: 'v_t \\ge \\frac{Q}{L\\,W} = v_o \;\\Rightarrow\; d_{100} = \\sqrt{\\frac{18\\,\\mu\\,v_o}{g\\,\\Delta\\rho}}' }]
      : [{ text: 'In a hydrocyclone the centrifugal acceleration a_c replaces gravity; a droplet must migrate inward across the liner radius within the residence time, at a velocity v_o = D_c/(2 t_res).', tex: 'd_{100} = \\sqrt{\\frac{18\\,\\mu\\,v_o}{a_c\\,\\Delta\\rho}} = \\sqrt{\\frac{9\\,\\mu\\,D_c}{a_c\\,\\Delta\\rho\\,t_{res}}}' }]),
    { text: a.plug_flow ? 'Smaller droplets are captured only if they enter close enough to the collecting surface; for a uniform inlet the captured fraction is the ratio of velocities.' : 'If the vessel is fully mixed the captured fraction follows from a balance between removal at the surface and wash-out with the flow.', tex: a.plug_flow ? '\\eta(d) = \\min\\!\\left[1,\\ \\left(\\frac{d}{d_{100}}\\right)^2\\right]' : '\\eta(d) = \\frac{(d/d_{100})^2}{1+(d/d_{100})^2}' },
    { text: 'The total efficiency is the grade efficiency weighted by the volume distribution of droplet sizes, here log-normal.', tex: 'E_T = \\int_0^\\infty \\eta(d)\\,f_v(d)\\,\\mathrm{d}d,\\qquad C_{out} = C_{in}\\,(1-E_T)' },
  ],
  solve(v, a) {
    const drho = v.rho_w - v.rho_o, acc = a.gravity ? g : v.a_c, Ah = v.L_sep * v.W_sep, vo = v.Q / Ah;
    const tres = v.n_c * Math.PI * v.D_c ** 2 * v.L_c / (4 * v.Q), vReq = a.gravity ? vo : (v.D_c / 2) / tres;
    const vel = (d, dr) => settlingVelocity(d, dr, v.mu_w, v.rho_w, acc, a.stokes);
    const d100s = Math.sqrt(18 * v.mu_w * vReq / (acc * drho));
    const d100 = a.stokes ? d100s : N.bisect(d => vel(d, drho) - vReq, d100s * 0.5, d100s * 100, 1e-12);
    const grade = (d, dr) => { const q = vel(d, dr) / vReq; return a.plug_flow ? Math.min(1, q) : q / (1 + q); };
    const oil = lognormalGrid(v.d_50, v.sigma_g), ET = N.sum(oil.d.map((d, i) => grade(d, drho) * oil.wt[i]));
    const Cout = v.C_in * (1 - ET), mIn = v.Q * v.C_in, mRec = mIn * ET, mOut = v.Q * Cout;
    const sol = lognormalGrid(v.d_s, 1.8), drs = v.rho_s - v.rho_w, ES = a.gravity ? N.sum(sol.d.map((d, i) => grade(d, drs) * sol.wt[i])) : 0;
    const sIn = v.Q * v.C_s, sSet = sIn * ES, sOut = sIn - sSet;
    const vt50 = vel(v.d_50, drho), Re50 = v.rho_w * vt50 * v.d_50 / v.mu_w;
    // required overflow-rate change to meet the limit (Stokes scaling of the cut size)
    const outAt = k => v.C_in * (1 - N.sum(oil.d.map((d, i) => { const q = vel(d, drho) / (vReq * k); return (a.plug_flow ? Math.min(1, q) : q / (1 + q)) * oil.wt[i]; })));
    const kReq = outAt(1e-6) > v.C_lim ? 0 : outAt(1e6) < v.C_lim ? Infinity : Math.exp(N.bisect(q => outAt(Math.exp(q)) - v.C_lim, Math.log(1e-6), Math.log(1e6), 1e-10));
    const ds = N.logspace(1e-6, 1e-3, 80), cum = (grid, f) => ds.map(dd => N.sum(grid.d.map((d, i) => (d <= dd ? f(d) * grid.wt[i] : 0))));
    const outTot = Math.max(1 - ET, 1e-300), Qs = N.linspace(0.2 * v.Q, 2 * v.Q, 40);
    const warnings = [];
    if (Cout > v.C_lim) warnings.push(`Outlet oil content of ${lab(Cout * 1000, 'mg/L')} exceeds the discharge limit of ${lab(v.C_lim * 1000, 'mg/L')}. ${Number.isFinite(kReq) && kReq > 0 ? `The ${a.gravity ? 'overflow rate' : 'flow per liner'} would have to fall to ${lab(kReq * 100, '%')} of its present value` : 'No practical size of this equipment would meet it'}; a secondary stage such as flotation is normally needed.`);
    if (a.stokes && Re50 > 1) warnings.push(`The particle Reynolds number of the median droplet is ${lab(Re50)}; Stokes’ law over-predicts its velocity. Switch on the drag correction.`);
    if (!a.gravity) warnings.push('Solids pass through a deoiling hydrocyclone with the water; a desander or solids-removal stage is needed upstream. The hydrocyclone model is a simplified migration-time estimate and should be calibrated against supplier data.');
    if (!a.no_coalescence) warnings.push('Coalescence in the inlet zone or on plate packs would raise the capture of fine droplets; shear in valves and pumps would lower it. Neither is resolved here.');
    if (a.gravity && vo > 0.01) warnings.push('The overflow rate is high enough that turbulence and short-circuiting will reduce performance well below the ideal value.');
    return {
      scalars: [
        scalar('v_t', 'Rise velocity of the median droplet', vt50, 'm/s', { show: 'mm/s' }), scalar('Re_p', 'Reynolds number of the median droplet', Re50, '1'),
        scalar('v_o', a.gravity ? 'Overflow rate Q/A' : 'Required radial migration velocity', vReq, 'm/s', { show: 'mm/s' }),
        scalar('t_res', 'Residence time in a hydrocyclone liner', tres, 's'), scalar('d_100', 'Cut size (smallest droplet fully captured in plug flow)', d100, 'm', { show: 'um' }),
        scalar('E_T', 'Total oil-removal efficiency', ET, '1', { show: '%' }), scalar('C_out', 'Oil in water at the outlet', Cout, 'kg/m^3', { show: 'mg/L' }),
        scalar('margin', 'Margin to the discharge limit', v.C_lim - Cout, 'kg/m^3', { show: 'mg/L', text: Cout > v.C_lim ? `Limit exceeded by ${lab((Cout - v.C_lim) * 1000, 'mg/L')}` : undefined }),
        scalar('k_req', 'Loading relative to present that would just meet the limit', kReq, '1', { text: kReq === 0 ? 'Limit cannot be met by resizing' : !Number.isFinite(kReq) ? 'Limit met at any loading' : undefined }),
        scalar('m_water', 'Stream table: water', v.Q * v.rho_w, 'kg/s', { show: 't/h' }), scalar('m_oil_in', 'Stream table: oil in the feed', mIn, 'kg/s', { show: 'kg/h' }),
        scalar('m_rec', 'Stream table: oil recovered', mRec, 'kg/s', { show: 'kg/h' }), scalar('m_oil_out', 'Stream table: oil in the treated water', mOut, 'kg/s', { show: 'kg/h' }),
        scalar('E_S', 'Solids-removal efficiency', ES, '1', { show: '%' }), scalar('m_s_in', 'Stream table: solids in the feed', sIn, 'kg/s', { show: 'kg/h' }),
        scalar('m_s_set', 'Stream table: solids settled', sSet, 'kg/s', { show: 'kg/h' }), scalar('m_s_out', 'Stream table: solids in the treated water', sOut, 'kg/s', { show: 'kg/h' }),
      ],
      series: [
        line('grade', 'Grade efficiency and droplet-size distributions', 'Droplet diameter', 'µm', ds.map(q => q * 1e6), [{ label: 'Grade efficiency', data: ds.map(d => grade(d, drho)) }, { label: 'Inlet cumulative volume', data: cum(oil, () => 1), dash: true }, { label: 'Outlet cumulative volume', data: cum(oil, d => (1 - grade(d, drho)) / outTot), dash: true }], 'Fraction', '–', { logx: true }),
        line('cout-Q', 'Outlet oil content against flow rate', 'Flow rate', 'm³/h', Qs.map(q => q * 3600), [{ label: 'Oil in water at the outlet', data: Qs.map(q => outAt(q / v.Q) * 1000) }, { label: 'Discharge limit', data: Qs.map(() => v.C_lim * 1000), dash: true }], 'Oil in water', 'mg/L'),
      ],
      checks: [
        check('Oil mass balance', (mIn - mRec - mOut) / mIn, 1e-12, 'Oil in = oil recovered + oil in treated water'),
        check('Solids mass balance', (sIn - sSet - sOut) / sIn, 1e-12, 'Solids in = solids settled + solids in treated water'),
        check('Size distribution normalised', N.sum(oil.wt) - 1, 1e-12, 'Volume fractions sum to one'),
        check('Efficiency within bounds', ET < 0 || ET > 1 ? 1 : 0, 0, '0 ≤ E_T ≤ 1'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { gravity: true, stokes: true, plug_flow: true, no_coalescence: true };
    const mono = this.solve({ ...v, sigma_g: 1.2, d_50: 20e-6 }, b), d100 = val(mono, 'd_100');
    const narrow = lognormalGrid(20e-6, 1.0001), eNarrow = N.sum(narrow.d.map((d, i) => Math.min(1, (d / d100) ** 2) * narrow.wt[i]));
    const vs = 1, u = settlingVelocity(1e-4, 100, 1e-3, 1000, 18 * 1e-3 * vs / (1e-8 * 100), false);
    return [
      bench('Stokes rise velocity of a 100 µm droplet', settlingVelocity(100e-6, 150, 1e-3, 1000, g, true), 9.80665 * 1e-8 * 150 / 0.018, 'v = g d² Δρ/(18 μ) = 0.817 mm/s', 1e-12),
      bench('Grade efficiency at the cut size', Math.min(1, settlingVelocity(d100, v.rho_w - v.rho_o, v.mu_w, v.rho_w, g, true) / (v.Q / (v.L_sep * v.W_sep))), 1, 'Definition of d_100', 1e-9),
      bench('Monodisperse limit of the total efficiency', eNarrow, Math.min(1, (20e-6 / d100) ** 2), 'E_T → (d/d_100)² as the distribution narrows', 1e-3),
      bench('Schiller–Naumann velocity satisfies its own drag law', u * (1 + 0.15 * Math.pow(1000 * u * 1e-4 / 1e-3, 0.687)), vs, 'v (1 + 0.15 Re^0.687) = v_Stokes', 1e-8),
    ];
  },
  validation: [],
  diagram(v, a) {
    return a.gravity ? svg(`
      ${S.rect(80, 110, 480, 150, 'd-body', 20)} ${S.rect(82, 140, 476, 118, 'd-liquid', 16)} ${S.path('M82 140 L558 140', 'd-liquid-line')}
      ${S.rect(82, 124, 476, 16, 'd-hazard', 6)} ${S.text(320, 104, 'oil layer skimmed')}
      ${S.arrow(20, 190, 78, 190)} ${S.text(46, 178, 'feed', 'd-text d-small')} ${S.arrow(562, 220, 622, 220)} ${S.text(596, 208, 'water', 'd-text d-small')}
      ${[0, 1, 2, 3].map(i => S.arrow(160 + i * 90, 230 - i * 14, 190 + i * 90, 180 - i * 14)).join('')} ${S.text(240, 246, 'droplets rise at v_t')}
      ${S.path('M120 256 L520 256', 'd-ground')} ${S.text(430, 250, 'solids settle', 'd-text d-small')}
      ${S.dim(80, 300, 560, 300, `L = ${lab(v.L_sep, 'm')},  W = ${lab(v.W_sep, 'm')}`)}
      ${S.text(320, 50, `Q = ${lab(v.Q * 3600, 'm³/h')},  median droplet ${lab(v.d_50 * 1e6, 'µm')}`)}
    `) : svg(`
      ${S.path('M120 130 L260 130 L560 165 L560 195 L260 230 L120 230 Z', 'd-body')}
      ${S.arrow(150, 70, 150, 128)} ${S.text(150, 60, 'tangential feed')}
      ${S.path('M130 180 L540 180', 'd-line d-hazard')} ${S.arrow(118, 180, 50, 180, 'd-arrow d-hazard')} ${S.text(70, 168, 'oil reject', 'd-text d-small')}
      ${S.arrow(562, 180, 620, 180)} ${S.text(592, 168, 'water', 'd-text d-small')}
      ${S.path('M180 140 Q200 180 180 220 M240 140 Q262 180 240 220 M310 146 Q328 180 310 214', 'd-line')}
      ${S.text(330, 270, `${Math.round(v.n_c)} liners of ${lab(v.D_c * 1000, 'mm')},  ${lab(v.a_c / g, 'g')}`)}
      ${S.text(320, 30, `Q = ${lab(v.Q * 3600, 'm³/h')},  median droplet ${lab(v.d_50 * 1e6, 'µm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the grade efficiency of a separator by comparing inlet and outlet droplet-size distributions, and verify the outlet oil-in-water concentration.',
    apparatus: ['Pilot gravity separator or single hydrocyclone liner on a test loop', 'Oil injection through a shear valve to generate a controlled dispersion', 'Isokinetic sampling points at inlet and outlet'],
    instruments: [{ name: 'Laser-diffraction or in-line image-analysis particle sizer', measures: 'Droplet-size distribution', range: '1–1000 µm', resolution: '±3 % on median' }, { name: 'Infrared or gas-chromatographic oil-in-water analysis of extracted samples', measures: 'Dispersed oil concentration', range: '1–2000 mg/L', resolution: '±10 % or ±2 mg/L' }, { name: 'Electromagnetic flow meter', measures: 'Water flow rate', range: '1–500 m³/h', resolution: '±0.5 %' }, { name: 'Differential pressure transmitters', measures: 'Hydrocyclone pressure-drop ratio', range: '0–20 bar', resolution: '±0.1 %' }],
    procedure: ['Establish steady flow and inlet dispersion; record inlet size distribution and concentration.', 'Sample the outlet after at least three residence times.', 'Compute the grade efficiency for each size class from the two distributions and the total efficiency.', 'Repeat over a range of flow rates and inlet droplet sizes.'],
    controls: ['Oil mass balance including the recovered stream', 'Repeat samples to quantify analytical scatter', 'Check for droplet break-up in the sampling line'],
    signatures: ['Grade efficiency rising as the square of diameter below the cut size', 'Outlet distribution depleted of large droplets', 'Efficiency falling as flow rate rises in a gravity vessel, but rising with flow in a hydrocyclone until break-up sets in'],
    safety: ['Hydrocarbon handling: ventilation, ignition control, spill containment', 'Pressurised test loop precautions', 'Solvent handling in oil-in-water analysis'],
  },
  falsify: ['Droplets well above the cut size found in the outlet of a properly baffled gravity separator in quantity inconsistent with short-circuiting.', 'Rise velocities of single small droplets departing from Stokes’ law at particle Reynolds numbers below 0.1 in clean water.'],
  alternatives: [{ name: 'Plate-pack (corrugated or parallel plate) interceptors', text: 'Reduce the rise distance to the plate spacing and so capture smaller droplets in the same footprint.' }, { name: 'Induced or dissolved gas flotation', text: 'Attaches droplets to gas bubbles, raising the effective density difference and diameter; the usual polishing stage after hydrocyclones.' }, { name: 'Empirical hydrocyclone correlations', text: 'Colman and Thew correlate migration probability with a hydrocyclone number; supplier curves are used in practice.' }],
  hazards: [{ hazard: 'Discharge above the permitted oil content', cause: 'Fine droplets from upstream shear, chemical upset, overload', mitigation: 'On-line monitoring, recycle of off-specification water, low-shear valves' }, { hazard: 'Sand accumulation and erosion', cause: 'Solids settling in vessels or passing through liners', mitigation: 'Desanders, jetting systems, erosion-resistant liners' }, { hazard: 'Hydrocarbon release', cause: 'Loss of containment', mitigation: 'Closed drains, gas detection' }],
  standards: ['OSPAR Recommendation 2001/1 (management of produced water from offshore installations)', 'API Publication 421 (design and operation of oil–water separators)', 'ISO 9377-2 (determination of hydrocarbon oil index in water)', 'US EPA 40 CFR Part 435 (oil and gas extraction effluent guidelines)'],
  limits: 'Dilute dispersions of rigid spherical droplets with no coalescence or break-up, ideal flow patterns and a log-normal size distribution. The hydrocyclone model is a first estimate only.',
  numerics: { method: 'Numerical quadrature over a logarithmic size grid; fixed-point iteration for the drag correction' },
  optimise: { objective: 'C_out', sense: 'min', vars: ['L_sep', 'W_sep'], note: 'Outlet oil falls with plan area; plate packs give the same effect in less space.' },
  inverse: { series: 'cout-Q', curve: 0, fit: ['d_50', 'sigma_g'] },
  extensions: ['Plate-pack geometry with laminar-flow criteria', 'Population balance for coalescence and break-up', 'Hydrocyclone pressure-drop ratio and reject-rate control', 'Gas flotation as a polishing stage'],
};

// ------------------------------------------------------------------ water hammer
function hammerSetup(v, a) {
  const c1 = a.anchored ? 1 - v.nu ** 2 : 1;
  const aw = Math.sqrt((v.K_f / v.rho) / (a.elastic ? 1 + v.K_f * v.D * c1 / (v.E_p * v.e_w) : 1));
  let f = a.friction ? v.f_D : 0, limited = false;
  if (f * v.L / v.D * v.v_0 ** 2 / (2 * g) > 0.9 * v.H_0) { f = 0.9 * v.H_0 * 2 * g * v.D / (v.L * v.v_0 ** 2); limited = true; }
  return { aw, f, limited, c1 };
}
/** Method of characteristics for a reservoir–pipe–valve system. Returns heads in metres above the valve outlet. */
function hammerMOC(v, a, setup, nReach, nPeriods = 4, tauOf) {
  const { aw, f } = setup, n = nReach, dx = v.L / n, dt = dx / aw, B = aw / g, Rf = f * dt / (2 * v.D);
  const x = N.linspace(0, v.L, n + 1);
  let H = x.map(s => v.H_0 - f * s / v.D * v.v_0 ** 2 / (2 * g)), V = x.map(() => v.v_0);
  const Hv0 = H[n], tau = tauOf || (t => (a.gradual ? Math.max(0, 1 - t / v.t_c) : 0));
  const tEnd = nPeriods * 4 * v.L / aw + (a.gradual ? v.t_c : 0), nt = Math.min(Math.ceil(tEnd / dt), 40000);
  const t = [0], Hvalve = [Hv0], Hmid = [H[n >> 1]], Vres = [v.v_0], frames = [H.slice()], ftimes = [0], every = Math.max(1, Math.floor(nt / 80));
  let Hmax = Hv0, Hmin = Hv0, HminAll = N.minOf(H);
  for (let k = 1; k <= nt; k++) {
    const Hn = new Array(n + 1), Vn = new Array(n + 1);
    for (let i = 1; i < n; i++) {
      const Cp = V[i - 1] + H[i - 1] / B - Rf * V[i - 1] * Math.abs(V[i - 1]), Cm = V[i + 1] - H[i + 1] / B - Rf * V[i + 1] * Math.abs(V[i + 1]);
      Vn[i] = 0.5 * (Cp + Cm); Hn[i] = 0.5 * B * (Cp - Cm);
    }
    Hn[0] = v.H_0; Vn[0] = V[1] - H[1] / B - Rf * V[1] * Math.abs(V[1]) + v.H_0 / B;
    const Cp = V[n - 1] + H[n - 1] / B - Rf * V[n - 1] * Math.abs(V[n - 1]), tk = tau(k * dt), kv = (tk * v.v_0) ** 2 / Hv0;
    if (tk <= 0 || Cp <= 0) { Vn[n] = 0; Hn[n] = B * Cp; } else { Vn[n] = 0.5 * (-kv * B + Math.sqrt((kv * B) ** 2 + 4 * kv * B * Cp)); Hn[n] = B * (Cp - Vn[n]); }
    H = Hn; V = Vn;
    t.push(k * dt); Hvalve.push(H[n]); Hmid.push(H[n >> 1]); Vres.push(V[0]);
    if (H[n] > Hmax) Hmax = H[n]; if (H[n] < Hmin) Hmin = H[n];
    const mn = N.minOf(H); if (mn < HminAll) HminAll = mn;
    if (k % every === 0) { frames.push(H.slice()); ftimes.push(k * dt); }
  }
  return { x, t, Hvalve, Hmid, Vres, frames, ftimes, Hmax, Hmin, HminAll, Hv0, dt };
}

const waterHammer = {
  id: 'water-hammer',
  title: 'Water hammer on valve closure',
  module: 2, klass: 'I', domains: ['pipeline', 'cfd'],
  keywords: ['water hammer', 'waterhammer', 'surge pressure', 'pressure surge', 'joukowsky', 'valve closure', 'pressure wave', 'method of characteristics', 'wave speed', 'transient', 'fluid transient', 'surge', 'hydraulic transient'],
  summary: 'Pressure surge when a valve closes at the end of a pipeline fed from a reservoir: wave speed with pipe elasticity, the Joukowsky pressure rise and a method-of-characteristics simulation of the transient.',
  background: [
    'When flow in a pipe is stopped suddenly, the kinetic energy of the liquid is converted to strain energy of the compressed liquid and stretched pipe wall. The disturbance travels upstream as a pressure wave at a speed set by the bulk modulus of the liquid and the hoop stiffness of the pipe. For an instantaneous stoppage the pressure rise is the product of density, wave speed and velocity change — the Joukowsky relation — and is independent of pipe length.',
    'The wave reflects from the reservoir with a change of sign and returns to the valve after the pipe period 2L/a. If the valve is still closing when the reflection arrives, the peak pressure is reduced; closure slower than the pipe period is therefore the basic means of surge control. The governing equations are hyperbolic and are solved exactly along characteristic lines dx/dt = ±a.',
  ],
  phenomena: ['Compressibility of the liquid', 'Elastic dilation of the pipe', 'Wave reflection at a reservoir and a closed end', 'Frictional attenuation'],
  laws: ['mass', 'momentum', 'hooke', 'darcy'],
  refs: ['Joukowsky, N. (1900). Über den hydraulischen Stoss in Wasserleitungsröhren. Mémoires de l’Académie Impériale des Sciences de St.-Pétersbourg, Series 8, 9(5).', 'Wylie, E. B. & Streeter, V. L. (1993). Fluid Transients in Systems. Prentice Hall.', 'Chaudhry, M. H. (2014). Applied Hydraulic Transients, 3rd ed., Springer.', 'Ghidaoui, M. S., Zhao, M., McInnis, D. A. & Axworthy, D. H. (2005). A review of water hammer theory and practice. Applied Mechanics Reviews 58, 49–76.', 'Korteweg, D. J. (1878). Ueber die Fortpflanzungsgeschwindigkeit des Schalles in elastischen Röhren. Annalen der Physik 241, 525–542.'],
  inputs: [
    inp('L', 'Pipe length', 'm', 1000, { min: 50, max: 20000, kind: 'geometry', aliases: ['length', 'pipe length', 'long'] }),
    inp('D', 'Inner diameter', 'm', 0.5, { min: 0.05, max: 3, kind: 'geometry', aliases: ['diameter', 'bore'] }),
    inp('e_w', 'Wall thickness', 'mm', 8, { min: 1, max: 50, kind: 'geometry', aliases: ['wall thickness', 'thickness'] }),
    inp('E_p', 'Young’s modulus of the pipe', 'GPa', 200, { min: 1, max: 220, kind: 'fluid', aliases: ['young modulus', 'elastic modulus', 'pipe modulus'], src: 'Carbon steel; about 3 GPa for PVC' }),
    inp('nu', 'Poisson’s ratio of the pipe', '1', 0.3, { min: 0.2, max: 0.5, kind: 'fluid', aliases: ['poisson'] }),
    inp('K_f', 'Bulk modulus of the liquid', 'GPa', 2.2, { min: 0.5, max: 3, kind: 'fluid', aliases: ['bulk modulus'], src: 'Water at 20 °C' }),
    inp('rho', 'Liquid density', 'kg/m^3', 1000, { min: 600, max: 1100, kind: 'fluid', aliases: ['density'] }),
    inp('v_0', 'Initial flow velocity', 'm/s', 1, { min: 0.1, max: 6, aliases: ['velocity', 'flow velocity', 'initial velocity'] }),
    inp('H_0', 'Reservoir head above the valve', 'm', 120, { min: 10, max: 500, aliases: ['reservoir head', 'static head', 'head'] }),
    inp('f_D', 'Darcy friction factor', '1', 0.018, { min: 0.005, max: 0.05, aliases: ['friction factor'] }),
    inp('t_c', 'Valve closure time', 's', 4, { min: 0.01, max: 120, aliases: ['closure time', 'closing time', 'valve closes'] }),
    inp('n_x', 'Number of pipe reaches', '1', 50, { min: 10, max: 400, kind: 'numerical' }),
  ],
  assumptions: [
    asm('elastic', 'The pipe wall is elastic and lowers the wave speed.', { why: 'Always true to some extent; large for plastic pipe', alt: 'The pipe is rigid: the wave travels at the speed of sound in the liquid.' }),
    asm('friction', 'Wall friction is included with a constant Darcy factor (quasi-steady).', { why: 'Attenuates the oscillation and causes line-packing', alt: 'The pipe is frictionless.' }),
    asm('gradual', 'The valve closes linearly over the stated closure time.', { why: 'Realistic actuator', alt: 'The valve closes instantaneously.' }),
    asm('anchored', 'The pipe is anchored against axial movement throughout.', { why: 'Buried or well-restrained pipe', alt: 'The pipe has expansion joints throughout, so no axial stress develops.' }),
  ],
  symbols: { a_w: ['Wave speed', 'm/s'], c_1: ['Axial-restraint factor', '1'], dp_J: ['Joukowsky pressure rise', 'Pa'], T_p: ['Pipe period 2L/a', 's'], p: ['Pressure', 'Pa'], v: ['Velocity', 'm/s'], x: ['Distance from the reservoir', 'm'], t: ['Time', 's'], p_max: ['Peak pressure at the valve', 'Pa'], sigma_h: ['Peak hoop stress', 'Pa'] },
  equations: a => [
    a.elastic ? eq('aw', 'Wave speed', 'a_w', 'sqrt((K_f/rho)/(1 + K_f*D*c_1/(E_p*e_w)))', { kind: 'law', origin: 'Korteweg (1878): mass conservation with liquid compressibility and hoop strain', needs: ['elastic'] }) : eq('aw', 'Wave speed', 'a_w', 'sqrt(K_f/rho)', { kind: 'law', origin: 'Speed of sound in the liquid' }),
    ...(a.elastic ? [a.anchored ? eq('c1', 'Restraint factor', 'c_1', '1 - nu^2', { kind: 'closure', origin: 'Pipe anchored against axial movement; Wylie & Streeter (1993)', needs: ['anchored'] }) : eq('c1', 'Restraint factor', 'c_1', '1', { kind: 'closure', origin: 'Expansion joints throughout' })] : []),
    eq('jouk', 'Joukowsky pressure rise', 'dp_J', 'rho*a_w*v_0', { kind: 'law', origin: 'Momentum balance across the wave front; Joukowsky (1900)' }),
    eq('cont', 'Continuity', 'pd(p,t)', '-rho*a_w^2*pd(v,x)', { kind: 'law', origin: 'Conservation of mass for a slightly compressible liquid in an elastic pipe' }),
    eq('mom', 'Momentum', 'pd(v,t)', a.friction ? '-pd(p,x)/rho - f_D*v*abs(v)/(2*D)' : '-pd(p,x)/rho', { kind: 'law', origin: 'Conservation of momentum' + (a.friction ? ' with Darcy–Weisbach friction' : ''), needs: a.friction ? ['friction'] : [] }),
    eq('per', 'Pipe period', 'T_p', '2*L/a_w', { kind: 'definition' }),
    eq('hoop', 'Peak hoop stress', 'sigma_h', 'p_max*D/(2*e_w)', { kind: 'law', origin: 'Thin-wall equilibrium' }),
  ],
  derivation: a => [
    { text: 'Consider a wave front moving upstream at speed a into liquid flowing at v₀, leaving stationary liquid behind. In a frame moving with the front, the momentum balance gives the pressure jump.', tex: '\\Delta p = \\rho\\,a\\,\\Delta v' },
    { text: 'Mass conservation across the front requires the incoming liquid to be stored by compression of the liquid and dilation of the pipe, which fixes the wave speed.', tex: a.elastic ? 'a = \\sqrt{\\frac{K/\\rho}{1 + \\dfrac{K D}{E e}\\,c_1}}' : 'a = \\sqrt{K/\\rho}' },
    { text: 'For small disturbances the continuity and momentum equations form a hyperbolic pair.', tex: '\\frac{\\partial p}{\\partial t} + \\rho a^2\\frac{\\partial v}{\\partial x} = 0,\\qquad \\frac{\\partial v}{\\partial t} + \\frac{1}{\\rho}\\frac{\\partial p}{\\partial x} + \\frac{f\\,v|v|}{2D} = 0' },
    { text: 'Adding and subtracting them shows that the combinations p ± ρ a v are carried unchanged (apart from friction) along the lines dx/dt = ±a. A grid with Δx = a Δt places the characteristics exactly on the nodes.', tex: '\\frac{\\mathrm{d}}{\\mathrm{d}t}\\big(p \\pm \\rho a v\\big) = \\mp\\,\\rho a\\,\\frac{f\\,v|v|}{2D}\\quad\\text{on}\\quad \\frac{\\mathrm{d}x}{\\mathrm{d}t} = \\pm a' },
    { text: 'The reflection from the reservoir returns after one pipe period. Closure faster than this produces the full Joukowsky rise.', tex: 'T_p = \\frac{2L}{a}' },
  ],
  solve(v, a) {
    const st = hammerSetup(v, a), n = Math.round(v.n_x), m = hammerMOC(v, a, st, n);
    const rg = v.rho * g, dpJ = v.rho * st.aw * v.v_0, Tp = 2 * v.L / st.aw, rapid = !a.gradual || v.t_c <= Tp;
    const pMax = rg * m.Hmax, pMin = rg * m.Hmin, p0 = rg * m.Hv0, rise = pMax - p0;
    const still = hammerMOC(v, a, st, Math.min(n, 20), 0.25, () => 1);
    const drift = N.maxOf(still.Hvalve.map(h => Math.abs(h - still.Hv0))) / v.H_0;
    const pVap = -(101325 - 2340) / rg;
    const warnings = [];
    if (st.limited) warnings.push('The stated velocity cannot be driven through this pipe by the reservoir head with the given friction factor; friction has been reduced so that the initial head at the valve is one tenth of the reservoir head.');
    if (m.HminAll < pVap) warnings.push(`The computed minimum head (${lab(m.HminAll, 'm')}) is below vapour pressure. Column separation would occur; the pressures after that instant are not reliable and the re-joining of the column can produce a larger spike.`);
    if (m.t.length >= 40001) warnings.push('The simulation was truncated at 40 000 time steps; reduce the number of reaches to cover the full duration.');
    return {
      scalars: [
        scalar('a_w', 'Wave speed', st.aw, 'm/s'), scalar('T_p', 'Pipe period 2L/a', Tp, 's'),
        scalar('closure', 'Closure classification', rapid ? 1 : 0, '1', { text: rapid ? 'Rapid (closure time not longer than the pipe period): full Joukowsky rise' : 'Slow (closure time longer than the pipe period): reflections relieve the surge' }),
        scalar('dp_J', 'Joukowsky pressure rise ρ a v₀', dpJ, 'Pa', { show: 'bar' }), scalar('dH_J', 'Joukowsky head rise a v₀/g', st.aw * v.v_0 / g, 'm'),
        scalar('p_0', 'Initial pressure at the valve (gauge)', p0, 'Pa', { show: 'bar' }), scalar('p_max', 'Peak pressure at the valve (gauge)', pMax, 'Pa', { show: 'bar' }),
        scalar('dp_max', 'Peak pressure rise at the valve', rise, 'Pa', { show: 'bar' }), scalar('ratio', 'Peak rise over Joukowsky rise', rise / dpJ, '1'),
        scalar('p_min', 'Minimum pressure at the valve (gauge)', pMin, 'Pa', { show: 'bar' }),
        scalar('sigma_h', 'Peak hoop stress in the wall', Math.max(pMax, 0) * v.D / (2 * v.e_w), 'Pa', { show: 'MPa' }),
        scalar('t_safe', 'Closure time above which the surge is relieved', Tp, 's'),
        scalar('E_k', 'Kinetic energy of the liquid column', 0.5 * v.rho * Math.PI * v.D ** 2 / 4 * v.L * v.v_0 ** 2, 'J', { show: 'kJ' }),
      ],
      series: [
        line('p-valve', 'Pressure at the valve', 'Time', 's', m.t, [{ label: 'At the valve', data: m.Hvalve.map(h => rg * h / 1e5) }, { label: 'At mid-length', data: m.Hmid.map(h => rg * h / 1e5), dash: true }], 'Gauge pressure', 'bar'),
        line('v-res', 'Velocity at the reservoir end', 'Time', 's', m.t, [{ label: 'Velocity at the reservoir', data: m.Vres }], 'Velocity', 'm/s'),
      ],
      anims: [anim('wave', 'Pressure wave along the pipe', 'Distance from the reservoir', 'm', m.x, m.frames.map(fr => fr.map(h => rg * h / 1e5)), m.ftimes, 'Gauge pressure', 'bar')],
      checks: [
        check('Steady state preserved with the valve open', drift, 1e-9, 'The initial condition is an exact fixed point of the characteristic scheme'),
        check('Courant number equals one', st.aw * m.dt / (v.L / n) - 1, 1e-12, 'Characteristics pass exactly through grid nodes'),
        check('Peak rise bounded by the Joukowsky value plus line-packing', Math.max(rise - dpJ - (p0 >= 0 ? rg * (v.H_0 - m.Hv0) : 0) - 1e-6 * dpJ, 0) / dpJ, 1e-6, 'Friction can add at most the initial friction head (line-packing) to the Joukowsky rise'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { elastic: true, friction: false, gradual: false, anchored: true }, st = hammerSetup(v, b), m = hammerMOC(v, b, st, 40, 2);
    const rigid = hammerSetup({ ...v, K_f: 2.2e9, rho: 1000 }, { ...b, elastic: false });
    // period of the valve-pressure oscillation: first return to the initial head after the first rise is at 2L/a
    const iDrop = m.Hvalve.findIndex((h, i) => i > 1 && h < m.Hv0 - 1e-6);
    return [
      bench('Peak rise for instantaneous frictionless closure vs Joukowsky', v.rho * g * (m.Hmax - m.Hv0), v.rho * st.aw * v.v_0, 'Δp = ρ a Δv', 1e-9),
      bench('Minimum for instantaneous frictionless closure', v.rho * g * (m.Hmin - m.Hv0), -v.rho * st.aw * v.v_0, 'Reflected wave: −ρ a Δv', 1e-9),
      bench('Time at which the reflected wave reaches the valve', m.t[iDrop], 2 * v.L / st.aw, 'Pipe period 2L/a', 0.03),
      bench('Wave speed in a rigid pipe, water', rigid.aw, 1483.24, '√(K/ρ) with K = 2.2 GPa', 1e-5),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(40, 70, 110, 150, 'd-body', 4)} ${S.rect(42, 100, 106, 118, 'd-liquid', 2)} ${S.path('M42 100 L148 100', 'd-liquid-line')} ${S.text(95, 60, 'reservoir')}
      ${S.path('M150 250 L540 250', 'd-pipe')} ${S.path('M95 220 L95 250 L150 250', 'd-pipe')}
      ${S.path('M540 232 L570 268 L570 232 L540 268 Z', 'd-body')} ${S.text(555, 222, a.gradual ? `valve, closes in ${lab(v.t_c, 's')}` : 'valve, instantaneous')}
      ${S.arrow(230, 232, 300, 232)} ${S.text(265, 222, `v₀ = ${lab(v.v_0, 'm/s')}`)}
      ${S.path('M420 250 L420 200 L540 200', 'd-line d-hazard')} ${S.arrow(470, 186, 425, 186, 'd-arrow d-hazard')} ${S.text(480, 176, 'pressure wave, speed a')}
      ${S.dim(150, 300, 540, 300, `L = ${lab(v.L, 'm')},  D = ${lab(v.D * 1000, 'mm')}`)}
      ${S.dim(20, 100, 20, 250, `H₀ = ${lab(v.H_0, 'm')}`)}
    `);
  },
  experiment: {
    objective: 'Record the pressure history at a fast-closing valve on a long pipe and compare the first peak with the Joukowsky value and the oscillation period with 4L/a.',
    apparatus: ['Constant-head tank feeding a coiled or straight pipe at least 50 m long, rigidly anchored', 'Fast-acting ball or solenoid valve at the downstream end with a closure-time measurement', 'Flow-control valve and weigh tank for steady flow measurement'],
    instruments: [{ name: 'Piezoelectric or piezoresistive pressure transducers at the valve and mid-length', measures: 'Transient pressure', range: '0–40 bar', resolution: '≥ 5 kHz bandwidth, ±0.25 %' }, { name: 'High-speed data acquisition', measures: 'Pressure against time', range: '—', resolution: '≥ 10 kHz per channel' }, { name: 'Electromagnetic flow meter', measures: 'Initial velocity', range: '0–5 m/s', resolution: '±0.5 %' }, { name: 'Valve position sensor', measures: 'Closure law', range: '0–90°', resolution: '±0.5°' }],
    procedure: ['Establish steady flow and record velocity and static pressures.', 'Close the valve rapidly, logging pressure at both stations.', 'Measure the wave speed from the delay between the two transducers.', 'Compare the first pressure rise with ρ a v₀ and the oscillation period with 4L/a.', 'Repeat with progressively slower closures to show relief once the closure time exceeds 2L/a.'],
    controls: ['Bleed all air: small gas fractions lower the wave speed dramatically', 'Repeat at several initial velocities to verify proportionality'],
    signatures: ['First pressure rise proportional to initial velocity and independent of pipe length', 'Square-wave pressure trace of period 4L/a for rapid closure, decaying through friction', 'Peak falling roughly as 2L/(a t_c) for slow closure'],
    safety: ['Rate all components for the full surge pressure with margin', 'Restrain the pipe against axial thrust', 'Keep clear of the valve end during rapid closure tests'],
  },
  falsify: ['A first pressure rise for closure faster than 2L/a that differs from ρ a v₀ by more than the measurement uncertainty in an air-free, well-anchored pipe.', 'A measured wave speed that does not follow the dependence on wall thickness and modulus predicted by the Korteweg formula.'],
  alternatives: [{ name: 'Rigid-column (mass oscillation) theory', text: 'Neglects compressibility; adequate for slow transients such as surge-tank oscillations.' }, { name: 'Unsteady friction models (Zielke, Brunone)', text: 'Add frequency-dependent wall shear, reproducing the faster damping seen in experiments.' }, { name: 'Discrete vapour or gas cavity models', text: 'Allow column separation and re-joining when pressure reaches vapour pressure.' }, { name: 'Fluid–structure interaction', text: 'Couples axial pipe motion to the liquid, important for flexible or poorly restrained pipework.' }],
  hazards: [{ hazard: 'Pipe or fitting rupture', cause: 'Surge pressure above rating', mitigation: 'Slow-closing valves, surge vessels, relief valves, higher pressure class' }, { hazard: 'Pipe collapse or column separation', cause: 'Sub-atmospheric pressure on the down-surge', mitigation: 'Air-inlet valves, surge tanks' }, { hazard: 'Support failure', cause: 'Unbalanced axial thrust as the wave passes bends', mitigation: 'Anchors and restraints designed for the transient load' }],
  standards: ['ASME B31.4 (pipeline transportation systems for liquids): surge allowance', 'AWWA Manual M11 (steel pipe — a guide for design and installation)', 'EN 805 (water supply — requirements for systems and components outside buildings)', 'DNV-RP-D101 (structural analysis of piping systems)'],
  limits: 'Single uniform pipe, single-phase liquid, thin-walled linearly elastic pipe, quasi-steady friction. Column separation, entrained gas, viscoelastic pipe walls and pump or check-valve dynamics are not modelled.',
  numerics: { method: 'Method of characteristics on a fixed grid with Δx = a Δt; first-order treatment of friction', order: 1, stability: 'Courant number exactly one: no numerical dispersion or dissipation in the frictionless case', resolution: 'n_x' },
  optimise: { objective: 'dp_max', sense: 'min', vars: ['t_c'], note: 'Surge falls once the closure time exceeds the pipe period 2L/a.' },
  inverse: { series: 'p-valve', curve: 0, fit: ['E_p', 'f_D'] },
  extensions: ['Non-linear valve characteristics and two-stage closure', 'Surge vessel or relief valve at the downstream end', 'Column separation with a discrete vapour cavity model', 'Pump trip with machine characteristics'],
};

// ------------------------------------------------------------------ lid-driven cavity
// Ghia, Ghia & Shin (1982), Table I, Re = 100: u/U on the vertical centre-line.
const GHIA_Y = [1, 0.9766, 0.9688, 0.9609, 0.9531, 0.8516, 0.7344, 0.6172, 0.5, 0.4531, 0.2813, 0.1719, 0.1016, 0.0703, 0.0625, 0.0547, 0];
const GHIA_U100 = [1, 0.84123, 0.78871, 0.73722, 0.68717, 0.23151, 0.00332, -0.13641, -0.20581, -0.21090, -0.15662, -0.10150, -0.06434, -0.04775, -0.04192, -0.03717, 0];
/** Weights of the quartic through five equally spaced values, at offset s (in spacings) from the middle one. */
const lag5 = s => [(s + 1) * s * (s - 1) * (s - 2) / 24, -(s + 2) * s * (s - 1) * (s - 2) / 6, (s + 2) * (s + 1) * (s - 1) * (s - 2) / 4, -(s + 2) * (s + 1) * s * (s - 2) / 6, (s + 2) * (s + 1) * s * (s - 1) / 24];
/** Stationary point of that quartic nearest the middle value: [offset, value]. */
function quarticExtremum(f) {
  const P = s => { const w = lag5(s); return w[0] * f[0] + w[1] * f[1] + w[2] * f[2] + w[3] * f[3] + w[4] * f[4]; }, e = 1e-3; let s = 0;
  for (let it = 0; it < 8; it++) { const p0 = P(s), pp = P(s + e), pm = P(s - e), d2 = pp - 2 * p0 + pm; if (!d2) break; s = N.clamp(s - 0.5 * e * (pp - pm) / d2, -1, 1); }
  return [s, P(s)];
}
/** Quartic (5 × 5 point) interpolation of an n × n nodal field at the position (fx, fy) measured in grid spacings. */
function cavInterp(a, n, fx, fy) {
  const i = N.clamp(Math.round(fx), 2, n - 3), j = N.clamp(Math.round(fy), 2, n - 3), wx = lag5(fx - i), wy = lag5(fy - j); let s = 0;
  for (let q = 0; q < 5; q++) { const r = (j + q - 2) * n + i - 2; s += wy[q] * (wx[0] * a[r] + wx[1] * a[r + 1] + wx[2] * a[r + 2] + wx[3] * a[r + 3] + wx[4] * a[r + 4]); }
  return s;
}
/**
 * LU factors, in place and without pivoting, of a band matrix of order M and half-width b stored by rows (entry (r, c) at r(2b + 1) + b + c − r).
 * Four pivot rows are eliminated together so that each remaining row is swept once instead of four times.
 */
function bandLU(A, M, b) {
  const bw = 2 * b + 1, o = [0, 0, 0, 0], pv = [0, 0, 0, 0];
  for (let p = 0; p < M; p += 4) {
    const nb = Math.min(4, M - p);
    for (let k = 0; k < nb; k++) { // the pivot rows among themselves
      const q = p + k, qo = q * bw + b - q; o[k] = qo;
      for (let l = 0; l < k; l++) { const f = A[qo + p + l] / pv[l], lo = o[l], hi = Math.min(M - 1, p + l + b); A[qo + p + l] = f; for (let c = p + l + 1; c <= hi; c++) A[qo + c] -= f * A[lo + c]; }
      pv[k] = A[qo + q];
    }
    const o0 = o[0], o1 = o[1], o2 = o[2], o3 = o[3], c0 = p + nb, last = Math.min(M - 1, p + b), rEnd = Math.min(M - 1, p + nb - 1 + b);
    for (let r = c0; r <= rEnd; r++) {
      const ro = r * bw + b - r; let f0 = 0, f1 = 0, f2 = 0, f3 = 0;
      if (r - p <= b) { f0 = A[ro + p] / pv[0]; A[ro + p] = f0; }
      if (nb > 1 && r - p - 1 <= b) { f1 = (A[ro + p + 1] - f0 * A[o0 + p + 1]) / pv[1]; A[ro + p + 1] = f1; }
      if (nb > 2 && r - p - 2 <= b) { f2 = (A[ro + p + 2] - f0 * A[o0 + p + 2] - f1 * A[o1 + p + 2]) / pv[2]; A[ro + p + 2] = f2; }
      if (nb > 3 && r - p - 3 <= b) { f3 = (A[ro + p + 3] - f0 * A[o0 + p + 3] - f1 * A[o1 + p + 3] - f2 * A[o2 + p + 3]) / pv[3]; A[ro + p + 3] = f3; }
      if (nb === 4) {
        for (let c = c0; c <= last; c++) A[ro + c] -= f0 * A[o0 + c] + f1 * A[o1 + c] + f2 * A[o2 + c] + f3 * A[o3 + c];
        for (let c = last + 1; c <= Math.min(M - 1, p + 3 + b); c++) A[ro + c] -= (c <= p + 1 + b ? f1 * A[o1 + c] : 0) + (c <= p + 2 + b ? f2 * A[o2 + c] : 0) + f3 * A[o3 + c];
      } else for (let k = 0; k < nb; k++) { const f = k === 0 ? f0 : k === 1 ? f1 : f2, lo = o[k], hi = Math.min(M - 1, p + k + b); for (let c = c0; c <= hi; c++) A[ro + c] -= f * A[lo + c]; }
    }
  }
}
/** Solves in place with the factors from bandLU. */
function bandSolve(A, M, b, x) {
  const bw = 2 * b + 1;
  for (let p = 0; p < M; p++) { const ro = p * bw + b - p; let c = Math.max(0, p - b), s0 = 0, s1 = 0; for (; c + 1 < p; c += 2) { s0 += A[ro + c] * x[c]; s1 += A[ro + c + 1] * x[c + 1]; } if (c < p) s0 += A[ro + c] * x[c]; x[p] -= s0 + s1; }
  for (let p = M - 1; p >= 0; p--) { const ro = p * bw + b - p, hi = Math.min(M - 1, p + b); let c = p + 1, s0 = 0, s1 = 0; for (; c < hi; c += 2) { s0 += A[ro + c] * x[c]; s1 += A[ro + c + 1] * x[c + 1]; } if (c === hi) s0 += A[ro + c] * x[c]; x[p] = (x[p] - s0 - s1) / A[ro + p]; }
}
const cavLid = (n, o) => Float64Array.from({ length: n }, (_, i) => { const x = i / (n - 1); return o.uniform ? 1 : 16 * x * x * (1 - x) * (1 - x); });
/** Wall vorticity from the streamfunction (Thom or Jensen), in place. */
function cavWalls(psi, om, n, lid, thom) {
  const h = 1 / (n - 1), h2 = h * h;
  for (let i = 1; i < n - 1; i++) {
    if (thom) { om[i] = -2 * psi[n + i] / h2; om[(n - 1) * n + i] = -2 * psi[(n - 2) * n + i] / h2 - 2 * lid[i] / h; }
    else { om[i] = (-8 * psi[n + i] + psi[2 * n + i]) / (2 * h2); om[(n - 1) * n + i] = (-8 * psi[(n - 2) * n + i] + psi[(n - 3) * n + i]) / (2 * h2) - 3 * lid[i] / h; }
  }
  for (let j = 1; j < n - 1; j++) {
    if (thom) { om[j * n] = -2 * psi[j * n + 1] / h2; om[j * n + n - 1] = -2 * psi[j * n + n - 2] / h2; }
    else { om[j * n] = (-8 * psi[j * n + 1] + psi[j * n + 2]) / (2 * h2); om[j * n + n - 1] = (-8 * psi[j * n + n - 2] + psi[j * n + n - 3]) / (2 * h2); }
  }
}
/** Impulsive start: explicit march of the vorticity equation with over-relaxation of the streamfunction equation. */
function cavityMarch(Re, n, o) {
  const h = 1 / (n - 1), h2 = h * h, psi = new Float64Array(n * n), om = new Float64Array(n * n), on = new Float64Array(n * n), lid = cavLid(n, o);
  const dt = o.central ? 0.8 * Math.min(Re * h2 / 4, 2 / Re) : 0.8 / (4 / (Re * h2) + 2 / h);
  const maxSteps = Math.min(Math.ceil(o.tStop / dt), 6000), w = 2 / (1 + Math.sin(Math.PI * h));
  let steps = 0, change = Infinity;
  for (; steps < maxSteps; steps++) {
    cavWalls(psi, om, n, lid, o.thom); change = 0;
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) {
      const k = j * n + i, u = (psi[k + n] - psi[k - n]) / (2 * h), v = -(psi[k + 1] - psi[k - 1]) / (2 * h);
      const conv = o.central ? u * (om[k + 1] - om[k - 1]) / (2 * h) + v * (om[k + n] - om[k - n]) / (2 * h)
        : (u > 0 ? u * (om[k] - om[k - 1]) : u * (om[k + 1] - om[k])) / h + (v > 0 ? v * (om[k] - om[k - n]) : v * (om[k + n] - om[k])) / h;
      const d = dt * (-conv + (om[k + 1] + om[k - 1] + om[k + n] + om[k - n] - 4 * om[k]) / (Re * h2));
      on[k] = om[k] + d; if (Math.abs(d) > change) change = Math.abs(d);
    }
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) om[j * n + i] = on[j * n + i];
    for (let s = 0; s < 4; s++) for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) { const k = j * n + i; psi[k] += w * (0.25 * (psi[k + 1] + psi[k - 1] + psi[k + n] + psi[k - n] + h2 * om[k]) - psi[k]); }
    if (!Number.isFinite(change)) break;
  }
  return { psi, om, steps, converged: true, change: change / dt, finite: Number.isFinite(change) };
}
/**
 * Steady state by Newton's method. The interior vorticity −∇²ψ and the wall vorticity are linear in the interior streamfunction, so the vorticity
 * equation is a system in ψ alone with a band of half-width 2(n − 2), factorised directly. A Jacobian is kept while the corrections still contract quickly.
 */
function cavitySteady(Re, n, o, guess) {
  const m = n - 2, h = 1 / (n - 1), h2 = h * h, M = m * m, b = 2 * m, bw = 2 * b + 1, d = 1 / (Re * h2), lid = cavLid(n, o);
  const psi = guess || new Float64Array(n * n), om = new Float64Array(n * n), R = new Float64Array(M), A = new Float64Array(M * bw), x = new Float64Array(M);
  const inner = (i, j) => i > 0 && i < n - 1 && j > 0 && j < n - 1, id = (i, j) => (j - 1) * m + i - 1;
  // dependence of the vorticity at node (i, j) on the interior streamfunction: f(i', j', coefficient)
  const dOm = (i, j, f) => {
    if (inner(i, j)) { f(i, j, 4 / h2); f(i + 1, j, -1 / h2); f(i - 1, j, -1 / h2); f(i, j + 1, -1 / h2); f(i, j - 1, -1 / h2); return; }
    const di = i === 0 ? 1 : i === n - 1 ? -1 : 0, dj = j === 0 ? 1 : j === n - 1 ? -1 : 0;
    if (o.thom) f(i + di, j + dj, -2 / h2); else { f(i + di, j + dj, -4 / h2); f(i + 2 * di, j + 2 * dj, 0.5 / h2); }
  };
  const residual = () => {
    cavWalls(psi, om, n, lid, o.thom); let r = 0;
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) { const k = j * n + i; om[k] = -(psi[k + 1] + psi[k - 1] + psi[k + n] + psi[k - n] - 4 * psi[k]) / h2; }
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) {
      const k = j * n + i, u = (psi[k + n] - psi[k - n]) / (2 * h), v = -(psi[k + 1] - psi[k - 1]) / (2 * h);
      const conv = o.central ? u * (om[k + 1] - om[k - 1]) / (2 * h) + v * (om[k + n] - om[k - n]) / (2 * h)
        : (u > 0 ? u * (om[k] - om[k - 1]) : u * (om[k + 1] - om[k])) / h + (v > 0 ? v * (om[k] - om[k - n]) : v * (om[k + n] - om[k])) / h;
      const q = d * (om[k + 1] + om[k - 1] + om[k + n] + om[k - n] - 4 * om[k]) - conv; R[id(i, j)] = q; if (Math.abs(q) > r) r = Math.abs(q);
    }
    return r;
  };
  const jacobian = () => {
    A.fill(0);
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) {
      const k = j * n + i, p = id(i, j), row = p * bw + b - p, u = (psi[k + n] - psi[k - n]) / (2 * h), v = -(psi[k + 1] - psi[k - 1]) / (2 * h);
      const addPsi = (a, c, w) => { if (inner(a, c)) A[row + id(a, c)] += w; }, addOm = (a, c, w) => dOm(a, c, (a2, c2, w2) => addPsi(a2, c2, w * w2));
      let cE, cW, cN, cS, cP = 0, gx, gy;
      if (o.central) { cE = -u / (2 * h); cW = -cE; cN = -v / (2 * h); cS = -cN; gx = (om[k + 1] - om[k - 1]) / (2 * h); gy = (om[k + n] - om[k - n]) / (2 * h); }
      else { cE = u > 0 ? 0 : -u / h; cW = u > 0 ? u / h : 0; cN = v > 0 ? 0 : -v / h; cS = v > 0 ? v / h : 0; cP = -(Math.abs(u) + Math.abs(v)) / h; gx = (u > 0 ? om[k] - om[k - 1] : om[k + 1] - om[k]) / h; gy = (v > 0 ? om[k] - om[k - n] : om[k + n] - om[k]) / h; }
      addPsi(i, j + 1, -gx / (2 * h)); addPsi(i, j - 1, gx / (2 * h)); addPsi(i + 1, j, gy / (2 * h)); addPsi(i - 1, j, -gy / (2 * h));
      addOm(i + 1, j, d + cE); addOm(i - 1, j, d + cW); addOm(i, j + 1, d + cN); addOm(i, j - 1, d + cS); addOm(i, j, cP - 4 * d);
    }
    bandLU(A, M, b);
  };
  let its = 0, dmax = Infinity, prev = Infinity, fresh = false, res = residual();
  for (; its < 40 && dmax > 1e-11; its++) {
    if (!fresh) { jacobian(); fresh = true; }
    for (let p = 0; p < M; p++) x[p] = -R[p];
    bandSolve(A, M, b, x);
    prev = dmax; dmax = 0;
    for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) { const q = x[id(i, j)]; psi[j * n + i] += q; if (Math.abs(q) > dmax) dmax = Math.abs(q); }
    if (!(dmax < 1e3)) break;
    res = residual(); if (!(dmax < 2e-2 && dmax < 0.25 * prev)) fresh = false;
  }
  let omax = 1e-30; for (let k = 0; k < n * n; k++) omax = Math.max(omax, Math.abs(om[k]));
  return { psi, om, steps: its, converged: dmax <= 1e-11, change: dmax, resN: res / (d * omax), finite: dmax < 1e3 };
}
/** Velocities u = ∂ψ/∂y and v = −∂ψ/∂x by fourth-order differences: central, one-sided next to a wall. */
function cavVelocity(psi, n, lid) {
  const h = 1 / (n - 1), u = new Float64Array(n * n), v = new Float64Array(n * n);
  const dif = (k, st, q) => (q === 1 ? -3 * psi[k - st] - 10 * psi[k] + 18 * psi[k + st] - 6 * psi[k + 2 * st] + psi[k + 3 * st] : q === n - 2 ? 3 * psi[k + st] + 10 * psi[k] - 18 * psi[k - st] + 6 * psi[k - 2 * st] - psi[k - 3 * st] : 8 * (psi[k + st] - psi[k - st]) - (psi[k + 2 * st] - psi[k - 2 * st])) / (12 * h);
  for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) { const k = j * n + i; u[k] = dif(k, n, j); v[k] = -dif(k, 1, i); }
  for (let i = 0; i < n; i++) u[(n - 1) * n + i] = lid[i];
  return [u, v];
}
/** Vortex centre and centre-line results of one grid solution, each located on the quartic through the nearest nodal values. */
function cavityResults(psi, u, v, n) {
  const h = 1 / (n - 1), mid = (n - 1) >> 1, e = 1e-3, F = (p, q) => cavInterp(psi, n, p, q);
  let kmin = 0; for (let k = 1; k < n * n; k++) if (psi[k] < psi[kmin]) kmin = k;
  // stationary point of the interpolant by Newton's method with differenced derivatives
  let xv = N.clamp(kmin % n, 2, n - 3), yv = N.clamp(Math.floor(kmin / n), 2, n - 3); const x0 = xv, y0 = yv;
  for (let it = 0; it < 8; it++) {
    const f0 = F(xv, yv), fe = F(xv + e, yv), fw = F(xv - e, yv), fn = F(xv, yv + e), fs = F(xv, yv - e), gx = (fe - fw) / (2 * e), gy = (fn - fs) / (2 * e), hxx = (fe - 2 * f0 + fw) / (e * e), hyy = (fn - 2 * f0 + fs) / (e * e);
    const hxy = (F(xv + e, yv + e) - F(xv + e, yv - e) - F(xv - e, yv + e) + F(xv - e, yv - e)) / (4 * e * e), det = hxx * hyy - hxy * hxy; if (!(Math.abs(det) > 0)) break;
    xv = N.clamp(xv - (hyy * gx - hxy * gy) / det, x0 - 1, x0 + 1); yv = N.clamp(yv - (hxx * gy - hxy * gx) / det, y0 - 1, y0 + 1);
  }
  const uc = Array.from({ length: n }, (_, j) => u[j * n + mid]), vc = Array.from({ length: n }, (_, i) => v[mid * n + i]);
  const ext = (f, sg) => { let k = 2; for (let q = 2; q < n - 2; q++) if (sg * f[q] > sg * f[k]) k = q; const [sq, fq] = quarticExtremum(f.slice(k - 2, k + 3)); return [fq, (k + sq) * h]; };
  const [umin, ymin] = ext(uc, -1), [vmax] = ext(vc, 1), [vmin] = ext(vc, -1);
  let flux = 0; for (let j = 0; j < n; j++) flux += (j === 0 || j === n - 1 ? 1 : j % 2 ? 4 : 2) * uc[j] * h / 3; // Simpson's rule
  return { uc, vc, q: { pmin: F(xv, yv), xv: xv * h, yv: yv * h, umin, ymin, vmax, vmin, flux } };
}
/**
 * Streamfunction–vorticity solution in units of the cavity size and lid speed. The steady state is solved on nested grids and Richardson-extrapolated to zero
 * grid spacing: the fields node by node, each reported result from its own values (an extremum is then unaffected by the grid-dependent shift of its position).
 * Central differences: two grids, error ∝ h². First-order upwind differences: the error is a series in h whose terms fall slowly (numerical viscosity U h/2
 * against 1/Re), so three grids (four from 51 points) remove the terms in h, h² (and h³).
 */
function cavitySolve(Re, n, o) {
  const h = 1 / (n - 1), h2 = h * h, lid = cavLid(n, o);
  let s, nc = 0, order = 0, out, info = { grids: [n], pRaw: NaN, pErr: NaN, cellC: Re * h };
  if (o.steady) {
    // nested grids: each solution starts the next; with central differences the last two have spacings in the ratio 3:4
    order = o.central ? 2 : 1;
    const ext = [...(o.central ? [0.75] : n >= 51 ? [0.48, 0.64, 0.76] : [0.64, 0.76]).map(q => 2 * Math.round(0.5 * q * (n - 1)) + 1), n], sizes = ext.slice(); nc = ext[ext.length - 2];
    if (o.central && nc >= 29) sizes.unshift(2 * Math.round(0.25 * (nc - 1)) + 1);
    const lift = (a, from, to) => { const g = new Float64Array(to * to), r = (from - 1) / (to - 1); for (let j = 1; j < to - 1; j++) for (let i = 1; i < to - 1; i++) g[j * to + i] = cavInterp(a, from, i * r, j * r); return g; };
    let c = null, steps = 0, ok = true, fin = true, resN = 0; const sols = [];
    for (const q of sizes) { c = cavitySteady(Re, q, o, c && c.finite ? lift(c.psi, c.n, q) : null); c.n = q; steps += c.steps; ok = ok && c.converged; fin = fin && c.finite; sols.push(c); }
    const E = sols.slice(-ext.length).map(q => { const [u, v] = cavVelocity(q.psi, q.n, q.n === n ? lid : cavLid(q.n, o)); resN = Math.max(resN, q.resN); return { n: q.n, psi: q.psi, u, v, t: (1 / (q.n - 1)) ** order }; });
    // Lagrange weights of the polynomial in h^order through the grids, evaluated at h = 0
    const wts = set => set.map((p, k) => set.reduce((w, q, j) => (j === k ? w : w * q.t / (q.t - p.t)), 1)), W = wts(E), top = E[E.length - 1], u = top.u, v = top.v;
    s = { ...c, u, v, steps, converged: ok, finite: fin, raw: c.psi, resN }; out = cavityResults(c.psi, u, v, n); info = { grids: ext, pRaw: out.q.pmin, pErr: NaN, cellC: Re / (ext[0] - 1) };
    if (fin) {
      const qs = E.map((p, k) => (k === E.length - 1 ? { ...out.q } : cavityResults(p.psi, p.u, p.v, p.n).q)), comb = (w, off, key) => w.reduce((t, wk, k) => t + wk * qs[k + off][key], 0);
      for (const k of Object.keys(out.q)) out.q[k] = comb(W, 0, k);
      // the same without the coarsest grid is the extrapolation of next lower order: the difference between the two estimates what is left
      if (E.length > 2) info.pErr = Math.abs(out.q.pmin - comb(wts(E.slice(1)), 1, 'pmin')) / Math.abs(out.q.pmin);
      const mix = f => { const g = new Float64Array(n * n), r = E.map(p => (p.n - 1) / (n - 1)); for (let j = 1; j < n - 1; j++) for (let i = 1; i < n - 1; i++) { const k = j * n + i; let t = W[E.length - 1] * f(top)[k]; for (let q = 0; q < E.length - 1; q++) t += W[q] * cavInterp(f(E[q]), E[q].n, i * r[q], j * r[q]); g[k] = t; } return g; };
      s.psi = mix(p => p.psi); s.u = mix(p => p.u); s.v = mix(p => p.v); for (let i = 0; i < n; i++) s.u[(n - 1) * n + i] = lid[i];
      const mid = (n - 1) >> 1; out.uc = out.uc.map((_, j) => s.u[j * n + mid]); out.vc = out.vc.map((_, i) => s.v[mid * n + i]);
    }
  } else { s = cavityMarch(Re, n, o); s.raw = s.psi; s.resN = 0; [s.u, s.v] = cavVelocity(s.psi, n, lid); out = cavityResults(s.psi, s.u, s.v, n); }
  const psi = s.psi, om = s.om, raw = s.raw, U = [], V = [], P = [], Sp = [];
  let res = 0, omax = 1e-30;
  for (let j = 0; j < n; j++) {
    const ru = new Array(n), rv = new Array(n), rp = new Array(n), rs = new Array(n);
    for (let i = 0; i < n; i++) {
      const k = j * n + i; ru[i] = s.u[k]; rv[i] = s.v[k]; rp[i] = psi[k]; rs[i] = Math.hypot(ru[i], rv[i]);
      if (i > 0 && i < n - 1 && j > 0 && j < n - 1) { res = Math.max(res, Math.abs((raw[k + 1] + raw[k - 1] + raw[k + n] + raw[k - n] - 4 * raw[k]) / h2 + om[k])); omax = Math.max(omax, Math.abs(om[k])); }
    }
    U.push(ru); V.push(rv); P.push(rp); Sp.push(rs);
  }
  // circulation theorem: the area integral of vorticity equals the line integral of velocity round the walls
  let circ = 0, lidInt = 0;
  for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) circ += om[j * n + i] * (i === 0 || i === n - 1 ? 0.5 : 1) * (j === 0 || j === n - 1 ? 0.5 : 1) * h2;
  for (let i = 0; i < n; i++) lidInt += lid[i] * (i === 0 || i === n - 1 ? 0.5 : 1) * h;
  return { n, nc, order, ...info, h, steps: s.steps, converged: s.converged, change: s.change, U, V, P, Sp, ...out.q, res: res / omax, resN: s.resN, circ, lidInt, y: N.linspace(0, 1, n), uc: out.uc, vc: out.vc, finite: s.finite };
}

const cavity = {
  id: 'lid-driven-cavity',
  title: 'Lid-driven cavity flow',
  module: 2, klass: 'I', domains: ['cfd'], heavy: true,
  keywords: ['lid-driven cavity', 'lid driven cavity', 'cavity flow', 'driven cavity', 'streamfunction', 'vorticity', 'navier-stokes', 'recirculation', 'ghia', 'cfd benchmark', 'incompressible flow', 'vortex', 'cavity'],
  summary: 'Two-dimensional incompressible flow in a square cavity driven by its sliding lid, solved in streamfunction–vorticity form by finite differences and compared with the benchmark of Ghia, Ghia and Shin.',
  background: [
    'A square cavity filled with viscous fluid whose lid slides at constant speed is the standard test problem for incompressible Navier–Stokes solvers. The geometry is trivial, the boundary conditions are simple, and yet the flow contains a primary recirculating vortex, secondary corner eddies and thin wall layers whose structure changes with Reynolds number.',
    'In two dimensions the pressure can be eliminated by writing the velocity as the curl of a streamfunction and transporting the vorticity. Continuity is then satisfied identically. The no-slip condition does not give the wall vorticity directly; it is obtained from a Taylor expansion of the streamfunction at the wall. The tabulated multigrid solutions of Ghia, Ghia and Shin (1982) on a 129 × 129 grid are the customary reference.',
  ],
  phenomena: ['Shear-driven recirculation', 'Viscous diffusion of vorticity', 'Advection of vorticity', 'Corner eddies', 'Corner singularity of a uniform lid'],
  laws: ['mass', 'momentum'],
  refs: ['Ghia, U., Ghia, K. N. & Shin, C. T. (1982). High-Re solutions for incompressible flow using the Navier–Stokes equations and a multigrid method. J. Computational Physics 48, 387–411.', 'Burggraf, O. R. (1966). Analytical and numerical studies of the structure of steady separated flows. J. Fluid Mechanics 24, 113–151.', 'Thom, A. (1933). The flow past circular cylinders at low speeds. Proc. Royal Society A 141, 651–669.', 'Roache, P. J. (1998). Fundamentals of Computational Fluid Dynamics. Hermosa Publishers.', 'Shankar, P. N. & Deshpande, M. D. (2000). Fluid mechanics in the driven cavity. Annual Review of Fluid Mechanics 32, 93–136.'],
  inputs: [
    inp('Re', 'Reynolds number U L/ν', '1', 100, { min: 10, max: 400, aliases: ['reynolds number', 'reynolds', 're'] }),
    inp('L', 'Cavity side length', 'm', 0.1, { min: 0.001, max: 10, kind: 'geometry', aliases: ['cavity size', 'side length', 'side', 'size'] }),
    inp('U_l', 'Lid speed', 'm/s', 0.01, { min: 1e-4, max: 10, aliases: ['lid speed', 'lid velocity', 'wall speed'] }),
    inp('n_g', 'Grid points per side', '1', 51, { min: 21, max: 81, kind: 'numerical' }),
  ],
  assumptions: [
    asm('steady', 'The flow is steady: the steady equations are solved directly.', { why: 'The steady solution is unique and stable at these Reynolds numbers', alt: 'The impulsively started flow is shown after two lid-transit times L/U, on the single grid chosen and without extrapolation.' }),
    asm('central', 'Advection of vorticity uses second-order central differences.', { why: 'Accurate while the cell Reynolds number is moderate', alt: 'First-order upwind differences are used: unconditionally bounded but numerically diffusive on any single grid. The steady result is extrapolated to zero grid spacing through three or four nested grids, which removes that error while the cell Reynolds number is moderate.' }),
    asm('thom', 'Wall vorticity is given by Thom’s first-order formula.', { why: 'Robust and widely used', alt: 'Jensen’s second-order formula, using two interior points, is used.' }),
    asm('uniform', 'The lid moves at uniform speed right into the corners.', { why: 'The classical problem, with singular corners', alt: 'The lid speed is regularised to 16 x²(1 − x)² so that it vanishes smoothly at the corners.' }),
  ],
  symbols: { psi: ['Streamfunction', 'm^2/s'], omega: ['Vorticity', '1/s'], u: ['Horizontal velocity', 'm/s'], v: ['Vertical velocity', 'm/s'], nu: ['Kinematic viscosity', 'm^2/s'], x: ['Horizontal coordinate', 'm'], y: ['Vertical coordinate', 'm'], t: ['Time', 's'], h_g: ['Grid spacing', 'm'], psi_1: ['Streamfunction one node in from the wall', 'm^2/s'], psi_2: ['Streamfunction two nodes in from the wall', 'm^2/s'], omega_w: ['Wall vorticity', '1/s'], U_w: ['Tangential wall speed', 'm/s'] },
  equations: a => [
    eq('re', 'Reynolds number', 'Re', 'U_l*L/nu', { kind: 'definition' }),
    eq('u', 'Horizontal velocity', 'u', 'pd(psi,y)', { kind: 'definition', origin: 'Streamfunction: continuity satisfied identically' }),
    eq('v', 'Vertical velocity', 'v', '-pd(psi,x)', { kind: 'definition', origin: 'Streamfunction: continuity satisfied identically' }),
    eq('poisson', 'Streamfunction equation', 'lap(psi)', '-omega', { kind: 'law', origin: 'Definition of vorticity' }),
    eq('vort', 'Vorticity transport', a.steady ? 'u*pd(omega,x) + v*pd(omega,y)' : 'pd(omega,t) + u*pd(omega,x) + v*pd(omega,y)', 'nu*lap(omega)', { kind: 'law', origin: 'Curl of the Navier–Stokes momentum equation in two dimensions', needs: a.steady ? ['steady'] : [] }),
    a.thom ? eq('wall', 'Wall vorticity', 'omega_w', '-2*psi_1/h_g^2 - 2*U_w/h_g', { kind: 'boundary', origin: 'Thom (1933): Taylor expansion of ψ at a no-slip wall', needs: ['thom'] }) : eq('wall', 'Wall vorticity', 'omega_w', '(psi_2 - 8*psi_1)/(2*h_g^2) - 3*U_w/h_g', { kind: 'boundary', origin: 'Jensen’s second-order wall formula' }),
  ],
  derivation: a => [
    { text: 'For incompressible flow in a plane, define a streamfunction whose derivatives give the velocity components; continuity is then automatically satisfied.', tex: 'u = \\frac{\\partial\\psi}{\\partial y},\\qquad v = -\\frac{\\partial\\psi}{\\partial x}' },
    { text: 'The vorticity is the curl of the velocity, which gives a Poisson equation linking the two fields.', tex: '\\omega = \\frac{\\partial v}{\\partial x} - \\frac{\\partial u}{\\partial y} \;\\Rightarrow\; \\nabla^2\\psi = -\\omega' },
    { text: 'Taking the curl of the momentum equation eliminates pressure and leaves an advection–diffusion equation for vorticity.', tex: '\\frac{\\partial\\omega}{\\partial t} + u\\frac{\\partial\\omega}{\\partial x} + v\\frac{\\partial\\omega}{\\partial y} = \\nu\\,\\nabla^2\\omega' },
    { text: 'On a wall ψ is constant and its normal derivative equals the wall speed. Expanding ψ to second order one grid spacing into the fluid gives the wall vorticity.', tex: '\\omega_w = -\\frac{2\\,\\psi_1}{h^2} - \\frac{2\\,U_w}{h}' },
    { text: 'Scaling lengths by L and velocities by U leaves the Reynolds number as the only parameter.', tex: '\\mathrm{Re} = \\frac{U L}{\\nu}' },
    ...(a.steady ? [a.central
      ? { text: 'The difference equations are second-order accurate, so the steady solutions on two grids of spacing h and H > h differ from the exact one by terms proportional to h² and H². Eliminating that term between the two (Richardson extrapolation) removes the leading discretisation error from the reported field.', tex: '\\psi \\approx \\psi_h + \\frac{\\psi_h - \\psi_H}{(H/h)^2 - 1}' }
      : { text: 'First-order upwind differences behave like central differences with an added numerical viscosity of order U h/2, which is not small beside 1/Re on these grids: the error is a series in h whose first terms are all significant. The steady solutions on three or four nested grids are therefore fitted by a polynomial in h, whose value at h = 0 is reported (Richardson extrapolation of order two or three).', tex: '\\psi \\approx \\sum_k w_k\\,\\psi_{h_k},\\qquad w_k = \\prod_{j \\ne k}\\frac{h_j}{h_j - h_k}' }] : []),
  ],
  solve(v, a) {
    const n = Math.max(11, Math.round(v.n_g)) | 1, c = cavitySolve(v.Re, n, { ...a, tStop: 2 });
    const nu = v.U_l * v.L / v.Re, cellRe = v.Re * c.h;
    const near100 = Math.abs(v.Re - 100) < 0.5 && a.steady && a.uniform;
    const vmax = c.vmax, vmin = c.vmin, xs = N.linspace(0, 1, n);
    const warnings = [];
    if (!c.finite) warnings.push('The iteration diverged. Use upwind differencing or a finer grid at this Reynolds number.');
    if (a.steady && c.finite && !c.converged) warnings.push(`Newton's method had not converged on the steady state after ${c.steps} iterations (last correction ${lab(c.change)}); treat the result as approximate.`);
    if (a.central && cellRe > 4) warnings.push(`The cell Reynolds number is ${lab(cellRe)}; central differencing can produce grid-scale oscillations above about 2–4. Refine the grid or switch to upwind differencing.`);
    if (!a.central && a.steady && c.finite) {
      warnings.push(`First-order upwind differencing adds numerical viscosity of order U h/2: on the ${n} × ${n} grid alone the streamfunction at the vortex centre is ${c.pRaw.toFixed(4)}, ${lab(Math.abs(c.pRaw / c.pmin - 1) * 100, '%')} from the value ${c.pmin.toFixed(4)} obtained by extrapolating through the ${c.grids.length} nested grids to zero spacing.`);
      if (c.cellC > 10) warnings.push(`The cell Reynolds number on the coarsest grid of the extrapolation is ${lab(c.cellC)}. Above about 10 the upwind error no longer falls as a low-order polynomial in the grid spacing, so the extrapolated results are indicative only (the two highest orders of extrapolation differ by ${lab(c.pErr * 100, '%')} in the streamfunction; errors of a few per cent in the centre-line velocities are typical). Use more grid points or central differences.`);
    } else if (!a.central) warnings.push('First-order upwind differencing adds numerical viscosity of order U h/2; the vortex is weaker than in the central-difference solution.');
    const safe = q => (Number.isFinite(q) ? q : 0);
    return {
      scalars: [
        scalar('nu', 'Kinematic viscosity implied by the Reynolds number', nu, 'm^2/s'), scalar('psi_min', 'Streamfunction at the primary vortex centre, ψ/(U L)', safe(c.pmin), '1'),
        ...(a.steady ? [scalar('psi_raw', 'Streamfunction at the vortex centre on the finest grid alone, before extrapolation', safe(c.pRaw), '1', { note: a.central ? undefined : 'weakened by the numerical viscosity of upwind differencing' })] : []),
        ...(a.steady && Number.isFinite(c.pErr) ? [scalar('psi_err', 'Estimated relative error of the extrapolated streamfunction (difference between the two highest orders of extrapolation over the grids)', c.pErr, '1', { show: '%' })] : []),
        scalar('psi_dim', 'Circulating flow per unit depth in the primary vortex', safe(-c.pmin) * v.U_l * v.L, 'm^2/s'),
        scalar('x_v', 'Vortex centre x/L', c.xv, '1'), scalar('y_v', 'Vortex centre y/L', c.yv, '1'),
        scalar('u_min', 'Minimum u/U on the vertical centre-line', safe(c.umin), '1'), scalar('y_umin', 'Height y/L of that minimum', safe(c.ymin), '1'),
        scalar('v_max', 'Maximum v/U on the horizontal centre-line', safe(vmax), '1'), scalar('v_min', 'Minimum v/U on the horizontal centre-line', safe(vmin), '1'),
        scalar('u_ret', 'Peak return-flow speed', safe(-c.umin) * v.U_l, 'm/s'), scalar('t_visc', 'Viscous time L²/ν', v.L ** 2 / nu, 's'),
        scalar('Re_cell', 'Cell Reynolds number', cellRe, '1'), scalar('steps', a.steady ? 'Newton iterations, all grids' : 'Time steps taken', c.steps, '1'), scalar('res', a.steady ? 'Residual of the steady vorticity equation over its largest viscous term' : 'Residual of the streamfunction equation over peak vorticity', safe(a.steady ? c.resN : c.res), '1'),
      ],
      series: [
        line('u-centre', 'Horizontal velocity on the vertical centre-line', 'u/U', '–', c.uc.map(safe), [{ label: 'This solution', data: c.y }], 'y/L', '–', { overlay: near100 ? [{ label: 'Ghia, Ghia & Shin (1982), Re = 100', x: GHIA_U100, y: GHIA_Y, kind: 'scatter' }] : [] }),
        line('v-centre', 'Vertical velocity on the horizontal centre-line', 'x/L', '–', xs, [{ label: 'v/U', data: c.vc.map(safe) }], 'v/U', '–'),
      ],
      fields: [
        field('psi', 'Streamfunction ψ/(U L)', c.P, [0, 1, 0, 1], 'x/L', 'y/L', '–', { vectors: { u: c.U, v: c.V } }),
        field('speed', 'Speed |u|/U', c.Sp, [0, 1, 0, 1], 'x/L', 'y/L', '–', { vectors: { u: c.U, v: c.V } }),
      ],
      checks: [
        check('Mass conservation across the vertical centre-line', safe(c.flux), 2e-3, '∫u dy = 0: no net flow across any section of a closed cavity (Simpson\'s rule on the centre-line profile)'),
        check('Circulation theorem', a.steady ? safe(c.circ + c.lidInt) / c.lidInt : 0, 0.08, '∬ω dA = −∫U dx along the lid, on the finer grid; first-order wall vorticity limits the accuracy'),
        check('Residual of the steady equations', a.steady ? safe(c.resN) : 0, 1e-6, 'Vorticity-transport residual of both grid solutions, relative to the largest viscous term'),
      ],
      warnings,
      notes: a.steady && c.finite ? [`The fields and results are Richardson-extrapolated (${a.central ? 'order 2' : `polynomial of degree ${c.grids.length - 1} in the grid spacing`}) from the steady solutions on ${c.grids.map(q => `${q} × ${q}`).join(', ').replace(/, ([^,]*)$/, ' and $1')} grids.`] : [],
    };
  },
  benchmarks(v, a) {
    const base = { steady: true, central: true, thom: true, uniform: true };
    const c = cavitySolve(100, 41, base), c4 = cavitySolve(400, 41, base), st = cavitySolve(1e-6, 21, base);
    const rms = Math.sqrt(N.mean(GHIA_Y.map((y, k) => (N.interp1(c.y, c.uc, y) - GHIA_U100[k]) ** 2)));
    return [
      bench('Minimum centre-line velocity at Re = 100 vs published benchmark', c.umin, -0.2109, 'Ghia, Ghia & Shin (1982), 129 × 129 multigrid solution; their tabulated point nearest the minimum', 0.03),
      bench('Centre-line velocity profile at Re = 100 vs published benchmark', 1 + rms, 1, 'Root-mean-square difference in u/U over the 17 points tabulated by Ghia, Ghia & Shin (1982)', 5e-3),
      bench('Primary-vortex streamfunction at Re = 100 vs published benchmark', c.pmin, -0.103423, 'Ghia, Ghia & Shin (1982)', 0.01),
      bench('Primary-vortex streamfunction at Re = 400 vs published benchmark', c4.pmin, -0.113909, 'Ghia, Ghia & Shin (1982)', 0.01),
      bench('Left–right symmetry of creeping flow', st.xv, 0.5, 'Stokes flow is reversible, so the vortex lies on the vertical centre-line', 1e-7),
      bench('Net flow across the centre-line', c.flux + 1, 1, 'Continuity in a closed cavity', 1e-3),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(200, 70, 240, 240, 'd-liquid', 0)} ${S.path('M200 70 L200 310 L440 310 L440 70', 'd-ground')}
      ${S.line(190, 70, 450, 70, 'd-pipe')} ${S.arrow(250, 52, 390, 52)} ${S.text(320, 40, `lid, U = ${lab(v.U_l, 'm/s')}`)}
      ${S.path('M320 120 Q410 130 400 200 Q390 270 320 265 Q250 260 245 195 Q240 125 320 120', 'd-line')} ${S.arrow(330, 120, 350, 122)}
      ${S.path('M410 290 Q425 285 428 270', 'd-line')} ${S.path('M228 292 Q215 286 212 274', 'd-line')}
      ${S.text(320, 198, 'primary vortex')} ${S.dim(200, 335, 440, 335, `L = ${lab(v.L, 'm')}`)}
      ${S.text(540, 190, `Re = ${lab(v.Re)}`)} ${S.text(540, 212, `${Math.round(v.n_g)} × ${Math.round(v.n_g)} grid`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the velocity field in a lid-driven cavity at a known Reynolds number and compare centre-line profiles with the computation.',
    apparatus: ['Transparent square cavity with a large spanwise aspect ratio (at least 3:1) to approximate two-dimensional flow at mid-span', 'Lid formed by a belt or rotating cylinder of large radius driven at constant speed', 'Working fluid of known viscosity (water–glycerol mixture) seeded with tracer particles', 'Temperature control to hold viscosity constant'],
    instruments: [{ name: 'Planar particle-image velocimetry system', measures: 'Two-component velocity field in the mid-plane', range: '0–0.5 m/s', resolution: '±1 % of lid speed' }, { name: 'Belt-speed encoder', measures: 'Lid velocity', range: '0–1 m/s', resolution: '±0.2 %' }, { name: 'Viscometer and thermometer', measures: 'Fluid viscosity', range: '1–1000 mPa·s', resolution: '±1 %' }],
    procedure: ['Set the belt speed for the target Reynolds number and wait at least one viscous time L²/ν.', 'Acquire several hundred image pairs in the mid-plane and average.', 'Extract u along the vertical centre-line and v along the horizontal centre-line.', 'Locate the vortex centre and compare with the computed position.', 'Repeat at several Reynolds numbers.'],
    controls: ['Measurements at two spanwise planes to quantify end-wall effects', 'Reversal of belt direction to check symmetry of the apparatus'],
    signatures: ['A single primary vortex displaced toward the downstream upper corner as Reynolds number rises', 'Corner eddies at the bottom', 'Centre-line minimum of u near −0.21 U at Re = 100'],
    safety: ['Guard moving belts and pulleys', 'Laser safety controls for particle-image velocimetry', 'Glycerol spills are slippery'],
  },
  falsify: ['Measured mid-plane centre-line velocities in a cavity of large span that differ from the converged two-dimensional solution by more than the measurement uncertainty at Reynolds numbers below a few hundred.', 'A net flow across the cavity centre-line.'],
  alternatives: [{ name: 'Primitive-variable (pressure–velocity) solvers', text: 'Projection or SIMPLE-type methods extend to three dimensions, where the streamfunction formulation does not.' }, { name: 'Lattice-Boltzmann methods', text: 'Recover the same solution from a kinetic model and parallelise readily.' }, { name: 'Three-dimensional cavity', text: 'End walls generate spanwise flow and Taylor–Görtler-like vortices; the two-dimensional solution becomes unstable near Re ≈ 800–1000 in practice.' }],
  hazards: [{ hazard: 'Misuse of an under-resolved solution', cause: 'Coarse grid or high cell Reynolds number', mitigation: 'Grid-refinement study; compare with benchmark data' }],
  standards: ['ASME V&V 20 (verification and validation in computational fluid dynamics and heat transfer)', 'AIAA G-077 (guide for the verification and validation of computational fluid dynamics simulations)', 'ERCOFTAC Best Practice Guidelines for industrial CFD'],
  limits: 'Two-dimensional, laminar, incompressible, Newtonian flow in a square cavity at Reynolds numbers from 10 to 400 on grids up to 81 × 81. Higher Reynolds numbers need finer grids than is practical here. The extrapolation to zero grid spacing assumes that all the grids resolve the flow; with first-order upwind differences that requires a cell Reynolds number on the coarsest grid below about 10, beyond which the extrapolated results carry errors of a few per cent. The lid corners of a uniform lid remain singular.',
  numerics: { method: 'Steady state: Newton iteration on the streamfunction–vorticity difference equations with a direct banded solve, on nested grids that are Richardson-extrapolated to zero grid spacing (central differences: two grids with spacings 3:4, error ∝ h²; upwind differences: three grids, or four from 51 points per side, removing the terms in h, h² and h³). Impulsive start: explicit marching of the vorticity equation with successive over-relaxation of the streamfunction equation', order: 2, stability: 'Newton iteration converges quadratically from the coarser-grid solution; the explicit march is limited by the diffusive and advective limits of the forward-time central-space scheme', resolution: 'n_g' },
  inverse: { series: 'u-centre', curve: 0, fit: ['Re'] },
  extensions: ['Higher Reynolds numbers with a multigrid Poisson solver', 'Rectangular and deep cavities with a sequence of counter-rotating eddies', 'Heat transfer with a heated lid (mixed convection)', 'Fourth-order compact differencing and subtraction of the corner singularities'],
};

// ------------------------------------------------------------------ viscous Burgers equation
/**
 * Cell faces on [0, L] for a shock layer of thickness δ centred on xc: n/200 cells per δ within 5δ of xc, growing geometrically beyond (doubling
 * every 2.5δ) up to a uniform outer size chosen so that there are exactly n cells. Uniform when a uniform grid is already that fine.
 */
function burgersGrid(n, L, xc, delta) {
  const hm = 200 * delta / n, uni = N.linspace(0, L, n + 1); if (!(hm > 0 && hm < L / n)) return uni;
  const W = 5 * delta, lam = 2.5 * delta, cW = W / hm, k = lam / hm;
  const cnt = (d, H) => { const d1 = W + lam * (H / hm - 1); return d <= W ? d / hm : d <= d1 ? cW + k * Math.log(1 + (d - W) / lam) : cW + k * Math.log(H / hm) + (d - d1) / H; };
  const H = N.bisect(q => cnt(xc, q) + cnt(L - xc, q) - n, hm, L, 1e-14 * L), cL = cnt(xc, H), c1 = cW + k * Math.log(H / hm), d1 = W + lam * (H / hm - 1), tot = cL + cnt(L - xc, H);
  return uni.map((_, i) => { const t = -cL + i * tot / n, q = Math.abs(t); return i === 0 ? 0 : i === n ? L : xc + Math.sign(t) * (q <= cW ? q * hm : q <= c1 ? W + lam * (Math.exp((q - cW) / k) - 1) : d1 + (q - c1) * H); });
}
/**
 * Finite-volume solution of u_t + (u²/2)_x = ν u_xx on the cells between the faces xf (uniform over [0, L] with n − 1 cells by default), seen from a frame moving at speed w.
 * Conservative form: MUSCL–Hancock scheme (piecewise-linear reconstruction with the monotonised-central limiter, face states advanced half a step, Godunov or
 * Lax–Friedrichs flux) with the central viscous flux at the old time level. Otherwise the advective form u ∂u/∂x with the same reconstruction, upwinded on the cell's own velocity.
 */
function burgersRun({ n, L, xf = N.linspace(0, L, n), nu, tEnd, u0, periodic, uL, uR, flux, conservative, w = 0, frames = 60, maxSteps = 20000 }) {
  const m = xf.length - 1, x = new Float64Array(m), dx = new Float64Array(m + 2), dc = new Float64Array(m + 1), rx = new Float64Array(m + 2), rc = new Float64Array(m + 1), r2 = new Float64Array(m + 2);
  for (let i = 0; i < m; i++) { x[i] = 0.5 * (xf[i] + xf[i + 1]); dx[i + 1] = xf[i + 1] - xf[i]; }
  dx[0] = periodic ? dx[m] : dx[1]; dx[m + 1] = periodic ? dx[1] : dx[m];
  for (let f = 0; f <= m; f++) { dc[f] = 0.5 * (dx[f] + dx[f + 1]); rc[f] = 1 / dc[f]; } for (let i = 1; i <= m; i++) { rx[i] = 1 / dx[i]; r2[i] = 1 / (dc[i - 1] + dc[i]); }
  // cells 1..m, with ghost cells 0 and m + 1; pl and pr are the states at the left and right faces of each cell
  let u = new Float64Array(m + 2), u1 = new Float64Array(m + 2); const pl = new Float64Array(m + 2), pr = new Float64Array(m + 2), F = new Float64Array(m + 1); for (let i = 0; i < m; i++) u[i + 1] = u0(x[i]);
  let um = periodic ? 0 : Math.max(Math.abs(uL - w), Math.abs(uR - w)), rate = 0, dxMin = Infinity; for (let i = 1; i <= m; i++) { um = Math.max(um, Math.abs(u[i] - w)); dxMin = Math.min(dxMin, dx[i]); }
  for (let i = 1; i <= m; i++) rate = Math.max(rate, 2 * um / dx[i] + 2 * nu / (dx[i] * Math.min(dc[i - 1], dc[i])));
  // Lax–Friedrichs dissipation Δx/(4Δt) uses half of the explicit diffusion limit on the smallest cell, so the viscous term may take 0.4 of it at most
  const god = flux === 'godunov' || !conservative, dt0 = god ? 0.9 / rate : 0.9 * Math.min(0.5 * dxMin / um, nu > 0 ? 0.225 * dxMin * dxMin / nu : Infinity), nt = Math.min(Math.max(1, Math.ceil(tEnd / dt0)), maxSteps), dt = Math.min(tEnd / nt, dt0), alf = 0.25 * dxMin / dt;
  const step = (a, b) => {
    a[0] = periodic ? a[m] : uL; a[m + 1] = periodic ? a[1] : uR;
    for (let i = 1; i <= m; i++) {
      const sm = (a[i] - a[i - 1]) * rc[i - 1], sp = (a[i + 1] - a[i]) * rc[i]; let h = 0;
      if (sm * sp > 0) { const c = Math.abs(a[i + 1] - a[i - 1]) * r2[i], q = 2 * Math.min(Math.abs(sm), Math.abs(sp)); h = 0.5 * dx[i] * (sm > 0 ? 1 : -1) * (c < q ? c : q); }
      const lo = a[i] - h, hi = a[i] + h, e = 0.5 * dt * rx[i] * (conservative ? hi * (0.5 * hi - w) - lo * (0.5 * lo - w) : (a[i] - w) * (hi - lo)); pl[i] = lo - e; pr[i] = hi - e;
    }
    pr[0] = periodic ? pr[m] : uL; pl[m + 1] = periodic ? pl[1] : uR;
    // advective form: the cell's own velocity at the half step times the upwind difference of the face states. Second order where the solution is
    // smooth, but not a difference of fluxes, so nothing is conserved across a jump
    if (!conservative) { for (let i = 1; i <= m; i++) { const c = 0.5 * (pl[i] + pr[i]) - w; b[i] = a[i] + dt * rx[i] * (nu * ((a[i + 1] - a[i]) * rc[i] - (a[i] - a[i - 1]) * rc[i - 1]) - c * (c > 0 ? pr[i] - pr[i - 1] : pl[i + 1] - pl[i])); } return; }
    for (let f = 0; f <= m; f++) {
      const p = pr[f], q = pl[f + 1]; let adv;
      if (god) { const us = p > q ? (0.5 * (p + q) > w ? p : q) : p > w ? p : q < w ? q : w; adv = us * (0.5 * us - w); } else adv = 0.25 * (p * p + q * q) - 0.5 * w * (p + q) - alf * (q - p);
      F[f] = adv - nu * (a[f + 1] - a[f]) * rc[f];
    }
    for (let i = 1; i <= m; i++) b[i] = a[i] - dt * rx[i] * (F[i] - F[i - 1]);
  };
  // steepest gradient: fourth-order difference where the grid is locally uniform, then the vertex of the parabola through the three values about the largest
  const g = f => Math.abs(f > 1 && f < m - 1 && Math.abs(dc[f - 1] - dc[f + 1]) < 1e-9 * dc[f] ? (27 * (u[f + 1] - u[f]) - (u[f + 2] - u[f - 1])) / (24 * dc[f]) : (u[f + 1] - u[f]) / dc[f]);
  const grad = () => { let k = 1, gk = 0; for (let f = 1; f < m; f++) { const q = Math.abs(u[f + 1] - u[f]) / dc[f]; if (q > gk) { gk = q; k = f; } } if (k < 2 || k > m - 2) return gk;
    const a = g(k - 1), b = g(k), c = g(k + 1), h1 = dx[k], h2 = dx[k + 1], d1 = (b - a) / h1, d2 = (c - b) / h2, cv = 2 * (d2 - d1) / (h1 + h2), s0 = (d1 * h2 + d2 * h1) / (h1 + h2); return cv < 0 ? b - s0 * s0 / (2 * cv) : b; };
  const snaps = [], times = [], gmax = [], out = () => Array.from(u.subarray(1, m + 1)), every = Math.max(1, Math.floor(nt / frames));
  let t = 0, steps = 0;
  for (let k = 0; k <= nt; k++) {
    if (k % every === 0 || k === nt) { snaps.push(out()); times.push(t); gmax.push(grad()); }
    if (k === nt) break;
    step(u, u1); const s = u; u = u1; u1 = s; t += dt; steps++;
  }
  return { x: Array.from(x), w: Array.from(dx.subarray(1, m + 1)), snaps, times, final: out(), dx: dxMin, dt, steps, gmax, tg: times, truncated: nt * dt < tEnd * (1 - 1e-9) };
}
/** Exact Cole–Hopf solution for one period of a sine wave of amplitude U: the velocity gradient at mid-domain, where the shock stands. */
function burgersSineSlope(U, L, nu, t) {
  // u = ∫ (x − ξ)/t e^(−G/2ν) dξ / ∫ e^(−G/2ν) dξ with G = ∫₀^ξ u₀ + (x − ξ)²/2t; its x-derivative at x = L/2 is 1/t − var(ξ)/(2νt²)
  const x = L / 2, R = 7 * Math.sqrt(2 * nu * t) + U * t, nq = 8001, G = q => U * L / (2 * Math.PI) * (1 - Math.cos(2 * Math.PI * q / L)) + (x - q) ** 2 / (2 * t);
  const xs = N.linspace(x - R, x + R, nq), gs = xs.map(G), gm = N.minOf(gs); let s0 = 0, s2 = 0;
  for (let i = 0; i < nq; i++) { const wt = Math.exp(-(gs[i] - gm) / (2 * nu)); s0 += wt; s2 += wt * (x - xs[i]) ** 2; }
  return 1 / t - s2 / s0 / (2 * nu * t * t);
}
const burgersWave = (x, t, uL, uR, x0, nu) => 0.5 * (uL + uR) - 0.5 * (uL - uR) * Math.tanh((uL - uR) * (x - x0 - 0.5 * (uL + uR) * t) / (4 * nu));

const burgers = {
  id: 'burgers-shock',
  title: 'Viscous Burgers equation: steepening and shock formation',
  module: [1, 2], klass: 'I', domains: ['cfd'],
  keywords: ['burgers equation', 'burgers', 'shock formation', 'wave steepening', 'shock wave', 'nonlinear advection', 'travelling wave', 'traveling wave', 'viscous shock', 'lax-friedrichs', 'godunov', 'upwind', 'conservation law', 'shock'],
  summary: 'Nonlinear steepening of a wave into a shock under the viscous Burgers equation, solved with a conservative finite-volume scheme and compared with the exact travelling-wave solution.',
  background: [
    'The Burgers equation is the simplest model that combines nonlinear advection with diffusion. Each part of a wave travels at its own local speed, so faster fluid overtakes slower fluid and compressive parts of the profile steepen. Without viscosity the profile would become multivalued at a finite breaking time; with viscosity the steepening is arrested when the gradient is large enough for diffusion to balance advection, leaving a thin shock layer.',
    'The steady shock structure is an exact hyperbolic-tangent profile whose thickness is proportional to viscosity divided by the velocity jump, and which moves at the mean of the velocities on either side — the Rankine–Hugoniot speed. A numerical scheme reproduces that speed only if it is written in conservation form, which is why the equation is used to test shock-capturing methods.',
  ],
  phenomena: ['Nonlinear wave steepening', 'Shock formation', 'Balance of advection and diffusion in a shock layer', 'Viscous decay of energy'],
  laws: ['momentum', 'mass'],
  refs: ['Burgers, J. M. (1948). A mathematical model illustrating the theory of turbulence. Advances in Applied Mechanics 1, 171–199.', 'Hopf, E. (1950). The partial differential equation u_t + u u_x = μ u_xx. Communications on Pure and Applied Mathematics 3, 201–230.', 'Cole, J. D. (1951). On a quasi-linear parabolic equation occurring in aerodynamics. Quarterly of Applied Mathematics 9, 225–236.', 'Whitham, G. B. (1974). Linear and Nonlinear Waves. Wiley.', 'LeVeque, R. J. (2002). Finite Volume Methods for Hyperbolic Problems. Cambridge University Press.', 'Lax, P. D. (1954). Weak solutions of nonlinear hyperbolic equations and their numerical computation. Communications on Pure and Applied Mathematics 7, 159–193.'],
  inputs: [
    inp('L', 'Domain length', 'm', 1, { min: 0.01, max: 1000, kind: 'geometry', aliases: ['domain length', 'length', 'wavelength'] }),
    inp('U_0', 'Velocity amplitude', 'm/s', 1, { min: 0.001, max: 1000, aliases: ['amplitude', 'velocity amplitude', 'velocity'] }),
    inp('Re', 'Reynolds number U₀L/ν', '1', 400, { min: 20, max: 5000, aliases: ['reynolds number', 'reynolds'] }),
    inp('t_s', 'End time in units of L/U₀', '1', 0.6, { min: 0.05, max: 2, aliases: ['end time', 'duration'] }),
    inp('n_x', 'Number of grid points', '1', 401, { min: 51, max: 1601, kind: 'numerical' }),
  ],
  assumptions: [
    asm('sine', 'The initial condition is one period of a sine wave on a periodic domain.', { why: 'Shows steepening and shock formation from smooth data', alt: 'The initial condition is the exact travelling-wave shock between U₀ and zero, to test propagation speed and thickness.' }),
    asm('viscous', 'Physical viscosity is present.', { why: 'Sets the shock thickness', alt: 'The inviscid equation is solved; only the numerical dissipation of the scheme smooths the shock.' }),
    asm('godunov', 'The interface flux is the Godunov (exact Riemann) flux.', { why: 'Least dissipative monotone flux', alt: 'A Lax–Friedrichs flux is used, with half the classical dissipation (coefficient Δx/(2Δt) for the smallest cell) so that it stays monotone when the explicit viscous term is added: simpler, but more diffusive.' }),
    asm('conservative', 'The scheme is written in conservation form.', { why: 'Required for the correct shock speed (Lax–Wendroff theorem)', alt: 'The non-conservative form u ∂u/∂x is differenced directly (same second-order reconstruction, upwinded on the cell velocity; for the travelling wave on a uniform grid at rest). A resolved viscous shock is still computed correctly, but an under-resolved or inviscid one travels at the wrong speed.' }),
  ],
  symbols: { u: ['Velocity', 'm/s'], x: ['Position', 'm'], t: ['Time', 's'], nu: ['Kinematic viscosity', 'm^2/s'], t_b: ['Breaking time', 's'], delta: ['Shock thickness', 'm'], u_L: ['Velocity of the left state, behind the shock', 'm/s'], u_R: ['Velocity of the right state, ahead of the shock', 'm/s'], s_w: ['Shock speed', 'm/s'], x_s: ['Initial shock position', 'm'] },
  equations: a => [
    a.conservative
      ? eq('pde', 'Burgers equation, conservation form', 'pd(u,t) + pd(u^2/2,x)', a.viscous ? 'nu*pd2(u,x)' : '0*nu*pd2(u,x)', { kind: 'law', origin: 'One-dimensional momentum balance without pressure', needs: ['conservative'] })
      : eq('pde', 'Burgers equation, advective form', 'pd(u,t) + u*pd(u,x)', a.viscous ? 'nu*pd2(u,x)' : '0*nu*pd2(u,x)', { kind: 'law', origin: 'One-dimensional momentum balance without pressure' }),
    eq('re', 'Reynolds number', 'Re', 'U_0*L/nu', { kind: 'definition' }),
    ...(a.sine ? [eq('tb', 'Breaking time of a sine wave', 't_b', 'L/(2*pi*U_0)', { kind: 'derived', origin: 'Method of characteristics: first crossing where −∂u₀/∂x is largest', needs: ['sine'] })] : [eq('tw', 'Travelling-wave solution', 'u', '(u_L + u_R)/2 - (u_L - u_R)/2*tanh((u_L - u_R)*(x - x_s - s_w*t)/(4*nu))', { kind: 'derived', origin: 'Exact steady solution in the frame of the shock' })]),
    eq('rh', 'Shock speed', 's_w', '(u_L + u_R)/2', { kind: 'law', origin: 'Rankine–Hugoniot jump condition for the flux u²/2' }),
    eq('thick', 'Shock thickness', 'delta', '4*nu/(u_L - u_R)', { kind: 'derived', origin: 'Width scale of the hyperbolic-tangent profile' }),
  ],
  derivation: a => [
    { text: 'Without viscosity each value of u is carried unchanged along a characteristic moving at speed u, so the profile at time t is the initial profile sheared in x.', tex: 'u(x,t) = u_0(\\xi),\\qquad x = \\xi + u_0(\\xi)\\,t' },
    { text: 'Characteristics first cross, and the gradient becomes infinite, at the breaking time set by the steepest negative initial slope.', tex: 't_b = \\frac{-1}{\\min_\\xi u_0\'(\\xi)} = \\frac{L}{2\\pi U_0}\\ \\text{for a sine wave}' },
    { text: 'Seek a steady profile in a frame moving at speed s between states u_L > u_R. Integrating the equation once gives a first-order equation whose solution is a hyperbolic tangent.', tex: 'u = \\frac{u_L+u_R}{2} - \\frac{u_L-u_R}{2}\\tanh\\!\\left[\\frac{(u_L-u_R)(x-st)}{4\\nu}\\right]' },
    { text: 'The integration constant fixes the speed: it is the mean of the two states, as also follows from conservation across a discontinuity.', tex: 's = \\frac{[u^2/2]}{[u]} = \\frac{u_L+u_R}{2}' },
    { text: 'The finite-volume update changes each cell average by the difference of fluxes through its faces, so the total of u is conserved exactly. The states either side of a face come from a limited linear reconstruction in each cell, and the viscous flux from the difference of the neighbouring cell values.', tex: '\\Delta x_i\\,\\frac{\\mathrm{d}u_i}{\\mathrm{d}t} = -\\big(F_{i+1/2}-F_{i-1/2}\\big) + \\nu\\left(\\frac{u_{i+1}-u_i}{x_{i+1}-x_i} - \\frac{u_i-u_{i-1}}{x_i-x_{i-1}}\\right)' },
    { text: 'The shock layer has the known thickness 4ν/Δu. Its position is known too — mid-domain for the sine wave, and at rest in a frame moving at the mean of the two states for the travelling wave — so the cells are concentrated there and the layer is resolved at any Reynolds number.', tex: '\\Delta x_{\\min} = \\frac{200}{n_x}\\,\\delta,\\qquad \\delta = \\frac{4\\nu}{u_L-u_R}' },
  ],
  solve(v, a) {
    const n = Math.max(21, Math.round(v.n_x)), nu = a.viscous ? v.U_0 * v.L / v.Re : 0, nuPhys = v.U_0 * v.L / v.Re, tEnd = v.t_s * v.L / v.U_0;
    const x0 = 0.25 * v.L, nuIC = nuPhys, m = n - 1;
    const tb = v.L / (2 * Math.PI * v.U_0), delta = a.viscous ? 4 * nuPhys / (a.sine ? 2 * v.U_0 : v.U_0) : 0;
    // the grid is refined about the shock layer, whose position is known: mid-domain for the sine wave, and at rest in a frame moving at the mean of the two
    // states for the travelling wave. The non-conservative and inviscid travelling waves keep the uniform grid at rest: their shocks are the under-resolved ones.
    const ride = !a.sine && a.viscous && a.conservative, w = ride ? 0.5 * v.U_0 : 0, fine = a.sine || ride ? delta : 0;
    const run = burgersRun({ xf: burgersGrid(m, v.L, a.sine ? 0.5 * v.L : x0, fine), nu, tEnd, periodic: a.sine, uL: v.U_0, uR: 0, w, flux: a.godunov ? 'godunov' : 'lf', conservative: a.conservative, maxSteps: N.clamp(Math.round(4e7 / n), 20000, 60000),
      u0: a.sine ? x => v.U_0 * Math.sin(2 * Math.PI * x / v.L) : x => burgersWave(x, 0, v.U_0, 0, x0, nuIC) });
    const tReal = run.times.at(-1), dx = run.dx, xExact = a.sine ? 0.5 * v.L : x0 + 0.5 * v.U_0 * tReal;
    // front position: where the profile crosses the mean of the two states (travelling wave) or zero in mid-domain (sine)
    const level = a.sine ? 0 : 0.5 * v.U_0;
    let xf = NaN;
    for (let i = 1; i < m; i++) { const p = run.final[i - 1], q = run.final[i]; if ((!a.sine || (run.x[i] > 0.25 * v.L && run.x[i - 1] < 0.75 * v.L)) && (p - level) * (q - level) <= 0 && p > q) { xf = run.x[i - 1] + (level - p) / (q - p) * (run.x[i] - run.x[i - 1]) + w * tReal; break; } }
    // profiles on a grid at rest: for the moving frame, the same refined grid placed where the shock ends, with the undisturbed states outside the moving cells
    let x = run.x, wd = run.w, snaps = run.snaps;
    if (ride) { const fo = burgersGrid(m, v.L, N.clamp(xExact, 0, v.L), fine); x = fo.slice(1).map((q, i) => 0.5 * (q + fo[i])); wd = fo.slice(1).map((q, i) => q - fo[i]); snaps = run.snaps.map((s, k) => { const sh = w * run.times[k]; return x.map(q => (q - sh < run.x[0] ? v.U_0 : q - sh > run.x[m - 1] ? 0 : N.interp1(run.x, s, q - sh))); }); }
    const uf = snaps.at(-1), integral = arr => arr.reduce((s, q, i) => s + q * wd[i], 0), I0 = integral(snaps[0]), I1 = integral(uf);
    const en = arr => 0.5 * arr.reduce((s, q, i) => s + q * q * wd[i], 0), E0 = en(snaps[0]), E1 = en(uf);
    const exact = a.sine ? null : x.map(q => burgersWave(q, tReal, v.U_0, 0, x0, Math.max(nu, 1e-12 * v.U_0 * v.L)));
    const gEnd = run.gmax.at(-1), thickNum = (a.sine ? 2 * v.U_0 : v.U_0) / (2 * Math.max(gEnd, 1e-300));
    // what the grid, not the physics, decides: the thickness and steepness of a shock with no (or unresolved) viscous layer, and the position of an
    // under-resolved viscous shock in the non-conservative form. These are named as such; everything else converges with the number of points.
    const shocked = !a.sine || tReal >= tb, thin = a.viscous ? delta < 1.5 * dx : shocked, drift = !a.sine && !a.conservative && a.viscous && thin;
    const xfr = Number.isFinite(xf) ? xf : xExact, sNum = a.sine ? 0 : (xfr - x0) / Math.max(tReal, 1e-300), sRH = a.sine ? 0 : 0.5 * v.U_0;
    const warnings = [];
    if (run.truncated) warnings.push(`The run was truncated at ${lab(tReal, 's')} after ${run.steps} time steps; use fewer grid points or a lower Reynolds number to reach the requested time.`);
    if (a.viscous && delta < 1.5 * dx) warnings.push(`The physical shock thickness (${lab(delta, 'm')}) is less than one and a half grid cells (${lab(dx, 'm')}): the computed thickness is set by numerical, not physical, viscosity.${a.sine || ride ? ' Use more grid points.' : ''}`);
    if (!a.viscous && shocked) warnings.push(`Without viscosity the shock is a discontinuity: its computed thickness (${lab(thickNum / dx)} cells) and steepest gradient are set by the grid and scale with the cell size however many points are used. The front position, the energy and the conservation of ∫u dx do not depend on it.`);
    if (!a.conservative) warnings.push(a.sine ? 'The non-conservative form does not conserve ∫u dx across an under-resolved shock. Here the shock stands at mid-domain by symmetry, so its position cannot show the error; the travelling wave does.'
      : !a.viscous ? `The non-conservative form advances each cell by its own velocity times the upwind difference, so fluid at rest ahead of the shock is never set in motion: without viscosity the front creeps forward only through the exponentially small tail of the initial profile and stalls. Its mean speed is ${lab(sNum, 'm/s')} against the Rankine–Hugoniot speed ${lab(sRH, 'm/s')}; this wrong value does not improve with more grid points.`
        : thin ? `The non-conservative form does not conserve ∫u dx across an under-resolved shock: the front has travelled at ${lab(sNum, 'm/s')} against the Rankine–Hugoniot speed ${lab(sRH, 'm/s')}, and that speed changes with the grid until the viscous layer spans a few cells (the conservative form gives the right speed on any grid).`
          : 'The viscous layer is resolved, so the non-conservative form still gives the right shock speed; the error appears when the layer is thinner than about one and a half cells, or without viscosity.');
    if (!a.sine && xExact > 0.9 * v.L) warnings.push('The shock has reached the outflow boundary; reduce the end time.');
    return {
      scalars: [
        scalar('nu', 'Kinematic viscosity', nuPhys, 'm^2/s', { note: a.viscous ? '' : 'not applied: inviscid run' }), scalar('t_b', 'Breaking time of the sine wave', tb, 's'),
        scalar('t_end', 'Simulated time', tReal, 's'), scalar('delta', 'Physical shock thickness 4ν/Δu', delta, 'm'), scalar('delta_num', thin ? 'Numerical shock thickness Δu/(2|∂u/∂x|max), set by the grid cell size' : 'Computed shock thickness Δu/(2|∂u/∂x|max)', thickNum, 'm', { note: !a.viscous ? (shocked ? 'an inviscid shock is a discontinuity: this is about one cell on any grid' : 'the wave has not yet broken: the profile is still smooth') : thin ? 'the physical layer is thinner than one and a half cells' : a.sine ? 'same definition as 4ν/Δu for a hyperbolic-tangent profile, with the initial jump 2U₀; the jump decays, so the layer is thicker than 4ν/Δu at late times' : 'same definition as 4ν/Δu for a hyperbolic-tangent profile' }),
        scalar('n_cells', 'Computed shock thickness in grid cells', thickNum / dx, '1'),
        scalar('g_max', thin ? 'Steepest gradient at the end time, set by the grid cell size' : 'Steepest gradient at the end time', gEnd, '1/s'), scalar('x_f', drift ? 'Front position (changes with the grid: under-resolved shock in non-conservative form)' : 'Front position', xfr, 'm', { text: Number.isFinite(xf) ? undefined : 'No front detected' }),
        scalar('x_f_exact', 'Exact front position', xExact, 'm'), scalar('s_w', 'Shock speed (Rankine–Hugoniot)', sRH, 'm/s'),
        scalar('s_num', drift ? 'Mean speed of the computed front (changes with the grid: under-resolved shock in non-conservative form)' : 'Mean speed of the computed front', sNum, 'm/s', { note: a.sine ? 'the shock stands at mid-domain by symmetry' : !a.conservative && !a.viscous ? 'wrong, and not improved by refinement: the advective form cannot set fluid at rest in motion' : undefined }),
        scalar('E_ratio', 'Kinetic energy remaining', E1 / E0, '1', { show: '%' }), scalar('dx', 'Smallest grid spacing', dx, 'm'), scalar('steps', 'Time steps', run.steps, '1'),
      ],
      series: [
        line('profiles', 'Velocity profiles', 'Position', 'm', x, [...[0, 0.25, 0.5, 1].map(f => { const k = Math.round(f * (snaps.length - 1)); return { label: `t = ${lab(run.times[k], 's')}`, data: snaps[k] }; }), ...(exact ? [{ label: 'Exact travelling wave at the end time', data: exact, dash: true }] : [])], 'Velocity', 'm/s'),
        line('gradient', 'Steepest gradient against time', 'Time', 's', run.tg, [{ label: 'max |∂u/∂x|', data: run.gmax }, ...(a.sine ? [{ label: 'Inviscid theory before breaking', data: run.tg.map(t => (t < 0.98 * tb ? 2 * Math.PI * v.U_0 / v.L / (1 - t / tb) : NaN)), dash: true }] : [])], 'Gradient', '1/s', { logy: true }),
      ],
      anims: [anim('u-anim', 'Velocity profile', 'Position', 'm', x, snaps, run.times, 'Velocity', 'm/s')],
      checks: [
        check('Conservation of ∫u dx', a.conservative && a.sine ? (I1 - I0) / (v.U_0 * v.L) : 0, 1e-10, 'Exact for a conservative scheme on a periodic domain'),
        check('Kinetic energy does not increase', a.sine ? Math.max(E1 / E0 - 1, 0) : 0, 1e-9, 'Viscosity and upwinding only dissipate energy on a periodic domain (not evaluated for the travelling wave, whose inflow boundary adds energy)'),
        check('Maximum principle', Math.max(N.maxOf(run.final) - v.U_0, -v.U_0 - N.minOf(run.final), 0) / v.U_0, 1e-9, 'A monotone scheme creates no new extrema'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const U = v.U_0, L = v.L, nu = U * L / 100, x0 = 0.25 * L, tEnd = 0.6 * L / U;
    const fine = burgersRun({ n: 401, L, nu, tEnd, periodic: false, uL: U, uR: 0, flux: 'godunov', conservative: true, u0: x => burgersWave(x, 0, U, 0, x0, nu), maxSteps: 40000 });
    const i = fine.x.findIndex(q => q >= x0 + 0.5 * U * tEnd + 2 * nu / U), tr = fine.times.at(-1);
    const front = r => { for (let k = 1; k < r.x.length; k++) if ((r.final[k - 1] - 0.5 * U) * (r.final[k] - 0.5 * U) <= 0) return r.x[k - 1] + (0.5 * U - r.final[k - 1]) / (r.final[k] - r.final[k - 1]) * (r.x[k] - r.x[k - 1]); return NaN; };
    const inv = burgersRun({ n: 201, L, nu: 0, tEnd: 0.5 * L / U, periodic: false, uL: U, uR: 0, flux: 'godunov', conservative: true, u0: x => (x < x0 ? U : 0) });
    const sine = burgersRun({ xf: burgersGrid(400, L, 0.5 * L, 2 * nu / (4 * U)), nu: nu / 4, tEnd, periodic: true, flux: 'godunov', conservative: true, u0: x => U * Math.sin(2 * Math.PI * x / L) });
    return [
      bench('Viscous shock position vs exact travelling wave', front(fine) / L, (x0 + 0.5 * U * tr) / L, 'x_s = x₀ + ½(u_L + u_R) t; grid at rest', 1e-3),
      bench('Velocity in the shock layer vs exact tanh profile', fine.final[i] / U, burgersWave(fine.x[i], tr, U, 0, x0, nu) / U, 'Exact travelling-wave solution, Re = 100', 0.01),
      bench('Inviscid shock speed vs Rankine–Hugoniot', (front(inv) - x0) / (0.5 * L / U) / U, 0.5, 's = ½(u_L + u_R); grid at rest', 5e-3),
      bench('Steepest gradient of the sine-wave shock vs exact solution', sine.gmax.at(-1) * L / U, -burgersSineSlope(U, L, nu / 4, sine.times.at(-1)) * L / U, 'Cole–Hopf transformation (Hopf 1950, Cole 1951), Re = 400, by quadrature', 0.02),
    ];
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.line(60, 250, 600, 250, 'd-line')} ${S.line(60, 60, 60, 300, 'd-line')} ${S.text(46, 70, 'u')} ${S.text(600, 270, 'x')}
      ${a.sine ? S.path('M60 180 Q195 20 330 180 Q465 340 600 180', 'd-dim') + S.path('M60 180 Q260 60 322 110 L338 250 Q400 300 600 180', 'd-line d-hazard') + S.text(330, 96, 'shock forms at mid-domain') : S.path('M60 110 L200 110 Q230 110 240 180 Q250 250 280 250 L600 250', 'd-dim') + S.path('M60 110 L380 110 Q410 110 420 180 Q430 250 460 250 L600 250', 'd-line d-hazard') + S.arrow(260, 150, 400, 150) + S.text(330, 140, 's = U₀/2')}
      ${S.text(330, 330, a.sine ? `breaking time L/(2πU₀) = ${lab(v.L / (2 * Math.PI * v.U_0), 's')}` : `thickness 4ν/U₀ = ${lab(4 * v.L / v.Re, 'm')}`)}
      ${S.text(330, 36, `Re = ${lab(v.Re)},  ${a.godunov ? 'Godunov' : 'Lax–Friedrichs'} flux`)}
    `);
  },
  experiment: {
    objective: 'Observe nonlinear steepening and shock formation in a system governed to good approximation by the Burgers equation, and measure the shock speed and thickness.',
    apparatus: ['Long tube filled with air and driven at one end by a loudspeaker or piston at high amplitude (finite-amplitude acoustics obey a Burgers equation in the retarded frame)', 'Alternatively, a shallow-water channel with a wave-maker for an analogous steepening bore', 'Anechoic termination to suppress reflections'],
    instruments: [{ name: 'Flush-mounted microphones or dynamic pressure transducers at several stations', measures: 'Waveform against distance', range: '100–170 dB re 20 µPa', resolution: '≥ 100 kHz bandwidth' }, { name: 'Digital oscilloscope', measures: 'Rise time of the pressure front', range: '—', resolution: '≥ 1 MS/s' }, { name: 'Thermometer and barometer', measures: 'Ambient state for sound speed and diffusivity', range: '—', resolution: '±0.2 K, ±50 Pa' }],
    procedure: ['Drive the tube with a sinusoidal source at a fixed frequency and several amplitudes.', 'Record the waveform at each station.', 'Measure the harmonic content and the steepest slope of each waveform; identify the shock-formation distance.', 'Compare the formation distance with the inviscid prediction and the rise time with the viscous thickness.'],
    controls: ['Low-amplitude run to confirm linear propagation without distortion', 'Check wall-boundary-layer attenuation separately'],
    signatures: ['Progressive distortion of a sine wave into a sawtooth', 'Shock-formation distance inversely proportional to source amplitude', 'Growth of harmonics followed by amplitude-independent decay (acoustic saturation)'],
    safety: ['Hearing protection: levels above 140 dB', 'Secure the driver and tube against vibration'],
  },
  falsify: ['A conservative scheme converging, under grid refinement, to a shock speed different from the mean of the two states.', 'Finite-amplitude plane waves in a thermoviscous gas failing to steepen at the predicted rate over distances short compared with the absorption length.'],
  alternatives: [{ name: 'Cole–Hopf transformation', text: 'Maps the viscous Burgers equation to the linear heat equation, giving the exact solution for any initial condition as a quadrature; it is used here as a benchmark.' }, { name: 'Higher-order schemes (WENO, discontinuous Galerkin)', text: 'Third- or higher-order reconstruction resolves the layer with fewer cells than the second-order limited scheme used here.' }, { name: 'Full Euler or Navier–Stokes equations', text: 'Burgers’ equation has no pressure or energy equation; real shocks also involve density and temperature jumps.' }],
  hazards: [{ hazard: 'Misinterpreting numerical viscosity as physical', cause: 'Under-resolved shock layer', mitigation: 'Check that the physical thickness spans several cells or report the numerical thickness' }],
  standards: ['ASME V&V 20 (verification and validation in computational fluid dynamics and heat transfer)', 'AIAA G-077 (guide for the verification and validation of computational fluid dynamics simulations)'],
  limits: 'One space dimension, constant viscosity, second-order accurate differences (first-order at extrema). The shock layer is resolved only while it spans about one and a half cells or more of the refined grid; the inviscid shock is always one or two cells thick, so its thickness and steepest gradient are properties of the grid and are named as such. In the non-conservative form the speed of an under-resolved shock depends on the grid, and of an inviscid one is wrong on every grid. The equation is a model: it omits pressure, density variation and energy.',
  numerics: { method: 'Explicit finite-volume scheme on a grid refined about the shock layer: MUSCL–Hancock (limited linear reconstruction, face states advanced half a step), Godunov or reduced-dissipation Lax–Friedrichs flux, central diffusion; the non-conservative option applies the same reconstruction to u ∂u/∂x, upwinded on the cell velocity', order: 2, stability: 'Time step 0.9 of the combined advective (Courant number ½) and diffusive limit of the smallest cell', resolution: 'n_x' },
  inverse: { series: 'profiles', curve: 3, fit: ['Re'] },
  extensions: ['Exact Cole–Hopf solution for arbitrary initial data', 'Grid that follows a shock whose path is not known in advance', 'Random initial data and Burgers turbulence', 'Two-dimensional Burgers equation'],
};

// ------------------------------------------------------------------ plane Poiseuille–Couette flow
/** Exact start-up from rest between y = 0 (fixed) and y = h (moving at U) with constant pressure gradient G = −dp/dx. */
function channelExact(y, t, h, U, G, mu, nuK) {
  // The sine series needs of order h/√(νt) terms. At early time the same solution is summed instead over images of the two walls
  // (Carslaw & Jaeger 1959, §3.3 and §3.14): error functions for the moving wall, their second integrals for the uniform force.
  const Fo = nuK * t / (h * h);
  if (Fo < 0.02) { if (!(t > 0)) return y >= h ? U : 0;
    const s2 = 2 * Math.sqrt(nuK * t), ec = z => { const q = 1 / (1 + 0.3275911 * z); return (((((1.061405429 * q - 1.453152027) * q) + 1.421413741) * q - 0.284496736) * q + 0.254829592) * q * Math.exp(-z * z); };
    const i2 = z => 0.25 * ((1 + 2 * z * z) * ec(z) - 2 * z * Math.exp(-z * z) / Math.sqrt(Math.PI));
    let uw = 0, up = 1; for (let k = 0; k < 3; k++) { uw += ec(((2 * k + 1) * h - y) / s2) - ec(((2 * k + 1) * h + y) / s2); up -= 4 * (k % 2 ? -1 : 1) * (i2((k * h + y) / s2) + i2(((k + 1) * h - y) / s2)); }
    return U * uw + G * nuK / mu * t * up; }
  let u = U * y / h + G / (2 * mu) * y * (h - y);
  for (let n = 1; n <= 200; n++) {
    const e = Math.exp(-n * n * Math.PI * Math.PI * nuK * t / (h * h)); if (e < 1e-16) break;
    const sn = Math.sin(n * Math.PI * y / h);
    u += 2 * U / (n * Math.PI) * (n % 2 ? -1 : 1) * sn * e;
    if (n % 2) u -= 4 * G * h * h / (mu * Math.pow(n * Math.PI, 3)) * sn * e;
  }
  return u;
}
/** Grid across the gap. Shortly after an impulsive start the velocity changes only within a layer of thickness δ = √(νt) at each
 *  wall; three quarters of the points of each half are then spread evenly over 6δ and the rest stride across the core, where the
 *  velocity is still uniform in y and any spacing represents it exactly. Uniform once 8δ reaches mid-gap. */
function channelGrid(h, ny, delta) {
  const Lh = h / 2, A = Math.min(Lh, 8 * delta); if (!(A < Lh)) return N.linspace(0, h, ny);
  const p = Math.max(2, Math.log((Lh - A) / delta) / Math.log(4 / 3)), g = q => A * q + (Lh - A) * q ** p;
  return Array.from({ length: ny }, (_, i) => { const xi = i / (ny - 1); return i === 0 ? 0 : i === ny - 1 ? h : xi <= 0.5 ? g(2 * xi) : h - g(2 * (1 - xi)); });
}
/** u_t = D u_yy + S(t) on a non-uniform grid y with u(0) = 0 and u(h) = uR: Crank–Nicolson in time, conservative three-point differences
 *  in space (the scheme of N.diffusion1D, to which it reduces on a uniform grid). Returns the same record. */
function channelMarch({ y, D, tEnd, nt, frames, u0, uR, source }) {
  const nx = y.length, dt = tEnd / nt, lo = new Float64Array(nx), up = new Float64Array(nx), cp = new Float64Array(nx);
  for (let i = 1; i < nx - 1; i++) { const hl = y[i] - y[i - 1], hr = y[i + 1] - y[i], w = 0.5 * (hl + hr); lo[i] = 0.5 * D * dt / (hl * w); up[i] = 0.5 * D * dt / (hr * w); }
  let u = y.map((q, i) => (typeof u0 === 'function' ? u0(q, i) : u0)); const snaps = [], times = [], every = Math.max(1, Math.floor(nt / frames));
  for (let n = 0; n <= nt; n++) {
    if (n % every === 0 || n === nt) { snaps.push(u.slice()); times.push(n * dt); }
    if (n === nt) break;
    const src = source ? dt * source(n * dt) : 0, un = new Array(nx); un[0] = 0; cp[0] = 0;
    for (let i = 1; i < nx - 1; i++) { const d = u[i] + lo[i] * (u[i - 1] - u[i]) + up[i] * (u[i + 1] - u[i]) + src, m = 1 + lo[i] + up[i] + lo[i] * cp[i - 1]; cp[i] = -up[i] / m; un[i] = (d + lo[i] * un[i - 1]) / m; }
    un[nx - 1] = uR; for (let i = nx - 2; i >= 1; i--) un[i] -= cp[i] * un[i + 1];
    u = un;
  }
  return { x: y, times, snaps, final: u, dt };
}

const channel = {
  id: 'channel-poiseuille-couette',
  title: 'Plane Poiseuille–Couette flow and its start-up',
  module: 2, klass: 'I', domains: ['cfd'],
  keywords: ['poiseuille', 'couette', 'channel flow', 'plane channel', 'parallel plates', 'pressure-driven flow', 'shear-driven flow', 'start-up flow', 'laminar flow', 'velocity profile', 'lubrication', 'wall shear'],
  summary: 'Laminar flow between parallel plates driven by a pressure gradient and a moving wall: the exact steady profile and a numerical solution of the transient start-up.',
  background: [
    'Fully developed laminar flow between two parallel plates is one of the few exact solutions of the Navier–Stokes equations. A pressure gradient alone gives the parabolic Poiseuille profile; a moving wall alone gives the linear Couette profile; because the governing equation is linear the two superpose. The combination describes lubricating films, coating flows and the leakage through narrow clearances.',
    'When the driving is applied suddenly, momentum diffuses in from the walls and the profile approaches its steady form on the viscous time scale h²/ν. The transient is governed by the one-dimensional diffusion equation with a uniform source and has an exact Fourier-series solution, which makes the problem a convenient verification case for diffusion solvers.',
  ],
  phenomena: ['Viscous diffusion of momentum', 'Pressure-driven and shear-driven flow', 'Approach to fully developed flow', 'Oscillatory (Womersley-type) response'],
  laws: ['momentum', 'mass'],
  refs: ['Batchelor, G. K. (1967). An Introduction to Fluid Dynamics. Cambridge University Press.', 'White, F. M. (2006). Viscous Fluid Flow, 3rd ed., McGraw-Hill.', 'Schlichting, H. & Gersten, K. (2017). Boundary-Layer Theory, 9th ed., Springer.', 'Couette, M. (1890). Études sur le frottement des liquides. Annales de Chimie et de Physique 21, 433–510.'],
  inputs: [
    inp('h', 'Gap between the plates', 'mm', 2, { min: 0.05, max: 100, kind: 'geometry', aliases: ['gap', 'channel height', 'plate spacing', 'clearance'] }),
    inp('U_w', 'Speed of the upper wall', 'm/s', 0.5, { min: 0, max: 10, aliases: ['wall speed', 'wall velocity', 'plate speed'] }),
    inp('G', 'Pressure gradient −dp/dx (positive drives flow in +x)', 'Pa/m', 400, { min: -1e5, max: 1e5, aliases: ['pressure gradient'] }),
    inp('mu', 'Dynamic viscosity', 'cP', 1, { min: 0.01, max: 1e4, kind: 'fluid', aliases: ['viscosity'] }),
    inp('rho', 'Density', 'kg/m^3', 1000, { min: 1, max: 2000, kind: 'fluid', aliases: ['density'] }),
    inp('t_end', 'Elapsed time since start-up', 's', 1, { min: 1e-3, max: 1e3, aliases: ['time', 'elapsed time', 'after'] }),
    inp('f_o', 'Forcing frequency (used when the pressure gradient oscillates)', 'Hz', 1, { min: 0.01, max: 100, aliases: ['frequency'] }),
    inp('n_y', 'Number of grid points across the gap', '1', 81, { min: 21, max: 401, kind: 'numerical' }),
  ],
  assumptions: [
    asm('pressure', 'A pressure gradient drives the flow.', { why: 'Poiseuille component', alt: 'There is no pressure gradient: pure Couette flow.' }),
    asm('moving', 'The upper wall moves in its own plane.', { why: 'Couette component', alt: 'Both walls are stationary: pure Poiseuille flow.' }),
    asm('from_rest', 'The fluid starts from rest.', { why: 'Impulsive start of both wall and pressure gradient', alt: 'The fluid starts from the steady Couette profile and only the pressure gradient is switched on.' }),
    asm('steady_forcing', 'The pressure gradient is constant in time.', { why: 'Leads to a steady state', alt: 'The pressure gradient oscillates as G cos(2π f t).' }),
  ],
  symbols: { q_s: ['Steady flow rate per unit width', 'm^2/s'],  u: ['Velocity', 'm/s'], y: ['Distance from the lower wall', 'm'], t: ['Time', 's'], nu: ['Kinematic viscosity', 'm^2/s'], u_s: ['Steady velocity profile', 'm/s'], q: ['Flow rate per unit width', 'm^2/s'], tau_w: ['Wall shear stress', 'Pa'], t_v: ['Viscous time', 's'], Re: ['Reynolds number', '1'], u_m: ['Mean velocity', 'm/s'] },
  equations: a => {
    const src = a.pressure ? (a.steady_forcing ? ' + G' : ' + G*cos(2*pi*f_o*t)') : '';
    const couette = a.moving ? 'U_w*y/h' : '', pois = a.pressure ? 'G*y*(h - y)/(2*mu)' : '';
    return [
      eq('mom', 'Momentum equation', 'rho*pd(u,t)', 'mu*pd2(u,y)' + src, { kind: 'law', origin: 'Navier–Stokes equations for unidirectional flow', needs: ['pressure', 'steady_forcing'].filter(q => a[q]) }),
      eq('bc', 'Upper-wall condition', 'u', a.moving ? 'U_w' : '0*U_w', { kind: 'boundary', origin: 'No slip at y = h', exportable: false, note: 'Holds only on the upper wall y = h.' }),
      ...(a.steady_forcing ? [eq('steady', 'Steady profile', 'u_s', [couette, pois].filter(Boolean).join(' + ') || '0*U_w', { kind: 'derived', origin: 'Exact solution of the steady momentum equation' }),
        eq('q', 'Steady flow rate per unit width', 'q_s', [a.moving ? 'U_w*h/2' : '', a.pressure ? 'G*h^3/(12*mu)' : ''].filter(Boolean).join(' + ') || '0*U_w*h', { kind: 'derived', origin: 'Integral of the steady profile' })] : []),
      eq('tw', 'Wall shear stress', 'tau_w', 'mu*pd(u,y)', { kind: 'law', origin: 'Newton’s law of viscosity' }),
      eq('tv', 'Viscous time', 't_v', 'h^2/nu', { kind: 'definition' }),
      eq('nu', 'Kinematic viscosity', 'nu', 'mu/rho', { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'For fully developed flow in x between infinite plates, the velocity depends only on y and t, continuity is satisfied identically and the nonlinear terms vanish. The x-momentum equation reduces to a diffusion equation with a source.', tex: '\\rho\\,\\frac{\\partial u}{\\partial t} = \\mu\\,\\frac{\\partial^2 u}{\\partial y^2} - \\frac{\\mathrm{d}p}{\\mathrm{d}x}' },
    { text: 'In steady state, integrating twice with no slip at both walls gives the superposition of a linear and a parabolic profile.', tex: 'u_s(y) = U\\,\\frac{y}{h} + \\frac{G}{2\\mu}\\,y\\,(h-y),\\qquad G = -\\frac{\\mathrm{d}p}{\\mathrm{d}x}' },
    { text: 'Integrating the profile gives the flow rate per unit width; the pressure-driven part varies as the cube of the gap.', tex: 'q = \\frac{U h}{2} + \\frac{G h^3}{12\\mu}' },
    { text: 'Starting from rest, the deviation from the steady profile satisfies the homogeneous diffusion equation and decays as a sine series.', tex: 'u = u_s + \\sum_{n=1}^{\\infty}\\left[\\frac{2U(-1)^n}{n\\pi} - \\frac{4Gh^2\\,[n\\ \\mathrm{odd}]}{\\mu\\,n^3\\pi^3}\\right]\\sin\\frac{n\\pi y}{h}\;e^{-n^2\\pi^2\\nu t/h^2}' },
    { text: 'The slowest mode decays on the viscous time scale.', tex: 't_v = \\frac{h^2}{\\nu},\\qquad \\text{slowest mode} \\propto e^{-\\pi^2 t/t_v}' },
  ],
  solve(v, a) {
    const ny = Math.max(11, Math.round(v.n_y)), nuK = v.mu / v.rho, U = a.moving ? v.U_w : 0, G = a.pressure ? v.G : 0, h = v.h, tv = h * h / nuK;
    const om = 2 * Math.PI * v.f_o;
    // Crank–Nicolson barely damps modes whose decay time is far shorter than the time step, so the march is staged: fine steps
    // through the impulsive start, then steps of a small fraction of the viscous time until the start-up transient has decayed
    // (about three viscous times). With steady forcing the profile is then steady and the march stops; with oscillating forcing
    // it continues to the requested time.
    // The grid is fitted to the wall layers √(ν t) while they are thin (only with steady forcing, where that is the one length scale).
    const yg = channelGrid(h, ny, a.steady_forcing ? Math.sqrt(nuK * v.t_end) : h);
    const src = G ? (a.steady_forcing ? () => G / v.rho : (t0, t1, nt) => t => G / v.rho * Math.cos(om * (t0 + t + 0.5 * (t1 - t0) / nt))) : undefined, fitted = yg[1] - yg[0] < 0.999 * h / (ny - 1);
    const stage = (u0, t0, t1, nt, frames) => { const s = src && (a.steady_forcing ? src : src(t0, t1, nt)); return fitted ? channelMarch({ y: yg, D: nuK, tEnd: t1 - t0, nt, frames, u0, uR: U, source: s })
      : N.diffusion1D({ D: nuK, L: h, nx: ny, tEnd: t1 - t0, nt, frames, u0, left: { type: 'dirichlet', value: 0 }, right: { type: 'dirichlet', value: U }, source: s && ((_, t) => s(t)) }); };
    const tA = Math.min(v.t_end, 0.02 * tv), tB = Math.min(v.t_end, 3 * tv), tC = a.steady_forcing ? tB : v.t_end;
    const sol = stage(a.from_rest ? 0 : y => U * y / h, 0, tA, tA < v.t_end ? 200 : 400, tA < v.t_end ? 8 : 50);
    const follow = (t0, t1, nt, frames) => { const prev = sol.final, s2 = stage((_, i) => prev[i], t0, t1, nt, frames); sol.final = s2.final; s2.snaps.slice(1).forEach((q, k) => { sol.snaps.push(q); sol.times.push(t0 + s2.times[k + 1]); }); };
    if (tB > tA) follow(tA, tB, 400, 40);
    if (tC > tB) follow(tB, tC, Math.round(N.clamp(40 * v.f_o * (tC - tB), 400, 4000)), 50);
    const y = sol.x, uf = sol.final, steady = y.map(q => U * q / h + G / (2 * v.mu) * q * (h - q));
    const scale = Math.max(Math.abs(U), Math.abs(G) * h * h / (8 * v.mu), 1e-30);
    const q = N.trapz(y, uf), qS = U * h / 2 + G * h ** 3 / (12 * v.mu), um = q / h;
    // wall gradient from the three points next to the wall (second order for unequal spacings h1, h2)
    const wallGrad = (f0, f1, f2, h1, h2) => -(2 * h1 + h2) / (h1 * (h1 + h2)) * f0 + (h1 + h2) / (h1 * h2) * f1 - h1 / (h2 * (h1 + h2)) * f2;
    const tauB = v.mu * wallGrad(uf[0], uf[1], uf[2], y[1] - y[0], y[2] - y[1]), tauT = -v.mu * wallGrad(uf[ny - 1], uf[ny - 2], uf[ny - 3], y[ny - 1] - y[ny - 2], y[ny - 2] - y[ny - 3]);
    const exactOK = a.from_rest && a.steady_forcing, exact = exactOK ? y.map(s => channelExact(s, v.t_end, h, U, G, v.mu, nuK)) : null;
    const errEx = exact ? N.maxOf(exact.map((e, i) => Math.abs(e - uf[i]))) / scale : 0, dev = N.maxOf(steady.map((s, i) => Math.abs(s - uf[i]))) / scale;
    const Re = v.rho * Math.abs(um) * 2 * h / v.mu, mid = (ny - 1) >> 1;
    const warnings = [];
    if (Re > 2000) warnings.push(`The Reynolds number based on twice the gap is ${lab(Re)}: plane channel flow is unlikely to remain laminar, and the laminar solution then under-predicts wall shear.`);
    if (!a.steady_forcing) warnings.push(`With oscillating forcing the Womersley number h√(ω/ν)/2 is ${lab(h / 2 * Math.sqrt(om / nuK))}; above about 3 the core moves as a plug out of phase with the pressure gradient.`);
    if (a.steady_forcing && dev > 0.01) warnings.push(`The flow has not yet reached steady state: the profile differs from the steady one by ${lab(dev * 100, '%')} of the velocity scale after ${lab(v.t_end / tv)} viscous times.`);
    if (!a.pressure && !a.moving) warnings.push('Neither a pressure gradient nor a moving wall is present: the fluid remains at rest.');
    if (a.steady_forcing && v.t_end > 3 * tv) warnings.push('The elapsed time is more than three viscous times: the profile shown is the steady state, reached well before the requested time.');
    return {
      scalars: [
        scalar('nu', 'Kinematic viscosity', nuK, 'm^2/s'), scalar('t_v', 'Viscous time h²/ν', tv, 's'), scalar('Fo', 'Elapsed time over viscous time', v.t_end / tv, '1'),
        scalar('u_c', 'Velocity at mid-gap', uf[mid], 'm/s'), scalar('u_max', 'Largest velocity magnitude', N.maxOf(uf.map(Math.abs)), 'm/s'), scalar('u_m', 'Mean velocity', um, 'm/s'),
        scalar('q', 'Flow rate per unit width', q, 'm^2/s'), scalar('q_s', 'Steady flow rate per unit width (exact)', qS, 'm^2/s'),
        scalar('tau_b', 'Shear stress on the lower wall', tauB, 'Pa'), scalar('tau_t', 'Shear stress exerted by the fluid on the upper wall', -tauT, 'Pa'),
        scalar('tau_s', 'Steady lower-wall shear stress (exact)', v.mu * U / h + G * h / 2, 'Pa'), scalar('Re', 'Reynolds number on twice the gap', Re, '1'),
        scalar('dev', 'Departure from the steady profile', dev, '1', { show: '%' }), scalar('P_w', 'Power to drive the upper wall per unit area', -tauT * -U, 'W/m^2'),
      ],
      series: [
        line('profiles', 'Velocity profiles during start-up', 'Velocity', 'm/s', uf, [{ label: `t = ${lab(v.t_end, 's')}`, data: y.map(s => s * 1000) }], 'Distance from lower wall', 'mm', { overlay: [...[0.1, 0.3].map(f => { const k = Math.max(1, Math.round(f * (sol.snaps.length - 1))); return { label: `t = ${lab(sol.times[k], 's')}`, x: sol.snaps[k], y: y.map(s => s * 1000) }; }), ...(a.steady_forcing ? [{ label: 'Exact steady profile', x: steady, y: y.map(s => s * 1000), dash: true }] : [])] }),
        line('history', 'Mid-gap and mean velocity against time', 'Time', 's', sol.times, [{ label: 'Mid-gap', data: sol.snaps.map(s => s[mid]) }, { label: 'Mean', data: sol.snaps.map(s => N.trapz(y, s) / h), dash: true }], 'Velocity', 'm/s'),
      ],
      anims: [anim('u-anim', 'Velocity profile across the gap', 'Distance from lower wall', 'mm', y.map(s => s * 1000), sol.snaps, sol.times, 'Velocity', 'm/s')],
      checks: [
        check('Numerical profile against the exact transient series', errEx, 5e-3, 'Evaluated for a start from rest with constant forcing'),
        check('No slip at both walls', (Math.abs(uf[0]) + Math.abs(uf[ny - 1] - U)) / scale, 1e-12, 'u(0) = 0 and u(h) = U'),
        check('Force balance at steady state', a.steady_forcing && dev < 1e-4 ? (G * h + tauT - tauB) / Math.max(Math.abs(G * h), Math.abs(tauB), 1e-30) : 0, 5e-3, 'Pressure force per unit area equals the difference of the wall shear stresses'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { pressure: true, moving: true, from_rest: true, steady_forcing: true }, nuK = v.mu / v.rho, tv = v.h ** 2 / nuK;
    const long = this.solve({ ...v, t_end: 5 * tv }, b), early = this.solve({ ...v, t_end: 0.05 * tv }, b);
    const uS = v.U_w / 2 + v.G * v.h ** 2 / (8 * v.mu), sc = Math.max(Math.abs(v.U_w), Math.abs(v.G) * v.h ** 2 / (8 * v.mu));
    return [
      bench('Steady mid-gap velocity', val(long, 'u_c') / sc + 2, uS / sc + 2, 'u(h/2) = U/2 + G h²/(8 μ)', 1e-4),
      bench('Steady flow rate', val(long, 'q') / (sc * v.h) + 2, val(long, 'q_s') / (sc * v.h) + 2, 'q = U h/2 + G h³/(12 μ)', 2e-4),
      bench('Mid-gap velocity at 0.05 viscous times vs exact series', val(early, 'u_c') / sc + 2, channelExact(v.h / 2, 0.05 * tv, v.h, v.U_w, v.G, v.mu, nuK) / sc + 2, 'Fourier-series solution of the start-up problem', 2e-3),
      bench('Poiseuille mean-to-maximum velocity ratio', (() => { const pz = this.solve({ ...v, G: Math.abs(v.G) || 1, t_end: 5 * tv }, { ...b, moving: false }); return val(pz, 'u_m') / val(pz, 'u_max'); })(), 2 / 3, 'u_mean/u_max = 2/3 for a parabolic profile', 2e-4),
    ];
  },
  validation: [],
  diagram(v, a) {
    const pts = N.linspace(0, 1, 9);
    return svg(`
      ${S.line(80, 90, 560, 90, 'd-pipe')} ${S.line(80, 270, 560, 270, 'd-pipe')} ${S.path('M80 274 L560 274', 'd-ground')}
      ${a.moving ? S.arrow(260, 70, 400, 70) + S.text(330, 58, `U = ${lab(v.U_w, 'm/s')}`) : S.text(330, 70, 'stationary wall')}
      ${S.line(200, 90, 200, 270, 'd-dim')}
      ${pts.map(s => { const u = (a.moving ? s : 0) + (a.pressure ? 4 * s * (1 - s) * 0.8 : 0); return Math.abs(u) > 0.02 ? S.arrow(200, 270 - s * 180, 200 + u * 130, 270 - s * 180) : ''; }).join('')}
      ${a.pressure ? S.arrow(90, 180, 150, 180, 'd-arrow d-hazard') + S.text(120, 168, '−dp/dx', 'd-text d-small') : ''}
      ${S.dim(590, 90, 590, 270, `h = ${lab(v.h * 1000, 'mm')}`)}
      ${S.text(330, 320, `μ = ${lab(v.mu * 1000, 'mPa·s')},  viscous time ${lab(v.h ** 2 * v.rho / v.mu, 's')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the velocity profile and flow rate between parallel plates with a moving wall and an imposed pressure gradient, and time the start-up transient.',
    apparatus: ['Channel of large width-to-gap ratio (at least 20:1) with one wall formed by a moving belt', 'Constant-head tanks to impose a pressure gradient', 'Viscous Newtonian liquid (silicone oil or glycerol solution) to lengthen the viscous time'],
    instruments: [{ name: 'Laser-Doppler or particle-image velocimeter', measures: 'Velocity profile across the gap', range: '0–2 m/s', resolution: '±1 %' }, { name: 'Differential pressure transducer between two taps', measures: 'Pressure gradient', range: '0–10 kPa', resolution: '±0.1 %' }, { name: 'Weigh tank and timer', measures: 'Flow rate', range: '—', resolution: '±0.5 %' }, { name: 'Belt encoder', measures: 'Wall speed', range: '0–2 m/s', resolution: '±0.2 %' }],
    procedure: ['With the belt stopped, set a pressure gradient and record the profile and flow rate (Poiseuille).', 'With no pressure gradient, run the belt and record the profile (Couette).', 'Apply both and verify superposition.', 'Start the belt impulsively and record the mid-gap velocity against time.'],
    controls: ['Measure at two streamwise stations to confirm the flow is fully developed', 'Vary the gap to verify the cubic dependence of the pressure-driven flow rate'],
    signatures: ['Parabolic, linear and combined profiles', 'Flow rate proportional to h³ at fixed pressure gradient', 'Start-up governed by a single exponential at late time with rate π²ν/h²'],
    safety: ['Guard the moving belt', 'Contain and clean oil spills'],
  },
  falsify: ['A steady laminar profile between wide parallel plates that is not the sum of a linear and a parabolic part.', 'A pressure-driven flow rate that does not scale with the cube of the gap at low Reynolds number.'],
  alternatives: [{ name: 'Turbulent channel flow', text: 'Above a Reynolds number of roughly 1000–2000 (on half-gap and centre-line velocity) the profile flattens and wall shear follows a logarithmic law.' }, { name: 'Non-Newtonian fluids', text: 'Power-law and Bingham fluids give blunted or plug-like profiles and a different flow-rate law.' }, { name: 'Slip boundary condition', text: 'In gases at low pressure or liquids on hydrophobic surfaces a Navier slip length modifies the profile.' }, { name: 'Reynolds lubrication theory', text: 'Extends this solution to slowly varying gaps, giving the pressure distribution in bearings.' }],
  hazards: [{ hazard: 'Viscous heating', cause: 'High shear rate in a thin film of viscous liquid', mitigation: 'Check the Brinkman number; provide cooling' }],
  standards: ['ISO 3104 (kinematic viscosity of petroleum products)', 'ISO 7902 (hydrodynamic plain journal bearings under steady-state conditions)', 'ASME V&V 20 (verification and validation in computational fluid dynamics and heat transfer)'],
  limits: 'Fully developed, laminar, incompressible, Newtonian flow between infinite parallel plates with constant properties. Entrance effects, side walls and viscous heating are neglected.',
  numerics: { method: 'Crank–Nicolson finite differences for the one-dimensional momentum equation, marched in stages with fine steps through the impulsive start; while the wall layers √(νt) are thinner than a sixteenth of the gap the grid is fitted to them', order: 2, stability: 'Unconditionally stable', resolution: 'n_y' },
  optimise: { objective: 'q', sense: 'max', vars: ['h'], note: 'The pressure-driven flow rate rises as h³; leakage paths are therefore very sensitive to clearance.' },
  inverse: { series: 'history', curve: 0, fit: ['mu'] },
  extensions: ['Oscillating wall (Stokes second problem) and exact Womersley solution', 'Power-law and Bingham fluids', 'Viscous heating with temperature-dependent viscosity', 'Slowly varying gap (Reynolds equation)'],
};

export default [conduction, exchanger, rankine, refrigeration, airCar, freeEnergy, reverseOsmosis, brinePlume, scaling, reactors, flash, producedWater, waterHammer, cavity, burgers, channel];
