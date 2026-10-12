// Pipeline hydraulics, hydrodynamic slugging and hydrate formation.
import { inp, asm, eq, scalar, line, field, anim, check, bench, frictionFactor, svg, S, lab, N, C } from './kit.js';

const g = 9.80665;

// ------------------------------------------------------------------ single-phase pipeline
const pipeline = {
  id: 'pipeline-thermal-hydraulics',
  title: 'Pipeline pressure and temperature profile',
  module: 2, klass: 'I', domains: ['pipeline', 'thermal', 'cfd'],
  keywords: ['pipeline pressure drop', 'pressure drop', 'flowline', 'pipeline', 'friction factor', 'temperature profile', 'heat loss', 'u-value', 'tieback', 'arrival temperature', 'pipe flow', 'colebrook', 'darcy'],
  summary: 'Steady single-phase flow in a buried or subsea pipeline: frictional and static pressure change with heat loss to the surroundings.',
  background: [
    'A fluid moving through a pipe loses mechanical energy to wall friction and exchanges heat with its surroundings. For steady flow the momentum balance reduces to the Darcy–Weisbach relation, with the friction factor given by the laminar result 64/Re or the Colebrook–White equation in turbulent flow. The energy balance, when the overall heat-transfer coefficient is constant, gives an exponential approach of the fluid temperature to the ambient temperature.',
    'These relations are the basis of pipeline sizing, pump and compressor selection and thermal design of subsea tiebacks, where the arrival temperature decides whether wax or hydrates can form.',
  ],
  phenomena: ['Wall friction', 'Hydrostatic head', 'Convective heat loss', 'Temperature-dependent viscosity'],
  laws: ['mass', 'momentum', 'energy', 'darcy', 'fourier'],
  refs: ['Colebrook, C. F. (1939). Turbulent flow in pipes. J. Inst. Civil Engineers 11, 133–156.', 'Moody, L. F. (1944). Friction factors for pipe flow. Trans. ASME 66, 671–684.', 'Bai, Y. & Bai, Q. (2019). Subsea Engineering Handbook, 2nd ed., Gulf Professional Publishing.'],
  inputs: [
    inp('L', 'Pipeline length', 'km', 12, { min: 0.01, max: 500, kind: 'geometry', aliases: ['length', 'long', 'tieback', 'distance'] }),
    inp('D', 'Inner diameter', 'in', 8, { min: 0.5, max: 60, kind: 'geometry', aliases: ['diameter', 'bore', 'id', 'inch'] }),
    inp('eps_r', 'Wall roughness', 'mm', 0.045, { min: 0, max: 5, kind: 'geometry', aliases: ['roughness'], src: 'Commercial steel, Moody (1944)' }),
    inp('dz', 'Elevation gain, inlet to outlet', 'm', 0, { min: -3000, max: 3000, kind: 'geometry', aliases: ['elevation', 'rise', 'riser height'] }),
    inp('Q', 'Volumetric flow rate', 'm^3/h', 250, { min: 0.01, max: 50000, aliases: ['flow rate', 'flowrate', 'throughput'] }),
    inp('rho', 'Fluid density', 'kg/m^3', 850, { min: 0.5, max: 2000, kind: 'fluid', aliases: ['density'], src: 'Light crude oil at 40 °C' }),
    inp('mu', 'Dynamic viscosity at inlet temperature', 'cP', 5, { min: 0.005, max: 5000, kind: 'fluid', aliases: ['viscosity'], src: 'Light crude oil at 40 °C' }),
    inp('cp', 'Specific heat capacity', 'J/(kg K)', 2000, { min: 500, max: 15000, kind: 'fluid', aliases: ['heat capacity', 'specific heat'] }),
    inp('p_in', 'Inlet pressure', 'bar', 120, { min: 1, max: 1500, aliases: ['inlet pressure', 'wellhead pressure', 'pressure'] }),
    inp('T_in', 'Inlet temperature', '°C', 70, { min: -50, max: 300, aliases: ['inlet temperature', 'wellhead temperature'] }),
    inp('T_amb', 'Ambient (seabed or soil) temperature', '°C', 4, { min: -5, max: 60, kind: 'environment', env: 'seabed_temp', aliases: ['seabed temperature', 'ambient temperature', 'sea temperature'] }),
    inp('U', 'Overall heat-transfer coefficient (inner-area basis)', 'W/(m^2 K)', 3, { min: 0.1, max: 500, aliases: ['u-value', 'u value', 'heat transfer coefficient', 'insulation'], src: 'Wet-insulated subsea flowline, typical 2–5 W/(m² K)' }),
    inp('B_mu', 'Viscosity–temperature coefficient', 'K', 2500, { min: 0, max: 8000, kind: 'fluid', src: 'Andrade-type fit, light crude' }),
    inp('n_seg', 'Number of integration segments', '1', 200, { min: 10, max: 4000, kind: 'numerical' }),
  ],
  assumptions: [
    asm('steady', 'Flow is steady; no transients or line-packing.', { why: 'Design operating point', alt: 'Not resolved here: the steady profiles are still shown and a warning points to a transient (water-hammer or thermal cool-down) model.' }),
    asm('incompressible', 'The fluid is incompressible, so velocity is constant along the pipe.', { why: 'Liquid service', alt: 'Density follows the ideal-gas law (molar mass fixed by the inlet density), velocity rises as pressure falls and the acceleration of the gas is included in the momentum balance.' }),
    asm('const_mu', 'Viscosity is constant at its inlet value.', { why: 'Simplest closure', alt: 'Viscosity follows an Andrade law μ = μ₀·exp[B(1/T − 1/T₀)], so friction rises as the fluid cools.' }),
    asm('no_fric_heat', 'Frictional heating and Joule–Thomson effects are neglected in the energy balance.', { why: 'Small against wall heat loss for liquids', alt: 'For a liquid, viscous dissipation is added as a heat source. For an ideal gas the Joule–Thomson coefficient is zero, so friction leaves the temperature unchanged; the kinetic- and potential-energy terms are added instead.' }),
  ],
  symbols: { u: ['Mean velocity', 'm/s'], A: ['Flow area', 'm^2'], Re: ['Reynolds number', '1'], f: ['Darcy friction factor', '1'], p: ['Pressure', 'Pa'], T: ['Fluid temperature', 'K'], x: ['Distance along pipe', 'm'], mdot: ['Mass flow rate', 'kg/s'], g: ['Gravitational acceleration', 'm/s^2'], theta: ['Pipe inclination', 'rad'], T_0: ['Reference temperature', 'K'], mu_0: ['Viscosity at reference temperature', 'Pa s'], M_g: ['Molar mass', 'kg/mol'], R_u: ['Molar gas constant', 'J/(mol K)'] },
  equations: (a, v) => [
    eq('cont', 'Continuity', 'mdot', 'rho*u*A', { kind: 'law', origin: 'Conservation of mass' }),
    eq('area', 'Flow area', 'A', 'pi*D^2/4', { kind: 'definition' }),
    eq('re', 'Reynolds number', 'Re', 'rho*u*D/mu', { kind: 'definition' }),
    a.incompressible
      ? eq('mom', 'Momentum balance', 'pd(p,x)', '-f*rho*u^2/(2*D) - rho*g*sin(theta)', { kind: 'law', origin: 'Conservation of momentum (Darcy–Weisbach)', needs: ['steady', 'incompressible'] })
      : eq('mom', 'Momentum balance with gas acceleration', 'pd(p,x)', '-f*rho*u^2/(2*D) - rho*g*sin(theta) - rho*u*pd(u,x)', { kind: 'law', origin: 'Conservation of momentum (Darcy–Weisbach) for a fluid of varying density', needs: ['steady'] }),
    // the solver uses 64/Re below Re = 2000, Colebrook–White above 4000 and a linear blend of the two in between
    v && 4 * v.rho * v.Q / (Math.PI * v.D * v.mu) < 2000
      ? eq('cw', 'Laminar friction factor', 'f', '64/Re', { kind: 'law', origin: 'Hagen–Poiseuille flow; applies below a Reynolds number of 2000' })
      : eq('cw', 'Colebrook–White friction factor', '1/sqrt(f)', '-2*log10(eps_r/(3.7*D) + 2.51/(Re*sqrt(f)))', { kind: 'empirical', origin: 'Colebrook (1939) fit to Nikuradse and commercial-pipe data; blended linearly with 64/Re between Reynolds numbers of 2000 and 4000' }),
    a.no_fric_heat
      ? eq('en', 'Energy balance', 'mdot*cp*pd(T,x)', '-U*pi*D*(T - T_amb)', { kind: 'law', origin: 'First law of thermodynamics', needs: ['steady', 'no_fric_heat'] })
      : a.incompressible
        ? eq('en', 'Energy balance with viscous heating', 'mdot*cp*pd(T,x)', '-U*pi*D*(T - T_amb) + f*rho*u^3*A/(2*D)', { kind: 'law', origin: 'First law of thermodynamics for an incompressible liquid', needs: ['steady', 'incompressible'] })
        : eq('en', 'Energy balance of an ideal gas', 'mdot*cp*pd(T,x)', '-U*pi*D*(T - T_amb) - mdot*(u*pd(u,x) + g*sin(theta))', { kind: 'law', origin: 'First law of thermodynamics with enthalpy a function of temperature only', needs: ['steady'] }),
    ...(a.const_mu ? [] : [eq('visc', 'Andrade viscosity law', 'mu', 'mu_0*exp(B_mu*(1/T - 1/T_0))', { kind: 'closure', origin: 'Andrade (1930) empirical liquid-viscosity relation' })]),
    ...(a.incompressible ? [] : [eq('eos', 'Ideal-gas density', 'rho', 'p*M_g/(R_u*T)', { kind: 'closure', origin: 'Ideal-gas equation of state' })]),
  ],
  derivation: a => [
    { text: 'Take a control volume of length dx. In steady flow the mass flow rate is the same through every cross-section.', tex: '\\dot m = \\rho\\,u\\,A = \\text{const}' },
    { text: 'Balance pressure force, wall shear and weight along the pipe axis. Writing the wall shear with the Darcy friction factor gives the pressure gradient.', tex: '\\frac{\\partial p}{\\partial x} = -\\frac{f\\,\\rho\\,u^2}{2D} - \\rho\\,g\\,\\sin\\theta' },
    { text: 'The enthalpy carried by the flow changes only by heat exchanged through the wall' + (a.no_fric_heat ? '.' : a.incompressible ? ' and by viscous dissipation.' : ' and by the small exchange with kinetic and potential energy.'), tex: '\\dot m\\,c_p\\,\\frac{\\partial T}{\\partial x} = -U\\,\\pi D\\,(T-T_{amb})' },
    { text: 'With constant U and c_p this integrates to an exponential decay toward ambient temperature over the thermal length ℓ = ṁ c_p/(U π D).', tex: 'T(x) = T_{amb} + (T_{in}-T_{amb})\\,e^{-x/\\ell}' },
  ],
  solve(v, a) {
    const A = Math.PI * v.D ** 2 / 4, n = Math.round(v.n_seg), dx = v.L / n, sinT = N.clamp(v.dz / v.L, -1, 1);
    const mdot = v.rho * v.Q, x = [0], p = [v.p_in], T = [v.T_in], fs = [], Res = [];
    const Mg = v.rho * C.R_u * v.T_in / v.p_in; // molar mass consistent with inlet density (compressible branch)
    let warnings = [], dpFric = 0, srcInt = 0, wallInt = 0, dudx = 0, machMax = 0;
    for (let i = 0; i < n; i++) {
      const Ti = T[i], pi = Math.max(p[i], 1);
      const rho = a.incompressible ? v.rho : pi * Mg / (C.R_u * Ti);
      const u = mdot / (rho * A);
      const mu = a.const_mu ? v.mu : v.mu * Math.exp(v.B_mu * (1 / Ti - 1 / v.T_in));
      const Re = rho * u * v.D / mu, f = frictionFactor(Re, v.eps_r / v.D);
      fs.push(f); Res.push(Re);
      const fric = f * rho * u * u / (2 * v.D);
      // liquid: viscous dissipation heats the fluid; ideal gas: enthalpy depends on temperature only, so the
      // source is the exchange with kinetic and potential energy (velocity gradient taken from the previous segment)
      const qf = a.no_fric_heat ? 0 : a.incompressible ? fric * u * A : -mdot * (u * dudx + g * sinT);
      // exact exponential step for the linear energy equation keeps the scheme unconditionally stable
      const ell = mdot * v.cp / (v.U * Math.PI * v.D), Teq = v.T_amb + qf / (v.U * Math.PI * v.D);
      const Tn = Teq + (Ti - Teq) * Math.exp(-dx / ell);
      let dpdx = -fric - rho * g * sinT;
      if (!a.incompressible) {
        // rho u du/dx = rho u^2 (T'/T − p'/p) for an ideal gas at constant mass flux
        const m2 = rho * u * u / pi; machMax = Math.max(machMax, m2);
        dpdx = (dpdx - rho * u * u * (Tn - Ti) / (dx * Ti)) / Math.max(1 - m2, 0.05);
        dudx = u * ((Tn - Ti) / (dx * Ti) - dpdx / pi);
      }
      // wall heat over the segment, integrated exactly along the exponential profile
      dpFric += fric * dx; srcInt += qf * dx; wallInt += v.U * Math.PI * v.D * ((Teq - v.T_amb) * dx + (Ti - Teq) * ell * -Math.expm1(-dx / ell));
      T.push(Tn); p.push(p[i] + dpdx * dx); x.push((i + 1) * dx);
    }
    const pOut = p[n], u0 = mdot / (v.rho * A);
    if (pOut <= 0) warnings.push('The computed outlet pressure is not positive: this flow rate cannot be delivered with the stated inlet pressure.');
    if (machMax > 0.5) warnings.push('The gas velocity approaches the isothermal speed of sound: the flow is close to choking and the marching solution is unreliable there.');
    if (Math.abs(v.dz) > v.L) warnings.push('The elevation change exceeds the pipe length; the inclination has been limited to vertical.');
    if (!a.steady) warnings.push('Transient behaviour is not resolved by this model: the profiles shown are the steady state. Use a water-hammer model for pressure surges or a cool-down model for shut-in.');
    const ell = mdot * v.cp / (v.U * Math.PI * v.D);
    const heatLoss = mdot * v.cp * (v.T_in - T[n]);
    const fr = N.mean(fs), dpF = dpFric;
    return {
      scalars: [
        scalar('u', 'Mean velocity at inlet', u0, 'm/s'), scalar('Re', 'Reynolds number at inlet', Res[0], '1', { note: Res[0] < 2000 ? 'laminar' : Res[0] < 4000 ? 'transitional' : 'turbulent' }),
        scalar('f', 'Darcy friction factor (mean)', fr, '1'), scalar('p_out', 'Outlet pressure', pOut, 'Pa', { show: 'bar' }),
        scalar('dp', 'Total pressure drop', v.p_in - pOut, 'Pa', { show: 'bar' }), scalar('dp_f', 'Frictional pressure drop', dpF, 'Pa', { show: 'bar' }),
        scalar('T_out', 'Arrival temperature', T[n], 'K', { show: '°C' }), scalar('ell', 'Thermal decay length', ell, 'm', { show: 'km' }),
        scalar('Q_loss', 'Heat lost to surroundings', heatLoss, 'W', { show: 'kW' }), scalar('P_pump', 'Hydraulic power for the pressure drop (inlet volume flow)', (v.p_in - pOut) * v.Q, 'W', { show: 'kW' }),
      ],
      series: [
        line('p-profile', 'Pressure along the pipeline', 'Distance', 'km', x.map(s => s / 1000), [{ label: 'Pressure', data: p.map(s => s / 1e5) }], 'Pressure', 'bar'),
        line('T-profile', 'Temperature along the pipeline', 'Distance', 'km', x.map(s => s / 1000), [{ label: 'Fluid', data: T.map(s => s - 273.15) }, { label: 'Ambient', data: x.map(() => v.T_amb - 273.15), dash: true }], 'Temperature', '°C'),
      ],
      checks: [
        check('Energy balance residual', (heatLoss + srcInt - wallInt) / Math.max(Math.abs(heatLoss), Math.abs(srcInt), Math.abs(wallInt), 1), 1e-9, 'Enthalpy lost by the fluid plus internal heating against the wall heat flux integrated along the profile'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const r = this.solve(v, a), get = s => r.scalars.find(q => q.sym === s).value, out = [];
    if (a.no_fric_heat) {
      const ell = v.rho * v.Q * v.cp / (v.U * Math.PI * v.D);
      out.push(bench('Arrival temperature vs exact exponential solution', get('T_out'), v.T_amb + (v.T_in - v.T_amb) * Math.exp(-v.L / ell), 'Analytical solution of the linear energy equation', 1e-6));
    }
    if (a.incompressible && a.const_mu) {
      const A = Math.PI * v.D ** 2 / 4, u = v.Q / A, f = frictionFactor(v.rho * u * v.D / v.mu, v.eps_r / v.D);
      out.push(bench('Pressure drop vs closed-form Darcy–Weisbach', get('dp'), f * v.L / v.D * v.rho * u * u / 2 + v.rho * g * v.dz, 'Darcy–Weisbach with Colebrook–White', 1e-6));
    }
    out.push(bench('Laminar friction factor f·Re at Re = 1000', frictionFactor(1000) * 1000, 64, 'Hagen–Poiseuille exact solution', 1e-12));
    {
      // isothermal ideal-gas flow in a horizontal pipe: p1² − p2² = G²(R T/M)[f L/D + 2 ln(p1/p2)], G = mass flux
      const gv = { ...v, rho: 50, mu: 1.2e-5, p_in: 6e6, T_in: 290, T_amb: 290, D: 0.3, L: 20000, dz: 0, Q: 0.6, eps_r: 4.5e-5, n_seg: 2000 };
      const rg = this.solve(gv, { steady: true, incompressible: false, const_mu: true, no_fric_heat: true }), ff = rg.scalars.find(q => q.sym === 'f').value;
      const G = gv.rho * gv.Q / (Math.PI * gv.D ** 2 / 4), rt = gv.p_in / gv.rho;
      const p2 = N.bisect(q => gv.p_in ** 2 - q * q - G * G * rt * (ff * gv.L / gv.D + 2 * Math.log(gv.p_in / q)), 0.2 * gv.p_in, gv.p_in, 1e-13);
      out.push(bench('Isothermal gas flow: outlet pressure vs closed-form solution', rg.scalars.find(q => q.sym === 'p_out').value, p2, 'p₁² − p₂² = G²(RT/M)[fL/D + 2 ln(p₁/p₂)], exact for isothermal ideal-gas flow', 2e-3));
    }
    return out;
  },
  validation: [
    { name: 'Smooth-pipe turbulent friction factor', ref: 'Nikuradse, J. (1932) VDI-Forschungsheft 356, smooth-pipe measurements; tabulated in Schlichting, Boundary-Layer Theory', note: 'Friction factor only; independent of the thermal model.',
      cases: [
        { label: 'Re = 1.0×10⁵', inputs: { rho: 1000, mu: 1e-3, D: 0.1, Q: Math.PI * 0.0025 * 1.0, eps_r: 0, L: 100, dz: 0 }, observable: 'f', observed: 0.0180, sigma: 0.0004 },
        { label: 'Re = 1.0×10⁶', inputs: { rho: 1000, mu: 1e-3, D: 0.1, Q: Math.PI * 0.0025 * 10.0, eps_r: 0, L: 100, dz: 0 }, observable: 'f', observed: 0.0116, sigma: 0.0003 },
      ] },
  ],
  diagram(v) {
    const y0 = 120, y1 = 120 - Math.max(-70, Math.min(70, v.dz / Math.max(v.L, 1) * 4000));
    return svg(`
      ${S.path(`M60 ${y0 + 150} L60 ${y0 + 190} L580 ${y0 + 190} L580 ${y0 + 150}`, 'd-ground')}
      ${S.path(`M60 ${y0 + 40} L580 ${y1 + 40}`, 'd-pipe')}
      ${S.arrow(70, y0 + 16, 150, y0 + 16 + (y1 - y0) * 0.15)} ${S.text(110, y0 + 4, 'flow Q')}
      ${S.text(60, y0 + 76, `inlet  ${lab(v.p_in / 1e5, 'bar')}, ${lab(v.T_in - 273.15, '°C')}`, 'd-text', 'start')}
      ${S.text(580, y1 + 76, 'outlet', 'd-text', 'end')}
      ${[0, 1, 2, 3].map(i => S.arrow(160 + i * 110, y0 + 52 + (y1 - y0) * (0.2 + 0.2 * i), 160 + i * 110, y0 + 92 + (y1 - y0) * (0.2 + 0.2 * i), 'd-arrow d-heat')).join('')}
      ${S.text(320, y0 + 122, `heat loss to surroundings at ${lab(v.T_amb - 273.15, '°C')},  U = ${lab(v.U, 'W/m²K')}`)}
      ${S.dim(60, 40, 580, 40, `L = ${lab(v.L / 1000, 'km')}   D = ${lab(v.D * 1000, 'mm')}`)}
    `);
  },
  experiment: {
    objective: 'Measure pressure drop and temperature decay along an instrumented flow loop and compare with the Darcy–Weisbach and exponential-cooling predictions.',
    apparatus: ['Closed flow loop with a straight test section at least 100 diameters long', 'Variable-speed pump', 'Jacketed section or water bath to impose a controlled ambient temperature', 'Upstream flow conditioner'],
    instruments: [{ name: 'Differential pressure transmitter', measures: 'Pressure drop across the test section', range: '0–2 bar', resolution: '±0.075 % of span' }, { name: 'Coriolis flow meter', measures: 'Mass flow rate and density', range: '0–50 kg/s', resolution: '±0.1 %' }, { name: 'RTD probes (Pt100, class A)', measures: 'Fluid temperature at inlet, mid-point and outlet', range: '−50 to 250 °C', resolution: '±0.15 K' }],
    procedure: ['Circulate until temperatures are steady to within 0.1 K over ten minutes.', 'Record differential pressure, flow rate and temperatures at each of at least eight flow rates spanning laminar to fully turbulent flow.', 'Repeat with the jacket at a second ambient temperature to separate hydraulic and thermal effects.'],
    controls: ['Isothermal run (jacket at fluid temperature) isolates friction from heat loss.', 'Zero-flow reading establishes transmitter offset.'],
    signatures: ['f·Re = 64 in laminar flow', 'Friction factor falling as Re^−0.25 at moderate turbulent Reynolds number', 'ln[(T−T_amb)/(T_in−T_amb)] linear in distance'],
    safety: ['Pressure-relief device set below the rating of the weakest component', 'Guarding and insulation on hot surfaces above 60 °C'],
  },
  falsify: ['A measured friction factor outside the Colebrook–White band by more than the combined uncertainty at the same Reynolds number and roughness.', 'A temperature profile that is not exponential in distance when U and c_p are constant.'],
  alternatives: [{ name: 'Haaland explicit friction factor', text: 'An explicit approximation to Colebrook–White, within about 2 % over the Moody range.' }, { name: 'Drag-reducing flow', text: 'Polymer additives lower turbulent friction below the Colebrook value; the Virk asymptote then bounds the friction factor.' }],
  hazards: [{ hazard: 'Over-pressure', cause: 'Blocked outlet or surge', mitigation: 'Relief system and high-pressure trip' }, { hazard: 'Wax or hydrate blockage', cause: 'Arrival temperature below the appearance temperature', mitigation: 'Insulation, inhibitor injection or heating' }],
  standards: ['ASME B31.4 / B31.8 (liquid and gas pipelines)', 'DNV-ST-F101 (submarine pipeline systems)', 'API RP 14E (sizing of offshore production piping)'],
  limits: 'Single-phase Newtonian flow in a circular pipe with fully developed profile. Not valid for multiphase flow, strongly non-Newtonian fluids, or near the critical point of a gas.',
  numerics: { method: 'Marching integration in distance: explicit for pressure, exact exponential update for temperature', order: 1, stability: 'Unconditionally stable for the thermal update', resolution: 'n_seg' },
  optimise: { objective: 'dp', sense: 'min', vars: ['D'], note: 'Pressure drop falls roughly as D⁻⁵; in practice minimise total installed cost instead.' },
  inverse: { series: 'p-profile', fit: ['eps_r', 'mu'] },
  extensions: ['Couple to a multiphase model when gas breaks out', 'Add a transient cool-down analysis after shut-in', 'Include buried-pipe soil resistance in the U-value'],
};

// ------------------------------------------------------------------ slug flow
function stratified(v, vsl, vsg) {
  const D = v.D, A = Math.PI * D * D / 4, th = v.theta;
  const geom = h => {
    const c = 2 * h - 1, ac = Math.acos(c), sq = Math.sqrt(Math.max(0, 1 - c * c));
    const AL = D * D * 0.25 * (Math.PI - ac + c * sq), AG = A - AL, SL = D * (Math.PI - ac), SG = D * ac, Si = D * sq;
    return { AL, AG, SL, SG, Si };
  };
  const fan = Re => (Re < 2000 ? 16 / Math.max(Re, 1e-9) : 0.046 * Math.pow(Re, -0.2));
  const resid = h => {
    const q = geom(h), uL = vsl * A / q.AL, uG = vsg * A / q.AG;
    const fL = fan(v.rho_l * uL * (4 * q.AL / q.SL) / v.mu_l), fG = fan(v.rho_g * uG * (4 * q.AG / (q.SG + q.Si)) / v.mu_g);
    const tL = fL * v.rho_l * uL * uL / 2, tG = fG * v.rho_g * uG * uG / 2, ti = fG * v.rho_g * (uG - uL) * Math.abs(uG - uL) / 2;
    return tG * q.SG / q.AG - tL * q.SL / q.AL + ti * q.Si * (1 / q.AL + 1 / q.AG) - (v.rho_l - v.rho_g) * g * Math.sin(th);
  };
  let lo = 1e-4, hi = 1 - 1e-4, h = 0.5;
  // with no sign change the net force on the liquid has one sign at every level: positive thins the layer, negative thickens it
  if (resid(lo) * resid(hi) < 0) h = N.bisect(resid, lo, hi, 1e-10); else h = resid(0.5) > 0 ? lo : hi;
  const q = geom(h), uL = vsl * A / q.AL, uG = vsg * A / q.AG;
  const kh = (1 - h) * Math.sqrt((v.rho_l - v.rho_g) * g * Math.cos(th) * q.AG / (v.rho_g * Math.max(q.Si, 1e-12)));
  const fL = fan(v.rho_l * uL * (4 * q.AL / q.SL) / v.mu_l);
  const disp = Math.sqrt(4 * q.AG * g * Math.cos(th) * (1 - v.rho_g / v.rho_l) / (Math.max(q.Si, 1e-12) * fL));
  // 0 stratified, 1 slug / intermittent, 2 annular, 3 dispersed bubble (Taitel & Dukler 1976; the intermittent–annular
  // boundary is taken at h/D = 0.35, the later revision by Barnea and co-workers of the original value of 0.5)
  const regime = uG < kh ? 0 : (h > 0.5 && uL > disp ? 3 : h > 0.35 ? 1 : 2);
  return { h, uL, uG, kh, regime };
}
const REGIMES = ['Stratified', 'Slug (intermittent)', 'Annular', 'Dispersed bubble'];

const slug = {
  id: 'hydrodynamic-slug-flow',
  title: 'Hydrodynamic slugging in a flowline',
  module: 2, klass: 'I', domains: ['multiphase', 'pipeline', 'offshore'],
  keywords: ['hydrodynamic slug', 'slug flow', 'slugging', 'slug frequency', 'slug length', 'slugs', 'slug', 'liquid holdup', 'two-phase flow', 'gas-liquid', 'flow regime', 'multiphase', 'slug load', 'taylor bubble', 'drift flux'],
  summary: 'Flow-regime prediction and slug characteristics (frequency, length, velocity, holdup, pressure gradient, bend loads) for gas–liquid flow in a near-horizontal pipe.',
  background: [
    'When gas and liquid flow together in a near-horizontal pipe at moderate rates, waves on the stratified liquid layer can grow until they bridge the pipe. The resulting liquid slugs travel at roughly the mixture velocity, separated by long gas bubbles riding over a slower liquid film. Slugging produces large fluctuations in pressure, liquid arrival rate and structural load.',
    'The transition from stratified flow is described mechanistically by the Kelvin–Helmholtz criterion of Taitel and Dukler; slug translational velocity by the drift-flux relation of Nicklin and Bendiksen; slug-body holdup and frequency by widely used correlations of Gregory and co-workers.',
  ],
  phenomena: ['Kelvin–Helmholtz interfacial instability', 'Taylor-bubble drift', 'Liquid pickup and shedding', 'Intermittent pressure loading'],
  laws: ['mass', 'momentum'],
  refs: ['Taitel, Y. & Dukler, A. E. (1976). A model for predicting flow regime transitions in horizontal and near horizontal gas–liquid flow. AIChE J. 22, 47–55.', 'Bendiksen, K. H. (1984). An experimental investigation of the motion of long bubbles in inclined tubes. Int. J. Multiphase Flow 10, 467–483.', 'Gregory, G. A. & Scott, D. S. (1969). Correlation of liquid slug velocity and frequency in horizontal cocurrent gas–liquid slug flow. AIChE J. 15, 933–935.', 'Gregory, G. A., Nicholson, M. K. & Aziz, K. (1978). Correlation of the liquid volume fraction in the slug for horizontal gas–liquid slug flow. Int. J. Multiphase Flow 4, 33–39.', 'Benjamin, T. B. (1968). Gravity currents and related phenomena. J. Fluid Mech. 31, 209–248.'],
  inputs: [
    inp('D', 'Pipe inner diameter', 'in', 8, { min: 1, max: 48, kind: 'geometry', aliases: ['diameter', 'bore', 'inch'] }),
    inp('L', 'Flowline length', 'km', 5, { min: 0.05, max: 200, kind: 'geometry', aliases: ['length', 'long'] }),
    inp('theta', 'Inclination (positive upward)', 'deg', 0, { min: -10, max: 30, kind: 'geometry', aliases: ['inclination', 'incline', 'angle'] }),
    inp('v_sl', 'Superficial liquid velocity', 'm/s', 0.8, { min: 0.01, max: 8, aliases: ['superficial liquid', 'liquid velocity'] }),
    inp('v_sg', 'Superficial gas velocity', 'm/s', 3.0, { min: 0.05, max: 40, aliases: ['superficial gas', 'gas velocity'] }),
    inp('rho_l', 'Liquid density', 'kg/m^3', 850, { min: 500, max: 1400, kind: 'fluid', aliases: ['liquid density', 'oil density'] }),
    inp('rho_g', 'Gas density at line conditions', 'kg/m^3', 50, { min: 0.5, max: 400, kind: 'fluid', aliases: ['gas density'], src: 'Lean natural gas near 60 bar, 20 °C' }),
    inp('mu_l', 'Liquid viscosity', 'cP', 5, { min: 0.2, max: 2000, kind: 'fluid', aliases: ['liquid viscosity', 'oil viscosity'] }),
    inp('mu_g', 'Gas viscosity', 'cP', 0.013, { min: 0.005, max: 0.1, kind: 'fluid', aliases: ['gas viscosity'] }),
    inp('n_ls', 'Slug length in pipe diameters', '1', 32, { min: 8, max: 300, kind: 'fluid', src: 'Stable slug length 12–40 D for small and medium pipes; Dukler & Hubbard (1975), Nicholson et al. (1978)' }),
    inp('p_out', 'Outlet (separator) pressure', 'bar', 30, { min: 1, max: 300, aliases: ['separator pressure', 'outlet pressure'] }),
  ],
  assumptions: [
    asm('developed', 'Slug flow is fully developed: slugs neither grow nor decay along the line.', { why: 'Long line, steady inlet rates', alt: 'Not resolved here: the developed-flow values are still shown and a warning points to slug-tracking or transient two-fluid simulation.' }),
    asm('bendiksen', 'Bubble translational velocity follows the Bendiksen (1984) drift-flux relation.', { why: 'Measured in inclined tubes over a wide range', alt: 'The simpler Nicklin value v_t = 1.2 v_m is used with no drift term.' }),
    asm('gregory_holdup', 'Slug-body liquid holdup follows Gregory, Nicholson & Aziz (1978).', { why: 'Widely used closure', alt: 'The slug body is treated as unaerated (holdup = 1).' }),
    asm('incomp', 'Phase densities are constant along the line.', { why: 'Moderate pressure drop relative to line pressure', alt: 'Not resolved here: the stated velocities are taken as outlet values and a warning reports how much smaller the gas volume flow is at the inlet pressure.' }),
  ],
  symbols: { v_m: ['Mixture velocity', 'm/s'], v_t: ['Slug translational velocity', 'm/s'], C_0: ['Distribution coefficient', '1'], v_d: ['Drift velocity', 'm/s'], H_ls: ['Slug-body liquid holdup', '1'], H_l: ['Mean liquid holdup', '1'], f_s: ['Slug frequency', '1/s'], L_s: ['Slug length', 'm'], L_u: ['Slug-unit length', 'm'], g: ['Gravitational acceleration', 'm/s^2'], F_b: ['Peak force on a 90° bend', 'N'], A: ['Pipe area', 'm^2'], rho_s: ['Slug-body density', 'kg/m^3'], v_ref: ['Reference velocity 8.66 m/s', 'm/s'], f_ref: ['Reference frequency 1 Hz', '1/s'], v_c: ['Reference velocity, v_c² = 19.75 m²/s²', 'm/s'], u_G: ['Gas velocity in stratified flow', 'm/s'], h_L: ['Liquid level over diameter', '1'], A_G: ['Gas flow area', 'm^2'], S_i: ['Interface width', 'm'] },
  equations: (a, v) => {
    // Bendiksen (1984) gives two branches, switching at a mixture Froude number v_m/sqrt(g D) of 3.5
    const lowFr = !v || (v.v_sl + v.v_sg) / Math.sqrt(g * v.D) < 3.5;
    return [
    eq('vm', 'Mixture velocity', 'v_m', 'v_sl + v_sg', { kind: 'law', origin: 'Conservation of volume for incompressible phases', needs: ['incomp'] }),
    a.bendiksen
      ? eq('vt', 'Translational velocity', 'v_t', 'C_0*v_m + v_d', { kind: 'closure', origin: 'Drift-flux relation; Nicklin (1962), Bendiksen (1984)' })
      : eq('vt', 'Translational velocity', 'v_t', '1.2*v_m', { kind: 'closure', origin: 'Nicklin et al. (1962)' }),
    ...(a.bendiksen ? [
      lowFr ? eq('c0', 'Distribution coefficient (Froude number below 3.5)', 'C_0', '1.05 + 0.15*sin(theta)^2', { kind: 'empirical', origin: 'Bendiksen (1984)' })
        : eq('c0', 'Distribution coefficient (Froude number of 3.5 or more)', 'C_0', '1.2', { kind: 'empirical', origin: 'Bendiksen (1984)' }),
      lowFr ? eq('vd', 'Drift velocity (Froude number below 3.5)', 'v_d', '0.54*sqrt(g*D)*cos(theta) + 0.35*sqrt(g*D)*sin(theta)', { kind: 'closure', origin: 'Benjamin (1968) horizontal and Dumitrescu (1943) vertical limits, combined by Bendiksen (1984)' })
        : eq('vd', 'Drift velocity (Froude number of 3.5 or more)', 'v_d', '0.35*sqrt(g*D)*sin(theta)', { kind: 'closure', origin: 'Bendiksen (1984): the horizontal drift term vanishes at high mixture velocity' })] : []),
    a.gregory_holdup
      ? eq('hls', 'Slug-body holdup', 'H_ls', '1/(1 + (v_m/v_ref)^1.39)', { kind: 'empirical', origin: 'Gregory, Nicholson & Aziz (1978); v_ref = 8.66 m/s' })
      : eq('hls', 'Slug-body holdup', 'H_ls', '1', { kind: 'closure', origin: 'Unaerated slug idealisation' }),
    eq('fs', 'Slug frequency', 'f_s/f_ref', '0.0226*(v_sl/(g*D)*(v_c^2/v_m + v_m))^1.2', { kind: 'empirical', origin: 'Gregory & Scott (1969), SI form; v_c² = 19.75 m²/s², f_ref = 1 Hz' }),
    eq('ls', 'Slug length', 'L_s', 'n_ls*D', { kind: 'empirical', origin: 'Observed stable slug length' }),
    eq('lu', 'Slug-unit length', 'L_u', 'v_t/f_s', { kind: 'derived', origin: 'Kinematics of a periodic slug train', needs: ['developed'] }),
    eq('hl', 'Mean liquid holdup', 'H_l', '1 - v_sg/v_t', { kind: 'derived', origin: 'Drift-flux gas continuity: the gas travels at the translational velocity' }),
    eq('kh', 'Stratified-to-intermittent transition', 'u_G', '(1 - h_L)*sqrt((rho_l - rho_g)*g*cos(theta)*A_G/(rho_g*S_i))', { kind: 'derived', origin: 'Kelvin–Helmholtz stability of a finite wave; Taitel & Dukler (1976)' }),
    eq('fb', 'Peak slug force on a 90° bend', 'F_b', 'sqrt(2)*rho_s*A*v_t^2', { kind: 'law', origin: 'Momentum flux change through a bend', needs: ['developed'] }),
    ];
  },
  derivation: () => [
    { text: 'For incompressible phases the total volumetric flux through any cross-section is the sum of the superficial velocities.', tex: 'v_m = v_{sl} + v_{sg}' },
    { text: 'A long gas bubble moves faster than the mean flow because it travels in the fast central region of the liquid ahead (factor C₀) and because buoyancy drives it relative to the liquid (drift v_d).', tex: 'v_t = C_0\\,v_m + v_d' },
    { text: 'Gas continuity in a frame moving with the bubbles gives the mean void fraction and hence the liquid holdup.', tex: 'H_l = 1 - \\frac{v_{sg}}{C_0 v_m + v_d}' },
    { text: 'A stratified layer is unstable when the Bernoulli suction over a wave crest exceeds the restoring weight of the wave. For a wave of finite amplitude in a pipe this gives the Taitel–Dukler criterion.', tex: 'u_G > \\left(1-\\tilde h_L\\right)\\sqrt{\\frac{(\\rho_l-\\rho_g)\\,g\\cos\\theta\\,A_G}{\\rho_g\\,S_i}}' },
    { text: 'Slugs passing a fixed point at frequency f_s and speed v_t are spaced one slug-unit length apart.', tex: 'L_u = v_t / f_s' },
    { text: 'When a slug of density ρ_s turns through 90°, the momentum flux ρ_s A v_t² is redirected; the resultant on the bend is √2 times that flux.', tex: 'F_b = \\sqrt2\\,\\rho_s A\\,v_t^2' },
  ],
  solve(v, a, o = {}) {
    const D = v.D, A = Math.PI * D * D / 4, vm = v.v_sl + v.v_sg, sgD = Math.sqrt(g * D), th = v.theta;
    const Fr = vm / sgD;
    let C0 = 1.2, vd = 0;
    if (a.bendiksen) {
      if (Fr < 3.5) { C0 = 1.05 + 0.15 * Math.sin(th) ** 2; vd = 0.54 * sgD * Math.cos(th) + 0.35 * sgD * Math.sin(th); }
      else { C0 = 1.2; vd = 0.35 * sgD * Math.sin(th); }
    }
    const vt = C0 * vm + vd;
    const Hls = a.gregory_holdup ? 1 / (1 + Math.pow(vm / 8.66, 1.39)) : 1;
    const fsOf = (vsl, vmm) => 0.0226 * Math.pow(vsl / (g * D) * (19.75 / vmm + vmm), 1.2);
    const fs = fsOf(v.v_sl, vm), Ls = v.n_ls * D, Lu = vt / fs;
    const Hl = N.clamp(1 - v.v_sg / vt, 0.01, 0.999);
    const rhoS = Hls * v.rho_l + (1 - Hls) * v.rho_g, rhoM = Hl * v.rho_l + (1 - Hl) * v.rho_g;
    const muS = Hls * v.mu_l + (1 - Hls) * v.mu_g;
    const fD = frictionFactor(rhoS * vm * D / muS, 0.045e-3 / D);
    const beta = N.clamp(Ls / Lu, 0, 1);
    const dpdx = beta * fD * rhoS * vm * vm / (2 * D) + rhoM * g * Math.sin(th);
    const st = stratified(v, v.v_sl, v.v_sg);
    const Fb = Math.SQRT2 * rhoS * A * vt * vt;
    const dpSlug = fD * rhoS * vm * vm / (2 * D) * Ls;
    const warnings = [];
    if (st.regime !== 1) warnings.push(`The Taitel–Dukler map places this operating point in ${REGIMES[st.regime].toLowerCase()} flow, not slug flow. The slug quantities below describe what slugging would look like if it occurred; treat them as indicative.`);
    if (Ls > Lu) warnings.push('The correlated slug length exceeds the slug-unit length: frequency and length correlations disagree here, a sign the point lies near the edge of their data range.');
    if (!a.developed) warnings.push('Slug growth and decay along the line are not resolved: the values shown are those of a developed slug train. Use slug-tracking or a transient two-fluid simulation for developing flow.');
    if (!a.incomp) { const pIn = v.p_out + Math.max(dpdx * v.L, 0); warnings.push(`Gas expansion along the line is not resolved. With the stated velocities taken at the outlet, the gas volume flow at the inlet pressure of ${lab(pIn / 1e5, 'bar')} is about ${lab(100 * v.p_out / pIn, '%')} of its outlet value, so slugs accelerate toward the outlet.`); }

    // sweeps
    const vsgs = N.logspace(0.2, 20, 60);
    const fsweep = vsgs.map(x => fsOf(v.v_sl, v.v_sl + x)), hsweep = vsgs.map(x => { const m = v.v_sl + x; const f3 = m / sgD < 3.5; const c = a.bendiksen ? (f3 ? 1.05 + 0.15 * Math.sin(th) ** 2 : 1.2) : 1.2; const d = a.bendiksen ? (f3 ? 0.54 * sgD * Math.cos(th) + 0.35 * sgD * Math.sin(th) : 0.35 * sgD * Math.sin(th)) : 0; return N.clamp(1 - x / (c * m + d), 0, 1); });
    // regime map
    const nx = o.light ? 2 : 34, ny = o.light ? 2 : 30, gx = N.logspace(0.05, 40, nx), gy = N.logspace(0.01, 8, ny);
    const map = gy.map(sl => gx.map(sg => stratified(v, sl, sg).regime));
    // slug train animation: holdup along a 40-unit window
    const xw = N.linspace(0, Math.min(v.L, 6 * Lu), 300), film = N.clamp((Hl - beta * Hls) / Math.max(1 - beta, 1e-6), 0.02, Hls);
    const T = Lu / vt, times = N.linspace(0, 2 * T, 48);
    const frames = times.map(t => xw.map(x => { const s = (((x - vt * t) % Lu) + Lu) % Lu; return s < Math.min(Ls, 0.95 * Lu) ? Hls : film; }));
    const tt = N.linspace(0, 6 * T, 400);
    const pOut = tt.map(t => { const s = ((vt * t) % Lu); return v.p_out / 1e5 + (s < Math.min(Ls, 0.95 * Lu) ? dpSlug / 1e5 * (1 - s / Math.max(Ls, 1e-9)) : 0); });
    return {
      scalars: [
        scalar('regime', 'Predicted flow regime', st.regime, '1', { text: REGIMES[st.regime] }),
        scalar('v_m', 'Mixture velocity', vm, 'm/s'), scalar('v_t', 'Slug translational velocity', vt, 'm/s'), scalar('C_0', 'Distribution coefficient', C0, '1'),
        scalar('H_ls', 'Slug-body liquid holdup', Hls, '1'), scalar('H_l', 'Mean liquid holdup', Hl, '1'),
        scalar('f_s', 'Slug frequency', fs, '1/s', { show: '1/min' }), scalar('L_s', 'Slug length', Ls, 'm'), scalar('L_u', 'Slug-unit length', Lu, 'm'),
        scalar('V_s', 'Liquid volume per slug', Hls * A * Ls, 'm^3'), scalar('dpdx', 'Mean pressure gradient', dpdx, 'Pa/m'),
        scalar('dp', 'Pressure drop over the line', dpdx * v.L, 'Pa', { show: 'bar' }), scalar('dp_slug', 'Pressure pulse per slug', dpSlug, 'Pa', { show: 'bar' }),
        scalar('F_b', 'Peak force on a 90° bend', Fb, 'N', { show: 'kN' }), scalar('h_L', 'Equilibrium stratified level h/D', st.h, '1'),
        scalar('n_slugs', 'Slugs in the line at any instant', v.L / Lu, '1'),
      ],
      series: [
        line('freq-sweep', 'Slug frequency against gas rate', 'Superficial gas velocity', 'm/s', vsgs, [{ label: 'Slug frequency', data: fsweep.map(x => x * 60) }], 'Frequency', '1/min', { logx: true }),
        line('holdup-sweep', 'Mean liquid holdup against gas rate', 'Superficial gas velocity', 'm/s', vsgs, [{ label: 'Liquid holdup', data: hsweep }], 'Holdup', '–', { logx: true }),
        line('p-outlet', 'Pressure upstream of the outlet as slugs arrive', 'Time', 's', tt, [{ label: 'Pressure', data: pOut }], 'Pressure', 'bar'),
      ],
      fields: [field('regime-map', 'Flow-regime map (Taitel–Dukler)', map, [Math.log10(0.05), Math.log10(40), Math.log10(0.01), Math.log10(8)], 'log₁₀ superficial gas velocity (m/s)', 'log₁₀ superficial liquid velocity (m/s)', 'regime', { categories: REGIMES, marker: [Math.log10(v.v_sg), Math.log10(v.v_sl)] })],
      anims: [anim('slug-train', 'Liquid holdup along the line', 'Distance', 'm', xw, frames, times, 'Liquid holdup', '–', { yRange: [0, 1], fill: true })],
      checks: [
        check('Gas volume balance', (v.v_sg - (1 - Hl) * vt) / v.v_sg, 1e-9, 'Superficial gas velocity against void fraction × bubble velocity'),
        check('Holdup within physical bounds', Hl < 0 || Hl > 1 ? 1 : 0, 0, '0 ≤ H_l ≤ 1'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const sgD = Math.sqrt(g * v.D), out = [];
    if (a.bendiksen) {
      const r0 = this.solve({ ...v, v_sl: 1e-9, v_sg: 1e-9, theta: 0 }, a).scalars.find(s => s.sym === 'v_t').value;
      out.push(bench('Horizontal bubble drift vs inviscid theory', r0 / sgD, 0.542, 'Benjamin (1968): v = 0.542 √(gD)', 0.01));
      const r1 = this.solve({ ...v, v_sl: 1e-9, v_sg: 1e-9, theta: Math.PI / 2 }, a).scalars.find(s => s.sym === 'v_t').value;
      out.push(bench('Vertical Taylor-bubble rise vs potential-flow theory', r1 / sgD, 0.351, 'Dumitrescu (1943): v = 0.351 √(gD)', 0.01));
    }
    const half = this.solve({ ...v, v_sl: 2.66, v_sg: 6 }, { ...a, gregory_holdup: true }).scalars.find(s => s.sym === 'H_ls').value;
    out.push(bench('Slug-body holdup at a mixture velocity of 8.66 m/s', half, 0.5, 'Gregory, Nicholson & Aziz (1978): the correlation passes through one half at its reference velocity', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    const xs = [70, 250, 430];
    return svg(`
      ${S.rect(40, 130, 560, 80, 'd-pipe-fill', 6)}
      ${S.path('M40 190 L600 190', 'd-liquid-line')}
      ${xs.map(x => S.rect(x, 132, 70, 76, 'd-liquid', 3)).join('')}
      ${xs.map(x => S.path(`M${x + 70} 132 Q${x + 110} 150 ${x + 180} 186`, 'd-line')).join('')}
      ${S.rect(40, 190, 560, 18, 'd-liquid', 0)}
      ${S.arrow(90, 110, 190, 110)} ${S.text(140, 100, 'v_t')}
      ${S.dim(250, 240, 320, 240, 'L_s')} ${S.dim(250, 275, 430, 275, 'L_u = v_t / f_s')}
      ${S.text(380, 162, 'gas bubble')} ${S.text(105, 174, 'slug')}
      ${S.text(320, 40, `D = ${lab(v.D * 1000, 'mm')}   v_sl = ${lab(v.v_sl, 'm/s')}   v_sg = ${lab(v.v_sg, 'm/s')}   θ = ${lab(v.theta * 180 / Math.PI, '°')}`)}
    `);
  },
  experiment: {
    objective: 'Measure slug frequency, translational velocity and body holdup in a transparent test section and compare with the correlations.',
    apparatus: ['Horizontal transparent pipe at least 400 diameters long with adjustable inclination', 'Separate metered air and liquid supplies joined at a Y-mixer', 'Outlet separator at controlled pressure'],
    instruments: [{ name: 'Two conductance or capacitance holdup probes a known distance apart', measures: 'Holdup time series; cross-correlation gives translational velocity', range: '0–1', resolution: '±0.02' }, { name: 'Fast pressure transducers', measures: 'Pressure pulses', range: '0–10 bar', resolution: '1 kHz, ±0.1 %' }, { name: 'High-speed camera', measures: 'Slug front and tail positions', range: '—', resolution: '≥ 500 frames/s' }, { name: 'Strain-gauged bend support', measures: 'Slug impact force', range: '0–5 kN', resolution: '±1 %' }],
    procedure: ['Set liquid rate, then raise gas rate in steps across the stratified–slug–annular range.', 'At each point record at least 300 slug passages.', 'Count slugs for frequency; cross-correlate the two probe signals for velocity; average the plateau of the holdup signal for body holdup.'],
    controls: ['Single-phase liquid runs to calibrate the holdup probes at 0 and 1', 'Repeat points in rising and falling gas-rate order to detect hysteresis'],
    signatures: ['Translational velocity linear in mixture velocity with slope near 1.2 and a positive intercept near 0.54√(gD)', 'Frequency minimum near a mixture velocity of about 4–5 m/s'],
    safety: ['Restrain the test section against slug loads', 'Guard against over-pressure of transparent pipe'],
  },
  falsify: ['Measured translational velocity not linear in mixture velocity.', 'Slug flow observed well inside the predicted stratified region for a clean, smooth, horizontal pipe.'],
  alternatives: [{ name: 'Severe (terrain or riser-base) slugging', text: 'Liquid accumulating at a low point produces much longer slugs governed by riser height and gas compressibility, not by interfacial instability.' }, { name: 'Zabaras (2000) frequency correlation', text: 'Extends Gregory–Scott with an inclination correction.' }, { name: 'Transient two-fluid or slug-tracking simulation', text: 'Resolves slug initiation, growth and dissipation instead of assuming a developed train.' }],
  hazards: [{ hazard: 'Fatigue of bends and supports', cause: 'Cyclic slug loads', mitigation: 'Dynamic stress analysis; add supports; reduce velocity' }, { hazard: 'Separator flooding', cause: 'Slug volume exceeding surge capacity', mitigation: 'Slug catcher sized for the largest credible slug; inlet choking' }],
  standards: ['API RP 14E', 'DNV-RP-F105 (free-spanning pipelines)', 'Energy Institute guidelines for the avoidance of vibration-induced fatigue failure in process pipework'],
  limits: 'Developed hydrodynamic slug flow in pipes inclined between about −10° and +30°, low-to-moderate viscosity liquids. The frequency correlation was built on small-diameter data at low pressure and is less reliable for large-diameter, high-pressure lines. The regime map follows Taitel and Dukler with the intermittent–annular boundary at a liquid level of 0.35 diameters (their original value was 0.5); the drift relation was measured for horizontal and upward-inclined tubes.',
  numerics: { method: 'Algebraic closure relations; bisection for the stratified equilibrium level' },
  optimise: { objective: 'F_b', sense: 'min', vars: ['D'], note: 'Larger diameter lowers velocity and bend load but raises liquid inventory.' },
  inverse: { series: 'freq-sweep', fit: ['v_sl'] },
  extensions: ['Riser-base severe slugging with gas compressibility', 'Statistical distribution of slug lengths (log-normal)', 'Coupling slug loads into a structural fatigue assessment'],
};

// ------------------------------------------------------------------ hydrates
const motiee = (pPa, sg) => { const lp = Math.log10(pPa / 6894.757); const tF = -238.24469 + 78.99667 * lp - 5.352544 * lp * lp + 349.473877 * sg - 150.854675 * sg * sg - 27.604065 * sg * lp; return (tF - 32) / 1.8 + 273.15; };
const kamath = pPa => 8533.80 / (38.980 - Math.log(pPa / 1000));
const MW = { methanol: 32.04, meg: 62.07 };

const hydrate = {
  id: 'hydrate-formation-risk',
  title: 'Hydrate formation risk in a high-pressure, low-temperature line',
  module: 2, klass: 'I', domains: ['hydrates', 'pipeline', 'offshore', 'thermal'],
  keywords: ['hydrate formation', 'gas hydrate', 'hydrates', 'hydrate', 'subcooling', 'flow assurance', 'inhibitor', 'methanol injection', 'meg', 'cooldown', 'shut-in', 'no-touch time', 'high pressure low temperature', 'plugging', 'clathrate'],
  summary: 'Hydrate stability boundary, subcooling along the line, thermodynamic inhibitor requirement and shut-in cool-down time.',
  background: [
    'Gas hydrates are ice-like solids in which water molecules form cages around small gas molecules. They are stable at high pressure and low temperature — exactly the conditions in deep-water flowlines — and can plug a line within hours.',
    'Risk is assessed by comparing the fluid pressure–temperature path with the hydrate equilibrium curve. The difference between the equilibrium temperature and the fluid temperature at the same pressure is the subcooling, the driving force for formation. Thermodynamic inhibitors such as methanol and mono-ethylene glycol shift the curve to lower temperatures by an amount estimated with the Hammerschmidt relation.',
  ],
  phenomena: ['Clathrate phase equilibrium', 'Convective cooling', 'Freezing-point depression by inhibitors', 'Transient cool-down after shut-in'],
  laws: ['mass', 'energy', 'fourier'],
  refs: ['Sloan, E. D. & Koh, C. A. (2008). Clathrate Hydrates of Natural Gases, 3rd ed., CRC Press.', 'Motiee, M. (1991). Estimate possibility of hydrates. Hydrocarbon Processing 70(7), 98–99.', 'Hammerschmidt, E. G. (1934). Formation of gas hydrates in natural gas transmission lines. Ind. Eng. Chem. 26, 851–855.', 'Kamath, V. A. (1984). Study of heat transfer characteristics during dissociation of gas hydrates. PhD thesis, University of Pittsburgh.', 'Carroll, J. (2014). Natural Gas Hydrates: A Guide for Engineers, 3rd ed., Gulf Professional Publishing.'],
  inputs: [
    inp('p_in', 'Inlet pressure', 'bar', 150, { min: 10, max: 700, aliases: ['pressure', 'inlet pressure', 'wellhead pressure'] }),
    inp('T_in', 'Inlet temperature', '°C', 60, { min: -10, max: 150, aliases: ['inlet temperature', 'wellhead temperature'] }),
    inp('T_amb', 'Seabed temperature', '°C', 4, { min: -2, max: 30, kind: 'environment', env: 'seabed_temp', aliases: ['seabed temperature', 'ambient temperature', 'sea temperature', 'water temperature'] }),
    inp('L', 'Flowline length', 'km', 20, { min: 0.1, max: 300, kind: 'geometry', aliases: ['length', 'long', 'tieback'] }),
    inp('D', 'Inner diameter', 'in', 10, { min: 2, max: 48, kind: 'geometry', aliases: ['diameter', 'bore', 'inch'] }),
    inp('t_w', 'Steel wall thickness', 'mm', 15, { min: 3, max: 60, kind: 'geometry', aliases: ['wall thickness'] }),
    inp('U', 'Overall heat-transfer coefficient', 'W/(m^2 K)', 3, { min: 0.2, max: 200, aliases: ['u-value', 'u value', 'insulation'] }),
    inp('mdot', 'Total mass flow rate', 'kg/s', 40, { min: 0.1, max: 2000, aliases: ['mass flow', 'mass rate'] }),
    inp('cp', 'Mixture specific heat', 'J/(kg K)', 2400, { min: 800, max: 5000, kind: 'fluid', aliases: ['specific heat'] }),
    inp('rho', 'Mixture density at line conditions', 'kg/m^3', 250, { min: 20, max: 1100, kind: 'fluid', aliases: ['density'] }),
    inp('dp', 'Pressure drop over the line', 'bar', 30, { min: 0, max: 400, aliases: ['pressure drop'] }),
    inp('sg', 'Gas specific gravity (air = 1)', '1', 0.65, { min: 0.554, max: 1.0, kind: 'fluid', aliases: ['gas gravity', 'specific gravity'] }),
    inp('wc', 'Water mass fraction of the stream', '%', 10, { min: 0.1, max: 90, kind: 'fluid', aliases: ['water cut', 'water fraction'] }),
    inp('margin', 'Design margin on inhibition', 'K', 3, { min: 0, max: 15, kind: 'operating' }),
    inp('k_g', 'Hydrate growth coefficient', '1/(K s)', 2e-6, { min: 1e-8, max: 1e-3, kind: 'hypothetical', src: 'Lumped subcooling-driven growth; order of magnitude from flow-loop studies. Calibrate against your own data.' }),
  ],
  assumptions: [
    asm('motiee', 'The hydrate boundary follows the Motiee (1991) gas-gravity correlation.', { why: 'Needs only gas gravity', alt: 'The boundary of pure methane (structure I) from Kamath (1984) is used.' }),
    asm('methanol', 'The thermodynamic inhibitor is methanol.', { why: 'Common for start-up and intermittent injection', alt: 'Mono-ethylene glycol is used instead.' }),
    asm('linear_p', 'Pressure falls linearly along the line.', { why: 'Adequate when only the end pressures are known', alt: 'The square of the pressure falls linearly with distance, as in isothermal gas flow, so more of the drop occurs toward the outlet.' }),
    asm('lumped', 'During shut-in the fluid and steel cool as one lumped thermal mass.', { why: 'Biot number of the pipe wall is small', alt: 'Radial conduction is not resolved; instead the heat stored in the steel is not credited, which gives a lower bound on the cool-down time.' }),
    asm('free_water', 'A free-water phase is present, so hydrates can form whenever conditions are inside the boundary.', { why: 'Conservative', alt: 'No free water: the boundary, subcooling and inhibitor dose are still reported, but hydrate growth is set to zero because water must condense first.' }),
  ],
  symbols: { T_eq: ['Hydrate equilibrium temperature', 'K'], dT_sub: ['Subcooling', 'K'], W: ['Inhibitor mass fraction in the aqueous phase', '1'], K_H: ['Hammerschmidt constant', 'K kg/mol'], M_i: ['Inhibitor molar mass', 'kg/mol'], dT_H: ['Hydrate-temperature depression', 'K'], tau_c: ['Cool-down time constant', 's'], T: ['Fluid temperature', 'K'], x: ['Distance', 'm'], t: ['Time', 's'], A: ['Flow area', 'm^2'], A_s: ['Steel cross-section', 'm^2'], rho_s: ['Steel density', 'kg/m^3'], c_s: ['Steel specific heat', 'J/(kg K)'], phi: ['Hydrate volume fraction', '1'], p: ['Pressure', 'Pa'] },
  equations: a => [
    eq('en', 'Flowing energy balance', 'mdot*cp*pd(T,x)', '-U*pi*D*(T - T_amb)', { kind: 'law', origin: 'First law of thermodynamics' }),
    a.linear_p ? eq('pp', 'Pressure profile', 'p', 'p_in - dp*x/L', { kind: 'closure', origin: 'Linear interpolation between end pressures', needs: ['linear_p'] })
      : eq('pp', 'Pressure profile', 'p', 'sqrt(p_in^2 - (p_in^2 - (p_in - dp)^2)*x/L)', { kind: 'closure', origin: 'Isothermal gas flow with constant friction factor: p² is linear in distance' }),
    eq('sub', 'Subcooling', 'dT_sub', 'T_eq - T', { kind: 'definition' }),
    eq('ham', 'Inhibitor depression', 'dT_H', 'K_H*W/(M_i*(1 - W))', { kind: 'empirical', origin: 'Hammerschmidt (1934); K_H = 1.297 K·kg/mol' }),
    a.lumped ? eq('cool', 'Shut-in cool-down', '(rho*cp*A + rho_s*c_s*A_s)*d(T,t)', '-U*pi*D*(T - T_amb)', { kind: 'law', origin: 'First law for a lumped thermal mass of fluid and steel', needs: ['lumped'] })
      : eq('cool', 'Shut-in cool-down, fluid heat capacity only', 'rho*cp*A*d(T,t)', '-U*pi*D*(T - T_amb)', { kind: 'law', origin: 'First law with the steel wall not credited (lower bound on cool-down time)' }),
    a.free_water ? eq('grow', 'Hydrate growth', 'd(phi,t)', 'k_g*max(dT_sub, 0)*(1 - phi)', { kind: 'hypothesis', origin: 'Subcooling-driven lumped kinetics; an engineering closure, not a first-principles law', needs: ['free_water'] })
      : eq('grow', 'Hydrate growth', 'd(phi,t)', '0*k_g*dT_sub', { kind: 'closure', origin: 'No free water, so no growth' }),
  ],
  derivation: a => [
    { text: 'The flowing temperature follows the same exponential law as any heat-losing pipeline.', tex: 'T(x) = T_{amb} + (T_{in}-T_{amb})\\,e^{-U\\pi D x/(\\dot m c_p)}' },
    { text: `The equilibrium temperature at each local pressure comes from the ${a.motiee ? 'Motiee gas-gravity' : 'pure-methane Kamath'} correlation; subcooling is the amount by which the fluid is colder than that.`, tex: '\\Delta T_{sub}(x) = T_{eq}\\big(p(x)\\big) - T(x)' },
    { text: 'An inhibitor at mass fraction W in the water phase lowers the equilibrium temperature. Inverting the Hammerschmidt relation gives the dose needed for a required depression.', tex: 'W = \\frac{M_i\\,\\Delta T_H}{K_H + M_i\\,\\Delta T_H}' },
    { text: 'After shut-in, with no flow, the stored heat of fluid and steel leaks through the insulation; the time to reach the hydrate temperature is the no-touch time.', tex: 't^* = \\tau_c\\,\\ln\\frac{T_0 - T_{amb}}{T_{eq} - T_{amb}}' },
  ],
  solve(v, a) {
    const Teq = p => (a.motiee ? motiee(p, v.sg) : kamath(p));
    const n = 240, x = N.linspace(0, v.L, n), ell = v.mdot * v.cp / (v.U * Math.PI * v.D);
    const T = x.map(s => v.T_amb + (v.T_in - v.T_amb) * Math.exp(-s / ell));
    const pEnd = v.p_in - v.dp;
    const p = x.map(s => Math.max(a.linear_p ? v.p_in - v.dp * s / v.L : Math.sqrt(Math.max(v.p_in ** 2 - (v.p_in ** 2 - Math.max(pEnd, 0) ** 2) * s / v.L, 0)), 1e5));
    const Te = p.map(Teq), sub = T.map((t, i) => Te[i] - t);
    const maxSub = N.maxOf(sub), iIn = sub.findIndex(s => s > 0);
    const xIn = iIn < 0 ? null : (iIn === 0 ? 0 : x[iIn - 1] + (x[iIn] - x[iIn - 1]) * (0 - sub[iIn - 1]) / (sub[iIn] - sub[iIn - 1]));
    const inside = maxSub > 0;
    const need = Math.max(0, maxSub + v.margin), M = (a.methanol ? MW.methanol : MW.meg) / 1000, KH = 1.297;
    const W = need > 0 ? M * need / (KH + M * need) : 0;
    const mWater = v.mdot * v.wc, mInh = mWater * W / Math.max(1 - W, 1e-9);
    // shut-in cool-down from the flowing profile, worst location = outlet end at settle-out pressure
    const A = Math.PI * v.D ** 2 / 4, As = Math.PI * ((v.D + 2 * v.t_w) ** 2 - v.D ** 2) / 4;
    const tau = (v.rho * v.cp * A + (a.lumped ? 7850 * 480 * As : 0)) / (v.U * Math.PI * v.D);
    const pSettle = v.p_in - v.dp / 2, TeS = Teq(pSettle);
    const tStar = xx => { const T0 = v.T_amb + (v.T_in - v.T_amb) * Math.exp(-xx / ell); if (T0 <= TeS) return 0; if (TeS <= v.T_amb) return Infinity; return tau * Math.log((T0 - v.T_amb) / (TeS - v.T_amb)); };
    const noTouch = tStar(v.L), tHot = tStar(0);
    const tt = N.linspace(0, Math.min(Math.max(3 * tau, 3600), 40 * 86400), 200);
    const coolOut = tt.map(t => v.T_amb + (T[n - 1] - v.T_amb) * Math.exp(-t / tau)), coolIn = tt.map(t => v.T_amb + (v.T_in - v.T_amb) * Math.exp(-t / tau));
    // growth at the coldest point during continued flow without inhibitor
    const dTs = Math.max(maxSub, 0);
    const g1 = N.rk45((t, y) => [a.free_water ? v.k_g * dTs * (1 - y[0]) : 0], [0], 0, 24 * 3600, 100);
    const phi24 = g1.y[0].at(-1);
    const pp = N.logspace(1e6, 6e7, 80);
    const warnings = [];
    if (!a.motiee && v.sg > 0.6) warnings.push('The pure-methane boundary under-predicts hydrate temperature for heavier gas; it is not conservative for this gas gravity.');
    if (pEnd < 1e5) warnings.push('The stated pressure drop exceeds the inlet pressure; the pressure has been limited to 1 bar.');
    if (v.p_in > 4.2e7 && a.motiee) warnings.push('Pressure exceeds the range over which the gravity correlation was fitted (to about 400 bar); treat the boundary as an extrapolation.');
    return {
      scalars: [
        scalar('inside', 'Line enters the hydrate region', inside ? 1 : 0, '1', { text: inside ? (a.free_water ? 'Yes — hydrates can form' : 'Yes — but hydrates form only once water condenses') : 'No — the whole line stays outside the hydrate region' }),
        scalar('dT_sub', 'Maximum subcooling', maxSub, 'K'), scalar('x_in', 'Distance at which the hydrate region is entered', xIn == null ? NaN : xIn, 'm', { show: 'km', text: xIn == null ? 'Not entered' : undefined }),
        scalar('T_out', 'Arrival temperature', T[n - 1], 'K', { show: '°C' }), scalar('T_eq_out', 'Hydrate equilibrium temperature at outlet pressure', Te[n - 1], 'K', { show: '°C' }),
        scalar('W', `${a.methanol ? 'Methanol' : 'MEG'} mass fraction required in the water phase`, W, '1', { show: '%' }),
        scalar('m_inh', `${a.methanol ? 'Methanol' : 'MEG'} injection rate`, mInh, 'kg/s', { show: 'kg/h' }),
        scalar('tau_c', 'Shut-in cool-down time constant', tau, 's', { show: 'h' }),
        scalar('t_nt', 'No-touch time at the cold end', noTouch, 's', { show: 'h', text: noTouch === 0 ? 'Zero — already inside the hydrate region while flowing' : !isFinite(noTouch) ? 'Unlimited — ambient is warmer than the hydrate temperature' : undefined }),
        scalar('t_hot', 'Cool-down time at the hot end', tHot, 's', { show: 'h', text: tHot === 0 ? 'Zero — already inside the hydrate region while flowing' : !isFinite(tHot) ? 'Unlimited — ambient is warmer than the hydrate temperature' : undefined }),
        scalar('phi_24', 'Hydrate volume fraction after 24 h at the coldest point (uninhibited)', phi24, '1', { show: '%', status: 'hypothetical' }),
      ],
      series: [
        line('pt-path', 'Operating path against the hydrate boundary', 'Temperature', '°C', pp.map(q => Teq(q) - 273.15), [{ label: 'Hydrate boundary', data: pp.map(q => q / 1e5) }], 'Pressure', 'bar', { overlay: [{ label: 'Flowing fluid, inlet → outlet', x: T.map(t => t - 273.15), y: p.map(q => q / 1e5) }], note: 'Hydrates are stable to the left of the boundary.' }),
        line('subcooling', 'Subcooling along the line', 'Distance', 'km', x.map(s => s / 1000), [{ label: 'Subcooling', data: sub }, { label: 'Zero', data: x.map(() => 0), dash: true }], 'Subcooling', 'K'),
        line('T-profile', 'Fluid and hydrate equilibrium temperature', 'Distance', 'km', x.map(s => s / 1000), [{ label: 'Fluid', data: T.map(t => t - 273.15) }, { label: 'Hydrate equilibrium', data: Te.map(t => t - 273.15), dash: true }], 'Temperature', '°C'),
        line('cooldown', 'Shut-in cool-down', 'Time', 'h', tt.map(t => t / 3600), [{ label: 'Hot end', data: coolIn.map(t => t - 273.15) }, { label: 'Cold end', data: coolOut.map(t => t - 273.15) }, { label: 'Hydrate temperature at settle-out pressure', data: tt.map(() => TeS - 273.15), dash: true }], 'Temperature', '°C'),
        line('growth', 'Hydrate fraction at the coldest point (uninhibited)', 'Time', 'h', g1.t.map(t => t / 3600), [{ label: 'Hydrate volume fraction', data: g1.y[0] }], 'Fraction', '–', { status: 'hypothetical' }),
      ],
      checks: [check('Hammerschmidt inversion', need > 0 ? (KH * W / (M * (1 - W)) - need) / need : 0, 1e-9, 'Dose reproduces the required depression')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const get = (r, s) => r.scalars.find(q => q.sym === s).value;
    const b = { motiee: false, methanol: true, linear_p: true, lumped: true, free_water: true };
    const rm = this.solve({ ...v, p_in: Math.exp(38.980 - 8533.80 / 280) * 1000, dp: 0 }, b);
    const out = [bench('Methane boundary through the solver at the pressure for 280 K', get(rm, 'T_eq_out'), 280, 'P = exp(38.980 − 8533.80/T) kPa, Kamath (1984)', 1e-10)];
    // Hammerschmidt worked value: 25 % by mass of methanol lowers the hydrate temperature by 1297 × 25/(32.04 × 75) = 13.49 K
    const r0 = this.solve({ ...v, U: Math.max(v.U, 30), margin: 0 }, b), need = Math.max(get(r0, 'dT_sub'), 0);
    if (need > 0) out.push(bench('Depression given by the computed methanol dose', 1297 * 100 * get(r0, 'W') / (32.04 * (100 - 100 * get(r0, 'W'))), need, 'Hammerschmidt (1934) in its original form ΔT = 1297 W/[M (100 − W)] with W in mass per cent and M in g/mol', 1e-9));
    // shut-in: integrate the lumped energy balance numerically up to the reported hot-end time and compare the temperature reached
    const tHot = get(r0, 't_hot'), tau = get(r0, 'tau_c');
    if (Number.isFinite(tHot) && tHot > 0) {
      // the hydrate temperature is taken at the settle-out pressure, the mean of the end pressures
      const ode = N.rk45((t, y) => [-(y[0] - v.T_amb) / tau], [v.T_in], 0, tHot, 3, { rtol: 1e-10, atol: 1e-10 });
      out.push(bench('Hot-end temperature at the reported cool-down time, by numerical integration', ode.y[0].at(-1), kamath(v.p_in - v.dp / 2), 'Independent Runge–Kutta integration of the lumped energy balance', 1e-6));
    }
    out.push(bench('Motiee correlation at 1000 psia and gas gravity 0.6', (motiee(1000 * 6894.757, 0.6) - 273.15) * 1.8 + 32, 56.26, 'Hand evaluation of the published polynomial, in °F', 1e-3));
    return out;
  },
  validation: [
    { name: 'Methane hydrate three-phase equilibrium', ref: 'Deaton, W. M. & Frost, E. M. (1946) U.S. Bureau of Mines Monograph 8, as tabulated in Sloan & Koh (2008)', note: 'Compares the pure-methane boundary; switch off the gas-gravity assumption to reproduce. The uncertainty covers the scatter between published data sets, not the precision of the original measurement.',
      cases: [
        { label: 'p = 3.81 MPa', inputs: { p_in: 3.81e6, dp: 0, L: 1 }, assumptions: { motiee: false }, observable: 'T_eq_out', observed: 277.1, sigma: 0.5 },
        { label: 'p = 5.35 MPa', inputs: { p_in: 5.35e6, dp: 0, L: 1 }, assumptions: { motiee: false }, observable: 'T_eq_out', observed: 280.4, sigma: 0.5 },
      ] },
  ],
  diagram(v) {
    return svg(`
      ${S.path('M30 70 L610 70', 'd-liquid-line')} ${S.text(600, 60, 'sea surface', 'd-text d-small', 'end')}
      ${S.path('M30 280 L610 280', 'd-ground')} ${S.text(600, 300, `seabed, ${lab(v.T_amb - 273.15, '°C')}`, 'd-text d-small', 'end')}
      ${S.rect(60, 236, 46, 44, 'd-body')} ${S.text(83, 228, 'well')}
      ${S.path('M106 262 L500 262', 'd-pipe')} ${S.path('M500 262 Q540 262 540 200 L540 90', 'd-pipe')}
      ${S.rect(505, 44, 70, 30, 'd-body')} ${S.text(540, 36, 'host')}
      ${S.rect(300, 250, 150, 24, 'd-hazard', 6)} ${S.text(375, 244, 'hydrate-stable zone')}
      ${S.arrow(130, 246, 200, 246)} ${S.text(165, 238, `${lab(v.p_in / 1e5, 'bar')}, ${lab(v.T_in - 273.15, '°C')}`)}
      ${S.dim(106, 325, 500, 325, `L = ${lab(v.L / 1000, 'km')}`)}
    `);
  },
  experiment: {
    objective: 'Locate the hydrate boundary of the actual produced fluid and measure the inhibitor dose that suppresses formation at line conditions.',
    apparatus: ['High-pressure stirred autoclave or rocking cell with sapphire window', 'Programmable cooling bath', 'Gas booster and sample cylinders with the field gas composition'],
    instruments: [{ name: 'Pressure transducer', measures: 'Cell pressure', range: '0–700 bar', resolution: '±0.05 %' }, { name: 'Pt100 probe in the liquid', measures: 'Cell temperature', range: '−20 to 60 °C', resolution: '±0.1 K' }, { name: 'Torque or motor-current sensor', measures: 'Onset of solids', range: '—', resolution: '—' }],
    procedure: ['Charge water and gas, pressurise, and cool at a constant rate until a sharp pressure fall marks formation.', 'Heat slowly in steps (isochoric step-heating); the point where the heating curve rejoins the cooling curve is the equilibrium point.', 'Repeat at several pressures and with each inhibitor concentration.'],
    controls: ['Pure-methane run compared with literature data to qualify the cell', 'Blank run with nitrogen (no hydrate at these conditions) to confirm leak-tightness'],
    signatures: ['Pressure drop at constant volume on formation', 'Exotherm on formation, endotherm on dissociation', 'Dissociation point independent of heating rate when stepped slowly'],
    safety: ['Pressure-rated cell with relief device', 'Flammable-gas detection and ventilation', 'Methanol is toxic and flammable: closed transfer and appropriate PPE'],
  },
  falsify: ['Measured dissociation points for the field gas lying warmer than the predicted boundary by more than about 2 K (the correlation would then be non-conservative).', 'Hydrate formation observed at an inhibitor dose above the predicted requirement.'],
  alternatives: [{ name: 'Statistical-thermodynamic (van der Waals–Platteeuw) model', text: 'Computes the boundary from composition; more accurate than gravity correlations, especially with CO₂, H₂S or salts.' }, { name: 'Kinetic or anti-agglomerant strategy', text: 'Low-dosage inhibitors delay nucleation or keep hydrates transportable rather than shifting the boundary.' }, { name: 'Nielsen–Bucklin relation', text: 'More accurate than Hammerschmidt at high inhibitor concentration.' }],
  hazards: [{ hazard: 'Hydrate plug', cause: 'Operation inside the hydrate region with free water', mitigation: 'Insulation, inhibitor, depressurisation procedure' }, { hazard: 'Projectile plug during remediation', cause: 'One-sided depressurisation', mitigation: 'Depressurise from both sides' }, { hazard: 'Methanol toxicity and fire', cause: 'Leak during injection', mitigation: 'Closed system, detection, bunding' }],
  standards: ['API RP 17A (subsea production systems)', 'ISO 13628 series', 'DNV-RP-F116 (integrity management of submarine pipeline systems)'],
  limits: 'Gravity correlation: sweet natural gas, gravity 0.55–1.0, to roughly 400 bar, no salts. Hammerschmidt relation: inhibitor mass fraction below about 0.25–0.3. Growth kinetics are a lumped closure for comparison only.',
  numerics: { method: 'Closed-form thermal profile; adaptive Runge–Kutta for growth' },
  optimise: { objective: 'm_inh', sense: 'min', vars: ['U'], note: 'Better insulation lowers the inhibitor demand until the line stays outside the hydrate region.' },
  inverse: { series: 'T-profile', fit: ['U'] },
  extensions: ['Composition-based boundary including CO₂, H₂S and salinity', 'Radial conduction through multi-layer insulation', 'Transportability of hydrate slurries with anti-agglomerants'],
};

export default [pipeline, slug, hydrate];
