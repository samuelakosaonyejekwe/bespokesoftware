// Electromagnetism, waves and acoustics, and functional materials.
import { inp, asm, eq, scalar, line, field, anim, check, bench, svg, S, lab, N, C } from './kit.js';

const g0 = 9.80665, TAU = 2 * Math.PI, EPS0 = C.eps_0, MU0 = C.mu_0;
const val = (r, s) => r.scalars.find(q => q.sym === s).value;

// complex arithmetic on [re, im] pairs
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const csub = (a, b) => [a[0] - b[0], a[1] - b[1]];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const cdiv = (a, b) => { const d = b[0] * b[0] + b[1] * b[1]; return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; };
const cabs = a => Math.hypot(a[0], a[1]);
const csqrt = a => { const r = cabs(a), re = Math.sqrt(Math.max(0, (r + a[0]) / 2)), im = Math.sqrt(Math.max(0, (r - a[0]) / 2)); return [re, a[1] < 0 ? -im : im]; };
const cexp = a => { const e = Math.exp(a[0]); return [e * Math.cos(a[1]), e * Math.sin(a[1])]; };
const ccos = a => [Math.cos(a[0]) * Math.cosh(a[1]), -Math.sin(a[0]) * Math.sinh(a[1])];
const csin = a => [Math.sin(a[0]) * Math.cosh(a[1]), Math.cos(a[0]) * Math.sinh(a[1])];
const mmul = (A, B) => [[cadd(cmul(A[0][0], B[0][0]), cmul(A[0][1], B[1][0])), cadd(cmul(A[0][0], B[0][1]), cmul(A[0][1], B[1][1]))], [cadd(cmul(A[1][0], B[0][0]), cmul(A[1][1], B[1][0])), cadd(cmul(A[1][0], B[0][1]), cmul(A[1][1], B[1][1]))]];
const dB = x => 20 * Math.log10(Math.max(x, 1e-300));
/** Bracketed root with a fallback value when the bracket does not straddle a sign change. */
const rootOr = (f, a, b, fallback) => { try { const r = N.findRoot(f, a, b); return Number.isFinite(r) ? r : fallback; } catch { return fallback; } };

// ------------------------------------------------------------------ electrostatic field in a 2-D gap
/** Successive over-relaxation for div(eps grad phi) = -rho with a dielectric layer occupying rows 0..jb. */
function sorLayered(nx, ny, fixed, epsB, jb, src, tol = 1e-6, maxIt = 4000) {
  const phi = Array.from({ length: ny }, () => new Float64Array(nx)), mask = Array.from({ length: ny }, () => new Uint8Array(nx));
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) { const q = fixed(i, j); if (q !== undefined) { phi[j][i] = q; mask[j][i] = 1; } }
  const w = 2 / (1 + Math.sin(Math.PI / Math.max(nx, ny))), eh = (epsB + 1) / 2, den = 2 * eh + epsB + 1;
  let it = 0, res = Infinity;
  for (; it < maxIt; it++) {
    res = 0;
    for (let j = 1; j < ny - 1; j++) {
      const pj = phi[j], pd = phi[j - 1], pu = phi[j + 1], mj = mask[j], sj = j > jb ? src : 0;
      for (let i = 1; i < nx - 1; i++) {
        if (mj[i]) continue;
        const gq = j === jb ? (eh * (pj[i - 1] + pj[i + 1]) + epsB * pd[i] + pu[i]) / den : (pj[i - 1] + pj[i + 1] + pd[i] + pu[i] + sj) * 0.25;
        const dl = gq - pj[i]; pj[i] += w * dl; if (Math.abs(dl) > res) res = Math.abs(dl);
      }
    }
    for (let i = 0; i < nx; i++) { if (!mask[0][i]) phi[0][i] = phi[1][i]; if (!mask[ny - 1][i]) phi[ny - 1][i] = phi[ny - 2][i]; }
    for (let j = 0; j < ny; j++) { if (!mask[j][0]) phi[j][0] = phi[j][1]; if (!mask[j][nx - 1]) phi[j][nx - 1] = phi[j][nx - 2]; }
    if (res < tol) break;
  }
  return { phi, iterations: it, residual: res, converged: res < tol };
}

/** Potential (normalised by the electrode voltage) between an electrode and a grounded plane. `plate` spans the electrode across the whole box. */
function gapField(v, a, plate = false) {
  const ng = Math.max(8, Math.round(v.n_gap)), dx = v.d_gap / ng;
  let nx = Math.max(21, Math.round(v.a_box * ng) + 1); if (nx % 2 === 0) nx++;
  const round = a.round_electrode && !plate, ic = (nx - 1) / 2;
  const nrWant = plate ? 0 : Math.round(v.r_e / dx), nr = plate ? 0 : Math.min(nrWant, 2 * ng, ic - 3);
  const jc = ng + (round ? nr : 0), ny = jc + (round ? nr : 0) + ng + 1;
  const jb = a.no_barrier ? 0 : N.clamp(Math.round(v.f_b * ng), 1, ng - 2), epsB = a.no_barrier ? 1 : v.eps_b;
  const open = a.open_box || plate;
  const inside = (i, j) => (plate ? j === jc : round ? (i - ic) ** 2 + (j - jc) ** 2 <= nr * nr + 0.25 : j === jc && Math.abs(i - ic) <= nr);
  const fixed = (i, j) => (j === 0 ? 0 : inside(i, j) ? 1 : !open && (i === 0 || i === nx - 1 || j === ny - 1) ? 0 : undefined);
  const rhoN = a.laplace ? 0 : v.rho_q / (EPS0 * v.V_0); // normalised charge density, 1/m^2
  const sol = a.no_barrier
    ? N.poisson2D({ nx, ny, dx, fixed, tol: 1e-6, maxIt: 4000, f: rhoN ? () => rhoN : undefined })
    : sorLayered(nx, ny, fixed, epsB, jb, rhoN * dx * dx);
  const phi = sol.phi;
  // peak field in the air: cell-centred magnitude, and the normal difference at the electrode surface
  let epk = 0;
  for (let j = jb; j < ny - 1; j++) for (let i = 0; i < nx - 1; i++) {
    const ex = (phi[j][i + 1] + phi[j + 1][i + 1] - phi[j][i] - phi[j + 1][i]) / (2 * dx), ey = (phi[j + 1][i] + phi[j + 1][i + 1] - phi[j][i] - phi[j][i + 1]) / (2 * dx);
    const e = Math.hypot(ex, ey); if (e > epk) epk = e;
    if (inside(i, j) !== inside(i + 1, j)) epk = Math.max(epk, Math.abs(phi[j][i + 1] - phi[j][i]) / dx);
    if (inside(i, j) !== inside(i, j + 1)) epk = Math.max(epk, Math.abs(phi[j + 1][i] - phi[j][i]) / dx);
  }
  const ecol = Array.from({ length: nx }, (_, i) => (phi[1][i] - phi[0][i]) / dx);
  let etan = 0; if (jb > 0) for (let i = 0; i < nx - 1; i++) etan = Math.max(etan, Math.abs(phi[jb][i + 1] - phi[jb][i]) / dx);
  // flux through horizontal faces: conserved between the collector and the row below the electrode
  const flux = j => { let s = 0; const ef = j < jb ? epsB : 1; for (let i = 1; i < nx - 1; i++) s += ef * (phi[j + 1][i] - phi[j][i]); return s; };
  const m = ng - 1, G0 = flux(0), Gm = flux(m);
  const fluxRes = open ? (Gm - G0 + rhoN * dx * dx * (nx - 2) * (m - jb)) / Math.max(Math.abs(G0), 1e-300) : 0;
  return { phi, nx, ny, dx, ng, nr, nrWant, jc, jb, ic, epsB, epk, ecol, etan, G0, fluxRes, open, iterations: sol.iterations, converged: sol.converged };
}
const acosh = x => Math.log(x + Math.sqrt(x * x - 1));

const electrostatic = {
  id: 'electrostatic-field-2d',
  title: 'Electrostatic field between a high-voltage electrode and a grounded plane',
  module: 2, klass: 'I', domains: ['electromagnetic'], heavy: true,
  keywords: ['electrostatic field', 'field enhancement', 'electrode', 'high voltage', 'laplace equation', 'poisson equation', 'potential', 'breakdown', 'creepage', 'clearance', 'dielectric barrier', 'corona onset', 'grounded plane', 'electric field', 'insulation'],
  summary: 'Potential and electric field in a two-dimensional gap between a small high-voltage electrode and a grounded collector, with optional dielectric barrier and space charge; peak field, field-enhancement factor, breakdown margin and creepage check.',
  background: [
    'In a region free of charge the electrostatic potential satisfies Laplace\'s equation; with a known space-charge density it satisfies Poisson\'s equation. The field is the negative gradient of the potential, and it concentrates wherever a conductor is small or sharply curved. The ratio of the peak field to the uniform value V/d is the field-enhancement factor.',
    'Air at sea level breaks down in a uniform field of about 3 MV/m. Where the peak field exceeds this value locally while the average field stays well below it, the result is a partial (corona) discharge rather than a spark. A solid dielectric layer in series with the air raises the field in the air, because the normal component of the flux density is continuous across the interface. Surfaces of solid insulation bridging the conductors must also be long enough to resist tracking; that length is the creepage distance.',
  ],
  phenomena: ['Field concentration at small conductors', 'Dielectric interface refraction of the field', 'Space-charge distortion of the potential', 'Partial discharge inception', 'Surface tracking along insulation'],
  laws: ['maxwell', 'charge'],
  refs: ['Jackson, J. D. (1999). Classical Electrodynamics, 3rd ed., Wiley.', 'Kuffel, E., Zaengl, W. S. & Kuffel, J. (2000). High Voltage Engineering: Fundamentals, 2nd ed., Newnes.', 'Peek, F. W. (1929). Dielectric Phenomena in High Voltage Engineering, 3rd ed., McGraw-Hill.', 'Press, W. H., Teukolsky, S. A., Vetterling, W. T. & Flannery, B. P. (2007). Numerical Recipes, 3rd ed., Cambridge University Press (successive over-relaxation).'],
  inputs: [
    inp('V_0', 'Electrode voltage', 'kV', 20, { min: 0.1, max: 300, aliases: ['voltage', 'kv', 'potential', 'high voltage'] }),
    inp('d_gap', 'Gap from electrode surface to grounded plane', 'mm', 30, { min: 1, max: 500, kind: 'geometry', aliases: ['gap', 'spacing', 'clearance', 'separation'] }),
    inp('r_e', 'Electrode radius (half-width)', 'mm', 6, { min: 0.05, max: 100, kind: 'geometry', aliases: ['electrode radius', 'radius', 'wire radius', 'tip radius'] }),
    inp('a_box', 'Box width as a multiple of the gap', '1', 4, { min: 2, max: 6, kind: 'geometry', aliases: ['box width', 'aspect'] }),
    inp('f_b', 'Barrier thickness as a fraction of the gap', '1', 0.2, { min: 0.05, max: 0.6, kind: 'geometry', aliases: ['barrier thickness', 'dielectric thickness'] }),
    inp('eps_b', 'Relative permittivity of the barrier', '1', 3.4, { min: 1, max: 100, kind: 'fluid', aliases: ['permittivity', 'dielectric constant'], src: 'Polyimide film, typical' }),
    inp('rho_q', 'Space-charge density in the air gap', 'uC/m^3', 50, { min: 0, max: 2000, aliases: ['space charge', 'charge density'], src: 'Order of magnitude in a unipolar corona drift region' }),
    inp('E_bd', 'Breakdown field of the gas', 'MV/m', 3, { min: 0.1, max: 30, kind: 'environment', aliases: ['breakdown field', 'breakdown strength', 'dielectric strength'], src: 'Dry air at 1 atm and 20 °C in a uniform field' }),
    inp('L_cr', 'Creepage path available along the insulation', 'mm', 400, { min: 1, max: 20000, kind: 'geometry', aliases: ['creepage', 'creepage distance', 'tracking distance'] }),
    inp('s_cr', 'Required specific creepage distance', 'mm/kV', 16, { min: 1, max: 60, aliases: ['specific creepage'], src: 'Order of the light-pollution class for outdoor insulators; take the value from the applicable insulation-coordination standard' }),
    inp('n_gap', 'Grid cells across the gap', '1', 16, { min: 12, max: 40, kind: 'numerical' }),
  ],
  assumptions: [
    asm('laplace', 'The gap carries no space charge, so the potential satisfies Laplace\'s equation.', { why: 'Valid below discharge inception', alt: 'A uniform space-charge density fills the air gap and the potential satisfies Poisson\'s equation.' }),
    asm('no_barrier', 'The gap is air only, with uniform permittivity.', { why: 'Bare electrode arrangement', alt: 'A solid dielectric barrier covers the grounded plane; the normal flux density is continuous at its surface.' }),
    asm('open_box', 'The side and top boundaries are open: the normal field vanishes there.', { why: 'Models one electrode of a row, or distant surroundings', alt: 'The box is a grounded metal enclosure.' }),
    asm('round_electrode', 'The electrode has a circular cross-section (a rod or wire seen end-on).', { why: 'Avoids singular edges', alt: 'The electrode is a thin flat strip of the same half-width, whose edges are field singularities.' }),
  ],
  symbols: { phi: ['Electrostatic potential', 'V'], x: ['Horizontal coordinate', 'm'], y: ['Height above the plane', 'm'], E: ['Electric field magnitude', 'V/m'], E_0: ['Uniform-field reference', 'V/m'], E_peak: ['Peak field in the air', 'V/m'], beta: ['Field-enhancement factor', '1'], M_bd: ['Breakdown margin', '1'], h_c: ['Height of the electrode axis', 'm'], E_w: ['Closed-form peak field, cylinder above a plane', 'V/m'], t_b: ['Barrier thickness', 'm'], E_nb: ['Normal field inside the barrier', 'V/m'], E_na: ['Normal field in the air at the barrier', 'V/m'], E_0b: ['Uniform field in the air with a barrier', 'V/m'], phi_w: ['Potential of the enclosure walls', 'V'], L_req: ['Required creepage distance', 'm'], M_cr: ['Creepage margin', '1'], w_e: ['Strip width', 'm'] },
  equations: a => [
    a.laplace
      ? eq('gov', 'Laplace equation', 'pd2(phi,x)', '-pd2(phi,y)', { kind: 'law', origin: 'Gauss\'s law with no free charge and uniform permittivity', needs: ['laplace'] })
      : eq('gov', 'Poisson equation', 'lap(phi)', '-rho_q/eps_0', { kind: 'law', origin: 'Gauss\'s law with a prescribed space-charge density' }),
    eq('field', 'Electric field magnitude', 'E', 'sqrt(pd(phi,x)^2 + pd(phi,y)^2)', { kind: 'definition' }),
    eq('e0', 'Uniform-field reference', 'E_0', 'V_0/d_gap', { kind: 'definition' }),
    eq('fef', 'Field-enhancement factor', 'beta', 'E_peak/E_0', { kind: 'definition' }),
    eq('mbd', 'Margin against breakdown', 'M_bd', 'E_bd/E_peak', { kind: 'definition' }),
    ...(a.round_electrode ? [] : [eq('strip', 'Strip width', 'w_e', '2*r_e', { kind: 'definition' })]),
    ...(a.round_electrode && a.laplace && a.no_barrier ? [
      eq('hc', 'Height of the electrode axis', 'h_c', 'd_gap + r_e', { kind: 'definition' }),
      eq('wire', 'Peak field of an isolated cylinder above a plane', 'E_w', 'V_0*sqrt((h_c + r_e)/(h_c - r_e))/(r_e*ln(h_c/r_e + sqrt((h_c/r_e)^2 - 1)))', { kind: 'derived', origin: 'Method of images for two line charges', needs: ['laplace', 'no_barrier', 'round_electrode'] }),
    ] : []),
    ...(a.no_barrier ? [] : [
      eq('tb', 'Barrier thickness', 't_b', 'f_b*d_gap', { kind: 'definition' }),
      eq('dn', 'Continuity of normal flux density at the barrier', 'eps_b*E_nb', 'E_na', { kind: 'boundary', origin: 'Gauss\'s law across an uncharged interface' }),
      eq('eb', 'Uniform field in the air with a barrier', 'E_0b', 'V_0/(d_gap - t_b + t_b/eps_b)', { kind: 'derived', origin: 'Two capacitors in series' }),
    ]),
    ...(a.open_box ? [] : [eq('enc', 'Grounded enclosure', 'phi_w', '0*V_0', { kind: 'boundary' })]),
    eq('creq', 'Required creepage distance', 'L_req', 's_cr*V_0', { kind: 'empirical', origin: 'Specific creepage distance from insulation-coordination practice' }),
    eq('mcr', 'Creepage margin', 'M_cr', 'L_cr/L_req', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'In electrostatics the field is irrotational, so it derives from a scalar potential.', tex: '\\mathbf{E} = -\\nabla\\varphi' },
    { text: 'Gauss\'s law relates the divergence of the flux density to the free charge.' + (a.laplace ? ' With no charge in the gap and uniform permittivity this is Laplace\'s equation.' : ' With a space-charge density ρ_q this is Poisson\'s equation.'), tex: a.laplace ? '\\nabla^2\\varphi = 0' : '\\nabla^2\\varphi = -\\frac{\\rho_q}{\\varepsilon_0}' },
    { text: 'Replacing the second derivatives by central differences on a square grid makes each interior potential the average of its four neighbours (plus a source term). Successive over-relaxation iterates this relation to convergence.', tex: '\\varphi_{i,j} = \\tfrac14\\left(\\varphi_{i+1,j}+\\varphi_{i-1,j}+\\varphi_{i,j+1}+\\varphi_{i,j-1} + h^2\\rho_q/\\varepsilon_0\\right)' },
    ...(a.no_barrier ? [] : [{ text: 'At the surface of the barrier the normal flux density is continuous, so the field in the air is larger than the field in the solid by the permittivity ratio.', tex: '\\varepsilon_b E_{n,b} = E_{n,a}' }]),
    { text: 'For a cylinder of radius r with its axis at height h above a plane, two image line charges at ±√(h²−r²) reproduce both equipotentials. The largest field is at the point of the cylinder nearest the plane.', tex: 'E_w = \\frac{V_0}{r\\,\\cosh^{-1}(h/r)}\\sqrt{\\frac{h+r}{h-r}}' },
    { text: 'The enhancement factor compares the peak field with the uniform value; the breakdown margin compares the gas strength with the peak field.', tex: '\\beta = \\frac{E_{peak}}{V_0/d},\\qquad M_{bd} = \\frac{E_{bd}}{E_{peak}}' },
  ],
  solve(v, a) {
    const s = gapField(v, a), V = v.V_0, dx = s.dx, E0 = V / v.d_gap, Epk = s.epk * V, beta = Epk / E0;
    const warnings = [];
    if (!s.converged) warnings.push('The relaxation did not reach its tolerance within the iteration limit; treat the field as approximate.');
    if (s.nr < s.nrWant) warnings.push('The electrode is too large for the box and has been truncated on the grid; widen the box or reduce the radius.');
    if (s.nr < 3) warnings.push('The electrode radius spans fewer than three grid cells, so the grid peak field under-estimates the true surface field. Use the closed-form cylinder value or refine the grid.');
    if (!a.round_electrode) warnings.push('A thin strip has singular edges: the grid peak field is an average over one cell and grows as the grid is refined.');
    const hc = v.d_gap + v.r_e, closed = a.round_electrode && a.laplace && a.no_barrier;
    const Ew = V * Math.sqrt((hc + v.r_e) / (hc - v.r_e)) / (v.r_e * acosh(hc / v.r_e));
    const Mbd = v.E_bd / Epk, Lreq = v.s_cr * V, Mcr = v.L_cr / Lreq;
    if (Mbd < 1) warnings.push('The peak field exceeds the breakdown field of the gas: partial discharge (corona) is expected at the electrode, and a spark if the average field is also high.');
    if (Mcr < 1) warnings.push('The available creepage path is shorter than the required distance: surface tracking is a risk.');
    const xs = N.linspace(-(s.nx - 1) / 2 * dx, (s.nx - 1) / 2 * dx, s.nx), ys = N.linspace(0, (s.ny - 1) * dx, s.ny);
    const data = s.phi.map(r => Array.from(r, q => q * V));
    const U = data.map((r, j) => r.map((_, i) => -(r[Math.min(i + 1, s.nx - 1)] - r[Math.max(i - 1, 0)]) / ((Math.min(i + 1, s.nx - 1) - Math.max(i - 1, 0)) * dx)));
    const W = data.map((r, j) => r.map((_, i) => { const jp = Math.min(j + 1, s.ny - 1), jm = Math.max(j - 1, 0); return -(data[jp][i] - data[jm][i]) / ((jp - jm) * dx); }));
    const jLow = s.jc - (a.round_electrode ? s.nr : 0);
    const yc = [], Ec = [], Ea = [], sImg = Math.sqrt(hc * hc - v.r_e * v.r_e);
    for (let j = 0; j < jLow; j++) { const ym = (j + 0.5) * dx; yc.push(ym * 1000); Ec.push((data[j + 1][s.ic] - data[j][s.ic]) / dx / 1e6); Ea.push(closed ? V / acosh(hc / v.r_e) * 2 * sImg / (sImg * sImg - ym * ym) / 1e6 : E0 / 1e6); }
    const Ecoll = N.maxOf(s.ecol.map(Math.abs)) * V;
    const scalars = [
      scalar('E_0', 'Uniform-field reference V/d', E0, 'V/m', { show: 'MV/m' }),
      scalar('E_peak', 'Peak field in the air (grid)', Epk, 'V/m', { show: 'MV/m' }),
      scalar('beta', 'Field-enhancement factor', beta, '1'),
      ...(closed ? [scalar('E_w', 'Closed-form peak field, isolated cylinder above a plane', Ew, 'V/m', { show: 'MV/m', note: 'Method of images; no box walls' })] : []),
      scalar('M_bd', 'Margin against gas breakdown', Mbd, '1', { text: Mbd >= 1 ? `${lab(Mbd)} — peak field below the breakdown field` : `${lab(Mbd)} — partial discharge expected` }),
      scalar('E_coll', 'Largest field at the grounded plane', Ecoll, 'V/m', { show: 'MV/m' }),
      ...(a.no_barrier ? [] : [scalar('E_0b', 'Uniform-field value in the air with the barrier', V / (v.d_gap * (1 - v.f_b) + v.f_b * v.d_gap / v.eps_b), 'V/m', { show: 'MV/m' }), scalar('E_tan', 'Largest tangential field along the barrier surface', s.etan * V, 'V/m', { show: 'MV/m' })]),
      scalar('C_l', 'Capacitance per unit length (from collector flux)', EPS0 * Math.abs(s.G0), 'F/m', { show: 'pF/m' }),
      scalar('L_req', 'Required creepage distance', Lreq, 'm', { show: 'mm' }),
      scalar('M_cr', 'Creepage margin', Mcr, '1', { text: Mcr >= 1 ? `${lab(Mcr)} — adequate` : `${lab(Mcr)} — too short` }),
      scalar('n_it', 'Relaxation sweeps used', s.iterations, '1'),
    ];
    return {
      scalars,
      series: [
        line('axis-field', 'Field on the axis between plane and electrode', 'Height above plane', 'mm', yc, [{ label: 'Computed', data: Ec }, { label: closed ? 'Isolated cylinder above a plane' : 'Uniform V/d', data: Ea, dash: true }], 'Field', 'MV/m'),
        line('collector-field', 'Field at the grounded plane', 'Horizontal position', 'mm', xs.map(q => q * 1000), [{ label: 'Normal field', data: s.ecol.map(q => q * V / 1e6) }], 'Field', 'MV/m'),
      ],
      fields: [field('potential', 'Electrostatic potential', data, [xs[0] * 1000, xs[s.nx - 1] * 1000, 0, ys[s.ny - 1] * 1000], 'x (mm)', 'y (mm)', 'V', { vectors: { u: U, v: W }, vectorLabel: 'Electric field' })],
      checks: [
        check('Flux conservation between collector and electrode', s.fluxRes, 1e-3, s.open ? 'Gauss\'s law on the grid: flux through the plane against flux below the electrode, less enclosed charge' : 'Not evaluated for a grounded enclosure, where flux also ends on the walls'),
        check('Potential within the electrode values', a.laplace ? Math.max(0, N.maxOf(data.map(r => N.maxOf(r))) / V - 1, -N.minOf(data.map(r => N.minOf(r))) / V) : 0, 1e-6, 'Maximum principle for Laplace\'s equation'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], ap = { ...a, laplace: true };
    const p = gapField(v, ap, true), tb = v.f_b * v.d_gap, jbT = p.jb * p.dx;
    out.push(bench('Parallel-plate limit: field in the air', p.epk * v.V_0, a.no_barrier ? v.V_0 / v.d_gap : v.V_0 / (v.d_gap - jbT + jbT / v.eps_b), a.no_barrier ? 'E = V/d' : 'Series capacitors, E = V/(d_air + t_b/ε_b), barrier on grid lines', 1e-3));
    const q = gapField(v, { ...a, laplace: false, no_barrier: true }, true);
    out.push(bench('Plane gap with uniform space charge: field at the collector', q.ecol[q.ic] * v.V_0, v.V_0 / v.d_gap + v.rho_q * (v.d_gap - q.dx) / (2 * EPS0), 'Exact solution of the 1-D Poisson equation, evaluated at the first cell centre', 1e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const r = N.clamp(v.r_e / v.d_gap * 150, 4, 34), yb = 280, ye = yb - 150 - r;
    return svg(`
      ${S.rect(90, 40, 460, 240, a.open_box ? 'd-dim' : 'd-body', 0)}
      ${S.path('M60 280 L580 280', 'd-ground')} ${S.text(570, 300, 'grounded plane', 'd-text d-small', 'end')}
      ${a.no_barrier ? '' : S.rect(90, yb - 150 * v.f_b, 460, 150 * v.f_b, 'd-liquid', 0) + S.text(100, yb - 150 * v.f_b - 6, `barrier, ε = ${lab(v.eps_b)}`, 'd-text d-small', 'start')}
      ${a.round_electrode ? S.circle(320, ye, r, 'd-hazard') : S.rect(320 - r, ye + r - 3, 2 * r, 6, 'd-hazard', 1)}
      ${S.text(320, ye - r - 8, `electrode, ${lab(v.V_0 / 1000, 'kV')}`)}
      ${[-70, -35, 0, 35, 70].map(q => S.arrow(320 + q * 0.5, ye + r + 6, 320 + q, yb - (a.no_barrier ? 6 : 150 * v.f_b + 6))).join('')}
      ${S.dim(470, ye + r, 470, yb, '')} ${S.text(476, (ye + r + yb) / 2, `d = ${lab(v.d_gap * 1000, 'mm')}`, 'd-text d-small', 'start')}
      ${S.text(320, 30, a.open_box ? 'open boundaries (zero normal field)' : 'grounded enclosure', 'd-text d-small')}
      ${S.text(320, 330, `r = ${lab(v.r_e * 1000, 'mm')}   E_bd = ${lab(v.E_bd / 1e6, 'MV/m')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the discharge-inception voltage of a rod–plane gap and compare the implied surface field with the computed peak field.',
    apparatus: ['Smooth cylindrical electrode on an insulating support above an earthed plate', 'Variable high-voltage direct or alternating supply with current-limiting resistor', 'Screened enclosure with interlock', 'Optional dielectric sheet on the plate'],
    instruments: [{ name: 'Resistive or capacitive voltage divider', measures: 'Electrode voltage', range: '0–100 kV', resolution: '±1 %' }, { name: 'Partial-discharge detector or picoammeter', measures: 'Inception of corona current', range: '1 pA–1 mA', resolution: '±2 %' }, { name: 'Electrostatic field mill or capacitive probe', measures: 'Field at the plane', range: '0–2 MV/m', resolution: '±5 %' }, { name: 'Barometer, thermometer and hygrometer', measures: 'Air density and humidity for correction', range: 'ambient', resolution: '±0.5 hPa, ±0.2 K, ±2 % RH' }],
    procedure: ['Set the gap with a gauge block and record ambient conditions.', 'Raise the voltage slowly until the first steady discharge current or audible corona, and record the inception voltage; repeat ten times.', 'Scan the field probe across the plane at a voltage well below inception.', 'Repeat for two further gaps and with the dielectric sheet in place.'],
    controls: ['Parallel-plate arrangement with guard ring to confirm E = V/d and qualify the field probe', 'Polished against roughened electrode to show the effect of surface condition'],
    signatures: ['Field at the plane proportional to voltage below inception', 'Peaked field profile on the plane directly beneath the electrode', 'Inception voltage rising less than linearly with gap for a small electrode'],
    safety: ['Interlocked enclosure and earthing stick; discharge all capacitances before access', 'Current-limited supply', 'Ventilation for ozone and nitrogen oxides during sustained corona'],
  },
  falsify: ['A field measured at the plane, below discharge inception, that is not proportional to the applied voltage.', 'A measured field profile on the plane that differs from the computed one by more than the combined probe and positioning uncertainty.', 'Discharge inception at a computed surface field well below the Peek value for that radius and air density.'],
  alternatives: [{ name: 'Closed-form image solutions', text: 'Cylinder–plane and sphere–plane gaps have exact image-charge solutions; they are preferred when the electrode is too small to resolve on the grid.' }, { name: 'Charge-simulation or boundary-element methods', text: 'Represent curved electrodes exactly and give smooth surface fields without a volume grid.' }, { name: 'Coupled corona model', text: 'Above inception the space charge is not prescribed but follows from ion drift and current continuity; the field at the emitter is then pinned near its onset value (Kaptzov\'s hypothesis).' }],
  hazards: [{ hazard: 'Electric shock and stored charge', cause: 'Contact with energised or undischarged parts', mitigation: 'Interlocks, earthing stick, current-limited supply, two-person working' }, { hazard: 'Flashover', cause: 'Insufficient clearance or creepage, contamination, humidity', mitigation: 'Design margins from the applicable standard; clean, dry insulation' }, { hazard: 'Ozone and nitrogen oxides', cause: 'Sustained corona', mitigation: 'Ventilation and exposure monitoring' }],
  standards: ['IEC 60664-1 (insulation coordination for equipment within low-voltage supply systems)', 'IEC 60071 series (insulation coordination)', 'IEC 60060-1 (high-voltage test techniques)', 'IEC 60815 series (selection and dimensioning of high-voltage insulators for polluted conditions)'],
  limits: 'Two-dimensional planar geometry (an electrode that is long out of the plane), electrostatic conditions, linear isotropic dielectrics and a prescribed uniform space charge. The grid cannot resolve conductors smaller than about three cells, nor the singular field at sharp edges. The breakdown comparison uses a single uniform-field strength; inception at small radii follows Peek\'s law and occurs at a higher surface field.',
  numerics: { method: 'Five-point finite differences solved by successive over-relaxation; flux-weighted stencil at the dielectric interface', order: 2, stability: 'Convergent for relaxation factors between 0 and 2', resolution: 'n_gap' },
  optimise: { objective: 'beta', sense: 'min', vars: ['r_e'], note: 'A larger electrode radius lowers the enhancement factor until the electrode is comparable with the gap.' },
  inverse: { series: 'collector-field', fit: ['r_e', 'd_gap'] },
  extensions: ['Axisymmetric (r–z) formulation for needle and sphere electrodes', 'Self-consistent ion-drift space charge above corona onset', 'Peek inception criterion with air-density and roughness factors', 'Time-harmonic fields with lossy dielectrics'],
};

// ------------------------------------------------------------------ series RLC circuit
/** Exact step response of the linear circuit: series R–L feeding C in parallel with a leakage resistance Rp (Infinity for none). */
function rlcExact(Rt, L, Cc, Rp, V, ts) {
  const gp = Number.isFinite(Rp) ? 1 / (Rp * Cc) : 0, A = [[-Rt / L, -1 / L], [1 / Cc, -gp]];
  const iss = Number.isFinite(Rp) ? V / (Rt + Rp) : 0, vss = Number.isFinite(Rp) ? V * Rp / (Rt + Rp) : V, y0 = [-iss, -vss];
  const s = (A[0][0] + A[1][1]) / 2, det = A[0][0] * A[1][1] - A[0][1] * A[1][0], disc = s * s - det;
  const B = [[A[0][0] - s, A[0][1]], [A[1][0], A[1][1] - s]], By = [B[0][0] * y0[0] + B[0][1] * y0[1], B[1][0] * y0[0] + B[1][1] * y0[1]];
  const tm = ts[ts.length - 1] || 1, q = Math.sqrt(Math.abs(disc)), i = [], vc = [];
  for (const t of ts) {
    let c0, c1; // y = c0*y0 + c1*B*y0
    if (q * tm < 1e-6) { c0 = Math.exp(s * t); c1 = t * c0; }
    else if (disc < 0) { c0 = Math.exp(s * t) * Math.cos(q * t); c1 = Math.exp(s * t) * Math.sin(q * t) / q; }
    else { const l2 = s - q, l1 = det / l2, e1 = Math.exp(l1 * t), e2 = Math.exp(l2 * t); c0 = (e1 + e2) / 2; c1 = (e1 - e2) / (2 * q); }
    i.push(iss + c0 * y0[0] + c1 * By[0]); vc.push(vss + c0 * y0[1] + c1 * By[1]);
  }
  return { i, vc, iss, vss, s, det, disc };
}
function rlcCore(v, a) {
  const L = v.L, Cc = v.C_cap, V = v.V_s, Rt = v.R + (a.ideal_L ? 0 : v.R_w) + (a.ideal_source ? 0 : v.R_src), Rp = a.no_leak ? Infinity : v.R_p;
  const gp = a.no_leak ? 0 : 1 / (Rp * Cc), alpha = (Rt / L + gp) / 2, wn = Math.sqrt(Rt / L * gp + 1 / (L * Cc)), zeta = alpha / wn;
  const w0 = 1 / Math.sqrt(L * Cc), Q = w0 * L / Rt;
  const slow = zeta > 1 ? wn * wn / (alpha + Math.sqrt(alpha * alpha - wn * wn)) : alpha;
  const tEnd = Math.max(3 * TAU / wn, Math.min(8 / slow, 60 * TAU / wn)), n = 900;
  const stiff = 4 * zeta * zeta > 2000;
  const Ld = i => (a.linear_L ? L : L / (1 + (i / v.I_sat) ** 2));
  let t, iL, vC, eRes = 0, method, truncated = false;
  if (stiff && a.linear_L) {
    t = N.linspace(0, tEnd, n); const ex = rlcExact(Rt, L, Cc, Rp, V, t); iL = ex.i; vC = ex.vc; method = 'exact';
  } else {
    const r = N.rk45((tt, y) => [(V - Rt * y[0] - y[1]) / Ld(y[0]), (y[0] - (a.no_leak ? 0 : y[1] / Rp)) / Cc, V * y[0], Rt * y[0] * y[0] + (a.no_leak ? 0 : y[1] * y[1] / Rp)], [0, 0, 0, 0], 0, tEnd, n, { rtol: 1e-7, atol: 1e-11 * Math.max(V, 1e-6), maxSteps: 60000 });
    t = r.t; iL = r.y[0]; vC = r.y[1]; method = 'rk45'; truncated = r.t.length < n;
    const k = t.length - 1, iE = iL[k], wL = a.linear_L ? 0.5 * L * iE * iE : 0.5 * L * v.I_sat ** 2 * Math.log(1 + (iE / v.I_sat) ** 2);
    eRes = r.y[2][k] !== 0 ? (r.y[2][k] - r.y[3][k] - wL - 0.5 * Cc * vC[k] ** 2) / Math.abs(r.y[2][k]) : 0;
  }
  // small-signal impedance seen by the source and capacitor-voltage gain
  const resp = f => { const w = TAU * f, zc = a.no_leak ? [0, -1 / (w * Cc)] : cdiv([Rp, 0], [1, w * Rp * Cc]), z = cadd([Rt, w * L], zc); return { z, h: cdiv(zc, z) }; };
  return { L, Cc, V, Rt, Rp, alpha, wn, zeta, w0, Q, tEnd, t, iL, vC, eRes, method, truncated, resp, vss: a.no_leak ? V : V * Rp / (Rt + Rp) };
}

const rlc = {
  id: 'rlc-circuit',
  title: 'Series RLC circuit: step and frequency response',
  module: [1, 2], klass: 'I', domains: ['electromagnetic'],
  keywords: ['rlc circuit', 'rlc', 'resonant circuit', 'series resonance', 'lc circuit', 'quality factor', 'q factor', 'damping ratio', 'step response', 'ringing', 'inductor', 'capacitor', 'resonance', 'bandwidth', 'tank circuit', 'circuit'],
  summary: 'Step response and frequency response of a series resistor–inductor–capacitor circuit: resonance, quality factor, damping regime, overshoot and settling.',
  background: [
    'A resistor, inductor and capacitor in series form the electrical analogue of a damped mass–spring oscillator. Kirchhoff\'s voltage law gives a second-order linear differential equation whose character is fixed by the damping ratio ζ = (R/2)√(C/L): under-damped (ringing) for ζ < 1, critically damped at ζ = 1 and over-damped above.',
    'Driven sinusoidally, the circuit resonates at ω₀ = 1/√(LC), where the inductive and capacitive reactances cancel and the impedance falls to the resistance. The sharpness of the resonance is the quality factor Q = ω₀L/R, equal to the ratio of the resonant frequency to the half-power bandwidth.',
  ],
  phenomena: ['Energy exchange between electric and magnetic storage', 'Ohmic dissipation', 'Resonance', 'Transient ringing', 'Inductor saturation'],
  laws: ['energy', 'charge', 'ohm', 'maxwell'],
  refs: ['Horowitz, P. & Hill, W. (2015). The Art of Electronics, 3rd ed., Cambridge University Press.', 'Nilsson, J. W. & Riedel, S. A. (2019). Electric Circuits, 11th ed., Pearson.', 'Feynman, R. P., Leighton, R. B. & Sands, M. (1964). The Feynman Lectures on Physics, Vol. II, ch. 22–23, Addison-Wesley.'],
  inputs: [
    inp('R', 'Series resistance', 'ohm', 10, { min: 0.1, max: 1e4, aliases: ['resistance', 'resistor', 'ohm', 'ohms'] }),
    inp('L', 'Inductance', 'mH', 10, { min: 1e-3, max: 1e4, aliases: ['inductance', 'inductor', 'henry', 'mh'] }),
    inp('C_cap', 'Capacitance', 'uF', 1, { min: 1e-3, max: 1e4, aliases: ['capacitance', 'capacitor', 'farad', 'uf', 'microfarad'] }),
    inp('V_s', 'Source step voltage', 'V', 5, { min: 0.01, max: 1000, aliases: ['voltage', 'step', 'source', 'supply'] }),
    inp('f_d', 'Drive frequency for the steady-state response', 'Hz', 1000, { min: 1, max: 1e6, aliases: ['frequency', 'drive frequency', 'hz'] }),
    inp('R_w', 'Inductor winding resistance', 'ohm', 2, { min: 0, max: 1000, aliases: ['winding resistance', 'esr'] }),
    inp('R_src', 'Source output resistance', 'ohm', 50, { min: 0, max: 1000, aliases: ['source resistance', 'output resistance'], src: 'Common signal-generator output impedance' }),
    inp('R_p', 'Capacitor leakage (parallel) resistance', 'kohm', 100, { min: 0.1, max: 1e6, aliases: ['leakage', 'parallel resistance'] }),
    inp('I_sat', 'Inductor saturation current scale', 'A', 0.2, { min: 1e-3, max: 100, aliases: ['saturation current'] }),
  ],
  assumptions: [
    asm('linear_L', 'The inductance is independent of current.', { why: 'Air core, or currents well below saturation', alt: 'The core saturates: the differential inductance falls as L/(1 + (i/I_sat)²).' }),
    asm('ideal_L', 'The inductor has no winding resistance.', { why: 'Loss lumped into the series resistor', alt: 'A winding resistance R_w adds to the series resistance.' }),
    asm('ideal_source', 'The source has zero output resistance.', { why: 'Stiff voltage source', alt: 'The source resistance R_src adds to the series resistance.' }),
    asm('no_leak', 'The capacitor has no leakage.', { why: 'Film and ceramic capacitors at low frequency', alt: 'A leakage resistance R_p in parallel with the capacitor adds damping and lowers the final voltage.' }),
  ],
  symbols: { i: ['Loop current', 'A'], v_C: ['Capacitor voltage', 'V'], t: ['Time', 's'], R_t: ['Total series resistance', 'ohm'], omega_0: ['Undamped resonant angular frequency', '1/s'], Q: ['Quality factor', '1'], zeta: ['Damping ratio', '1'], omega_d: ['Damped angular frequency', '1/s'], Z_d: ['Impedance magnitude at the drive frequency', 'ohm'], L_d: ['Differential inductance', 'H'], BW: ['Half-power bandwidth', 'Hz'], f_0: ['Resonant frequency', 'Hz'] },
  equations: a => [
    eq('kvl', 'Kirchhoff voltage law around the loop', `${a.linear_L ? 'L' : 'L_d'}*d(i,t) + R_t*i + v_C`, 'V_s', { kind: 'law', origin: 'Faraday\'s law and conservation of energy around a closed loop' }),
    ...(a.linear_L ? [] : [eq('sat', 'Saturating differential inductance', 'L_d', 'L/(1 + (i/I_sat)^2)', { kind: 'closure', origin: 'Smooth saturation law for a gapped ferromagnetic core' })]),
    a.no_leak
      ? eq('cap', 'Capacitor charge balance', 'C_cap*d(v_C,t)', 'i', { kind: 'law', origin: 'Conservation of charge', needs: ['no_leak'] })
      : eq('cap', 'Capacitor charge balance with leakage', 'C_cap*d(v_C,t)', 'i - v_C/R_p', { kind: 'law', origin: 'Conservation of charge' }),
    eq('rt', 'Total series resistance', 'R_t', `R${a.ideal_L ? '' : ' + R_w'}${a.ideal_source ? '' : ' + R_src'}`, { kind: 'definition' }),
    eq('w0', 'Resonant angular frequency', 'omega_0', '1/sqrt(L*C_cap)', { kind: 'derived', origin: 'Reactances cancel' }),
    eq('f0', 'Resonant frequency', 'f_0', 'omega_0/(2*pi)', { kind: 'definition' }),
    eq('q', 'Quality factor', 'Q', 'omega_0*L/R_t', { kind: 'definition' }),
    eq('zeta', 'Damping ratio', 'zeta', 'R_t/2*sqrt(C_cap/L)', { kind: 'derived' }),
    eq('wd', 'Damped angular frequency', 'omega_d', 'omega_0*sqrt(1 - zeta^2)', { kind: 'derived', note: 'Real only when under-damped' }),
    eq('bw', 'Half-power bandwidth', 'BW', 'f_0/Q', { kind: 'derived' }),
    eq('z', 'Impedance magnitude', 'Z_d', 'sqrt(R_t^2 + (2*pi*f_d*L - 1/(2*pi*f_d*C_cap))^2)', { kind: 'derived', origin: 'Phasor sum of resistance and reactances' }),
  ],
  derivation: a => [
    { text: 'The voltages across inductor, resistor and capacitor sum to the source voltage.', tex: 'L\\frac{\\mathrm{d}i}{\\mathrm{d}t} + R_t\\,i + v_C = V_s' },
    { text: 'The current charges the capacitor' + (a.no_leak ? '.' : ', less the leakage current.'), tex: a.no_leak ? 'C\\frac{\\mathrm{d}v_C}{\\mathrm{d}t} = i' : 'C\\frac{\\mathrm{d}v_C}{\\mathrm{d}t} = i - \\frac{v_C}{R_p}' },
    { text: 'Eliminating the current gives the damped-oscillator equation with natural frequency ω₀ and damping ratio ζ.', tex: '\\ddot v_C + 2\\zeta\\omega_0\\,\\dot v_C + \\omega_0^2\\,v_C = \\omega_0^2 V_s,\\quad \\omega_0=\\frac{1}{\\sqrt{LC}},\\ \\zeta=\\frac{R_t}{2}\\sqrt{\\frac{C}{L}}' },
    { text: 'For ζ < 1 the step response rings at the damped frequency inside an exponential envelope.', tex: 'v_C = V_s\\left[1 - e^{-\\zeta\\omega_0 t}\\left(\\cos\\omega_d t + \\frac{\\zeta\\omega_0}{\\omega_d}\\sin\\omega_d t\\right)\\right]' },
    { text: 'With a sinusoidal source the phasor impedance is R + j(ωL − 1/ωC); its magnitude is least, and equal to R, at resonance. The half-power points are separated by ω₀/Q.', tex: '|Z| = \\sqrt{R_t^2 + \\left(\\omega L - \\frac{1}{\\omega C}\\right)^2},\\qquad Q = \\frac{\\omega_0 L}{R_t}' },
  ],
  solve(v, a) {
    const c = rlcCore(v, a), { t, iL, vC, V, Rt } = c, k = t.length - 1, warnings = [];
    const regime = c.zeta < 0.999 ? 'Under-damped (ringing)' : c.zeta <= 1.001 ? 'Critically damped' : 'Over-damped';
    let ip = 0; for (let j = 1; j <= k; j++) if (vC[j] > vC[ip]) ip = j;
    const os = Math.max(0, (vC[ip] - c.vss) / c.vss);
    let js = 0; for (let j = k; j >= 0; j--) if (Math.abs(vC[j] - c.vss) > 0.02 * Math.abs(c.vss)) { js = Math.min(j + 1, k); break; }
    if (c.truncated) warnings.push('The transient is too stiff for the explicit integrator with a saturating inductor; the response shown is truncated.');
    if (!a.linear_L) { const im = N.maxOf(iL.map(Math.abs)); if (im < 0.1 * v.I_sat) warnings.push('The current stays far below the saturation scale, so the saturating inductor behaves linearly here.'); }
    const d = c.resp(v.f_d), Zd = cabs(d.z), Id = V / Zd;
    const fs = N.logspace(c.w0 / TAU / 30, c.w0 / TAU * 30, 241), rs = fs.map(c.resp);
    const f0 = c.w0 / TAU;
    return {
      scalars: [
        scalar('f_0', 'Resonant frequency', f0, 'Hz'), scalar('omega_0', 'Resonant angular frequency', c.w0, '1/s'),
        scalar('Z_0', 'Characteristic impedance √(L/C)', Math.sqrt(c.L / c.Cc), 'ohm'),
        scalar('R_t', 'Total series resistance', Rt, 'ohm'),
        scalar('Q', 'Quality factor', c.Q, '1'), scalar('zeta', 'Damping ratio', c.zeta, '1', { note: regime }),
        scalar('regime', 'Damping regime', c.zeta < 0.999 ? 0 : c.zeta <= 1.001 ? 1 : 2, '1', { text: regime }),
        scalar('f_dmp', 'Damped (ringing) frequency', c.zeta < 1 ? c.wn * Math.sqrt(1 - c.zeta * c.zeta) / TAU : 0, 'Hz', c.zeta < 1 ? {} : { text: 'None — no oscillation' }),
        scalar('tau_env', 'Decay time constant of the envelope', 1 / c.alpha, 's', { show: 'ms' }),
        scalar('BW', 'Half-power bandwidth', f0 / c.Q, 'Hz'),
        scalar('v_pk', 'Peak capacitor voltage after the step', vC[ip], 'V'), scalar('OS', 'Overshoot', os, '1', { show: '%' }),
        scalar('t_set', 'Settling time to within 2 %', t[js], 's', { show: 'ms' }),
        scalar('i_pk', 'Peak current after the step', N.maxOf(iL), 'A'),
        scalar('Z_d', 'Impedance magnitude at the drive frequency', Zd, 'ohm'), scalar('I_d', 'Current amplitude at the drive frequency', Id, 'A'),
        scalar('phi_d', 'Phase of current relative to source voltage', -Math.atan2(d.z[1], d.z[0]), 'rad', { show: 'deg' }),
        scalar('G_d', 'Capacitor-voltage gain at the drive frequency', cabs(d.h), '1'),
        scalar('P_d', 'Mean power dissipated at the drive frequency', 0.5 * Id * Id * d.z[0], 'W'),
      ],
      series: [
        line('step', 'Step response', 'Time', 'ms', t.map(q => q * 1e3), [{ label: 'Capacitor voltage', data: vC }, { label: 'Final value', data: t.map(() => c.vss), dash: true }], 'Voltage', 'V'),
        line('step-current', 'Loop current after the step', 'Time', 'ms', t.map(q => q * 1e3), [{ label: 'Current', data: iL.map(q => q * 1e3) }], 'Current', 'mA'),
        line('gain', 'Capacitor-voltage gain against frequency', 'Frequency', 'Hz', fs, [{ label: '|V_C/V_s|', data: rs.map(q => cabs(q.h)) }], 'Gain', '–', { logx: true, logy: true }),
        line('phase', 'Phase of capacitor voltage against frequency', 'Frequency', 'Hz', fs, [{ label: 'Phase', data: rs.map(q => Math.atan2(q.h[1], q.h[0]) * 180 / Math.PI) }], 'Phase', 'deg', { logx: true }),
      ],
      checks: [check('Energy balance over the transient', c.eRes, 1e-5, c.method === 'rk45' ? 'Energy delivered by the source against stored plus dissipated energy' : 'Not evaluated: closed-form solution used for a very stiff over-damped circuit')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], c = rlcCore(v, a);
    if (a.linear_L && c.method === 'rk45') {
      const j = Math.round(c.t.length / 3), ex = rlcExact(c.Rt, c.L, c.Cc, c.Rp, c.V, [c.t[j]]);
      out.push(bench('Step response against the closed-form solution', c.vC[j], ex.vc[0], 'Exact solution of the linear second-order system', 1e-5));
    }
    if (a.no_leak) {
      const f0 = c.w0 / TAU;
      out.push(bench('Impedance at resonance equals the resistance', cabs(c.resp(f0).z), c.Rt, '|Z(ω₀)| = R', 1e-9));
      const hp = f => cabs(c.resp(f).z) - Math.SQRT2 * c.Rt, f1 = N.findRoot(hp, f0 * 1e-6, f0), f2 = N.findRoot(hp, f0, f0 * 1e6);
      out.push(bench('Half-power bandwidth equals f₀/Q', f2 - f1, f0 / c.Q, 'Exact for a series RLC circuit', 1e-6));
    }
    if (a.linear_L && a.no_leak && c.zeta < 1) {
      const ex = rlcExact(c.Rt, c.L, c.Cc, Infinity, 1, [Math.PI / (c.w0 * Math.sqrt(1 - c.zeta ** 2))]);
      out.push(bench('First overshoot against exp(−πζ/√(1−ζ²))', ex.vc[0] - 1, Math.exp(-Math.PI * c.zeta / Math.sqrt(1 - c.zeta ** 2)), 'Standard second-order result', 1e-9));
    }
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.path('M120 250 L120 90 L200 90 M280 90 L340 90 M420 90 L520 90 L520 150 M520 190 L520 250 L120 250', 'd-line')}
      ${S.circle(120, 170, 24, 'd-body')} ${S.text(120, 175, 'V_s')} ${S.text(72, 175, lab(v.V_s, 'V'), 'd-text d-small', 'end')}
      ${S.rect(200, 76, 80, 28, 'd-body')} ${S.text(240, 66, `R = ${lab(v.R, 'Ω')}`)}
      ${S.path('M340 90 q10 -26 20 0 q10 -26 20 0 q10 -26 20 0 q10 -26 20 0', 'd-line')} ${S.text(380, 56, `L = ${lab(v.L * 1e3, 'mH')}`)}
      ${S.line(496, 150, 544, 150)} ${S.line(496, 190, 544, 190)} ${S.text(556, 175, `C = ${lab(v.C_cap * 1e6, 'µF')}`, 'd-text', 'start')}
      ${a.no_leak ? '' : S.path('M520 120 L590 120 L590 150 M590 190 L590 220 L520 220', 'd-line') + S.rect(580, 150, 20, 40, 'd-body') + S.text(606, 215, 'R_p', 'd-text d-small', 'start')}
      ${S.arrow(300, 250, 260, 250)} ${S.text(280, 272, 'i(t)')}
      ${S.text(320, 320, `f₀ = ${lab(1 / (TAU * Math.sqrt(v.L * v.C_cap)), 'Hz')}`)}
    `);
  },
  experiment: {
    objective: 'Record the step response and the frequency response of a series RLC circuit and compare the measured resonant frequency, quality factor and overshoot with prediction.',
    apparatus: ['Film capacitor, air-core or gapped inductor and metal-film resistor on a low-inductance board', 'Function generator with square and sine outputs', 'Buffer amplifier if the generator impedance is not negligible'],
    instruments: [{ name: 'Digital oscilloscope with ×10 probes', measures: 'Capacitor voltage and, across the resistor, loop current', range: 'DC–100 MHz', resolution: '8–12 bit, ±2 %' }, { name: 'LCR meter', measures: 'Component values and inductor series resistance at the resonant frequency', range: '20 Hz–1 MHz', resolution: '±0.2 %' }, { name: 'Frequency counter', measures: 'Ringing and drive frequency', range: 'to 10 MHz', resolution: '±1 ppm' }],
    procedure: ['Measure R, L, C and the winding resistance with the LCR meter.', 'Apply a slow square wave and capture the capacitor voltage; read the ringing period, the first overshoot and the logarithmic decrement.', 'Sweep a sine wave through resonance and record the amplitude and phase of the capacitor voltage at 20 or more frequencies.', 'Repeat with two further resistor values, including one near critical damping.'],
    controls: ['Replace the inductor with a short to confirm the RC time constant', 'Measure with the probe on the generator alone to establish source loading'],
    signatures: ['Ringing frequency independent of step amplitude (linearity)', 'Successive peak ratios constant (exponential envelope)', 'Phase of capacitor voltage passing through −90° at resonance'],
    safety: ['Capacitor voltage at resonance is Q times the source amplitude: check component ratings', 'Discharge the capacitor before handling'],
  },
  falsify: ['A ringing frequency that changes with amplitude in a circuit with an air-core inductor.', 'A measured quality factor that disagrees with ω₀L/R_t by more than the component uncertainties once all series losses are included.', 'A half-power bandwidth that is not f₀/Q.'],
  alternatives: [{ name: 'Parallel RLC circuit', text: 'The dual arrangement: impedance is greatest at resonance and Q = R√(C/L).' }, { name: 'Distributed (transmission-line) resonator', text: 'When the circuit is not small compared with the wavelength, lumped elements no longer describe it and standing-wave modes appear.' }, { name: 'Frequency-dependent loss', text: 'Skin effect and core loss make the effective resistance rise with frequency, so Q is not simply proportional to ω₀.' }],
  hazards: [{ hazard: 'Over-voltage at resonance', cause: 'Voltage magnification by Q', mitigation: 'Rate capacitor and inductor insulation for Q times the drive amplitude' }, { hazard: 'Stored energy', cause: 'Charged capacitor or energised inductor at switch-off', mitigation: 'Bleed resistor and freewheel path' }],
  standards: ['IEC 60384 series (fixed capacitors for use in electronic equipment)', 'IEC 62024-1 (high-frequency inductive components: electrical characteristics and measuring methods)', 'IEC 61010-1 (safety requirements for electrical equipment for measurement, control and laboratory use)'],
  limits: 'Lumped, linear, time-invariant elements (apart from the optional smooth saturation law), frequencies low enough that the circuit is small compared with the wavelength and that parasitic capacitance of the inductor is negligible.',
  numerics: { method: 'Adaptive Dormand–Prince Runge–Kutta for the transient, with energy integrals carried as extra states; closed-form matrix exponential when the linear circuit is very stiff; phasor algebra for the frequency response', order: 5, stability: 'Explicit: step limited by the fastest time constant' },
  optimise: { objective: 't_set', sense: 'min', vars: ['R'], note: 'Settling is fastest slightly below critical damping.' },
  inverse: { series: 'step', fit: ['R', 'L'] },
  extensions: ['Parallel and series–parallel topologies', 'Frequency-dependent resistance from skin effect', 'Coupled resonators and band-pass filters', 'Hysteretic core model'],
};

// ------------------------------------------------------------------ electrohydrodynamic (ionic-wind) thruster
/** One-dimensional unipolar drift region: current density, field profile, thrust and power per unit area. */
function ehd(v, a) {
  const rho = v.rho_air, mu = a.mu_const ? v.mu_i : v.mu_i * 1.225 / rho, V = v.V, d = v.d_gap;
  const Jmg = 9 / 8 * EPS0 * mu * V * V / d ** 3;
  // potential difference across the gap for current density J, emitter-side field E0 and bulk gas speed u
  const Vint = (J, E0, u) => { const a0 = (u + mu * E0) ** 2, b = 2 * mu * J / EPS0; return b * d < 1e-7 * a0 ? E0 * d + J * d * d / (2 * EPS0 * (u + mu * E0)) : (-u * d + 2 / (3 * b) * (Math.pow(a0 + b * d, 1.5) - Math.pow(a0, 1.5))) / mu; };
  const Eat = (J, E0, u, x) => (-u + Math.sqrt((u + mu * E0) ** 2 + 2 * mu * J * x / EPS0)) / mu;
  const dragF = a.no_drag ? 0 : v.C_d * v.t_c / (4 * v.w_c);
  const Jt = v.k_T * EPS0 * mu * V * Math.max(V - v.V_on, 0) / (d * d) / v.w_c;
  let u = 0, J = 0, E0 = 0, Ed = 0, TA = 0, Tn = 0, ud = 0, Jscl = Jmg, capped = false;
  for (let k = 0; k < 20; k++) {
    Jscl = u > 0 ? rootOr(q => Vint(q, 0, u) - V, Jmg, Jmg * (1 + u * d / (mu * V)) ** 2 * 1.02, Jmg) : Jmg;
    if (a.scl) { J = Jscl; E0 = 0; }
    else {
      capped = Jt >= Jscl; J = Math.min(Jt, Jscl);
      E0 = J <= 0 ? V / d : capped ? 0 : rootOr(q => Vint(J, q, u) - V, 0, V / d, 0);
    }
    Ed = Eat(J, E0, u, d); TA = EPS0 * (Ed * Ed - E0 * E0) / 2; Tn = TA / (1 + dragF);
    const un = Math.sqrt(Math.max(Tn, 0) / (2 * rho));
    if (a.static) { ud = un; break; }
    if (Math.abs(un - u) <= 1e-10 * Math.max(un, 1e-12)) { ud = un; u = un; break; }
    u = ud = un;
  }
  const uI = a.static ? 0 : ud;
  return { mu, V, d, Jmg, Jscl, J, E0, Ed, TA, Tn, ud, uI, capped, Jt, E: x => Eat(J, E0, uI, x), tp: J > 0 ? Tn / (J * V) : d / (mu * V) / (1 + dragF) };
}

const ionicWind = {
  id: 'ionic-wind-thruster',
  title: 'Ionic-wind (electrohydrodynamic) thruster and hover feasibility',
  module: [1, 2], klass: ['I', 'II'], domains: ['electromagnetic', 'aerospace'],
  keywords: ['ionic wind', 'ion wind', 'electrohydrodynamic', 'ehd thruster', 'ehd', 'corona thruster', 'ionocraft', 'lifter', 'ion drift', 'solid-state propulsion', 'electroaerodynamic', 'corona discharge', 'thrust-to-power', 'biefeld-brown', 'hover', 'thrust to weight', 'space-charge limited', 'mott-gurney'],
  summary: 'One-dimensional ion-drift thruster: space-charge-limited or corona current, thrust, thrust-to-power, induced jet velocity, thrust-density limit, total thrust of an annular array and a thrust-to-weight verdict including the mass of the high-voltage supply.',
  background: [
    'A corona discharge at a thin emitter produces ions of one polarity that drift through neutral air to a collector. Each ion is pushed by the electric field and passes that momentum to the air through collisions; the reaction on the electrodes is a thrust. Because the mechanism is a body force on charged air, it requires an atmosphere and vanishes in vacuum.',
    'This physics is measured and uncontroversial. For one-dimensional unipolar drift the thrust is T = I d/μ and the thrust-to-power ratio is 1/(μE), so efficiency improves at low field while thrust per unit area, bounded by the space-charge limit (9/8)ε₀V²/d², improves at high field (Masuyama & Barrett 2013). A fixed-wing aeroplane of 2.45 kg has flown in steady level flight on this principle, with wings providing the lift (Xu et al. 2018).',
    'What has not been demonstrated is a practical craft that hovers on ion-drift thrust alone while carrying its own power supply and useful payload: thrust densities of a few newtons per square metre and thrust-to-power of order 5–20 N/kW set a demanding mass budget. Claims of thrust in vacuum, or of thrust beyond the momentum given to the air, have not survived controlled tests (Tajmar 2004). This model computes the measured mechanism only and reports whether the stated mass budget closes.',
  ],
  phenomena: ['Corona ionisation at the emitter', 'Unipolar ion drift', 'Ion–neutral momentum transfer', 'Space-charge limitation of current', 'Induced air jet', 'Electrical breakdown limit'],
  laws: ['charge', 'maxwell', 'momentum', 'newton3', 'energy', 'mass'],
  refs: ['Masuyama, K. & Barrett, S. R. H. (2013). On the performance of electrohydrodynamic propulsion. Proc. R. Soc. A 469, 20120623.', 'Xu, H., He, Y., Strobel, K. L., Gilmore, C. K., Kelley, S. P., Hennick, C. C., Sebastian, T., Woolston, M. R., Perreault, D. J. & Barrett, S. R. H. (2018). Flight of an aeroplane with solid-state propulsion. Nature 563, 532–535.', 'Mott, N. F. & Gurney, R. W. (1940). Electronic Processes in Ionic Crystals, Oxford University Press.', 'Townsend, J. S. (1914). The potentials required to maintain currents between coaxial cylinders. Phil. Mag. 28, 83–90.', 'Robinson, M. (1961). Movement of air in the electric wind of the corona discharge. Trans. AIEE 80, 143–150.', 'Tajmar, M. (2004). Biefeld–Brown effect: misinterpretation of corona wind phenomena. AIAA Journal 42, 315–318.'],
  inputs: [
    inp('V', 'Applied voltage', 'kV', 40, { min: 5, max: 150, aliases: ['voltage', 'kv', 'potential'] }),
    inp('d_gap', 'Emitter-to-collector gap', 'mm', 50, { min: 5, max: 300, kind: 'geometry', aliases: ['gap', 'electrode gap', 'spacing', 'separation'] }),
    inp('mu_i', 'Ion mobility at sea-level density', 'cm^2/(V s)', 2.0, { min: 0.5, max: 3, kind: 'fluid', aliases: ['mobility', 'ion mobility'], src: 'Positive ions in air at 1 atm, about 2×10⁻⁴ m²/(V s)' }),
    inp('b_s', 'Emitter span of one sector', 'm', 1, { min: 0.05, max: 10, kind: 'geometry', aliases: ['span', 'emitter length', 'wire length'] }),
    inp('w_c', 'Width of the drift region (collector chord)', 'mm', 60, { min: 5, max: 500, kind: 'geometry', aliases: ['collector width', 'chord', 'drift width'] }),
    inp('N_s', 'Number of sectors in the annular array', '1', 8, { min: 1, max: 200, kind: 'geometry', aliases: ['sectors', 'segments', 'stages', 'number of sectors'] }),
    inp('V_on', 'Corona-onset voltage', 'kV', 10, { min: 0.5, max: 60, aliases: ['onset voltage', 'corona onset', 'inception voltage'] }),
    inp('k_T', 'Townsend current coefficient', '1', 1, { min: 0.05, max: 5, aliases: ['townsend coefficient', 'current coefficient'], src: 'Geometry-dependent; fit to a measured current–voltage curve' }),
    inp('rho_air', 'Air density', 'kg/m^3', 1.225, { min: 0.3, max: 1.5, kind: 'environment', env: 'air_density', aliases: ['air density', 'density'] }),
    inp('E_bd', 'Mean field at spark-over', 'MV/m', 3, { min: 0.5, max: 5, kind: 'environment', aliases: ['breakdown field', 'breakdown strength'], src: 'Uniform-field strength of dry air at 1 atm; practical gaps spark at lower mean field' }),
    inp('t_c', 'Collector thickness facing the flow', 'mm', 5, { min: 0.1, max: 50, kind: 'geometry', aliases: ['collector thickness'] }),
    inp('C_d', 'Collector drag coefficient', '1', 1.0, { min: 0.01, max: 2, aliases: ['drag coefficient'], src: 'About 1 for a circular cylinder at Reynolds numbers 10³–10⁵; far lower for an aerofoil section' }),
    inp('m_0', 'Fixed mass: airframe, payload and energy store', 'kg', 0.5, { min: 0.001, max: 100, aliases: ['mass', 'payload', 'airframe mass', 'weight'] }),
    inp('m_A', 'Electrode structure mass per unit drift area', 'kg/m^2', 0.1, { min: 0.005, max: 5, kind: 'geometry', aliases: ['areal mass', 'structure mass'] }),
    inp('sp_psu', 'Specific power of the high-voltage supply', 'kW/kg', 1, { min: 0.05, max: 20, aliases: ['specific power', 'power density', 'converter'], src: 'Order of magnitude for a lightweight custom converter; verify for the chosen unit' }),
  ],
  assumptions: [
    asm('scl', 'The current is space-charge limited (Mott–Gurney): the field at the emitter side of the drift region falls to zero.', { why: 'Upper bound on current and thrust density in one dimension', alt: 'The current follows the Townsend corona law I′ = k_T ε₀ μ V (V − V_on)/d² per unit emitter length, capped at the space-charge limit.' }),
    asm('mu_const', 'Ion mobility equals its sea-level value.', { why: 'Operation near standard density', alt: 'Mobility scales inversely with air density, μ = μ_i ρ_ref/ρ.' }),
    asm('static', 'The air moves slowly compared with the ion drift speed, so ions travel at μE.', { why: 'Drift speed is of order 100 m/s; induced flow is a few m/s', alt: 'Ions travel at μE + u, with u the induced air speed; thrust-to-power becomes 1/(μE + u).' }),
    asm('no_drag', 'The electrodes add no aerodynamic drag to the induced flow.', { why: 'Idealised upper bound', alt: 'Collector drag ½ρu²C_d on its frontal area is subtracted from the thrust.' }),
    asm('psu_onboard', 'The high-voltage supply is carried on board; its mass is power divided by specific power.', { why: 'Required for free flight', alt: 'The supply is on the ground (tethered test); its mass is excluded from the weight.' }),
  ],
  symbols: { mu_e: ['Effective ion mobility', 'm^2/(V s)'], rho_ref: ['Reference air density 1.225 kg/m³', 'kg/m^3'], E: ['Electric field in the drift region', 'V/m'], x: ['Distance from the emitter', 'm'], rho_q: ['Ion charge density', 'C/m^3'], J: ['Current density', 'A/m^2'], I_l: ['Current per unit emitter length', 'A/m'], T_A: ['Electrostatic thrust per unit area', 'N/m^2'], T_n: ['Net thrust per unit area', 'N/m^2'], E_d: ['Field at the collector', 'V/m'], E_e: ['Field at the emitter side', 'V/m'], theta_TP: ['Thrust-to-power ratio', 'N/W'], u_d: ['Induced air speed at the electrode plane', 'm/s'], T: ['Total thrust', 'N'], P: ['Total electrical power', 'W'], W: ['Total weight', 'N'], TWR: ['Thrust-to-weight ratio', '1'], T_max: ['Thrust density at the spark-over field', 'N/m^2'] },
  equations: a => [
    a.mu_const ? eq('mob', 'Ion mobility', 'mu_e', 'mu_i', { kind: 'closure', needs: ['mu_const'] }) : eq('mob', 'Ion mobility scaled with gas density', 'mu_e', 'mu_i*rho_ref/rho_air', { kind: 'closure', origin: 'Constant reduced mobility: mobility inversely proportional to gas number density' }),
    eq('gauss', 'Gauss\'s law in the drift region', 'eps_0*pd(E,x)', 'rho_q', { kind: 'law', origin: 'Maxwell\'s equations' }),
    a.static ? eq('drift', 'Ion drift current', 'J', 'rho_q*mu_e*E', { kind: 'closure', origin: 'Mobility-limited drift', needs: ['static'] }) : eq('drift', 'Ion drift and convection current', 'J', 'rho_q*(mu_e*E + u_d)', { kind: 'closure', origin: 'Mobility-limited drift relative to moving air' }),
    ...(a.scl
      ? [a.static ? eq('mg', 'Space-charge-limited current density', 'J', '9/8*eps_0*mu_e*V^2/d_gap^3', { kind: 'derived', origin: 'Mott–Gurney law: Gauss\'s law with drift current and zero emitter field', needs: ['scl', 'static'] }) : eq('mg', 'Space-charge limit with moving air', 'V', 'int(E, x)', { kind: 'boundary', origin: 'Voltage constraint with zero emitter-side field', needs: ['scl'] })]
      : [eq('town', 'Corona current per unit emitter length', 'I_l', 'k_T*eps_0*mu_e*V*(V - V_on)/d_gap^2', { kind: 'empirical', origin: 'Townsend (1914) quadratic corona law' }), eq('jl', 'Current density', 'J', 'I_l/w_c', { kind: 'definition' })]),
    eq('force', 'Coulomb body force on the air', 'T_A', 'int(rho_q*E, x)', { kind: 'law', origin: 'Lorentz force on the ions, transferred to neutrals by collisions; reaction on the electrodes by Newton\'s third law' }),
    a.static ? eq('thr', 'Thrust per unit area', 'T_A', 'J*d_gap/mu_e', { kind: 'derived', origin: 'Body-force integral with J = ρ_q μ E', needs: ['static'] }) : eq('thr', 'Thrust per unit area from the Maxwell stress', 'T_A', 'eps_0*(E_d^2 - E_e^2)/2', { kind: 'derived', origin: 'Body-force integral with Gauss\'s law' }),
    a.static ? eq('tp', 'Thrust-to-power ratio', 'theta_TP', 'd_gap/(mu_e*V)', { kind: 'derived', needs: ['static'] }) : eq('tp', 'Thrust-to-power ratio', 'theta_TP', 'T_n/(J*V)', { kind: 'definition' }),
    a.no_drag ? eq('net', 'Net thrust per unit area', 'T_n', 'T_A', { kind: 'closure', needs: ['no_drag'] }) : eq('net', 'Net thrust per unit area after collector drag', 'T_n', 'T_A/(1 + C_d*t_c/(4*w_c))', { kind: 'derived', origin: 'Drag ½ρu²C_d on the collector frontal area with u from momentum theory' }),
    eq('ud', 'Induced air speed at the electrode plane', 'u_d', 'sqrt(T_n/(2*rho_air))', { kind: 'derived', origin: 'Actuator-disc momentum theory at zero flight speed' }),
    eq('tot', 'Total thrust of the array', 'T', 'T_n*N_s*b_s*w_c', { kind: 'definition' }),
    eq('pow', 'Total electrical power', 'P', 'J*V*N_s*b_s*w_c', { kind: 'law', origin: 'Joule\'s law' }),
    a.psu_onboard ? eq('wt', 'Total weight with on-board supply', 'W', 'g*(m_0 + m_A*N_s*b_s*w_c + P/sp_psu)', { kind: 'definition', needs: ['psu_onboard'] }) : eq('wt', 'Total weight, supply off board', 'W', 'g*(m_0 + m_A*N_s*b_s*w_c)', { kind: 'definition' }),
    eq('twr', 'Thrust-to-weight ratio', 'TWR', 'T/W', { kind: 'definition' }),
    eq('lim', 'Thrust density at the spark-over field', 'T_max', '9/8*eps_0*E_bd^2', { kind: 'derived', origin: 'Space-charge limit evaluated at the largest sustainable mean field' }),
  ],
  derivation: a => [
    { text: 'Ions of charge density ρ_q drift at speed μE through the air, carrying a current density that is the same at every plane between the electrodes (charge conservation in steady state).', tex: 'J = \\rho_q\\,\\mu\\,E = \\text{const}' },
    { text: 'Gauss\'s law links the field gradient to the charge.', tex: '\\varepsilon_0\\frac{\\mathrm{d}E}{\\mathrm{d}x} = \\rho_q = \\frac{J}{\\mu E}\\ \\Rightarrow\\ E^2 = E_e^2 + \\frac{2Jx}{\\varepsilon_0\\mu}' },
    { text: a.scl ? 'The largest current is reached when the charge screens the emitter-side field to zero. Integrating the field to obtain the voltage gives the Mott–Gurney law.' : 'Below the space-charge limit the current is set by the corona, which follows Townsend\'s quadratic law above the onset voltage.', tex: a.scl ? 'J = \\frac{9}{8}\\,\\varepsilon_0\\,\\mu\\,\\frac{V^2}{d^3}' : 'I\' = k_T\\,\\varepsilon_0\\,\\mu\\,\\frac{V\\,(V-V_{on})}{d^2}' },
    { text: 'The force on the air is the Coulomb force on the ions; since ρ_q E = J/μ is uniform, the thrust per unit area is simply J d/μ, and the thrust of a device carrying current I is I d/μ.', tex: '\\frac{T}{A} = \\int_0^d \\rho_q E\\,\\mathrm{d}x = \\frac{J\\,d}{\\mu},\\qquad T = \\frac{I\\,d}{\\mu}' },
    { text: 'Dividing by the electrical power IV gives the thrust-to-power ratio, which depends only on mobility and mean field.', tex: '\\frac{T}{P} = \\frac{d}{\\mu V} = \\frac{1}{\\mu \\bar E}' },
    { text: 'Momentum theory for a static actuator disc relates thrust density to the induced air speed at the disc and in the far wake.', tex: 'u_d = \\sqrt{\\frac{T/A}{2\\rho}},\\qquad u_\\infty = 2u_d' },
    { text: 'Hover requires thrust to exceed the weight of everything carried, including the supply whose mass grows with power.', tex: '\\frac{T}{W} = \\frac{T}{g\\,(m_0 + m_A A + P/\\sigma_P)} \\ge 1' },
  ],
  solve(v, a) {
    const s = ehd(v, a), Ns = Math.max(1, Math.round(v.N_s)), A1 = v.b_s * v.w_c, A = Ns * A1, warnings = [];
    const T = s.Tn * A, P = s.J * s.V * A, mPsu = a.psu_onboard ? P / v.sp_psu : 0, mTot = v.m_0 + v.m_A * A + mPsu, W = g0 * mTot, TWR = T / W;
    const Emean = s.V / s.d, Tmax = 9 / 8 * EPS0 * v.E_bd ** 2;
    if (Emean > v.E_bd) warnings.push('The mean field exceeds the spark-over field: the gap would arc rather than sustain a corona. The result is not physically attainable.');
    else if (Emean > 0.5 * v.E_bd) warnings.push('The mean field is above half the uniform-field strength of air; practical wire-to-collector gaps usually spark before this point.');
    if (!a.scl && s.V <= v.V_on) warnings.push('The applied voltage is below corona onset: no ion current flows and there is no thrust.');
    if (!a.scl && s.capped) warnings.push('The Townsend law would exceed the one-dimensional space-charge limit at this voltage; the current has been capped at that limit.');
    if (a.scl) warnings.push('The space-charge limit is an upper bound: measured wire-to-collector currents are usually several times lower, so thrust and power are optimistic.');
    // profiles on a grid clustered toward the emitter
    const n = 200, sg = N.linspace(0, 1, n), xg = sg.map(q => s.d * q * q), Eg = xg.map(s.E);
    const vNum = N.trapz(sg, Eg.map((e, i) => e * 2 * s.d * sg[i]));
    let jRes = 0;
    if (s.J > 0) for (let i = 0; i < n - 1; i++) { const sm = (sg[i] + sg[i + 1]) / 2, rq = EPS0 * (Eg[i + 1] - Eg[i]) / (xg[i + 1] - xg[i]); jRes = Math.max(jRes, Math.abs(rq * (s.mu * s.E(s.d * sm * sm) + s.uI) / s.J - 1)); }
    const fNum = s.J > 0 ? N.trapz(sg, Eg.map((e, i) => s.J / (s.mu * e + s.uI + 1e-300) * e * 2 * s.d * sg[i])) : 0;
    const rq = xg.map((_, i) => (s.J > 0 ? s.J / (s.mu * Eg[i] + s.uI) : 0));
    // sweeps in voltage
    const Vs = N.linspace(0.2 * s.V, 1.6 * s.V, 36), sw = Vs.map(q => ehd({ ...v, V: q }, a));
    const feasible = TWR >= 1;
    const verdict = feasible
      ? `Thrust exceeds weight by ${lab((TWR - 1) * 100, '%')} on these inputs — hover is possible in principle, subject to the breakdown and drag warnings.`
      : `Thrust is ${lab(TWR * 100, '%')} of the weight — the craft cannot hover on these inputs.`;
    const twrInf = s.Tn / (g0 * (v.m_A + (a.psu_onboard ? s.J * s.V / v.sp_psu : 0)));
    return {
      scalars: [
        scalar('mu_e', 'Effective ion mobility', s.mu, 'm^2/(V s)'), scalar('E_mean', 'Mean drift field V/d', Emean, 'V/m', { show: 'MV/m' }),
        scalar('J', 'Current density', s.J, 'A/m^2', { show: 'mA/m^2' }), scalar('J_scl', 'Space-charge-limited current density', s.Jscl, 'A/m^2', { show: 'mA/m^2' }),
        scalar('I_s', 'Current per sector', s.J * A1, 'A', { show: 'mA' }), scalar('I_tot', 'Total current', s.J * A, 'A', { show: 'mA' }),
        scalar('T_A', 'Electrostatic thrust per unit area', s.TA, 'N/m^2'), scalar('T_n', 'Net thrust per unit area', s.Tn, 'N/m^2'),
        scalar('T_max', 'Thrust density at the spark-over field', Tmax, 'N/m^2'),
        scalar('T_s', 'Thrust per sector', s.Tn * A1, 'N'), scalar('T', 'Total thrust of the array', T, 'N'),
        scalar('P', 'Total electrical power', P, 'W'), scalar('theta_TP', 'Thrust-to-power ratio', s.tp, 'N/W', { show: 'N/kW' }),
        scalar('u_d', 'Induced air speed at the electrode plane', s.ud, 'm/s'), scalar('u_w', 'Far-wake jet speed', 2 * s.ud, 'm/s'),
        scalar('v_ion', 'Ion drift speed at the mean field', s.mu * Emean, 'm/s'),
        scalar('eta', 'Electrical-to-jet efficiency T·u_d/P', P > 0 ? T * s.ud / P : 0, '1', { show: '%' }),
        scalar('A_tot', 'Total drift area', A, 'm^2'), scalar('R_m', 'Mean radius of the annulus', Ns * v.b_s / TAU, 'm'),
        scalar('m_psu', 'Supply mass carried', mPsu, 'kg'), scalar('m_tot', 'Total mass', mTot, 'kg'), scalar('W', 'Total weight', W, 'N'),
        scalar('TWR', 'Thrust-to-weight ratio', TWR, '1'), scalar('TWR_inf', 'Thrust-to-weight of the bare array and supply (no fixed mass)', twrInf, '1'),
        scalar('hover', 'Hover feasible on these inputs', feasible ? 1 : 0, '1', { text: verdict }),
      ],
      series: [
        line('iv', 'Current against voltage', 'Voltage', 'kV', Vs.map(q => q / 1e3), [{ label: 'Total current', data: sw.map(q => q.J * A * 1e3) }], 'Current', 'mA'),
        line('thrust-voltage', 'Thrust against voltage', 'Voltage', 'kV', Vs.map(q => q / 1e3), [{ label: 'Total thrust', data: sw.map(q => q.Tn * A) }, { label: 'Weight', data: sw.map(q => g0 * (v.m_0 + v.m_A * A + (a.psu_onboard ? q.J * q.V * A / v.sp_psu : 0))), dash: true }], 'Force', 'N'),
        line('tp-voltage', 'Thrust-to-power against voltage', 'Voltage', 'kV', Vs.map(q => q / 1e3), [{ label: 'Thrust-to-power', data: sw.map(q => q.tp * 1e3) }], 'Thrust-to-power', 'N/kW'),
        line('profiles', 'Field across the drift region', 'Distance from emitter', 'mm', xg.slice(1).map(q => q * 1e3), [{ label: 'Electric field', data: Eg.slice(1).map(q => q / 1e6) }, { label: 'Mean field V/d', data: xg.slice(1).map(() => Emean / 1e6), dash: true }], 'Field', 'MV/m'),
        line('charge', 'Ion charge density across the drift region', 'Distance from emitter', 'mm', xg.slice(4).map(q => q * 1e3), [{ label: 'Charge density', data: rq.slice(4).map(q => q * 1e6) }], 'Charge density', 'µC/m³'),
      ],
      checks: [
        check('Voltage equals the integral of the field', (vNum - s.V) / s.V, 1e-4, 'Numerical quadrature of the field profile'),
        check('Charge conservation with Gauss\'s law', jRes, 1e-3, 'ε₀ dE/dx times drift speed reproduces the same current density at every station'),
        check('Thrust equals the body-force integral', s.TA > 0 ? (fNum - s.TA) / s.TA : 0, 1e-4, 'Integrated Coulomb force on the air against the Maxwell-stress difference at the electrodes'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { ...a, scl: true, static: true, no_drag: true }, s = ehd(v, b), out = [];
    out.push(bench('Mott–Gurney current density', s.J, 9 / 8 * EPS0 * s.mu * v.V ** 2 / v.d_gap ** 3, 'J = (9/8) ε₀ μ V²/d³', 1e-12));
    out.push(bench('Thrust per unit area equals J d/μ', s.TA, s.J * v.d_gap / s.mu, 'T = I d/μ', 1e-9));
    out.push(bench('Thrust-to-power equals d/(μV)', s.tp, v.d_gap / (s.mu * v.V), 'T/P = 1/(μE)', 1e-9));
    const m = ehd(v, { ...b, static: false });
    out.push(bench('Moving-air solution recovers the static limit to first order in u/(μE)', m.tp * (1 + m.ud / (m.mu * v.V / v.d_gap)), s.tp, 'T/P ≈ 1/(μE + u)', 0.02));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const xs = [150, 230, 310, 390, 470];
    return svg(`
      ${xs.map(x => S.circle(x, 90, 3, 'd-hazard')).join('')} ${S.text(520, 94, 'emitter wires, +V', 'd-text d-small', 'start')}
      ${xs.map(x => S.rect(x - 14, 230, 28, 10, 'd-body', 5)).join('')} ${S.text(520, 240, 'collector, earthed', 'd-text d-small', 'start')}
      ${xs.map(x => S.arrow(x, 104, x, 222)).join('')} ${S.text(96, 165, 'ion drift', 'd-text d-small')}
      ${S.arrow(310, 60, 310, 22, 'd-arrow d-heat')} ${S.text(326, 34, 'thrust on electrodes', 'd-text', 'start')}
      ${S.arrow(270, 262, 270, 310)} ${S.arrow(350, 262, 350, 310)} ${S.text(310, 330, 'induced air jet')}
      ${S.dim(60, 90, 60, 235, '')} ${S.text(54, 100, `d = ${lab(v.d_gap * 1e3, 'mm')}`, 'd-text d-small', 'start')}
      ${S.text(320, 350, `${lab(v.V / 1e3, 'kV')}   ${Math.round(v.N_s)} sectors × ${lab(v.b_s, 'm')} span${a.psu_onboard ? '   supply on board' : '   supply off board'}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure thrust, current and voltage of a wire-to-collector thruster and test T = I d/μ and T/P = d/(μV); then repeat at reduced pressure to confirm that the thrust requires air.',
    apparatus: ['Emitter wire (25–100 µm) and smooth cylindrical or aerofoil collector on a light insulating frame', 'Regulated high-voltage direct supply with current limit', 'Earthed screened enclosure; a vacuum chamber for the control experiment', 'Grounded mesh between thruster and balance to exclude electrostatic attraction to the surroundings'],
    instruments: [{ name: 'Precision balance or torsion pendulum', measures: 'Thrust', range: '0–1 N', resolution: '±0.1 mN' }, { name: 'High-voltage divider', measures: 'Applied voltage', range: '0–100 kV', resolution: '±1 %' }, { name: 'Shunt microammeter on the earthed collector', measures: 'Ion current', range: '1 µA–10 mA', resolution: '±1 %' }, { name: 'Hot-wire or Pitot traverse', measures: 'Induced jet velocity profile', range: '0.1–10 m/s', resolution: '±3 %' }, { name: 'Barometer, thermometer, hygrometer', measures: 'Air density and humidity', range: 'ambient', resolution: '±0.5 hPa, ±0.2 K, ±2 % RH' }],
    procedure: ['Record the zero of the balance with the supply connected but off.', 'Raise the voltage in steps from below onset to just below spark-over; at each step record voltage, current and thrust after the reading settles.', 'Plot thrust against I d and fit the slope to obtain 1/μ.', 'Repeat for three gaps and for both polarities.', 'Integrate the measured jet momentum flux and compare with the balance thrust.', 'Repeat in a chamber at several pressures down to high vacuum.'],
    controls: ['Reversed polarity: thrust direction unchanged (toward the emitter side), ruling out simple electrostatic attraction', 'Shielded dummy load drawing the same current with no corona: zero thrust', 'High-vacuum run: thrust falls to zero within resolution'],
    signatures: ['Thrust proportional to current times gap', 'Current following V(V − V_on)', 'Thrust-to-power falling as 1/V at fixed gap', 'Jet momentum flux equal to thrust'],
    safety: ['Lethal voltages: interlocked enclosure, earthing stick, current-limited supply', 'Ozone and nitrogen oxides from the corona: ventilate and monitor', 'Ultraviolet emission and radio-frequency interference from sparks'],
  },
  falsify: ['Thrust persisting in high vacuum with the same current would contradict the ion-drift mechanism.', 'Thrust not proportional to I d at fixed mobility, beyond what electrode drag and non-uniform fields explain.', 'A measured thrust-to-power ratio well above d/(μV) in still air.', 'Jet momentum flux that does not account for the measured thrust.'],
  alternatives: [{ name: 'Electrostatic attraction to surroundings', text: 'Image charges in nearby earthed objects attract a charged frame; this is a static force, independent of current, and is removed by shielding.' }, { name: 'Claims of thrust without reaction mass', text: 'Reports of a force on asymmetric capacitors in vacuum (the so-called Biefeld–Brown effect) have not been reproduced in controlled experiments; measured forces vanish with the air.' }, { name: 'Multi-stage and ducted designs', text: 'Stacking stages in series raises the pressure rise and jet speed; ducting recovers some thrust, at the cost of mass and drag.' }, { name: 'Dielectric-barrier discharge actuators', text: 'Alternating-voltage surface discharges give a wall jet without a free emitter wire, with different scaling.' }],
  hazards: [{ hazard: 'Electric shock', cause: 'Exposed emitters at tens of kilovolts', mitigation: 'Guarding, interlocks, current limiting, discharge of stored energy' }, { hazard: 'Ozone and nitrogen oxides', cause: 'Corona chemistry in air', mitigation: 'Ventilation; monitor against occupational exposure limits' }, { hazard: 'Fire', cause: 'Spark-over igniting light structures or vapours', mitigation: 'Operate below spark-over; non-flammable materials' }, { hazard: 'Electromagnetic interference', cause: 'Corona and spark emission', mitigation: 'Screening and filtering' }],
  standards: ['IEC 61010-1 (safety requirements for electrical equipment for measurement, control and laboratory use)', 'IEC 60060-1 (high-voltage test techniques)', 'National workplace exposure limits for ozone'],
  limits: 'One-dimensional unipolar drift at atmospheric pressure, steady direct voltage, zero flight speed. Real wire-to-collector fields are strongly non-uniform, so currents lie well below the planar space-charge limit; the Townsend coefficient must be fitted to data. Humidity, electrode contamination, reverse corona at the collector and spark-over are not modelled.',
  numerics: { method: 'Closed-form field profile with root finding for the emitter-side field or limiting current; fixed-point iteration on the induced air speed', stability: 'Monotone bracketing; converges in a few iterations' },
  optimise: { objective: 'TWR', sense: 'max', vars: ['V', 'd_gap'], note: 'High field raises thrust density but lowers thrust-to-power; the best gap balances supply mass against structure mass, and must stay below spark-over.' },
  inverse: { series: 'iv', fit: ['mu_i'] },
  logicPreset: {
    atoms: [{ k: 'H', text: 'The craft hovers carrying its own supply' }, { k: 'W', text: 'Thrust is at least the total weight' }, { k: 'D', text: 'Thrust density stays below the space-charge limit at spark-over' }, { k: 'M', text: 'Supply specific power is high enough for the thrust-to-power achieved' }],
    premises: ['H -> W', 'W -> (D & M)'], conclusion: 'H -> M',
  },
  extensions: ['Two-dimensional wire-to-cylinder field with self-consistent space charge', 'Forward-flight performance with ion slip', 'Multi-stage arrays and duct effects', 'Battery mass and endurance'],
};

// ------------------------------------------------------------------ Helmholtz-resonator synthetic jet
function sjCore(v, a) {
  const rc = v.D_c / 2, ro = v.d_o / 2, Ao = Math.PI * ro * ro, Vc = Math.PI * rc * rc * v.H_c;
  const Leff = v.l_o + (a.end_corr ? 1.7 * ro : 0), fH = v.c_s / TAU * Math.sqrt(Ao / (Vc * Leff));
  const dV = (a.clamped ? 1 / 3 : 1) * Math.PI * rc * rc * v.delta_0;
  const Ca = Vc / (v.rho * v.c_s ** 2), Ma = v.rho * Leff / Ao, Rv = 8 * v.rho * v.nu * v.l_o / (Math.PI * ro ** 4), kn = 4 * v.K_o * v.rho / (3 * Math.PI * Ao * Ao);
  /** Orifice volume-velocity amplitude at frequency f; `lossless` drops both resistances. */
  const Qo = (f, incompressible = a.incompressible, lossless = false) => {
    const w = TAU * f, Qd = w * dV;
    if (incompressible) return Qd;
    const x = Math.abs(1 - w * w * Ma * Ca);
    if (lossless) return Qd / Math.max(x, 1e-12);
    const gq = q => q * Math.hypot(x, w * Ca * (Rv + kn * q)) - Qd;
    const hi = Math.min(Qd / Math.max(x, 1e-12), Math.sqrt(Qd / (w * Ca * kn))) * 1.0001;
    return rootOr(gq, 0, hi, hi);
  };
  const press = (f, q) => q * Math.hypot(TAU * f * Ma, Rv + kn * q);
  return { rc, ro, Ao, Vc, Leff, fH, dV, Ca, Ma, Rv, kn, Qo, press };
}

const syntheticJet = {
  id: 'helmholtz-synthetic-jet',
  title: 'Piezo-driven Helmholtz synthetic-jet actuator',
  module: 2, klass: 'I', domains: ['waves', 'aerospace', 'mechanical'],
  keywords: ['synthetic jet', 'zero net mass flux', 'znmf', 'helmholtz resonator', 'helmholtz resonance', 'piezo actuator', 'piezoelectric diaphragm', 'jet actuator', 'orifice', 'cavity', 'stroke length', 'vortex ring', 'flow control', 'helmholtz'],
  summary: 'Lumped model of a cavity-and-orifice actuator driven by an oscillating diaphragm: Helmholtz resonance, orifice velocity, stroke length, Reynolds and Stokes numbers, jet-formation criterion, time-mean momentum flux (thrust) and power.',
  background: [
    'A synthetic jet is produced by a diaphragm that alternately expels fluid from a cavity through an orifice and draws it back. Over a cycle no net mass leaves the cavity, yet a steady jet forms: on the outstroke the flow separates at the orifice edge and rolls up into a vortex ring that carries momentum away, while on the instroke fluid is drawn in from all directions like a sink. Zero net mass flux therefore does not mean zero net momentum flux.',
    'The cavity and orifice form a Helmholtz resonator — the air in the neck is a mass, the air in the cavity a spring — with natural frequency f_H = (c/2π)√(A/(V L_eff)). Well below f_H the cavity air is effectively incompressible and the orifice flow equals the volume swept by the diaphragm; near f_H the orifice flow is amplified, limited mainly by nonlinear orifice loss. A jet escapes only if the ejected ring travels far enough not to be re-ingested: the criterion of Holman et al. (2005) is Re/S² greater than about 0.16 for a round orifice and about 1 for a two-dimensional slot.',
  ],
  phenomena: ['Helmholtz resonance', 'Vortex-ring formation and escape', 'Oscillatory orifice flow with separation', 'Rectification of oscillatory flow into mean momentum', 'Viscous and nonlinear orifice loss'],
  laws: ['mass', 'momentum', 'energy', 'newton2'],
  refs: ['Smith, B. L. & Glezer, A. (1998). The formation and evolution of synthetic jets. Phys. Fluids 10, 2281–2297.', 'Glezer, A. & Amitay, M. (2002). Synthetic jets. Annu. Rev. Fluid Mech. 34, 503–529.', 'Holman, R., Utturkar, Y., Mittal, R., Smith, B. L. & Cattafesta, L. (2005). Formation criterion for synthetic jets. AIAA Journal 43, 2110–2116.', 'Gallas, Q., Holman, R., Nishida, T., Carroll, B., Sheplak, M. & Cattafesta, L. (2003). Lumped element modeling of piezoelectric-driven synthetic jet actuators. AIAA Journal 41, 240–247.', 'Kinsler, L. E., Frey, A. R., Coppens, A. B. & Sanders, J. V. (2000). Fundamentals of Acoustics, 4th ed., Wiley.'],
  inputs: [
    inp('D_c', 'Cavity (diaphragm) diameter', 'mm', 30, { min: 5, max: 200, kind: 'geometry', aliases: ['cavity diameter', 'diaphragm diameter', 'membrane diameter'] }),
    inp('H_c', 'Cavity depth', 'mm', 5, { min: 0.5, max: 100, kind: 'geometry', aliases: ['cavity depth', 'cavity height'] }),
    inp('d_o', 'Orifice diameter', 'mm', 2, { min: 0.2, max: 20, kind: 'geometry', aliases: ['orifice diameter', 'orifice', 'nozzle diameter', 'hole'] }),
    inp('l_o', 'Orifice (neck) length', 'mm', 2, { min: 0.2, max: 30, kind: 'geometry', aliases: ['neck length', 'orifice length', 'plate thickness'] }),
    inp('f_d', 'Drive frequency', 'Hz', 300, { min: 10, max: 20000, aliases: ['frequency', 'drive frequency', 'hz'] }),
    inp('delta_0', 'Diaphragm centre displacement amplitude', 'um', 50, { min: 1, max: 2000, aliases: ['displacement', 'deflection', 'stroke', 'amplitude'] }),
    inp('c_s', 'Speed of sound', 'm/s', 343, { min: 200, max: 1500, kind: 'fluid', aliases: ['speed of sound', 'sound speed'], src: 'Air at 20 °C' }),
    inp('rho', 'Fluid density', 'kg/m^3', 1.2, { min: 0.3, max: 1.5, kind: 'environment', env: 'air_density', aliases: ['density', 'air density'] }),
    inp('nu', 'Kinematic viscosity', 'm^2/s', 1.5e-5, { min: 5e-6, max: 5e-5, kind: 'fluid', aliases: ['viscosity', 'kinematic viscosity'], src: 'Air at 20 °C' }),
    inp('K_o', 'Orifice loss coefficient', '1', 1, { min: 0.2, max: 3, aliases: ['loss coefficient', 'discharge loss'], src: 'Order one for a sharp-edged orifice in oscillatory flow' }),
    inp('K_j', 'Jet-formation constant', '1', 0.16, { min: 0.05, max: 2, aliases: ['formation constant', 'formation criterion'], src: 'Holman et al. (2005): about 0.16 for round orifices, about 1 for two-dimensional slots' }),
    inp('eta_e', 'Electrical-to-fluidic efficiency', '%', 5, { min: 0.1, max: 50, aliases: ['efficiency'], src: 'User estimate; depends on the piezo element and drive electronics' }),
  ],
  assumptions: [
    asm('incompressible', 'The cavity air is incompressible: the orifice volume flow equals the diaphragm volume velocity.', { why: 'Valid well below the Helmholtz frequency', alt: 'Cavity compliance, neck inertance and orifice resistance are included (lumped-element model), giving resonant amplification.' }),
    asm('end_corr', 'The oscillating mass includes an end correction of 0.85 orifice radii at each end of the neck.', { why: 'Fluid just outside a flanged opening moves with the plug', alt: 'The effective length is the geometric neck length.' }),
    asm('clamped', 'The diaphragm deflects as a clamped circular plate, w(r) = δ₀(1 − r²/a²)².', { why: 'Edge-bonded piezo disc', alt: 'The diaphragm moves as a rigid piston over the full cavity area.' }),
    asm('slug', 'The orifice velocity is uniform across the exit (slug profile).', { why: 'High Stokes number', alt: 'A parabolic profile is assumed: momentum flux is 4/3 and kinetic-energy flux twice the slug value at the same mean velocity.' }),
  ],
  symbols: { A_o: ['Orifice area', 'm^2'], V_c: ['Cavity volume', 'm^3'], L_eff: ['Effective neck length', 'm'], f_H: ['Helmholtz frequency', 'Hz'], dV: ['Volume displaced by the diaphragm', 'm^3'], Q_d: ['Diaphragm volume-velocity amplitude', 'm^3/s'], U_o: ['Orifice velocity amplitude', 'm/s'], C_a: ['Acoustic compliance of the cavity', 'm^3/Pa'], M_a: ['Acoustic mass of the neck', 'kg/m^4'], R_a: ['Acoustic resistance of the orifice', 'Pa s/m^3'], L_0: ['Stroke length', 'm'], Re_j: ['Jet Reynolds number', '1'], S_t: ['Stokes number', '1'], F_j: ['Jet-formation parameter Re/S²', '1'], T_j: ['Time-mean thrust', 'N'], P_f: ['Fluidic power', 'W'], P_e: ['Electrical power', 'W'] },
  equations: a => [
    eq('ao', 'Orifice area', 'A_o', 'pi*d_o^2/4', { kind: 'definition' }),
    eq('vc', 'Cavity volume', 'V_c', 'pi*D_c^2/4*H_c', { kind: 'definition' }),
    a.end_corr ? eq('leff', 'Effective neck length', 'L_eff', 'l_o + 0.85*d_o', { kind: 'closure', origin: 'Flanged-opening end correction 8a/(3π) at each end' }) : eq('leff', 'Effective neck length', 'L_eff', 'l_o', { kind: 'closure' }),
    eq('fh', 'Helmholtz frequency', 'f_H', 'c_s/(2*pi)*sqrt(A_o/(V_c*L_eff))', { kind: 'derived', origin: 'Neck mass on cavity spring' }),
    a.clamped ? eq('dv', 'Volume displaced, clamped plate', 'dV', 'pi*D_c^2*delta_0/12', { kind: 'derived', origin: 'Integral of the clamped-plate deflection', needs: ['clamped'] }) : eq('dv', 'Volume displaced, piston', 'dV', 'pi*D_c^2*delta_0/4', { kind: 'definition' }),
    eq('qd', 'Diaphragm volume velocity', 'Q_d', '2*pi*f_d*dV', { kind: 'derived' }),
    ...(a.incompressible
      ? [eq('uo', 'Orifice velocity amplitude', 'U_o', 'Q_d/A_o', { kind: 'law', origin: 'Conservation of mass for incompressible cavity fluid', needs: ['incompressible'] })]
      : [eq('ca', 'Cavity compliance', 'C_a', 'V_c/(rho*c_s^2)', { kind: 'derived', origin: 'Isentropic compression' }), eq('ma', 'Neck acoustic mass', 'M_a', 'rho*L_eff/A_o', { kind: 'derived' }),
        eq('ra', 'Orifice resistance', 'R_a', '8*rho*nu*l_o/(pi*(d_o/2)^4) + 4*K_o*rho*U_o/(3*pi*A_o)', { kind: 'closure', origin: 'Poiseuille resistance plus the describing-function equivalent of a quadratic orifice loss' }),
        eq('uo', 'Orifice velocity amplitude', 'U_o*A_o*sqrt((1 - (2*pi*f_d)^2*M_a*C_a)^2 + (2*pi*f_d*R_a*C_a)^2)', 'Q_d', { kind: 'derived', origin: 'Mass balance of the compressible cavity with momentum balance of the neck' })]),
    eq('l0', 'Stroke length', 'L_0', 'U_o/(pi*f_d)', { kind: 'derived', origin: 'Integral of the exit velocity over the expulsion half-cycle' }),
    eq('re', 'Jet Reynolds number', 'Re_j', '2*U_o*d_o/(pi*nu)', { kind: 'definition', origin: 'Based on the mean expulsion velocity' }),
    eq('st', 'Stokes number', 'S_t', 'sqrt(2*pi*f_d*d_o^2/nu)', { kind: 'definition' }),
    eq('fj', 'Jet-formation parameter', 'F_j', 'Re_j/S_t^2', { kind: 'empirical', origin: 'Holman et al. (2005): a jet forms when this exceeds K_j', note: 'Equal to the inverse Strouhal number' }),
    eq('thr', 'Time-mean thrust', 'T_j', `${a.slug ? '' : '4/3*'}rho*A_o*U_o^2/4`, { kind: 'derived', origin: 'Momentum of the fluid slug ejected each cycle' }),
    eq('pf', 'Fluidic power', 'P_f', `${a.slug ? '' : '2*'}rho*A_o*U_o^3/(3*pi)`, { kind: 'derived', origin: 'Kinetic-energy flux during expulsion' }),
    eq('pe', 'Electrical power', 'P_e', 'P_f/eta_e', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'The plug of air in the neck, of mass ρ A L_eff, is pushed by the cavity pressure. A displacement ξ of the plug changes the cavity volume by Aξ and the pressure isentropically.', tex: '\\rho A L_{eff}\\,\\ddot\\xi = -\\frac{\\rho c^2 A^2}{V}\\,\\xi \\ \\Rightarrow\\ f_H = \\frac{c}{2\\pi}\\sqrt{\\frac{A}{V L_{eff}}}' },
    { text: 'The diaphragm sweeps a volume ΔV each quarter cycle, giving a volume-velocity amplitude ωΔV.', tex: a.clamped ? '\\Delta V = \\int_0^a \\delta_0\\left(1-\\tfrac{r^2}{a^2}\\right)^2 2\\pi r\\,\\mathrm{d}r = \\tfrac{\\pi}{3}a^2\\delta_0' : '\\Delta V = \\pi a^2 \\delta_0' },
    { text: a.incompressible ? 'Well below resonance the cavity fluid is incompressible, so all the swept volume passes through the orifice.' : 'With cavity compliance C, neck mass M and resistance R the orifice flow follows a driven second-order system.', tex: a.incompressible ? 'U_o = \\frac{\\omega\\,\\Delta V}{A_o}' : '\\frac{Q_o}{Q_d} = \\frac{1}{1-\\omega^2 M_a C_a + j\\omega R_a C_a}' },
    { text: 'The length of the fluid slug pushed out in one outstroke is the stroke length.', tex: 'L_0 = \\int_0^{T/2} U_o\\sin\\omega t\\,\\mathrm{d}t = \\frac{U_o}{\\pi f}' },
    { text: 'A vortex ring escapes re-ingestion when its self-induced speed carries it clear during the instroke; this reduces to a threshold on the inverse Strouhal number.', tex: '\\frac{1}{Sr} = \\frac{\\bar U}{\\omega d} = \\frac{Re}{S^2} > K_j' },
    { text: 'Each outstroke ejects momentum ρA∫u² dt; the instroke draws fluid in from all sides and returns little directed momentum. Averaged over the cycle this is the thrust.', tex: 'T_j \\approx \\rho A_o f\\int_0^{T/2} U_o^2\\sin^2\\omega t\\,\\mathrm{d}t = \\tfrac14\\rho A_o U_o^2' },
  ],
  solve(v, a) {
    const c = sjCore(v, a), f = v.f_d, w = TAU * f, warnings = [];
    const Q = c.Qo(f), Uo = Q / c.Ao, Ubar = 2 * Uo / Math.PI, L0 = Uo / (Math.PI * f);
    const Re = Ubar * v.d_o / v.nu, St = Math.sqrt(w * v.d_o ** 2 / v.nu), Fj = Re / (St * St), formed = Fj > v.K_j;
    const bm = a.slug ? 1 : 4 / 3, be = a.slug ? 1 : 2;
    const Tj = formed ? bm * v.rho * c.Ao * Uo * Uo / 4 : 0, Pf = be * v.rho * c.Ao * Uo ** 3 / (3 * Math.PI), Pe = Pf / v.eta_e;
    if (a.incompressible && f > 0.5 * c.fH) warnings.push('The drive frequency is above half the Helmholtz frequency: cavity compressibility matters and the incompressible assumption should be switched off.');
    if (Uo / v.c_s > 0.3) warnings.push('The orifice Mach number exceeds 0.3; compressible orifice flow and choking are not modelled.');
    if (!formed) warnings.push('The jet-formation criterion is not met: the ejected vortex ring is drawn back on the instroke, so no steady jet and essentially no thrust results.');
    if (Math.max(v.D_c, v.H_c) > v.c_s / f / 6) warnings.push('The cavity is not small compared with the acoustic wavelength; the lumped description is unreliable.');
    if (St < 10 && a.slug) warnings.push('The Stokes number is below about 10: the exit profile is closer to parabolic than to a slug.');
    const fs = N.logspace(c.fH / 20, c.fH * 5, 140);
    const tt = N.linspace(0, 1 / f, 201), u = tt.map(t => Uo * Math.sin(w * t)), mf = u.map(q => bm * v.rho * c.Ao * q * q);
    const meanU = N.trapz(tt, u) * f, meanM = N.trapz(tt, mf) * f;
    return {
      scalars: [
        scalar('f_H', 'Helmholtz frequency', c.fH, 'Hz'), scalar('L_eff', 'Effective neck length', c.Leff, 'm', { show: 'mm' }),
        scalar('V_c', 'Cavity volume', c.Vc, 'm^3', { show: 'mL' }), scalar('dV', 'Volume displaced by the diaphragm', c.dV, 'm^3', { show: 'mL' }),
        scalar('Q_d', 'Diaphragm volume-velocity amplitude', w * c.dV, 'm^3/s', { show: 'L/s' }),
        scalar('U_o', 'Orifice velocity amplitude', Uo, 'm/s'), scalar('gain', 'Orifice flow / diaphragm flow', Q / (w * c.dV), '1'),
        scalar('U_bar', 'Mean velocity during expulsion', Ubar, 'm/s'), scalar('L_0', 'Stroke length', L0, 'm', { show: 'mm' }),
        scalar('L_d', 'Stroke ratio L₀/d', L0 / v.d_o, '1'),
        scalar('Re_j', 'Jet Reynolds number', Re, '1'), scalar('S_t', 'Stokes number', St, '1'),
        scalar('F_j', 'Jet-formation parameter Re/S²', Fj, '1', { text: `${lab(Fj)} — ${formed ? 'jet forms' : 'no jet'} (threshold ${lab(v.K_j)})` }),
        scalar('Ma', 'Orifice Mach number', Uo / v.c_s, '1'),
        scalar('p_c', 'Cavity pressure amplitude', c.press(f, Q), 'Pa'),
        scalar('T_j', 'Time-mean thrust (upper estimate)', Tj, 'N', { show: 'mN', note: 'Momentum of the ejected slug; suction-side pressure deficit and friction reduce it' }),
        scalar('M_dot', 'Mass expelled per second during outstrokes', v.rho * c.Ao * Uo / Math.PI, 'kg/s', { show: 'g/s' }),
        scalar('P_f', 'Fluidic power', Pf, 'W', { show: 'mW' }), scalar('P_e', 'Electrical power', Pe, 'W'),
        scalar('TP', 'Thrust per unit electrical power', Pe > 0 ? Tj / Pe : 0, 'N/W', { show: 'mN/W' }),
      ],
      series: [
        line('response', 'Orifice velocity amplitude against frequency', 'Frequency', 'Hz', fs, [{ label: 'Lumped-element model', data: fs.map(q => c.Qo(q, false) / c.Ao) }, { label: 'Incompressible cavity', data: fs.map(q => c.Qo(q, true) / c.Ao), dash: true }], 'Velocity amplitude', 'm/s', { logx: true, logy: true, note: 'Fixed diaphragm displacement amplitude' }),
        line('cycle', 'Orifice velocity over one cycle', 'Time', 'ms', tt.map(q => q * 1e3), [{ label: 'Exit velocity', data: u }, { label: 'Cycle mean (zero net mass flux)', data: tt.map(() => meanU), dash: true }], 'Velocity', 'm/s'),
        line('momentum', 'Momentum flux through the orifice plane', 'Time', 'ms', tt.map(q => q * 1e3), [{ label: 'Instantaneous ρAu²', data: mf.map(q => q * 1e3) }, { label: 'Ejected-slug mean (thrust estimate)', data: tt.map(() => bm * v.rho * c.Ao * Uo * Uo / 4 * 1e3), dash: true }], 'Momentum flux', 'mN'),
      ],
      checks: [
        check('Zero net mass flux over a cycle', meanU / Math.max(Uo, 1e-300), 1e-9, 'Cycle average of the exit velocity'),
        check('Mean momentum flux is positive and equals ½ρAβU²', meanM / (bm * v.rho * c.Ao * Uo * Uo / 2) - 1, 1e-6, 'Quadrature over one cycle; the momentum flux has the same sign on both strokes'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const c = sjCore(v, a), out = [];
    out.push(bench('Helmholtz frequency from lumped mass and compliance', 1 / (TAU * Math.sqrt(c.Ma * c.Ca)), c.fH, 'f_H = 1/(2π√(M_a C_a))', 1e-12));
    out.push(bench('Lossless amplification at half the Helmholtz frequency', c.Qo(c.fH / 2, false, true) / (Math.PI * c.fH * c.dV), 4 / 3, '1/(1 − (f/f_H)²)', 1e-9));
    const Uo = c.Qo(v.f_d) / c.Ao, tt = N.linspace(0, 0.5 / v.f_d, 801);
    out.push(bench('Stroke length by quadrature', N.trapz(tt, tt.map(t => Uo * Math.sin(TAU * v.f_d * t))), Uo / (Math.PI * v.f_d), 'L₀ = U_o/(πf)', 1e-5));
    return out;
  },
  validation: [],
  diagram(v) {
    return svg(`
      ${S.path('M200 90 L200 250 L440 250 L440 90', 'd-body')} ${S.path('M200 90 L296 90 M344 90 L440 90', 'd-pipe')}
      ${S.path('M200 250 Q320 222 440 250', 'd-hazard')} ${S.path('M200 250 Q320 278 440 250', 'd-dim')}
      ${S.text(320, 296, `diaphragm, ±${lab(v.delta_0 * 1e6, 'µm')} at ${lab(v.f_d, 'Hz')}`)}
      ${S.text(320, 175, `cavity  ⌀${lab(v.D_c * 1e3, 'mm')} × ${lab(v.H_c * 1e3, 'mm')}`)}
      ${S.arrow(320, 84, 320, 30, 'd-arrow d-heat')} ${S.text(336, 40, 'jet', 'd-text', 'start')}
      ${S.circle(296, 52, 9, 'd-line')} ${S.circle(344, 52, 9, 'd-line')} ${S.text(250, 48, 'vortex ring', 'd-text d-small', 'end')}
      ${S.arrow(250, 70, 300, 86)} ${S.arrow(390, 70, 340, 86)} ${S.text(460, 70, 'suction from all sides', 'd-text d-small', 'start')}
      ${S.dim(296, 110, 344, 110, `d = ${lab(v.d_o * 1e3, 'mm')}`)}
      ${S.text(320, 335, 'zero net mass flux, non-zero momentum flux', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the orifice velocity, the frequency response and the jet thrust of a piezo-driven cavity and compare with the lumped model and the formation criterion.',
    apparatus: ['Piezo-ceramic disc bonded to a brass shim, clamped over a machined cavity with interchangeable orifice plates', 'Signal generator and high-voltage piezo amplifier', 'Still-air enclosure', 'Light pendulum or balance for thrust'],
    instruments: [{ name: 'Laser Doppler vibrometer or displacement sensor', measures: 'Diaphragm centre displacement', range: '0–1 mm', resolution: '±1 µm' }, { name: 'Hot-wire anemometer (single wire) at the exit', measures: 'Exit velocity waveform', range: '0.2–80 m/s', resolution: '±3 %, 20 kHz' }, { name: 'Microbalance', measures: 'Time-mean thrust', range: '0–10 mN', resolution: '±5 µN' }, { name: 'Current probe and oscilloscope', measures: 'Electrical power', range: 'to 100 W', resolution: '±2 %' }, { name: 'Schlieren or smoke visualisation', measures: 'Vortex-ring formation and escape', range: '—', resolution: '—' }],
    procedure: ['At fixed drive voltage sweep frequency from one-tenth to three times the predicted Helmholtz frequency, recording diaphragm displacement and exit velocity amplitude.', 'At selected frequencies vary amplitude through the predicted formation threshold and note by visualisation whether rings escape.', 'Measure thrust with the actuator firing horizontally from the balance arm.', 'Traverse the hot-wire across the jet at several distances to integrate the mean momentum flux.'],
    controls: ['Blocked-orifice run to obtain diaphragm response without acoustic loading', 'De-rectify the hot-wire signal using the known phase to distinguish outflow from inflow'],
    signatures: ['Velocity amplitude proportional to frequency well below resonance at fixed displacement', 'A peak near the Helmholtz frequency', 'Jet onset at a stroke ratio near 0.5 for a round orifice', 'Thrust growing as the square of the velocity amplitude'],
    safety: ['Piezo amplifiers deliver hazardous voltage: insulate terminals', 'High sound levels near resonance: hearing protection', 'Do not exceed the depolarisation field or the fracture strain of the ceramic'],
  },
  falsify: ['A resonance in the measured orifice velocity far from f_H when the diaphragm resonance lies elsewhere.', 'Steady jets observed well below the formation threshold, or absent well above it.', 'A non-zero cycle-mean velocity at the exit plane (net mass flux) in a sealed actuator.', 'Measured thrust exceeding ρAU²/2, the total momentum flux through the exit plane.'],
  alternatives: [{ name: 'Coupled diaphragm–cavity model', text: 'The piezo diaphragm is itself a resonator; coupling it to the Helmholtz mode gives two peaks. A full lumped model includes the diaphragm compliance, mass and electromechanical transduction (Gallas et al. 2003).' }, { name: 'Acoustic streaming', text: 'At very small stroke ratios a weak mean flow can still arise from viscous attenuation of the sound field; it is a distinct mechanism from vortex-ring rectification.' }, { name: 'Continuous or pulsed jets', text: 'Supply net mass flux and therefore need plumbing, but are not limited by the formation criterion.' }],
  hazards: [{ hazard: 'Electric shock', cause: 'Piezo drive voltages of 100 V or more', mitigation: 'Insulation and enclosure' }, { hazard: 'Noise exposure', cause: 'Operation in the audible band near resonance', mitigation: 'Enclosure and hearing protection' }, { hazard: 'Diaphragm fracture', cause: 'Over-driving at resonance', mitigation: 'Amplitude limit and monitoring' }],
  standards: ['IEC 61010-1 (safety requirements for electrical equipment for measurement, control and laboratory use)', 'IEEE Std 176 (standard on piezoelectricity)', 'ISO 9612 (determination of occupational noise exposure)'],
  limits: 'Lumped elements: cavity and neck small compared with the wavelength. Prescribed diaphragm displacement (its structural resonance and loading by the cavity are not modelled). Quiescent surroundings, orifice Mach number below about 0.3, sinusoidal slug or parabolic exit profile. The thrust is an upper estimate from the ejected-slug momentum.',
  numerics: { method: 'Algebraic lumped-element relations; bracketed root finding for the amplitude-dependent orifice resistance; trapezoidal quadrature over the cycle' },
  optimise: { objective: 'T_j', sense: 'max', vars: ['d_o', 'f_d'], note: 'At fixed displacement, thrust rises steeply with frequency and with a smaller orifice until compressibility, loss or Mach number intervene.' },
  inverse: { series: 'response', fit: ['l_o', 'K_o'] },
  extensions: ['Coupled piezo-diaphragm dynamics with electromechanical transduction', 'Slot orifices and arrays', 'Interaction with a cross-flow boundary layer', 'Compressible orifice flow at high amplitude'],
};

// ------------------------------------------------------------------ acoustic radiation pressure and levitation
function arfCore(v, a) {
  const w = TAU * v.f_a, k = w / v.c_s, lam = v.c_s / v.f_a, kap = v.rho_0 * v.c_s ** 2;
  const Et = v.p_a ** 2 / (2 * kap), Eac = v.p_a ** 2 / (4 * kap), dl = Math.sqrt(2 * v.nu / w);
  const f1 = rp => (a.rigid ? 1 : 1 - kap / (rp * v.c_p ** 2));
  const f2 = (rp, R) => {
    const rt = rp / v.rho_0;
    if (a.inviscid) return 2 * (rt - 1) / (2 * rt + 1);
    const dt = dl / R, gam = [-1.5 * dt, -1.5 * (1 + dt) * dt];
    return cdiv(cmul([2 * (rt - 1), 0], csub([1, 0], gam)), csub([2 * rt + 1, 0], [3 * gam[0], 3 * gam[1]]))[0];
  };
  const Phi = (rp, R) => f1(rp) / 3 + f2(rp, R) / 2;
  const size = R => { if (a.small_sphere) return 1; const q = 2 * k * R; return q < 1e-3 ? 1 - q * q / 10 : 3 * (Math.sin(q) - q * Math.cos(q)) / q ** 3; };
  const Fmax = (rp, R) => 4 * Math.PI * R ** 3 * k * Eac * Phi(rp, R) * size(R);
  const Wt = (rp, R) => 4 / 3 * Math.PI * R ** 3 * (rp - v.rho_0) * g0;
  return { w, k, lam, kap, Et, Eac, dl, f1, f2, Phi, size, Fmax, Wt };
}

const radiationPressure = {
  id: 'acoustic-radiation-pressure',
  title: 'Acoustic radiation pressure and standing-wave levitation',
  module: [1, 2], klass: 'I', domains: ['waves'],
  keywords: ['acoustic radiation pressure', 'radiation pressure', 'acoustic levitation', 'acoustic radiation force', 'levitation', 'standing wave', 'ultrasonic', 'ultrasound', 'gorkov', 'radiation force', 'sound pressure', 'acoustic trap', 'acoustic tweezers'],
  summary: 'Time-averaged force of a sound wave: radiation pressure of a plane wave on an absorbing or reflecting target, and the Gor\'kov/King force on a small sphere in a standing wave, with the levitation margin, threshold pressure and largest levitated diameter.',
  background: [
    'A sound wave carries momentum as well as energy. Although the acoustic pressure averages to zero over a cycle, second-order terms do not: a plane wave of energy density E exerts a steady pressure E on a surface that absorbs it and 2E on one that reflects it. For a pressure amplitude p in a medium of density ρ and sound speed c the energy density is E = p²/(2ρc²).',
    'In a standing wave a particle much smaller than the wavelength feels a force that derives from a potential (Gor\'kov 1962). The potential combines a monopole term, from the particle\'s compressibility relative to the medium, and a dipole term, from its density contrast. A dense, stiff particle in air is driven toward the pressure nodes; the force amplitude for a rigid sphere reduces to King\'s (1934) formula. Levitation is possible when this force exceeds the weight. Because both scale with volume, the threshold in the small-sphere limit does not depend on size; the size limit comes from the breakdown of the small-sphere approximation as the diameter approaches half a wavelength.',
  ],
  phenomena: ['Momentum flux of a sound wave', 'Scattering from a compressible sphere', 'Trapping at pressure nodes', 'Viscous boundary layer around the particle'],
  laws: ['momentum', 'energy', 'mass', 'newton2'],
  refs: ['King, L. V. (1934). On the acoustic radiation pressure on spheres. Proc. R. Soc. Lond. A 147, 212–240.', 'Gor\'kov, L. P. (1962). On the forces acting on a small particle in an acoustical field in an ideal fluid. Sov. Phys. Dokl. 6, 773–775.', 'Bruus, H. (2012). Acoustofluidics 7: The acoustic radiation force on small particles. Lab Chip 12, 1014–1021.', 'Settnes, M. & Bruus, H. (2012). Forces acting on a small particle in an acoustical field in a viscous fluid. Phys. Rev. E 85, 016327.', 'Brandt, E. H. (2001). Suspended by sound. Nature 413, 474–475.', 'Kinsler, L. E., Frey, A. R., Coppens, A. B. & Sanders, J. V. (2000). Fundamentals of Acoustics, 4th ed., Wiley.'],
  inputs: [
    inp('p_a', 'Acoustic pressure amplitude', 'Pa', 2000, { min: 1, max: 2e4, aliases: ['pressure amplitude', 'sound pressure', 'acoustic pressure', 'pa'] }),
    inp('f_a', 'Frequency', 'kHz', 40, { min: 1, max: 5000, aliases: ['frequency', 'khz', 'ultrasonic frequency'] }),
    inp('rho_0', 'Density of the medium', 'kg/m^3', 1.2, { min: 0.3, max: 1100, kind: 'environment', env: 'air_density', aliases: ['air density', 'medium density', 'fluid density'] }),
    inp('c_s', 'Speed of sound in the medium', 'm/s', 343, { min: 200, max: 1600, kind: 'fluid', aliases: ['speed of sound', 'sound speed'] }),
    inp('A_t', 'Target area for the plane-wave case', 'cm^2', 10, { min: 0.01, max: 1e4, kind: 'geometry', aliases: ['target area', 'area', 'absorber area'] }),
    inp('d_p', 'Sphere diameter', 'mm', 1, { min: 0.01, max: 20, kind: 'geometry', aliases: ['sphere diameter', 'particle diameter', 'bead', 'droplet', 'diameter'] }),
    inp('rho_p', 'Sphere density', 'kg/m^3', 30, { min: 1, max: 20000, kind: 'fluid', aliases: ['particle density', 'sphere density', 'bead density'], src: 'Expanded polystyrene bead' }),
    inp('c_p', 'Speed of sound in the sphere', 'm/s', 900, { min: 50, max: 7000, kind: 'fluid', aliases: ['particle sound speed'] }),
    inp('nu', 'Kinematic viscosity of the medium', 'm^2/s', 1.5e-5, { min: 1e-7, max: 1e-3, kind: 'fluid', aliases: ['viscosity', 'kinematic viscosity'] }),
    inp('ka_lim', 'Largest k·a trusted for the small-sphere formula', '1', 0.5, { min: 0.1, max: 1.5, kind: 'numerical' }),
  ],
  assumptions: [
    asm('absorber', 'The plane-wave target absorbs the wave completely.', { why: 'Radiation-force balance with an absorbing target', alt: 'The target reflects the wave completely at normal incidence: the pressure doubles.' }),
    asm('small_sphere', 'The sphere is much smaller than the wavelength (k·a ≪ 1), so the point-particle Gor\'kov force applies.', { why: 'Standard regime of the theory', alt: 'The force density is averaged over the sphere volume, which reduces the force and makes it vanish near a diameter of 0.7 wavelengths. This is an approximation, not exact scattering theory.' }),
    asm('inviscid', 'The viscous boundary layer around the sphere is thin compared with its radius.', { why: 'Millimetre beads in air at ultrasonic frequency', alt: 'The dipole coefficient is corrected for the viscous boundary layer (Settnes & Bruus 2012).' }),
    asm('rigid', 'The sphere is incompressible compared with the medium (monopole coefficient f₁ = 1).', { why: 'Solids and liquids in a gas', alt: 'The finite compressibility of the sphere enters through f₁ = 1 − ρ₀c₀²/(ρ_p c_p²).' }),
  ],
  symbols: { k_w: ['Wavenumber', '1/m'], E_t: ['Energy density of the travelling wave', 'J/m^3'], p_rad: ['Radiation pressure', 'Pa'], F_t: ['Radiation force on the target', 'N'], E_ac: ['Energy density of the standing wave', 'J/m^3'], f_1: ['Monopole (compressibility) coefficient', '1'], f_2: ['Dipole (density) coefficient', '1'], delta_v: ['Viscous boundary-layer thickness', 'm'], C_v: ['Viscous correction to the dipole coefficient', '1'], Phi_c: ['Acoustic contrast factor', '1'], F_max: ['Peak radiation force on the sphere', 'N'], W_p: ['Net weight of the sphere', 'N'], M_lev: ['Levitation margin', '1'], U_g: ['Gor\'kov potential', 'J'], z: ['Position along the standing wave, from a pressure antinode', 'm'] },
  equations: a => [
    eq('k', 'Wavenumber', 'k_w', '2*pi*f_a/c_s', { kind: 'definition' }),
    eq('et', 'Energy density of a travelling plane wave', 'E_t', 'p_a^2/(2*rho_0*c_s^2)', { kind: 'derived', origin: 'Time-averaged kinetic plus potential acoustic energy' }),
    a.absorber ? eq('prad', 'Radiation pressure on an absorber', 'p_rad', 'E_t', { kind: 'law', origin: 'Momentum flux of the wave fully absorbed', needs: ['absorber'] }) : eq('prad', 'Radiation pressure on a reflector', 'p_rad', '2*E_t', { kind: 'law', origin: 'Momentum flux reversed on reflection' }),
    eq('ft', 'Force on the target', 'F_t', 'p_rad*A_t', { kind: 'definition' }),
    eq('eac', 'Energy density of the standing wave', 'E_ac', 'p_a^2/(4*rho_0*c_s^2)', { kind: 'derived' }),
    a.rigid ? eq('f1', 'Monopole coefficient', 'f_1', '1', { kind: 'closure', needs: ['rigid'] }) : eq('f1', 'Monopole coefficient', 'f_1', '1 - rho_0*c_s^2/(rho_p*c_p^2)', { kind: 'derived', origin: 'Compressibility contrast' }),
    ...(a.inviscid
      ? [eq('f2', 'Dipole coefficient', 'f_2', '2*(rho_p - rho_0)/(2*rho_p + rho_0)', { kind: 'derived', origin: 'Density contrast in an ideal fluid', needs: ['inviscid'] })]
      : [eq('dv', 'Viscous boundary-layer thickness', 'delta_v', 'sqrt(nu/(pi*f_a))', { kind: 'derived', origin: 'Stokes layer of an oscillating flow' }), eq('f2', 'Dipole coefficient with viscous correction', 'f_2', '2*(rho_p - rho_0)/(2*rho_p + rho_0)*C_v', { kind: 'derived', origin: 'Settnes & Bruus (2012); C_v is the real part of a complex function of δ_v/a and the density ratio' })]),
    eq('phi', 'Acoustic contrast factor', 'Phi_c', 'f_1/3 + f_2/2', { kind: 'definition' }),
    eq('gor', 'Gor\'kov potential', 'U_g', 'pi*d_p^3/6*E_ac*(f_1*cos(k_w*z)^2 - 3/2*f_2*sin(k_w*z)^2)', { kind: 'law', origin: 'Gor\'kov (1962)' }),
    a.small_sphere
      ? eq('fmax', 'Peak force on the sphere', 'F_max', 'pi*d_p^3/2*k_w*E_ac*Phi_c', { kind: 'derived', origin: 'Negative gradient of the Gor\'kov potential', needs: ['small_sphere'] })
      : eq('fmax', 'Peak force with finite-size averaging', 'F_max', 'pi*d_p^3/2*k_w*E_ac*Phi_c*3*(sin(k_w*d_p) - k_w*d_p*cos(k_w*d_p))/(k_w*d_p)^3', { kind: 'closure', origin: 'Force density averaged over the sphere volume' }),
    eq('wp', 'Net weight of the sphere', 'W_p', 'pi*d_p^3/6*(rho_p - rho_0)*g', { kind: 'law', origin: 'Weight less buoyancy' }),
    eq('mlev', 'Levitation margin', 'M_lev', 'F_max/W_p', { kind: 'definition' }),
  ],
  derivation: () => [
    { text: 'A plane wave of pressure amplitude p has particle-velocity amplitude p/(ρc). Its time-averaged energy density is the sum of equal kinetic and potential parts.', tex: 'E = \\frac{p_a^2}{2\\rho_0 c^2},\\qquad I = E\\,c' },
    { text: 'The wave carries momentum flux E per unit area. Absorbing it exerts pressure E; reversing it exerts 2E.', tex: 'p_{rad} = E\\ \\text{(absorber)},\\qquad p_{rad} = 2E\\ \\text{(reflector)}' },
    { text: 'For a sphere of radius a ≪ λ, scattering theory gives a force that is the negative gradient of a potential built from the mean-square pressure and velocity of the incident field.', tex: 'U = \\frac{4\\pi a^3}{3}\\left[f_1\\frac{\\langle p^2\\rangle}{2\\rho_0c^2} - \\frac{3}{4}f_2\\,\\rho_0\\langle v^2\\rangle\\right]' },
    { text: 'The coefficients measure the contrast in compressibility and density between sphere and medium.', tex: 'f_1 = 1-\\frac{\\rho_0c^2}{\\rho_pc_p^2},\\qquad f_2 = \\frac{2(\\rho_p-\\rho_0)}{2\\rho_p+\\rho_0}' },
    { text: 'In a standing wave p = p_a cos kz cos ωt the force is sinusoidal with half the acoustic wavelength, directed toward the pressure nodes when the contrast factor is positive.', tex: 'F_z = 4\\pi a^3 k\\,E_{ac}\\,\\Phi\\,\\sin 2kz,\\qquad \\Phi = \\frac{f_1}{3}+\\frac{f_2}{2},\\quad E_{ac}=\\frac{p_a^2}{4\\rho_0c^2}' },
    { text: 'Levitation requires the peak force to exceed the net weight. The radius cancels, leaving a threshold on the pressure amplitude.', tex: '3k\\,E_{ac}\\,\\Phi \\ge (\\rho_p-\\rho_0)\\,g' },
  ],
  solve(v, a) {
    const c = arfCore(v, a), R = v.d_p / 2, k = c.k, warnings = [];
    const prad = (a.absorber ? 1 : 2) * c.Et, Ft = prad * v.A_t, va = v.p_a / (v.rho_0 * v.c_s);
    const Phi = c.Phi(v.rho_p, R), F0 = c.Fmax(v.rho_p, R), W = c.Wt(v.rho_p, R), aF = Math.abs(F0), aW = Math.abs(W);
    const margin = aF / Math.max(aW, 1e-300), lev = margin >= 1, ka = k * R;
    const drho = Math.abs(v.rho_p - v.rho_0), sz = c.size(R);
    const pMin = Math.sqrt(4 * c.kap * drho * g0 / (3 * k * Math.max(Math.abs(Phi * sz), 1e-300)));
    let rhoMax = v.rho_p; for (let i = 0; i < 12; i++) rhoMax = v.rho_0 + 3 * k * c.Eac * Math.abs(c.Phi(rhoMax, R) * sz) / g0;
    const ratio = r => 3 * k * c.Eac * Math.abs(c.Phi(v.rho_p, r)) * c.size(r) / Math.max(drho * g0, 1e-300) - 1;
    const Rcap = 4.4934 / (2 * k);
    const dMax = a.small_sphere ? (lev ? 2 * v.ka_lim / k : 0) : (ratio(Rcap * 1e-4) > 0 ? 2 * rootOr(ratio, Rcap * 1e-4, Rcap, Rcap) : 0);
    const zOff = lev ? Math.asin(Math.min(1, aW / aF)) / (2 * k) : 0;
    const mp = 4 / 3 * Math.PI * R ** 3 * v.rho_p, kTrap = lev ? 2 * k * aF * Math.sqrt(Math.max(0, 1 - (aW / aF) ** 2)) : 0;
    if (ka > v.ka_lim && a.small_sphere) warnings.push('k·a exceeds the stated limit of the small-sphere formula; the force is over-estimated. Switch off the small-sphere assumption for a finite-size estimate.');
    if (va / v.c_s > 0.1) warnings.push('The acoustic Mach number exceeds 0.1: the wave steepens and second-order theory is unreliable.');
    if (a.inviscid && c.dl > 0.2 * R) warnings.push('The viscous boundary layer is not thin compared with the sphere; switch off the inviscid assumption.');
    if (Phi < 0) warnings.push('The contrast factor is negative: the sphere is drawn to pressure antinodes rather than nodes.');
    const zs = N.linspace(0, c.lam / 2, 401), Fz = zs.map(z => F0 * Math.sin(2 * k * z));
    const U = z => 4 / 3 * Math.PI * R ** 3 * c.Eac * sz * (c.f1(v.rho_p) * Math.cos(k * z) ** 2 - 1.5 * c.f2(v.rho_p, R) * Math.sin(k * z) ** 2);
    let gRes = 0; const h = zs[1] - zs[0];
    for (let i = 1; i < 400; i++) gRes = Math.max(gRes, Math.abs(-(U(zs[i] + h) - U(zs[i] - h)) / (2 * h) - Fz[i]));
    const rhos = N.logspace(Math.max(v.rho_0 * 1.5, 2), 2e4, 60);
    const ds = N.linspace(c.lam * 0.01, c.lam * 0.7, 80);
    const fin = arfCore(v, { ...a, small_sphere: false }), pt = arfCore(v, { ...a, small_sphere: true });
    return {
      scalars: [
        scalar('lambda', 'Wavelength', c.lam, 'm', { show: 'mm' }), scalar('k_w', 'Wavenumber', k, '1/m'),
        scalar('SPL', 'Sound pressure level (re 20 µPa)', dB(v.p_a / Math.SQRT2 / 20e-6), 'dB'),
        scalar('v_a', 'Particle-velocity amplitude', va, 'm/s'), scalar('Ma_a', 'Acoustic Mach number', va / v.c_s, '1'),
        scalar('I_ac', 'Intensity of the travelling wave', c.Et * v.c_s, 'W/m^2'), scalar('E_t', 'Energy density of the travelling wave', c.Et, 'J/m^3'),
        scalar('p_rad', `Radiation pressure on ${a.absorber ? 'an absorber' : 'a reflector'}`, prad, 'Pa'), scalar('F_t', 'Radiation force on the target', Ft, 'N', { show: 'mN' }),
        scalar('ka', 'Size parameter k·a', ka, '1'), scalar('delta_v', 'Viscous boundary-layer thickness', c.dl, 'm', { show: 'um' }),
        scalar('f_1', 'Monopole coefficient', c.f1(v.rho_p), '1'), scalar('f_2', 'Dipole coefficient', c.f2(v.rho_p, R), '1'), scalar('Phi_c', 'Acoustic contrast factor', Phi, '1'),
        scalar('F_max', 'Peak radiation force on the sphere', aF, 'N', { show: 'uN' }), scalar('W_p', 'Net weight of the sphere', aW, 'N', { show: 'uN' }),
        scalar('M_lev', 'Levitation margin (force / weight)', margin, '1', { text: `${lab(margin)} — ${lev ? 'the sphere can be levitated' : 'the field is too weak to levitate the sphere'}` }),
        scalar('p_min', 'Pressure amplitude needed to levitate', pMin, 'Pa'),
        scalar('rho_max', 'Largest density that can be levitated', rhoMax, 'kg/m^3'),
        scalar('d_max', 'Largest levitated diameter', dMax, 'm', { show: 'mm', note: a.small_sphere ? 'Set by the validity limit of the small-sphere formula' : 'Root of force = weight with finite-size averaging' }),
        scalar('z_off', 'Sag of the equilibrium below the pressure node', zOff, 'm', { show: 'um' }),
        scalar('f_trap', 'Oscillation frequency of the trapped sphere', Math.sqrt(kTrap / mp) / TAU, 'Hz'),
      ],
      series: [
        line('force-z', 'Radiation force along the standing wave', 'Distance from pressure antinode', 'mm', zs.map(q => q * 1e3), [{ label: 'Radiation force', data: Fz.map(q => q * 1e6) }, { label: 'Net weight', data: zs.map(() => aW * 1e6), dash: true }], 'Force', 'µN', { note: 'The pressure node lies at a quarter wavelength' }),
        line('threshold', 'Levitation threshold against sphere density', 'Sphere density', 'kg/m³', rhos, [{ label: 'Pressure amplitude needed', data: rhos.map(r => Math.sqrt(4 * c.kap * Math.abs(r - v.rho_0) * g0 / (3 * k * Math.max(Math.abs(c.Phi(r, R) * sz), 1e-300)))) }, { label: 'Applied amplitude', data: rhos.map(() => v.p_a), dash: true }], 'Pressure amplitude', 'Pa', { logx: true, logy: true }),
        line('force-size', 'Peak force and weight against diameter', 'Diameter / wavelength', '–', ds.map(q => q / c.lam), [{ label: 'Small-sphere force', data: ds.map(q => Math.abs(pt.Fmax(v.rho_p, q / 2)) * 1e6) }, { label: 'Finite-size averaged force', data: ds.map(q => Math.abs(fin.Fmax(v.rho_p, q / 2)) * 1e6), dash: true }, { label: 'Net weight', data: ds.map(q => Math.abs(c.Wt(v.rho_p, q / 2)) * 1e6) }], 'Force', 'µN'),
      ],
      checks: [
        check('Force equals the negative gradient of the Gor\'kov potential', gRes / Math.max(aF, 1e-300), 1e-3, 'Central difference of the potential against the closed-form force'),
        check('Force averages to zero over a period (conservative field)', N.trapz(zs, Fz) / Math.max(aF * c.lam / 2, 1e-300), 1e-9, 'Integral of the force over half an acoustic wavelength'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const c = arfCore(v, { ...a, inviscid: true, rigid: true, small_sphere: true }), R = v.d_p / 2, out = [];
    out.push(bench('Rigid, dense sphere: contrast factor', c.Phi(1e12 * v.rho_0, R), 5 / 6, 'King (1934): Φ = 5/6', 1e-9));
    out.push(bench('King force amplitude for a rigid dense sphere', c.Fmax(1e12 * v.rho_0, R), 5 * Math.PI / 6 * R ** 3 * c.k * v.p_a ** 2 / c.kap, 'F = (5π/6) k a³ p²/(ρc²)', 1e-9));
    out.push(bench('Radiation pressure equals intensity over sound speed', c.Et, (v.p_a ** 2 / (2 * v.rho_0 * v.c_s)) / v.c_s, 'p_rad = I/c for an absorber', 1e-12));
    const cv = arfCore({ ...v, nu: 1e-12 }, { ...a, inviscid: false });
    out.push(bench('Viscous dipole coefficient in the thin-layer limit', cv.f2(v.rho_p, R), c.f2(v.rho_p, R), 'Settnes & Bruus (2012) reduces to the ideal-fluid value', 1e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const ys = [70, 150, 230];
    return svg(`
      ${S.rect(240, 24, 160, 22, 'd-body')} ${S.text(320, 18, 'transducer')}
      ${S.rect(240, 300, 160, 14, 'd-body')} ${S.text(320, 334, 'reflector')}
      ${S.path(`M320 46 ${N.linspace(46, 300, 60).map(y => `L${320 + 46 * Math.cos((y - 46) / 254 * 3 * Math.PI)} ${y}`).join(' ')}`, 'd-line')}
      ${S.path(`M320 46 ${N.linspace(46, 300, 60).map(y => `L${320 - 46 * Math.cos((y - 46) / 254 * 3 * Math.PI)} ${y}`).join(' ')}`, 'd-dim')}
      ${ys.map(y => S.line(250, y + 18.5, 390, y + 18.5, 'd-dim')).join('')}
      ${S.circle(320, 173, 9, 'd-hazard')} ${S.arrow(320, 184, 320, 214)} ${S.text(332, 210, 'weight', 'd-text d-small', 'start')}
      ${S.arrow(320, 162, 320, 136, 'd-arrow d-heat')} ${S.text(332, 142, 'radiation force', 'd-text d-small', 'start')}
      ${S.text(232, 92, 'pressure node', 'd-text d-small', 'end')}
      ${S.text(520, 150, `${lab(v.f_a / 1e3, 'kHz')}, λ = ${lab(v.c_s / v.f_a * 1e3, 'mm')}`, 'd-text d-small')}
      ${S.text(520, 172, `p = ${lab(v.p_a, 'Pa')}`, 'd-text d-small')} ${S.text(520, 194, `sphere ⌀${lab(v.d_p * 1e3, 'mm')}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the radiation force of an ultrasonic beam on an absorbing and a reflecting target, and the pressure amplitude at which beads of known density are just levitated in a standing wave.',
    apparatus: ['Langevin transducer with horn (20–40 kHz) or a phased array', 'Flat or concave reflector on a micrometer stage set to an integer number of half-wavelengths', 'Absorbing target (open-cell foam wedge) and rigid reflecting target on a balance pan', 'Beads of several densities and diameters'],
    instruments: [{ name: 'Calibrated measurement microphone or optical (laser Doppler / schlieren) pressure measurement', measures: 'Pressure amplitude at the antinode', range: 'to 170 dB', resolution: '±0.5 dB' }, { name: 'Microbalance', measures: 'Radiation force on the target', range: '0–100 mN', resolution: '±1 µN' }, { name: 'Camera with macro lens', measures: 'Bead position relative to the node', range: '—', resolution: '±10 µm' }, { name: 'Thermometer and barometer', measures: 'Air density and sound speed', range: 'ambient', resolution: '±0.2 K' }],
    procedure: ['Tune the reflector distance for maximum standing-wave ratio.', 'Place the target on the balance in a travelling-wave arrangement (absorbing termination) and record force against drive level for both targets.', 'Insert a bead at a node and reduce the drive until it falls; record the pressure amplitude at release.', 'Repeat for each bead density and diameter; record the sag below the node at several drive levels.'],
    controls: ['Balance reading with the beam blocked, to remove thermal and streaming drift', 'Different bead diameters of the same material: the release threshold should not change while k·a is small'],
    signatures: ['Force on the reflector twice that on the absorber', 'Force proportional to the square of the pressure amplitude', 'Release threshold proportional to the square root of density contrast and independent of diameter for small beads', 'Trapping positions spaced by half a wavelength'],
    safety: ['High-intensity airborne ultrasound: hearing protection and enclosure; observe occupational exposure guidance', 'Transducer horn surfaces become hot and carry high voltage', 'Do not place fingers in the beam at high drive'],
  },
  falsify: ['A radiation force on a reflector that is not twice that on an absorber at the same incident intensity.', 'A force that scales other than as the square of the pressure amplitude at small amplitude.', 'A levitation threshold that depends on bead diameter while k·a is well below one and the viscous layer is thin.', 'Stable trapping of dense rigid beads at pressure antinodes.'],
  alternatives: [{ name: 'Acoustic streaming', text: 'A distinct mechanism: attenuation of the wave in the bulk (Eckart) or at boundaries (Rayleigh, Schlichting) drives a steady flow that exerts Stokes drag on the particle. It dominates for very small particles and must not be confused with the radiation force.' }, { name: 'Exact scattering theory', text: 'For spheres comparable with the wavelength the full partial-wave series (King; Hasegawa) is required; the force oscillates with k·a and can change sign.' }, { name: 'Near-field and single-beam levitation', text: 'Squeeze-film levitation close to a vibrating surface, and holographic acoustic traps, rest on the same second-order physics but different field geometries.' }],
  hazards: [{ hazard: 'Hearing damage and sub-harmonic noise', cause: 'High-level ultrasound and audible sub-harmonics', mitigation: 'Enclosure, absorbers, hearing protection' }, { hazard: 'Burns', cause: 'Hot transducer horn; absorption in targets', mitigation: 'Duty-cycle limits and guarding' }, { hazard: 'Electric shock', cause: 'Piezo drive voltage', mitigation: 'Insulated, earthed housing' }],
  standards: ['IEC 61161 (ultrasonics — power measurement — radiation force balances and performance requirements)', 'IEC 61672-1 (sound level meters)', 'IEC 61010-1 (safety requirements for electrical equipment for measurement, control and laboratory use)'],
  limits: 'Second-order (weakly nonlinear) acoustics; plane travelling or one-dimensional standing wave; isolated sphere away from walls. The Gor\'kov force requires k·a ≪ 1; the finite-size option is an approximation only. Acoustic streaming, thermal effects, droplet deformation and particle–particle forces are not included.',
  numerics: { method: 'Closed-form expressions; complex arithmetic for the viscous correction; bracketed root finding for the largest diameter; fixed-point iteration for the largest density' },
  optimise: { objective: 'M_lev', sense: 'max', vars: ['f_a'], note: 'Force per unit volume grows with frequency, but the usable sphere size shrinks with the wavelength.' },
  inverse: { series: 'force-z', fit: ['p_a'] },
  extensions: ['Partial-wave series for spheres of arbitrary size', 'Streaming drag and the critical particle size', 'Transverse trapping in a focused beam', 'Droplet flattening and break-up limit'],
};

// ------------------------------------------------------------------ vibrating string
function stringCore(v, a) {
  const L = v.L, T = v.T_s, mu = v.mu_l, Aw = Math.PI * v.d_w ** 2 / 4, Ia = Math.PI * v.d_w ** 4 / 64, xp = v.x_p * L, wh = 0.03 * L;
  const u0 = x => (a.plucked ? v.a_p * (x < xp ? x / xp : (L - x) / (L - xp)) : 0);
  const w0 = x => (a.plucked ? 0 : v.v_h * Math.exp(-(((x - xp) / wh) ** 2)));
  const xq = N.linspace(0, L, 801);
  const E0 = a.plucked ? T * v.a_p ** 2 / 2 * (1 / xp + 1 / (L - xp)) : 0.5 * mu * N.trapz(xq, xq.map(x => w0(x) ** 2));
  const Te = a.small_amp ? T : T + v.E_y * Aw * E0 / (2 * T * L);
  const c = Math.sqrt(Te / mu), f1 = c / (2 * L), B = a.flexible ? 0 : Math.PI ** 2 * v.E_y * Ia / (Te * L * L), gam = a.undamped ? 0 : v.gamma_d;
  const fn = (n, b = B) => n * f1 * Math.sqrt(1 + b * n * n);
  const nm = 60, An = [], Vn = [];
  for (let n = 1; n <= nm; n++) {
    An.push(a.plucked ? 2 * v.a_p * L * L / (n * n * Math.PI ** 2 * xp * (L - xp)) * Math.sin(n * Math.PI * xp / L) : 0);
    Vn.push(a.plucked ? 0 : 2 / L * N.trapz(xq, xq.map(x => w0(x) * Math.sin(n * Math.PI * x / L))));
  }
  /** Modal amplitude of mode n (1-based) at time t. */
  const qn = (n, t, b = B) => {
    const w = TAU * fn(n, b), A = An[n - 1], Vv = Vn[n - 1] + gam * A / 2, d2 = w * w - gam * gam / 4, e = Math.exp(-gam * t / 2);
    if (d2 > 0) { const wd = Math.sqrt(d2); return e * (A * Math.cos(wd * t) + Vv / wd * Math.sin(wd * t)); }
    const s = Math.sqrt(-d2); return s * t < 1e-9 ? e * (A + Vv * t) : e * (A * Math.cosh(s * t) + Vv / s * Math.sinh(s * t));
  };
  const modal = (x, t, b = B) => { let s = 0; for (let n = 1; n <= nm; n++) s += qn(n, t, b) * Math.sin(n * Math.PI * x / L); return s; };
  return { L, T, mu, Aw, Ia, xp, u0, w0, E0, Te, c, f1, B, gam, fn, nm, An, Vn, qn, modal };
}

const vibratingString = {
  id: 'vibrating-string-wave',
  title: 'Waves on a plucked or struck string',
  module: [1, 2], klass: 'I', domains: ['waves', 'classical'],
  keywords: ['vibrating string', 'plucked string', 'string', 'guitar string', 'piano string', 'wave equation', 'standing wave', 'harmonics', 'overtones', 'fundamental frequency', 'tension', 'linear density', 'normal modes', 'inharmonicity', 'wave speed'],
  summary: 'Transverse waves on a stretched string with fixed ends, from a plucked shape or a hammer blow: wave speed, fundamental and overtones, standing-wave motion, harmonic content and the effect of damping, stiffness and large amplitude.',
  background: [
    'A flexible string under tension T with mass per unit length μ obeys the one-dimensional wave equation; disturbances travel at c = √(T/μ) without change of shape. With both ends fixed, only waves that fit a whole number of half-wavelengths persist, giving the harmonic series f_n = n c/(2L). Any initial shape is a superposition of these standing waves.',
    'A string plucked at a fraction p of its length has harmonic amplitudes proportional to sin(nπp)/n², so harmonics with a node at the plucking point are absent. Real strings depart from the ideal in three ways treated here: losses make each mode decay, bending stiffness raises the overtones progressively (inharmonicity, important in pianos), and at large amplitude the stretching of the string raises the tension and hence the pitch.',
  ],
  phenomena: ['Travelling and standing transverse waves', 'Reflection with inversion at fixed ends', 'Harmonic series', 'Modal damping', 'Stiffness inharmonicity', 'Amplitude-dependent tension'],
  laws: ['newton2', 'momentum', 'energy', 'hooke'],
  refs: ['Fletcher, N. H. & Rossing, T. D. (1998). The Physics of Musical Instruments, 2nd ed., Springer.', 'Morse, P. M. & Ingard, K. U. (1968). Theoretical Acoustics, McGraw-Hill.', 'French, A. P. (1971). Vibrations and Waves, W. W. Norton.', 'Fletcher, H. (1964). Normal vibration frequencies of a stiff piano string. J. Acoust. Soc. Am. 36, 203–209.'],
  inputs: [
    inp('L', 'String length', 'm', 0.65, { min: 0.1, max: 5, kind: 'geometry', aliases: ['length', 'string length', 'scale length', 'long'] }),
    inp('T_s', 'Tension', 'N', 70, { min: 1, max: 2000, aliases: ['tension', 'newton', 'newtons'] }),
    inp('mu_l', 'Mass per unit length', 'g/m', 0.385, { min: 0.05, max: 50, kind: 'fluid', aliases: ['linear density', 'mass per length', 'mass per unit length'], src: 'Plain steel wire of 0.25 mm diameter' }),
    inp('x_p', 'Pluck or strike position as a fraction of the length', '1', 0.2, { min: 0.02, max: 0.98, kind: 'geometry', aliases: ['pluck position', 'plucked at', 'strike position'] }),
    inp('a_p', 'Pluck amplitude', 'mm', 3, { min: 0.01, max: 50, aliases: ['amplitude', 'pluck amplitude', 'displacement'] }),
    inp('x_o', 'Pickup position as a fraction of the length', '1', 0.3, { min: 0.02, max: 0.98, kind: 'geometry', aliases: ['pickup position', 'observation point'] }),
    inp('gamma_d', 'Damping rate', '1/s', 3, { min: 0, max: 200, aliases: ['damping', 'decay rate'] }),
    inp('E_y', 'Young\'s modulus of the string', 'GPa', 200, { min: 1, max: 450, kind: 'fluid', aliases: ['young modulus', 'modulus', 'stiffness'], src: 'Steel' }),
    inp('d_w', 'String diameter', 'mm', 0.25, { min: 0.05, max: 3, kind: 'geometry', aliases: ['string diameter', 'wire diameter', 'gauge'] }),
    inp('v_h', 'Peak hammer velocity imparted to the string', 'm/s', 2, { min: 0.01, max: 20, aliases: ['hammer velocity', 'strike velocity'] }),
    inp('n_x', 'Grid points along the string', '1', 201, { min: 51, max: 801, kind: 'numerical' }),
  ],
  assumptions: [
    asm('undamped', 'The string loses no energy.', { why: 'Isolates the wave motion', alt: 'A viscous damping term γ ∂u/∂t makes every mode decay as exp(−γt/2).' }),
    asm('flexible', 'The string is perfectly flexible: bending stiffness is negligible.', { why: 'Thin strings at low mode numbers', alt: 'Bending stiffness EI adds a fourth-derivative term and raises the overtones: f_n = n f₁ √(1 + B n²).' }),
    asm('small_amp', 'Displacements are small, so the tension stays constant.', { why: 'Linear wave equation', alt: 'The mean stretch of the string raises the tension (Kirchhoff–Carrier correction), sharpening the pitch.' }),
    asm('plucked', 'The string is released from rest from a triangular plucked shape.', { why: 'Guitar or harp excitation', alt: 'The string is struck: it starts undisplaced with a localised velocity pulse (piano hammer).' }),
  ],
  symbols: { u: ['Transverse displacement', 'm'], x: ['Position along the string', 'm'], t: ['Time', 's'], c_w: ['Wave speed', 'm/s'], f_1: ['Fundamental frequency', 'Hz'], f_n: ['Frequency of mode n', 'Hz'], n: ['Mode number', '1'], B_s: ['Inharmonicity coefficient', '1'], I_a: ['Second moment of area', 'm^4'], A_w: ['Cross-sectional area', 'm^2'], T_e: ['Effective tension', 'N'], E_0: ['Initial energy', 'J'], u_0: ['Initial displacement', 'm'], w_0: ['Initial transverse velocity', 'm/s'], Z_w: ['Wave impedance', 'kg/s'], A_n: ['Amplitude of mode n', 'm'] },
  equations: a => [
    eq('wave', 'Equation of motion', `pd2(u,t)${a.undamped ? '' : ' + gamma_d*pd(u,t)'}`, `c_w^2*pd2(u,x)${a.flexible ? '' : ' - E_y*I_a/mu_l*pd2(pd2(u,x),x)'}`, { kind: 'law', origin: 'Newton\'s second law for an element of string' }),
    ...(a.small_amp
      ? [eq('c', 'Wave speed', 'c_w', 'sqrt(T_s/mu_l)', { kind: 'derived', needs: ['small_amp'] })]
      : [eq('te', 'Effective tension', 'T_e', 'T_s + E_y*A_w*E_0/(2*T_s*L)', { kind: 'closure', origin: 'Hooke\'s law applied to the time-averaged stretch (Kirchhoff–Carrier)' }), eq('aw', 'Cross-sectional area', 'A_w', 'pi*d_w^2/4', { kind: 'definition' }), eq('c', 'Wave speed', 'c_w', 'sqrt(T_e/mu_l)', { kind: 'derived' })]),
    eq('f1', 'Fundamental frequency', 'f_1', 'c_w/(2*L)', { kind: 'derived', origin: 'Half a wavelength fits the string' }),
    ...(a.flexible
      ? [eq('fn', 'Mode frequencies', 'f_n', 'n*f_1', { kind: 'derived', needs: ['flexible'] })]
      : [eq('ia', 'Second moment of area', 'I_a', 'pi*d_w^4/64', { kind: 'definition' }), eq('bs', 'Inharmonicity coefficient', 'B_s', 'pi^2*E_y*I_a/(T_s*L^2)', { kind: 'derived' }), eq('fn', 'Mode frequencies of a stiff string', 'f_n', 'n*f_1*sqrt(1 + B_s*n^2)', { kind: 'derived', origin: 'Dispersion relation of a tensioned beam with pinned ends' })]),
    a.plucked
      ? eq('ic', 'Initial shape, left of the pluck point', 'u_0', 'a_p*x/(x_p*L)', { kind: 'initial' })
      : eq('ic', 'Initial velocity from the hammer', 'w_0', 'v_h*exp(-((x - x_p*L)/(0.03*L))^2)', { kind: 'initial' }),
    ...(a.plucked ? [eq('an', 'Harmonic amplitudes of a plucked string', 'A_n', '2*a_p/(n^2*pi^2*x_p*(1 - x_p))*sin(n*pi*x_p)', { kind: 'derived', origin: 'Fourier sine series of the triangular shape', needs: ['plucked'] })] : []),
    eq('z', 'Wave impedance', 'Z_w', 'sqrt(T_s*mu_l)', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'An element of string of length dx and mass μ dx is accelerated by the difference in the transverse components of tension at its ends. For small slopes this difference is T ∂²u/∂x² dx.', tex: '\\mu\\,\\frac{\\partial^2 u}{\\partial t^2} = T\\,\\frac{\\partial^2 u}{\\partial x^2}\\ \\Rightarrow\\ c = \\sqrt{T/\\mu}' },
    { text: 'The general solution is a pair of waves travelling in opposite directions (d\'Alembert).', tex: 'u(x,t) = F(x-ct) + G(x+ct)' },
    { text: 'Fixed ends require u = 0 at x = 0 and x = L. Standing waves that satisfy this have a whole number of half-wavelengths on the string.', tex: 'u_n = \\sin\\frac{n\\pi x}{L}\\cos 2\\pi f_n t,\\qquad f_n = \\frac{n}{2L}\\sqrt{\\frac{T}{\\mu}}' },
    { text: a.plucked ? 'Expanding the triangular plucked shape in these modes gives amplitudes that fall as 1/n² and vanish for modes with a node at the plucking point.' : 'A velocity pulse excites each mode in proportion to the overlap of the pulse with the mode shape; a narrow pulse excites many overtones.', tex: a.plucked ? 'A_n = \\frac{2a}{n^2\\pi^2\\,p\\,(1-p)}\\sin(n\\pi p)' : '\\dot q_n(0) = \\frac{2}{L}\\int_0^L w_0(x)\\sin\\frac{n\\pi x}{L}\\,\\mathrm{d}x' },
    ...(a.flexible ? [] : [{ text: 'Bending stiffness adds a restoring moment. For pinned ends the mode shapes are unchanged but the frequencies are stretched.', tex: 'f_n = n f_1\\sqrt{1+Bn^2},\\qquad B = \\frac{\\pi^2 E I}{T L^2}' }]),
    ...(a.undamped ? [] : [{ text: 'With viscous damping each mode decays exponentially and its frequency is lowered slightly.', tex: 'q_n(t) \\propto e^{-\\gamma t/2}\\cos\\!\\left(t\\sqrt{\\omega_n^2-\\gamma^2/4}\\right)' }]),
  ],
  solve(v, a) {
    const s = stringCore(v, a), L = s.L, T1 = 1 / s.f1, tEnd = 3 * T1, warnings = [];
    const nx = Math.round(v.n_x), xs = N.linspace(0, L, nx), io = N.clamp(Math.round(v.x_o * (nx - 1)), 1, nx - 2), xo = xs[io];
    let times, frames, pick, ref, fNum = NaN, rms = 0, method;
    if (a.flexible) {
      const r = N.wave1D({ c: s.c, L, nx, tEnd, cfl: 1, u0: s.u0, v0: s.w0, ends: 'fixed', frames: 360, damping: s.gam });
      times = r.times; frames = r.snaps; pick = frames.map(f => f[io]); method = 'grid';
      // period from zero crossings of the projection on the first mode
      const sn = xs.map(x => Math.sin(Math.PI * x / L)), q1 = frames.map(f => { let q = 0; for (let i = 0; i < nx; i++) q += f[i] * sn[i]; return q; });
      const zc = []; for (let k = 1; k < q1.length; k++) if (q1[k - 1] * q1[k] < 0) zc.push(times[k - 1] + (times[k] - times[k - 1]) * q1[k - 1] / (q1[k - 1] - q1[k]));
      if (zc.length >= 2) fNum = (zc.length - 1) / (2 * (zc[zc.length - 1] - zc[0]));
      ref = times.map(t => s.modal(xo, t)); const amp = Math.max(N.maxOf(ref.map(Math.abs)), 1e-300);
      rms = Math.sqrt(N.mean(pick.map((p, k) => (p - ref[k]) ** 2))) / amp;
    } else {
      times = N.linspace(0, tEnd, 361); const xm = N.linspace(0, L, 121);
      frames = times.filter((_, k) => k % 4 === 0).map(t => xm.map(x => s.modal(x, t)));
      pick = times.map(t => s.modal(xo, t)); ref = times.map(t => s.modal(xo, t, 0)); method = 'modal';
    }
    const af = a.flexible ? frames.filter((_, k) => k % 4 === 0) : frames, at = times.filter((_, k) => k % 4 === 0);
    const ax = a.flexible ? xs : N.linspace(0, L, 121);
    const ns = Array.from({ length: 12 }, (_, i) => i + 1);
    const amp = ns.map(n => (a.plucked ? Math.abs(s.An[n - 1]) : Math.abs(s.Vn[n - 1]) / (TAU * s.fn(n))));
    const eModal = N.sum(ns.concat(Array.from({ length: s.nm - 12 }, (_, i) => i + 13)).map(n => 0.25 * s.mu * L * ((TAU * s.fn(n, 0)) ** 2 * s.An[n - 1] ** 2 + s.Vn[n - 1] ** 2)));
    let slope = 0; af.forEach(f => { slope = Math.max(slope, Math.abs(f[1] - f[0]) / (ax[1] - ax[0])); });
    const stress = s.Te / s.Aw, pk = 1.1e3 * Math.max(...af.map(f => N.maxOf(Array.from(f, Math.abs)))) || 1;
    if (stress > 2.5e9) warnings.push('The tensile stress exceeds about 2.5 GPa, beyond the strength of music wire.');
    if (v.a_p / L > 0.02 && a.small_amp && a.plucked) warnings.push('The pluck amplitude exceeds 2 % of the length; the constant-tension assumption is marginal.');
    if (!a.flexible) warnings.push('With bending stiffness the response is computed by modal superposition (pinned-end mode shapes), not on the finite-difference grid.');
    if (s.gam / 2 > TAU * s.f1) warnings.push('The damping is so heavy that the fundamental no longer oscillates.');
    return {
      scalars: [
        scalar('c_w', 'Wave speed', s.c, 'm/s'), scalar('f_1', 'Fundamental frequency', s.f1 * Math.sqrt(1 + s.B), 'Hz'), scalar('T_1', 'Fundamental period', T1, 's', { show: 'ms' }),
        scalar('f_2', 'Second partial', s.fn(2), 'Hz'), scalar('f_3', 'Third partial', s.fn(3), 'Hz'),
        scalar('lambda_1', 'Wavelength of the fundamental on the string', 2 * L, 'm'),
        scalar('Z_w', 'Wave impedance √(Tμ)', Math.sqrt(s.Te * s.mu), 'kg/s'),
        scalar('E_0', 'Energy given to the string', s.E0, 'J', { show: 'mJ' }),
        scalar('T_e', 'Effective tension', s.Te, 'N'), scalar('sigma_w', 'Tensile stress', stress, 'Pa', { show: 'MPa' }),
        scalar('B_s', 'Inharmonicity coefficient', s.B, '1'),
        scalar('cents_2', 'Sharpness of the second partial relative to 2f₁', 1200 * Math.log2(s.fn(2) / (2 * s.fn(1))), '1', { note: 'cents' }),
        scalar('tau_d', 'Amplitude decay time', s.gam > 0 ? 2 / s.gam : 0, 's', s.gam > 0 ? {} : { text: 'No decay (undamped)' }),
        scalar('F_br', 'Peak transverse force on the end support', s.Te * slope, 'N'),
        scalar('f_num', 'Fundamental measured from the simulation', a.flexible && Number.isFinite(fNum) ? fNum : s.fn(1), 'Hz', { note: a.flexible ? 'Zero crossings of the first-mode projection' : 'Modal solution' }),
      ],
      series: [
        line('pickup', 'Displacement at the pickup position', 'Time', 'ms', times.map(t => t * 1e3), [{ label: a.flexible ? 'Finite-difference solution' : 'Stiff string (modal)', data: pick.map(q => q * 1e3) }, { label: a.flexible ? 'Modal series (60 modes)' : 'Flexible string (modal)', data: ref.map(q => q * 1e3), dash: true }], 'Displacement', 'mm'),
        line('harmonics', 'Initial amplitude of each partial', 'Frequency', 'Hz', ns.map(n => s.fn(n)), [{ label: 'Modal amplitude', data: amp.map(q => q * 1e3) }], 'Amplitude', 'mm', { kind: 'bar' }),
      ],
      anims: [anim('string', 'Shape of the string', 'Position', 'm', ax, af.map(f => Array.from(f, q => q * 1e3)), at, 'Displacement', 'mm', { yRange: [-pk, pk] })],
      checks: [
        check('Grid solution against the modal series at the pickup', rms, 0.02, method === 'grid' ? 'Root-mean-square difference relative to the peak displacement' : 'Not evaluated: modal solution used'),
        check('Modal energy sum against the energy supplied', (eModal - s.E0) / s.E0, 0.03, 'Parseval\'s relation with 60 modes'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], b = { ...a, flexible: true }, r = this.solve(v, b), s = stringCore(v, b);
    const fd = s.gam / 2 < TAU * s.f1 ? Math.sqrt((TAU * s.f1) ** 2 - s.gam ** 2 / 4) / TAU : NaN;
    if (Number.isFinite(fd)) out.push(bench('Fundamental frequency from the simulation', val(r, 'f_num'), fd, s.gam > 0 ? 'f₁ = (1/2L)√(T/μ), lowered by damping' : 'f₁ = (1/2L)√(T/μ)', 1e-3));
    out.push(bench('Wave speed', s.c, Math.sqrt(s.Te / v.mu_l), 'c = √(T/μ)', 1e-12));
    if (a.plucked) out.push(bench('Plucked-string series reproduces the pluck amplitude', s.modal(s.xp, 0), v.a_p, 'Fourier sine series of a triangle, 60 modes', 0.02));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const xp = 80 + 480 * v.x_p, xo = 80 + 480 * v.x_o;
    return svg(`
      ${S.rect(60, 150, 20, 60, 'd-body')} ${S.rect(560, 150, 20, 60, 'd-body')}
      ${S.line(80, 180, 560, 180, 'd-dim')}
      ${a.plucked ? S.poly([[80, 180], [xp, 110], [560, 180]], 'd-pipe') + S.arrow(xp, 96, xp, 60) + S.text(xp, 50, `pluck ${lab(v.a_p * 1e3, 'mm')}`) : S.line(80, 180, 560, 180, 'd-pipe') + S.arrow(xp, 120, xp, 172, 'd-arrow d-heat') + S.text(xp, 110, `hammer ${lab(v.v_h, 'm/s')}`)}
      ${S.circle(xo, 196, 5, 'd-hazard')} ${S.text(xo, 222, 'pickup', 'd-text d-small')}
      ${S.arrow(470, 150, 540, 150)} ${S.arrow(170, 150, 100, 150)} ${S.text(320, 146, `tension ${lab(v.T_s, 'N')}`)}
      ${S.dim(80, 270, 560, 270, `L = ${lab(v.L, 'm')}`)}
      ${S.text(320, 320, `μ = ${lab(v.mu_l * 1e3, 'g/m')}   c = ${lab(Math.sqrt(v.T_s / v.mu_l), 'm/s')}   f₁ = ${lab(Math.sqrt(v.T_s / v.mu_l) / (2 * v.L), 'Hz')}`)}
    `);
  },
  experiment: {
    objective: 'Measure the fundamental frequency and overtone spectrum of a stretched wire as functions of tension, length and plucking position.',
    apparatus: ['Sonometer: steel wire over two knife-edge bridges on a rigid bench', 'Tension from a hanging mass over a pulley, or a load cell with a tuning machine', 'Plectrum on a release jig to give a repeatable pluck at a set position and amplitude'],
    instruments: [{ name: 'Load cell or calibrated masses', measures: 'Tension', range: '0–200 N', resolution: '±0.1 N' }, { name: 'Magnetic pickup or laser displacement sensor with data acquisition', measures: 'String displacement or velocity', range: '±5 mm, 20 kHz', resolution: '16 bit' }, { name: 'Balance and micrometer', measures: 'Mass per unit length and diameter of the wire', range: '—', resolution: '±1 mg, ±2 µm' }, { name: 'Steel rule', measures: 'Speaking length', range: '0–1 m', resolution: '±0.5 mm' }],
    procedure: ['Weigh a measured length of wire to obtain μ.', 'Set a tension, pluck near the middle and record at least 2 s of signal; take the spectrum and read the partial frequencies.', 'Repeat at six tensions and four lengths.', 'At one setting pluck at 1/2, 1/3, 1/5 and 1/8 of the length and compare the harmonic amplitudes.', 'Fit the partial frequencies to n f₁√(1 + Bn²) to obtain the inharmonicity coefficient.'],
    controls: ['Vary the pluck amplitude to confirm that the frequency does not change at small amplitude', 'Check that the bridges do not move by repeating with added bench mass'],
    signatures: ['f₁ proportional to √T at fixed length and to 1/L at fixed tension', 'Missing harmonics at multiples of 1/p', 'Partials progressively sharp of the harmonic series by an amount growing as n²'],
    safety: ['A wire breaking under tension whips: wear eye protection and shield the wire', 'Secure hanging masses against falling'],
  },
  falsify: ['A fundamental frequency that is not proportional to √(T/μ)/L within the measurement uncertainty.', 'Harmonics present with a node at the plucking point for an ideal narrow pluck.', 'Overtones flat, rather than sharp, of the harmonic series for a stiff string with rigidly pinned ends.'],
  alternatives: [{ name: 'Travelling-wave (d\'Alembert) description', text: 'Equivalent to the modal picture: the plucked shape splits into two half-amplitude copies that reflect with inversion at the ends.' }, { name: 'Compliant end supports', text: 'A bridge that moves couples the string to the instrument body, shifting mode frequencies and adding radiation damping.' }, { name: 'Frequency-dependent damping', text: 'Air damping, internal friction and bridge losses each scale differently with frequency; a single rate is a simplification.' }],
  hazards: [{ hazard: 'Wire whip', cause: 'Tensile failure of the string', mitigation: 'Stay below about 70 % of the breaking stress; eye protection; shield' }],
  standards: ['ISO 16:1975 (acoustics — standard tuning frequency)', 'ASTM A228/A228M (steel wire, music spring quality)'],
  limits: 'Transverse motion in one plane, uniform string, rigid end supports, slopes small compared with one. The large-amplitude correction is a time-averaged first-order estimate. Longitudinal and torsional waves, and coupling to the instrument body, are not included.',
  numerics: { method: 'Explicit leapfrog finite differences at unit Courant number, where the scheme reproduces d\'Alembert\'s solution on the grid; modal superposition with 60 modes for the stiff string and for cross-checking', order: 2, stability: 'Stable for Courant number up to one', resolution: 'n_x' },
  optimise: { objective: 'f_1', sense: 'max', vars: ['T_s'], note: 'Pitch rises as the square root of tension until the breaking stress is reached.' },
  inverse: { series: 'pickup', fit: ['T_s'] },
  extensions: ['Compliant bridge and body coupling', 'Hammer–string contact dynamics', 'Two transverse polarisations and whirling at large amplitude', 'Frequency-dependent loss model'],
};

// ------------------------------------------------------------------ coupled oscillators
function coCore(v, a) {
  const m = v.m, k1 = v.k, k2 = a.identical ? v.k : v.k * (1 + v.delta_k), kc = v.k_c, cd = a.undamped ? 0 : v.c_d, k3 = a.linear ? 0 : v.k_3;
  const s = (k1 + k2 + 2 * kc) / (2 * m), dd = Math.hypot((k1 - k2) / (2 * m), kc / m), w1 = Math.sqrt(Math.max(s - dd, 0)), w2 = Math.sqrt(s + dd);
  const trans = (kc / m) ** 2 / (dd * dd);
  const energy = (x1, v1, x2, v2) => 0.5 * m * (v1 * v1 + v2 * v2) + 0.5 * k1 * x1 * x1 + 0.5 * k2 * x2 * x2 + 0.5 * kc * (x1 - x2) ** 2 + 0.25 * k3 * (x1 ** 4 + x2 ** 4);
  const dw = Math.max(w2 - w1, 1e-12 * w2), tFast = TAU / w2;
  const tEnd = Math.min(Math.max(2 * TAU / dw, 6 * TAU / Math.max(w1, 1e-9)), 60 * tFast);
  const run = (n = 900) => N.rk45((t, y) => [y[1], (-k1 * y[0] - kc * (y[0] - y[2]) - cd * y[1] - k3 * y[0] ** 3) / m, y[3], (-k2 * y[2] - kc * (y[2] - y[0]) - cd * y[3] - k3 * y[2] ** 3) / m, cd * (y[1] * y[1] + y[3] * y[3])], [v.x_0, 0, 0, 0, 0], 0, tEnd, n, { rtol: 1e-8, atol: 1e-12 * v.x_0, maxSteps: 120000 });
  /** Steady-state complex amplitudes under a force F0 cos(wt) on mass 1. */
  const resp = w => { const D1 = [k1 + kc - m * w * w, w * cd], D2 = [k2 + kc - m * w * w, w * cd], det = csub(cmul(D1, D2), [kc * kc, 0]), dn = cabs(det) > 0 ? det : [1e-300, 0]; return [cdiv(cmul([v.F_0, 0], D2), dn), cdiv([v.F_0 * kc, 0], dn)]; };
  return { m, k1, k2, kc, cd, k3, w1, w2, dw, trans, energy, tEnd, run, resp };
}

const coupledOsc = {
  id: 'coupled-oscillators-resonance',
  title: 'Two coupled oscillators: normal modes, beating and synchronisation',
  module: [1, 2], klass: 'I', domains: ['waves', 'classical'],
  keywords: ['coupled oscillators', 'coupled oscillator', 'coupled pendulums', 'normal modes', 'beating', 'beats', 'energy exchange', 'mode splitting', 'avoided crossing', 'resonance', 'synchronisation', 'synchronization', 'phase locking', 'phase-locking', 'kuramoto', 'entrainment', 'sympathetic resonance'],
  summary: 'Two mass–spring oscillators joined by a coupling spring: normal-mode frequencies, beating and periodic energy exchange, driven frequency response, and — as an alternative — phase locking of two self-sustained oscillators with Kuramoto-type coupling.',
  background: [
    'Two identical oscillators joined by a weak spring have two normal modes: an in-phase mode at the uncoupled frequency, in which the coupling spring is not stretched, and an anti-phase mode at a higher frequency. Starting one oscillator alone excites both modes equally; their slow relative drift in phase appears as beating, with the energy passing completely to the second oscillator and back in a time π/(ω_b − ω_a). If the oscillators are detuned the transfer is incomplete.',
    'These oscillators are passive: energy is conserved or lost, and the two mode frequencies never merge. Synchronisation is a different phenomenon. It occurs between self-sustained oscillators — each with its own energy source and amplitude-limiting nonlinearity — whose phases are free. Weak coupling then pulls the phases together, and the pair locks to a common frequency when the coupling exceeds half the detuning (Adler 1946; Kuramoto 1984).',
  ],
  phenomena: ['Normal modes and mode splitting', 'Beating', 'Resonant energy exchange', 'Anti-resonance (dynamic absorption)', 'Phase locking of self-sustained oscillators'],
  laws: ['newton2', 'newton3', 'hooke', 'energy'],
  refs: ['French, A. P. (1971). Vibrations and Waves, W. W. Norton.', 'Feynman, R. P., Leighton, R. B. & Sands, M. (1963). The Feynman Lectures on Physics, Vol. I, ch. 49, Addison-Wesley.', 'Adler, R. (1946). A study of locking phenomena in oscillators. Proc. IRE 34, 351–357.', 'Kuramoto, Y. (1984). Chemical Oscillations, Waves, and Turbulence, Springer.', 'Pikovsky, A., Rosenblum, M. & Kurths, J. (2001). Synchronization: A Universal Concept in Nonlinear Sciences, Cambridge University Press.'],
  inputs: [
    inp('m', 'Mass of each oscillator', 'kg', 0.5, { min: 0.01, max: 100, aliases: ['mass', 'kg'] }),
    inp('k', 'Spring stiffness of each oscillator', 'N/m', 50, { min: 0.1, max: 1e5, aliases: ['stiffness', 'spring constant', 'spring'] }),
    inp('k_c', 'Coupling spring stiffness', 'N/m', 5, { min: 0.001, max: 1e4, aliases: ['coupling', 'coupling spring', 'coupling stiffness'] }),
    inp('x_0', 'Initial displacement of the first mass', 'cm', 2, { min: 0.01, max: 50, aliases: ['initial displacement', 'amplitude'] }),
    inp('c_d', 'Viscous damping coefficient of each oscillator', 'N s/m', 0.05, { min: 0, max: 10, aliases: ['damping', 'damping coefficient'] }),
    inp('delta_k', 'Fractional stiffness excess of the second oscillator', '%', 5, { min: -50, max: 100, aliases: ['detuning', 'mistuning'] }),
    inp('k_3', 'Cubic (Duffing) stiffness', 'N/m^3', 2e4, { min: 0, max: 1e7, aliases: ['cubic stiffness', 'duffing', 'nonlinear stiffness'] }),
    inp('F_0', 'Drive force amplitude on the first mass', 'N', 0.1, { min: 0.001, max: 100, aliases: ['force', 'drive force', 'forcing'] }),
    inp('df', 'Natural-frequency detuning of the self-sustained pair', 'Hz', 0.05, { min: 0, max: 5, aliases: ['frequency difference', 'frequency detuning'] }),
    inp('K_s', 'Phase-coupling strength', '1/s', 0.2, { min: 0.001, max: 50, aliases: ['coupling strength', 'kuramoto coupling', 'phase coupling'] }),
  ],
  assumptions: [
    asm('identical', 'The two oscillators are identical.', { why: 'Gives complete energy exchange', alt: 'The second spring is stiffer by a set fraction; the modes localise and energy transfer is incomplete.' }),
    asm('undamped', 'There is no damping.', { why: 'Isolates the mode structure', alt: 'Each mass has a viscous damper; the beats decay and resonances have finite height.' }),
    asm('linear', 'The springs are linear.', { why: 'Small displacements', alt: 'Each grounded spring has an added cubic (Duffing) term; frequencies depend on amplitude and exchange can be suppressed.' }),
    asm('passive', 'The oscillators are passive: no energy source, so the phases are fixed by the modes and no locking occurs.', { why: 'Mass–spring system', alt: 'The oscillators are self-sustained (limit cycles) with weak coupling; their phase difference obeys the Adler/Kuramoto equation and can lock.' }),
  ],
  symbols: { x_1: ['Displacement of mass 1', 'm'], x_2: ['Displacement of mass 2', 'm'], t: ['Time', 's'], k_2: ['Stiffness of the second oscillator', 'N/m'], omega_a: ['Lower normal-mode angular frequency', '1/s'], omega_b: ['Upper normal-mode angular frequency', '1/s'], f_beat: ['Beat frequency', 'Hz'], T_ex: ['Energy-exchange time', 's'], eta_tr: ['Largest fraction of energy transferred', '1'], psi: ['Phase difference of the self-sustained pair', '1'], K_c: ['Critical coupling for locking', '1/s'] },
  equations: a => [
    eq('eom1', 'Equation of motion, mass 1', 'm*d2(x_1,t)', `-k*x_1 - k_c*(x_1 - x_2)${a.undamped ? '' : ' - c_d*d(x_1,t)'}${a.linear ? '' : ' - k_3*x_1^3'}`, { kind: 'law', origin: 'Newton\'s second law with Hooke\'s law' }),
    eq('eom2', 'Equation of motion, mass 2', 'm*d2(x_2,t)', `-k_2*x_2 - k_c*(x_2 - x_1)${a.undamped ? '' : ' - c_d*d(x_2,t)'}${a.linear ? '' : ' - k_3*x_2^3'}`, { kind: 'law', origin: 'Newton\'s second and third laws' }),
    a.identical ? eq('k2', 'Second spring', 'k_2', 'k', { kind: 'closure', needs: ['identical'] }) : eq('k2', 'Second spring, detuned', 'k_2', 'k*(1 + delta_k)', { kind: 'definition' }),
    ...(a.identical
      ? [eq('wa', 'In-phase mode', 'omega_a', 'sqrt(k/m)', { kind: 'derived', needs: ['identical', 'linear'] }), eq('wb', 'Anti-phase mode', 'omega_b', 'sqrt((k + 2*k_c)/m)', { kind: 'derived', needs: ['identical', 'linear'] })]
      : [eq('wa', 'Lower mode', 'omega_a^2', '(k + k_2 + 2*k_c)/(2*m) - sqrt(((k - k_2)/(2*m))^2 + (k_c/m)^2)', { kind: 'derived', origin: 'Eigenvalues of the stiffness matrix' }), eq('wb', 'Upper mode', 'omega_b^2', '(k + k_2 + 2*k_c)/(2*m) + sqrt(((k - k_2)/(2*m))^2 + (k_c/m)^2)', { kind: 'derived', origin: 'Eigenvalues of the stiffness matrix' })]),
    eq('fb', 'Beat frequency', 'f_beat', '(omega_b - omega_a)/(2*pi)', { kind: 'derived' }),
    eq('tex', 'Energy-exchange time', 'T_ex', 'pi/(omega_b - omega_a)', { kind: 'derived' }),
    a.identical ? eq('tr', 'Largest energy transfer', 'eta_tr', '1', { kind: 'derived', needs: ['identical'] }) : eq('tr', 'Largest energy transfer', 'eta_tr', '(k_c/m)^2/(((k - k_2)/(2*m))^2 + (k_c/m)^2)', { kind: 'derived', origin: 'Projection of the initial state on the two modes' }),
    ...(a.passive ? [] : [eq('adler', 'Phase-difference dynamics', 'd(psi,t)', '2*pi*df - 2*K_s*sin(psi)', { kind: 'closure', origin: 'Phase reduction of weakly coupled limit-cycle oscillators (Adler 1946; Kuramoto 1984)' }), eq('kc', 'Critical coupling for locking', 'K_c', 'pi*df', { kind: 'derived' })]),
  ],
  derivation: a => [
    { text: 'Each mass is acted on by its own spring and by the coupling spring, which is stretched by the difference of the displacements.', tex: 'm\\ddot x_1 = -kx_1 - k_c(x_1-x_2),\\qquad m\\ddot x_2 = -k_2x_2 - k_c(x_2-x_1)' },
    { text: 'Seeking solutions in which both masses oscillate at one frequency gives a 2×2 eigenvalue problem. For identical oscillators the sum and difference coordinates decouple.', tex: '\\omega_a = \\sqrt{k/m},\\qquad \\omega_b = \\sqrt{(k+2k_c)/m}' },
    { text: 'Releasing mass 1 from rest excites both modes equally. The motion of each mass is a fast oscillation inside a slow envelope.', tex: 'x_{1,2} = \\frac{x_0}{2}\\left(\\cos\\omega_a t \\pm \\cos\\omega_b t\\right) = x_0\\,{\\cos\\atop\\sin}\\!\\left(\\tfrac{\\omega_b-\\omega_a}{2}t\\right){\\cos\\atop\\sin}\\!\\left(\\tfrac{\\omega_b+\\omega_a}{2}t\\right)' },
    { text: 'The envelope of mass 1 first vanishes, with all the energy in mass 2, after the exchange time. For weak coupling the splitting is ω₀k_c/k.', tex: 'T_{ex} = \\frac{\\pi}{\\omega_b-\\omega_a} \\approx \\frac{\\pi k}{\\omega_0 k_c}' },
    ...(a.passive ? [] : [{ text: 'For two self-sustained oscillators with natural frequencies ω₁, ω₂ and weak coupling K, only the phases matter. Subtracting the two phase equations gives a single equation for the phase difference, which has a fixed point — locking — when the detuning is less than twice the coupling.', tex: '\\dot\\psi = \\Delta\\omega - 2K\\sin\\psi,\\qquad |\\Delta\\omega| \\le 2K \\Rightarrow \\psi^* = \\arcsin\\frac{\\Delta\\omega}{2K}' }]),
  ],
  solve(v, a) {
    const c = coCore(v, a), r = c.run(), t = r.t, n = t.length, x1 = r.y[0], x2 = r.y[2], warnings = [];
    const E0 = c.energy(v.x_0, 0, 0, 0), e1 = t.map((_, i) => 0.5 * c.m * r.y[1][i] ** 2 + 0.5 * c.k1 * x1[i] ** 2 + 0.25 * c.k3 * x1[i] ** 4), e2 = t.map((_, i) => 0.5 * c.m * r.y[3][i] ** 2 + 0.5 * c.k2 * x2[i] ** 2 + 0.25 * c.k3 * x2[i] ** 4);
    const eEnd = c.energy(x1[n - 1], r.y[1][n - 1], x2[n - 1], r.y[3][n - 1]), eRes = (eEnd + r.y[4][n - 1] - E0) / E0;
    const w0 = Math.sqrt(c.k1 / c.m), trNum = N.maxOf(e2) / E0;
    if (n < 900) warnings.push('The integration stopped early at its step limit; the time series is truncated.');
    if (c.kc / c.k1 > 0.5) warnings.push('The coupling is strong: the motion is no longer a slow beat on a fast carrier, and the weak-coupling estimates do not apply.');
    if (!a.linear && c.k3 * v.x_0 ** 2 > 0.3 * c.k1) warnings.push('The cubic term is comparable with the linear stiffness at this amplitude; the linear mode frequencies are only indicative.');
    if (!a.passive && !a.undamped) warnings.push('The phase-locking analysis treats ideal self-sustained oscillators; it is independent of the damped mass–spring simulation shown alongside.');
    const ws = N.linspace(0.3 * c.w1, 1.6 * c.w2, 500), rs = ws.map(c.resp);
    const scalars = [
      scalar('f_0', 'Uncoupled natural frequency', w0 / TAU, 'Hz'), scalar('f_a', 'Lower normal-mode frequency', c.w1 / TAU, 'Hz'), scalar('f_b', 'Upper normal-mode frequency', c.w2 / TAU, 'Hz'),
      scalar('kappa', 'Coupling ratio k_c/k', c.kc / c.k1, '1'),
      scalar('f_beat', 'Beat frequency', c.dw / TAU, 'Hz'), scalar('T_ex', 'Energy-exchange time', Math.PI / c.dw, 's'),
      scalar('eta_tr', 'Largest fraction of energy transferred (linear theory)', c.trans, '1', { show: '%' }),
      scalar('eta_num', 'Largest fraction of energy seen in oscillator 2 (simulation)', trNum, '1', { show: '%' }),
      scalar('E_0', 'Initial energy', E0, 'J', { show: 'mJ' }),
      scalar('f_anti', 'Anti-resonance frequency of the driven mass', Math.sqrt((c.k2 + c.kc) / c.m) / TAU, 'Hz'),
      scalar('Q', 'Quality factor of each oscillator', c.cd > 0 ? c.m * w0 / c.cd : 0, '1', c.cd > 0 ? {} : { text: 'Unbounded (undamped)' }),
      scalar('X_st', 'Static deflection under the drive force', v.F_0 * (c.k2 + c.kc) / ((c.k1 + c.kc) * (c.k2 + c.kc) - c.kc ** 2), 'm', { show: 'mm' }),
    ];
    const series = [
      line('motion', 'Displacements after releasing mass 1', 'Time', 's', t, [{ label: 'Mass 1', data: x1.map(q => q * 100) }, { label: 'Mass 2', data: x2.map(q => q * 100) }], 'Displacement', 'cm'),
      line('energy', 'Energy held by each oscillator', 'Time', 's', t, [{ label: 'Oscillator 1', data: e1.map(q => q / E0) }, { label: 'Oscillator 2', data: e2.map(q => q / E0) }], 'Energy / initial energy', '–'),
      line('response', 'Steady-state amplitude under a sinusoidal force on mass 1', 'Drive frequency', 'Hz', ws.map(q => q / TAU), [{ label: 'Mass 1', data: rs.map(q => Math.min(cabs(q[0]), 1e6) * 1e3) }, { label: 'Mass 2', data: rs.map(q => Math.min(cabs(q[1]), 1e6) * 1e3) }], 'Amplitude', 'mm', { logy: true }),
    ];
    if (!a.passive) {
      const dW = TAU * v.df, K = v.K_s, locked = Math.abs(dW) <= 2 * K, slip = Math.sqrt(Math.max(dW * dW - 4 * K * K, 0));
      const tK = 6 * TAU / Math.max(Math.sqrt(Math.abs(dW * dW - 4 * K * K)), 0.3 * (Math.abs(dW) + 2 * K)), p = N.rk45((tt, y) => [dW - 2 * K * Math.sin(y[0])], [0], 0, tK, 400, { rtol: 1e-9 });
      const Ks = N.linspace(0, Math.max(1.5 * Math.abs(dW), 2 * K), 80);
      scalars.push(
        scalar('lock', 'Phase locking of the self-sustained pair', locked ? 1 : 0, '1', { text: locked ? 'Locked — the pair runs at a common frequency' : 'Not locked — the phase difference slips' }),
        scalar('K_c', 'Critical coupling for locking', Math.abs(dW) / 2, '1/s'),
        scalar('psi_lock', 'Locked phase difference', locked ? Math.asin(dW / (2 * K)) : 0, 'rad', locked ? { show: 'deg' } : { text: 'None — not locked' }),
        scalar('f_slip', 'Residual beat (phase-slip) frequency', slip / TAU, 'Hz'),
        scalar('psi_end', 'Phase difference at the end of the run', p.y[0][p.y[0].length - 1], 'rad'));
      series.push(
        line('phase', 'Phase difference of the self-sustained pair', 'Time', 's', p.t, [{ label: 'Phase difference', data: p.y[0] }], 'Phase difference', 'rad'),
        line('locking', 'Observed frequency difference against coupling', 'Coupling strength', '1/s', Ks, [{ label: 'Frequency difference', data: Ks.map(q => Math.sqrt(Math.max(dW * dW - 4 * q * q, 0)) / TAU) }, { label: 'Uncoupled detuning', data: Ks.map(() => Math.abs(v.df)), dash: true }], 'Frequency difference', 'Hz'));
    }
    return { scalars, series, checks: [check('Energy balance', eRes, 1e-5, a.undamped ? 'Total mechanical energy conserved' : 'Mechanical energy plus dissipated work equals the initial energy')], warnings };
  },
  benchmarks(v, a) {
    const out = [], id = { ...a, identical: true }, w = coCore({ ...v, k_c: 1e-4 * v.k }, id), w0 = Math.sqrt(v.k / v.m);
    out.push(bench('Weak-coupling mode splitting', (w.w2 - w.w1) / w0, 1e-4, 'ω_b − ω_a → ω₀ k_c/k', 1e-3));
    if (a.identical && a.undamped && a.linear) {
      const c = coCore(v, a), r = c.run(), n = r.t.length - 1, te = r.t[n];
      out.push(bench('Displacement of mass 1 against the two-mode solution', r.y[0][n] + v.x_0, v.x_0 / 2 * (Math.cos(c.w1 * te) + Math.cos(c.w2 * te)) + v.x_0, 'x₁ = (x₀/2)(cos ω_a t + cos ω_b t), offset by x₀', 1e-6));
      const e2 = r.t.map((_, i) => 0.5 * c.m * r.y[3][i] ** 2 + 0.5 * c.k2 * r.y[2][i] ** 2);
      if (c.tEnd >= TAU / c.dw && c.kc / c.k1 < 0.3) out.push(bench('Complete energy transfer between identical oscillators', N.maxOf(e2) / c.energy(v.x_0, 0, 0, 0), 1, 'All the energy passes to oscillator 2', 0.02));
    }
    if (!a.passive && TAU * v.df < 2 * v.K_s) { const r = this.solve(v, a); out.push(bench('Locked phase difference', val(r, 'psi_end') + 1, Math.asin(TAU * v.df / (2 * v.K_s)) + 1, 'ψ* = arcsin(Δω/2K), offset by 1', 1e-3)); }
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(40, 110, 16, 120, 'd-ground', 0)} ${S.rect(584, 110, 16, 120, 'd-ground', 0)}
      ${S.path('M56 170 l14 0 l8 -16 l16 32 l16 -32 l16 32 l16 -32 l8 16 l14 0', 'd-line')} ${S.text(118, 140, `k = ${lab(v.k, 'N/m')}`, 'd-text d-small')}
      ${S.rect(164, 140, 80, 60, 'd-body')} ${S.text(204, 175, `m`)}
      ${S.path('M244 170 l24 0 l8 -12 l16 24 l16 -24 l16 24 l16 -24 l16 24 l8 -12 l32 0', 'd-heat')} ${S.text(320, 140, `k_c = ${lab(v.k_c, 'N/m')}`, 'd-text d-small')}
      ${S.rect(396, 140, 80, 60, 'd-body')} ${S.text(436, 175, 'm')}
      ${S.path('M476 170 l14 0 l8 -16 l16 32 l16 -32 l16 32 l16 -32 l8 16 l14 0', 'd-line')} ${S.text(530, 140, a.identical ? 'k' : `k(1+${lab(v.delta_k * 100, '%')})`, 'd-text d-small')}
      ${S.arrow(204, 122, 250, 122)} ${S.text(226, 112, 'x₁')} ${S.arrow(436, 122, 482, 122)} ${S.text(458, 112, 'x₂')}
      ${S.path('M56 230 L584 230', 'd-ground')}
      ${S.text(320, 290, `released with x₁ = ${lab(v.x_0 * 100, 'cm')}, x₂ = 0`)}
      ${S.text(320, 320, a.passive ? 'passive oscillators: beating, no locking' : 'plus phase-locking analysis of a self-sustained pair', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the two normal-mode frequencies, the beat period and the completeness of energy exchange for two coupled oscillators as the coupling and detuning are varied.',
    apparatus: ['Two air-track gliders with identical springs to fixed ends and a light coupling spring; or two pendulums joined by a soft spring', 'Set of coupling springs of different stiffness', 'Small added masses for detuning'],
    instruments: [{ name: 'Ultrasonic or optical position sensors on each mass', measures: 'Displacement against time', range: '±0.2 m', resolution: '±0.5 mm at 100 Hz' }, { name: 'Force sensor and rule', measures: 'Spring constants from static extension', range: '0–10 N', resolution: '±0.01 N' }, { name: 'Balance', measures: 'Masses', range: '0–1 kg', resolution: '±0.1 g' }],
    procedure: ['Measure each spring constant and mass.', 'Excite the in-phase mode (equal displacements) and the anti-phase mode (opposite displacements) in turn and time 20 cycles of each.', 'Hold mass 2 at rest, displace mass 1 and release; record both positions over several beats.', 'Repeat with three coupling springs, then with mass added to one glider.'],
    controls: ['Each oscillator alone with the other clamped, to obtain the uncoupled frequency and damping', 'Swap the gliders to confirm symmetry'],
    signatures: ['In-phase frequency independent of the coupling spring', 'Beat frequency equal to the difference of the two mode frequencies', 'Complete exchange only when the oscillators are tuned alike', 'A quarter-period lag of the driven oscillator behind the driver during transfer'],
    safety: ['Secure the air track; keep fingers clear of springs under tension'],
  },
  falsify: ['A beat frequency that differs from f_b − f_a measured separately.', 'Complete energy transfer between measurably detuned oscillators, or incomplete transfer between tuned, undamped ones.', 'Frequency locking of two passive linear oscillators (their mode frequencies must stay distinct).'],
  alternatives: [{ name: 'Kuramoto phase model', text: 'For self-sustained oscillators the amplitudes are slaved to limit cycles and only phases evolve; coupling through the sine of the phase difference produces locking above a critical strength. Huygens\' clocks and injection-locked electronic oscillators are examples.' }, { name: 'Inertial or dissipative coupling', text: 'Coupling through a shared mass or a damper, rather than a spring, changes which mode is shifted and can make one mode decay faster.' }, { name: 'Quantum two-level analogue', text: 'The same mathematics describes Rabi oscillation and avoided level crossings.' }],
  hazards: [{ hazard: 'Resonant build-up', cause: 'Driving near a mode frequency with little damping', mitigation: 'Limit drive amplitude; add damping; avoid dwelling on resonance' }],
  standards: ['ISO 2041 (mechanical vibration, shock and condition monitoring — vocabulary)', 'ISO 7626 series (experimental determination of mechanical mobility)'],
  limits: 'Two lumped masses moving in one dimension with spring coupling. The mode formulae are linear; the Duffing option is integrated numerically but the reported mode frequencies remain the small-amplitude values. The phase-locking analysis assumes weak coupling of limit-cycle oscillators and says nothing about passive ones.',
  numerics: { method: 'Adaptive Dormand–Prince Runge–Kutta with the dissipated energy carried as an extra state; complex 2×2 solve for the frequency response', order: 5, stability: 'Step-size controlled to a relative tolerance of 10⁻⁸' },
  optimise: { objective: 'T_ex', sense: 'min', vars: ['k_c'], note: 'Stiffer coupling exchanges energy faster.' },
  inverse: { series: 'motion', fit: ['k_c', 'k'] },
  extensions: ['Chains of N oscillators and the continuum limit', 'Parametric coupling and mode conversion', 'Populations of phase oscillators with distributed frequencies (Kuramoto transition)', 'Amplitude death and oscillation quenching'],
};

// ------------------------------------------------------------------ time-reversal focusing
function trSim(v, a) {
  let nx = Math.max(101, Math.round(v.n_x)); if (nx % 2 === 0) nx++;
  const L = v.L, c = v.c_w, dx = L / (nx - 1), dt = dx / c, cr = a.homogeneous ? 1 : v.c_ratio;
  const i1 = Math.round(0.62 * (nx - 1)), i2 = Math.round(0.74 * (nx - 1));
  const C2 = new Float64Array(nx).fill(1); if (cr < 1) for (let i = i1; i <= i2; i++) C2[i] = cr * cr;
  const gam = a.lossless ? 0 : v.zeta_L * c / L, gd = gam * dt / 2;
  const is = Math.round(v.x_s * (nx - 1)), sig = v.w_p * L, xs = N.linspace(0, L, nx);
  const g = xs.map(x => Math.exp(-((x - xs[is]) ** 2) / (2 * sig * sig)));
  const Nf = Math.ceil((1.35 + (cr < 1 ? 0.12 * (1 / cr - 1) + 0.96 / cr : 0)) * (nx - 1));
  const step = (u, up, un) => { for (let i = 1; i < nx - 1; i++) un[i] = (2 * u[i] - (1 - gd) * up[i] + C2[i] * (u[i + 1] - 2 * u[i] + u[i - 1])) / (1 + gd); };
  // forward: emit and record at both ends (open boundaries)
  let up = Float64Array.from(g), u = new Float64Array(nx), un = new Float64Array(nx);
  for (let i = 1; i < nx - 1; i++) u[i] = up[i] + 0.5 * C2[i] * (up[i + 1] - 2 * up[i] + up[i - 1]);
  u[0] = up[1]; u[nx - 1] = up[nx - 2];
  const recL = new Float64Array(Nf + 1), recR = new Float64Array(Nf + 1), every = Math.max(1, Math.floor(Nf / 36)), frames = [Array.from(up)], times = [0];
  recL[0] = up[0]; recR[0] = up[nx - 1]; recL[1] = u[0]; recR[1] = u[nx - 1];
  for (let n = 1; n < Nf; n++) {
    step(u, up, un); un[0] = u[1]; un[nx - 1] = u[nx - 2];
    [up, u, un] = [u, un, up]; recL[n + 1] = u[0]; recR[n + 1] = u[nx - 1];
    if ((n + 1) % every === 0) { frames.push(Array.from(u)); times.push((n + 1) * dt); }
  }
  let resid = 0; for (let i = 0; i < nx; i++) resid = Math.max(resid, Math.abs(u[i]));
  // energy leaving through the ends, in units of the wave impedance times c
  let eOut = 0; for (let n = 1; n <= Nf; n++) eOut += ((recL[n] - recL[n - 1]) ** 2 + (recR[n] - recR[n - 1]) ** 2) / dt;
  let e0 = 0; for (let i = 1; i < nx; i++) e0 += 0.5 * (g[i] - g[i - 1]) ** 2 / dx;
  eOut /= c; // both in the same normalisation: ½∫u_x² dx against (1/c)∫u_t² dt
  // sensors: optional additive noise
  const sL = Float64Array.from(recL), sR = Float64Array.from(recR);
  if (!a.ideal_sensors) { const rn = N.rng(7); for (let n = 0; n <= Nf; n++) { sL[n] += v.sigma_n * rn.normal(); sR[n] += v.sigma_n * rn.normal(); } }
  // backward: quiescent medium driven at the sensors by the time-reversed records
  up = new Float64Array(nx); u = new Float64Array(nx); un = new Float64Array(nx);
  up[0] = sL[Nf]; u[0] = sL[Nf - 1];
  if (a.two_sided) { up[nx - 1] = sR[Nf]; u[nx - 1] = sR[Nf - 1]; }
  const src = [up[is], u[is]];
  for (let mI = 1; mI < Nf; mI++) {
    step(u, up, un); un[0] = sL[Nf - mI - 1]; un[nx - 1] = a.two_sided ? sR[Nf - mI - 1] : u[nx - 2];
    [up, u, un] = [u, un, up]; src.push(u[is]);
    if ((mI + 1) % every === 0 || mI + 1 === Nf) { frames.push(Array.from(u)); times.push((Nf + mI + 1) * dt); }
  }
  const wF = Array.from(u);
  let ip = 0; for (let i = 1; i < nx; i++) if (Math.abs(wF[i]) > Math.abs(wF[ip])) ip = i;
  let sw = 0, sg = 0, swg = 0, bg = 0, nb = 0, eIn = 0;
  for (let i = 0; i < nx; i++) { sw += wF[i] ** 2; sg += g[i] ** 2; swg += wF[i] * g[i]; if (Math.abs(xs[i] - xs[is]) > 4 * sig) { bg += wF[i] ** 2; nb++; } else if (Math.abs(xs[i] - xs[is]) <= 3 * sig) eIn += wF[i] ** 2; }
  // full width at half maximum around the largest peak
  const half = Math.abs(wF[ip]) / 2; let il = ip, ir = ip;
  while (il > 0 && Math.abs(wF[il]) > half) il--; while (ir < nx - 1 && Math.abs(wF[ir]) > half) ir++;
  const xl = il === ip ? xs[il] : xs[il] + dx * (half - Math.abs(wF[il])) / Math.max(Math.abs(wF[il + 1]) - Math.abs(wF[il]), 1e-300);
  const xr = ir === ip ? xs[ir] : xs[ir] - dx * (half - Math.abs(wF[ir])) / Math.max(Math.abs(wF[ir - 1]) - Math.abs(wF[ir]), 1e-300);
  return { nx, xs, dx, dt, Nf, g, wF, is, ip, sig, gam, recL: Array.from(recL), recR: Array.from(recR), src, frames, times, resid, e0, eOut,
    q: wF[is], corr: swg / Math.sqrt(Math.max(sw * sg, 1e-300)), fwhm: xr - xl, bgRms: nb ? Math.sqrt(bg / nb) : 0, eFrac: eIn / sg, peakL: N.maxOf(Array.from(recL)) };
}

const timeReversal = {
  id: 'time-reversal-focusing',
  title: 'Time-reversal focusing of a wave pulse',
  module: [1, 2], klass: 'I', domains: ['waves'],
  keywords: ['time reversal', 'time-reversal', 'time reversed', 'time-reversal mirror', 'refocusing', 'focusing', 'reciprocity', 'phase conjugation', 'loschmidt echo', 'wave equation', 'pulse', 'time reversal symmetry', 'reversibility'],
  summary: 'A pulse is emitted in a one-dimensional medium, recorded at sensors on the boundary and re-emitted in reverse time order; the wave reconverges on its source. Focus quality is quantified for full and partial apertures, a scattering inclusion, sensor noise and damping.',
  background: [
    'The lossless wave equation contains only a second derivative in time, so if u(x, t) is a solution then u(x, −t) is one too. A set of transducers that records the field on a surface enclosing the source and replays the records backwards therefore launches a wave that retraces the original propagation and converges on the source. This is the time-reversal mirror developed by Fink and co-workers, used in medical ultrasound, underwater acoustics and non-destructive testing.',
    'Time-reversal focusing does not need the medium to be uniform: reflections from scatterers are retraced as well, so a heterogeneous medium can even improve the focus obtained from a limited aperture. What it does need is reciprocity and the absence of dissipation. A damping term, first order in time, changes sign under time reversal; the replayed wave is attenuated again rather than re-amplified, and the focus is weakened by the loss accumulated over both journeys.',
  ],
  phenomena: ['Time-reversal invariance of the wave equation', 'Reciprocity', 'Refocusing through a scattering medium', 'Aperture limitation', 'Dissipation breaking time-reversal symmetry'],
  laws: ['newton2', 'energy', 'causality', 'noether'],
  refs: ['Fink, M. (1992). Time reversal of ultrasonic fields — Part I: Basic principles. IEEE Trans. Ultrason. Ferroelectr. Freq. Control 39, 555–566.', 'Fink, M. (1997). Time reversed acoustics. Physics Today 50(3), 34–40.', 'Draeger, C. & Fink, M. (1997). One-channel time reversal of elastic waves in a chaotic 2D-silicon cavity. Phys. Rev. Lett. 79, 407–410.', 'Morse, P. M. & Ingard, K. U. (1968). Theoretical Acoustics, McGraw-Hill.'],
  inputs: [
    inp('L', 'Length of the medium', 'm', 1, { min: 0.05, max: 100, kind: 'geometry', aliases: ['length', 'domain length', 'long'] }),
    inp('c_w', 'Wave speed', 'm/s', 343, { min: 10, max: 6000, kind: 'fluid', aliases: ['wave speed', 'speed of sound', 'sound speed'] }),
    inp('x_s', 'Source position as a fraction of the length', '1', 0.4, { min: 0.15, max: 0.6, kind: 'geometry', aliases: ['source position', 'source at'] }),
    inp('w_p', 'Pulse width (standard deviation) as a fraction of the length', '1', 0.02, { min: 0.01, max: 0.04, aliases: ['pulse width', 'pulse length'] }),
    inp('zeta_L', 'Attenuation parameter γL/c (damping over one transit)', '1', 0.5, { min: 0, max: 5, aliases: ['damping', 'attenuation', 'loss'] }),
    inp('c_ratio', 'Wave speed in the inclusion relative to the host', '1', 0.6, { min: 0.4, max: 1, kind: 'fluid', aliases: ['inclusion speed', 'speed ratio', 'contrast'] }),
    inp('sigma_n', 'Sensor noise, r.m.s. relative to the emitted amplitude', '%', 5, { min: 0, max: 50, aliases: ['noise', 'sensor noise'] }),
    inp('n_x', 'Grid points', '1', 401, { min: 201, max: 801, kind: 'numerical' }),
  ],
  assumptions: [
    asm('lossless', 'The medium is lossless, so the wave equation is invariant under time reversal.', { why: 'Ideal case', alt: 'A damping term γ ∂u/∂t attenuates the wave on both the outward and the replayed journey.' }),
    asm('two_sided', 'Sensors at both ends record and re-emit (the mirror encloses the source).', { why: 'Full aperture', alt: 'Only the left-hand sensor is used; the right-hand end is left open.' }),
    asm('homogeneous', 'The wave speed is uniform.', { why: 'Simplest medium', alt: 'A slower inclusion between 62 % and 74 % of the length reflects and delays part of the wave.' }),
    asm('ideal_sensors', 'The sensors are noise-free.', { why: 'Isolates the wave physics', alt: 'Independent Gaussian noise is added to each recorded sample.' }),
  ],
  symbols: { u: ['Wave displacement', 'm'], x: ['Position', 'm'], t: ['Time', 's'], c_x: ['Local wave speed', 'm/s'], gamma_d: ['Damping rate', '1/s'], u_a: ['Emitted amplitude', 'm'], u_0: ['Initial displacement', 'm'], u_TR: ['Displacement imposed at a sensor during replay', 'm'], u_rec: ['Displacement recorded at that sensor', 'm'], n_s: ['Sensor noise', 'm'], q_f: ['Refocused amplitude over emitted amplitude', '1'], T_r: ['Recording time', 's'] },
  equations: a => [
    eq('wave', 'Wave equation', `pd2(u,t)${a.lossless ? '' : ' + gamma_d*pd(u,t)'}`, 'c_x^2*pd2(u,x)', { kind: 'law', origin: 'Newton\'s second law for the medium' }),
    a.homogeneous ? eq('cx', 'Wave speed', 'c_x', 'c_w', { kind: 'closure', needs: ['homogeneous'] }) : eq('cx', 'Wave speed inside the inclusion', 'c_x', 'c_ratio*c_w', { kind: 'closure' }),
    ...(a.lossless ? [] : [eq('gam', 'Damping rate', 'gamma_d', 'zeta_L*c_w/L', { kind: 'definition' })]),
    eq('ic', 'Emitted pulse', 'u_0', 'u_a*exp(-(x - x_s*L)^2/(2*(w_p*L)^2))', { kind: 'initial' }),
    eq('tr', 'Replay at a sensor', 'u_TR', `u_rec${a.ideal_sensors ? '' : ' + n_s'}`, { kind: 'boundary', origin: 'Time-reversal mirror', note: 'The record is replayed in reverse order: the value imposed at time t is the one recorded at T_r − t' }),
    a.lossless
      ? eq('qf', 'Expected refocused amplitude', 'q_f', a.two_sided ? '1' : '1/2', { kind: 'derived', origin: 'Time-reversal invariance; half the wave is recorded by one sensor' })
      : eq('qf', 'Expected refocused amplitude with damping', 'q_f', a.two_sided ? '(exp(-zeta_L*x_s) + exp(-zeta_L*(1 - x_s)))/2' : 'exp(-zeta_L*x_s)/2', { kind: 'derived', origin: 'Attenuation exp(−γt/2) accumulated on the outward and return paths' }),
  ],
  derivation: a => [
    { text: 'The lossless wave equation is unchanged by the substitution t → −t, because time enters only through a second derivative.', tex: '\\frac{\\partial^2 u}{\\partial t^2} = c^2\\frac{\\partial^2 u}{\\partial x^2}\\quad\\Rightarrow\\quad u(x,-t)\\ \\text{is also a solution}' },
    { text: 'The emitted pulse splits into two half-amplitude pulses travelling in opposite directions (d\'Alembert), which reach the sensors at the ends.', tex: 'u(x,t) = \\tfrac12 u_0(x-ct) + \\tfrac12 u_0(x+ct)' },
    { text: 'Once the field inside has left, imposing the records in reverse order at the boundary defines a solution that coincides with the time-reversed original, by uniqueness of the boundary-value problem.', tex: 'u_{TR}(x,t) = u(x, T_r - t)' },
    { text: 'At the instant T_r the two returning pulses overlap at the source and rebuild the emitted shape; they then pass through each other, since nothing absorbs them there.', tex: 'u_{TR}(x,T_r) = u_0(x)' },
    ...(a.lossless ? [] : [{ text: 'With damping the equation is no longer time-reversal invariant. Each pulse decays as exp(−γt/2) on the way out and again on the way back, so the refocused amplitude is reduced by the loss over the round trip.', tex: '\\frac{A_f}{A_0} \\approx \\tfrac12\\left[e^{-\\gamma x_s/c} + e^{-\\gamma (L-x_s)/c}\\right]' }]),
  ],
  solve(v, a) {
    const s = trSim(v, a), warnings = [];
    const zs = v.zeta_L, qPred = a.lossless ? (a.two_sided ? 1 : 0.5) : (a.two_sided ? (Math.exp(-zs * v.x_s) + Math.exp(-zs * (1 - v.x_s))) / 2 : Math.exp(-zs * v.x_s) / 2);
    const fw0 = 2 * Math.sqrt(2 * Math.log(2)) * s.sig, tRec = s.Nf * s.dt;
    if (!a.homogeneous && s.resid > 0.02) warnings.push('Reverberation inside the inclusion had not fully left the medium when recording stopped; part of the information is missing from the records.');
    if (!a.homogeneous && !a.lossless) warnings.push('With an inclusion the simple damped-amplitude estimate ignores the extra path length of reflected waves.');
    if (!a.ideal_sensors && v.sigma_n > 0.2) warnings.push('The sensor noise is large: the focus is comparable with the noise injected along the whole medium.');
    const tm = Array.from({ length: s.Nf + 1 }, (_, n) => n * s.dt * 1e3), ideal = a.lossless && a.two_sided && a.homogeneous && a.ideal_sensors;
    const ym = 1.1 * Math.max(1, ...s.frames.map(f => N.maxOf(f.map(Math.abs))));
    return {
      scalars: [
        scalar('q_f', 'Refocused amplitude at the source / emitted amplitude', s.q, '1'),
        scalar('q_pred', 'Expected amplitude ratio from the loss estimate', qPred, '1'),
        scalar('rho_f', 'Correlation of the refocused field with the emitted pulse', s.corr, '1'),
        scalar('E_f', 'Energy within ±3 pulse widths of the source / emitted energy', s.eFrac, '1'),
        scalar('w_f', 'Width of the focus (FWHM)', s.fwhm, 'm', { show: 'mm' }), scalar('w_0', 'Width of the emitted pulse (FWHM)', fw0, 'm', { show: 'mm' }),
        scalar('x_err', 'Offset of the focal peak from the source', s.xs[s.ip] - s.xs[s.is], 'm', { show: 'mm' }),
        scalar('bg', 'Background r.m.s. away from the focus / emitted amplitude', s.bgRms, '1'),
        scalar('SNR_f', 'Focus-to-background ratio', dB(Math.abs(s.q) / Math.max(s.bgRms, 1e-12)), 'dB', s.bgRms > 1e-12 ? {} : { text: 'Unbounded — no background' }),
        scalar('T_r', 'Recording time', tRec, 's', { show: 'ms' }), scalar('t_tr', 'Transit time L/c', v.L / v.c_w, 's', { show: 'ms' }),
        scalar('gamma_d', 'Damping rate', s.gam, '1/s'),
        scalar('resid', 'Largest field left in the medium when recording stopped', s.resid, '1'),
      ],
      series: [
        line('records', 'Signals recorded at the boundary sensors', 'Time', 'ms', tm, [{ label: 'Left sensor', data: s.recL }, { label: 'Right sensor', data: s.recR }], 'Displacement / emitted amplitude', '–'),
        line('focus', 'Refocused field against the emitted pulse', 'Position', 'm', s.xs, [{ label: 'Refocused at the focal instant', data: s.wF }, { label: 'Emitted pulse', data: s.g, dash: true }], 'Displacement / emitted amplitude', '–'),
        line('source-trace', 'Displacement at the source during replay', 'Replay time', 'ms', tm.slice(0, s.src.length), [{ label: 'At the source position', data: s.src }], 'Displacement / emitted amplitude', '–'),
      ],
      anims: [anim('wave', 'Emission, recording and time-reversed replay', 'Position', 'm', s.xs, s.frames, s.times, 'Displacement / emitted amplitude', '–', { yRange: [-ym, ym], note: 'Replay begins at the recording time' })],
      checks: [
        check('Time-reversal invariance: refocused field equals the emitted pulse', ideal ? s.q - 1 : 0, 1e-6, ideal ? 'Lossless medium, enclosing mirror, ideal sensors' : 'Not applicable with the present assumptions'),
        check('Energy recorded leaving equals energy emitted', a.lossless && a.homogeneous ? (s.eOut - s.e0) / s.e0 : 0, 0.03, a.lossless && a.homogeneous ? 'Integrated flux through both ends against initial strain energy' : 'Not applicable with loss or an inclusion still reverberating'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const id = { lossless: true, two_sided: true, homogeneous: true, ideal_sensors: true }, s = trSim(v, id), out = [];
    out.push(bench('Ideal time reversal restores the emitted amplitude', s.q, 1, 'Time-reversal invariance of the wave equation', 1e-9));
    out.push(bench('Ideal time reversal restores the pulse shape', s.corr, 1, 'Correlation with the emitted pulse', 1e-9));
    out.push(bench('Each outgoing pulse carries half the amplitude', s.peakL, 0.5, 'd\'Alembert solution', 1e-9));
    const o = trSim(v, { ...id, two_sided: false });
    out.push(bench('One-sided mirror refocuses half the amplitude', o.q, 0.5, 'Only one of the two outgoing pulses is recorded', 1e-9));
    const d = trSim(v, { ...id, lossless: false });
    out.push(bench('Damped refocused amplitude against the round-trip loss estimate', d.q, (Math.exp(-v.zeta_L * v.x_s) + Math.exp(-v.zeta_L * (1 - v.x_s))) / 2, 'A_f/A₀ ≈ ½[exp(−γx_s/c) + exp(−γ(L−x_s)/c)]', 0.03));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const xs = 80 + 480 * v.x_s;
    return svg(`
      ${S.rect(80, 150, 480, 40, 'd-body', 2)}
      ${a.homogeneous ? '' : S.rect(80 + 480 * 0.62, 150, 480 * 0.12, 40, 'd-liquid', 0) + S.text(80 + 480 * 0.68, 142, 'slow inclusion', 'd-text d-small')}
      ${S.rect(56, 136, 24, 68, 'd-hazard', 3)} ${S.text(68, 126, 'sensor')}
      ${S.rect(560, 136, 24, 68, a.two_sided ? 'd-hazard' : 'd-dim', 3)} ${S.text(572, 126, a.two_sided ? 'sensor' : 'open')}
      ${S.path(`M${xs - 30} 150 Q${xs} 80 ${xs + 30} 150`, 'd-pipe')} ${S.text(xs, 84, 'source pulse')}
      ${S.arrow(xs - 40, 110, xs - 110, 110)} ${S.arrow(xs + 40, 110, xs + 110, 110)} ${S.text(320, 60, '1  emit and record')}
      ${S.arrow(110, 232, xs - 24, 232, 'd-arrow d-heat')} ${a.two_sided ? S.arrow(530, 232, xs + 24, 232, 'd-arrow d-heat') : ''} ${S.text(320, 262, '2  replay the records backwards')}
      ${S.dim(80, 300, 560, 300, `L = ${lab(v.L, 'm')},  c = ${lab(v.c_w, 'm/s')}`)}
      ${S.text(320, 340, a.lossless ? 'lossless: the wave retraces its path' : `damped: γL/c = ${lab(v.zeta_L)}`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Demonstrate time-reversal focusing in an acoustic waveguide or on a plate, and measure how the focal amplitude depends on aperture, on a scatterer and on added absorption.',
    apparatus: ['Air-filled tube or water-filled channel several wavelengths long with anechoic terminations', 'Small source transducer at an interior point (used once as emitter, then as the probe)', 'Reversible transducers at each end with arbitrary-waveform generators and recorders', 'Removable scatterer (a section of different cross-section) and removable absorbing lining'],
    instruments: [{ name: 'Two-channel digitiser and arbitrary-waveform generator', measures: 'Recorded and replayed signals', range: '≥ 10× the pulse bandwidth', resolution: '14 bit' }, { name: 'Probe microphone or hydrophone on a traverse', measures: 'Field along the guide at the focal instant', range: '—', resolution: '±1 mm position' }, { name: 'Thermometer', measures: 'Temperature, for the wave speed', range: 'ambient', resolution: '±0.1 K' }],
    procedure: ['Emit a short pulse from the interior source and record at both end transducers until the signals have died away.', 'Reverse the records in time and replay them from the same transducers.', 'Record the signal at the source position and traverse the probe to map the focal spot.', 'Repeat using one end only, then with the scatterer inserted, then with the absorbing lining.', 'Change the temperature of the medium between recording and replay to test sensitivity to a changed medium.'],
    controls: ['Replay the records without reversing them: no focus should form', 'Replay with one record delayed: the focus should degrade'],
    signatures: ['A compressed pulse at the source position at the predicted instant', 'Focal amplitude halved with one-sided replay in a uniform open guide', 'Focus preserved, or improved for a one-sided mirror, when a lossless scatterer is added', 'Focal amplitude falling exponentially with added attenuation'],
    safety: ['Limit drive levels to protect transducers and hearing', 'Electrical safety of power amplifiers'],
  },
  falsify: ['In a lossless, reciprocal medium with an enclosing mirror, a refocused pulse whose shape differs from the emitted one beyond the bandwidth and noise limits of the apparatus.', 'A focus that forms when the records are replayed without time reversal.', 'A focal amplitude that does not fall when dissipation is added.'],
  alternatives: [{ name: 'Phase conjugation', text: 'The monochromatic equivalent: conjugating the phase of each frequency component is the same operation as reversing the signal in time.' }, { name: 'Diffraction-limited focus', text: 'In two and three dimensions the converging wave is followed by a diverging one, and without an acoustic sink at the source the focal spot cannot be smaller than half a wavelength.' }, { name: 'Flow or magnetic fields', text: 'A moving medium or a magnetic bias breaks reciprocity, so the replayed wave does not retrace its path even without dissipation.' }, { name: 'Inverse filtering', text: 'Compensates for attenuation by amplifying the attenuated components, at the cost of noise amplification.' }],
  hazards: [{ hazard: 'Unexpectedly high focal pressure', cause: 'Many channels adding coherently at the focus', mitigation: 'Calculate the focal gain before raising drive levels' }],
  standards: ['IEC 61391-1 (ultrasonics — pulse-echo scanners — calibration of spatial measurement systems)', 'ISO 16063 series (methods for the calibration of vibration and shock transducers)'],
  limits: 'One spatial dimension, linear waves, displacement sensors that both record and impose the field exactly. In higher dimensions a finite aperture and diffraction limit the focus. The damping model is a uniform viscous term; frequency-dependent absorption additionally distorts the pulse.',
  numerics: { method: 'Explicit leapfrog finite differences at unit Courant number in the host medium, with exact one-way (Mur) open boundaries during recording and prescribed boundary values during replay', order: 2, stability: 'Stable for local Courant number up to one', resolution: 'n_x' },
  optimise: { objective: 'q_f', sense: 'max', vars: ['x_s'], note: 'With damping and a one-sided mirror, sources nearer the sensor refocus more strongly.' },
  inverse: { series: 'focus', fit: ['zeta_L'] },
  extensions: ['Two-dimensional cavity with a single-channel mirror', 'Acoustic sink to beat the diffraction limit', 'Medium changed between recording and replay (Loschmidt echo sensitivity)', 'Iterative time reversal for selective focusing'],
};

// ------------------------------------------------------------------ Doppler effect and beats
/** Received frequency for source speed vs (toward the observer) and observer speed vo (toward the source). Returns NaN when the source outruns its waves. */
function dopplerF(v, a, vs = v.v_s, vo = v.v_o, cosT = a.collinear ? 1 : Math.cos(v.theta)) {
  const f0 = v.f_0, us = vs * cosT;
  if (a.classical) {
    const w = a.still_medium ? 0 : v.v_w, c1 = v.c_s + w, c2 = v.c_s - w;
    if (a.one_way) return c1 - us > 0 && c1 + vo > 0 ? f0 * (c1 + vo) / (c1 - us) : NaN;
    return c1 - vo > 0 && c2 - us > 0 && c1 + us > 0 && c2 + vo > 0 ? f0 * (c1 + us) / (c1 - vo) * (c2 + vo) / (c2 - us) : NaN;
  }
  const bs = vs / C.c, bo = vo / C.c;
  if (Math.abs(bs) >= 1 || Math.abs(bo) >= 1) return NaN;
  if (a.one_way) return f0 * Math.sqrt((1 + bo) / (1 - bo)) * Math.sqrt(1 - bs * bs) / (1 - bs * cosT);
  const br = (bo + bs * cosT) / (1 + bo * bs * cosT);
  return f0 * (1 + br) / (1 - br);
}

const doppler = {
  id: 'doppler-and-beats',
  title: 'Doppler shift and beats',
  module: [1, 2], klass: 'I', domains: ['waves', 'classical', 'relativity'],
  keywords: ['doppler effect', 'doppler shift', 'doppler', 'beats', 'beat frequency', 'moving source', 'moving observer', 'siren', 'redshift', 'blueshift', 'radar speed', 'relativistic doppler', 'pitch change', 'frequency shift'],
  summary: 'Frequency received from a moving source by a moving observer in a medium, with wind, oblique motion and echo options; the relativistic formula as an alternative; and the beat produced by mixing the received tone with the emitted one.',
  background: [
    'When a source of waves moves through a medium, successive crests are emitted from different positions, so the wavelength is shortened ahead of the source and lengthened behind. A moving observer meets the crests at a different rate. For sound these two effects are not equivalent: the received frequency is f₀(c + v_o)/(c − v_s), which depends on the speeds of source and observer separately, each measured relative to the medium.',
    'Light needs no medium. Only the relative velocity matters, and time dilation of the source adds a factor that survives even for purely transverse motion. Two tones of nearly equal frequency superpose to a tone at the mean frequency whose loudness swells and fades at the difference frequency; mixing a Doppler-shifted echo with the emitted wave therefore gives a beat proportional to the target\'s speed, the principle of Doppler radar and ultrasonic flow meters.',
  ],
  phenomena: ['Wavelength compression ahead of a moving source', 'Changed crest-arrival rate for a moving observer', 'Convection of sound by wind', 'Time dilation (transverse Doppler shift)', 'Beating of two tones'],
  laws: ['causality', 'sr'],
  refs: ['Doppler, C. (1842). Über das farbige Licht der Doppelsterne und einiger anderer Gestirne des Himmels. Abh. Königl. Böhm. Ges. Wiss. 2, 465–482.', 'Einstein, A. (1905). Zur Elektrodynamik bewegter Körper. Ann. Phys. 17, 891–921.', 'Ives, H. E. & Stilwell, G. R. (1938). An experimental study of the rate of a moving atomic clock. J. Opt. Soc. Am. 28, 215–226.', 'Kinsler, L. E., Frey, A. R., Coppens, A. B. & Sanders, J. V. (2000). Fundamentals of Acoustics, 4th ed., Wiley.'],
  inputs: [
    inp('f_0', 'Emitted frequency', 'Hz', 440, { min: 1, max: 1e11, aliases: ['frequency', 'emitted frequency', 'source frequency', 'hz', 'tone'] }),
    inp('c_s', 'Wave speed in the medium', 'm/s', 343, { min: 300, max: 3e8, kind: 'fluid', aliases: ['speed of sound', 'wave speed', 'sound speed'], src: 'Air at 20 °C' }),
    inp('v_s', 'Source speed toward the observer', 'm/s', 30, { min: -250, max: 250, aliases: ['source speed', 'source velocity', 'moving at', 'approaching', 'speed'] }),
    inp('v_o', 'Observer speed toward the source', 'm/s', 0, { min: -250, max: 250, aliases: ['observer speed', 'observer velocity', 'listener speed'] }),
    inp('v_w', 'Wind speed from source toward observer', 'm/s', 10, { min: -30, max: 30, kind: 'environment', env: 'wind_speed', aliases: ['wind', 'wind speed'] }),
    inp('theta', 'Angle between source velocity and the line of sight', 'deg', 30, { min: 0, max: 180, kind: 'geometry', aliases: ['angle'] }),
    inp('b_min', 'Closest distance of the fly-by path', 'm', 10, { min: 0.1, max: 1e4, kind: 'geometry', aliases: ['closest approach', 'miss distance', 'passes at'] }),
  ],
  assumptions: [
    asm('classical', 'The wave travels in a medium at a speed far below that of light (Galilean kinematics).', { why: 'Sound, water waves', alt: 'The wave is light in vacuum: only relative velocity matters and time dilation is included.' }),
    asm('still_medium', 'The medium is at rest.', { why: 'No wind', alt: 'A steady wind along the line from source to observer carries the wave.' }),
    asm('collinear', 'Source and observer move along the line joining them.', { why: 'Head-on approach or recession', alt: 'The source velocity makes an angle θ with the line of sight; only its radial component shifts the frequency classically.' }),
    asm('one_way', 'The observer receives the wave directly from the source.', { why: 'Passive listening', alt: 'The moving body reflects a wave sent by the observer (echo): the shift is applied on both legs.' }),
  ],
  symbols: { f_obs: ['Received frequency', 'Hz'], u_s: ['Radial component of the source velocity', 'm/s'], beta_s: ['Source speed over the speed of light', '1'], beta_o: ['Observer speed over the speed of light', '1'], beta_r: ['Relative closing speed over the speed of light', '1'], f_beat: ['Beat frequency', 'Hz'], lambda_f: ['Wavelength ahead of the source', 'm'] },
  equations: a => {
    const w = a.still_medium ? '' : ' + v_w', wm = a.still_medium ? '' : ' - v_w', ct = a.collinear ? '' : '*cos(theta)';
    const out = [eq('us', 'Radial source speed', 'u_s', `v_s${ct}`, { kind: 'definition' })];
    if (a.classical) {
      out.push(a.one_way
        ? eq('dop', 'Doppler shift in a medium', 'f_obs', `f_0*(c_s${w} + v_o)/(c_s${w} - u_s)`, { kind: 'derived', origin: 'Crest counting with Galilean kinematics' })
        : eq('dop', 'Doppler shift of an echo', 'f_obs', `f_0*(c_s${w} + u_s)/(c_s${w} - v_o)*(c_s${wm} + v_o)/(c_s${wm} - u_s)`, { kind: 'derived', origin: 'Shift on the outward and on the return leg' }));
      out.push(eq('lam', 'Wavelength ahead of the source', 'lambda_f', `(c_s${w} - u_s)/f_0`, { kind: 'derived' }));
    } else {
      out.push(eq('bs', 'Source speed ratio', 'beta_s', 'v_s/c', { kind: 'definition' }), eq('bo', 'Observer speed ratio', 'beta_o', 'v_o/c', { kind: 'definition' }));
      out.push(a.one_way
        ? eq('dop', 'Relativistic Doppler shift', 'f_obs', `f_0*sqrt((1 + beta_o)/(1 - beta_o))*sqrt(1 - beta_s^2)/(1 - beta_s${ct})`, { kind: 'law', origin: 'Lorentz transformation of the wave four-vector' })
        : eq('dop', 'Relativistic echo shift', 'f_obs', 'f_0*(1 + beta_r)/(1 - beta_r)', { kind: 'law', origin: 'Lorentz transformation applied on both legs' }));
      if (!a.one_way) out.push(eq('br', 'Relative closing speed', 'beta_r', `(beta_o + beta_s${ct})/(1 + beta_o*beta_s${ct})`, { kind: 'law', origin: 'Relativistic addition of velocities' }));
    }
    out.push(eq('beat', 'Beat frequency against the emitted tone', 'f_beat', 'abs(f_obs - f_0)', { kind: 'derived', origin: 'Superposition of two tones' }));
    return out;
  },
  derivation: a => [
    { text: 'A source approaching at speed v_s emits crests one period apart, but each new crest starts closer to the observer by v_s/f₀. The wavelength ahead of the source is shortened.', tex: '\\lambda\' = \\frac{c - v_s}{f_0}' },
    { text: 'An observer approaching at speed v_o meets crests at relative speed c + v_o.', tex: 'f = \\frac{c+v_o}{\\lambda\'} = f_0\\,\\frac{c+v_o}{c-v_s}' },
    ...(a.classical ? [] : [{ text: 'For light the source\'s clock runs slow by the Lorentz factor and the wave speed is the same for every observer; the result depends only on relative velocity.', tex: 'f = f_0\\,\\frac{\\sqrt{1-\\beta^2}}{1-\\beta\\cos\\theta}\\ \\xrightarrow{\\ \\theta=0\\ }\\ f_0\\sqrt{\\frac{1+\\beta}{1-\\beta}}' }]),
    ...(a.one_way ? [] : [{ text: 'A moving reflector first receives a shifted wave as a moving observer and then re-emits it as a moving source, so the shift is applied twice.', tex: 'f_{echo} = f_0\\,\\frac{c+v}{c-v} \\approx f_0\\left(1+\\frac{2v}{c}\\right)' }]),
    { text: 'Adding two tones of nearly equal frequency gives a carrier at the mean frequency with an envelope at half the difference; the intensity therefore pulses at the difference frequency.', tex: '\\cos 2\\pi f_1 t + \\cos 2\\pi f_2 t = 2\\cos\\!\\big(\\pi(f_1-f_2)t\\big)\\cos\\!\\big(\\pi(f_1+f_2)t\\big)' },
  ],
  solve(v, a) {
    const f = dopplerF(v, a), fr = dopplerF(v, a, -v.v_s, -v.v_o), ok = Number.isFinite(f), warnings = [];
    const c = a.classical ? v.c_s : C.c, w = a.classical && !a.still_medium ? v.v_w : 0, us = v.v_s * (a.collinear ? 1 : Math.cos(v.theta));
    if (!ok) warnings.push('The source moves faster than the wave: no Doppler tone reaches the observer ahead of the source; a shock (Mach cone) forms instead.');
    if (!a.classical && v.c_s < 0.99 * C.c) warnings.push('The relativistic formula applies to light in vacuum; the wave speed entered for the medium is not used.');
    if (a.classical && Math.max(Math.abs(v.v_s), Math.abs(v.v_o)) > 0.1 * C.c) warnings.push('Speeds above a tenth of the speed of light need the relativistic formula.');
    const fb = ok ? Math.abs(f - v.f_0) : 0;
    // crest-arrival count: emit crests at the source and time their arrival at the observer
    let cnt = 0;
    if (ok && a.classical && a.one_way) { const nC = 200, D = 1e3 * c, tau = n => (D + (c + w - us) * n / v.f_0) / (c + w + v.v_o); cnt = nC / (tau(nC) - tau(0)) / f - 1; }
    const Ms = N.linspace(-0.9, 0.9, 181);
    const fl = v.b_min / Math.max(Math.abs(v.v_s), 1e-9), T = Math.abs(v.v_s) > 1e-6 ? 4 * fl : 1, te = N.linspace(-T, T, 241);
    const fly = te.map(t => { const x = v.v_s * t, r = Math.hypot(x, v.b_min); return dopplerF(v, { ...a, collinear: false, one_way: true, still_medium: true }, v.v_s, 0, -x / r); });
    const ta = te.map(t => t + Math.hypot(v.v_s * t, v.b_min) / c);
    const Tb = fb > 0 ? 1 / fb : 1 / v.f_0, tb = N.linspace(0, 3 * Tb, 1201), fine = ok && fb > 0 && v.f_0 / fb < 80;
    const env = tb.map(t => 2 * Math.abs(Math.cos(Math.PI * fb * t)));
    return {
      scalars: [
        scalar('f_obs', 'Received frequency', ok ? f : NaN, 'Hz', ok ? {} : { text: 'None — source outruns its waves' }),
        scalar('df', 'Frequency shift', ok ? f - v.f_0 : NaN, 'Hz', ok ? {} : { text: 'Not defined' }),
        scalar('ratio', 'Received / emitted frequency', ok ? f / v.f_0 : NaN, '1', ok ? {} : { text: 'Not defined' }),
        scalar('cents', 'Musical interval of the shift', ok ? 1200 * Math.log2(f / v.f_0) : NaN, '1', ok ? { note: 'cents; 100 cents is one semitone' } : { text: 'Not defined' }),
        scalar('lambda_0', 'Wavelength from a source at rest', c / v.f_0, 'm'),
        scalar('lambda_f', 'Wavelength ahead of the moving source', Math.max(c + w - us, 0) / v.f_0, 'm'),
        scalar('M_s', 'Source speed / wave speed', v.v_s / c, '1'), scalar('M_o', 'Observer speed / wave speed', v.v_o / c, '1'),
        scalar('f_rec', 'Received frequency with both velocities reversed (receding)', Number.isFinite(fr) ? fr : NaN, 'Hz', Number.isFinite(fr) ? {} : { text: 'Not defined' }),
        scalar('f_beat', 'Beat frequency against the emitted tone', fb, 'Hz'),
        scalar('T_beat', 'Beat period', fb > 0 ? 1 / fb : 0, 's', fb > 0 ? {} : { text: 'No beat — frequencies equal' }),
        scalar('v_est', 'Closing speed inferred from the shift', ok ? (a.one_way ? c * (f - v.f_0) / f : c * (f - v.f_0) / (f + v.f_0)) : NaN, 'm/s', ok ? { note: 'Assuming a stationary observer and still medium' } : { text: 'Not defined' }),
      ],
      series: [
        line('f-vs-speed', 'Received frequency against speed', 'Speed / wave speed', '–', Ms, [{ label: 'Moving source, classical', data: Ms.map(M => v.f_0 / (1 - M)) }, { label: 'Moving observer, classical', data: Ms.map(M => v.f_0 * (1 + M)) }, { label: 'Relativistic (light)', data: Ms.map(M => v.f_0 * Math.sqrt((1 + M) / (1 - M))), dash: true }], 'Frequency', 'Hz', { note: 'Positive speed means approach' }),
        line('flyby', 'Frequency heard as the source passes', 'Arrival time', 's', ta, [{ label: 'Received frequency', data: fly }, { label: 'Emitted frequency', data: ta.map(() => v.f_0), dash: true }], 'Frequency', 'Hz', { note: 'Stationary observer, still medium, straight path at the closest distance given' }),
        line('beats', 'Beat between received and emitted tones', 'Time', 's', tb, fine ? [{ label: 'Sum of the two tones', data: tb.map(t => Math.cos(TAU * v.f_0 * t) + Math.cos(TAU * f * t)) }, { label: 'Envelope', data: env, dash: true }] : [{ label: 'Envelope', data: env }, { label: 'Lower envelope', data: env.map(q => -q), dash: true }], 'Amplitude (each tone = 1)', '–'),
      ],
      checks: [check('Crest-arrival count against the formula', cnt, 1e-9, ok && a.classical && a.one_way ? 'Arrival times of 200 successive crests' : 'Evaluated only for the direct classical case')],
      warnings,
    };
  },
  benchmarks(v, a) {
    const cl = { classical: true, still_medium: true, collinear: true, one_way: true }, out = [];
    out.push(bench('No relative motion: no shift', dopplerF({ ...v, v_s: 0, v_o: 0 }, a), v.f_0, 'f = f₀', 1e-12));
    out.push(bench('Source approaching at one-tenth of the wave speed', dopplerF({ ...v, v_s: 0.1 * v.c_s, v_o: 0 }, cl) / v.f_0, 1 / 0.9, 'f/f₀ = 1/(1 − M)', 1e-12));
    out.push(bench('Observer approaching at one-tenth of the wave speed', dopplerF({ ...v, v_s: 0, v_o: 0.1 * v.c_s }, cl) / v.f_0, 1.1, 'f/f₀ = 1 + M', 1e-12));
    out.push(bench('Relativistic shift at half the speed of light', dopplerF({ ...v, v_s: 0.5 * C.c, v_o: 0 }, { ...cl, classical: false }) / v.f_0, Math.sqrt(3), 'f/f₀ = √((1+β)/(1−β))', 1e-12));
    out.push(bench('Transverse relativistic shift at 0.6c', dopplerF({ ...v, v_s: 0.6 * C.c, v_o: 0, theta: Math.PI / 2 }, { ...cl, classical: false, collinear: false }) / v.f_0, 0.8, 'f/f₀ = √(1 − β²): pure time dilation', 1e-9));
    out.push(bench('Echo from a slow reflector', (dopplerF({ ...v, v_s: 1e-4 * v.c_s, v_o: 0 }, { ...cl, one_way: false }) / v.f_0 - 1) / 2e-4, 1, 'Δf/f₀ → 2v/c', 1e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const sx = 250, k = N.clamp(v.v_s / (a.classical ? v.c_s : C.c), -0.8, 0.8);
    return svg(`
      ${[1, 2, 3, 4, 5].map(n => S.circle(sx - k * n * 30, 180, n * 30, 'd-line')).join('')}
      ${S.circle(sx, 180, 7, 'd-hazard')} ${S.text(sx, 210, 'source', 'd-text d-small')}
      ${S.arrow(sx + 10, 180, sx + 10 + 60 * Math.sign(k || 1), 180, 'd-arrow d-heat')} ${S.text(sx + 40, 168, `v_s = ${lab(v.v_s, 'm/s')}`, 'd-text d-small')}
      ${S.rect(540, 166, 22, 28, 'd-body')} ${S.text(551, 214, 'observer', 'd-text d-small')}
      ${v.v_o !== 0 ? S.arrow(538, 180, 538 - 40 * Math.sign(v.v_o), 180) : ''}
      ${S.text(470, 120, 'shortened wavelength ahead', 'd-text d-small')} ${S.text(90, 120, 'lengthened behind', 'd-text d-small')}
      ${S.text(320, 330, `f₀ = ${lab(v.f_0, 'Hz')}   ${a.classical ? `c = ${lab(v.c_s, 'm/s')}` : 'light in vacuum'}${a.one_way ? '' : '   echo'}`)}
    `);
  },
  experiment: {
    objective: 'Measure the Doppler shift of a tone from a source moving at known speed, separately for a moving source and a moving observer, and the beat against a stationary reference.',
    apparatus: ['Small loudspeaker emitting a steady tone of a few kilohertz on a motor-driven carriage or rotating arm', 'Second identical stationary loudspeaker as reference', 'Fixed microphone on the line of motion; alternatively the microphone on the carriage and the source fixed'],
    instruments: [{ name: 'Microphone with digitiser and spectrum analysis', measures: 'Received frequency and beat frequency', range: '20 Hz–20 kHz', resolution: '±0.1 Hz with 10 s records' }, { name: 'Photogates or encoder', measures: 'Carriage speed', range: '0–20 m/s', resolution: '±0.5 %' }, { name: 'Thermometer and anemometer', measures: 'Sound speed and air movement', range: 'ambient', resolution: '±0.2 K, ±0.1 m/s' }],
    procedure: ['Record the tone with everything at rest to fix f₀.', 'Run the source toward and away from the microphone at several speeds and record the frequency in each pass.', 'Exchange the roles: fixed source, moving microphone.', 'Switch on the reference loudspeaker and measure the beat frequency directly.', 'For the fly-by, place the microphone a known distance from the track and record the frequency through the pass.'],
    controls: ['Stationary run before and after to check frequency drift', 'Repeat in both directions to cancel any steady air current'],
    signatures: ['Shift proportional to speed at low speed', 'Slightly larger shift for a moving source than for a moving observer at the same speed, the difference growing as (v/c)²', 'Beat frequency equal to the measured shift', 'An S-shaped frequency curve through a fly-by, steeper for a closer pass'],
    safety: ['Guard the moving carriage or rotating arm', 'Keep sound levels moderate'],
  },
  falsify: ['For sound, equal shifts for a moving source and a moving observer at speeds where the second-order difference is resolvable.', 'For light, any dependence on the separate velocities of source and observer rather than their relative velocity.', 'Absence of a transverse (time-dilation) shift for a fast source viewed at right angles.'],
  alternatives: [{ name: 'Relativistic Doppler effect', text: 'Required for light and for any speed comparable with c; symmetric in source and observer and including a transverse shift.' }, { name: 'Gravitational and cosmological redshift', text: 'Frequency shifts that arise from gravitational potential difference or the expansion of space, not from motion through space.' }, { name: 'Supersonic sources', text: 'When the source exceeds the wave speed the crests pile into a Mach cone and the Doppler formula no longer applies ahead of the source.' }],
  hazards: [{ hazard: 'Moving machinery', cause: 'Carriage or rotating arm', mitigation: 'Guards and an emergency stop' }],
  standards: ['IEC 61672-1 (sound level meters)', 'ISO 9613-1 (attenuation of sound during propagation outdoors: absorption by the atmosphere)'],
  limits: 'Uniform straight-line motion, a uniform medium and steady wind along the line of sight. The classical formulae require speeds below the wave speed; the relativistic ones apply to light in vacuum. Near-field effects and acceleration are neglected.',
  numerics: { method: 'Closed-form expressions; retarded-time mapping for the fly-by curve' },
  inverse: { series: 'flyby', fit: ['v_s', 'b_min'] },
  extensions: ['Accelerating and circling sources', 'Doppler broadening of spectral lines', 'Pulsed-Doppler range–velocity measurement', 'Mach cone and sonic boom'],
};

// ------------------------------------------------------------------ one-dimensional phononic crystal
function pcCore(v, a, lossless = a.lossless) {
  const c1 = a.longitudinal ? v.c_1 : v.ct_1, c2 = a.longitudinal ? v.c_2 : v.ct_2, eta = lossless ? 0 : v.eta_l;
  const cc1 = [c1, -c1 * eta / 2], cc2 = [c2, -c2 * eta / 2], Z1 = [v.rho_1 * cc1[0], v.rho_1 * cc1[1]], Z2 = [v.rho_2 * cc2[0], v.rho_2 * cc2[1]];
  const sI = a.perfect_bond ? 0 : 1 / v.K_i, d1 = v.d_1, d2 = v.d_2, ac = d1 + d2, Nc = Math.max(1, Math.round(v.N_c));
  const Ze = a.matched_ends ? v.rho_1 * c1 : v.Z_ext;
  const layer = (w, cc, Z, d) => { const kd = cdiv([w * d, 0], cc), co = ccos(kd), si = csin(kd), wz = [w * Z[0], w * Z[1]]; return [[co, cdiv(si, wz)], [cmul([-1, 0], cmul(wz, si)), co]]; };
  const S = [[[1, 0], [sI, 0]], [[0, 0], [1, 0]]];
  const cell = w => { const m1 = layer(w, cc1, Z1, d1), m2 = layer(w, cc2, Z2, d2); return sI > 0 ? mmul(S, mmul(m2, mmul(S, m1))) : mmul(m2, m1); };
  const half = w => { const m = cell(w); return [(m[0][0][0] + m[1][1][0]) / 2, (m[0][0][1] + m[1][1][1]) / 2]; };
  /** Bloch phase per cell: [Re(qa) in 0..π, Im(qa) ≥ 0]. */
  const bloch = w => {
    const h = half(w);
    if (Math.abs(h[1]) < 1e-14 * Math.max(1, Math.abs(h[0]))) return Math.abs(h[0]) <= 1 ? [Math.acos(h[0]), 0] : [h[0] > 0 ? 0 : Math.PI, Math.log(Math.abs(h[0]) + Math.sqrt(h[0] * h[0] - 1))];
    const s = csqrt(csub([1, 0], cmul(h, h))), t = cadd(h, [-s[1], s[0]]), q = [Math.atan2(t[1], t[0]), -Math.log(cabs(t))];
    return q[1] < 0 ? [Math.abs(q[0]), -q[1]] : [Math.abs(q[0]), q[1]];
  };
  /** Amplitude transmission and reflection of n cells between half-spaces of impedance Ze. */
  const trans = (w, n = Nc) => {
    let M = [[[1, 0], [0, 0]], [[0, 0], [1, 0]]], b = cell(w), e = n;
    while (e > 0) { if (e & 1) M = mmul(b, M); b = mmul(b, b); e >>= 1; }
    const j = [0, w * Ze], P = csub(M[0][0], cmul(j, M[0][1])), Q = cadd(M[0][0], cmul(j, M[0][1])), R = csub(M[1][0], cmul(j, M[1][1])), Sv = cadd(M[1][0], cmul(j, M[1][1]));
    const r = cdiv(csub(Sv, cmul(j, Q)), csub(cmul(j, P), R)), t = cadd(Q, cmul(P, r));
    return { T: cabs(t) ** 2, R: cabs(r) ** 2 };
  };
  const fB = 1 / (2 * (d1 / c1 + d2 / c2)), rhoE = (v.rho_1 * d1 + v.rho_2 * d2) / ac;
  const cEff = Math.sqrt(ac / (rhoE * (d1 / (v.rho_1 * c1 * c1) + d2 / (v.rho_2 * c2 * c2) + 2 * sI)));
  return { c1, c2, Z1: v.rho_1 * c1, Z2: v.rho_2 * c2, sI, d1, d2, ac, Nc, Ze, cell, half, bloch, trans, fB, cEff };
}
/** Edges of the first stop band of the lossless crystal below fMax, or null when there is none. */
function firstGap(c0, fMax) {
  const g = f => Math.abs(c0.half(TAU * f)[0]) - 1 - 1e-10, n = 1500; let lo = null, hi = null, fp = fMax / n * 0.5, gp = g(fp), aMax = 0;
  for (let i = 1; i <= n; i++) {
    const f = fMax * (i + 0.5) / (n + 1), gv = g(f);
    if (lo === null && gp <= 0 && gv > 0) lo = rootOr(g, fp, f, f);
    else if (lo !== null && hi === null && gp > 0 && gv <= 0) { hi = rootOr(g, fp, f, f); break; }
    if (lo !== null && hi === null && gv > 0) aMax = Math.max(aMax, Math.log(gv + 1 + Math.sqrt((gv + 1) ** 2 - 1)));
    fp = f; gp = gv;
  }
  if (lo === null) return null;
  return { lo, hi: hi === null ? fMax : hi, open: hi === null, aMax };
}

const phononic = {
  id: 'phononic-crystal-bandgap',
  title: 'Band gap of a one-dimensional phononic crystal',
  module: 2, klass: 'I', domains: ['materials', 'waves'],
  keywords: ['phononic crystal', 'phononic', 'band gap', 'bandgap', 'stop band', 'bloch wave', 'periodic medium', 'superlattice', 'layered medium', 'acoustic metamaterial', 'bragg reflection', 'transfer matrix', 'dispersion', 'multilayer', 'acoustic filter'],
  summary: 'Elastic waves at normal incidence in a periodic stack of two alternating layers: Bloch dispersion relation, edges and width of the first stop band, attenuation per cell and the transmission of a finite stack by transfer matrices.',
  background: [
    'A wave travelling through a periodic medium is partially reflected at every interface. Near frequencies where reflections from successive cells add in phase — the Bragg condition, one half-wavelength per cell — no propagating solution exists: the wave decays exponentially with distance and is reflected. These frequency intervals are stop bands, or band gaps, the acoustic analogue of electronic band gaps in crystals and of photonic stop bands in dielectric mirrors.',
    'For two alternating layers the dispersion relation is known in closed form (Rytov 1956): cos(qa) = cos(k₁d₁)cos(k₂d₂) − ½(Z₁/Z₂ + Z₂/Z₁) sin(k₁d₁) sin(k₂d₂). Whenever the right-hand side exceeds one in magnitude the Bloch wavenumber q is complex. The gap width grows with the contrast in acoustic impedance Z = ρc and vanishes when the impedances are equal. A finite stack of N cells transmits roughly exp(−2N·Im(qa)) of the incident power inside the gap.',
  ],
  phenomena: ['Bragg reflection', 'Bloch waves', 'Evanescent decay inside a stop band', 'Impedance mismatch at interfaces', 'Fabry–Pérot ripple of a finite stack', 'Long-wavelength homogenisation'],
  laws: ['newton2', 'hooke', 'momentum', 'energy'],
  refs: ['Rytov, S. M. (1956). Acoustical properties of a thinly laminated medium. Sov. Phys. Acoust. 2, 68–80.', 'Brillouin, L. (1953). Wave Propagation in Periodic Structures, 2nd ed., Dover.', 'Kushwaha, M. S., Halevi, P., Dobrzynski, L. & Djafari-Rouhani, B. (1993). Acoustic band structure of periodic elastic composites. Phys. Rev. Lett. 71, 2022–2025.', 'Hussein, M. I., Leamy, M. J. & Ruzzene, M. (2014). Dynamics of phononic materials and structures: historical origins, recent progress, and future outlook. Appl. Mech. Rev. 66, 040802.', 'Brekhovskikh, L. M. (1980). Waves in Layered Media, 2nd ed., Academic Press.'],
  inputs: [
    inp('d_1', 'Thickness of layer 1', 'mm', 1, { min: 0.01, max: 100, kind: 'geometry', aliases: ['layer thickness', 'thickness', 'first layer'] }),
    inp('d_2', 'Thickness of layer 2', 'mm', 1, { min: 0.01, max: 100, kind: 'geometry', aliases: ['second layer', 'second thickness'] }),
    inp('rho_1', 'Density of layer 1', 'kg/m^3', 7850, { min: 500, max: 20000, kind: 'fluid', aliases: ['density'], src: 'Steel' }),
    inp('c_1', 'Longitudinal wave speed in layer 1', 'm/s', 5900, { min: 300, max: 12000, kind: 'fluid', aliases: ['wave speed', 'sound speed', 'longitudinal speed'], src: 'Steel' }),
    inp('rho_2', 'Density of layer 2', 'kg/m^3', 1180, { min: 500, max: 20000, kind: 'fluid', aliases: ['second density'], src: 'Epoxy resin' }),
    inp('c_2', 'Longitudinal wave speed in layer 2', 'm/s', 2500, { min: 300, max: 12000, kind: 'fluid', aliases: ['second wave speed'], src: 'Epoxy resin' }),
    inp('ct_1', 'Shear wave speed in layer 1', 'm/s', 3200, { min: 100, max: 7000, kind: 'fluid', aliases: ['shear speed'], src: 'Steel' }),
    inp('ct_2', 'Shear wave speed in layer 2', 'm/s', 1100, { min: 100, max: 7000, kind: 'fluid', src: 'Epoxy resin' }),
    inp('N_c', 'Number of cells in the finite stack', '1', 8, { min: 1, max: 40, kind: 'geometry', aliases: ['cells', 'periods', 'number of cells', 'bilayers'] }),
    inp('eta_l', 'Material loss factor', '1', 0.02, { min: 0, max: 0.3, kind: 'fluid', aliases: ['loss factor', 'damping'] }),
    inp('K_i', 'Interface stiffness per unit area', 'GPa/mm', 100, { min: 0.1, max: 1e5, aliases: ['interface stiffness', 'bond stiffness'] }),
    inp('Z_ext', 'Acoustic impedance of the surrounding medium', 'MPa s/m', 1.48, { min: 1e-4, max: 100, kind: 'environment', aliases: ['surrounding impedance', 'external impedance'], src: 'Water' }),
  ],
  assumptions: [
    asm('lossless', 'Both materials are lossless.', { why: 'Gives real band edges', alt: 'A loss factor makes the wave speeds complex; band edges blur and pass-band transmission falls.' }),
    asm('longitudinal', 'The wave is longitudinal (compressional) at normal incidence.', { why: 'Usual ultrasonic test', alt: 'A shear wave at normal incidence is considered instead, using the shear speeds.' }),
    asm('perfect_bond', 'Layers are perfectly bonded: displacement and stress are continuous.', { why: 'Ideal interfaces', alt: 'Each interface is a thin compliant bond (spring model): the displacement jumps by stress divided by the interface stiffness.' }),
    asm('matched_ends', 'The finite stack sits between half-spaces of material 1.', { why: 'Isolates the effect of periodicity', alt: 'The stack is immersed in a different medium of given acoustic impedance.' }),
  ],
  symbols: { f: ['Frequency', 'Hz'], c_a: ['Wave speed used in layer 1', 'm/s'], c_b: ['Wave speed used in layer 2', 'm/s'], k_1: ['Wavenumber in layer 1', '1/m'], k_2: ['Wavenumber in layer 2', '1/m'], Z_1: ['Acoustic impedance of layer 1', 'Pa s/m'], Z_2: ['Acoustic impedance of layer 2', 'Pa s/m'], q_B: ['Bloch wavenumber', '1/m'], a_c: ['Cell length', 'm'], f_B: ['Bragg frequency', 'Hz'], c_eff: ['Long-wavelength effective speed', 'm/s'], alpha_m: ['Material attenuation coefficient', '1/m'], alpha_B: ['Bloch attenuation per cell', '1'], T_g: ['Power transmission inside the gap', '1'], Z_e: ['Impedance of the end media', 'Pa s/m'] },
  equations: a => [
    eq('ca', 'Wave speed in layer 1', 'c_a', a.longitudinal ? 'c_1' : 'ct_1', { kind: 'closure' }), eq('cb', 'Wave speed in layer 2', 'c_b', a.longitudinal ? 'c_2' : 'ct_2', { kind: 'closure' }),
    eq('k1', 'Wavenumber in layer 1', 'k_1', '2*pi*f/c_a', { kind: 'definition' }), eq('k2', 'Wavenumber in layer 2', 'k_2', '2*pi*f/c_b', { kind: 'definition' }),
    eq('z1', 'Acoustic impedance of layer 1', 'Z_1', 'rho_1*c_a', { kind: 'definition' }), eq('z2', 'Acoustic impedance of layer 2', 'Z_2', 'rho_2*c_b', { kind: 'definition' }),
    eq('ac', 'Cell length', 'a_c', 'd_1 + d_2', { kind: 'definition' }),
    a.perfect_bond
      ? eq('bloch', 'Bloch dispersion relation', 'cos(q_B*a_c)', 'cos(k_1*d_1)*cos(k_2*d_2) - (Z_1/Z_2 + Z_2/Z_1)/2*sin(k_1*d_1)*sin(k_2*d_2)', { kind: 'derived', origin: 'Floquet–Bloch theorem with continuity of displacement and stress (Rytov 1956)', needs: ['perfect_bond'] })
      : eq('bloch', 'Bloch dispersion relation with compliant interfaces', 'cos(q_B*a_c)', 'cos(k_1*d_1)*cos(k_2*d_2) - (Z_1/Z_2 + Z_2/Z_1)/2*sin(k_1*d_1)*sin(k_2*d_2) - 2*pi*f/K_i*(Z_1*sin(k_1*d_1)*cos(k_2*d_2) + Z_2*sin(k_2*d_2)*cos(k_1*d_1)) + (2*pi*f)^2*Z_1*Z_2/(2*K_i^2)*sin(k_1*d_1)*sin(k_2*d_2)', { kind: 'derived', origin: 'Half-trace of the unit-cell transfer matrix with spring interfaces' }),
    eq('fb', 'Bragg frequency', 'f_B', '1/(2*(d_1/c_a + d_2/c_b))', { kind: 'derived', origin: 'Half a wavelength of phase per cell' }),
    a.perfect_bond
      ? eq('ceff', 'Long-wavelength effective speed', 'c_eff', 'a_c/sqrt((d_1/c_a)^2 + (d_2/c_b)^2 + (Z_1/Z_2 + Z_2/Z_1)*d_1*d_2/(c_a*c_b))', { kind: 'derived', origin: 'Small-argument expansion of the dispersion relation' })
      : eq('ceff', 'Long-wavelength effective speed', 'c_eff', 'sqrt(a_c^2/((rho_1*d_1 + rho_2*d_2)*(d_1/(rho_1*c_a^2) + d_2/(rho_2*c_b^2) + 2/K_i)))', { kind: 'derived', origin: 'Series compliance and mean density' }),
    ...(a.lossless ? [] : [eq('loss', 'Material attenuation in layer 1', 'alpha_m', 'pi*f*eta_l/c_a', { kind: 'closure', origin: 'Complex modulus with loss factor η' })]),
    eq('ze', 'End media', 'Z_e', a.matched_ends ? 'Z_1' : 'Z_ext', { kind: 'boundary' }),
    eq('tg', 'Transmission of a finite stack inside the gap', 'T_g', 'exp(-2*N_c*alpha_B)', { kind: 'derived', origin: 'Evanescent Bloch wave across N cells', note: 'Order-of-magnitude estimate; the transfer-matrix result includes the end mismatch' }),
  ],
  derivation: a => [
    { text: 'In each layer the displacement is a sum of forward and backward waves. Displacement u and stress σ = ρc² ∂u/∂x at the two faces of a layer of thickness d are related by a 2×2 transfer matrix.', tex: '\\begin{pmatrix}u\\\\ \\sigma\\end{pmatrix}_{d} = \\begin{pmatrix}\\cos kd & \\dfrac{\\sin kd}{\\omega Z}\\\\ -\\omega Z\\sin kd & \\cos kd\\end{pmatrix}\\begin{pmatrix}u\\\\ \\sigma\\end{pmatrix}_{0}' },
    { text: a.perfect_bond ? 'With perfect bonding u and σ are continuous, so the matrix of one cell is the product of the two layer matrices.' : 'A compliant bond adds a displacement jump σ/K at each interface, represented by a further unit-determinant matrix.', tex: a.perfect_bond ? '\\mathbf{M} = \\mathbf{M}_2\\mathbf{M}_1' : '\\mathbf{M} = \\mathbf{S}\\mathbf{M}_2\\mathbf{S}\\mathbf{M}_1,\\quad \\mathbf{S}=\\begin{pmatrix}1 & 1/K\\\\ 0 & 1\\end{pmatrix}' },
    { text: 'Bloch\'s theorem requires the state to change only by a phase factor across one cell, so exp(±iqa) are the eigenvalues of M. Because det M = 1 their sum is the trace.', tex: '\\cos qa = \\tfrac12\\,\\mathrm{tr}\\,\\mathbf{M} = \\cos k_1d_1\\cos k_2d_2 - \\tfrac12\\left(\\frac{Z_1}{Z_2}+\\frac{Z_2}{Z_1}\\right)\\sin k_1d_1\\sin k_2d_2' },
    { text: 'Where the right-hand side lies outside [−1, 1] the Bloch wavenumber acquires an imaginary part: the wave is evanescent. The first such interval is centred near the Bragg frequency.', tex: '|\\cos qa|>1\\ \\Rightarrow\\ \\mathrm{Im}(qa) = \\cosh^{-1}|\\cos qa|,\\qquad f_B = \\frac{1}{2\\,(d_1/c_1+d_2/c_2)}' },
    { text: 'For N cells the total matrix is Mᴺ. Matching to incident, reflected and transmitted waves in the end media gives the transmission coefficient.', tex: 'T = \\frac{Z_b}{Z_a}|t|^2,\\qquad R + T = 1\\ \\text{(lossless)}' },
    { text: 'At low frequency, expanding the cosines recovers a homogeneous medium with the mean density and the series (Reuss) stiffness.', tex: 'c_{eff}^2 = \\frac{a^2}{\\left(\\rho_1d_1+\\rho_2d_2\\right)\\left(\\dfrac{d_1}{\\rho_1c_1^2}+\\dfrac{d_2}{\\rho_2c_2^2}\\right)}' },
  ],
  solve(v, a) {
    const c = pcCore(v, a), c0 = a.lossless ? c : pcCore(v, a, true), fMax = 2.6 * c.fB, warnings = [];
    const gap = firstGap(c0, fMax), nf = 480, fs = N.linspace(fMax / nf, fMax, nf);
    const q = fs.map(f => c.bloch(TAU * f)), tr = fs.map(f => c.trans(TAU * f));
    const fc = gap ? (gap.lo + gap.hi) / 2 : c.fB, qc = c0.bloch(TAU * fc), tc = c.trans(TAU * fc);
    let cons = 0, det = 0;
    if (a.lossless) tr.forEach(t => { cons = Math.max(cons, Math.abs(t.R + t.T - 1)); });
    [0.3, 0.9, 1.7].forEach(x => { const m = c0.cell(TAU * x * c.fB), d = csub(cmul(m[0][0], m[1][1]), cmul(m[0][1], m[1][0])); det = Math.max(det, Math.hypot(d[0] - 1, d[1])); });
    if (!gap) warnings.push('No stop band was found below 2.6 times the Bragg frequency: the two layers are acoustically matched, so the medium is effectively homogeneous.');
    else if (gap.open) warnings.push('The first stop band extends beyond the plotted frequency range; its upper edge is truncated.');
    if (!a.lossless && v.eta_l > 0.1) warnings.push('With a loss factor above 0.1 the band edges are heavily blurred; the lossless edges are reported.');
    const kHz = 1e-3, unit = 'kHz';
    const und = { text: 'None — no stop band' };
    return {
      scalars: [
        scalar('Z_1', 'Acoustic impedance of layer 1', c.Z1, 'Pa s/m', { show: 'MPa s/m' }), scalar('Z_2', 'Acoustic impedance of layer 2', c.Z2, 'Pa s/m', { show: 'MPa s/m' }),
        scalar('r_Z', 'Impedance ratio Z₁/Z₂', c.Z1 / c.Z2, '1'), scalar('R_int', 'Amplitude reflection at a single interface', (c.Z2 - c.Z1) / (c.Z2 + c.Z1), '1'),
        scalar('a_c', 'Cell length', c.ac, 'm', { show: 'mm' }), scalar('f_B', 'Bragg frequency', c.fB, 'Hz', { show: unit }),
        scalar('f_lo', 'Lower edge of the first stop band', gap ? gap.lo : NaN, 'Hz', gap ? { show: unit } : und), scalar('f_hi', 'Upper edge of the first stop band', gap ? gap.hi : NaN, 'Hz', gap ? { show: unit } : und),
        scalar('gap_w', 'Width of the first stop band', gap ? gap.hi - gap.lo : 0, 'Hz', { show: unit }), scalar('gap_rel', 'Relative gap width Δf/f_centre', gap ? (gap.hi - gap.lo) / fc : 0, '1', { show: '%' }),
        scalar('alpha_B', 'Largest Bloch attenuation in the gap', gap ? gap.aMax : 0, '1', { note: 'nepers per cell' }), scalar('att_dB', 'Largest attenuation per cell', gap ? 8.686 * gap.aMax : 0, 'dB'),
        scalar('T_c', `Power transmission of ${c.Nc} cells at the gap centre`, 10 * Math.log10(Math.max(tc.T, 1e-300)), 'dB'),
        scalar('T_est', 'Estimate exp(−2N·Im qa) at the gap centre', -8.686 * 2 * c.Nc * qc[1] / 2, 'dB'),
        scalar('c_eff', 'Long-wavelength effective wave speed', c.cEff, 'm/s'),
        scalar('lam_B', 'Wavelength in layer 1 at the Bragg frequency', c.c1 / c.fB, 'm', { show: 'mm' }),
      ],
      series: [
        line('transmission', `Power transmission through ${c.Nc} cells`, 'Frequency', unit, fs.map(f => f * kHz), [{ label: 'Transfer-matrix result', data: tr.map(t => 10 * Math.log10(Math.max(t.T, 1e-30))) }, { label: 'Infinite-crystal estimate', data: q.map(z => -8.686 * c.Nc * z[1]), dash: true }], 'Transmission', 'dB'),
        line('dispersion', 'Bloch dispersion', 'Frequency', unit, fs.map(f => f * kHz), [{ label: 'Re(qa)/π — phase per cell', data: q.map(z => z[0] / Math.PI) }, { label: 'Im(qa) — attenuation per cell (Np)', data: q.map(z => z[1]), dash: true }], 'Bloch wavenumber × cell length', '–', { note: 'Propagation where Im(qa) = 0; stop band where Re(qa) is pinned at 0 or π' }),
        line('reflection', `Power reflection from ${c.Nc} cells`, 'Frequency', unit, fs.map(f => f * kHz), [{ label: 'Reflection', data: tr.map(t => t.R) }], 'Reflection coefficient', '–'),
      ],
      checks: [
        check('Energy conservation R + T = 1', cons, 1e-8, a.lossless ? 'Largest deviation over the frequency sweep' : 'Not applicable: absorption in the layers'),
        check('Unit determinant of the cell matrix (reciprocity)', det, 1e-9, 'Lossless cell matrix at three frequencies'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], hom = { ...v, rho_2: v.rho_1, c_2: v.c_1, ct_2: v.ct_1 }, id = { ...a, lossless: true, perfect_bond: true, matched_ends: true };
    const h = pcCore(hom, id), gh = firstGap(h, 2.6 * h.fB);
    out.push(bench('Homogeneous limit: no stop band', gh ? gh.hi - gh.lo : 0, 0, 'Identical layers form a uniform medium', 1e-9));
    out.push(bench('Homogeneous limit: full transmission', h.trans(TAU * 1.03 * h.fB).T, 1, 'T = 1 at every frequency', 1e-9));
    const c = pcCore(v, a, true), w = TAU * 0.37 * c.fB, k1 = w / c.c1, k2 = w / c.c2, s1 = Math.sin(k1 * c.d1), s2 = Math.sin(k2 * c.d2), c1 = Math.cos(k1 * c.d1), c2 = Math.cos(k2 * c.d2), z1 = w * c.Z1, z2 = w * c.Z2;
    out.push(bench('Half-trace of the cell matrix against the closed-form dispersion relation', c.half(w)[0] + 2, c1 * c2 - 0.5 * (z1 / z2 + z2 / z1) * s1 * s2 - c.sI * (z1 * s1 * c2 + z2 * s2 * c1) + 0.5 * c.sI ** 2 * z1 * z2 * s1 * s2 + 2, a.perfect_bond ? 'Rytov (1956), offset by 2' : 'Rytov relation extended with spring interfaces, offset by 2', 1e-9));
    const wl = TAU * c.fB / 300;
    out.push(bench('Low-frequency Bloch speed against the homogenised value', wl * c.ac / c.bloch(wl)[0], c.cEff, 'Mean density with series stiffness', 1e-3));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const n = Math.min(Math.max(1, Math.round(v.N_c)), 8), w = 400 / n, w1 = w * v.d_1 / (v.d_1 + v.d_2);
    return svg(`
      ${Array.from({ length: n }, (_, i) => S.rect(120 + i * w, 110, w1, 120, 'd-body', 0) + S.rect(120 + i * w + w1, 110, w - w1, 120, 'd-liquid', 0)).join('')}
      ${S.arrow(30, 150, 112, 150)} ${S.text(70, 140, 'incident')} ${S.arrow(112, 192, 30, 192, 'd-arrow d-heat')} ${S.text(70, 212, 'reflected')}
      ${S.arrow(528, 170, 610, 170)} ${S.text(570, 160, 'transmitted')}
      ${S.dim(120, 260, 120 + w, 260, `a = ${lab((v.d_1 + v.d_2) * 1e3, 'mm')}`)}
      ${S.text(320, 96, `${Math.round(v.N_c)} cells${n < Math.round(v.N_c) ? ' (8 drawn)' : ''}`)}
      ${S.text(320, 310, `layer 1: ${lab(v.d_1 * 1e3, 'mm')}, Z = ${lab(v.rho_1 * (a.longitudinal ? v.c_1 : v.ct_1) / 1e6, 'MRayl')}    layer 2: ${lab(v.d_2 * 1e3, 'mm')}, Z = ${lab(v.rho_2 * (a.longitudinal ? v.c_2 : v.ct_2) / 1e6, 'MRayl')}`, 'd-text d-small')}
      ${S.text(320, 336, a.matched_ends ? 'between half-spaces of material 1' : 'immersed in a surrounding medium', 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the ultrasonic transmission spectrum of a bonded multilayer stack and compare the stop-band edges and depth with the transfer-matrix prediction.',
    apparatus: ['Stack of alternating metal and polymer plates bonded with thin adhesive layers, faces ground parallel', 'Pair of broadband ultrasonic transducers (longitudinal or shear) with couplant or water path', 'Reference block of material 1 with the same total thickness'],
    instruments: [{ name: 'Pulser–receiver and digitising oscilloscope', measures: 'Transmitted waveform', range: '0.1–20 MHz', resolution: '12 bit, 100 MS/s' }, { name: 'Micrometer', measures: 'Layer thicknesses', range: '0–25 mm', resolution: '±2 µm' }, { name: 'Balance and time-of-flight measurement on single plates', measures: 'Density and wave speed of each material', range: '—', resolution: '±0.2 %' }],
    procedure: ['Measure thickness, density and wave speed of each plate before assembly.', 'Record the transmitted pulse through the reference block and through the stack.', 'Divide the spectra to obtain the transmission coefficient against frequency.', 'Repeat for stacks of 2, 4 and 8 cells, and with shear transducers.'],
    controls: ['Reference block to remove the transducer response', 'A stack of identical plates bonded in the same way, to separate bond-line effects from periodicity'],
    signatures: ['A transmission notch centred near the Bragg frequency', 'Notch depth in decibels proportional to the number of cells', 'N − 1 ripples in each pass band for N cells', 'Stop band at lower frequency for shear than for longitudinal waves'],
    safety: ['Electrical safety of the high-voltage pulser', 'Handling precautions for uncured epoxy'],
  },
  falsify: ['A stop band between two layers of equal acoustic impedance with perfect bonds.', 'A stop-band depth that does not scale with the number of cells.', 'Band edges that disagree with the dispersion relation by more than the uncertainty in thickness and wave speed.', 'R + T differing from one in a lossless stack.'],
  alternatives: [{ name: 'Locally resonant metamaterials', text: 'Gaps opened by resonators embedded in each cell appear far below the Bragg frequency and do not rely on periodicity.' }, { name: 'Oblique incidence', text: 'Away from normal incidence longitudinal and shear waves couple at each interface and a 4×4 transfer matrix is needed.' }, { name: 'Two- and three-dimensional crystals', text: 'Complete gaps for all directions require periodicity in more than one dimension and are found by plane-wave expansion or finite elements.' }, { name: 'Disorder', text: 'Random thickness variation localises waves and fills in the pass bands without a sharp gap.' }],
  hazards: [{ hazard: 'Delamination', cause: 'Thermal mismatch or high-amplitude ultrasound at bond lines', mitigation: 'Controlled cure and drive levels' }],
  standards: ['ASTM E494 (measuring ultrasonic velocity in materials)', 'ASTM E664 (measurement of the apparent attenuation of longitudinal ultrasonic waves by immersion method)', 'ISO 16810 (non-destructive testing — ultrasonic testing — general principles)'],
  limits: 'Plane waves at normal incidence in a laterally infinite stack of homogeneous, isotropic, linear layers. Frequency-independent loss factor. No mode conversion, no lateral resonances, no diffraction.',
  numerics: { method: 'Complex 2×2 transfer matrices with exponentiation by squaring; stop-band edges by bracketed root finding on the half-trace', stability: 'Unconditionally stable; inside deep gaps matrix elements grow as exp(N·Im qa)' },
  optimise: { objective: 'gap_rel', sense: 'max', vars: ['d_1'], note: 'The gap is widest near the quarter-wave condition d₁/c₁ = d₂/c₂.' },
  inverse: { series: 'transmission', fit: ['d_1'] },
  extensions: ['Oblique incidence with mode conversion', 'Defect layer and localised cavity mode', 'Graded and quasi-periodic stacks', 'Thermal phonon transport in superlattices'],
};

// ------------------------------------------------------------------ effective-medium theory for a two-phase composite
const cR = x => [x, 0];
/** Maxwell Garnett: inclusions (property pi, fraction f, depolarisation factor L) in a host ph. Complex pairs. */
const mgMix = (ph, pi, f, L) => cadd(ph, cdiv(cmul(cR(f), cmul(ph, csub(pi, ph))), cadd(ph, cmul(cR(L * (1 - f)), csub(pi, ph)))));
/** Symmetric Bruggeman mixture; the passive root (non-negative real part, non-positive imaginary part) is selected. */
function brMix(pm, pi, f, L) {
  const b = cadd(cmul(cR(f), csub(cmul(cR(1 - L), pi), cmul(cR(L), pm))), cmul(cR(1 - f), csub(cmul(cR(1 - L), pm), cmul(cR(L), pi))));
  const pp = cmul(pi, pm), s = csqrt(cadd(cmul(b, b), cmul(cR(4 * (1 - L) * L), pp)));
  let r = b[0] >= 0 ? cdiv(cadd(b, s), cR(2 * (1 - L))) : cdiv(cmul(cR(2 * L), pp), csub(s, b));
  if (r[0] < 0 || r[1] > 1e-12 * Math.abs(r[0])) { const alt = cdiv(cmul(cR(-L / (1 - L)), pp), r); if (alt[0] >= 0) r = alt; }
  return r;
}
function emtCore(v, a) {
  const L = a.spheres ? 1 / 3 : v.L_d;
  const coat = (core, shell) => (a.no_interphase ? core : cmul(shell, cdiv(cadd(cadd(core, cmul(cR(2), shell)), cmul(cR(2 * v.beta_c), csub(core, shell))), csub(cadd(core, cmul(cR(2), shell)), cmul(cR(v.beta_c), csub(core, shell))))));
  const mg = (pm, pi, f) => (a.mg_host ? mgMix(pm, pi, f, L) : mgMix(pi, pm, 1 - f, L));
  const br = (pm, pi, f) => brMix(pm, pi, f, L);
  const eI = coat(cR(v.eps_i), cR(v.eps_sh))[0], sI = coat(cR(v.sigma_i), cR(v.sigma_m))[0];
  /** Complex relative permittivities of matrix and (equivalent) inclusion at frequency f. */
  const cplx = f => { const w = TAU * f * EPS0; return { m: [v.eps_m, -v.sigma_m / w], i: coat([v.eps_i, -v.sigma_i / w], [v.eps_sh, -v.sigma_m / w]) }; };
  const hs = (pm, pi, f) => { const lo = Math.min(pm, pi), hi = Math.max(pm, pi), fl = pm <= pi ? 1 - f : f; // fl: fraction of the low phase
    return pm === pi ? [pm, pm] : [lo + (1 - fl) / (1 / (hi - lo) + fl / (3 * lo)), hi + fl / (1 / (lo - hi) + (1 - fl) / (3 * hi))]; };
  const wiener = (pm, pi, f) => [1 / (f / pi + (1 - f) / pm), f * pi + (1 - f) * pm];
  return { L, mg, br, eI, sI, cplx, hs, wiener };
}

const effectiveMedium = {
  id: 'effective-medium-composite',
  title: 'Effective permittivity and conductivity of a filled composite',
  module: 2, klass: 'I', domains: ['materials', 'electromagnetic'],
  keywords: ['effective medium', 'maxwell garnett', 'bruggeman', 'composite', 'filler fraction', 'effective permittivity', 'effective conductivity', 'mixing rule', 'hashin-shtrikman', 'percolation', 'dielectric composite', 'nanocomposite', 'filled polymer', 'homogenisation', 'mixture'],
  summary: 'Maxwell Garnett and Bruggeman estimates of the effective permittivity and conductivity of a matrix filled with inclusions, checked against the Hashin–Shtrikman and Wiener bounds, with options for aligned spheroids, coated particles, phase inversion and frequency-dependent (Maxwell–Wagner) response.',
  background: [
    'A composite whose inclusions are much smaller than the wavelength and the sample responds to a uniform field like a homogeneous material with an effective property. The Maxwell Garnett formula treats isolated inclusions in a continuous host and is exact to first order in volume fraction. The Bruggeman formula treats both phases symmetrically, each embedded in the effective medium itself, and predicts a percolation threshold at which a conducting filler first forms a connected path.',
    'Without knowledge of the microstructure the effective property cannot be fixed, only bounded. The Wiener bounds (series and parallel layers) hold for any two-phase material; for a statistically isotropic one the tighter Hashin–Shtrikman bounds apply, and the Maxwell Garnett result coincides with one of them. Permittivity, electrical and thermal conductivity, diffusivity and magnetic permeability all obey the same mathematics. When the phases differ in both permittivity and conductivity, charge accumulates at their interfaces and the effective permittivity becomes frequency dependent (Maxwell–Wagner polarisation).',
  ],
  phenomena: ['Polarisation of inclusions', 'Field concentration in the matrix', 'Percolation of a conducting phase', 'Interfacial (Maxwell–Wagner) polarisation', 'Shape anisotropy through depolarisation factors'],
  laws: ['maxwell', 'charge', 'ohm'],
  refs: ['Maxwell Garnett, J. C. (1904). Colours in metal glasses and in metallic films. Phil. Trans. R. Soc. Lond. A 203, 385–420.', 'Bruggeman, D. A. G. (1935). Berechnung verschiedener physikalischer Konstanten von heterogenen Substanzen. Ann. Phys. 416, 636–664.', 'Hashin, Z. & Shtrikman, S. (1962). A variational approach to the theory of the effective magnetic permeability of multiphase materials. J. Appl. Phys. 33, 3125–3131.', 'Sihvola, A. (1999). Electromagnetic Mixing Formulas and Applications, IEE.', 'Torquato, S. (2002). Random Heterogeneous Materials: Microstructure and Macroscopic Properties, Springer.', 'Landauer, R. (1978). Electrical conductivity in inhomogeneous media. AIP Conf. Proc. 40, 2–45.'],
  inputs: [
    inp('eps_m', 'Relative permittivity of the matrix', '1', 3, { min: 1, max: 100, kind: 'fluid', aliases: ['matrix permittivity', 'host permittivity', 'polymer permittivity'], src: 'Typical epoxy or polyimide' }),
    inp('eps_i', 'Relative permittivity of the filler', '1', 100, { min: 1, max: 1e4, kind: 'fluid', aliases: ['filler permittivity', 'inclusion permittivity', 'particle permittivity'] }),
    inp('phi', 'Filler volume fraction', '1', 0.2, { min: 0, max: 1, aliases: ['volume fraction', 'filler fraction', 'loading', 'fraction'] }),
    inp('sigma_m', 'Conductivity of the matrix', 'S/m', 1e-10, { min: 1e-16, max: 1e-2, kind: 'fluid', aliases: ['matrix conductivity'] }),
    inp('sigma_i', 'Conductivity of the filler', 'S/m', 1e-4, { min: 1e-16, max: 1e8, kind: 'fluid', aliases: ['filler conductivity', 'inclusion conductivity'] }),
    inp('L_d', 'Depolarisation factor of the inclusions along the field', '1', 0.1, { min: 0.02, max: 0.9, kind: 'geometry', aliases: ['depolarisation factor', 'depolarization factor', 'shape factor'], src: '1/3 for spheres; smaller for needles along the field, larger for discs across it' }),
    inp('f_e', 'Frequency for the complex response', 'Hz', 1000, { min: 1e-3, max: 1e9, aliases: ['frequency'] }),
    inp('beta_c', 'Core volume fraction of a coated particle', '1', 0.8, { min: 0.1, max: 0.99, kind: 'geometry', aliases: ['core fraction'] }),
    inp('eps_sh', 'Relative permittivity of the coating', '1', 5, { min: 1, max: 1000, kind: 'fluid', aliases: ['shell permittivity', 'coating permittivity'] }),
  ],
  assumptions: [
    asm('spheres', 'The inclusions are spheres (depolarisation factor 1/3), so the composite is isotropic.', { why: 'Simplest shape', alt: 'The inclusions are aligned spheroids with depolarisation factor L along the field; the result is the property along that axis.' }),
    asm('mg_host', 'The matrix is the continuous phase in the Maxwell Garnett estimate.', { why: 'Dilute, well-dispersed filler', alt: 'Phase inversion: the filler material is the continuous phase and the matrix forms the inclusions.' }),
    asm('static', 'The response is static: permittivity and conductivity are treated independently as real quantities.', { why: 'Zero-frequency limit', alt: 'A complex permittivity ε − iσ/(ωε₀) is used for each phase at a given frequency, giving interfacial polarisation and loss.' }),
    asm('no_interphase', 'The particles are bare.', { why: 'No surface treatment', alt: 'Each particle carries a concentric coating; it is replaced by the equivalent homogeneous sphere.' }),
  ],
  symbols: { alpha_p: ['Polarisability factor of an inclusion', '1'], eps_q: ['Equivalent permittivity of a coated particle', '1'], eps_MG: ['Maxwell Garnett effective permittivity', '1'], eps_BR: ['Bruggeman effective permittivity', '1'], eps_HSL: ['Hashin–Shtrikman lower bound', '1'], eps_HSU: ['Hashin–Shtrikman upper bound', '1'], eps_Wlo: ['Wiener lower bound (series)', '1'], eps_Whi: ['Wiener upper bound (parallel)', '1'], sigma_MG: ['Maxwell Garnett effective conductivity', 'S/m'], tau_MW: ['Maxwell–Wagner relaxation time', 's'], tan_m: ['Conduction loss tangent of the matrix', '1'], L_s: ['Depolarisation factor', '1'] },
  equations: a => {
    const ei = a.no_interphase ? 'eps_i' : 'eps_q', L = a.spheres ? '1/3' : 'L_d';
    const mg = (h, i, f) => `${h} + ${f}*${h}*(${i} - ${h})/(${h} + ${L}*(1 - ${f})*(${i} - ${h}))`;
    return [
      ...(a.no_interphase ? [] : [eq('coat', 'Equivalent permittivity of a coated sphere', 'eps_q', 'eps_sh*((eps_i + 2*eps_sh) + 2*beta_c*(eps_i - eps_sh))/((eps_i + 2*eps_sh) - beta_c*(eps_i - eps_sh))', { kind: 'derived', origin: 'Exact field solution for concentric spheres' })]),
      eq('ap', 'Polarisability factor', 'alpha_p', a.spheres ? `(${ei} - eps_m)/(${ei} + 2*eps_m)` : `(${ei} - eps_m)/(3*(eps_m + L_d*(${ei} - eps_m)))`, { kind: 'derived', origin: 'Field inside an isolated ellipsoid in a uniform field' }),
      a.mg_host
        ? eq('mg', 'Maxwell Garnett mixing formula', 'eps_MG', mg('eps_m', ei, 'phi'), { kind: 'derived', origin: 'Clausius–Mossotti (Lorentz) local field', needs: ['mg_host'] })
        : eq('mg', 'Maxwell Garnett formula with phases inverted', 'eps_MG', mg(ei, 'eps_m', '(1 - phi)'), { kind: 'derived', origin: 'Clausius–Mossotti local field with the filler as host' }),
      eq('br', 'Bruggeman self-consistency condition', `phi*(${ei} - eps_BR)/(eps_BR + ${L}*(${ei} - eps_BR)) + (1 - phi)*(eps_m - eps_BR)/(eps_BR + ${L}*(eps_m - eps_BR))`, '0', { kind: 'closure', origin: 'Mean polarisation of both phases embedded in the effective medium vanishes' }),
      ...(a.spheres ? [
        eq('hsl', 'Hashin–Shtrikman bound with the matrix as host', 'eps_HSL', `eps_m + phi/(1/(${ei} - eps_m) + (1 - phi)/(3*eps_m))`, { kind: 'law', origin: 'Variational bound for isotropic two-phase media', needs: ['spheres'] }),
        eq('hsu', 'Hashin–Shtrikman bound with the filler as host', 'eps_HSU', `${ei} + (1 - phi)/(1/(eps_m - ${ei}) + phi/(3*${ei}))`, { kind: 'law', origin: 'Variational bound for isotropic two-phase media', needs: ['spheres'] })] : []),
      eq('wlo', 'Wiener bound, layers in series', 'eps_Wlo', `1/(phi/${ei} + (1 - phi)/eps_m)`, { kind: 'law', origin: 'Uniform flux density' }),
      eq('whi', 'Wiener bound, layers in parallel', 'eps_Whi', `phi*${ei} + (1 - phi)*eps_m`, { kind: 'law', origin: 'Uniform field' }),
      eq('smg', 'Maxwell Garnett effective conductivity', 'sigma_MG', a.mg_host ? mg('sigma_m', 'sigma_i', 'phi') : mg('sigma_i', 'sigma_m', '(1 - phi)'), { kind: 'derived', origin: 'Same mathematics with conductivity in place of permittivity' }),
      ...(a.static ? [] : [
        eq('mw', 'Maxwell–Wagner relaxation time', 'tau_MW', `eps_0*(eps_m + ${L}*(1 - phi)*(${ei} - eps_m))/(sigma_m + ${L}*(1 - phi)*(sigma_i - sigma_m))`, { kind: 'derived', origin: 'Pole of the Maxwell Garnett formula with complex permittivities' }),
        eq('tm', 'Conduction loss tangent of the matrix', 'tan_m', 'sigma_m/(2*pi*f_e*eps_0*eps_m)', { kind: 'definition' })]),
    ];
  },
  derivation: a => [
    { text: 'An isolated ellipsoid in a uniform field E₀ is uniformly polarised; the field inside it is reduced by the depolarisation factor L (1/3 for a sphere).', tex: 'E_{in} = \\frac{\\varepsilon_m}{\\varepsilon_m + L(\\varepsilon_i-\\varepsilon_m)}\\,E_0' },
    { text: 'Summing the dipole moments of many such inclusions, each exposed to the Lorentz local field of the others, gives the Maxwell Garnett formula.', tex: '\\varepsilon_{MG} = \\varepsilon_m + \\frac{\\phi\\,\\varepsilon_m(\\varepsilon_i-\\varepsilon_m)}{\\varepsilon_m + L(1-\\phi)(\\varepsilon_i-\\varepsilon_m)}' },
    { text: 'Bruggeman instead embeds a grain of each phase in the unknown effective medium and requires the average polarisation to vanish.', tex: '\\phi\\,\\frac{\\varepsilon_i-\\varepsilon}{\\varepsilon+L(\\varepsilon_i-\\varepsilon)} + (1-\\phi)\\,\\frac{\\varepsilon_m-\\varepsilon}{\\varepsilon+L(\\varepsilon_m-\\varepsilon)} = 0' },
    { text: 'This is a quadratic for ε. With an insulating matrix its conducting root is zero until the filler fraction reaches the depolarisation factor: a percolation threshold of one-third for spheres.', tex: '\\sigma_{BR} = \\sigma_i\\,\\frac{\\phi-L}{1-L}\\quad(\\phi>L,\\ \\sigma_m\\to0)' },
    { text: 'Variational principles bound the effective property of any isotropic two-phase material. The bounds are attained by assemblages of coated spheres, and coincide with the Maxwell Garnett formula taken with each phase in turn as host.', tex: '\\varepsilon_m + \\frac{\\phi}{\\dfrac{1}{\\varepsilon_i-\\varepsilon_m}+\\dfrac{1-\\phi}{3\\varepsilon_m}} \\ \\le\\ \\varepsilon_{eff}\\ \\le\\ \\varepsilon_i + \\frac{1-\\phi}{\\dfrac{1}{\\varepsilon_m-\\varepsilon_i}+\\dfrac{\\phi}{3\\varepsilon_i}}' },
    ...(a.static ? [] : [{ text: 'At angular frequency ω each phase has a complex permittivity. Inserting these into the mixing formula yields a Debye-type relaxation caused by charge accumulating at the interfaces.', tex: '\\varepsilon^*_k = \\varepsilon_k - \\frac{i\\sigma_k}{\\omega\\varepsilon_0},\\qquad \\tau_{MW} = \\varepsilon_0\\frac{\\varepsilon_m + L(1-\\phi)(\\varepsilon_i-\\varepsilon_m)}{\\sigma_m + L(1-\\phi)(\\sigma_i-\\sigma_m)}' }]),
  ],
  solve(v, a) {
    const c = emtCore(v, a), f = v.phi, em = v.eps_m, ei = c.eI, sm = v.sigma_m, si = c.sI, warnings = [];
    const eMG = c.mg(cR(em), cR(ei), f)[0], eBR = c.br(cR(em), cR(ei), f)[0], sMG = c.mg(cR(sm), cR(si), f)[0], sBR = c.br(cR(sm), cR(si), f)[0];
    const hsE = c.hs(em, ei, f), hsS = c.hs(sm, si, f), wE = c.wiener(em, ei, f), wS = c.wiener(sm, si, f);
    const viol = (x, b) => Math.max(0, (b[0] - x) / b[0], (x - b[1]) / b[1]);
    const hsV = a.static && a.spheres ? Math.max(viol(eMG, hsE), viol(eBR, hsE), viol(sMG, hsS), viol(sBR, hsS)) : 0;
    const wV = a.static ? Math.max(viol(eMG, wE), viol(eBR, wE), viol(sMG, wS), viol(sBR, wS)) : 0;
    if (a.mg_host && f > 0.3) warnings.push('The Maxwell Garnett formula assumes well-separated inclusions; above about 30 % loading the Bruggeman estimate and the bounds are a better guide.');
    if (Math.max(si / sm, sm / si) > 1e3 && Math.abs(f - c.L) < 0.1) warnings.push('The loading is near the Bruggeman percolation threshold, where the conductivity is extremely sensitive to microstructure; treat the estimates as order-of-magnitude.');
    if (!a.spheres) warnings.push('Aligned spheroids make the composite anisotropic: the Hashin–Shtrikman bounds for isotropic media do not apply, only the Wiener bounds.');
    const fin = ei / em / (1 + c.L * (ei / em - 1));
    const tauMW = EPS0 * (em + c.L * (1 - f) * (ei - em)) / (sm + c.L * (1 - f) * (si - sm));
    const ps = N.linspace(0, 1, 101);
    const scalars = [
      scalar('eps_MG', 'Effective permittivity, Maxwell Garnett', eMG, '1'), scalar('eps_BR', 'Effective permittivity, Bruggeman', eBR, '1'),
      scalar('eps_HSL', 'Hashin–Shtrikman lower bound on permittivity', hsE[0], '1'), scalar('eps_HSU', 'Hashin–Shtrikman upper bound on permittivity', hsE[1], '1'),
      scalar('eps_Wlo', 'Wiener lower bound (series)', wE[0], '1'), scalar('eps_Whi', 'Wiener upper bound (parallel)', wE[1], '1'),
      scalar('sigma_MG', 'Effective conductivity, Maxwell Garnett', sMG, 'S/m'), scalar('sigma_BR', 'Effective conductivity, Bruggeman', sBR, 'S/m'),
      scalar('sigma_HSL', 'Hashin–Shtrikman lower bound on conductivity', hsS[0], 'S/m'), scalar('sigma_HSU', 'Hashin–Shtrikman upper bound on conductivity', hsS[1], 'S/m'),
      scalar('alpha_p', 'Polarisability factor of an inclusion', (ei - em) / (3 * (em + c.L * (ei - em))), '1'),
      scalar('E_in', 'Field inside an inclusion / applied field', 1 / (1 + c.L * (ei / em - 1)), '1'),
      scalar('FE', 'Largest field in the matrix at an inclusion / applied field', Math.max(fin, 1 / (1 + c.L * (ei / em - 1))), '1', { note: 'Dilute limit; governs breakdown initiation' }),
      scalar('phi_c', 'Bruggeman percolation threshold', c.L, '1'),
      scalar('eps_q', 'Equivalent permittivity of the particle', ei, '1'),
    ];
    const series = [
      line('eps-phi', 'Effective permittivity against filler fraction', 'Filler volume fraction', '–', ps, [{ label: 'Maxwell Garnett', data: ps.map(p => c.mg(cR(em), cR(ei), p)[0]) }, { label: 'Bruggeman', data: ps.map(p => c.br(cR(em), cR(ei), p)[0]) }, { label: 'Hashin–Shtrikman lower', data: ps.map(p => c.hs(em, ei, p)[0]), dash: true }, { label: 'Hashin–Shtrikman upper', data: ps.map(p => c.hs(em, ei, p)[1]), dash: true }, { label: 'Wiener series', data: ps.map(p => c.wiener(em, ei, p)[0]), dash: true }, { label: 'Wiener parallel', data: ps.map(p => c.wiener(em, ei, p)[1]), dash: true }], 'Relative permittivity', '–', { logy: Math.max(ei / em, em / ei) > 30 }),
      line('sigma-phi', 'Effective conductivity against filler fraction', 'Filler volume fraction', '–', ps, [{ label: 'Maxwell Garnett', data: ps.map(p => c.mg(cR(sm), cR(si), p)[0]) }, { label: 'Bruggeman', data: ps.map(p => c.br(cR(sm), cR(si), p)[0]) }, { label: 'Hashin–Shtrikman lower', data: ps.map(p => c.hs(sm, si, p)[0]), dash: true }, { label: 'Hashin–Shtrikman upper', data: ps.map(p => c.hs(sm, si, p)[1]), dash: true }], 'Conductivity', 'S/m', { logy: true }),
    ];
    if (!a.static) {
      const z = c.cplx(v.f_e), zm = c.mg(z.m, z.i, f), zb = c.br(z.m, z.i, f);
      const fs = N.logspace(Math.min(1e-2, 0.01 / (TAU * tauMW)), Math.max(1e6, 100 / (TAU * tauMW)), 121), zs = fs.map(q => { const y = c.cplx(q); return [c.mg(y.m, y.i, f), c.br(y.m, y.i, f)]; });
      scalars.push(
        scalar('eps_re', 'Real permittivity at the stated frequency, Maxwell Garnett', zm[0], '1'), scalar('tan_d', 'Loss tangent at the stated frequency, Maxwell Garnett', -zm[1] / zm[0], '1'),
        scalar('eps_re_BR', 'Real permittivity at the stated frequency, Bruggeman', zb[0], '1'), scalar('tan_d_BR', 'Loss tangent at the stated frequency, Bruggeman', -zb[1] / zb[0], '1'),
        scalar('tau_MW', 'Maxwell–Wagner relaxation time', tauMW, 's'), scalar('f_MW', 'Maxwell–Wagner relaxation frequency', 1 / (TAU * tauMW), 'Hz'));
      series.push(
        line('eps-f', 'Real permittivity against frequency', 'Frequency', 'Hz', fs, [{ label: 'Maxwell Garnett', data: zs.map(q => q[0][0]) }, { label: 'Bruggeman', data: zs.map(q => q[1][0]) }], 'Relative permittivity', '–', { logx: true }),
        line('loss-f', 'Loss tangent against frequency', 'Frequency', 'Hz', fs, [{ label: 'Maxwell Garnett', data: zs.map(q => -q[0][1] / q[0][0]) }, { label: 'Bruggeman', data: zs.map(q => -q[1][1] / q[1][0]) }], 'Loss tangent', '–', { logx: true, logy: true }));
    }
    return {
      scalars, series,
      checks: [
        check('Estimates within the Hashin–Shtrikman bounds', hsV, 1e-9, a.static && a.spheres ? 'Permittivity and conductivity, both formulae' : 'Not applicable to anisotropic or complex-valued cases'),
        check('Estimates within the Wiener bounds', wV, 1e-9, a.static ? 'Series and parallel limits' : 'Not applicable to complex-valued response'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const s = { ...a, static: true, spheres: true, mg_host: true }, c = emtCore(v, s), em = v.eps_m, ei = c.eI, out = [];
    out.push(bench('Dilute limit of Maxwell Garnett', (c.mg(cR(em), cR(ei), 1e-6)[0] - em) / (em * 1e-6), 3 * (ei - em) / (ei + 2 * em), 'Maxwell: ε = ε_m(1 + 3φα)', 1e-4));
    out.push(bench('Bruggeman conductivity above percolation with an insulating matrix', c.br(cR(0), cR(1), 0.5)[0], 0.25, 'σ = σ_i(3φ − 1)/2 at φ = 0.5', 1e-9));
    out.push(bench('Bruggeman below percolation with an insulating matrix', c.br(cR(0), cR(1), 0.2)[0] + 1, 1, 'σ = 0 for φ < 1/3, offset by 1', 1e-9));
    const lo = Math.min(c.hs(em, ei, v.phi)[0], c.hs(em, ei, v.phi)[1]), hi = Math.max(...c.hs(em, ei, v.phi));
    out.push(bench('Maxwell Garnett coincides with a Hashin–Shtrikman bound', c.mg(cR(em), cR(ei), v.phi)[0], ei >= em ? lo : hi, 'Coated-sphere assemblage', 1e-9));
    out.push(bench('Bruggeman returns the filler value at full loading', c.br(cR(em), cR(ei), 1)[0], ei, 'φ = 1', 1e-9));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const r = N.rng(11), n = Math.round(6 + 40 * v.phi), pts = Array.from({ length: n }, () => [130 + 380 * r(), 80 + 190 * r()]);
    return svg(`
      ${S.rect(110, 60, 420, 230, 'd-body', 6)}
      ${pts.map(p => (a.spheres ? S.circle(p[0], p[1], 10, 'd-liquid') : `<ellipse cx="${p[0]}" cy="${p[1]}" rx="5" ry="16" class="d-liquid"/>`) + (a.no_interphase ? '' : S.circle(p[0], p[1], 14, 'd-dim'))).join('')}
      ${S.rect(110, 44, 420, 12, 'd-hazard', 2)} ${S.rect(110, 294, 420, 12, 'd-hazard', 2)}
      ${[170, 320, 470].map(x => S.arrow(x, 60, x, 100)).join('')} ${S.text(560, 180, 'E', 'd-text', 'start')} ${S.arrow(552, 150, 552, 210)}
      ${S.text(320, 30, `matrix ε = ${lab(v.eps_m)},  filler ε = ${lab(v.eps_i)},  φ = ${lab(v.phi)}`)}
      ${S.text(320, 336, a.spheres ? 'spherical inclusions (L = 1/3)' : `aligned spheroids (L = ${lab(v.L_d)})`, 'd-text d-small')}
    `);
  },
  experiment: {
    objective: 'Measure the permittivity and conductivity of a filled polymer over a range of loadings and frequencies and compare with the mixing formulae and bounds.',
    apparatus: ['Series of disc specimens with filler volume fractions from 0 to at least 0.5, with evaporated or sputtered electrodes and a guard ring', 'Parallel-plate test fixture in a temperature-controlled, dry enclosure', 'Density measurement (Archimedes) to verify the volume fraction and porosity'],
    instruments: [{ name: 'Impedance analyser or LCR meter', measures: 'Capacitance and loss tangent', range: '10 mHz–10 MHz', resolution: '±0.1 %, tan δ ±10⁻⁴' }, { name: 'Electrometer with guarded electrodes', measures: 'Direct-current conductivity', range: '10⁻¹⁶–10⁻² S/m', resolution: '±2 %' }, { name: 'Micrometer', measures: 'Specimen thickness', range: '0–10 mm', resolution: '±1 µm' }, { name: 'Electron microscope', measures: 'Dispersion, particle shape and agglomeration', range: '—', resolution: '—' }],
    procedure: ['Measure thickness and electrode area of each specimen; determine actual filler fraction from density.', 'Record capacitance and loss tangent across the frequency range at fixed temperature.', 'Measure the steady direct-current conductivity after polarisation currents have decayed.', 'Plot effective permittivity and conductivity against loading together with the two formulae and the bounds.'],
    controls: ['Unfilled matrix and, where possible, a dense compact of the filler to fix the end-points', 'Specimens of two thicknesses to detect electrode polarisation'],
    signatures: ['Data lying between the Hashin–Shtrikman bounds for a well-dispersed isotropic composite', 'Agreement with Maxwell Garnett at low loading', 'A sharp rise in conductivity at a percolation threshold when the filler conducts', 'A loss peak near the Maxwell–Wagner frequency'],
    safety: ['Fine filler powders: respiratory protection and local extraction', 'Guard against electric shock at the test voltage'],
  },
  falsify: ['Measured effective permittivity or conductivity of a two-phase, pore-free, isotropic composite lying outside the Hashin–Shtrikman bounds.', 'Any two-phase measurement outside the Wiener bounds.', 'A dilute-limit slope dε/dφ that differs from 3ε_m α for well-separated spheres.'],
  alternatives: [{ name: 'Percolation theory', text: 'Near the threshold conductivity follows a power law σ ∝ (φ − φ_c)^t with a universal exponent t ≈ 2 in three dimensions, and the threshold depends strongly on particle aspect ratio; mean-field formulae give the wrong exponent.' }, { name: 'Lichtenecker logarithmic rule', text: 'An empirical interpolation, ln ε = Σ φ_k ln ε_k, often used for ceramic–polymer composites.' }, { name: 'Interphase and tunnelling models', text: 'In nanocomposites an interfacial layer and inter-particle tunnelling can dominate; a third phase or a tunnelling network model is then required.' }, { name: 'Full-field simulation', text: 'Finite-element or fast-Fourier-transform homogenisation of an imaged or generated microstructure resolves clustering and shape distributions.' }],
  hazards: [{ hazard: 'Dielectric breakdown', cause: 'Field concentration in the matrix beside high-permittivity or conducting particles', mitigation: 'Derate the design field by the field-enhancement factor; control agglomeration' }, { hazard: 'Powder inhalation', cause: 'Handling fine filler', mitigation: 'Extraction and protective equipment' }],
  standards: ['ASTM D150 (AC loss characteristics and permittivity of solid electrical insulation)', 'ASTM D257 (DC resistance or conductance of insulating materials)', 'IEC 62631 series (dielectric and resistive properties of solid insulating materials)'],
  limits: 'Quasi-static fields: inclusions much smaller than the wavelength and the skin depth. Two homogeneous, linear, isotropic phases with sharp interfaces and no porosity. Maxwell Garnett is reliable for dilute, well-separated inclusions; Bruggeman is a mean-field theory and misrepresents the critical region near percolation.',
  numerics: { method: 'Closed-form expressions in complex arithmetic; the Bruggeman quadratic is solved in a cancellation-free form and the passive root selected' },
  inverse: { series: 'eps-phi', fit: ['eps_i'] },
  extensions: ['Distribution of shapes and orientations', 'Three-phase composites with porosity', 'Differential effective-medium scheme', 'Nonlinear (field-dependent) fillers'],
};

// ------------------------------------------------------------------ memristor (linear ion drift)
function memSim(v, a, f = v.f_d, ncyc = 3, nper = 1500, x0 = v.x_0) {
  const k = v.mu_v * v.R_on / v.D_f ** 2, Rs = a.no_series ? 0 : v.R_s, p = Math.max(1, Math.round(v.p_w)), lo = a.window ? 1e-6 : 0, hi = 1 - lo;
  const drive = t => (a.sinusoid ? v.V_0 * Math.sin(TAU * f * t) : 2 * v.V_0 / Math.PI * Math.asin(Math.sin(TAU * f * t)));
  const M = x => v.R_on * x + v.R_off * (1 - x);
  const win = x => (a.window ? 1 - Math.pow(2 * x - 1, 2 * p) : 1);
  const rate = (x, t) => { const xc = N.clamp(x, lo, hi), i = drive(t) / (M(xc) + Rs); return (a.linear_drift ? k * i : v.mu_v * v.E_c / v.D_f * Math.sinh(N.clamp(v.R_on * i / (v.D_f * v.E_c), -50, 50))) * win(xc); };
  const n = ncyc * nper, dt = 1 / (f * nper), t = new Array(n + 1), x = new Array(n + 1), vv = new Array(n + 1), ii = new Array(n + 1);
  let xc = N.clamp(x0, lo, hi), dxMax = 0;
  for (let j = 0; j <= n; j++) {
    const tj = j * dt; t[j] = tj; x[j] = xc; vv[j] = drive(tj); ii[j] = vv[j] / (M(xc) + Rs);
    if (j === n) break;
    const k1 = rate(xc, tj), k2 = rate(xc + 0.5 * dt * k1, tj + 0.5 * dt), k3 = rate(xc + 0.5 * dt * k2, tj + 0.5 * dt), k4 = rate(xc + dt * k3, tj + dt);
    const xn = N.clamp(xc + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4), lo, hi);
    dxMax = Math.max(dxMax, Math.abs(xn - xc)); xc = xn;
  }
  // lobe areas of the last cycle: |∮ i dv| over each half-period
  const j0 = n - nper, jh = j0 + nper / 2; let ap = 0, am = 0;
  for (let j = j0; j < n; j++) { const da = 0.5 * (ii[j] + ii[j + 1]) * (vv[j + 1] - vv[j]); if (j < jh) ap += da; else am += da; }
  return { t, x, v: vv, i: ii, M, Rs, k, j0, n, nper, dxMax, areaP: Math.abs(ap), areaM: Math.abs(am) };
}

const memristor = {
  id: 'memristor-hysteresis',
  title: 'Memristor: pinched current–voltage hysteresis',
  module: [1, 2], klass: 'I', domains: ['materials', 'electromagnetic'],
  keywords: ['memristor', 'memristive', 'memristance', 'pinched hysteresis', 'resistive switching', 'ion drift', 'titanium dioxide', 'resistive memory', 'rram', 'hysteresis loop', 'window function', 'memory resistor', 'neuromorphic'],
  summary: 'Linear ion-drift memristor under periodic drive: evolution of the internal state, the pinched current–voltage loop, the range of memristance swept and the dependence of loop area on frequency.',
  background: [
    'A memristor is a two-terminal element whose resistance depends on the history of the current that has passed through it (Chua 1971). In the thin-film model of Strukov et al. (2008) a film of thickness D consists of a conducting doped region of width w in series with an insulating undoped region. Current moves the boundary by drifting charged dopants, so the resistance M = R_on w/D + R_off (1 − w/D) depends on the charge that has flowed.',
    'Under a periodic voltage the current–voltage curve is a loop pinched at the origin: with no voltage there is no current, whatever the state. The loop is widest when the drive period is comparable with the time needed to move the boundary across the film, and collapses to a straight line at high frequency, when the state has no time to change. Because the drift speed scales as 1/D², the effect is appreciable only in nanometre-scale films. Window functions keep the boundary inside the film and represent the slowing of drift near the electrodes.',
  ],
  phenomena: ['Drift of charged dopants in an electric field', 'History-dependent resistance', 'Pinched hysteresis', 'Frequency-dependent loop collapse', 'Saturation of the state at the film boundaries'],
  laws: ['ohm', 'charge', 'energy'],
  refs: ['Chua, L. O. (1971). Memristor — the missing circuit element. IEEE Trans. Circuit Theory 18, 507–519.', 'Strukov, D. B., Snider, G. S., Stewart, D. R. & Williams, R. S. (2008). The missing memristor found. Nature 453, 80–83.', 'Joglekar, Y. N. & Wolf, S. J. (2009). The elusive memristor: properties of basic electrical circuits. Eur. J. Phys. 30, 661–675.', 'Strukov, D. B. & Williams, R. S. (2009). Exponential ionic drift: fast switching and low volatility of thin-film memristors. Appl. Phys. A 94, 515–519.', 'Chua, L. O. & Kang, S. M. (1976). Memristive devices and systems. Proc. IEEE 64, 209–223.'],
  inputs: [
    inp('R_on', 'Resistance when fully doped', 'ohm', 100, { min: 1, max: 1e4, aliases: ['on resistance', 'low resistance', 'r_on'] }),
    inp('R_off', 'Resistance when fully undoped', 'kohm', 16, { min: 0.1, max: 1000, aliases: ['off resistance', 'high resistance', 'r_off'] }),
    inp('D_f', 'Film thickness', 'nm', 10, { min: 1, max: 100, kind: 'geometry', aliases: ['film thickness', 'thickness'] }),
    inp('mu_v', 'Dopant (ion) mobility', 'm^2/(V s)', 1e-14, { min: 1e-16, max: 1e-12, kind: 'fluid', aliases: ['ion mobility', 'dopant mobility', 'mobility'], src: 'Oxygen vacancies in titanium dioxide, order of magnitude used by Strukov et al. (2008)' }),
    inp('V_0', 'Drive voltage amplitude', 'V', 1, { min: 0.01, max: 10, aliases: ['voltage', 'amplitude', 'drive voltage'] }),
    inp('f_d', 'Drive frequency', 'Hz', 1, { min: 0.01, max: 1e4, aliases: ['frequency', 'hz'] }),
    inp('x_0', 'Initial state w/D', '1', 0.1, { min: 0.01, max: 0.99, aliases: ['initial state'] }),
    inp('p_w', 'Window exponent', '1', 2, { min: 1, max: 10, aliases: ['window exponent', 'window parameter'] }),
    inp('R_s', 'Series (contact and lead) resistance', 'ohm', 50, { min: 0, max: 1e4, aliases: ['series resistance', 'contact resistance'] }),
    inp('E_c', 'Characteristic field for nonlinear drift', 'MV/m', 100, { min: 1, max: 1000, aliases: ['characteristic field'], src: 'Of the order of 1 MV/cm for ion hopping in oxides' }),
  ],
  assumptions: [
    asm('window', 'A Joglekar window f(x) = 1 − (2x − 1)^(2p) slows the drift near the film boundaries.', { why: 'Keeps the state within the film smoothly', alt: 'No window: the drift is uniform and the state is clipped abruptly at the boundaries.' }),
    asm('linear_drift', 'Dopant drift velocity is proportional to the field (ohmic ionic conduction).', { why: 'Low-field limit', alt: 'Drift is exponential in the field, v = μE_c sinh(E/E_c), giving much faster switching at high voltage.' }),
    asm('sinusoid', 'The drive voltage is sinusoidal.', { why: 'Standard test waveform', alt: 'A triangular (linear-sweep) voltage of the same amplitude and frequency is applied.' }),
    asm('no_series', 'There is no resistance in series with the device.', { why: 'Ideal element', alt: 'A fixed series resistance takes part of the applied voltage and limits the current in the low-resistance state.' }),
  ],
  symbols: { x_w: ['State variable w/D', '1'], t: ['Time', 's'], v_m: ['Applied voltage', 'V'], i_m: ['Current', 'A'], M_r: ['Memristance', 'ohm'], F_w: ['Window function', '1'], Q_D: ['Charge to move the boundary across the film', 'C'], phi_D: ['Flux to switch fully', 'V s'], f_c: ['Characteristic switching frequency', 'Hz'] },
  equations: a => [
    eq('ohm', 'State-dependent Ohm\'s law', 'v_m', a.no_series ? 'M_r*i_m' : '(M_r + R_s)*i_m', { kind: 'law', origin: 'Chua (1971) memristor constitutive relation' }),
    eq('mem', 'Memristance of the two-region film', 'M_r', 'R_on*x_w + R_off*(1 - x_w)', { kind: 'closure', origin: 'Doped and undoped regions in series (Strukov et al. 2008)' }),
    a.linear_drift
      ? eq('state', 'Drift of the doped-region boundary', 'd(x_w,t)', 'mu_v*R_on/D_f^2*i_m*F_w', { kind: 'closure', origin: 'Dopants drifting at μ times the field in the doped region', needs: ['linear_drift'] })
      : eq('state', 'Nonlinear drift of the boundary', 'd(x_w,t)', 'mu_v*E_c/D_f*sinh(R_on*i_m/(D_f*E_c))*F_w', { kind: 'closure', origin: 'Field-activated ion hopping (Strukov & Williams 2009)' }),
    a.window ? eq('win', 'Window function', 'F_w', '1 - (2*x_w - 1)^(2*p_w)', { kind: 'closure', origin: 'Joglekar & Wolf (2009)' }) : eq('win', 'No window', 'F_w', '1', { kind: 'closure' }),
    a.sinusoid ? eq('drive', 'Applied voltage', 'v_m', 'V_0*sin(2*pi*f_d*t)', { kind: 'boundary' }) : eq('drive', 'Applied triangular voltage', 'v_m', '2*V_0/pi*asin(sin(2*pi*f_d*t))', { kind: 'boundary' }),
    eq('qd', 'Charge to cross the film', 'Q_D', 'D_f^2/(mu_v*R_on)', { kind: 'derived' }),
    eq('phid', 'Flux to switch fully', 'phi_D', 'Q_D*(R_on + R_off)/2', { kind: 'derived', origin: 'Integral of memristance over charge' }),
    eq('fc', 'Characteristic frequency', 'f_c', a.sinusoid ? 'V_0/(pi*phi_D)' : 'V_0/(4*phi_D)', { kind: 'derived', origin: 'Half-cycle flux equal to the switching flux' }),
  ],
  derivation: a => [
    { text: 'The film is two resistors in series whose lengths sum to D. With x = w/D the fraction that is doped, the resistance is a weighted sum.', tex: 'M(x) = R_{on}\\,x + R_{off}\\,(1-x)' },
    { text: 'The field in the doped region is R_on i/D. Dopants of mobility μ drift at μ times that field, moving the boundary.', tex: '\\frac{\\mathrm{d}x}{\\mathrm{d}t} = \\frac{\\mu R_{on}}{D^2}\\,i(t)\\,f(x)' },
    { text: 'Without a window the state is proportional to the charge passed, so the resistance is a function of charge alone — the defining property of a memristor.', tex: 'x = x_0 + \\frac{\\mu R_{on}}{D^2}\\,q,\\qquad M(q) = R_0 - (R_{off}-R_{on})\\frac{\\mu R_{on}}{D^2}\\,q' },
    { text: 'Integrating v = M(q) dq/dt gives the charge in terms of the flux φ = ∫v dt, a single-valued relation between charge and flux.', tex: 'R_0\\,q - \\tfrac12(R_{off}-R_{on})\\frac{\\mu R_{on}}{D^2}q^2 = \\varphi(t)' },
    { text: 'Since i = v/M, the current vanishes whenever the voltage does: the loop is pinched at the origin. The state changes appreciably only if the flux per half-cycle is comparable with the switching flux, which sets a characteristic frequency.', tex: `f_c = \\frac{V_0}{${a.sinusoid ? '\\pi' : '4'}\\,\\varphi_D},\\qquad \\varphi_D = \\frac{D^2}{\\mu R_{on}}\\cdot\\frac{R_{on}+R_{off}}{2}` },
  ],
  solve(v, a) {
    const s = memSim(v, a), { t, x, i } = s, vv = s.v, j0 = s.j0, n = s.n, warnings = [];
    const Ms = x.map(q => s.M(q)), last = arr => arr.slice(j0, n + 1);
    const xl = last(x), Ml = last(Ms), il = last(i), vl = last(vv);
    const QD = v.D_f ** 2 / (v.mu_v * v.R_on), phiD = QD * (v.R_on + v.R_off) / 2, fc = (a.sinusoid ? v.V_0 / Math.PI : v.V_0 / 4) / phiD;
    const pw = il.map((q, j) => q * vl[j]), tl = last(t), Ecyc = N.trapz(tl, pw);
    let pinch = 0; vl.forEach((q, j) => { if (Math.abs(q) < 1e-9 * v.V_0) pinch = Math.max(pinch, Math.abs(il[j])); });
    if (s.dxMax > 0.05) warnings.push('The state switches within a few time steps at this voltage and frequency; the loop is resolved coarsely.');
    if (a.window && (N.maxOf(xl) > 0.999 || N.minOf(xl) < 0.001)) warnings.push('The state reaches a film boundary, where the Joglekar window stalls the drift; recovery from the boundary is unrealistically slow in this model.');
    if (v.R_off < v.R_on) warnings.push('The undoped resistance is below the doped resistance: the roles of the two states are reversed.');
    if (v.f_d > 30 * fc) warnings.push('The drive is far above the characteristic frequency: the state barely moves and the loop is nearly a straight line.');
    const fs = N.logspace(Math.max(fc / 30, 1e-6), fc * 300, 13), sw = fs.map(f => memSim(v, a, f, 2, 500));
    return {
      scalars: [
        scalar('R_0', 'Initial memristance', s.M(v.x_0), 'ohm'), scalar('M_min', 'Lowest memristance in the cycle', N.minOf(Ml), 'ohm'), scalar('M_max', 'Highest memristance in the cycle', N.maxOf(Ml), 'ohm'),
        scalar('r_sw', 'Resistance ratio swept in the cycle', N.maxOf(Ml) / N.minOf(Ml), '1'),
        scalar('x_min', 'Lowest state w/D in the cycle', N.minOf(xl), '1'), scalar('x_max', 'Highest state w/D in the cycle', N.maxOf(xl), '1'),
        scalar('I_pk', 'Peak current', N.maxOf(il.map(Math.abs)), 'A', { show: 'mA' }),
        scalar('A_lobe', 'Area of the positive-voltage lobe of the loop', s.areaP, 'W', { show: 'mW', note: 'Units of volt × ampere' }),
        scalar('A_neg', 'Area of the negative-voltage lobe', s.areaM, 'W', { show: 'mW' }),
        scalar('E_cyc', 'Energy dissipated per cycle', Ecyc, 'J', { show: 'mJ' }), scalar('P_avg', 'Mean power', Ecyc * v.f_d, 'W', { show: 'mW' }),
        scalar('Q_D', 'Charge to move the boundary across the film', QD, 'C', { show: 'uC' }), scalar('phi_D', 'Flux to switch fully', phiD, 'V s'),
        scalar('f_c', 'Characteristic switching frequency', fc, 'Hz'), scalar('f_rel', 'Drive frequency / characteristic frequency', v.f_d / fc, '1'),
        scalar('v_drift', 'Peak boundary speed', N.maxOf(x.slice(1).map((q, j) => Math.abs(q - x[j]))) * v.D_f * v.f_d * s.nper, 'm/s', { show: 'nm/s' }),
      ],
      series: [
        line('iv-loop', 'Current–voltage loop (last cycle)', 'Voltage', 'V', vl, [{ label: 'Current', data: il.map(q => q * 1e3) }], 'Current', 'mA', { parametric: true, note: 'Pinched at the origin' }),
        line('state', 'State and drive against time', 'Time', 's', t, [{ label: 'State w/D', data: x }, { label: 'Voltage / amplitude', data: vv.map(q => q / v.V_0), dash: true }], 'State; normalised voltage', '–'),
        line('memristance', 'Memristance against time', 'Time', 's', t, [{ label: 'Memristance', data: Ms.map(q => q / 1e3) }], 'Resistance', 'kΩ'),
        line('area-f', 'Loop-lobe area against drive frequency', 'Frequency', 'Hz', fs, [{ label: 'Positive-lobe area', data: sw.map(q => q.areaP * 1e3) }], 'Area', 'mW', { logx: true }),
      ],
      checks: [
        check('Loop pinched at the origin', pinch / Math.max(N.maxOf(il.map(Math.abs)), 1e-300), 1e-9, 'Current at the instants of zero voltage'),
        check('Passivity: instantaneous power never negative', Math.min(0, N.minOf(pw)) / Math.max(N.maxOf(pw), 1e-300), 1e-12, 'A memristor stores no energy'),
        check('State stays within the film', Math.max(0, N.maxOf(x) - 1, -N.minOf(x)), 0, '0 ≤ w/D ≤ 1'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const b = { ...a, window: false, linear_drift: true, sinusoid: true }, out = [];
    const QD = v.D_f ** 2 / (v.mu_v * v.R_on), phiD = QD * (v.R_on + v.R_off) / 2, fc = v.V_0 / (Math.PI * phiD), x0 = Math.min(v.x_0, 0.5);
    const k = v.mu_v * v.R_on / v.D_f ** 2, R0 = v.R_on * x0 + v.R_off * (1 - x0) + (a.no_series ? 0 : v.R_s), dR = v.R_off - v.R_on, qL = 0.4 / k, phiL = R0 * qL - dR * k * qL * qL / 2;
    const f = Math.max(v.f_d, 4 * fc, v.V_0 / (Math.PI * Math.max(phiL, 1e-300))), phi = v.V_0 / (Math.PI * f), s = memSim(v, b, f, 1, 2000, x0);
    const q = 2 * phi / (R0 + Math.sqrt(Math.max(R0 * R0 - 2 * dR * k * phi, 0)));
    out.push(bench('State after half a cycle against the charge–flux solution', s.x[1000], x0 + k * q, 'Closed form for linear drift without a window', 1e-6));
    const s1 = memSim(v, b, 40 * fc, 2, 1000), s2 = memSim(v, b, 400 * fc, 2, 1000);
    out.push(bench('Loop area falls inversely with frequency well above f_c', s2.areaP / s1.areaP, 0.1, 'First-order perturbation in f_c/f', 0.06));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const w = 60 + 220 * v.x_0;
    return svg(`
      ${S.rect(140, 110, 20, 120, 'd-hazard', 2)} ${S.rect(480, 110, 20, 120, 'd-hazard', 2)} ${S.text(150, 100, 'Pt')} ${S.text(490, 100, 'Pt')}
      ${S.rect(160, 120, w, 100, 'd-liquid', 0)} ${S.rect(160 + w, 120, 320 - w, 100, 'd-body', 0)}
      ${S.text(160 + w / 2, 176, 'doped')} ${S.text(160 + w + (320 - w) / 2, 176, 'undoped')}
      ${S.arrow(160 + w - 4, 96, 160 + w + 50, 96, 'd-arrow d-heat')} ${S.text(160 + w + 60, 90, 'boundary drifts with current', 'd-text d-small', 'start')}
      ${S.dim(160, 250, 160 + w, 250, 'w')} ${S.dim(160, 285, 480, 285, `D = ${lab(v.D_f * 1e9, 'nm')}`)}
      ${S.path('M150 230 L150 320 L300 320 M340 320 L490 320 L490 230', 'd-line')} ${S.circle(320, 320, 20, 'd-body')} ${S.text(320, 325, '~')}
      ${S.text(320, 40, `R_on = ${lab(v.R_on, 'Ω')}   R_off = ${lab(v.R_off / 1e3, 'kΩ')}   ${lab(v.V_0, 'V')} at ${lab(v.f_d, 'Hz')}${a.sinusoid ? '' : ' (triangular)'}`)}
    `);
  },
  experiment: {
    objective: 'Record current–voltage loops of a thin-film resistive-switching device over several decades of sweep frequency and test for the fingerprints of memristive behaviour.',
    apparatus: ['Metal–oxide–metal crossbar device (for example Pt/TiO₂₋ₓ/Pt, oxide 5–50 nm thick) on a probe station', 'Screened, vibration-isolated enclosure', 'Series current-compliance resistor'],
    instruments: [{ name: 'Source–measure unit or semiconductor parameter analyser', measures: 'Current against swept voltage', range: '±10 V, 1 pA–100 mA', resolution: '±0.1 %' }, { name: 'Arbitrary-waveform generator with fast oscilloscope and transimpedance amplifier', measures: 'Loops at high sweep rate', range: 'to 10 MHz', resolution: '8–12 bit' }, { name: 'Temperature-controlled chuck', measures: 'Device temperature', range: '250–400 K', resolution: '±0.1 K' }],
    procedure: ['Electroform the device if required, with current compliance.', 'Apply sinusoidal or triangular sweeps at fixed amplitude over at least four decades of frequency, recording several cycles at each.', 'Integrate current and voltage to obtain charge and flux and plot one against the other.', 'Repeat at several amplitudes and temperatures.'],
    controls: ['A fixed resistor in place of the device, to reveal instrumental phase lag that would open a false loop', 'Open- and short-circuit sweeps to quantify parasitic capacitance and inductance'],
    signatures: ['A loop that passes through the origin at every frequency', 'Loop area shrinking monotonically toward a single-valued line as frequency rises', 'A single-valued charge–flux curve for an ideal memristor'],
    safety: ['Electrostatic-discharge precautions for the device', 'Current compliance to prevent thermal runaway and electrode damage'],
  },
  falsify: ['A current–voltage loop that does not pass through the origin (a stored-energy element or electromotive force is then present).', 'Loop area that grows without limit as frequency increases.', 'A charge–flux relation that is not single-valued in a device claimed to be an ideal memristor.'],
  alternatives: [{ name: 'Filamentary switching', text: 'In many oxides conduction changes by growth and rupture of a nanoscale conducting filament driven by Joule heating and redox reactions, giving abrupt, stochastic switching rather than smooth boundary drift.' }, { name: 'Other window and threshold models', text: 'The Biolek window removes the stalling at the boundaries; threshold models (for example the voltage-threshold adaptive model) reproduce the absence of drift below a critical voltage.' }, { name: 'Memristive systems', text: 'Real devices generally need more than one state variable and are described as memristive systems (Chua & Kang 1976) rather than ideal memristors.' }, { name: 'Parasitic capacitance', text: 'A capacitor in parallel opens the loop at the origin; non-pinched loops are evidence of such parasitics or of an internal battery effect.' }],
  hazards: [{ hazard: 'Device destruction', cause: 'Thermal runaway in the low-resistance state', mitigation: 'Current compliance and limited pulse energy' }],
  standards: ['IEC 62374 (semiconductor devices — time-dependent dielectric breakdown test for gate dielectric films)', 'JEDEC JESD22 series (reliability test methods for packaged devices)'],
  limits: 'One state variable, uniform one-dimensional film, isothermal operation. Linear drift holds only at fields well below about 1 MV/cm; the nonlinear option is a single-parameter extension. Joule heating, filament formation, electrode reactions and device-to-device variability are not modelled. The Joglekar window stalls at the film boundaries.',
  numerics: { method: 'Fixed-step fourth-order Runge–Kutta with the state confined to the film at every stage; trapezoidal quadrature for loop areas', order: 4, stability: 'Explicit: accuracy degrades when the state crosses the film in a few steps' },
  optimise: { objective: 'A_lobe', sense: 'max', vars: ['f_d'], note: 'The loop is widest when the drive frequency is near the characteristic frequency.' },
  inverse: { series: 'state', fit: ['mu_v'] },
  extensions: ['Biolek and threshold-type window functions', 'Joule-heating feedback', 'Pulse-train programming and synaptic plasticity rules', 'Crossbar arrays with sneak-path currents'],
};

// ------------------------------------------------------------------ ferroelectric hysteresis (Landau–Khalatnikov)
function feCore(v, a) {
  const al = v.a_0 * (v.T - v.T_0) + (a.screened ? 0 : v.lambda_d / EPS0), be = v.beta_L, ga = a.second_order ? 0 : v.gamma_L, G = v.Gamma_k;
  const dF = P => al * P + be * P ** 3 + ga * P ** 5, d2F = P => al + 3 * be * P * P + 5 * ga * P ** 4;
  const Ps = al >= 0 ? 0 : ga > 0 ? Math.sqrt(2 * (-al) / (be + Math.sqrt(be * be - 4 * al * ga))) : Math.sqrt(-al / be);
  // thermodynamic coercive field: largest restoring field on the polar branch, at the inflection of the free energy
  const Pc = al >= 0 ? 0 : ga > 0 ? Math.sqrt(2 * (-al) / (3 * be + Math.sqrt(9 * be * be - 20 * al * ga))) : Math.sqrt(-al / (3 * be));
  const Ec0 = Math.abs(dF(Pc)), tau = 1 / (G * Math.max(Math.abs(d2F(Ps)), 1e-300));
  return { al, be, ga, G, dF, d2F, Ps, Pc, Ec0, tau };
}
/** Integrate dP/dt = −Γ(∂F/∂P − E) over ncyc cycles with nper steps each; implicit, so stable for any stiffness. */
function feSim(v, a, f = v.f_d, E0 = v.E_0, ncyc = 2, nper = 6000) {
  const c = feCore(v, a), dt = 1 / (f * nper), n = ncyc * nper, B = 2 * (c.Ps + Math.cbrt(E0 / c.be)) + 1e-9;
  const drive = t => (a.sine_drive ? E0 * Math.sin(TAU * f * t) : 2 * E0 / Math.PI * Math.asin(Math.sin(TAU * f * t)));
  const th = dt * c.G * Math.max(Math.abs(c.al), c.d2F(c.Ps), 3 * c.be * B * B / 4) < 0.5 ? 0.5 : 1; // trapezoidal when resolved, backward Euler when stiff
  const t = new Array(n + 1), P = new Array(n + 1), E = new Array(n + 1);
  let p = c.Ps, e = drive(0), scans = 0;
  const solveStep = (pn, en, e1) => {
    const rhs = pn - dt * c.G * (1 - th) * (c.dF(pn) - en), g = q => q + dt * c.G * th * (c.dF(q) - e1) - rhs;
    let q = pn, ok = false;
    for (let it = 0; it < 40; it++) {
      const gp = 1 + dt * c.G * th * c.d2F(q); if (!(gp > 1e-3)) break;
      const dq = g(q) / gp; q -= dq; if (!(Math.abs(q) <= 4 * B)) break;
      if (Math.abs(dq) <= 1e-13 * B) { ok = true; break; }
    }
    if (ok) return q;
    // branch lost: bracket every root and take the one nearest the previous state
    scans++; const m = 160; let best = null, any = null, qa = -1.5 * B, ga = g(qa);
    for (let j = 1; j <= m; j++) { const qb = -1.5 * B + 3 * B * j / m, gb = g(qb); if (ga === 0 || ga * gb < 0) { const r = ga === 0 ? qa : N.bisect(g, qa, qb, 1e-13), st = 1 + dt * c.G * th * c.d2F(r) > 0; if (st && (best === null || Math.abs(r - pn) < Math.abs(best - pn))) best = r; if (any === null || Math.abs(r - pn) < Math.abs(any - pn)) any = r; } qa = qb; ga = gb; }
    return best !== null ? best : any !== null ? any : pn;
  };
  for (let j = 0; j <= n; j++) {
    t[j] = j * dt; P[j] = p; E[j] = e;
    if (j === n) break;
    const e1 = drive((j + 1) * dt); p = solveStep(p, e, e1); e = e1;
  }
  // loop metrics from the last cycle
  const j0 = n - nper; let W = 0, Dq = 0, jm = 0, pr = [], ec = [];
  for (let j = j0; j < n; j++) {
    const dP = P[j + 1] - P[j]; W += 0.5 * (E[j] + E[j + 1]) * dP; Dq += dP * dP / (c.G * dt); jm = Math.max(jm, Math.abs(dP) / dt);
    if (E[j] * E[j + 1] <= 0 && E[j] !== E[j + 1]) pr.push(P[j] + dP * (0 - E[j]) / (E[j + 1] - E[j]));
    if (P[j] * P[j + 1] < 0) ec.push(E[j] + (E[j + 1] - E[j]) * (0 - P[j]) / dP);
  }
  const Pr = pr.length ? N.maxOf(pr.map(Math.abs)) : 0, Ec = ec.length ? N.mean(ec.map(Math.abs)) : 0;
  return { c, t, P, E, j0, n, nper, dt, th, W, Dq, jm, Pr, Ec, switched: ec.length >= 2, Pmax: N.maxOf(P.slice(j0).map(Math.abs)), scans };
}

const ferroelectric = {
  id: 'ferroelectric-hysteresis',
  title: 'Ferroelectric hysteresis from Landau–Khalatnikov dynamics',
  module: 2, klass: 'I', domains: ['materials', 'electromagnetic'],
  keywords: ['ferroelectric', 'polarisation', 'polarization', 'hysteresis loop', 'coercive field', 'remanent polarisation', 'remanent polarization', 'landau', 'landau-khalatnikov', 'landau-devonshire', 'p-e loop', 'domain switching', 'curie temperature', 'barium titanate', 'feram'],
  summary: 'Polarisation of a single-domain ferroelectric driven by an alternating field: the polarisation–field loop, coercive field, remanent polarisation, switching current and energy loss per cycle, with their dependence on frequency and temperature.',
  background: [
    'Below its Curie temperature a ferroelectric has a spontaneous electric polarisation that can be reversed by an applied field. Landau theory describes this with a free energy that is a double well in the polarisation, F = αP²/2 + βP⁴/4 − EP with α negative below the transition. The two minima at P = ±√(−α/β) are the remanent states; an opposing field tilts the wells until, at the thermodynamic coercive field, one minimum disappears and the polarisation switches.',
    'The Landau–Khalatnikov equation supplies the dynamics: the polarisation relaxes toward lower free energy at a rate set by a kinetic coefficient Γ. Driven slowly, the system traces the static loop; driven at a frequency comparable with its relaxation rate, switching lags the field and the loop widens. Real crystals switch by nucleation and growth of domains at fields one to two orders of magnitude below the single-domain value computed here, so the model gives the intrinsic upper limit on the coercive field.',
  ],
  phenomena: ['Spontaneous polarisation below the Curie temperature', 'Bistability and switching', 'Relaxational polarisation dynamics', 'Dielectric loss as loop area', 'Depolarising field from imperfect screening'],
  laws: ['energy', 'second', 'maxwell'],
  refs: ['Landau, L. D. & Khalatnikov, I. M. (1954). On the anomalous absorption of sound near a second-order phase transition point. Dokl. Akad. Nauk SSSR 96, 469–472.', 'Devonshire, A. F. (1949). Theory of barium titanate — Part I. Phil. Mag. 40, 1040–1063.', 'Lines, M. E. & Glass, A. M. (1977). Principles and Applications of Ferroelectrics and Related Materials, Oxford University Press.', 'Rabe, K. M., Ahn, C. H. & Triscone, J.-M. (eds) (2007). Physics of Ferroelectrics: A Modern Perspective, Springer.', 'Sawyer, C. B. & Tower, C. H. (1930). Rochelle salt as a dielectric. Phys. Rev. 35, 269–273.'],
  inputs: [
    inp('a_0', 'Curie–Weiss coefficient of the quadratic term', 'm/(F K)', 6.68e5, { min: 1e4, max: 1e7, kind: 'fluid', aliases: ['curie-weiss coefficient', 'landau coefficient'], src: 'Order of magnitude for barium titanate (Curie constant about 1.7×10⁵ K)' }),
    inp('T_0', 'Curie–Weiss temperature', 'K', 381, { min: 50, max: 1000, kind: 'fluid', aliases: ['curie temperature', 'transition temperature', 'curie-weiss temperature'], src: 'Barium titanate' }),
    inp('T', 'Sample temperature', 'K', 298, { min: 4, max: 1200, kind: 'environment', env: 'air_temp', aliases: ['temperature'] }),
    inp('beta_L', 'Quartic Landau coefficient', 'V m^5/C^3', 8.2e8, { min: 1e7, max: 1e11, kind: 'fluid', aliases: ['quartic coefficient', 'beta'], src: 'Chosen to give a spontaneous polarisation of 0.26 C/m² at room temperature' }),
    inp('Gamma_k', 'Kinetic coefficient', 'S/m', 2e-3, { min: 1e-6, max: 100, kind: 'fluid', aliases: ['kinetic coefficient', 'mobility coefficient'], src: 'Sets the relaxation time; fit to the frequency dependence of the loop' }),
    inp('E_0', 'Field amplitude', 'MV/m', 12, { min: 0.1, max: 100, aliases: ['field amplitude', 'drive field', 'electric field'] }),
    inp('f_d', 'Drive frequency', 'Hz', 1000, { min: 0.01, max: 1e6, aliases: ['frequency', 'hz'] }),
    inp('gamma_L', 'Sixth-order Landau coefficient', 'V m^9/C^5', 1e10, { min: 1e8, max: 1e12, kind: 'fluid', aliases: ['sixth-order coefficient'] }),
    inp('lambda_d', 'Residual depolarisation factor', '1', 1e-4, { min: 0, max: 0.01, kind: 'geometry', aliases: ['depolarisation factor', 'depolarization factor', 'dead layer'] }),
    inp('eps_b', 'Background relative permittivity', '1', 50, { min: 1, max: 1000, kind: 'fluid', aliases: ['background permittivity'] }),
  ],
  assumptions: [
    asm('second_order', 'The free energy is truncated at the quartic term (second-order transition).', { why: 'Minimal model with a double well', alt: 'A positive sixth-order term γP⁶/6 is added, which limits the polarisation at high field.' }),
    asm('screened', 'The electrodes screen the polarisation charge perfectly: there is no depolarising field.', { why: 'Thick sample with ideal metal electrodes', alt: 'A residual depolarising field −λP/ε₀ opposes the polarisation, lowering the transition temperature and tilting the loop.' }),
    asm('sine_drive', 'The applied field is sinusoidal.', { why: 'Simple harmonic test', alt: 'A triangular field of the same amplitude and frequency is applied, as in a standard loop tracer.' }),
    asm('no_background', 'Only the switchable polarisation is plotted.', { why: 'Isolates the ferroelectric contribution', alt: 'The measured displacement D = P + ε₀ε_b E includes the linear background response.' }),
  ],
  symbols: { alpha_L: ['Quadratic Landau coefficient', 'm/F'], F_L: ['Free-energy density', 'J/m^3'], P: ['Polarisation', 'C/m^2'], E: ['Applied electric field', 'V/m'], t: ['Time', 's'], P_s: ['Spontaneous polarisation', 'C/m^2'], E_c0: ['Thermodynamic coercive field', 'V/m'], tau_P: ['Polarisation relaxation time', 's'], D_e: ['Electric displacement', 'C/m^2'], W_c: ['Energy dissipated per cycle and unit volume', 'J/m^3'] },
  equations: a => [
    eq('al', 'Quadratic coefficient', 'alpha_L', `a_0*(T - T_0)${a.screened ? '' : ' + lambda_d/eps_0'}`, { kind: 'closure', origin: 'Curie–Weiss law' + (a.screened ? '' : ' with depolarising-field energy') }),
    eq('fe', 'Landau free-energy density', 'F_L', `alpha_L*P^2/2 + beta_L*P^4/4${a.second_order ? '' : ' + gamma_L*P^6/6'} - E*P`, { kind: 'law', origin: 'Landau–Devonshire expansion in the order parameter' }),
    eq('lk', 'Landau–Khalatnikov equation', 'd(P,t)', `-Gamma_k*(alpha_L*P + beta_L*P^3${a.second_order ? '' : ' + gamma_L*P^5'} - E)`, { kind: 'law', origin: 'Relaxational dynamics down the free-energy gradient' }),
    a.sine_drive ? eq('drive', 'Applied field', 'E', 'E_0*sin(2*pi*f_d*t)', { kind: 'boundary' }) : eq('drive', 'Applied triangular field', 'E', '2*E_0/pi*asin(sin(2*pi*f_d*t))', { kind: 'boundary' }),
    ...(a.second_order
      ? [eq('ps', 'Spontaneous polarisation', 'P_s', 'sqrt(-alpha_L/beta_L)', { kind: 'derived', origin: 'Minimum of the free energy at zero field', needs: ['second_order'] }), eq('ec', 'Thermodynamic coercive field', 'E_c0', '2/(3*sqrt(3))*(-alpha_L)*sqrt(-alpha_L/beta_L)', { kind: 'derived', origin: 'Field at which the metastable minimum disappears', needs: ['second_order'] }), eq('tau', 'Relaxation time about the polar state', 'tau_P', '1/(2*Gamma_k*abs(alpha_L))', { kind: 'derived' })]
      : [eq('ps', 'Spontaneous polarisation (implicit)', 'alpha_L + beta_L*P_s^2 + gamma_L*P_s^4', '0*alpha_L', { kind: 'derived', origin: 'Minimum of the free energy at zero field' })]),
    a.no_background ? eq('disp', 'Displacement plotted', 'D_e', 'P', { kind: 'closure', needs: ['no_background'] }) : eq('disp', 'Electric displacement', 'D_e', 'P + eps_0*eps_b*E', { kind: 'law', origin: 'Constitutive relation with a linear background' }),
    eq('loss', 'Energy dissipated per cycle', 'W_c', 'int(E, P)', { kind: 'law', origin: 'Electrical work around a closed loop' }),
  ],
  derivation: a => [
    { text: 'Near the transition the free energy is expanded in even powers of the polarisation; the field couples linearly.', tex: 'F = \\tfrac12\\alpha P^2 + \\tfrac14\\beta P^4 - EP,\\qquad \\alpha = a_0\\,(T-T_0)' },
    { text: 'At zero field and α < 0 the minima are the two spontaneous states.', tex: '\\frac{\\partial F}{\\partial P}=0\\ \\Rightarrow\\ P_s = \\pm\\sqrt{-\\alpha/\\beta}' },
    { text: 'A field opposing the polarisation raises that well. The well vanishes where the static curve E = αP + βP³ turns over, which defines the intrinsic coercive field.', tex: '\\frac{\\partial^2 F}{\\partial P^2}=0\\ \\Rightarrow\\ P = \\frac{P_s}{\\sqrt3},\\qquad E_{c0} = \\frac{2}{3\\sqrt3}\\,|\\alpha|\\,P_s' },
    { text: 'Out of equilibrium the polarisation relaxes at a rate proportional to the thermodynamic force.', tex: '\\frac{\\mathrm{d}P}{\\mathrm{d}t} = -\\Gamma\\,\\frac{\\partial F}{\\partial P} = -\\Gamma\\left(\\alpha P + \\beta P^3 - E\\right)' },
    { text: 'Multiplying by dP/dt and integrating round a cycle shows that the loop area equals the energy dissipated, which is never negative.', tex: '\\oint E\\,\\mathrm{d}P = \\frac{1}{\\Gamma}\\oint\\left(\\frac{\\mathrm{d}P}{\\mathrm{d}t}\\right)^2\\mathrm{d}t \\ \\ge 0' },
    ...(a.screened ? [] : [{ text: 'Incomplete screening leaves a depolarising field proportional to the polarisation, which adds a positive quadratic term to the free energy.', tex: 'E_d = -\\frac{\\lambda P}{\\varepsilon_0}\\ \\Rightarrow\\ \\alpha \\to \\alpha + \\frac{\\lambda}{\\varepsilon_0}' }]),
  ],
  solve(v, a) {
    const s = feSim(v, a), c = s.c, warnings = [], bg = a.no_background ? 0 : EPS0 * v.eps_b;
    const j0 = s.j0, El = s.E.slice(j0), Pl = s.P.slice(j0), Dl = Pl.map((p, j) => p + bg * El[j]);
    const polar = c.al < 0, wt = TAU * v.f_d * c.tau;
    if (!polar) warnings.push('The sample is above its transition temperature (the quadratic coefficient is positive): it is paraelectric and shows no hysteresis beyond dielectric loss.');
    else if (v.E_0 < c.Ec0 && !s.switched) warnings.push('The field amplitude is below the thermodynamic coercive field: the polarisation does not switch and only a minor loop is traced.');
    if (polar) warnings.push('The coercive field is the single-domain (intrinsic) value. Measured coercive fields are typically ten to a hundred times smaller because switching proceeds by domain nucleation and wall motion.');
    if (s.th === 1) warnings.push('The relaxation is much faster than the time step, so a first-order implicit scheme is used; the loop is the quasi-static one.');
    const fs = N.logspace(Math.min(1e-3 / (TAU * c.tau), v.f_d), Math.max(3 / (TAU * c.tau), v.f_d), 9), sw = fs.map(f => feSim(v, a, f, v.E_0, 2, 1200));
    const Tc = v.T_0 - (a.screened ? 0 : v.lambda_d / (EPS0 * v.a_0));
    const Ts = N.linspace(Math.max(4, Tc - 250), Tc + 60, 80), psT = Ts.map(T => feCore({ ...v, T }, a).Ps), ecT = Ts.map(T => feCore({ ...v, T }, a).Ec0 / 1e6);
    const Pq = N.linspace(-1.4 * Math.max(c.Ps, s.Pmax), 1.4 * Math.max(c.Ps, s.Pmax), 161);
    return {
      scalars: [
        scalar('alpha_L', 'Quadratic Landau coefficient', c.al, 'm/F'), scalar('T_c', 'Transition temperature', Tc, 'K'),
        scalar('P_s', 'Spontaneous polarisation (static)', c.Ps, 'C/m^2'), scalar('P_r', 'Remanent polarisation from the loop', s.Pr, 'C/m^2'),
        scalar('P_max', 'Polarisation at peak field', s.Pmax, 'C/m^2'),
        scalar('E_c0', 'Thermodynamic coercive field', c.Ec0, 'V/m', { show: 'MV/m' }), scalar('E_c', 'Coercive field from the loop', s.Ec, 'V/m', s.switched ? { show: 'MV/m' } : { show: 'MV/m', text: 'None — no switching' }),
        scalar('W_c', 'Energy dissipated per cycle', s.W, 'J/m^3', { show: 'MJ/m^3' }), scalar('P_loss', 'Mean dissipated power density', s.W * v.f_d, 'W/m^3'),
        scalar('J_sw', 'Peak switching current density', s.jm, 'A/m^2'),
        scalar('tau_P', 'Polarisation relaxation time', c.tau, 's', { show: 'us' }), scalar('wt', 'Drive angular frequency × relaxation time', wt, '1'),
        scalar('eps_r', 'Small-signal relative permittivity', 1 + 1 / (EPS0 * Math.max(c.d2F(c.Ps), 1e-300)) + (a.no_background ? 0 : v.eps_b - 1), '1'),
        scalar('dF_b', 'Energy barrier between the two states', polar ? -(c.al * c.Ps ** 2 / 2 + c.be * c.Ps ** 4 / 4 + c.ga * c.Ps ** 6 / 6) : 0, 'J/m^3', { show: 'MJ/m^3' }),
      ],
      series: [
        line('pe-loop', a.no_background ? 'Polarisation–field loop (last cycle)' : 'Displacement–field loop (last cycle)', 'Electric field', 'MV/m', El.map(q => q / 1e6), [{ label: a.no_background ? 'Polarisation' : 'Displacement', data: Dl }], a.no_background ? 'Polarisation' : 'Displacement', 'C/m²', { parametric: true }),
        line('static', 'Static equation of state', 'Polarisation', 'C/m²', Pq, [{ label: 'E = ∂F/∂P at equilibrium', data: Pq.map(p => c.dF(p) / 1e6) }], 'Field', 'MV/m', { note: 'The branch of negative slope is unstable' }),
        line('time', 'Polarisation and field against time', 'Time', 'ms', s.t.map(q => q * 1e3), [{ label: 'Polarisation / P_max', data: s.P.map(q => q / Math.max(s.Pmax, 1e-300)) }, { label: 'Field / amplitude', data: s.E.map(q => q / v.E_0), dash: true }], 'Normalised value', '–'),
        line('ec-f', 'Coercive field against frequency', 'Frequency', 'Hz', fs, [{ label: 'Coercive field from the loop', data: sw.map(q => q.Ec / 1e6) }, { label: 'Thermodynamic value', data: fs.map(() => c.Ec0 / 1e6), dash: true }], 'Coercive field', 'MV/m', { logx: true }),
        line('ps-T', 'Spontaneous polarisation against temperature', 'Temperature', 'K', Ts, [{ label: 'Spontaneous polarisation', data: psT }], 'Polarisation', 'C/m²'),
        line('ec-T', 'Thermodynamic coercive field against temperature', 'Temperature', 'K', Ts, [{ label: 'Coercive field', data: ecT }], 'Coercive field', 'MV/m'),
      ],
      checks: [
        check('Loop area equals the dissipation integral', s.W !== 0 ? (s.W - s.Dq) / Math.abs(s.W) : 0, s.th === 0.5 ? 0.02 : 1, s.th === 0.5 ? 'Electrical work ∮E dP against (1/Γ)∮(dP/dt)² dt' : 'Indicative only: unresolved switching transient in the stiff regime'),
        check('Dissipation is non-negative (second law)', Math.min(0, s.W) / Math.max(Math.abs(s.W), 1e-300), 1e-9, 'The loop is traversed anticlockwise'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const c = feCore(v, a), out = [];
    if (c.al < 0) {
      const fq = 1e-6 / (TAU * c.tau), s = feSim(v, a, fq, 3 * c.Ec0, 2, 4000);
      out.push(bench('Quasi-static remanent polarisation', s.Pr, c.Ps, a.second_order ? 'P_r = √(−α/β)' : 'Minimum of the free energy at zero field', 1e-3));
      out.push(bench('Quasi-static coercive field', s.Ec, c.Ec0, a.second_order ? 'E_c = (2/3√3)|α|P_s' : 'Field at the inflection of the free energy', 0.02));
      if (a.second_order) out.push(bench('Spontaneous polarisation', c.Ps, Math.sqrt(-c.al / c.be), 'P_s = √(−α/β)', 1e-12));
    } else {
      const fq = 1e-6 / (TAU * c.tau), s = feSim(v, a, fq, 1e-6 * c.al * Math.sqrt(c.al / c.be), 1, 400);
      out.push(bench('Paraelectric susceptibility', s.P[100] / s.E[100], 1 / c.al, 'P = E/α (Curie–Weiss)', 1e-3));
    }
    return out;
  },
  validation: [],
  diagram(v, a) {
    const c = feCore(v, a), w = P => (c.al * P * P / 2 + c.be * P ** 4 / 4), Pm = 1.5 * (c.Ps || 0.2), ws = N.linspace(-Pm, Pm, 60).map(w), lo = N.minOf(ws), hi = N.maxOf(ws);
    const pts = N.linspace(-Pm, Pm, 60).map((P, i) => [80 + 200 * i / 59, 250 - 150 * (ws[i] - lo) / Math.max(hi - lo, 1e-300)]);
    return svg(`
      ${S.poly(pts, 'd-pipe')} ${S.line(80, 262, 280, 262, 'd-dim')} ${S.text(180, 284, 'polarisation P', 'd-text d-small')} ${S.text(180, 80, 'free energy F(P) at zero field')}
      ${c.Ps > 0 ? S.circle(80 + 200 * (0.5 + c.Ps / (2 * Pm)), 250, 6, 'd-hazard') + S.circle(80 + 200 * (0.5 - c.Ps / (2 * Pm)), 250, 6, 'd-body') : S.circle(180, 250, 6, 'd-hazard')}
      ${S.rect(400, 100, 160, 14, 'd-body', 2)} ${S.rect(400, 226, 160, 14, 'd-body', 2)} ${S.rect(400, 114, 160, 112, 'd-liquid', 0)}
      ${[430, 480, 530].map(x => S.arrow(x, 210, x, 130, 'd-arrow d-heat')).join('')} ${S.text(480, 176, 'P')}
      ${S.path('M480 100 L480 60 L600 60 L600 280 L480 280 L480 240', 'd-line')} ${S.circle(600, 170, 16, 'd-body')} ${S.text(600, 175, '~')}
      ${S.text(480, 310, `${lab(v.E_0 / 1e6, 'MV/m')} at ${lab(v.f_d, 'Hz')}`, 'd-text d-small')}
      ${S.text(320, 340, `T = ${lab(v.T, 'K')},  T₀ = ${lab(v.T_0, 'K')}  →  ${c.al < 0 ? 'ferroelectric (double well)' : 'paraelectric (single well)'}`)}
    `);
  },
  experiment: {
    objective: 'Measure polarisation–field loops of a ferroelectric capacitor as functions of field amplitude, frequency and temperature, and extract remanent polarisation, coercive field and loss.',
    apparatus: ['Thin-film or thinned single-crystal capacitor with metal electrodes of known area', 'Sawyer–Tower circuit (series reference capacitor) or virtual-earth charge amplifier', 'Temperature stage spanning the Curie temperature', 'Silicone-oil bath for bulk samples to suppress surface flashover'],
    instruments: [{ name: 'Ferroelectric tester or function generator with high-voltage amplifier', measures: 'Applied triangular or sinusoidal field', range: 'to ±500 V (films) or ±10 kV (bulk)', resolution: '±0.5 %' }, { name: 'Charge amplifier and digitiser', measures: 'Switched charge', range: '1 pC–10 µC', resolution: '±1 %' }, { name: 'Thermocouple or platinum resistance thermometer', measures: 'Sample temperature', range: '80–700 K', resolution: '±0.2 K' }, { name: 'Impedance analyser', measures: 'Small-signal permittivity against temperature', range: '100 Hz–1 MHz', resolution: '±0.1 %' }],
    procedure: ['Record loops at increasing amplitude until the remanent polarisation saturates.', 'At fixed amplitude vary the frequency over at least four decades and record the coercive field.', 'Apply positive-up-negative-down pulse sequences to separate switching from leakage and linear response.', 'Repeat while stepping the temperature through the transition; record small-signal permittivity for the Curie–Weiss plot.'],
    controls: ['A linear capacitor of similar capacitance in place of the sample, to check for phase errors', 'Leakage measurement at constant field, since a lossy linear dielectric also gives an open loop'],
    signatures: ['Saturating, square-shouldered loop with remanence independent of amplitude beyond saturation', 'Switching-current peaks at the coercive field', 'Remanent polarisation falling to zero at the transition', 'Inverse permittivity linear in temperature above the transition'],
    safety: ['High voltage: interlocked fixture and current limit', 'Dielectric breakdown can shatter brittle samples: shield and immerse in oil', 'Lead-containing ceramics: avoid dust and wash after handling'],
  },
  falsify: ['A remanent polarisation that depends on the sweep amplitude after saturation, or a loop that does not saturate (indicating leakage rather than ferroelectricity).', 'A loop traversed clockwise in the P–E plane, implying negative dissipation.', 'A spontaneous polarisation that does not vanish continuously as (T_c − T)^½ for a material with a second-order transition.', 'A measured single-domain coercive field above the thermodynamic value.'],
  alternatives: [{ name: 'Nucleation-limited switching (Kolmogorov–Avrami–Ishibashi)', text: 'Reversal by nucleation and growth of reversed domains; explains coercive fields far below the Landau value and their logarithmic or power-law frequency dependence.' }, { name: 'First-order transition', text: 'A negative quartic and positive sixth-order coefficient give a discontinuous transition with thermal hysteresis and double loops just above the Curie temperature.' }, { name: 'Preisach model', text: 'A distribution of elementary bistable units reproduces minor loops and gradual switching in ceramics.' }, { name: 'Leaky dielectric', text: 'A resistor in parallel with a linear capacitor traces an elliptical loop that can be mistaken for ferroelectric hysteresis.' }],
  hazards: [{ hazard: 'Electric shock', cause: 'Kilovolt drive for bulk samples', mitigation: 'Interlocks and current limiting' }, { hazard: 'Sample fracture', cause: 'Dielectric breakdown or piezoelectric strain', mitigation: 'Oil immersion, shielding, gradual amplitude increase' }, { hazard: 'Toxic constituents', cause: 'Lead-based compositions', mitigation: 'Dust control and hygiene' }],
  standards: ['IEEE Std 180 (standard definitions of terms associated with ferroelectric and related materials)', 'IEC 62047 series (micro-electromechanical devices: thin-film material test methods)', 'IEC 61010-1 (safety requirements for electrical equipment for measurement, control and laboratory use)'],
  limits: 'Uniform (single-domain) polarisation along one axis, uniform field, isothermal conditions, a temperature-independent quartic coefficient. Domain nucleation and wall motion, leakage current, fatigue, strain coupling and the first-order character of many real transitions are not included.',
  numerics: { method: 'Implicit trapezoidal time stepping with Newton iteration, falling back to backward Euler with a bracketed root search when the relaxation is unresolved', order: 2, stability: 'Unconditionally stable' },
  optimise: { objective: 'W_c', sense: 'min', vars: ['f_d'], note: 'Loss per cycle is least in the quasi-static limit and grows as switching begins to lag the field.' },
  inverse: { series: 'ec-f', fit: ['Gamma_k'] },
  extensions: ['Kolmogorov–Avrami–Ishibashi domain-switching kinetics', 'First-order free energy with double loops', 'Electromechanical (strain) coupling', 'Negative-capacitance transients in a series circuit'],
};

export default [electrostatic, rlc, ionicWind, syntheticJet, radiationPressure, vibratingString, coupledOsc, timeReversal, doppler, phononic, effectiveMedium, memristor, ferroelectric];
