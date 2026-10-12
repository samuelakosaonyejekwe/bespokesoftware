// Nuclear and radiation engineering: reactor point kinetics, shielding, and decay chains.
import { inp, asm, eq, scalar, line, check, bench, svg, S, lab, N } from './kit.js';

const LN2 = Math.LN2;

// ------------------------------------------------------------------ point kinetics
const kinetics = {
  id: 'reactor-point-kinetics',
  title: 'Reactor point kinetics after a reactivity step',
  module: 2, klass: 'I', domains: ['nuclear'],
  keywords: ['point kinetics', 'reactor kinetics', 'reactivity', 'delayed neutrons', 'prompt jump', 'reactor period', 'prompt critical', 'neutron population', 'nuclear reactor'],
  summary: 'Neutron population and precursor concentration after a step change in reactivity, with one effective group of delayed neutrons.',
  background: [
    'The power of a reactor follows its neutron population. Most fission neutrons appear promptly, but a small fraction β is emitted seconds later by the decay of fission-product precursors. Because the chain reaction must wait for these delayed neutrons whenever the reactivity is below β, the population changes on a time scale of seconds rather than microseconds, which is what makes a reactor controllable.',
    'With one effective precursor group the point-kinetics equations are a pair of linear ordinary differential equations. After a step in reactivity the population jumps quickly to a new level (the prompt jump) and then grows or decays exponentially with the stable reactor period.',
  ],
  phenomena: ['Prompt neutron multiplication', 'Delayed-neutron precursor decay', 'Prompt jump', 'Stable period'],
  laws: ['mass'],
  refs: ['Duderstadt, J. J. & Hamilton, L. J. (1976). Nuclear Reactor Analysis. Wiley.', 'Lamarsh, J. R. & Baratta, A. J. (2001). Introduction to Nuclear Engineering, 3rd ed. Prentice Hall.', 'Keepin, G. R. (1965). Physics of Nuclear Kinetics. Addison-Wesley.'],
  inputs: [
    inp('rho_r', 'Reactivity inserted', '1', 0.001, { min: -0.02, max: 0.0055, aliases: ['reactivity', 'reactivity insertion', 'reactivity step'], src: 'About 0.15 dollars for uranium-235 fuel' }),
    inp('beta_d', 'Delayed-neutron fraction', '1', 0.0065, { min: 0.002, max: 0.008, kind: 'fluid', aliases: ['delayed neutron fraction', 'beta'], src: 'Thermal fission of uranium-235 (Keepin 1965)' }),
    inp('lambda_d', 'Effective precursor decay constant', '1/s', 0.0767, { min: 0.01, max: 1, kind: 'fluid', aliases: ['decay constant', 'precursor decay constant'], src: 'One-group value for uranium-235' }),
    inp('Lambda_g', 'Prompt-neutron generation time', 's', 1e-4, { min: 1e-7, max: 1e-2, kind: 'fluid', aliases: ['generation time', 'neutron lifetime'], src: 'Typical of a light-water thermal reactor' }),
    inp('t_end', 'Duration simulated', 's', 60, { min: 1, max: 3600, kind: 'numerical', aliases: ['duration', 'time'] }),
  ],
  assumptions: [
    asm('one_group', 'Delayed neutrons are represented by one effective precursor group.', { why: 'Captures the prompt jump and the stable period with two equations', alt: 'Six groups are needed to follow the transient accurately between the prompt jump and the asymptotic period.' }),
    asm('no_feedback', 'Reactivity stays constant after the step: no temperature or void feedback.', { why: 'Isolates the neutron kinetics', alt: 'A negative power coefficient reduces the reactivity as the population rises and arrests the excursion.' }),
    asm('delayed', 'Delayed neutrons are present.', { why: 'They are, in every real reactor', alt: 'With all neutrons prompt the population follows exp(ρt/Λ): a counterfactual that shows why delayed neutrons matter.' }),
  ],
  symbols: { n: ['Neutron population relative to its initial value', '1'], C: ['Precursor concentration (same normalisation)', '1'], t: ['Time', 's'], alpha_f: ['Power feedback coefficient of reactivity', '1'], T_p: ['Stable reactor period', 's'], T_pa: ['Approximate stable period', 's'], n_pj: ['Population after the prompt jump', '1'] },
  equations: a => [
    a.delayed
      ? eq('n', 'Neutron balance', 'd(n,t)', `(${a.no_feedback ? 'rho_r' : '(rho_r - alpha_f*(n - 1))'} - beta_d)/Lambda_g*n + lambda_d*C`, { kind: 'law', origin: 'Neutron conservation in a point reactor', needs: ['one_group'] })
      : eq('n', 'Neutron balance without delayed neutrons', 'd(n,t)', 'rho_r/Lambda_g*n', { kind: 'hypothesis', origin: 'Counterfactual: every neutron prompt' }),
    ...(a.delayed ? [eq('c', 'Precursor balance', 'd(C,t)', 'beta_d/Lambda_g*n - lambda_d*C', { kind: 'law', origin: 'Production by fission and loss by radioactive decay' }),
      eq('pj', 'Prompt jump', 'n_pj', 'beta_d/(beta_d - rho_r)', { kind: 'derived', origin: 'Precursors frozen during the fast transient; valid for ρ < β' }),
      eq('per', 'Stable period, small-reactivity approximation', 'T_pa', '(beta_d - rho_r)/(lambda_d*rho_r)', { kind: 'derived', origin: 'Slow root of the inhour equation for ρ well below β; the solver reports the exact root' })] : []),
  ],
  derivation: () => [
    { text: 'Count neutrons: each generation of duration Λ multiplies the prompt population by (1 − β + ρ), and precursors decaying at rate λ add delayed neutrons.', tex: '\\frac{\\mathrm{d}n}{\\mathrm{d}t} = \\frac{\\rho-\\beta}{\\Lambda}\\,n + \\lambda C' },
    { text: 'Precursors are produced in proportion to the fission rate and decay exponentially.', tex: '\\frac{\\mathrm{d}C}{\\mathrm{d}t} = \\frac{\\beta}{\\Lambda}\\,n - \\lambda C' },
    { text: 'Trying exponential solutions gives the characteristic (inhour) equation, with one fast negative root and one slow root.', tex: '\\rho = \\omega\\Lambda + \\frac{\\omega\\beta}{\\omega+\\lambda}' },
    { text: 'On the fast time scale the precursors do not change, so the population settles almost at once to the prompt-jump level, then follows the slow root.', tex: 'n_{pj} = \\frac{\\beta}{\\beta-\\rho},\\qquad T_p \\approx \\frac{\\beta-\\rho}{\\lambda\\rho}' },
  ],
  solve(v, a) {
    const { rho_r: rho, beta_d: beta, lambda_d: lam, Lambda_g: L } = v, alphaF = 2e-3, warnings = [];
    const C0 = beta / (L * lam);
    const f = (t, y) => { const r = a.no_feedback ? rho : rho - alphaF * (y[0] - 1); return a.delayed ? [(r - beta) / L * y[0] + lam * y[1], beta / L * y[0] - lam * y[1]] : [r / L * y[0], 0]; };
    // the system is stiff (fast root ~ beta/Lambda): integrate the linear case exactly, otherwise with fine adaptive steps
    let t, n;
    const b = (beta - rho) / L + lam, c = -rho * lam / L, disc = Math.sqrt(b * b - 4 * c), w1 = (-b + disc) / 2, w2 = (-b - disc) / 2;
    const tEnd = !a.delayed && rho > 0 ? Math.min(v.t_end, 30 * L / rho) : v.t_end;
    if (a.delayed && a.no_feedback) {
      t = N.linspace(0, tEnd, 500);
      const A1 = (lam * C0 + (rho - beta) / L - w2) / (w1 - w2), A2 = 1 - A1;
      n = t.map(x => A1 * Math.exp(w1 * x) + A2 * Math.exp(w2 * x));
    } else if (!a.delayed) { t = N.linspace(0, tEnd, 500); const sol = N.rk45(f, [1, 0], 0, tEnd, 500, { rtol: 1e-8, maxSteps: 400000 }); t = sol.t; n = sol.y[0]; }
    else { const sol = N.rk45(f, [1, C0], 0, tEnd, 500, { rtol: 1e-7, atol: 1e-12, maxSteps: 2000000 }); t = sol.t; n = sol.y[0]; }
    const npj = beta / (beta - rho), Tp = rho !== 0 ? 1 / w1 : Infinity, dollars = rho / beta;
    if (rho >= beta) warnings.push('Reactivity is at or above the delayed-neutron fraction: the reactor is prompt critical and the population rises on the prompt time scale.');
    if (!a.delayed) warnings.push('Counterfactual: with no delayed neutrons the population e-folds every Λ/ρ, far too fast for mechanical control.');
    return {
      scalars: [
        scalar('dollars', 'Reactivity in dollars (ρ/β)', dollars, '1'), scalar('n_pj', 'Population after the prompt jump', a.delayed ? npj : NaN, '1', { text: a.delayed ? undefined : 'No prompt jump without delayed neutrons' }),
        scalar('T_p', 'Stable reactor period', a.delayed ? Tp : (rho !== 0 ? L / rho : Infinity), 's', { text: rho === 0 ? 'Infinite: the reactor is exactly critical' : undefined }),
        scalar('T_double', 'Doubling time', (a.delayed ? Tp : L / (rho || 1e-30)) * LN2, 's', { text: rho <= 0 ? 'Not applicable: the population is falling' : undefined }),
        scalar('omega_fast', 'Fast (prompt) decay rate', -w2, '1/s'), scalar('n_end', 'Relative population at the end of the run', n[n.length - 1], '1'),
      ],
      series: [line('population', 'Neutron population after the step', 'Time', 's', t, [{ label: 'Relative population', data: n }, ...(a.delayed && a.no_feedback ? [{ label: 'Asymptote: prompt jump × exp(t/T)', data: t.map(x => npj * Math.exp(x / Tp)), dash: true }] : [])], 'n / n₀', '–'),
        line('early', 'The first moments: the prompt jump', 'Time', 's', t.filter(x => x <= Math.min(tEnd, 60 * L / Math.max(beta - rho, 1e-4))).length > 5 ? N.linspace(0, Math.min(tEnd, 60 * L / Math.max(beta - rho, 1e-4)), 200) : t.slice(0, 50), (() => { const tt = N.linspace(0, Math.min(tEnd, 60 * L / Math.max(beta - rho, 1e-4)), 200); if (!(a.delayed && a.no_feedback)) return [{ label: 'Relative population', data: tt.map(x => N.interp1(t, n, x)) }]; const A1 = (lam * C0 + (rho - beta) / L - w2) / (w1 - w2); return [{ label: 'Relative population', data: tt.map(x => A1 * Math.exp(w1 * x) + (1 - A1) * Math.exp(w2 * x)) }]; })(), 'n / n₀', '–')],
      checks: a.delayed && a.no_feedback ? [check('Roots satisfy the inhour equation', (w1 * L + w1 * beta / (w1 + lam) - rho) / Math.max(Math.abs(rho), 1e-9), 1e-8, 'Slow root substituted back')] : [],
      warnings,
    };
  },
  benchmarks(v, a) {
    const r = this.solve({ ...v, rho_r: 0.001, beta_d: 0.0065, lambda_d: 0.0767, Lambda_g: 1e-4 }, { one_group: true, no_feedback: true, delayed: true }), g = s => r.scalars.find(q => q.sym === s).value;
    return [bench('Prompt jump for ρ = 0.001, β = 0.0065', g('n_pj'), 0.0065 / 0.0055, 'n = β/(β − ρ)', 1e-12), bench('Stable period against the small-reactivity formula', g('T_p'), 0.0055 / (0.0767 * 0.001), 'T ≈ (β − ρ)/(λρ); exact root is slightly longer', 0.03)];
  },
  validation: [],
  diagram(v) {
    return svg(`${S.rect(230, 90, 180, 180, 'd-body', 12)}${S.text(320, 80, 'reactor core')}
      ${S.circle(290, 170, 26, 'd-hazard')}${S.text(290, 174, 'n')}${S.circle(360, 210, 22, 'd-body')}${S.text(360, 214, 'C')}
      ${S.arrow(312, 184, 342, 200)}${S.text(360, 160, 'β/Λ', 'd-text d-small')}${S.arrow(340, 222, 300, 196)}${S.text(300, 240, 'λ', 'd-text d-small')}
      ${S.arrow(120, 170, 226, 170)}${S.text(170, 160, `ρ = ${lab(v.rho_r / v.beta_d, '$', 3)}`)}
      ${S.text(320, 310, `β = ${lab(v.beta_d)}   λ = ${lab(v.lambda_d, '1/s')}   Λ = ${lab(v.Lambda_g, 's')}`)}`);
  },
  experiment: { objective: 'Measure the stable period after a small, known reactivity insertion in a low-power research reactor and compare with the inhour relation.', apparatus: ['Zero-power research reactor or subcritical assembly with a calibrated control rod', 'Neutron detectors (fission or ion chambers) outside the core'], instruments: [{ name: 'Compensated ion chamber with logarithmic amplifier', measures: 'Neutron flux over several decades', range: '10⁻¹¹–10⁻³ A', resolution: '±2 %' }, { name: 'Period meter', measures: 'Rate of change of log power', range: '3 s to ∞', resolution: '±5 %' }], procedure: ['Bring the reactor critical at low power and hold steady.', 'Withdraw the calibrated rod by a known small worth.', 'After transients decay (about a minute), time the rise between two power levels to obtain the period.', 'Repeat for several insertions, positive and negative.'], controls: ['Measurements at powers low enough that temperature feedback is negligible', 'Rod-drop measurement as an independent check of rod worth'], signatures: ['Abrupt rise by β/(β − ρ) within milliseconds', 'Straight line on a logarithmic power plot thereafter', 'Period lengthening without limit as ρ → 0'], safety: ['Licensed facility and operators only', 'Automatic trip on short period and on high power', 'Insertions limited to a small fraction of β'] },
  falsify: ['A measured period that departs from the inhour equation by more than the uncertainty in rod worth and kinetic parameters.', 'Absence of the prompt jump on a step insertion.'],
  alternatives: [{ name: 'Six-group kinetics', text: 'Resolves the transition between prompt jump and stable period accurately; the one-group model shortens it.' }, { name: 'Space–time kinetics', text: 'Needed when the flux shape changes during the transient, as in large loosely coupled cores.' }],
  hazards: [{ hazard: 'Prompt criticality', cause: 'Reactivity insertion approaching β', mitigation: 'Limits on rod worth and withdrawal rate; fast shutdown system' }],
  standards: ['IAEA Safety Standards Series No. SSR-3 (safety of research reactors)', 'ANSI/ANS-15.1 (technical specifications for research reactors)'],
  limits: 'Point reactor with fixed flux shape, one delayed group, reactivity below β for the prompt-jump and period formulas. No thermal feedback unless the feedback assumption is released, and then only through a single illustrative power coefficient.',
  numerics: { method: 'Exact two-exponential solution for the linear case; adaptive Runge–Kutta when feedback is included' },
  inverse: { series: 'population', fit: ['rho_r'] },
  extensions: ['Six delayed groups', 'Temperature and void feedback from a thermal-hydraulic model', 'Ramp and oscillating reactivity'],
};

// ------------------------------------------------------------------ shielding
const shielding = {
  id: 'radiation-shielding',
  title: 'Gamma-ray shielding and dose rate',
  module: 2, klass: 'I', domains: ['nuclear'],
  keywords: ['radiation shielding', 'shielding', 'shield thickness', 'gamma dose', 'dose rate', 'half value layer', 'tenth value layer', 'attenuation coefficient', 'lead shield', 'gamma', 'radiation dose', 'build-up factor'],
  summary: 'Dose rate from a point gamma source behind a slab shield: inverse-square spreading, exponential attenuation and scattered-photon build-up.',
  background: [
    'Gamma photons are removed from a narrow beam exponentially with thickness, at a rate set by the linear attenuation coefficient of the material. In a real, broad-beam geometry some scattered photons still reach the detector, so the dose is higher than the narrow-beam value by a build-up factor.',
    'For a point source the unshielded dose rate falls with the square of distance and is proportional to the activity and to a gamma-ray constant characteristic of the nuclide.',
  ],
  phenomena: ['Photoelectric absorption', 'Compton scattering', 'Pair production', 'Geometric spreading'],
  laws: ['energy'],
  refs: ['Shultis, J. K. & Faw, R. E. (2000). Radiation Shielding. American Nuclear Society.', 'Knoll, G. F. (2010). Radiation Detection and Measurement, 4th ed. Wiley.', 'Hubbell, J. H. & Seltzer, S. M. Tables of X-Ray Mass Attenuation Coefficients. NIST Standard Reference Database 126.'],
  inputs: [
    inp('A_s', 'Source activity', 'Bq', 3.7e10, { min: 1e3, max: 1e16, aliases: ['activity', 'source strength'], src: 'One curie' }),
    inp('Gamma_k', 'Specific gamma-ray dose constant', 'Sv m^2/(Bq s)', 8.5e-17, { min: 1e-19, max: 1e-15, kind: 'fluid', aliases: ['gamma constant', 'dose constant'], src: 'Cobalt-60, about 0.31 mSv·m²/(GBq·h)' }),
    inp('r_d', 'Distance from source to dose point', 'm', 1, { min: 0.05, max: 100, kind: 'geometry', aliases: ['distance', 'away'] }),
    inp('mu_a', 'Linear attenuation coefficient of the shield', '1/m', 65, { min: 1, max: 2000, kind: 'fluid', aliases: ['attenuation coefficient'], src: 'Lead at about 1.25 MeV (mass coefficient 0.0057 m²/kg × 11 340 kg/m³)' }),
    inp('x_s', 'Shield thickness', 'cm', 5, { min: 0, max: 100, kind: 'geometry', aliases: ['thickness', 'thick', 'shield thickness'] }),
    inp('k_b', 'Linear build-up coefficient', '1', 1, { min: 0, max: 3, kind: 'fluid', src: 'B = 1 + k·μx; k near 1 for lead at 1 MeV, larger for light materials' }),
    inp('H_lim', 'Dose-rate limit to be met', 'Sv/s', 2.8e-9, { min: 1e-12, max: 1e-3, aliases: ['dose limit', 'limit'], src: '10 µSv/h, a common design target for an occupied area' }),
  ],
  assumptions: [
    asm('buildup', 'Scattered photons are accounted for with a linear build-up factor.', { why: 'Broad-beam geometry is the realistic case', alt: 'Narrow-beam attenuation only: under-predicts dose and is not conservative.' }),
    asm('point', 'The source is a point and the shield a slab normal to the line of sight.', { why: 'Valid when the distance is several source dimensions', alt: 'Extended sources need a point-kernel integration over the source.' }),
    asm('mono', 'A single effective photon energy characterises the attenuation.', { why: 'Adequate for one or two close lines', alt: 'Each line must be attenuated separately; the spectrum hardens with depth.' }),
  ],
  symbols: { H: ['Dose rate at the dose point', 'Sv/s'], H_0: ['Unshielded dose rate', 'Sv/s'], B: ['Build-up factor', '1'], x_half: ['Half-value layer', 'm'] },
  equations: a => [
    eq('h0', 'Unshielded dose rate', 'H_0', 'Gamma_k*A_s/r_d^2', { kind: 'law', origin: 'Inverse-square spreading from a point source', needs: ['point'] }),
    eq('att', 'Shielded dose rate', 'H', a.buildup ? 'H_0*(1 + k_b*mu_a*x_s)*exp(-mu_a*x_s)' : 'H_0*exp(-mu_a*x_s)', { kind: a.buildup ? 'empirical' : 'law', origin: a.buildup ? 'Exponential attenuation with a linear build-up factor' : 'Beer–Lambert attenuation of a narrow beam', needs: ['mono'] }),
    eq('hvl', 'Half-value layer', 'x_half', 'ln(2)/mu_a', { kind: 'derived', origin: 'Thickness that halves a narrow beam' }),
  ],
  derivation: () => [
    { text: 'Photons from a point source spread over a sphere, so the fluence rate and dose rate fall as the inverse square of distance.', tex: '\\dot H_0 = \\frac{\\Gamma A}{r^2}' },
    { text: 'In a thin layer dx a fraction μ dx of the photons interacts; integrating gives exponential attenuation of the unscattered beam.', tex: '\\frac{\\mathrm{d}I}{\\mathrm{d}x} = -\\mu I \\;\\Rightarrow\\; I = I_0 e^{-\\mu x}' },
    { text: 'Scattered photons that still reach the dose point are included through a build-up factor B ≥ 1 that grows with the number of mean free paths.', tex: '\\dot H = \\dot H_0\\,B(\\mu x)\\,e^{-\\mu x},\\qquad B \\approx 1 + k\\,\\mu x' },
  ],
  solve(v, a) {
    const H0 = v.Gamma_k * v.A_s / v.r_d ** 2, mfp = v.mu_a * v.x_s, B = a.buildup ? 1 + v.k_b * mfp : 1, H = H0 * B * Math.exp(-mfp);
    const g = x => H0 * (a.buildup ? 1 + v.k_b * v.mu_a * x : 1) * Math.exp(-v.mu_a * x) - v.H_lim;
    let xReq = 0; if (g(0) > 0) { let hi = 0.01; while (g(hi) > 0 && hi < 100) hi *= 2; xReq = g(hi) > 0 ? NaN : N.bisect(g, 0, hi, 1e-10); }
    const xs = N.linspace(0, Math.max(2 * (xReq || v.x_s), v.x_s * 1.5, 0.02), 160);
    return {
      scalars: [scalar('H_0', 'Unshielded dose rate', H0, 'Sv/s', { show: 'mSv/h' }), scalar('H', 'Dose rate behind the shield', H, 'Sv/s', { show: 'uSv/h' }), scalar('B', 'Build-up factor', B, '1'), scalar('mfp', 'Shield thickness in mean free paths', mfp, '1'),
        scalar('TF', 'Transmission (shielded ÷ unshielded)', H / H0, '1'), scalar('x_half', 'Half-value layer (narrow beam)', LN2 / v.mu_a, 'm', { show: 'cm' }), scalar('x_tenth', 'Tenth-value layer (narrow beam)', Math.LN10 / v.mu_a, 'm', { show: 'cm' }),
        scalar('x_req', 'Thickness needed to meet the limit', xReq, 'm', { show: 'cm', text: xReq === 0 ? 'None: the limit is met unshielded' : Number.isNaN(xReq) ? 'Not achievable within 100 m of this material' : undefined }),
        scalar('margin', 'Ratio of dose rate to limit', H / v.H_lim, '1', { note: H <= v.H_lim ? 'limit met' : 'limit exceeded' })],
      series: [line('dose-thickness', 'Dose rate against shield thickness', 'Thickness', 'cm', xs.map(x => x * 100), [{ label: a.buildup ? 'Broad beam (with build-up)' : 'Narrow beam', data: xs.map(x => (g(x) + v.H_lim) * 3.6e9) }, ...(a.buildup ? [{ label: 'Narrow beam', data: xs.map(x => H0 * Math.exp(-v.mu_a * x) * 3.6e9), dash: true }] : []), { label: 'Limit', data: xs.map(() => v.H_lim * 3.6e9), dash: true }], 'Dose rate', 'µSv/h', { logy: true }),
        line('dose-distance', 'Dose rate against distance at the present thickness', 'Distance', 'm', N.logspace(0.1, 50, 80), [{ label: 'Dose rate', data: N.logspace(0.1, 50, 80).map(r => v.Gamma_k * v.A_s / r ** 2 * B * Math.exp(-mfp) * 3.6e9) }], 'Dose rate', 'µSv/h', { logx: true, logy: true })],
      checks: [check('Shield never increases the narrow-beam dose', Math.max(Math.exp(-mfp) - 1, 0), 0, 'Transmission of unscattered photons ≤ 1')],
      warnings: [...(mfp > 20 ? ['Beyond about twenty mean free paths the linear build-up form is unreliable; use tabulated build-up factors.'] : []), ...(!a.buildup ? ['Narrow-beam attenuation under-predicts the dose in a real geometry: do not use it for design.'] : [])],
    };
  },
  benchmarks(v, a) {
    const r = this.solve({ ...v, x_s: LN2 / v.mu_a }, { ...a, buildup: false });
    return [bench('One half-value layer halves a narrow beam', r.scalars.find(s => s.sym === 'TF').value, 0.5, 'exp(−ln 2) = ½', 1e-12), bench('Inverse-square law', this.solve({ ...v, r_d: 2 * v.r_d }, a).scalars.find(s => s.sym === 'H_0').value / this.solve(v, a).scalars.find(s => s.sym === 'H_0').value, 0.25, 'Doubling the distance quarters the dose rate', 1e-12)];
  },
  validation: [],
  diagram(v) {
    return svg(`${S.circle(110, 180, 14, 'd-hazard')}${S.text(110, 215, 'source')}
      ${[-30, -15, 0, 15, 30].map(d => S.arrow(126, 180 + d * 0.3, 300, 180 + d * 1.6)).join('')}
      ${S.rect(304, 80, 60, 200, 'd-body', 4)}${S.text(334, 70, 'shield')}${S.dim(304, 300, 364, 300, `x = ${lab(v.x_s * 100, 'cm')}`)}
      ${S.arrow(368, 180, 500, 180, 'd-arrow d-heat')}${S.circle(520, 180, 12, 'd-body')}${S.text(520, 215, 'dose point')}
      ${S.dim(110, 330, 520, 330, `r = ${lab(v.r_d, 'm')}`)}${S.text(334, 40, `μ = ${lab(v.mu_a, '1/m')}`)}`);
  },
  experiment: { objective: 'Measure transmission through increasing thicknesses of shield in narrow- and broad-beam geometry to obtain the attenuation coefficient and the build-up factor.', apparatus: ['Sealed gamma source in a collimated holder', 'Set of shield plates of known thickness and density', 'Second collimator at the detector for the narrow-beam runs'], instruments: [{ name: 'NaI(Tl) or HPGe spectrometer', measures: 'Counts in the full-energy peak', range: '50 keV–3 MeV', resolution: '7 % (NaI) or 0.2 % (HPGe) at 662 keV' }, { name: 'Calibrated dose-rate meter', measures: 'Ambient dose equivalent rate', range: '0.1 µSv/h–10 mSv/h', resolution: '±15 %' }], procedure: ['Record the unshielded count rate and background.', 'Add plates one at a time, recording peak counts (narrow beam) and dose rate (broad beam).', 'Fit ln(counts) against thickness for μ; the ratio of broad- to narrow-beam readings gives B.'], controls: ['Background run with the source removed', 'Repeat without the detector collimator to show the effect of scatter'], signatures: ['Straight line of ln(counts) against thickness in narrow-beam geometry', 'Broad-beam readings above that line by a factor growing with thickness'], safety: ['Source handling by trained staff with dosimetry', 'Time, distance and shielding to keep exposures as low as reasonably achievable', 'Leak-tested sealed sources only'] },
  falsify: ['Narrow-beam transmission that is not exponential in thickness for a monoenergetic source.', 'A measured dose rate that does not fall as the inverse square of distance in free air.'],
  alternatives: [{ name: 'Tabulated build-up factors (Taylor or geometric-progression forms)', text: 'More accurate than the linear form, especially beyond a few mean free paths and for light materials.' }, { name: 'Monte Carlo transport', text: 'Handles real geometry, spectra and streaming paths that a point-kernel estimate cannot.' }],
  hazards: [{ hazard: 'Under-shielding', cause: 'Neglecting build-up, streaming through gaps or sky-shine', mitigation: 'Conservative build-up, overlapping joints, survey measurements after installation' }],
  standards: ['ICRP Publication 103 (recommendations on radiological protection)', 'IAEA General Safety Requirements Part 3', 'ANSI/ANS-6.4.3 (gamma-ray attenuation coefficients and build-up factors)'],
  limits: 'Point isotropic source, slab shield, one effective energy, linear build-up. Not valid for neutrons, for extended sources close to the dose point, or beyond roughly twenty mean free paths.',
  numerics: { method: 'Closed-form evaluation; bisection for the required thickness' },
  optimise: { objective: 'H', sense: 'min', vars: ['x_s'], note: 'Dose falls monotonically with thickness; in practice minimise mass or cost subject to the dose limit.' },
  inverse: { series: 'dose-thickness', fit: ['mu_a', 'k_b'] },
  extensions: ['Energy-dependent attenuation with spectral hardening', 'Multi-layer shields', 'Neutron removal cross-sections'],
};

// ------------------------------------------------------------------ decay chain
const decay = {
  id: 'decay-chain',
  title: 'Radioactive decay chain',
  module: [1, 2], klass: 'I', domains: ['nuclear'],
  keywords: ['decay chain', 'radioactive decay', 'half-life', 'half life', 'bateman', 'daughter', 'secular equilibrium', 'transient equilibrium', 'isotope', 'activity', 'radioactive'],
  summary: 'Amounts and activities of a parent, daughter and granddaughter nuclide over time (Bateman equations).',
  background: ['An unstable nuclide decays at a rate proportional to the number present. When its product is also radioactive, the amounts of each member of the chain follow coupled linear equations solved by Bateman in 1910. If the parent is much longer-lived than the daughter, the daughter activity grows until it equals the parent activity (secular equilibrium).'],
  phenomena: ['Exponential decay', 'In-growth of daughters', 'Secular and transient equilibrium'],
  laws: ['mass'],
  refs: ['Bateman, H. (1910). The solution of a system of differential equations occurring in the theory of radio-active transformations. Proc. Cambridge Philos. Soc. 15, 423–427.', 'Krane, K. S. (1988). Introductory Nuclear Physics. Wiley.'],
  inputs: [
    inp('N_0', 'Initial number of parent nuclei', '1', 1e20, { min: 1, max: 1e30, aliases: ['initial number', 'nuclei', 'atoms'] }),
    inp('T_1', 'Half-life of the parent', 'd', 2.75, { min: 1e-9, max: 1e13, aliases: ['parent half-life', 'half-life', 'half life'], src: 'Molybdenum-99 (65.9 h)' }),
    inp('T_2', 'Half-life of the daughter', 'h', 6.01, { min: 1e-12, max: 1e17, aliases: ['daughter half-life'], src: 'Technetium-99m' }),
    inp('T_3', 'Half-life of the granddaughter', 'yr', 2.11e5, { min: 1e-12, max: 1e18, aliases: ['granddaughter half-life'], src: 'Technetium-99' }),
    inp('f_b', 'Branching fraction of parent to daughter', '1', 0.875, { min: 0, max: 1, aliases: ['branching', 'branching fraction'], src: 'Fraction of molybdenum-99 decays feeding technetium-99m' }),
    inp('t_end', 'Duration simulated', 'd', 10, { min: 1e-6, max: 1e12, kind: 'numerical', aliases: ['duration'] }),
  ],
  assumptions: [
    asm('no_initial_daughter', 'Only the parent is present at the start.', { why: 'Freshly separated source', alt: 'The daughter starts in equilibrium with the parent.' }),
    asm('closed', 'Nothing is added or removed: a closed system.', { why: 'Sealed source', alt: 'The daughter is eluted (removed) once a day, as in a medical generator.' }),
  ],
  symbols: { N_1: ['Parent nuclei', '1'], N_2: ['Daughter nuclei', '1'], N_3: ['Granddaughter nuclei', '1'], lambda_1: ['Parent decay constant', '1/s'], lambda_2: ['Daughter decay constant', '1/s'], lambda_3: ['Granddaughter decay constant', '1/s'], t: ['Time', 's'], A_2: ['Daughter activity', '1/s'], t_max: ['Time of maximum daughter activity', 's'] },
  equations: () => [
    eq('p', 'Parent decay', 'd(N_1,t)', '-lambda_1*N_1', { kind: 'law', origin: 'Radioactive decay law' }),
    eq('d', 'Daughter balance', 'd(N_2,t)', 'f_b*lambda_1*N_1 - lambda_2*N_2', { kind: 'law', origin: 'Production by parent decay, loss by its own decay' }),
    eq('g', 'Granddaughter balance', 'd(N_3,t)', 'lambda_2*N_2 - lambda_3*N_3', { kind: 'law', origin: 'Production by daughter decay, loss by its own decay' }),
    eq('lam', 'Decay constant', 'lambda_1', 'ln(2)/T_1', { kind: 'definition' }),
    eq('tm', 'Time of maximum daughter activity', 't_max', 'ln(lambda_2/lambda_1)/(lambda_2 - lambda_1)', { kind: 'derived', origin: 'Setting dN₂/dt = 0 with no initial daughter' }),
  ],
  derivation: () => [
    { text: 'Each nucleus has the same probability of decaying per unit time, so the parent decays exponentially.', tex: 'N_1(t) = N_0\\,e^{-\\lambda_1 t}' },
    { text: 'The daughter is fed by the parent and decays itself; the linear equation integrates with an integrating factor.', tex: 'N_2(t) = \\frac{f\\,\\lambda_1 N_0}{\\lambda_2-\\lambda_1}\\left(e^{-\\lambda_1 t}-e^{-\\lambda_2 t}\\right)' },
    { text: 'Daughter activity peaks when production equals loss.', tex: 't_{max} = \\frac{\\ln(\\lambda_2/\\lambda_1)}{\\lambda_2-\\lambda_1}' },
  ],
  solve(v, a) {
    const l1 = LN2 / v.T_1, l2 = LN2 / v.T_2, l3 = LN2 / v.T_3, f = v.f_b, N0 = v.N_0, n = 400, t = N.linspace(0, v.t_end, n);
    const same = Math.abs(l2 - l1) < 1e-9 * Math.max(l1, l2);
    const N20 = a.no_initial_daughter ? 0 : f * l1 * N0 / Math.max(l2 - l1, 1e-300) * (l2 > l1 ? 1 : 0);
    const n1 = x => N0 * Math.exp(-l1 * x);
    const n2c = (x, start) => (same ? f * l1 * N0 * x * Math.exp(-l1 * x) : f * l1 * N0 / (l2 - l1) * (Math.exp(-l1 * x) - Math.exp(-l2 * x))) + start * Math.exp(-l2 * x);
    let N2;
    if (a.closed) N2 = t.map(x => n2c(x, N20));
    else { const day = 86400; N2 = t.map(x => { const t0 = Math.floor(x / day) * day, dt = x - t0, p0 = n1(t0); return same ? f * l1 * p0 * dt * Math.exp(-l1 * dt) : f * l1 * p0 / (l2 - l1) * (Math.exp(-l1 * dt) - Math.exp(-l2 * dt)); }); }
    // granddaughter by quadrature of its balance (stable for any ratio of half-lives)
    const N3 = [0]; for (let i = 1; i < n; i++) { const h = t[i] - t[i - 1], src = 0.5 * l2 * (N2[i] + N2[i - 1]); N3.push((N3[i - 1] + h * src) * Math.exp(-l3 * h)); }
    const N1 = t.map(n1), A1 = N1.map(x => x * l1), A2 = N2.map(x => x * l2);
    const tmax = !same && l2 > 0 && l1 > 0 ? Math.log(l2 / l1) / (l2 - l1) : 1 / l1;
    const total = N1[n - 1] + N2[n - 1] + N3[n - 1] + (1 - f) * (N0 - N1[n - 1]);
    return {
      scalars: [scalar('lambda_1', 'Parent decay constant', l1, '1/s'), scalar('lambda_2', 'Daughter decay constant', l2, '1/s'), scalar('A_0', 'Initial parent activity', N0 * l1, 'Bq', { show: 'GBq' }),
        scalar('t_max', 'Time of maximum daughter activity', tmax, 's', { show: 'h' }), scalar('A_2max', 'Maximum daughter activity', n2c(tmax, 0) * l2, 'Bq', { show: 'GBq' }),
        scalar('ratio', 'Daughter-to-parent activity ratio at the end', A2[n - 1] / Math.max(A1[n - 1], 1e-300), '1', { note: l2 > l1 ? `tends to ${(f * l2 / (l2 - l1)).toPrecision(4)} in equilibrium` : 'no equilibrium: the daughter outlives the parent' }),
        scalar('N_1_end', 'Parent nuclei remaining', N1[n - 1], '1'), scalar('N_3_end', 'Granddaughter nuclei at the end', N3[n - 1], '1')],
      series: [line('activity', 'Activities of parent and daughter', 'Time', 'd', t.map(x => x / 86400), [{ label: 'Parent', data: A1 }, { label: 'Daughter', data: A2 }], 'Activity', 'Bq'),
        line('amounts', 'Number of nuclei', 'Time', 'd', t.map(x => x / 86400), [{ label: 'Parent', data: N1 }, { label: 'Daughter', data: N2 }, { label: 'Granddaughter', data: N3 }], 'Nuclei', '–')],
      checks: a.closed && a.no_initial_daughter && l3 * v.t_end < 1e-3 ? [check('Nuclei are conserved', (total - N0) / N0, 2e-3, 'Parent + daughter + granddaughter + other branch against the initial number')] : [],
      warnings: a.closed ? [] : ['Daughter removed completely once every 24 hours; real elution efficiency is below 100 %.'],
    };
  },
  benchmarks(v, a) {
    const r = this.solve({ ...v, t_end: v.T_1 }, { no_initial_daughter: true, closed: true });
    const l1 = LN2 / v.T_1, l2 = LN2 / v.T_2, tm = Math.log(l2 / l1) / (l2 - l1), q = this.solve({ ...v, t_end: 2 * tm }, { no_initial_daughter: true, closed: true }), s = q.series[0], i = s.y[1].data.indexOf(N.maxOf(s.y[1].data));
    return [bench('Half the parent remains after one half-life', r.scalars.find(s2 => s2.sym === 'N_1_end').value / v.N_0, 0.5, 'Decay law', 1e-12), bench('Computed peak of daughter activity at the analytic time', s.x.data[i] * 86400 / tm, 1, 't_max = ln(λ₂/λ₁)/(λ₂ − λ₁)', 0.01)];
  },
  validation: [],
  diagram(v) {
    const d = x => (x > 3.15e7 ? lab(x / 3.156e7, 'yr') : x > 86400 ? lab(x / 86400, 'd') : x > 3600 ? lab(x / 3600, 'h') : lab(x, 's'));
    return svg(`${S.circle(120, 180, 40, 'd-hazard')}${S.text(120, 184, 'parent')}${S.circle(320, 180, 34, 'd-body')}${S.text(320, 184, 'daughter')}${S.circle(520, 180, 34, 'd-body')}${S.text(520, 176, 'grand-')}${S.text(520, 192, 'daughter')}
      ${S.arrow(162, 180, 284, 180)}${S.text(222, 168, `T½ = ${d(v.T_1)}`)}${S.text(222, 200, `fraction ${lab(v.f_b)}`, 'd-text d-small')}${S.arrow(356, 180, 484, 180)}${S.text(420, 168, `T½ = ${d(v.T_2)}`)}${S.arrow(520, 216, 520, 280)}${S.text(520, 300, `T½ = ${d(v.T_3)}`)}`);
  },
  experiment: { objective: 'Follow the in-growth and decay of a short-lived daughter after chemical separation from its parent.', apparatus: ['Radionuclide generator or separated parent solution', 'Shielded counting well'], instruments: [{ name: 'Gamma spectrometer', measures: 'Counts in the daughter and parent peaks', range: '50 keV–2 MeV', resolution: '0.2–7 %' }, { name: 'Dose calibrator', measures: 'Activity', range: '1 kBq–100 GBq', resolution: '±3 %' }], procedure: ['Separate the daughter completely and note the time.', 'Count the parent fraction at regular intervals of about a tenth of the daughter half-life.', 'Plot daughter activity against time and compare with the Bateman curve.'], controls: ['Background counts', 'Counting a long-lived reference source to track detector stability'], signatures: ['Daughter activity rising as 1 − exp(−λ₂t) at first', 'Maximum at the predicted time', 'Constant activity ratio thereafter'], safety: ['Work in a licensed radiochemistry laboratory', 'Shielding, remote handling and personal dosimetry', 'Contamination monitoring after each separation'] },
  falsify: ['A decay curve of a single nuclide that is not exponential beyond counting statistics.', 'A daughter-activity maximum at a time different from the Bateman prediction by more than the half-life uncertainties allow.'],
  alternatives: [{ name: 'Full Bateman solution for long chains', text: 'Closed form for any number of members; numerically delicate when two decay constants nearly coincide.' }, { name: 'Matrix exponential', text: 'Robust for branched networks and near-equal constants.' }],
  hazards: [{ hazard: 'In-growth of a more hazardous daughter', cause: 'Storage of a parent whose progeny emit more penetrating radiation', mitigation: 'Assess the whole chain, not the parent alone' }],
  standards: ['IAEA Specific Safety Guide SSG-46 (radiation protection in medical uses)', 'ISO 2919 (sealed radioactive sources)'],
  limits: 'Three-member linear chain with one branching fraction, constant decay constants. No neutron activation, no chemical fractionation other than the optional complete daily removal of the daughter.',
  numerics: { method: 'Closed-form Bateman expressions for parent and daughter; exponential-integrator quadrature for the granddaughter' },
  inverse: { series: 'activity', fit: ['T_1'] },
  extensions: ['Arbitrary chains and branches by matrix exponential', 'Production by irradiation (activation and burn-up)', 'Partial elution efficiency'],
};

export default [kinetics, shielding, decay];
