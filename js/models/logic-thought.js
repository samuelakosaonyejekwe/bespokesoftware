// Classic logical, probabilistic, decision-theoretic and conceptual thought experiments.
// Every model is computable (exact probabilities, series, simulations, payoffs, bounds) and carries
// the propositional skeleton of its argument in `logicPreset`.
import { inp, asm, eq, scalar, line, field, check, bench, svg, S, lab, N, C } from './kit.js';

// ------------------------------------------------------------------ shared helpers
const val = (r, s) => r.scalars.find(q => q.sym === s).value;
/** Round to an integer and clamp: inputs that count things may arrive as non-integers. */
const int = (x, lo, hi) => Math.min(hi, Math.max(lo, Math.round(Number.isFinite(x) ? x : lo)));
/** Roughly logarithmically spaced integer checkpoints 1 … n for convergence plots. */
const marks = (n, m = 60) => { const s = new Set(); for (let i = 0; i < m; i++) s.add(Math.max(1, Math.round(Math.pow(n, i / (m - 1))))); s.add(n); return [...s].sort((p, q) => p - q); };
/** Binary entropy in nats. */
const H2 = e => (e <= 0 || e >= 1 ? 0 : -e * Math.log(e) - (1 - e) * Math.log(1 - e));
/** Standard normal cumulative distribution (Abramowitz & Stegun 7.1.26, absolute error below 1.5e-7). */
const Phi = z => { const x = Math.abs(z) / Math.SQRT2, t = 1 / (1 + 0.3275911 * x); const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x); return z >= 0 ? 0.5 * (1 + y) : 0.5 * (1 - y); };
const PCT = { show: '%' };
const YEAR = 3.15576e7, LY = 9.4607304725808e15;

// ================================================================== 1. Monty Hall
const montyHall = {
  id: 'monty-hall',
  title: 'The Monty Hall problem',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['monty hall', 'three doors', 'game show', 'goat', 'switch doors', 'stay or switch', 'host opens a door', 'conditional probability', 'door'],
  summary: 'A prize is hidden behind one of n doors; after the first choice the host opens k losing doors. Exact and simulated probabilities of winning by staying or by switching.',
  background: [
    'A contestant picks one of three doors, one of which hides a car and the others goats. The host, who knows where the car is, opens one of the two remaining doors to reveal a goat and offers the contestant the chance to switch. Most people judge the two closed doors to be equally likely; in fact switching wins with probability 2/3.',
    'The result follows from conditional probability once the host\'s behaviour is specified. The first choice is right with probability 1/n and the host\'s action, being constrained never to reveal the car, carries no information about that door. All the remaining probability is therefore concentrated on the doors he leaves closed. If the host instead opens doors at random and merely happens to reveal goats, the advantage disappears: the answer depends on the protocol, not only on what is seen.',
  ],
  phenomena: ['Conditional probability', 'Information carried by a constrained choice', 'Dependence of an inference on the data-generating protocol', 'Monte-Carlo convergence'],
  laws: ['kolmogorov', 'logic_nc'],
  refs: ['Selvin, S. (1975). A problem in probability (letter to the editor). The American Statistician 29(1), 67.', 'Selvin, S. (1975). On the Monty Hall problem (letter to the editor). The American Statistician 29(3), 134.', 'Granberg, D. & Brown, T. A. (1995). The Monty Hall dilemma. Personality and Social Psychology Bulletin 21, 711–723.', 'Rosenhouse, J. (2009). The Monty Hall Problem. Oxford University Press.', 'Gill, R. D. (2011). The Monty Hall problem is not a probability puzzle (it\'s a challenge in mathematical modelling). Statistica Neerlandica 65, 58–71.'],
  inputs: [
    inp('n_d', 'Number of doors', '1', 3, { min: 3, max: 100, aliases: ['doors', 'number of doors', 'boxes', 'cups'] }),
    inp('k_open', 'Doors opened by the host', '1', 1, { min: 1, max: 98, aliases: ['opened', 'host opens', 'revealed'] }),
    inp('n_trials', 'Simulated games', '1', 20000, { min: 100, max: 500000, kind: 'numerical', aliases: ['trials', 'games', 'simulations'] }),
    inp('seed', 'Random seed', '1', 1, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('host_knows', 'The host knows where the prize is and always opens losing doors.', { why: 'The standard statement of the problem', alt: 'An ignorant host opens doors at random; games in which the prize is exposed are void. Conditional on only goats being shown, staying and switching are equally good.' }),
    asm('must_offer', 'The host must always offer the switch, whatever the first choice.', { why: 'Without a fixed protocol the offer itself carries information', alt: 'An adversarial host offers the switch only when the first choice is correct, so switching always loses.' }),
  ],
  symbols: { P_st: ['Probability of winning by staying', '1'], P_sw: ['Probability of winning by switching to one remaining door', '1'], A_sw: ['Advantage ratio of switching', '1'], sigma_mc: ['Standard error of the simulated frequency', '1'], P_valid: ['Probability that the game proceeds to the offer', '1'], n_left: ['Other doors left closed', '1'] },
  equations: a => (!a.must_offer ? [
    eq('offer', 'Probability that the switch is offered', 'P_valid', '1/n_d', { kind: 'derived', origin: 'The adversarial host offers only when the first choice is correct' }),
    eq('stay', 'Winning by staying, given an offer', 'P_st', '1', { kind: 'derived', origin: 'Bayes\' theorem: the offer reveals that the first choice is right' }),
    eq('switch', 'Winning by switching, given an offer', 'P_sw', '0', { kind: 'derived', origin: 'Complement of staying' }),
    eq('se', 'Standard error of a simulated frequency', 'sigma_mc', 'sqrt(P_sw*(1 - P_sw)/(n_trials*P_valid))', { kind: 'derived', origin: 'Binomial sampling over the games in which the offer is made' }),
  ] : a.host_knows ? [
    eq('left', 'Other doors left closed', 'n_left', 'n_d - min(k_open, n_d - 2) - 1', { kind: 'definition', note: 'The host opens at most n − 2 doors, so that one other door is left to switch to.' }),
    eq('stay', 'Winning by staying', 'P_st', '1/n_d', { kind: 'law', origin: 'Uniform prior; the informed host\'s action is uninformative about the chosen door', needs: ['host_knows', 'must_offer'] }),
    eq('switch', 'Winning by switching to one of the remaining doors', 'P_sw', '(n_d - 1)/(n_d*n_left)', { kind: 'derived', origin: 'Total probability: the mass (n − 1)/n is shared among the n − k − 1 doors left closed', needs: ['host_knows', 'must_offer'] }),
    eq('adv', 'Advantage of switching', 'A_sw', 'P_sw/P_st', { kind: 'definition' }),
    eq('se', 'Standard error of a simulated frequency', 'sigma_mc', 'sqrt(P_sw*(1 - P_sw)/n_trials)', { kind: 'derived', origin: 'Binomial sampling' }),
  ] : [
    eq('left', 'Other doors left closed', 'n_left', 'n_d - min(k_open, n_d - 2) - 1', { kind: 'definition', note: 'The host opens at most n − 2 doors, so that one other door is left to switch to.' }),
    eq('valid', 'Probability that no prize is exposed', 'P_valid', '(n_left + 1)/n_d', { kind: 'derived', origin: 'Total probability over the position of the prize' }),
    eq('stay', 'Winning by staying, given only goats are exposed', 'P_st', '1/(n_left + 1)', { kind: 'derived', origin: 'Bayes\' theorem with a host who opens doors at random: one of the n − k doors still closed' }),
    eq('switch', 'Winning by switching, given only goats are exposed', 'P_sw', '1/(n_left + 1)', { kind: 'derived', origin: 'Symmetry among all n − k doors still closed' }),
    eq('adv', 'Advantage of switching', 'A_sw', 'P_sw/P_st', { kind: 'definition' }),
    eq('se', 'Standard error of a simulated frequency', 'sigma_mc', 'sqrt(P_sw*(1 - P_sw)/(n_trials*P_valid))', { kind: 'derived', origin: 'Binomial sampling over the games that are not void' }),
  ]),
  derivation: a => [
    { text: 'The prize is equally likely to be behind any door, so the first choice is correct with probability 1/n.', tex: 'P(\\text{first choice correct}) = \\frac{1}{n}' },
    ...(!a.must_offer ? [
      { text: 'If the host offers the switch only when the first choice is correct, the offer is itself decisive evidence.', tex: 'P(\\text{first correct}\\mid\\text{offer}) = 1,\\qquad P_{sw} = 0' },
    ] : a.host_knows ? [
      { text: 'An informed host can always open k losing doors among the n − 1 others, whatever the first choice. His action therefore has the same probability under both hypotheses about the chosen door and does not change its probability.', tex: 'P_{st} = P(\\text{first correct}\\mid\\text{host opens } k \\text{ goats}) = \\frac{1}{n}' },
      { text: 'The remaining probability (n − 1)/n belongs to the n − k − 1 other doors still closed, which are symmetric.', tex: 'P_{sw} = \\frac{n-1}{n\\,(n-k-1)}' },
      { text: 'For three doors and one opened this gives 2/3 against 1/3. The ratio of switching to staying exceeds one whenever the host opens at least one door.', tex: '\\frac{P_{sw}}{P_{st}} = \\frac{n-1}{n-k-1} > 1' },
    ] : [
      { text: 'A host who opens k of the other doors at random exposes the prize with probability k/(n − 1) when the first choice is wrong, and never when it is right.', tex: 'P(\\text{goats only}) = \\frac1n + \\frac{n-1}{n}\\cdot\\frac{n-1-k}{n-1} = \\frac{n-k}{n}' },
      { text: 'Seeing only goats is now evidence in favour of the first choice, and Bayes\' theorem makes every closed door equally likely.', tex: 'P_{st} = \\frac{1/n}{(n-k)/n} = \\frac{1}{n-k} = P_{sw}' },
    ]),
    { text: 'A simulation of N valid games estimates each probability with binomial standard error.', tex: '\\sigma = \\sqrt{\\frac{p\\,(1-p)}{N}}' },
  ],
  solve(v, a) {
    const n = int(v.n_d, 3, 1000), k = int(v.k_open, 1, n - 2), m = n - k - 1;
    const nT = int(v.n_trials, 100, 2000000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const warnings = [];
    if (Math.round(v.k_open) > n - 2) warnings.push(`The host can open at most n − 2 = ${n - 2} doors while leaving one to switch to; that value has been used.`);
    let pSt, pSw, pValid = 1;
    if (!a.must_offer) { pSt = 1; pSw = 0; pValid = 1 / n; }
    else if (a.host_knows) { pSt = 1 / n; pSw = (n - 1) / (n * m); }
    else { pSt = 1 / (n - k); pSw = 1 / (n - k); pValid = (n - k) / n; }
    if (!a.must_offer && !a.host_knows) warnings.push('An adversarial host must know where the prize is; the informed adversarial protocol has been used.');
    // simulation: the contestant always picks door 0; only the facts that matter are sampled
    let games = 0, wSt = 0, wSw = 0, ci = 0;
    const cp = marks(nT), xs = [], ySt = [], ySw = [];
    for (let t = 1; t <= nT; t++) {
      const first = rnd() * n < 1;
      let valid = true;
      if (!a.must_offer) valid = first;
      else if (!a.host_knows && !first) valid = rnd() * (n - 1) >= k;
      if (valid) { games++; if (first) wSt++; else if (rnd() * m < 1) wSw++; }
      if (t === cp[ci]) { ci++; if (games > 0) { xs.push(t); ySt.push(wSt / games); ySw.push(wSw / games); } }
    }
    const fSt = games ? wSt / games : 0, fSw = games ? wSw / games : 0;
    const sig = Math.sqrt(pSw * (1 - pSw) / Math.max(games, 1)), sigSt = Math.sqrt(pSt * (1 - pSt) / Math.max(games, 1));
    const ks = Array.from({ length: n - 2 }, (_, i) => i + 1);
    const swK = ks.map(q => (!a.must_offer ? 0 : a.host_knows ? (n - 1) / (n * (n - q - 1)) : 1 / (n - q)));
    const stK = ks.map(q => (!a.must_offer ? 1 : a.host_knows ? 1 / n : 1 / (n - q)));
    const ns = Array.from({ length: 18 }, (_, i) => i + 3);
    return {
      scalars: [
        scalar('P_st', 'Probability of winning by staying', pSt, '1', PCT),
        scalar('P_sw', 'Probability of winning by switching to one remaining door', pSw, '1', PCT),
        scalar('A_sw', 'Advantage ratio, switching against staying', pSw / pSt, '1'),
        scalar('P_valid', 'Probability that the game reaches the offer', pValid, '1', PCT),
        scalar('f_st', 'Simulated frequency of winning by staying', fSt, '1', PCT),
        scalar('f_sw', 'Simulated frequency of winning by switching', fSw, '1', PCT),
        scalar('sigma_mc', 'Standard error of the simulated switching frequency', Math.sqrt(pSw * (1 - pSw) / (nT * pValid)), '1'),
        scalar('n_games', 'Valid games simulated', games, '1'),
        scalar('n_left', 'Other doors left closed', m, '1'),
      ],
      series: [
        line('convergence', 'Simulated win frequency against number of games', 'Games played', '–', xs, [{ label: 'Switch (simulated)', data: ySw }, { label: 'Stay (simulated)', data: ySt }, { label: 'Switch (exact)', data: xs.map(() => pSw), dash: true }, { label: 'Stay (exact)', data: xs.map(() => pSt), dash: true }], 'Win frequency', '–', { logx: true }),
        line('by-opened', 'Win probability against doors opened', 'Doors opened by the host', '–', ks, [{ label: 'Switch', data: swK }, { label: 'Stay', data: stK }], 'Probability', '–', { kind: ks.length < 3 ? 'scatter' : 'line' }),
        line('by-doors', 'Host opens all but one other door', 'Number of doors', '–', ns, [{ label: 'Switch', data: ns.map(q => (!a.must_offer ? 0 : a.host_knows ? (q - 1) / q : 0.5)) }, { label: 'Stay', data: ns.map(q => (!a.must_offer ? 1 : a.host_knows ? 1 / q : 0.5)) }], 'Probability', '–'),
      ],
      checks: [
        check('Total probability', pSt + m * pSw - 1, 1e-12, 'Staying plus switching to each of the remaining doors exhausts the possibilities'),
        check('Simulated switching frequency against exact value', fSw - pSw, 4 * sig + 1e-12, 'Within four binomial standard errors'),
        check('Simulated staying frequency against exact value', fSt - pSt, 4 * sigSt + 1e-12, 'Within four binomial standard errors'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const r = this.solve(v, a), out = [];
    const pSw = val(r, 'P_sw'), sig = val(r, 'sigma_mc');
    out.push(bench('Simulated against exact switching probability', val(r, 'f_sw'), pSw, 'Exact conditional probability; tolerance of four standard errors', pSw > 0 ? Math.max(4 * sig / pSw, 1e-9) : 1e-9));
    const c = this.solve({ ...v, n_d: 3, k_open: 1 }, { host_knows: true, must_offer: true });
    out.push(bench('Classic three-door game: switching', val(c, 'P_sw'), 2 / 3, 'Selvin (1975)', 1e-12));
    const g = this.solve({ ...v, n_d: 3, k_open: 1 }, { host_knows: false, must_offer: true });
    out.push(bench('Ignorant host, three doors: switching', val(g, 'P_sw'), 1 / 2, 'Bayes\' theorem with a random reveal', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const n = int(v.n_d, 3, 1000), k = int(v.k_open, 1, n - 2), show = Math.min(n, 7), w = 60, gap = 18, x0 = 320 - (show * w + (show - 1) * gap) / 2;
    const opened = Math.min(k, show - 2);
    const doors = Array.from({ length: show }, (_, i) => {
      const x = x0 + i * (w + gap), isOpen = i > 0 && i <= opened;
      return `${S.rect(x, 110, w, 120, isOpen ? 'd-hazard' : 'd-body')}${S.text(x + w / 2, 175, i === 0 ? 'chosen' : isOpen ? 'goat' : '?', 'd-text d-small')}${S.text(x + w / 2, 250, i === 0 ? '1' : isOpen ? 'opened' : 'closed', 'd-text d-small')}`;
    }).join('');
    return svg(`
      ${S.text(320, 40, `${n} doors, host opens ${k}${n > show ? ` (first ${show} drawn)` : ''}`)}
      ${S.text(320, 70, a.host_knows ? 'The host knows where the prize is' : 'The host opens doors at random', 'd-text d-small')}
      ${doors}
      ${S.arrow(x0 + w / 2, 290, x0 + w / 2, 262)} ${S.text(x0 + w / 2, 310, 'stay', 'd-text d-small')}
      ${S.arrow(x0 + (show - 1) * (w + gap) + w / 2, 290, x0 + (show - 1) * (w + gap) + w / 2, 262)} ${S.text(x0 + (show - 1) * (w + gap) + w / 2, 310, 'switch', 'd-text d-small')}
      ${S.text(320, 345, `P(stay) = ${lab(!a.must_offer ? 1 : a.host_knows ? 1 / n : 1 / (n - k))}    P(switch) = ${lab(!a.must_offer ? 0 : a.host_knows ? (n - 1) / (n * (n - k - 1)) : 1 / (n - k))}`)}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'HostGoat', text: 'The host knowingly opens a losing door and leaves exactly one other door closed' }, { k: 'FirstCar', text: 'The first choice hides the car' }, { k: 'StayWins', text: 'Staying wins' }, { k: 'SwitchWins', text: 'Switching wins' }],
    premises: ['HostGoat', 'FirstCar -> StayWins', '(~FirstCar & HostGoat) -> SwitchWins', 'StayWins <-> ~SwitchWins'],
    conclusion: 'SwitchWins <-> ~FirstCar',
  },
  philosophy: [
    'The problem is a compact demonstration that the evidential weight of an observation depends on the process that produced it. The same visual scene — a chosen door, an open door showing a goat, one closed door — supports different conclusions according to whether the host was constrained to show a goat or merely happened to.',
    'It also illustrates the gap between intuitive and normative reasoning. The strong and persistent intuition that two unopened doors must be equally likely applies a principle of indifference to a situation whose symmetry has been broken by the host\'s knowledge.',
    'For the methodology of thought experiments the lesson is that an under-specified scenario has no single answer. Writing the protocol down as explicit premises is what turns a dispute into a calculation.',
  ],
  experiment: {
    objective: 'Estimate the winning frequencies of the stay and switch strategies under a fixed host protocol and compare them with the exact probabilities.',
    apparatus: ['Three opaque cups and one small object, or three playing cards with one ace', 'A second person to act as host who can see where the object is placed', 'Alternatively a computer simulation with a recorded random seed'],
    instruments: [{ name: 'Tally sheet or log file', measures: 'Outcome of each game under each strategy', range: '≥ 300 games per strategy', resolution: 'One game' }, { name: 'Die or random-number table', measures: 'Placement of the prize and first choice', range: '1–3', resolution: '—' }],
    procedure: ['Place the prize by a random draw hidden from the contestant.', 'The contestant chooses a cup; the host lifts one of the other cups that does not hide the prize, choosing at random when two are available.', 'Record whether staying would have won and whether switching would have won.', 'Repeat at least 300 times, then compute the frequencies and their binomial standard errors.'],
    controls: ['Repeat with a host who lifts one of the other cups blindly, discarding games in which the prize is exposed; the two frequencies should then be equal.', 'Check that the prize position is uniform over the cups.'],
    signatures: ['Switching frequency near 2/3 and staying frequency near 1/3 with an informed host', 'Both frequencies near 1/2 with an ignorant host, conditional on a goat being shown', 'Sampling error shrinking as the inverse square root of the number of games'],
    safety: [],
  },
  falsify: ['A long run of games under the informed-host protocol in which the switching frequency differs from (n − 1)/(n(n − k − 1)) by many standard errors.', 'An ignorant-host run, conditioned on goats being exposed, in which switching retains a systematic advantage.'],
  alternatives: [
    { name: 'Ignorant host ("Monty Fall")', text: 'If the host opens a door at random and it happens to show a goat, the observation favours the first choice and the two remaining doors are equally likely.' },
    { name: 'Adversarial host', text: 'If the host is free to choose whether to make the offer, an offer made only when the first choice is right makes switching a certain loss. Without a stated protocol the problem has no determinate answer.' },
    { name: 'Biased host', text: 'If, when free to choose, the host prefers one door with probability q, the conditional probability of winning by switching given the door actually opened lies between 1/2 and 1, although the unconditional value remains 2/3.' },
  ],
  limits: 'Uniform placement of the prize, a first choice made without information, and a host protocol fixed in advance. With several doors the switching probability is that of moving to one uniformly chosen remaining door. The integer inputs are rounded, and the number of opened doors is limited to n − 2.',
  numerics: { method: 'Closed-form conditional probabilities; Monte-Carlo simulation with a seeded generator', order: 0.5, stability: 'Sampling error falls as N^(−1/2)', resolution: 'n_trials' },
  extensions: ['Host with a biased choice between two goat doors', 'Several contestants or sequential reveals', 'Quantum versions of the game with entangled strategies'],
};

// ================================================================== 2. Zeno: Achilles and the tortoise
const zenoAchilles = {
  id: 'zeno-achilles',
  title: 'Zeno\'s paradox of Achilles and the tortoise',
  module: 1, klass: ['II', 'I'], domains: ['logic', 'classical'],
  keywords: ['achilles and the tortoise', 'zeno', 'achilles', 'tortoise', 'dichotomy', 'supertask', 'infinite series', 'geometric series', 'infinitely many steps', 'catch up'],
  summary: 'Achilles chases a slower tortoise with a head start. The infinitely many stages of Zeno\'s description form a geometric series whose partial sums converge to the finite catch-up time.',
  background: [
    'Zeno of Elea argued that swift Achilles can never overtake a tortoise given a head start: by the time Achilles reaches the point where the tortoise was, the tortoise has moved on, and this repeats without end. The description is correct stage by stage; the conclusion that the pursuit never ends requires the further premise that infinitely many stages cannot be completed in a finite time.',
    'With constant speeds the durations of successive stages form a geometric sequence with ratio equal to the ratio of the speeds. Since Cauchy and Weierstrass the sum of such a series is defined as the limit of its partial sums, which here is finite and equal to the time obtained by elementary kinematics. Whether a completed infinity of tasks is thereby made unproblematic remains a subject of philosophical discussion under the heading of supertasks.',
  ],
  phenomena: ['Uniform motion', 'Convergence of a geometric series', 'Limit of partial sums', 'Infinite divisibility of an interval'],
  laws: ['logic_nc'],
  refs: ['Aristotle. Physics, Book VI, ch. 9, 239b14–29.', 'Salmon, W. C. (ed.) (2001). Zeno\'s Paradoxes. Hackett Publishing.', 'Thomson, J. F. (1954). Tasks and super-tasks. Analysis 15, 1–13.', 'Benacerraf, P. (1962). Tasks, super-tasks, and the modern Eleatics. Journal of Philosophy 59, 765–784.', 'Grünbaum, A. (1967). Modern Science and Zeno\'s Paradoxes. Wesleyan University Press.'],
  inputs: [
    inp('d_0', 'Head start of the tortoise', 'm', 100, { min: 0.1, max: 10000, aliases: ['head start', 'lead', 'distance ahead'] }),
    inp('v_A', 'Speed of Achilles', 'm/s', 10, { min: 0.1, max: 100, aliases: ['achilles speed', 'runner speed', 'speed of achilles'] }),
    inp('v_T', 'Speed of the tortoise', 'm/s', 1, { min: 0.001, max: 50, aliases: ['tortoise speed', 'speed of the tortoise'] }),
    inp('tau_f', 'Fatigue time constant of Achilles (used when speeds are not constant)', 's', 20, { min: 1, max: 10000, aliases: ['fatigue', 'tiring'] }),
    inp('ell_min', 'Smallest meaningful length (used when space is not infinitely divisible)', 'm', 0.001, { min: 1e-9, max: 1, kind: 'hypothetical', aliases: ['smallest length', 'minimum length', 'grain of space'] }),
    inp('n_st', 'Stages of Zeno\'s construction to evaluate', '1', 30, { min: 2, max: 200, kind: 'numerical', aliases: ['stages', 'steps', 'terms'] }),
  ],
  assumptions: [
    asm('limit_exists', 'An infinite series of positive terms may have a finite sum, namely the limit of its partial sums.', { why: 'Standard analysis since Cauchy; the premise Zeno\'s argument tacitly denies', alt: 'Zeno\'s hidden premise is adopted instead: infinitely many tasks cannot be completed, so no catch-up time is asserted even though every partial sum stays below a fixed bound.' }),
    asm('const_speed', 'Both runners move at constant speed.', { why: 'The classical statement', alt: 'Achilles tires: his speed decays exponentially with the stated time constant, so he covers only a finite distance and may never catch the tortoise.' }),
    asm('continuum', 'Space and time are infinitely divisible.', { why: 'Needed for the construction to have infinitely many stages', alt: 'Below a smallest length the stages are no longer distinct; the construction ends after finitely many stages.' }),
  ],
  symbols: { r_v: ['Speed ratio', '1'], tau_k: ['Duration of stage k', 's'], k_i: ['Stage index', '1'], t_n: ['Elapsed time after n stages', 's'], t_c: ['Catch-up time', 's'], t_sup: ['Least upper bound of the partial sums', 's'], x_c: ['Catch-up position', 'm'], x_A: ['Position of Achilles', 'm'], x_T: ['Position of the tortoise', 'm'], t: ['Time', 's'], t_k: ['Time at the start of a stage', 's'], t_next: ['Time at the end of a stage', 's'], n_fin: ['Number of distinct stages', '1'] },
  equations: a => [
    eq('ratio', 'Speed ratio', 'r_v', 'v_T/v_A', { kind: 'definition' }),
    ...(a.const_speed ? [
      eq('stage', 'Duration of stage k', 'tau_k', 'd_0*r_v^k_i/v_A', { kind: 'derived', origin: 'Uniform motion: each stage covers the previous gap', needs: ['const_speed'] }),
      eq('part', 'Elapsed time after n stages', 't_n', 'd_0*(1 - r_v^n_st)/(v_A*(1 - r_v))', { kind: 'derived', origin: 'Sum of a finite geometric progression', needs: ['const_speed'], ...(a.continuum ? {} : { exportable: false, note: 'When the construction ends at the smallest length, the solver sums only the stages actually completed, which may be fewer than the number requested.' }) }),
      a.limit_exists
        ? eq('lim', 'Catch-up time (limit of the partial sums)', 't_c', 'd_0/(v_A - v_T)', { kind: 'derived', origin: 'Limit of the geometric series; identical to the kinematic solution', needs: ['limit_exists', 'const_speed'] })
        : eq('lim', 'Least upper bound of the partial sums', 't_sup', 'd_0/(v_A - v_T)', { kind: 'derived', origin: 'Every partial sum is smaller; whether the bound is attained is the point in dispute', needs: ['const_speed'] }),
      ...(a.limit_exists ? [eq('xc', 'Catch-up position', 'x_c', 'v_A*t_c', { kind: 'derived', origin: 'Uniform motion', needs: ['limit_exists', 'const_speed'] })] : []),
    ] : [
      eq('xa', 'Position of a tiring Achilles', 'x_A', 'v_A*tau_f*(1 - exp(-t/tau_f))', { kind: 'closure', origin: 'Exponentially decaying speed, integrated' }),
      eq('xt', 'Position of the tortoise', 'x_T', 'd_0 + v_T*t', { kind: 'law', origin: 'Uniform motion' }),
      eq('rec', 'Stage recursion', 't_next', '-tau_f*ln(1 - (d_0 + v_T*t_k)/(v_A*tau_f))', { kind: 'derived', origin: 'Time for Achilles to reach the tortoise\'s previous position' }),
    ]),
    ...(a.continuum ? [] : [eq('nfin', 'Number of stages longer than the smallest length', 'n_fin', 'ln(d_0/ell_min)/ln(v_A/v_T)', { kind: 'hypothesis', origin: 'Gap d₀ rᵏ compared with the smallest length', exportable: false, note: 'The solver reports a whole number of stages, rounding this value up.' })]),
  ],
  derivation: a => [
    { text: 'In stage 0 Achilles runs the head start d₀, taking d₀/v_A. Meanwhile the tortoise advances by the fraction r = v_T/v_A of that distance, which becomes the gap for the next stage.', tex: 'g_k = d_0\\,r^k,\\qquad \\tau_k = \\frac{d_0\\,r^k}{v_A},\\qquad r = \\frac{v_T}{v_A}' },
    { text: 'The time elapsed after n stages is a finite geometric sum.', tex: 't_n = \\sum_{k=0}^{n-1}\\tau_k = \\frac{d_0}{v_A}\\,\\frac{1-r^n}{1-r}' },
    a.limit_exists
      ? { text: 'For r < 1 the partial sums increase and are bounded, so they converge. The limit is the catch-up time, the same value obtained by equating the two positions directly.', tex: 't_c = \\lim_{n\\to\\infty} t_n = \\frac{d_0}{v_A - v_T},\\qquad x_c = v_A t_c = \\frac{d_0}{1-r}' }
      : { text: 'Every partial sum is smaller than d₀/(v_A − v_T). If one denies that infinitely many stages can be completed, the bound is approached but the argument declines to say it is reached.', tex: 't_n < \\frac{d_0}{v_A - v_T}\\quad\\text{for every } n' },
    { text: 'If the tortoise is at least as fast (r ≥ 1) the gaps do not shrink, the partial sums grow without bound and no catch-up occurs: Zeno\'s conclusion is then true for a physical reason.', tex: 'r \\ge 1 \\;\\Rightarrow\\; t_n \\to \\infty' },
    ...(a.const_speed ? [] : [{ text: 'A runner whose speed decays as v_A e^{−t/τ} covers at most v_A τ. Catch-up requires his position curve to cross the tortoise\'s straight line.', tex: 'x_A(t) = v_A\\tau\\left(1-e^{-t/\\tau}\\right),\\qquad x_T(t) = d_0 + v_T t' }]),
  ],
  solve(v, a) {
    const r = v.v_T / v.v_A, n = int(v.n_st, 2, 400), tau = v.tau_f, warnings = [];
    const xA = t => (a.const_speed ? v.v_A * t : v.v_A * tau * (1 - Math.exp(-t / tau)));
    const tA = x => (a.const_speed ? x / v.v_A : (x < v.v_A * tau ? -tau * Math.log(1 - x / (v.v_A * tau)) : Infinity));
    const xT = t => v.d_0 + v.v_T * t;
    // true meeting time from kinematics
    let tc = Infinity;
    if (a.const_speed) { if (r < 1) tc = v.d_0 / (v.v_A - v.v_T); }
    else if (v.v_A > v.v_T) {
      const tm = tau * Math.log(v.v_A / v.v_T), f = t => xA(t) - xT(t);
      if (f(tm) >= 0) tc = N.bisect(f, 0, tm, 1e-14);
    }
    const catches = Number.isFinite(tc);
    // Zeno's stages
    const ts = [0], gaps = [v.d_0];
    let ended = '';
    for (let k = 0; k < n; k++) {
      const tn = tA(xT(ts[k]));
      if (!Number.isFinite(tn)) { ended = 'unreachable'; break; }
      ts.push(tn); gaps.push(xT(tn) - xA(tn));
      if (!a.continuum && gaps[gaps.length - 1] < v.ell_min) { ended = 'grain'; break; }
    }
    const K = ts.length - 1, tn = ts[K];
    const nFin = !a.continuum && catches && a.const_speed ? Math.max(1, Math.ceil(Math.log(v.d_0 / v.ell_min) / Math.log(1 / r))) : NaN;
    if (!catches) warnings.push(a.const_speed ? 'The tortoise is at least as fast as Achilles: the gaps do not shrink, the series diverges and there is no catch-up.' : 'Achilles tires before closing the gap: he never reaches the tortoise.');
    if (ended === 'unreachable') warnings.push(`After ${K} stage(s) the tortoise is beyond the greatest distance a tiring Achilles can cover.`);
    const tEnd = catches ? 1.3 * tc : Math.max(tn, 3 * v.d_0 / v.v_A);
    const tt = N.linspace(0, tEnd, 160), idx = ts.map((_, i) => i);
    const tcText = !catches ? 'Never: no catch-up' : !a.limit_exists ? `Not asserted: completion of infinitely many stages is denied (every partial sum is below ${lab(tc, 's', 6)})` : undefined;
    const closed = a.const_speed && r < 1 ? v.d_0 / v.v_A * (1 - Math.pow(r, K)) / (1 - r) : NaN;
    const checks = [];
    if (Number.isFinite(closed)) checks.push(check('Summed stages against the closed-form partial sum', (tn - closed) / closed, 1e-9, 'Geometric progression'));
    if (catches) checks.push(check('Partial sums never exceed the catch-up time', Math.max(0, tn - tc) / tc, 1e-9, 'Monotone bounded sequence'));
    if (catches) checks.push(check('Positions coincide at the catch-up time', (xA(tc) - xT(tc)) / xT(tc), 1e-9, 'Kinematic solution'));
    if (!checks.length) checks.push(check('Gaps do not shrink when there is no catch-up', a.const_speed ? Math.max(0, gaps[0] - gaps[K]) / gaps[0] : 0, 1e-9, 'Each stage leaves a gap at least as large as the last'));
    return {
      scalars: [
        scalar('r_v', 'Speed ratio, tortoise to Achilles', r, '1'),
        scalar('t_c', 'Catch-up time', catches && a.limit_exists ? tc : (catches ? NaN : Infinity), 's', { text: tcText }),
        scalar('x_c', 'Catch-up position', catches && a.limit_exists ? xA(tc) : (catches ? NaN : Infinity), 'm', { text: !catches ? 'None' : !a.limit_exists ? 'Not asserted' : undefined }),
        scalar('t_sup', 'Least upper bound of the partial sums', catches ? tc : Infinity, 's', { text: catches ? undefined : 'Unbounded' }),
        scalar('t_n', `Elapsed time after ${K} stage(s)`, tn, 's'),
        scalar('gap_n', `Remaining gap after ${K} stage(s)`, gaps[K], 'm'),
        scalar('t_rem', 'Time still to run after those stages', catches ? tc - tn : Infinity, 's', { text: catches ? undefined : 'Unbounded' }),
        scalar('n_done', 'Stages evaluated', K, '1'),
        scalar('n_fin', 'Number of distinct stages', Number.isFinite(nFin) ? nFin : Infinity, '1', { text: Number.isFinite(nFin) ? undefined : (a.continuum && catches ? 'Infinitely many' : !catches ? 'Not applicable' : `${K} evaluated`) }),
      ],
      series: [
        line('partial-sums', 'Elapsed time after each stage', 'Stage', '–', idx, [{ label: 'Partial sum of stage durations', data: ts }, ...(catches ? [{ label: a.limit_exists ? 'Catch-up time (limit)' : 'Upper bound', data: idx.map(() => tc), dash: true }] : [])], 'Time', 's'),
        line('gap', 'Gap remaining after each stage', 'Stage', '–', idx, [{ label: 'Gap', data: gaps.map(q => Math.max(q, 1e-300)) }], 'Gap', 'm', { logy: true }),
        line('worldlines', 'Positions against time', 'Time', 's', tt, [{ label: 'Achilles', data: tt.map(xA) }, { label: 'Tortoise', data: tt.map(xT) }], 'Position', 'm'),
      ],
      checks, warnings,
    };
  },
  benchmarks(v, a) {
    const on = { limit_exists: true, const_speed: true, continuum: true };
    const r = this.solve({ ...v, d_0: 100, v_A: 10, v_T: 1, n_st: 30 }, on), out = [];
    out.push(bench('Catch-up time for a 100 m lead at 10 m/s against 1 m/s', val(r, 't_c'), 100 / 9, 'Kinematics: d₀/(v_A − v_T)', 1e-12));
    out.push(bench('Catch-up position', val(r, 'x_c'), 1000 / 9, 'Sum of the geometric series d₀/(1 − r)', 1e-12));
    out.push(bench('Thirty-stage partial sum', val(r, 't_n'), 10 * (1 - 1e-30) / 0.9, 'Finite geometric sum', 1e-12));
    const f = this.solve({ ...v, d_0: 100, v_A: 10, v_T: 1, tau_f: 1e9 }, { ...on, const_speed: false });
    out.push(bench('Tiring runner with a very long fatigue time recovers the constant-speed result', val(f, 't_c'), 100 / 9, 'Limit τ → ∞', 1e-6));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const r = Math.min(0.95, v.v_T / v.v_A), x0 = 70, x1 = 570, span = x1 - x0;
    const pts = []; let x = 0;
    for (let k = 0; k < 6; k++) { pts.push(x); x += (1 - r) * Math.pow(r, k); }
    return svg(`
      ${S.line(x0, 200, x1, 200)}
      ${pts.map((p, i) => `${S.line(x0 + p * span, 190, x0 + p * span, 210)}${S.text(x0 + p * span, 228, i === 0 ? 'start' : `stage ${i}`, 'd-text d-small')}`).join('')}
      ${S.line(x1, 180, x1, 220, 'd-line d-hazard')} ${S.text(x1, 170, 'catch-up point', 'd-text d-small')}
      ${S.circle(x0, 150, 9)} ${S.text(x0, 130, 'Achilles')} ${S.arrow(x0 + 14, 150, x0 + 84, 150)} ${S.text(x0 + 50, 142, lab(v.v_A, 'm/s'), 'd-text d-small')}
      ${S.rect(x0 + (1 - r) * span - 10, 143, 20, 14)} ${S.text(x0 + (1 - r) * span, 130, 'tortoise')} ${S.arrow(x0 + (1 - r) * span + 14, 150, x0 + (1 - r) * span + 44, 150)}
      ${S.dim(x0, 270, x0 + (1 - r) * span, 270, `head start ${lab(v.d_0, 'm')}`)}
      ${S.text(320, 50, a.const_speed ? `Each stage is shorter than the last by the factor r = ${lab(v.v_T / v.v_A)}` : 'Achilles slows as he tires')}
      ${S.text(320, 320, v.v_T < v.v_A ? `Infinitely many stages, total time ${lab(v.d_0 / (v.v_A - v.v_T), 's')}` : 'The tortoise is not slower: the stages do not shrink', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Inf', text: 'The pursuit consists of infinitely many successive stages' }, { k: 'Conv', text: 'The durations of the stages have a finite sum' }, { k: 'Catch', text: 'Achilles catches the tortoise in a finite time' }, { k: 'NoSuper', text: 'Infinitely many tasks cannot be completed in a finite time' }],
    premises: ['Inf', 'Conv', 'Conv -> Catch', '(Inf & NoSuper) -> ~Catch'],
    conclusion: '~NoSuper',
  },
  philosophy: [
    'Zeno\'s argument is valid: if the pursuit has infinitely many stages and no infinite sequence of tasks can be completed, Achilles never arrives. The standard reply accepts the first premise and rejects the second, pointing to the convergent series as a consistent account of how infinitely many intervals fit into a finite one.',
    'Whether the mathematics settles the matter is contested. The limit of the partial sums is by definition the sum, but a critic may ask whether that definition describes what a runner does. The literature on supertasks, beginning with Thomson\'s lamp, examines which infinite sequences of acts are coherent and what state obtains at their completion.',
    'A different response denies the infinite divisibility of space or time, so that the construction ends after finitely many stages. That view is consistent as well, and whether physical space is a continuum is an empirical question the paradox does not decide.',
  ],
  experiment: {
    objective: 'Time a faster body overtaking a slower one and compare the measured meeting time and place with the limit of the geometric series.',
    apparatus: ['Two constant-speed carts or motorised toys on parallel straight tracks', 'A measured head start marked on the track', 'Alternatively a spreadsheet or program that tabulates the successive stages'],
    instruments: [{ name: 'Video camera with a frame counter', measures: 'Positions of both bodies against time', range: '0–60 s', resolution: '1/30 s' }, { name: 'Tape measure', measures: 'Head start and meeting point', range: '0–20 m', resolution: '1 mm' }, { name: 'Light gates', measures: 'Speeds of each body', range: '0.01–5 m/s', resolution: '±1 %' }],
    procedure: ['Measure the two speeds separately over a known distance.', 'Release the faster body when the slower one passes the head-start mark.', 'From the video read the time and place at which the two are level.', 'Tabulate the stage durations d₀ rᵏ/v_A, form the partial sums and compare their limit with the measurement.'],
    controls: ['Repeat with the speeds exchanged: no meeting should occur.', 'Vary the head start; the meeting time should scale in proportion.'],
    signatures: ['Meeting time equal to d₀/(v_A − v_T) within measurement uncertainty', 'Successive gaps falling by the constant factor v_T/v_A', 'Partial sums approaching the measured time from below'],
    safety: [],
  },
  falsify: ['A measured overtaking time that differs from d₀/(v_A − v_T) beyond experimental uncertainty for bodies verified to move uniformly.', 'A slower pursuer overtaking, or a faster one failing to, under uniform motion.'],
  alternatives: [
    { name: 'Standard analysis', text: 'The sum of an infinite series is the limit of its partial sums. The stage durations sum to a finite time, so the infinitely many stages are completed.' },
    { name: 'Finitism about tasks', text: 'A completed infinity of acts is rejected as incoherent. The description in stages is then held to be a misdescription of motion, which is not composed of acts at all.' },
    { name: 'Discrete space and time', text: 'If intervals cannot be divided below some smallest size the regress stops after finitely many stages and no infinite sum is required.' },
    { name: 'Non-standard analysis', text: 'Infinitesimals give an alternative rigorous account in which the sum over a hyperfinite number of stages is infinitely close to the standard limit.' },
    { name: 'A tortoise that is not slower', text: 'If the tortoise moves at least as fast as Achilles the stage durations do not decrease, their sum diverges and Achilles never draws level. Zeno\'s conclusion is then correct, for kinematic and not logical reasons.' },
  ],
  limits: 'One-dimensional motion of point bodies. With constant speeds the catch-up time is exact; the fatigue variant uses a simple exponential decay of speed. The number of stages evaluated numerically is finite, and stage durations fall below floating-point resolution after roughly 16/log₁₀(1/r) stages.',
  numerics: { method: 'Direct summation of stage durations compared with the closed-form geometric sum; bisection for the meeting time of a tiring runner', resolution: 'n_st' },
  extensions: ['The dichotomy, arrow and stadium paradoxes', 'Thomson\'s lamp and other supertasks without a defined final state', 'Relativistic pursuit at speeds near that of light'],
};

// ================================================================== 3. Maxwell's demon (Szilard engine)
const maxwellsDemon = {
  id: 'maxwells-demon',
  title: 'Maxwell\'s demon and the Szilard engine',
  module: 1, klass: ['II', 'I'], domains: ['thermal', 'logic'],
  keywords: ['maxwell\'s demon', 'maxwells demon', 'maxwell demon', 'szilard engine', 'szilard', 'landauer', 'erasure', 'information engine', 'demon', 'second law', 'information thermodynamics', 'bit'],
  summary: 'A one-molecule heat engine operated by a measuring agent: work extracted per bit, the entropy cost of resetting the agent\'s memory, and the net entropy balance.',
  background: [
    'Maxwell imagined a being able to observe individual molecules and sort them without doing work, apparently lowering the entropy of a gas. Szilard reduced the idea to an engine containing a single molecule: the demon measures which half of a box the molecule occupies, inserts a partition and lets the molecule push it back isothermally, extracting k_B T ln 2 of work from a single heat bath in each cycle.',
    'The modern resolution, due to Landauer and Bennett, locates the compensating entropy in the demon\'s memory. Measurement can in principle be performed reversibly, but to operate in a cycle the demon must reset its one-bit record, and erasing a bit in an environment at temperature T dissipates at least k_B T ln 2 of heat. With an imperfect measurement the extractable work falls to k_B T times the mutual information between record and molecule. Both the erasure bound and the information-to-work conversion have been confirmed in experiments on colloidal particles.',
  ],
  phenomena: ['Isothermal expansion of a one-molecule gas', 'Measurement and feedback', 'Logically irreversible erasure', 'Mutual information as a thermodynamic resource'],
  laws: ['second', 'landauer', 'energy'],
  refs: ['Szilard, L. (1929). Über die Entropieverminderung in einem thermodynamischen System bei Eingriffen intelligenter Wesen. Zeitschrift für Physik 53, 840–856.', 'Landauer, R. (1961). Irreversibility and heat generation in the computing process. IBM Journal of Research and Development 5, 183–191.', 'Bennett, C. H. (1982). The thermodynamics of computation — a review. International Journal of Theoretical Physics 21, 905–940.', 'Sagawa, T. & Ueda, M. (2010). Generalized Jarzynski equality under nonequilibrium feedback control. Physical Review Letters 104, 090602.', 'Toyabe, S., Sagawa, T., Ueda, M., Muneyuki, E. & Sano, M. (2010). Experimental demonstration of information-to-energy conversion and validation of the generalized Jarzynski equality. Nature Physics 6, 988–992.', 'Bérut, A. et al. (2012). Experimental verification of Landauer\'s principle linking information and thermodynamics. Nature 483, 187–189.', 'Leff, H. S. & Rex, A. F. (eds) (2003). Maxwell\'s Demon 2: Entropy, Classical and Quantum Information, Computing. Institute of Physics Publishing.'],
  inputs: [
    inp('T', 'Temperature of the heat bath', 'K', 300, { min: 1, max: 1000, aliases: ['temperature', 'bath temperature'] }),
    inp('r_b', 'Engine cycles (bits measured) per second', '1/s', 1e6, { min: 1, max: 1e15, aliases: ['bits per second', 'cycles per second', 'rate', 'molecules per second'] }),
    inp('eps_m', 'Measurement error probability', '1', 0, { min: 0, max: 0.5, aliases: ['error probability', 'measurement error', 'error rate'] }),
    inp('eta_w', 'Fraction of the ideal work recovered (used when the expansion is not quasi-static)', '1', 0.8, { min: 0.01, max: 1, aliases: ['work efficiency', 'recovered fraction'] }),
  ],
  assumptions: [
    asm('landauer', 'Resetting one bit of the demon\'s memory dissipates at least k_B T ln 2 of heat.', { why: 'Landauer\'s principle, a consequence of the second law for logically irreversible operations', alt: 'Hypothetical: erasure is free. The cycle then lowers the total entropy and the second law appears to be violated.', affects: ['Q_er', 'dS_net'] }),
    asm('rev_meas', 'The measurement itself can be performed reversibly, at no entropy cost.', { why: 'Bennett\'s analysis of reversible measurement', alt: 'Each measurement is taken to generate k_B ln 2 of entropy, as Szilard and Brillouin supposed.', affects: ['dS_net'] }),
    asm('quasi_static', 'The expansion is quasi-static and isothermal, so the full available work is extracted.', { why: 'Reversible limit', alt: 'Only the stated fraction of the ideal work is recovered in a finite-time stroke.', affects: ['W_x'] }),
  ],
  symbols: { I_m: ['Information gained per measurement', '1'], W_x: ['Work extracted per cycle', 'J'], Q_er: ['Heat dissipated in resetting the memory', 'J'], dS_net: ['Net entropy change of bath, engine and memory per cycle', 'J/K'], P_x: ['Gross power extracted', 'W'], W_net: ['Net work per cycle after resetting the memory', 'J'] },
  equations: a => [
    eq('info', 'Information gained per measurement (nats)', 'I_m', 'ln(2) + eps_m*ln(eps_m) + (1 - eps_m)*ln(1 - eps_m)', { kind: 'definition', origin: 'Mutual information of a binary symmetric channel with equiprobable input' }),
    eq('work', 'Work extracted per cycle', 'W_x', a.quasi_static ? 'k_B*T*I_m' : 'eta_w*k_B*T*I_m', { kind: 'law', origin: 'Szilard (1929); feedback bound of Sagawa & Ueda (2010)', needs: a.quasi_static ? ['quasi_static'] : [] }),
    a.landauer
      ? eq('erase', 'Minimum heat to reset one bit', 'Q_er', 'k_B*T*ln(2)', { kind: 'law', origin: 'Landauer (1961)', needs: ['landauer'] })
      : eq('erase', 'Heat to reset one bit (hypothetical free erasure)', 'Q_er', '0*k_B*T', { kind: 'hypothesis', origin: 'Counterfactual premise contradicting Landauer\'s principle' }),
    eq('ent', 'Net entropy change per cycle', 'dS_net', a.rev_meas ? '(Q_er - W_x)/T' : '(Q_er - W_x)/T + k_B*ln(2)', { kind: 'law', origin: 'Entropy bookkeeping for bath, engine and memory over a closed cycle' }),
    eq('net', 'Net work per cycle', 'W_net', a.rev_meas ? 'W_x - Q_er' : 'W_x - Q_er - k_B*T*ln(2)', { kind: 'law', origin: 'First law over a closed cycle' }),
    eq('pow', 'Gross power extracted', 'P_x', 'r_b*W_x', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'A single molecule in a box of volume V exerts a mean pressure k_B T/V. After the demon learns which half it occupies, a partition is inserted and the molecule expands isothermally from V/2 to V.', tex: 'W = \\int_{V/2}^{V}\\frac{k_B T}{V\'}\\,dV\' = k_B T\\ln 2' },
    { text: 'If the measurement is wrong with probability ε the best feedback protocol recovers only k_B T times the mutual information between record and molecule.', tex: 'W = k_B T\\,I,\\qquad I = \\ln 2 + \\varepsilon\\ln\\varepsilon + (1-\\varepsilon)\\ln(1-\\varepsilon)' },
    { text: 'The work is drawn as heat from the bath, lowering its entropy by W/T. The engine returns to its initial state. The demon\'s one-bit record, however, is equally likely to read left or right and must be reset before the next cycle.', tex: '\\Delta S_{bath} = -\\frac{W}{T}' },
    a.landauer
      ? { text: 'Resetting a bit is logically irreversible and releases at least k_B T ln 2 of heat to the bath. The total entropy change of the cycle is then never negative.', tex: '\\Delta S_{net} = k_B\\ln 2 - \\frac{W}{T} = k_B\\left[\\ln 2 - I\\right] \\ge 0' }
      : { text: 'If erasure were free nothing would compensate the entropy removed from the bath, and each cycle would lower the total entropy.', tex: '\\Delta S_{net} = -\\frac{W}{T} = -k_B\\,I < 0' },
    a.landauer
      ? { text: 'The second law is therefore preserved by exactly one premise in the bookkeeping: the cost of forgetting.', tex: 'W_{net} = W - Q_{erase} \\le 0' }
      : { text: 'Without the cost of forgetting the cycle would deliver net work from a single bath. The second law is preserved by exactly that one premise in the bookkeeping.', tex: 'W_{net} = W - Q_{erase} = W > 0' },
  ],
  solve(v, a) {
    const kB = C.k_B, kT = kB * v.T, I = Math.LN2 - H2(v.eps_m), eta = a.quasi_static ? 1 : v.eta_w;
    const W = eta * kT * I, Qer = a.landauer ? kT * Math.LN2 : 0, Sm = a.rev_meas ? 0 : kB * Math.LN2;
    const dS = (Qer - W) / v.T + Sm, Wnet = W - Qer - v.T * Sm, viol = dS < -1e-12 * kB;
    const es = N.linspace(0, 0.5, 101), Ts = N.linspace(1, 1000, 80);
    const dSof = (e, land) => ((land ? Math.LN2 : 0) - eta * (Math.LN2 - H2(e))) + (a.rev_meas ? 0 : Math.LN2);
    const warnings = [];
    if (viol) warnings.push('With free erasure the cycle converts heat from a single bath into work with no compensating entropy increase. This is the apparent violation of the second law; it follows from the hypothetical premise, not from physics.');
    return {
      scalars: [
        scalar('I_m', 'Information gained per measurement (nats)', I, '1'),
        scalar('I_bit', 'Information gained per measurement (bits)', I / Math.LN2, '1'),
        scalar('W_x', 'Work extracted per cycle', W, 'J', { show: 'eV' }),
        scalar('w_kT', 'Work extracted per cycle in units of k_B T', W / kT, '1'),
        scalar('Q_er', 'Heat dissipated in resetting the memory', Qer, 'J', { show: 'eV', status: a.landauer ? undefined : 'hypothetical' }),
        scalar('W_net', 'Net work per cycle', Wnet, 'J', { show: 'eV', status: a.landauer ? undefined : 'hypothetical' }),
        scalar('dS_net', 'Net entropy change per cycle', dS, 'J/K', { status: a.landauer ? undefined : 'hypothetical' }),
        scalar('s_kB', 'Net entropy change per cycle in units of k_B', dS / kB, '1'),
        scalar('P_x', 'Gross power extracted', v.r_b * W, 'W'),
        scalar('P_net', 'Net power after resetting the memory', v.r_b * Wnet, 'W', { status: a.landauer ? undefined : 'hypothetical' }),
        scalar('S_dot', 'Net entropy production rate', v.r_b * dS, 'W/K'),
        scalar('viol', 'Second law', viol ? 1 : 0, '1', { text: viol ? 'Apparently violated (hypothetical premise)' : 'Respected', note: viol ? 'expected with free erasure: this is the paradox, resolved by charging k_B T ln 2 for resetting the memory' : undefined }),
      ],
      series: [
        line('work-vs-error', 'Work per cycle against measurement error', 'Error probability', '–', es, [{ label: 'Work extracted', data: es.map(e => eta * (Math.LN2 - H2(e)) / Math.LN2) }, { label: 'Cost of resetting the memory', data: es.map(() => (a.landauer ? 1 : 0)), dash: true }], 'Energy', 'k_B T ln 2'),
        line('entropy-vs-error', 'Net entropy change per cycle', 'Error probability', '–', es, [{ label: 'With Landauer\'s principle', data: es.map(e => dSof(e, true)) }, { label: 'With free erasure (hypothetical)', data: es.map(e => dSof(e, false)), dash: true }, { label: 'Zero', data: es.map(() => 0), dash: true }], 'Entropy change', 'k_B'),
        line('power-vs-T', 'Gross power against bath temperature', 'Temperature', 'K', Ts, [{ label: 'Gross power', data: Ts.map(t => v.r_b * eta * kB * t * I) }], 'Power', 'W'),
      ],
      checks: [
        // with free erasure a negative balance is the paradox itself, the expected outcome of the counterfactual premise; what must
        // then hold is that the deficit never exceeds the omitted erasure cost, so that Landauer's principle alone restores the law
        a.landauer ? check('Second law: net entropy change per cycle is not negative', Math.min(0, dS / kB), 1e-12, 'Bath, engine and memory together')
          : check('Free erasure (hypothetical): the entropy deficit per cycle does not exceed the omitted erasure cost k_B ln 2', Math.min(0, dS / kB + Math.LN2), 1e-12, `${viol ? `The balance is ${(dS / kB).toPrecision(4)} k_B per cycle: the apparent violation of the second law that the thought experiment is about, expected under this premise` : 'The balance is not negative here'}; charging k_B ln 2 for the reset (Landauer's principle) makes it ${(dS / kB + Math.LN2).toPrecision(4)} k_B ≥ 0`),
        check('Extracted work does not exceed k_B T times the information gained', Math.max(0, W / kT - I), 1e-12, 'Sagawa–Ueda bound'),
        check('Information lies between zero and one bit', I < -1e-15 || I > Math.LN2 + 1e-15 ? 1 : 0, 0, '0 ≤ I ≤ ln 2'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const on = { landauer: true, rev_meas: true, quasi_static: true }, out = [];
    const r = this.solve({ ...v, T: 300, eps_m: 0 }, on);
    out.push(bench('Work per bit at 300 K', val(r, 'W_x'), 1.380649e-23 * 300 * Math.LN2, 'k_B T ln 2 with the exact SI value of k_B', 1e-12));
    out.push(bench('Net entropy change of the ideal cycle', val(r, 's_kB'), 0, 'Reversible limit: erasure exactly compensates extraction', 1e-12));
    const h = this.solve({ ...v, T: 300, eps_m: 0.5 }, on);
    out.push(bench('Work with an uninformative measurement', val(h, 'w_kT'), 0, 'Zero mutual information at ε = 1/2', 1e-12));
    const f = this.solve({ ...v, T: 300, eps_m: 0 }, { ...on, landauer: false });
    out.push(bench('Entropy change with free erasure', val(f, 's_kB'), -Math.LN2, 'Hypothetical: −k_B ln 2 per cycle', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(90, 110, 260, 130)} ${S.line(220, 110, 220, 240, 'd-line d-hazard')} ${S.text(220, 100, 'partition / piston', 'd-text d-small')}
      ${S.circle(150, 180, 8)} ${S.arrow(160, 174, 190, 156)} ${S.text(150, 215, 'one molecule', 'd-text d-small')}
      ${S.arrow(226, 175, 300, 175)} ${S.text(290, 162, 'W', 'd-text')}
      ${S.rect(90, 262, 260, 34)} ${S.text(220, 284, `heat bath, T = ${lab(v.T, 'K')}`)}
      ${S.arrow(220, 262, 220, 244)} ${S.text(236, 256, 'Q', 'd-text d-small', 'start')}
      ${S.rect(430, 110, 140, 60)} ${S.text(500, 136, 'demon')} ${S.text(500, 156, 'memory: 1 bit', 'd-text d-small')}
      ${S.arrow(430, 140, 354, 140)} ${S.text(392, 130, 'measure', 'd-text d-small')}
      ${S.arrow(500, 170, 500, 262)} ${S.text(510, 220, a.landauer ? 'erase: k_B T ln 2' : 'erase: free (hypothetical)', a.landauer ? 'd-text d-small' : 'd-text d-small d-hazard', 'start')}
      ${S.line(350, 279, 600, 279)} ${S.line(500, 262, 500, 279)}
      ${S.text(320, 50, `Work per cycle ${lab((a.quasi_static ? 1 : v.eta_w) * C.k_B * v.T * (Math.LN2 - H2(v.eps_m)), 'J')}`)}
      ${S.text(320, 335, 'One cycle: measure, insert partition, expand, reset the memory', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Extract', text: 'Each cycle extracts work from a single heat bath using one bit of information' }, { k: 'FreeErase', text: 'The demon\'s memory can be reset at no entropy cost' }, { k: 'Violation', text: 'The total entropy decreases in a cycle' }, { k: 'SecondLaw', text: 'The second law of thermodynamics holds' }],
    premises: ['Extract', '(Extract & FreeErase) -> Violation', 'Violation <-> ~SecondLaw', 'SecondLaw'],
    conclusion: '~FreeErase',
  },
  philosophy: [
    'The demon tests whether the second law is a law about matter or about what can be known of it. The resolution by way of information makes entropy partly a statement about an observer\'s record, yet ties that record to a physical memory with physical costs.',
    'The argument can be read in two directions. Taking the second law as secure, one infers Landauer\'s principle; taking Landauer\'s principle as independently established, one explains why the demon fails. Critics have pointed out that the first reading presupposes the law it claims to defend, and the status of the principle as an independent result remains a matter of debate.',
    'The thought experiment also shows how a paradox can be dissolved by completing the system description. The demon appeared to violate a conservation-like principle only while its own state was left out of the accounts.',
  ],
  experiment: {
    objective: 'Measure the work extracted from a single Brownian particle under feedback control and the heat dissipated when one bit stored in the particle\'s position is erased.',
    apparatus: ['A micrometre-sized colloidal bead in water at controlled temperature', 'A double-well optical trap or a tilted periodic electric potential that can be reshaped on demand', 'Real-time particle tracking with a feedback loop to the trap controller'],
    instruments: [{ name: 'High-speed camera or quadrant photodiode', measures: 'Bead position', range: '±2 µm', resolution: '≈ 1 nm at kHz bandwidth' }, { name: 'Calibrated trap stiffness and potential profile', measures: 'Force on the bead, hence work and heat along each trajectory', range: '0–10 k_B T', resolution: '≈ 0.05 k_B T after averaging' }, { name: 'Thermometer on the sample cell', measures: 'Bath temperature', range: '280–320 K', resolution: '±0.1 K' }],
    procedure: ['Calibrate the potential from the equilibrium position histogram.', 'Feedback run: measure which well the bead occupies, raise the barrier behind it and lower the potential ahead; integrate the work along each trajectory.', 'Erasure run: starting from either well with equal probability, drive the bead to a chosen well by lowering the barrier and tilting; integrate the dissipated heat.', 'Repeat for decreasing protocol speed and extrapolate to the quasi-static limit.'],
    controls: ['Runs without feedback, in which no net work should be extracted', 'Deliberately degraded measurements to vary the error probability', 'Reversal of the protocol to test the fluctuation relations'],
    signatures: ['Mean extracted work approaching but not exceeding k_B T times the mutual information', 'Mean erasure heat approaching k_B T ln 2 from above as the protocol is slowed', 'Net entropy production of the combined cycle not negative'],
    safety: ['Laser safety for the optical trap: enclosed beam path and appropriate eyewear'],
  },
  falsify: ['A reproducible cyclic process that extracts net work from a single heat bath after all memory has been restored to its initial state.', 'Mean heat of erasure significantly below k_B T ln 2 per bit in the quasi-static limit for a symmetric, equiprobable bit.', 'Mean extracted work exceeding k_B T times the measured mutual information.'],
  alternatives: [
    { name: 'Measurement cost (Szilard, Brillouin)', text: 'The entropy is generated in acquiring the information, for example by the photons needed to see the molecule. Bennett showed that measurement can be made reversible, moving the unavoidable cost to erasure; the measurement-cost view remains adequate for many practical detectors.' },
    { name: 'Landauer–Bennett erasure', text: 'Measurement and feedback are reversible; the irreducible cost arises when the record is reset. This is the account implemented here by default.' },
    { name: 'Demon without erasure', text: 'A demon with an unbounded blank memory can run indefinitely, but its filling memory is a growing entropy store: the tape is a thermodynamic resource being consumed.' },
    { name: 'Critiques of the information-theoretic exorcism', text: 'Some authors argue that Landauer\'s principle is derived from the second law and therefore cannot independently rescue it; on this view the demon is excluded by statistical mechanics directly, through fluctuations in any physical sorting mechanism.' },
  ],
  limits: 'Classical one-molecule engine with a symmetric partition and an equiprobable binary record, in contact with a single bath. Erasure is charged at its minimum, k_B T ln 2 for the full one-bit record. The finite-time option is a single efficiency factor, not a model of dissipation. Quantum effects and correlations between successive cycles are not included.',
  numerics: { method: 'Closed-form thermodynamic bookkeeping' },
  extensions: ['Finite-time erasure with dissipation proportional to the inverse cycle time', 'Asymmetric partitions and biased bits', 'Quantum Szilard engines with indistinguishable particles', 'Autonomous demons modelled as coupled stochastic systems'],
};

// ================================================================== 4. Prisoner's dilemma
const PD_STRATS = [
  { key: 'alld', name: 'Always defect', move: () => false },
  { key: 'allc', name: 'Always co-operate', move: () => true },
  { key: 'tft', name: 'Tit for tat', move: (t, oppLast) => (t === 0 ? true : oppLast) },
  { key: 'grim', name: 'Grim trigger', move: (t, oppLast, st) => { if (t > 0 && !oppLast) st.grim = true; return !st.grim; } },
  { key: 'rand', name: 'Random', move: (t, oppLast, st, rnd, pc) => rnd() < pc, mixed: true },
];
/** Expected total scores of one iterated match, exactly: every strategy here is a finite-state machine driven by the opponent's last
 *  move, so the pair (last moves, triggered flags) is a Markov chain of at most sixteen states whose distribution is propagated
 *  round by round. No sampling is involved, so the ranking cannot be decided by the luck of a seed. */
function pdExpect(i, j, n, pay, noise, pc) {
  const intent = (k, t, oppLast, g) => { const st = { grim: g }, c = PD_STRATS[k].mixed ? pc : (PD_STRATS[k].move(t, oppLast, st) ? 1 : 0); return [c, !!st.grim]; };
  // transition table for one round from each state: [next state, probability, payoff to i, payoff to j] × 4 outcomes (the rule of every strategy is the same for all t ≥ 1)
  const table = t => { const tb = new Float64Array(16 * 16);
    for (let s = 0; s < 16; s++) { const li = !!(s & 1), lj = !!(s & 2), [ci, gi] = intent(i, t, lj, !!(s & 4)), [cj, gj] = intent(j, t, li, !!(s & 8));
      const ai = ci * (1 - noise) + (1 - ci) * noise, aj = cj * (1 - noise) + (1 - cj) * noise, base = (gi ? 4 : 0) + (gj ? 8 : 0);
      for (let o = 0; o < 4; o++) { const mi = !!(o & 1), mj = !!(o & 2), k = 16 * s + 4 * o; tb[k] = base + o; tb[k + 1] = (mi ? ai : 1 - ai) * (mj ? aj : 1 - aj); tb[k + 2] = pay(mi, mj); tb[k + 3] = pay(mj, mi); } }
    return tb; };
  let w = new Float64Array(16), nw = new Float64Array(16), ti = 0, tj = 0, tb = table(0); w[3] = 1;   // state index: li + 2·lj + 4·gi + 8·gj
  for (let t = 0; t < n; t++) { if (t === 1) tb = table(1); nw.fill(0);
    for (let s = 0; s < 16; s++) { const q = w[s]; if (q === 0) continue;
      for (let k = 16 * s; k < 16 * s + 16; k += 4) { const pr = q * tb[k + 1]; if (pr === 0) continue; ti += pr * tb[k + 2]; tj += pr * tb[k + 3]; nw[tb[k]] += pr; } }
    const sw = w; w = nw; nw = sw; }
  return { ti, tj };
}
/** One iterated match. Returns total scores and the cumulative score histories. */
function pdMatch(i, j, n, pay, rnd, noise, pc, hist = true) {
  const si = {}, sj = {}; let li = true, lj = true, ti = 0, tj = 0; const ci = [], cj = [];
  for (let t = 0; t < n; t++) {
    let mi = PD_STRATS[i].move(t, lj, si, rnd, pc), mj = PD_STRATS[j].move(t, li, sj, rnd, pc);
    if (noise > 0) { if (rnd() < noise) mi = !mi; if (rnd() < noise) mj = !mj; }
    ti += pay(mi, mj); tj += pay(mj, mi); if (hist) { ci.push(ti); cj.push(tj); } li = mi; lj = mj;
  }
  return { ti, tj, ci, cj };
}
const prisonersDilemma = {
  id: 'prisoners-dilemma',
  title: 'The prisoner\'s dilemma',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['prisoner\'s dilemma', 'prisoners dilemma', 'prisoner dilemma', 'nash equilibrium', 'tit for tat', 'defect', 'cooperate', 'co-operate', 'game theory', 'payoff matrix', 'iterated game', 'axelrod'],
  summary: 'A two-player game in which individually rational choices give a jointly worse outcome: Nash and Pareto analysis of the payoff matrix and a round-robin tournament of standard strategies in the repeated game.',
  background: [
    'Two players choose independently whether to co-operate or to defect. Each receives the reward R if both co-operate and the punishment P if both defect; a lone defector receives the temptation T and the co-operator the sucker\'s payoff S. When T > R > P > S, defection is the better reply to either choice by the other player, so mutual defection is the unique Nash equilibrium, yet both would do better under mutual co-operation.',
    'When the game is repeated between the same players, strategies can condition on past behaviour. In Axelrod\'s computer tournaments the simple reciprocal strategy tit for tat, which co-operates first and then copies the opponent\'s previous move, obtained the highest total score although it never beats any single opponent. Co-operation can be sustained as an equilibrium of the indefinitely repeated game when the probability of continuation is high enough.',
  ],
  phenomena: ['Dominant strategies', 'Nash equilibrium', 'Pareto inefficiency', 'Reciprocity in repeated interaction', 'Sensitivity of reciprocal strategies to noise'],
  laws: ['logic_nc', 'kolmogorov'],
  refs: ['Nash, J. F. (1950). Equilibrium points in n-person games. Proceedings of the National Academy of Sciences 36, 48–49.', 'Rapoport, A. & Chammah, A. M. (1965). Prisoner\'s Dilemma: A Study in Conflict and Cooperation. University of Michigan Press.', 'Axelrod, R. & Hamilton, W. D. (1981). The evolution of cooperation. Science 211, 1390–1396.', 'Axelrod, R. (1984). The Evolution of Cooperation. Basic Books.', 'Nowak, M. & Sigmund, K. (1993). A strategy of win-stay, lose-shift that outperforms tit-for-tat in the Prisoner\'s Dilemma game. Nature 364, 56–58.'],
  inputs: [
    inp('T_p', 'Temptation payoff T (defect against a co-operator)', '1', 5, { min: 0, max: 10, aliases: ['temptation', 'temptation payoff'] }),
    inp('R_p', 'Reward payoff R (mutual co-operation)', '1', 3, { min: 0, max: 10, aliases: ['reward', 'reward payoff'] }),
    inp('P_p', 'Punishment payoff P (mutual defection)', '1', 1, { min: 0, max: 10, aliases: ['punishment', 'punishment payoff'] }),
    inp('S_p', 'Sucker\'s payoff S (co-operate against a defector)', '1', 0, { min: 0, max: 10, aliases: ['sucker', 'sucker payoff'] }),
    inp('p_c', 'Co-operation probability of the random strategy', '1', 0.5, { min: 0, max: 1, aliases: ['random cooperation probability'] }),
    inp('eps_n', 'Probability that a move is executed wrongly (used when moves are noisy)', '1', 0.05, { min: 0, max: 0.5, aliases: ['noise', 'error rate', 'trembling hand'] }),
    inp('alpha_o', 'Weight each player gives to the other\'s payoff (used when players are not purely self-interested)', '1', 0.6, { min: 0, max: 1, kind: 'hypothetical', aliases: ['altruism', 'other-regarding weight'] }),
    inp('n_rounds', 'Rounds per match', '1', 200, { min: 2, max: 2000, kind: 'numerical', aliases: ['rounds', 'iterations'] }),
    inp('seed', 'Random seed', '1', 7, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('selfish', 'Each player cares only about his or her own payoff.', { why: 'The standard game-theoretic statement', alt: 'Each player adds the other\'s payoff, weighted by the stated factor, to his or her own. With enough weight mutual co-operation becomes an equilibrium and the dilemma dissolves.', affects: ['n_ne'] }),
    asm('no_noise', 'Moves are executed exactly as intended.', { why: 'Idealised play', alt: 'Each move is flipped with the stated probability. Unforgiving reciprocal strategies then fall into long runs of mutual retaliation.' }),
    asm('self_play', 'Every strategy also plays a copy of itself, as in Axelrod\'s tournament.', { why: 'Rewards strategies that do well in a population of their own kind', alt: 'Matches are played only between different strategies.' }),
  ],
  symbols: { g_T: ['Gain from defecting against a co-operator', '1'], g_P: ['Gain from defecting against a defector', '1'], K_r: ['Co-operation index', '1'], delta_c: ['Critical continuation probability', '1'], U_T: ['Effective temptation payoff', '1'], U_R: ['Effective reward payoff', '1'], U_P: ['Effective punishment payoff', '1'], U_S: ['Effective sucker\'s payoff', '1'], q_ok: ['Probability that both moves in a round are executed as intended', '1'] },
  equations: a => [
    eq('dom1', 'Gain from defecting against a co-operator', 'g_T', a.selfish ? 'T_p - R_p' : 'U_T - U_R', { kind: 'definition' }),
    eq('dom2', 'Gain from defecting against a defector', 'g_P', a.selfish ? 'P_p - S_p' : 'U_P - U_S', { kind: 'definition' }),
    ...(a.selfish ? [] : [
      eq('ut', 'Effective temptation payoff', 'U_T', 'T_p + alpha_o*S_p', { kind: 'hypothesis', origin: 'Other-regarding preferences with linear weight' }),
      eq('ur', 'Effective reward payoff', 'U_R', '(1 + alpha_o)*R_p', { kind: 'hypothesis', origin: 'Other-regarding preferences with linear weight' }),
      eq('up', 'Effective punishment payoff', 'U_P', '(1 + alpha_o)*P_p', { kind: 'hypothesis', origin: 'Other-regarding preferences with linear weight' }),
      eq('us', 'Effective sucker\'s payoff', 'U_S', 'S_p + alpha_o*T_p', { kind: 'hypothesis', origin: 'Other-regarding preferences with linear weight' }),
    ]),
    eq('ki', 'Co-operation index', 'K_r', '(R_p - P_p)/(T_p - S_p)', { kind: 'empirical', origin: 'Rapoport & Chammah (1965)' }),
    eq('folk', 'Critical continuation probability for grim trigger', 'delta_c', '(T_p - R_p)/(T_p - P_p)', { kind: 'derived', origin: 'One-shot deviation principle in the indefinitely repeated game' }),
    ...(a.no_noise ? [] : [eq('noise', 'Probability that a round is played as intended', 'q_ok', '(1 - eps_n)^2', { kind: 'derived', origin: 'Independent execution errors' })]),
  ],
  derivation: a => [
    { text: 'Write the payoff to the row player for each pair of moves. The game is symmetric.', tex: '\\begin{array}{c|cc} & C & D\\\\\\hline C & R & S\\\\ D & T & P\\end{array}' },
    { text: 'If T > R and P > S, defecting gives the higher payoff whatever the other player does: defection strictly dominates.', tex: 'T > R \\quad\\text{and}\\quad P > S \\;\\Rightarrow\\; D \\text{ dominates } C' },
    { text: 'Both players reasoning in this way reach mutual defection, the unique Nash equilibrium. Since R > P it is Pareto-dominated by mutual co-operation.', tex: '(D,D)\\ \\text{is Nash};\\qquad (R,R) \\succ (P,P)' },
    { text: 'In the repeated game with continuation probability δ, co-operating for ever against grim trigger is worth R/(1 − δ); defecting once yields T followed by P for ever. Co-operation is an equilibrium when the first is at least the second.', tex: '\\frac{R}{1-\\delta} \\ge T + \\frac{\\delta P}{1-\\delta} \\iff \\delta \\ge \\delta_c = \\frac{T-R}{T-P}' },
    { text: 'The condition 2R > T + S ensures that taking turns to exploit one another does not beat steady mutual co-operation.', tex: '2R > T + S' },
    ...(a.selfish ? [] : [{ text: 'If each player values the other\'s payoff with weight α, defecting against a co-operator is no longer attractive once the effective temptation falls below the effective reward.', tex: 'T + \\alpha S \\le (1+\\alpha) R \\iff \\alpha \\ge \\frac{T-R}{R-S}' }]),
  ],
  solve(v, a) {
    const { T_p: T, R_p: R, P_p: P, S_p: S0 } = v, n = int(v.n_rounds, 2, 5000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const pay = (me, opp) => (me ? (opp ? R : S0) : (opp ? T : P));
    const al = a.selfish ? 0 : v.alpha_o, u = (me, opp) => pay(me, opp) + al * pay(opp, me);
    // one-shot analysis by enumeration of the four pure profiles
    const prof = [[true, true], [true, false], [false, true], [false, false]], nm = p => `(${p[0] ? 'C' : 'D'}, ${p[1] ? 'C' : 'D'})`;
    const isNE = p => u(p[0], p[1]) >= u(!p[0], p[1]) && u(p[1], p[0]) >= u(!p[1], p[0]);
    const ne = prof.filter(isNE);
    const dominated = p => prof.some(q => pay(q[0], q[1]) >= pay(p[0], p[1]) && pay(q[1], q[0]) >= pay(p[1], p[0]) && (pay(q[0], q[1]) > pay(p[0], p[1]) || pay(q[1], q[0]) > pay(p[1], p[0])));
    const pareto = prof.filter(p => !dominated(p));
    const dilemma = T > R && R > P && P > S0, iter = 2 * R > T + S0;
    const neDD = ne.some(p => !p[0] && !p[1]), neCC = ne.some(p => p[0] && p[1]);
    const warnings = [];
    if (!dilemma) warnings.push('The payoffs do not satisfy T > R > P > S, so this is not a prisoner\'s dilemma; the analysis below describes the game actually entered.');
    else if (!iter) warnings.push('2R > T + S fails: in the repeated game, alternating exploitation pays more than steady mutual co-operation.');
    if (!a.selfish && dilemma && !neDD) warnings.push('With the stated regard for the other player, mutual defection is no longer an equilibrium: the dilemma has been dissolved by changing the preferences, not by changing the reasoning.');
    // round-robin tournament. The scores reported are exact expectations (Markov chain over the joint state of each pair); a set of
    // seeded sample tournaments is played as well, to show one realisation and to test the expectations against direct simulation
    const m = PD_STRATS.length, noise = a.no_noise ? 0 : v.eps_n, NREP = 16;
    const robin = play => { const tot = new Array(m).fill(0), cnt = new Array(m).fill(0); let show = null;
      for (let i = 0; i < m; i++) for (let j = i; j < m; j++) {
        if (i === j && !a.self_play) continue;
        const r = play(i, j);
        if (i === j) { tot[i] += (r.ti + r.tj) / 2; cnt[i]++; } else { tot[i] += r.ti; tot[j] += r.tj; cnt[i]++; cnt[j]++; }
        if (i === 0 && j === 2) show = r;
      }
      return { avg: tot.map((s, i) => s / (cnt[i] * n)), show }; };
    const avg = robin((i, j) => pdExpect(i, j, n, pay, noise, v.p_c)).avg;
    const reps = Array.from({ length: NREP }, (_, k) => robin((i, j) => pdMatch(i, j, n, pay, rnd, noise, v.p_c, k === 0 && i === 0 && j === 2))), showcase = reps[0].show;
    const sMean = avg.map((_, i) => N.mean(reps.map(q => q.avg[i]))), sErr = avg.map((_, i) => Math.sqrt(reps.reduce((q, r) => q + (r.avg[i] - sMean[i]) ** 2, 0) / (NREP * (NREP - 1))));
    const lo = Math.min(T, R, P, S0), hi = Math.max(T, R, P, S0), tiny = 1e-9 * (1 + Math.max(Math.abs(lo), Math.abs(hi)));
    const zs = avg.map((q, i) => (Math.abs(sMean[i] - q) <= tiny ? 0 : Math.abs(sMean[i] - q) / Math.max(sErr[i], 1e-300))), zMax = N.maxOf(zs);
    // ranking on the exact expectations; strategies whose scores coincide are reported as tied, not ordered by rounding
    const top = N.maxOf(avg), tied = avg.map((q, i) => i).filter(i => top - avg[i] <= tiny), best = tied[0];
    const runner = N.maxOf(avg.filter((q, i) => !tied.includes(i)).concat(-Infinity)), lead = top - runner;
    const dc = T - P > 0 ? (T - R) / (T - P) : NaN, Kr = T - S0 !== 0 ? (R - P) / (T - S0) : NaN;
    const ds = N.linspace(0, 0.99, 100), rounds = showcase.ci.map((_, i) => i + 1);
    return {
      scalars: [
        scalar('n_ne', 'Pure-strategy Nash equilibria', ne.length, '1', { text: ne.length ? `${ne.length}: ${ne.map(nm).join(', ')}` : 'None in pure strategies' }),
        scalar('n_par', 'Pareto-optimal outcomes', pareto.length, '1', { text: `${pareto.length}: ${pareto.map(nm).join(', ')}` }),
        scalar('dil', 'Dilemma structure T > R > P > S', dilemma ? 1 : 0, '1', { text: dilemma ? 'Yes' : 'No' }),
        scalar('iter', 'Repeated-game condition 2R > T + S', iter ? 1 : 0, '1', { text: iter ? 'Yes' : 'No' }),
        scalar('ineff', 'Equilibrium is Pareto-dominated', neDD && !neCC && R > P ? 1 : 0, '1', { text: neDD && !neCC && R > P ? 'Yes: both players prefer mutual co-operation to the equilibrium' : 'No' }),
        scalar('g_T', 'Gain from defecting against a co-operator', u(false, true) - u(true, true), '1'),
        scalar('g_P', 'Gain from defecting against a defector', u(false, false) - u(true, false), '1'),
        scalar('K_r', 'Co-operation index (R − P)/(T − S)', Kr, '1', { text: Number.isFinite(Kr) ? undefined : 'Undefined' }),
        scalar('delta_c', 'Critical continuation probability for grim trigger', dc, '1', { text: !Number.isFinite(dc) ? 'Undefined (T ≤ P)' : dc <= 0 ? 'None needed: co-operation is already a best reply' : undefined }),
        ...PD_STRATS.map((s, i) => scalar(`S_${s.key}`, `Average payoff per round: ${s.name.toLowerCase()}`, avg[i], '1', { note: 'expected value, exact' })),
        scalar('best', 'Highest-scoring strategy in the tournament', best + 1, '1', { text: tied.length > 1 ? `Tie: ${tied.map(i => PD_STRATS[i].name).join(', ')}` : PD_STRATS[best].name, note: tied.length === m ? 'all strategies score the same' : `leads the next score by ${lead.toPrecision(3)} per round (expected values, not subject to sampling error)` }),
        scalar('S_mean', 'Mean payoff per round over all strategies', N.mean(avg), '1'),
        scalar('z_sim', `Largest departure of ${NREP} sampled tournaments from the expected scores, in standard errors`, zMax, '1'),
      ],
      series: [
        line('tournament', 'Average payoff per round in the round-robin tournament', 'Strategy', '–', PD_STRATS.map((_, i) => i + 1), [{ label: 'Expected payoff', data: avg }, { label: `Mean of ${NREP} sampled tournaments`, data: sMean }], 'Payoff per round', '–', { kind: 'bar', categories: PD_STRATS.map(s => s.name) }),
        line('match', 'Cumulative score in one sampled match: always defect against tit for tat', 'Round', '–', rounds, [{ label: 'Always defect', data: showcase.ci }, { label: 'Tit for tat', data: showcase.cj }, { label: 'Mutual co-operation (reference)', data: rounds.map(q => q * R), dash: true }], 'Cumulative payoff', '–'),
        line('folk', 'Co-operating for ever against a single defection, facing grim trigger', 'Continuation probability', '–', ds, [{ label: 'Co-operate for ever', data: ds.map(() => R) }, { label: 'Defect once, then be punished', data: ds.map(d => (1 - d) * T + d * P) }], 'Normalised discounted payoff', '–'),
      ],
      checks: [
        check('Mutual defection is an equilibrium whenever T > R > P > S and players are self-interested', a.selfish && dilemma && !neDD ? 1 : 0, 0, 'Dominance argument against enumeration'),
        check('Tournament averages lie within the range of the payoff matrix', avg.some(q => q < lo - 1e-9 || q > hi + 1e-9) ? 1 : 0, 0, 'Every round pays one of T, R, P, S'),
        check('At least one outcome is Pareto-optimal', pareto.length >= 1 ? 0 : 1, 0, 'Guaranteed for any finite game'),
        check('Sampled tournaments agree with the expected scores within sampling error', zMax, 6, `Largest difference between the mean of ${NREP} seeded tournaments and the exact expectation, in standard errors of that mean`),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const { T_p: T, R_p: R, P_p: P, S_p: S0 } = v, n = 50, pay = (me, opp) => (me ? (opp ? R : S0) : (opp ? T : P)), rnd = N.rng(1), out = [];
    const r = pdMatch(0, 2, n, pay, rnd, 0, 0.5);
    out.push(bench('Tit for tat against always defect over 50 rounds', r.tj, S0 + (n - 1) * P, 'Exploited once, then mutual defection', 1e-12));
    out.push(bench('Always defect against tit for tat over 50 rounds', r.ti, T + (n - 1) * P, 'One temptation payoff, then mutual defection', 1e-12));
    out.push(bench('Grim trigger against tit for tat', pdMatch(3, 2, n, pay, rnd, 0, 0.5).ti, n * R, 'Uninterrupted mutual co-operation', 1e-12));
    const e = v.eps_n, xc = pdExpect(1, 1, n, pay, e, 0.5).ti / n, xe = (1 - e) * (1 - e) * R + e * (1 - e) * (S0 + T) + e * e * P;
    out.push(bench('Expected payoff of two unconditional co-operators with noisy moves', xe === 0 ? xc : xc / xe, xe === 0 ? 0 : 1, '(1 − ε)²R + ε(1 − ε)(S + T) + ε²P per round', 1e-12));
    const xt = pdExpect(2, 4, n, pay, 0, v.p_c), pc = v.p_c, ye = (pc * R + (1 - pc) * S0) + (n - 1) * (pc * pc * R + pc * (1 - pc) * (S0 + T) + (1 - pc) * (1 - pc) * P);
    out.push(bench('Expected score of tit for tat against the random strategy', ye === 0 ? xt.ti : xt.ti / ye, ye === 0 ? 0 : 1, 'First round co-operates; thereafter it repeats an independent draw of the random strategy', 1e-12));
    const s = this.solve({ ...v, T_p: 5, R_p: 3, P_p: 1, S_p: 0 }, { selfish: true, no_noise: true, self_play: true });
    out.push(bench('Number of pure Nash equilibria for payoffs 5, 3, 1, 0', val(s, 'n_ne'), 1, 'Unique equilibrium of mutual defection', 1e-12));
    out.push(bench('Critical continuation probability for payoffs 5, 3, 1, 0', val(s, 'delta_c'), 0.5, '(T − R)/(T − P)', 1e-12));
    return out;
  },
  validation: [],
  diagram(v) {
    const cell = (x, y, top, bot, cls) => `${S.rect(x, y, 150, 80, cls)}${S.text(x + 75, y + 36, top)}${S.text(x + 75, y + 58, bot, 'd-text d-small')}`;
    return svg(`
      ${S.text(395, 60, 'Player B')} ${S.text(320, 92, 'co-operate', 'd-text d-small')} ${S.text(470, 92, 'defect', 'd-text d-small')}
      ${S.text(110, 190, 'Player A')} ${S.text(205, 145, 'co-operate', 'd-text d-small', 'end')} ${S.text(205, 225, 'defect', 'd-text d-small', 'end')}
      ${cell(245, 100, `${lab(v.R_p)} , ${lab(v.R_p)}`, 'R , R', 'd-body')}
      ${cell(395, 100, `${lab(v.S_p)} , ${lab(v.T_p)}`, 'S , T', 'd-body')}
      ${cell(245, 180, `${lab(v.T_p)} , ${lab(v.S_p)}`, 'T , S', 'd-body')}
      ${cell(395, 180, `${lab(v.P_p)} , ${lab(v.P_p)}`, 'P , P', 'd-hazard')}
      ${S.arrow(320, 172, 320, 188)} ${S.arrow(470, 172, 470, 188)} ${S.arrow(388, 140, 402, 140)} ${S.arrow(388, 220, 402, 220)}
      ${S.text(320, 300, 'Arrows show each player\'s incentive: both lead to mutual defection', 'd-text d-small')}
      ${S.text(320, 330, 'Payoffs are written as (A, B)', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'RatA', text: 'Player A chooses a strictly dominant strategy when one exists' }, { k: 'RatB', text: 'Player B chooses a strictly dominant strategy when one exists' }, { k: 'DefA', text: 'Player A defects' }, { k: 'DefB', text: 'Player B defects' }, { k: 'Optimal', text: 'The outcome is Pareto-optimal' }],
    premises: ['RatA', 'RatB', 'RatA -> DefA', 'RatB -> DefB', '(DefA & DefB) -> ~Optimal'],
    conclusion: '~Optimal',
  },
  philosophy: [
    'The dilemma separates two senses of rationality that ordinarily coincide: choosing the best reply to whatever others do, and reaching an outcome that the group has reason to want. It is the simplest formal demonstration that the first does not guarantee the second.',
    'It has been used as a model for arms races, the over-use of common resources and the evolution of altruism. Its force in each application depends on whether the payoff structure, the absence of binding agreements and the independence of the choices are actually present.',
    'Proposed escapes divide into those that change the game — repetition, reputation, enforceable contracts, concern for others — and those that revise the theory of rational choice itself, for instance by holding that symmetric reasoners should treat their choices as correlated. The first kind leaves the one-shot analysis intact; the second remains controversial.',
  ],
  experiment: {
    objective: 'Measure co-operation rates and strategy performance in one-shot and repeated play and compare them with the equilibrium prediction and the tournament ranking.',
    apparatus: ['Pairs of participants making simultaneous choices on separate terminals, with payoffs paid in money', 'Alternatively a computer tournament in which submitted strategies meet in a round robin'],
    instruments: [{ name: 'Experiment software log', measures: 'Each participant\'s choice in every round', range: '1–200 rounds', resolution: 'One choice' }, { name: 'Payment ledger', measures: 'Realised payoffs', range: '—', resolution: 'One payoff unit' }],
    procedure: ['Explain the payoff matrix and verify comprehension.', 'One-shot treatment: random anonymous pairing, a single simultaneous choice.', 'Repeated treatment: fixed pairs with a constant probability of continuation after each round.', 'Record co-operation rates by round and estimate the strategies used from the choice histories.'],
    controls: ['Re-matching after every round to remove reputational effects', 'Varying the co-operation index (R − P)/(T − S) between sessions', 'A known final round, to test backward induction'],
    signatures: ['Substantial but minority co-operation in one-shot play, declining with experience', 'Higher co-operation when the continuation probability exceeds (T − R)/(T − P)', 'Reciprocal strategies outscoring unconditional ones in a mixed population'],
    safety: [],
  },
  falsify: ['Computed tournament scores that differ from the exactly known match results for deterministic strategies.', 'For the descriptive claim that people play the equilibrium: stable, high co-operation among experienced anonymous participants in genuinely one-shot play.'],
  alternatives: [
    { name: 'Repeated game and the folk theorem', text: 'With a sufficiently likely future, conditional co-operation is an equilibrium. Defection remains an equilibrium as well; repetition permits co-operation and does not compel it.' },
    { name: 'Other-regarding preferences', text: 'If players value fairness or one another\'s welfare, the material payoffs do not represent their preferences and the game being played is not a prisoner\'s dilemma.' },
    { name: 'Superrationality and evidential reasoning', text: 'Players who know they reason alike may treat their choices as correlated and co-operate. Causal decision theorists reply that the choices are causally independent, so dominance still applies.' },
    { name: 'Evolutionary dynamics', text: 'In populations with assortment, kin structure or repeated encounters, co-operative strategies can spread without any appeal to individual rationality.' },
  ],
  limits: 'Symmetric two-player game with two moves and perfect information about the payoffs. The tournament uses five fixed strategies and a fixed number of rounds; its ranking depends on the field of entrants and should not be read as a general result. With noisy moves an unforgiving strategy is soon triggered and then behaves as always defect, so the two differ only by what happens in the first few rounds and their lead over one another falls as one over the number of rounds. Mixed-strategy equilibria are not enumerated.',
  numerics: { method: 'Exhaustive enumeration of pure-strategy profiles; exact expected scores of the round-robin tournament from the Markov chain of each pair of strategies, cross-checked by seeded sample tournaments', resolution: 'n_rounds' },
  extensions: ['Win-stay lose-shift, generous tit for tat and zero-determinant strategies', 'Replicator dynamics over the strategy population', 'Spatial games on a lattice', 'n-player public-goods games'],
};

// ================================================================== 5. Newcomb's problem
const newcombProblem = {
  id: 'newcomb-problem',
  title: 'Newcomb\'s problem',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['newcomb\'s problem', 'newcomb', 'one box', 'two boxes', 'one-box', 'two-box', 'predictor', 'evidential decision theory', 'causal decision theory', 'opaque box', 'dominance'],
  summary: 'A predictor has already filled an opaque box according to its forecast of your choice. Expected value of taking one box or both as a function of predictor accuracy, under evidential and causal decision theory.',
  background: [
    'A transparent box contains a small sum K. An opaque box contains a large sum M if a highly reliable predictor foresaw that you would take only the opaque box, and nothing if it foresaw that you would take both. The prediction has been made and the boxes are sealed. Do you take one box or two?',
    'Two widely accepted principles give opposite advice. Maximising expected utility conditional on the act favours one box whenever the predictor is accurate enough, because one-boxers are nearly always found to be rich. The dominance principle favours two boxes, because whatever the opaque box contains, taking both yields K more. The disagreement has become the standard test case separating evidential from causal decision theory.',
  ],
  phenomena: ['Conditional expected utility', 'Dominance reasoning', 'Correlation without causal influence', 'Dependence of advice on the theory of choice'],
  laws: ['kolmogorov', 'causality', 'logic_nc'],
  refs: ['Nozick, R. (1969). Newcomb\'s problem and two principles of choice. In N. Rescher (ed.), Essays in Honor of Carl G. Hempel, Reidel, 114–146.', 'Gibbard, A. & Harper, W. L. (1978). Counterfactuals and two kinds of expected utility. In C. A. Hooker, J. J. Leach & E. F. McClennen (eds), Foundations and Applications of Decision Theory, Reidel, 125–162.', 'Lewis, D. (1981). Causal decision theory. Australasian Journal of Philosophy 59, 5–30.', 'Jeffrey, R. C. (1983). The Logic of Decision, 2nd ed. University of Chicago Press.', 'Joyce, J. M. (1999). The Foundations of Causal Decision Theory. Cambridge University Press.'],
  inputs: [
    inp('M_big', 'Amount in the opaque box if one-boxing was predicted', '1', 1000000, { min: 1000, max: 1e9, aliases: ['million', 'large prize', 'opaque box'] }),
    inp('K_small', 'Amount in the transparent box', '1', 1000, { min: 1, max: 1e6, aliases: ['thousand', 'small prize', 'transparent box'] }),
    inp('p_acc', 'Predictor accuracy', '1', 0.9, { min: 0, max: 1, aliases: ['accuracy', 'predictor accuracy', 'reliability'] }),
    inp('q_full', 'Credence that the opaque box is full, held independently of the act (causal reasoning)', '1', 0.5, { min: 0, max: 1, aliases: ['credence', 'prior that the box is full'] }),
    inp('w_0', 'Existing wealth (used when utility is not linear in money)', '1', 10000, { min: 1, max: 1e9, aliases: ['wealth', 'initial wealth'] }),
  ],
  assumptions: [
    asm('evidential', 'The choice is treated as evidence about the prediction: expected utilities use probabilities conditional on the act.', { why: 'Evidential decision theory, the reasoning behind one-boxing', alt: 'Causal decision theory: the contents are already fixed and unaffected by the choice, so the same credence applies to both acts and two-boxing dominates at every accuracy.', affects: ['EV_1', 'EV_2', 'p_star'] }),
    asm('risk_neutral', 'Utility is linear in money.', { why: 'The usual statement of the problem', alt: 'Utility is the logarithm of final wealth. The stakes are compressed and the break-even accuracy rises slightly.', affects: ['EV_1', 'EV_2', 'p_star'] }),
  ],
  symbols: { EV_1: ['Expected utility of taking one box', '1'], EV_2: ['Expected utility of taking both boxes', '1'], dEV: ['Advantage of one-boxing', '1'], p_star: ['Accuracy at which the two acts are equally good', '1'], u_M: ['Utility of the large prize', '1'], u_K: ['Utility of the small prize', '1'], u_MK: ['Utility of both prizes', '1'] },
  equations: a => {
    const lin = a.risk_neutral, uM = lin ? 'M_big' : 'u_M', uK = lin ? 'K_small' : 'u_K', uMK = lin ? '(M_big + K_small)' : 'u_MK';
    return [
      ...(lin ? [] : [
        eq('um', 'Utility of the large prize', 'u_M', 'ln(1 + M_big/w_0)', { kind: 'closure', origin: 'Logarithmic (Bernoulli) utility of final wealth' }),
        eq('uk', 'Utility of the small prize', 'u_K', 'ln(1 + K_small/w_0)', { kind: 'closure', origin: 'Logarithmic (Bernoulli) utility of final wealth' }),
        eq('umk', 'Utility of both prizes', 'u_MK', 'ln(1 + (M_big + K_small)/w_0)', { kind: 'closure', origin: 'Logarithmic (Bernoulli) utility of final wealth' }),
      ]),
      ...(a.evidential ? [
        eq('ev1', 'Expected utility of one box', 'EV_1', `p_acc*${uM}`, { kind: 'derived', origin: 'Expectation conditional on the act (Jeffrey)', needs: ['evidential'] }),
        eq('ev2', 'Expected utility of two boxes', 'EV_2', `(1 - p_acc)*${uMK} + p_acc*${uK}`, { kind: 'derived', origin: 'Expectation conditional on the act (Jeffrey)', needs: ['evidential'] }),
        eq('thr', 'Break-even accuracy', 'p_star', lin ? '(M_big + K_small)/(2*M_big)' : 'u_MK/(u_M + u_MK - u_K)', { kind: 'derived', origin: 'Setting the two expected utilities equal', needs: ['evidential'] }),
      ] : [
        eq('ev1', 'Expected utility of one box', 'EV_1', `q_full*${uM}`, { kind: 'derived', origin: 'Expectation with act-independent credence (Gibbard & Harper; Lewis)' }),
        eq('ev2', 'Expected utility of two boxes', 'EV_2', `q_full*${uMK} + (1 - q_full)*${uK}`, { kind: 'derived', origin: 'Expectation with act-independent credence (Gibbard & Harper; Lewis)' }),
      ]),
      eq('adv', 'Advantage of one-boxing', 'dEV', 'EV_1 - EV_2', { kind: 'definition' }),
    ];
  },
  derivation: a => [
    { text: 'Let p be the probability that the prediction matches the act actually chosen, whichever act that is.', tex: 'P(\\text{full}\\mid\\text{one box}) = p,\\qquad P(\\text{full}\\mid\\text{two boxes}) = 1-p' },
    ...(a.evidential ? [
      { text: 'Conditioning on the act, a one-boxer receives M with probability p. A two-boxer receives M + K if the predictor erred and K otherwise.', tex: 'EV_1 = p\\,M,\\qquad EV_2 = (1-p)(M+K) + pK = (1-p)M + K' },
      { text: 'One-boxing has the higher expectation when p exceeds a threshold only slightly above one half.', tex: 'pM > (1-p)M + K \\iff p > p^* = \\frac{M+K}{2M}' },
    ] : [
      { text: 'The contents were fixed before the choice. Let q be the credence that the opaque box is full; the choice cannot change q.', tex: 'EV_1 = qM,\\qquad EV_2 = q(M+K) + (1-q)K = qM + K' },
      { text: 'Two-boxing is better by exactly K for every q, and hence for every predictor accuracy: it dominates.', tex: 'EV_2 - EV_1 = K > 0' },
    ]),
    { text: 'Whatever theory guides the choice, the long-run average actually received by people who always take one box is pM, and by those who always take both it is (1 − p)M + K.', tex: '\\bar W_1 = pM,\\qquad \\bar W_2 = (1-p)M + K' },
  ],
  solve(v, a) {
    const M = v.M_big, K = v.K_small, p = v.p_acc, q = v.q_full;
    const u = x => (a.risk_neutral ? x : Math.log(1 + x / v.w_0));
    const ev = (pp, qq) => (a.evidential ? [pp * u(M) + (1 - pp) * u(0), (1 - pp) * u(M + K) + pp * u(K)] : [qq * u(M) + (1 - qq) * u(0), qq * u(M + K) + (1 - qq) * u(K)]);
    const [e1, e2] = ev(p, q);
    const pStar = (u(M + K) - u(0)) / (u(M) - u(0) + u(M + K) - u(K));
    const one = e1 > e2, ps = N.linspace(0, 1, 101), ks = N.logspace(1e-4, 1, 60);
    const warnings = [];
    if (K >= M) warnings.push('The transparent box holds at least as much as the opaque box could: taking both is then better under either theory at every accuracy.');
    if (a.evidential && p < 0.5) warnings.push('An accuracy below one half describes a predictor that is systematically wrong; doing the opposite of what it expects is then informative in the other direction.');
    const eAt = ev(Math.min(pStar, 1), q);
    return {
      scalars: [
        scalar('EV_1', `Expected ${a.risk_neutral ? 'value' : 'utility'} of taking one box`, e1, '1'),
        scalar('EV_2', `Expected ${a.risk_neutral ? 'value' : 'utility'} of taking both boxes`, e2, '1'),
        scalar('dEV', 'Advantage of one-boxing', e1 - e2, '1'),
        scalar('p_star', 'Break-even predictor accuracy', a.evidential ? pStar : NaN, '1', { text: !a.evidential ? 'None: two-boxing dominates at every accuracy' : pStar > 1 ? 'Above 1: one-boxing is never preferred' : undefined }),
        scalar('choice', 'Recommended act under the adopted theory', one ? 1 : 2, '1', { text: one ? 'Take one box' : e1 === e2 ? 'Indifferent' : 'Take both boxes' }),
        scalar('W_1', 'Long-run average received by habitual one-boxers', p * M, '1'),
        scalar('W_2', 'Long-run average received by habitual two-boxers', (1 - p) * M + K, '1'),
        scalar('ratio', 'Ratio of the small prize to the large prize', K / M, '1'),
      ],
      series: [
        line('ev-vs-p', `Expected ${a.risk_neutral ? 'value' : 'utility'} against predictor accuracy`, 'Predictor accuracy', '–', ps, [{ label: 'One box', data: ps.map(x => ev(x, q)[0]) }, { label: 'Two boxes', data: ps.map(x => ev(x, q)[1]) }], a.risk_neutral ? 'Expected value' : 'Expected utility', '–', { note: a.evidential ? 'The lines cross at the break-even accuracy.' : 'Under causal reasoning the lines do not depend on accuracy and never cross.' }),
        line('realised', 'Long-run average winnings of habitual choosers', 'Predictor accuracy', '–', ps, [{ label: 'Always one box', data: ps.map(x => x * M) }, { label: 'Always two boxes', data: ps.map(x => (1 - x) * M + K) }], 'Average winnings', '–'),
        line('threshold', 'Break-even accuracy against the ratio of the prizes', 'Small prize / large prize', '–', ks, [{ label: 'Break-even accuracy (linear utility)', data: ks.map(x => Math.min(1, (1 + x) / 2)) }], 'Accuracy', '–', { logx: true }),
      ],
      checks: [
        check('Expected utilities coincide at the break-even accuracy', a.evidential && pStar <= 1 ? (eAt[0] - eAt[1]) / Math.max(Math.abs(eAt[0]), 1e-300) : 0, 1e-9, 'Definition of the threshold'),
        check('Dominance: with a fixed credence two-boxing is never worse than one-boxing', a.evidential ? 0 : Math.max(0, e1 - e2), 0, 'Causal expected utility'),
        check('Probabilities lie in [0, 1]', p < 0 || p > 1 || q < 0 || q > 1 ? 1 : 0, 0, ''),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const r = this.solve({ ...v, M_big: 1e6, K_small: 1e3, p_acc: 0.9 }, { evidential: true, risk_neutral: true }), out = [];
    out.push(bench('One box at 90 % accuracy', val(r, 'EV_1'), 900000, 'p·M', 1e-12));
    out.push(bench('Two boxes at 90 % accuracy', val(r, 'EV_2'), 101000, '(1 − p)·M + K', 1e-12));
    out.push(bench('Break-even accuracy for 1 000 000 and 1 000', val(r, 'p_star'), 0.5005, '(M + K)/(2M)', 1e-12));
    const c = this.solve({ ...v, M_big: 1e6, K_small: 1e3, p_acc: 0.9, q_full: 0.3 }, { evidential: false, risk_neutral: true });
    out.push(bench('Causal advantage of two-boxing', -val(c, 'dEV'), 1000, 'Dominance: exactly K', 1e-9));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.rect(120, 120, 150, 120)} ${S.text(195, 110, 'transparent box A')} ${S.text(195, 186, lab(v.K_small, '', 4))}
      ${S.rect(370, 120, 150, 120, 'd-hazard')} ${S.text(445, 110, 'opaque box B')} ${S.text(445, 176, `${lab(v.M_big, '', 4)} or 0`)} ${S.text(445, 200, 'already fixed', 'd-text d-small')}
      ${S.rect(250, 30, 140, 40)} ${S.text(320, 55, `predictor, p = ${lab(v.p_acc)}`, 'd-text d-small')}
      ${S.arrow(390, 60, 440, 116)} ${S.text(455, 84, 'fills B earlier', 'd-text d-small', 'start')}
      ${S.circle(320, 300, 12)} ${S.text(320, 335, 'chooser')}
      ${S.arrow(332, 292, 430, 246)} ${S.text(420, 285, 'one box: B only', 'd-text d-small', 'start')}
      ${S.arrow(308, 292, 210, 246)} ${S.text(222, 285, 'two boxes: A and B', 'd-text d-small', 'end')}
      ${S.text(110, 55, a.evidential ? 'Evidential reasoning' : 'Causal reasoning', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Dominance', text: 'One should choose an act that is better in every state not causally influenced by the choice' }, { k: 'MaxEU', text: 'One should choose the act with the highest expected utility conditional on the act' }, { k: 'Accurate', text: 'The predictor\'s accuracy exceeds the break-even value' }, { k: 'OneBox', text: 'One should take only the opaque box' }],
    premises: ['Dominance -> ~OneBox', '(MaxEU & Accurate) -> OneBox', 'Accurate', 'Dominance', 'MaxEU'],
    conclusion: null,
  },
  philosophy: [
    'Newcomb\'s problem sets two principles of rational choice against each other in a case where each seems individually compelling. Formally the premises are jointly inconsistent once the predictor is accurate, so at least one principle must be restricted; there is no agreement about which.',
    'One-boxers stress outcomes: those who follow the evidential rule end up richer, and a theory of rationality that predictably leaves its adherents poorer needs an explanation. Two-boxers stress causal structure: the money is already there or not, and no choice made now can alter it, so the one-boxer\'s wealth reflects the kind of person the predictor took them to be and not the merit of the act.',
    'The case bears on free will, on whether correlation with one\'s own decision may be treated like any other evidence, and on the design of decision procedures for agents whose choices can be predicted from their construction. Variants with imperfect and with perfect predictors, and with transparent boxes, test how far each position can be pressed.',
  ],
  experiment: {
    objective: 'Compare the realised winnings of one-boxing and two-boxing participants facing a predictor of known empirical accuracy.',
    apparatus: ['A predictor based on prior questionnaire responses or earlier choices of the same participants', 'Two envelopes per participant filled before the choice is made', 'Alternatively a computer simulation in which an agent\'s policy is read by the predictor with a stated error rate'],
    instruments: [{ name: 'Choice record', measures: 'One box or two', range: '≥ 100 participants', resolution: 'One choice' }, { name: 'Calibration table', measures: 'Fraction of predictions that match the choices', range: '0–1', resolution: '±0.05 at 100 participants' }],
    procedure: ['Collect the information the predictor will use and generate its forecasts.', 'Fill the opaque envelopes according to the forecasts and seal them.', 'Explain the rules, including the predictor\'s track record, and record each choice.', 'Open the envelopes; compute realised accuracy and mean winnings for each group.'],
    controls: ['A treatment with contents assigned at random, in which two-boxing should earn K more on average', 'Informing some participants of the predictor\'s accuracy and not others'],
    signatures: ['Mean winnings of one-boxers near p·M and of two-boxers near (1 − p)·M + K', 'One-boxers better off whenever realised accuracy exceeds (M + K)/(2M)', 'Within any group with identical envelope contents, two-boxers ahead by K'],
    safety: [],
  },
  falsify: ['The arithmetic claims are falsified if tabulated mean winnings by policy differ from p·M and (1 − p)·M + K for a predictor of measured accuracy p.', 'The normative claims are not empirically falsifiable; they are assessed by argument and by their consequences in other decision problems.'],
  alternatives: [
    { name: 'Evidential decision theory', text: 'Choose the act that is the best news about the outcome. Recommends one box when accuracy exceeds the threshold. Faces objections from cases of spurious correlation such as medical "smoking lesion" examples.' },
    { name: 'Causal decision theory', text: 'Weight outcomes by the probability that the act would bring them about. Recommends two boxes always. Faces the objection that its followers predictably fare worse here.' },
    { name: 'Policy-level theories', text: 'Evaluate the disposition or decision procedure, not the isolated act; since the predictor responds to the disposition, the best policy is to be a one-boxer. Such theories are recent and their foundations are disputed.' },
    { name: 'Rejecting the scenario', text: 'Some hold that a sufficiently reliable predictor of a free choice is impossible or that the problem is under-specified, so no determinate advice exists.' },
  ],
  limits: 'A single decision with two acts, a predictor whose accuracy is the same for both kinds of chooser, and stated utilities. The model computes what each decision theory recommends; it does not adjudicate between them.',
  numerics: { method: 'Closed-form expected utilities' },
  extensions: ['Predictor with different accuracies for the two kinds of chooser', 'Transparent-box and repeated versions', 'Parfit\'s hitch-hiker and other problems with the same structure', 'Agents whose source code is visible to the predictor'],
};

// ================================================================== 6. Liar paradox
/** Number of classical valuations of a cycle of m sentences, each saying that the next is false. */
function liarModels(m) { let c = 0; for (let w = 0; w < (1 << m); w++) { let ok = true; for (let i = 0; i < m && ok; i++) if (((w >> i) & 1) === ((w >> ((i + 1) % m)) & 1)) ok = false; if (ok) c++; } return c; }
const liarParadox = {
  id: 'liar-paradox',
  title: 'The liar paradox',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['liar paradox', 'this sentence is false', 'this statement is false', 'liar', 'self-reference', 'epimenides', 'truth value gap', 'three-valued logic', 'fixed point', 'tarski'],
  summary: 'The sentence "this sentence is false" has no consistent classical truth value. Exhaustive search over two-valued assignments, the oscillating revision sequence, and the fixed point at one half in three-valued and fuzzy logic.',
  background: [
    'A sentence that says of itself that it is false is true if and only if it is false. In classical two-valued logic the condition L ↔ ¬L has no model, so the sentence cannot be assigned a truth value without contradiction. Tarski concluded that a language cannot consistently contain its own truth predicate and proposed a hierarchy of languages.',
    'Other approaches keep self-reference and change the logic. In Kripke\'s construction over Kleene\'s strong three-valued scheme the liar is neither true nor false; in fuzzy logics, where negation maps a degree v to 1 − v, it receives the degree one half. The revision theory of Gupta and Belnap instead treats the definition of truth as a rule for revising hypotheses, under which the liar\'s value oscillates for ever.',
  ],
  phenomena: ['Self-reference', 'Absence of a classical fixed point', 'Oscillation under revision', 'Truth-value gaps and intermediate degrees'],
  laws: ['logic_nc', 'logic_em'],
  refs: ['Tarski, A. (1944). The semantic conception of truth and the foundations of semantics. Philosophy and Phenomenological Research 4, 341–376.', 'Kripke, S. (1975). Outline of a theory of truth. Journal of Philosophy 72, 690–716.', 'Priest, G. (1979). The logic of paradox. Journal of Philosophical Logic 8, 219–241.', 'Gupta, A. & Belnap, N. (1993). The Revision Theory of Truth. MIT Press.', 'Kleene, S. C. (1952). Introduction to Metamathematics. North-Holland.'],
  inputs: [
    inp('v_0', 'Initial truth value assigned to the sentence', '1', 1, { min: 0, max: 1, aliases: ['initial truth value', 'initial guess', 'starting value'] }),
    inp('lambda_r', 'Relaxation factor of the revision (used when intermediate values are allowed)', '1', 0.3, { min: 0.01, max: 1, aliases: ['relaxation', 'damping'] }),
    inp('m_c', 'Sentences in the cycle (used when the reference is indirect)', '1', 3, { min: 1, max: 12, aliases: ['cycle length', 'number of sentences'] }),
    inp('n_it', 'Revision steps', '1', 40, { min: 4, max: 400, kind: 'numerical', aliases: ['steps', 'iterations'] }),
  ],
  assumptions: [
    asm('bivalent', 'Every sentence is either true or false, and not both.', { why: 'Classical logic: excluded middle with non-contradiction', alt: 'Truth comes in degrees between 0 and 1 with negation v ↦ 1 − v (Kleene and Łukasiewicz). The liar then has the consistent value one half.', affects: ['n_mod', 'v_fix'] }),
    asm('single', 'A single sentence refers directly to itself.', { why: 'The simple liar', alt: 'A cycle of sentences, each saying that the next is false. Cycles of even length are classically consistent; cycles of odd length are not.', affects: ['n_mod'] }),
  ],
  symbols: { v_L: ['Truth value of the liar sentence', '1'], v_k: ['Truth value at revision step k', '1'], v_next: ['Truth value at the following step', '1'], v_nb: ['Truth value of the next sentence in the cycle', '1'], v_fix: ['Fixed-point truth value', '1'], rho_c: ['Contraction factor of the damped revision', '1'] },
  equations: a => [
    eq('liar', a.single ? 'Liar condition' : 'Condition on each sentence of the cycle', 'v_L', a.single ? '1 - v_L' : '1 - v_nb', { kind: 'definition', origin: 'The sentence asserts the falsity of ' + (a.single ? 'itself' : 'its successor') }),
    ...(a.bivalent ? [
      eq('biv', 'Bivalence', 'v_L*(1 - v_L)', '0', { kind: 'law', origin: 'Excluded middle and non-contradiction: the value is 0 or 1', needs: ['bivalent'] }),
      eq('rev', 'Revision rule', 'v_next', a.single ? '1 - v_k' : '1 - v_nb', { kind: 'definition', origin: 'Gupta & Belnap (1993)' }),
    ] : [
      eq('fix', 'Fixed point', 'v_fix', '1/2', { kind: 'derived', origin: 'Unique solution of v = 1 − v on the unit interval' }),
      eq('rev', 'Damped revision rule', 'v_next', a.single ? 'v_k + lambda_r*(1 - 2*v_k)' : 'v_k + lambda_r*(1 - v_nb - v_k)', { kind: 'definition', origin: 'Under-relaxed fixed-point iteration' }),
      a.single
        ? eq('rate', 'Contraction factor', 'rho_c', 'abs(1 - 2*lambda_r)', { kind: 'derived', origin: 'Linear iteration about the fixed point' })
        : eq('rate', 'Contraction factor for a cycle of odd length', 'rho_c', 'sqrt(1 - 2*lambda_r*(1 - lambda_r)*(1 - cos(pi/m_c)))', { kind: 'derived', origin: 'Largest eigenvalue modulus |1 − λ − λ e^(2πij/m)| of the cyclic iteration', exportable: false, note: 'Holds for a cycle of odd length. For an even cycle the alternating mode is not damped and the solver reports a factor of 1.' }),
    ]),
  ],
  derivation: a => [
    { text: 'Let v be the truth value of L, with 1 for true and 0 for false. L says that L is false, so its value must equal that of its own negation.', tex: 'v(L) = 1 - v(L)' },
    a.bivalent
      ? { text: 'Neither classical value satisfies the condition: 1 ≠ 0 and 0 ≠ 1. Equivalently the formula L ↔ ¬L is unsatisfiable.', tex: 'v\\in\\{0,1\\}:\\quad 1 \\ne 1-1,\\qquad 0 \\ne 1-0' }
      : { text: 'If v may take any value in the unit interval the condition has exactly one solution.', tex: 'v = 1 - v \\iff v = \\tfrac12' },
    a.bivalent
      ? { text: 'Treating the condition as a rule for revising a guess produces an endless alternation with period two.', tex: 'v_{k+1} = 1 - v_k:\\qquad 1,\\,0,\\,1,\\,0,\\,\\ldots' }
      : a.single
        ? { text: 'A damped revision moves a fraction λ of the way towards the revised value. The distance from one half shrinks by the factor |1 − 2λ| at each step.', tex: 'v_{k+1} - \\tfrac12 = (1-2\\lambda)\\left(v_k - \\tfrac12\\right)' }
        : { text: 'A damped revision moves the value of each sentence a fraction λ of the way towards the value its successor requires of it.', tex: 'v^{(i)}_{k+1} = v^{(i)}_k + \\lambda\\left(1 - v^{(i+1)}_k - v^{(i)}_k\\right)' },
    ...(a.single ? [] : [{ text: 'For a cycle of m sentences each saying that the next is false, a classical assignment must alternate around the cycle, which is possible exactly when m is even.', tex: '\\#\\text{models} = \\begin{cases}2 & m \\text{ even}\\\\ 0 & m \\text{ odd}\\end{cases}' }]),
    ...(a.single || a.bivalent ? [] : [{ text: 'On a cycle the damped revision couples each sentence to its successor. Its modes are the m-th roots of unity; for odd m the slowest one sets the rate of approach to one half, and for even m the alternating mode is not damped at all.', tex: '\\rho = \\max_j\\left|1-\\lambda-\\lambda e^{2\\pi i j/m}\\right| = \\sqrt{1-2\\lambda(1-\\lambda)\\left(1-\\cos\\tfrac{\\pi}{m}\\right)}\\quad(m\\ \\text{odd})' }]),
  ],
  solve(v, a) {
    const m = a.single ? 1 : int(v.m_c, 1, 14), n = int(v.n_it, 4, 2000), lam = v.lambda_r;
    const nModels = liarModels(m);
    // classical revision of the whole cycle from the initial valuation
    const start = Array.from({ length: m }, (_, i) => (i === 0 ? v.v_0 : 0));
    let cl = start.map(x => (x >= 0.5 ? 1 : 0)), fz = start.slice();
    const res = s => N.maxOf(s.map((x, i) => Math.abs(x - (1 - s[(i + 1) % m]))));
    const steps = [0], yc = [cl[0]], yf = [fz[0]], rr = [Math.max(res(fz), 1e-17)], seen = new Map([[cl.join(''), 0]]);
    let period = NaN, nConv = NaN;
    for (let k = 1; k <= n; k++) {
      cl = cl.map((_, i) => 1 - cl[(i + 1) % m]);
      fz = fz.map((x, i) => x + lam * (1 - fz[(i + 1) % m] - x));
      const key = cl.join('');
      if (Number.isNaN(period) && seen.has(key)) period = k - seen.get(key);
      if (!seen.has(key)) seen.set(key, k);
      const rf = res(fz);
      if (Number.isNaN(nConv) && rf < 1e-6) nConv = k;
      steps.push(k); yc.push(cl[0]); yf.push(fz[0]); rr.push(Math.max(rf, 1e-17));
    }
    // slowest mode of v ← (1 − λ)v − λPv + λ on the cycle: eigenvalues 1 − λ − λ·exp(2πij/m)
    const classicalOk = nModels > 0, rho = m % 2 === 0 ? 1 : Math.sqrt(Math.max(0, 1 - 2 * lam * (1 - lam) * (1 - Math.cos(Math.PI / m))));
    const warnings = [];
    if (!a.bivalent && lam >= 1 && m === 1) warnings.push('With a relaxation factor of 1 the revision is undamped and oscillates; any smaller positive factor converges to one half.');
    if (!a.bivalent && m % 2 === 0) warnings.push('For a cycle of even length the alternating assignments (v, 1 − v, …) are all fixed points; the damped revision settles on one of them, determined by the starting values.');
    return {
      scalars: [
        scalar('n_mod', 'Consistent two-valued assignments', nModels, '1', { text: classicalOk ? `${nModels}: classically consistent` : 'None: no classical truth value is possible' }),
        scalar('m_len', 'Sentences in the self-referential cycle', m, '1'),
        scalar('per', 'Period of the classical revision sequence', period, '1', { text: Number.isNaN(period) ? 'Not found within the steps taken' : period === 1 ? '1: the starting assignment is stable' : undefined }),
        scalar('v_fix', 'Fixed-point truth value', a.bivalent ? (classicalOk ? cl[0] : NaN) : 0.5, '1', { text: a.bivalent ? (classicalOk ? 'Either 0 or 1, depending on the assignment chosen' : 'None in {0, 1}') : undefined }),
        scalar('v_end', 'Value of the first sentence after the last revision step', a.bivalent ? cl[0] : fz[0], '1'),
        scalar('res', 'Residual of the liar condition after the last step', a.bivalent ? res(cl) : res(fz), '1'),
        scalar('rho_c', 'Contraction factor of the damped revision', rho, '1'),
        scalar('n_conv', 'Damped steps needed for a residual below 10⁻⁶', nConv, '1', { text: Number.isNaN(nConv) ? 'Not reached within the steps taken' : undefined }),
      ],
      series: [
        line('revision', 'Truth value of the sentence under repeated revision', 'Revision step', '–', steps, [{ label: 'Two-valued revision', data: yc, dash: !a.bivalent }, { label: 'Damped revision with degrees of truth', data: yf, dash: a.bivalent }, { label: 'One half', data: steps.map(() => 0.5), dash: true }], 'Truth value', '–'),
        line('residual', 'Residual of the self-reference condition under damped revision', 'Revision step', '–', steps, [{ label: 'max |v − (1 − v′)|', data: rr }], 'Residual', '–', { logy: true }),
      ],
      checks: [
        check('Exhaustive count agrees with the parity rule', nModels - (m % 2 === 0 ? 2 : 0), 0, 'Two models for even cycles, none for odd ones'),
        check('One half satisfies the liar condition', Math.abs(0.5 - (1 - 0.5)), 1e-15, 'Fixed point of v ↦ 1 − v'),
        check('Degrees of truth remain in the unit interval', yf.some(x => x < -1e-12 || x > 1 + 1e-12) ? 1 : 0, 0, ''),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const out = [];
    let dev = 0; for (let m = 1; m <= 8; m++) dev += Math.abs(liarModels(m) - (m % 2 === 0 ? 2 : 0));
    out.push(bench('Model counts for cycles of one to eight sentences', dev, 0, 'Parity rule: 0, 2, 0, 2, …', 1e-12));
    const r = this.solve({ ...v, v_0: 1, lambda_r: 0.5, n_it: 10 }, { bivalent: false, single: true });
    out.push(bench('Damped revision with relaxation one half', val(r, 'v_end'), 0.5, 'Reaches the fixed point in one step', 1e-12));
    const q = this.solve({ ...v, v_0: 1, lambda_r: 0.25, n_it: 10 }, { bivalent: false, single: true });
    out.push(bench('Deviation after ten damped steps with relaxation one quarter', val(q, 'v_end') - 0.5, 0.5 * Math.pow(0.5, 10), 'Geometric contraction (1 − 2λ)ᵏ', 1e-9));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const m = a.single ? 1 : int(v.m_c, 1, 14);
    if (m === 1) return svg(`
      ${S.rect(170, 130, 300, 70)} ${S.text(320, 172, '"This sentence is false."')}
      ${S.path('M470 150 C560 90 560 250 474 186', 'd-line')} ${S.arrow(480, 190, 472, 186)}
      ${S.text(560, 172, 'refers to', 'd-text d-small', 'start')}
      ${S.text(320, 70, a.bivalent ? 'true → false → true → …' : 'degree of truth 1/2')}
      ${S.text(320, 260, a.bivalent ? 'No assignment of true or false is stable' : 'v = 1 − v has the solution v = 1/2', 'd-text d-small')}
    `);
    const show = Math.min(m, 8), cx = 320, cy = 185, R = 110;
    const pt = i => [cx + R * Math.cos(2 * Math.PI * i / show - Math.PI / 2), cy + R * Math.sin(2 * Math.PI * i / show - Math.PI / 2)];
    return svg(`
      ${Array.from({ length: show }, (_, i) => { const [x, y] = pt(i), [x2, y2] = pt((i + 1) % show); const dx = x2 - x, dy = y2 - y, L = Math.hypot(dx, dy) || 1; return `${S.circle(x, y, 18)}${S.text(x, y + 5, `S${i + 1}`, 'd-text d-small')}${S.arrow(x + dx / L * 22, y + dy / L * 22, x2 - dx / L * 22, y2 - dy / L * 22)}`; }).join('')}
      ${S.text(320, 40, `${m} sentences, each saying "the next sentence is false"${m > show ? ` (${show} drawn)` : ''}`)}
      ${S.text(320, 340, m % 2 === 0 ? 'Even cycle: alternate true and false' : 'Odd cycle: no consistent assignment', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'L', text: 'The liar sentence is true' }],
    premises: ['L <-> ~L'],
    conclusion: null,
  },
  philosophy: [
    'The liar shows that three plausible commitments cannot all be kept: that every declarative sentence is true or false, that a language may refer to its own sentences, and that "is true" behaves as the T-schema requires. Each major response gives up or restricts one of them.',
    'Tarski\'s hierarchy restricts self-application of truth; gap theories such as Kripke\'s restrict bivalence; dialetheism accepts that some sentences are both true and false and weakens the logic so that contradictions do not entail everything. Strengthened liars — "this sentence is not true" — are designed to re-create the difficulty for whichever solution is on offer.',
    'The construction is not an idle curiosity. The same diagonal pattern underlies Gödel\'s incompleteness theorem, Tarski\'s undefinability theorem and the unsolvability of the halting problem, where it yields theorems instead of contradictions.',
  ],
  experiment: {
    objective: 'Verify by exhaustive search that no two-valued assignment satisfies the liar condition and observe the behaviour of the revision sequence.',
    apparatus: ['A truth-table program or a spreadsheet', 'Alternatively an inverting logic gate with its output wired to its input (a ring oscillator of one stage)'],
    instruments: [{ name: 'Truth-table enumerator', measures: 'Models of the defining biconditionals', range: '1–16 sentences', resolution: 'Exact' }, { name: 'Oscilloscope (hardware version)', measures: 'Output voltage of the inverter loop', range: '0–5 V', resolution: '≈ 1 ns' }],
    procedure: ['Encode each sentence as a propositional variable and each self-reference as a biconditional.', 'Enumerate all assignments and count those satisfying every biconditional.', 'Starting from an arbitrary assignment, apply the revision rule repeatedly and record the sequence.', 'Repeat with continuous values and under-relaxation and record the limit.'],
    controls: ['The truth-teller "this sentence is true", which is satisfied by both values', 'Cycles of even length, which have exactly two classical models'],
    signatures: ['Zero models for every odd cycle, two for every even cycle', 'Period-two alternation of the classical revision sequence for the simple liar', 'Convergence of the damped continuous iteration to one half; a physical inverter loop either oscillates or settles at its mid-rail voltage'],
    safety: [],
  },
  falsify: ['Discovery of a two-valued assignment satisfying L ↔ ¬L would refute classical propositional logic itself; none exists among the two candidates.', 'A damped revision with relaxation strictly between 0 and 1 that fails to approach one half for the single liar.'],
  alternatives: [
    { name: 'Hierarchy of languages (Tarski)', text: 'Truth for a language is defined only in a richer metalanguage, so the liar sentence cannot be formed. Consistent, at the cost of fragmenting the ordinary notion of truth.' },
    { name: 'Truth-value gaps (Kripke)', text: 'The liar is ungrounded and receives no classical value in the minimal fixed point. The sentence "this sentence is not true" then seems true, the so-called revenge problem.' },
    { name: 'Dialetheism (Priest)', text: 'The liar is both true and false. A paraconsistent logic prevents the contradiction from trivialising the theory.' },
    { name: 'Revision theory (Gupta and Belnap)', text: 'The definition of truth is circular and yields a rule of revision, not a fixed extension. The liar is classified by its unstable pattern under revision.' },
  ],
  limits: 'Propositional treatment of a single sentence or a simple cycle with the self-reference encoded as a biconditional. Quantified or contingent liars, and the strengthened liar, are not modelled. The value one half represents either "undefined" in Kleene\'s scheme or the middle degree in fuzzy logic; the two readings differ philosophically.',
  numerics: { method: 'Exhaustive enumeration of 2ᵐ assignments; fixed-point iteration with under-relaxation', stability: 'Converges for relaxation strictly between 0 and 1', resolution: 'n_it' },
  extensions: ['Yablo\'s paradox, an infinite sequence without direct self-reference', 'Curry\'s paradox', 'Kripke\'s least fixed point computed for a small language', 'Connection to Gödel sentences and the halting problem'],
};

// ================================================================== 7. Ship of Theseus
const shipOfTheseus = {
  id: 'ship-of-theseus',
  title: 'The ship of Theseus',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['ship of theseus', 'theseus', 'identity over time', 'gradual replacement', 'replace every part', 'same ship', 'persistence', 'planks', 'personal identity', 'identity'],
  summary: 'A ship is repaired plank by plank while the discarded planks are reassembled elsewhere. Fraction of original matter against time, and the conflict between identity by continuity and identity by composition.',
  background: [
    'Plutarch reports that the Athenians preserved the ship of Theseus by replacing its timbers as they decayed, and that philosophers disputed whether it remained the same ship. Hobbes sharpened the puzzle: suppose the removed planks are kept and reassembled in their original arrangement. There are then two candidates, one continuous in form and function with the original, the other made of the original matter.',
    'The quantitative side is simple. If parts are replaced at random the expected fraction of original matter decays geometrically; if they are replaced in order it falls linearly. The philosophical side is the choice of a criterion of identity. Continuity of form and sameness of matter each seem sufficient alone, but together with the principle that at most one thing can be identical with the original they yield a contradiction.',
  ],
  phenomena: ['Gradual replacement of components', 'Exponential and linear depletion of original material', 'Competing criteria of persistence', 'Transitivity and uniqueness of identity'],
  laws: ['logic_nc', 'mass'],
  refs: ['Plutarch. Life of Theseus, 23.1.', 'Hobbes, T. (1655). De Corpore, Part II, ch. 11.', 'Wiggins, D. (1980). Sameness and Substance. Blackwell.', 'Parfit, D. (1984). Reasons and Persons. Oxford University Press.', 'Lowe, E. J. (1983). On the identity of artifacts. Journal of Philosophy 80, 220–232.'],
  inputs: [
    inp('N_p', 'Number of parts in the ship', '1', 1000, { min: 10, max: 1000000, aliases: ['parts', 'planks', 'components'] }),
    inp('r_rep', 'Replacement rate', '1/yr', 50, { min: 0.1, max: 100000, aliases: ['replacement rate', 'parts per year', 'planks per year'] }),
    inp('t_obs', 'Time at which identity is assessed', 'yr', 30, { min: 0, max: 10000, aliases: ['after', 'elapsed time', 'years'] }),
    inp('seed', 'Random seed', '1', 3, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('random_repl', 'Each repair replaces a part chosen at random, which may already be a replacement.', { why: 'Failures are not ordered by age of installation', alt: 'Parts are replaced systematically, oldest first, so the original fraction falls linearly and reaches zero after N replacements.', affects: ['f_o', 't_50'] }),
    asm('form_crit', 'Continuity of form and function suffices for identity.', { why: 'The ordinary criterion for artefacts under repair', alt: 'Continuity alone does not confer identity.', affects: ['n_claim'] }),
    asm('matter_crit', 'Being composed mostly of the original matter, in the original arrangement, suffices for identity.', { why: 'The criterion applied to a dismantled and rebuilt object', alt: 'Material composition alone does not confer identity.', affects: ['n_claim'] }),
    asm('reassembled', 'The discarded parts are kept and reassembled into a second ship.', { why: 'Hobbes\'s version of the puzzle', alt: 'The discarded parts are destroyed; only the repaired ship exists.', affects: ['n_claim', 'f_B'] }),
  ],
  symbols: { f_o: ['Fraction of original matter in the repaired ship', '1'], f_B: ['Fraction of the original matter in the reassembled ship', '1'], t: ['Time', 's'], t_50: ['Time at which half the original matter remains', 's'], t_all: ['Expected time for every original part to be replaced', 's'] },
  equations: a => [
    ...(a.random_repl ? [
      eq('frac', 'Expected original fraction', 'f_o', '(1 - 1/N_p)^(r_rep*t)', { kind: 'derived', origin: 'Each replacement spares a given part with probability 1 − 1/N', needs: ['random_repl'] }),
      eq('half', 'Time to one half', 't_50', 'ln(1/2)/(r_rep*ln(1 - 1/N_p))', { kind: 'derived', origin: 'Inverting the geometric decay', needs: ['random_repl'] }),
      eq('all', 'Expected time until no original part remains', 't_all', 'N_p*(ln(N_p) + 0.5772156649 + 1/(2*N_p))/r_rep', { kind: 'derived', origin: 'Coupon-collector expectation N·H_N with the harmonic number H_N ≈ ln N + γ + 1/(2N), in error by less than 1/(12N²)', needs: ['random_repl'] }),
    ] : [
      eq('frac', 'Original fraction', 'f_o', 'max(0, 1 - r_rep*t/N_p)', { kind: 'derived', origin: 'One original part removed per replacement' }),
      eq('half', 'Time to one half', 't_50', 'N_p/(2*r_rep)', { kind: 'derived', origin: 'Linear depletion' }),
      eq('all', 'Time until no original part remains', 't_all', 'N_p/r_rep', { kind: 'derived', origin: 'Linear depletion' }),
    ]),
    ...(a.reassembled ? [eq('other', 'Share of the original matter in the reassembled ship', 'f_B', '1 - f_o', { kind: 'law', origin: 'Conservation of the original parts', needs: ['reassembled'] })] : []),
  ],
  derivation: a => [
    a.random_repl
      ? { text: 'At each repair one of the N parts is chosen at random. A particular original part survives one repair with probability 1 − 1/N, and n independent repairs with that probability raised to the n-th power.', tex: 'f(n) = \\left(1-\\frac1N\\right)^{n} \\approx e^{-n/N},\\qquad n = r\\,t' }
      : { text: 'If the oldest part is replaced each time, every repair removes one original part until none is left.', tex: 'f(n) = \\max\\left(0,\\,1-\\frac{n}{N}\\right),\\qquad n = r\\,t' },
    a.random_repl
      ? { text: 'The time for the original fraction to fall to a given level q follows by taking logarithms; one half is reached after about N ln 2 replacements.', tex: 't_q = \\frac{\\ln q}{r\\,\\ln(1-1/N)} \\approx \\frac{N}{r}\\ln\\frac1q' }
      : { text: 'The original fraction reaches q after (1 − q)N replacements.', tex: 't_q = \\frac{(1-q)\\,N}{r}' },
    { text: 'Call the repaired ship A and the ship rebuilt from the discarded parts B. The two criteria of identity, with the uniqueness of the original, give three claims that cannot all hold once B contains most of the original matter.', tex: '\\text{Form}\\rightarrow A = O,\\qquad \\text{Matter}\\rightarrow B = O,\\qquad \\lnot(A = O \\land B = O)' },
  ],
  solve(v, a) {
    const Np = int(v.N_p, 2, 1e7), r = v.r_rep, nObs = r * v.t_obs;
    const f = n => (a.random_repl ? Math.pow(1 - 1 / Np, n) : Math.max(0, 1 - n / Np));
    const tq = q => (a.random_repl ? Math.log(q) / Math.log(1 - 1 / Np) : (1 - q) * Np) / r;
    let HN = 0; if (Np <= 20000) { for (let i = 1; i <= Np; i++) HN += 1 / i; } else HN = Math.log(Np) + 0.5772156649015329 + 1 / (2 * Np);
    const tAll = (a.random_repl ? Np * HN : Np) / r;
    const fo = f(nObs), fB = a.reassembled ? 1 - fo : 0;
    const claimA = a.form_crit || (a.matter_crit && fo > 0.5), claimB = a.reassembled && a.matter_crit && fB > 0.5;
    const nClaim = (claimA ? 1 : 0) + (claimB ? 1 : 0);
    const verdict = nClaim === 2 ? 'Two: the repaired ship and the reassembled ship both qualify, which contradicts the uniqueness of the original' : nClaim === 0 ? 'None: no ship satisfies an adopted criterion' : claimA ? 'One: the repaired ship' : 'One: the reassembled ship';
    // replacement simulation on a model ship of at most 4000 parts
    const Ns = Math.min(Np, 4000), rnd = N.rng(int(v.seed, 1, 2147483647)), nEnd = Math.round((a.random_repl ? 5 : 1.2) * Ns), cp = marks(nEnd, 50);
    const orig = new Uint8Array(Ns).fill(1); let left = Ns, ci = 0, simAtN = NaN; const sx = [], sy = [];
    for (let k = 1; k <= nEnd; k++) {
      const i = a.random_repl ? Math.floor(rnd() * Ns) : (k - 1) % Ns;
      if (orig[i]) { orig[i] = 0; left--; }
      if (k === Ns) simAtN = left / Ns;
      if (k === cp[ci]) { ci++; sx.push(k / Ns); sy.push(left / Ns); }
    }
    const exactS = n => (a.random_repl ? Math.pow(1 - 1 / Ns, n) : Math.max(0, 1 - n / Ns));
    // exact variance of the number of surviving originals after Ns random draws (the survival indicators are negatively correlated)
    const qS = exactS(Ns), sigS = a.random_repl ? Math.sqrt(Math.max(Ns * qS + Ns * (Ns - 1) * Math.pow(1 - 2 / Ns, Ns) - Ns * Ns * qS * qS, 0)) / Ns : 0;
    const tEnd = (a.random_repl ? 5 : 1.2) * Np / r, tt = N.linspace(0, tEnd, 200);
    return {
      scalars: [
        scalar('f_o', 'Fraction of original matter in the repaired ship', fo, '1', PCT),
        scalar('f_B', 'Fraction of the original matter in the reassembled ship', fB, '1', { show: '%', text: a.reassembled ? undefined : 'No second ship' }),
        scalar('n_rep', 'Replacements carried out', nObs, '1'),
        scalar('t_50', 'Time at which half the original matter remains', tq(0.5), 's', { show: 'yr' }),
        scalar('t_01', 'Time at which 1 % of the original matter remains', tq(0.01), 's', { show: 'yr' }),
        scalar('t_all', `${a.random_repl ? 'Expected time' : 'Time'} until no original part remains`, tAll, 's', { show: 'yr' }),
        scalar('n_claim', 'Ships that qualify as the original under the adopted criteria', nClaim, '1', { text: verdict }),
        scalar('f_sim', 'Simulated original fraction after N replacements', simAtN, '1', PCT),
        scalar('sigma_mc', 'Standard deviation expected for that simulated fraction', sigS, '1'),
      ],
      series: [
        line('original-fraction', 'Original matter in each ship', 'Time', 'yr', tt.map(t => t / YEAR), [{ label: 'Repaired ship', data: tt.map(t => f(r * t)) }, ...(a.reassembled ? [{ label: 'Reassembled ship (share of the original parts)', data: tt.map(t => 1 - f(r * t)) }] : []), { label: 'One half', data: tt.map(() => 0.5), dash: true }], 'Fraction', '–'),
        line('simulation', `Simulated replacement of a ${Ns}-part ship`, 'Replacements / number of parts', '–', sx, [{ label: 'Simulated', data: sy }, { label: 'Expected', data: sx.map(x => exactS(x * Ns)), dash: true }], 'Original fraction', '–', { kind: 'line' }),
      ],
      checks: [
        check('Original parts are conserved between the two ships', a.reassembled ? fo + fB - 1 : 0, 1e-12, 'Every original part is in one ship or the other'),
        check('Fraction lies in [0, 1]', fo < 0 || fo > 1 ? 1 : 0, 0, ''),
        check('Simulated fraction after N replacements against expectation', simAtN - exactS(Ns), 4 * sigS + 1e-12, 'Within four standard deviations'),
      ],
      warnings: nClaim === 2 ? ['Both criteria of identity are in force and each picks out a different ship. Holding them together with the uniqueness of the original is inconsistent; one premise must be given up or restricted.'] : [],
    };
  },
  benchmarks(v, a) {
    const Np = int(v.N_p, 2, 1e7), on = { random_repl: true, form_crit: true, matter_crit: true, reassembled: true }, out = [];
    const r = this.solve(v, on);
    out.push(bench('Half-life against the continuous approximation N ln 2 / r', val(r, 't_50'), Np * Math.LN2 / v.r_rep, 'Exponential limit; agreement to order 1/N', 1 / Np));
    const e = this.solve({ ...v, t_obs: Np / v.r_rep }, on);
    out.push(bench('Original fraction after N random replacements', val(e, 'f_o'), Math.exp(-1), '(1 − 1/N)ᴺ → 1/e', 1 / Np));
    const l = this.solve({ ...v, t_obs: 0.25 * Np / v.r_rep }, { ...on, random_repl: false });
    out.push(bench('Systematic replacement of a quarter of the parts', val(l, 'f_o'), 0.75, 'Linear depletion', 1e-9));
    const s = this.solve({ ...v, N_p: 10, r_rep: 1, t_obs: 10 }, on);
    out.push(bench('Ten random replacements in a ship of ten parts', val(s, 'f_o'), 0.3486784401, 'Exact value (9/10)¹⁰', 1e-9));
    out.push(bench('Expected replacements until no original part remains, ten parts', val(s, 't_all'), 7381 / 252, 'Coupon collector: 10·H₁₀ with H₁₀ = 7381/2520', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const hull = (x, y, cls) => S.path(`M${x} ${y} L${x + 180} ${y} L${x + 150} ${y + 40} L${x + 30} ${y + 40} Z`, cls);
    return svg(`
      ${hull(60, 150, 'd-body')} ${S.line(150, 150, 150, 80)} ${S.path('M150 85 L200 115 L150 140', 'd-line')} ${S.text(150, 215, 'original ship O')}
      ${S.arrow(250, 150, 400, 95)} ${S.text(320, 105, 'repair, part by part', 'd-text d-small')}
      ${hull(410, 70, 'd-body')} ${S.text(500, 135, 'A: repaired ship')} ${S.text(500, 152, 'continuous form, new matter', 'd-text d-small')}
      ${a.reassembled ? `${S.arrow(250, 190, 400, 245)} ${S.text(320, 240, 'old parts kept', 'd-text d-small')} ${hull(410, 220, 'd-hazard')} ${S.text(500, 285, 'B: reassembled ship')} ${S.text(500, 302, 'original matter', 'd-text d-small')}` : S.text(450, 250, 'old parts destroyed', 'd-text d-small')}
      ${S.text(320, 340, `${lab(v.N_p)} parts, ${lab(v.r_rep * YEAR)} replaced per year`, 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Form', text: 'Continuity of form and function suffices for identity with the original' }, { k: 'Matter', text: 'Composition from the original matter suffices for identity with the original' }, { k: 'A', text: 'The repaired ship is the original ship' }, { k: 'B', text: 'The reassembled ship is the original ship' }],
    premises: ['Form -> A', 'Matter -> B', '~(A & B)', 'Form', 'Matter'],
    conclusion: null,
  },
  philosophy: [
    'The puzzle shows that ordinary judgements of sameness rest on more than one criterion, and that the criteria, harmless in everyday cases, can be made to diverge. It does not show that any fact about planks is unknown: everything physical is specified, and the dispute concerns what the word "same" should track.',
    'Responses differ on what gives way. Some privilege spatio-temporal continuity under a sortal concept; some hold that identity over time is a matter of convention or degree; four-dimensionalists describe two overlapping space-time objects sharing early stages; others deny that composite artefacts have strict identity conditions at all.',
    'The same structure appears in discussions of personal identity, where gradual replacement of cells, or hypothetical duplication, plays the role of the planks, and in practical questions about the authenticity of restored buildings, instruments and works of art.',
  ],
  experiment: {
    objective: 'Measure the decline of original components in a maintained system and compare it with the geometric or linear law, and elicit identity judgements for the two candidate objects.',
    apparatus: ['A model built from numbered blocks, with a supply of replacement blocks of a different colour', 'Maintenance records of a real fleet or instrument as an observational alternative', 'A questionnaire presenting the repaired and the reassembled object'],
    instruments: [{ name: 'Parts register', measures: 'Which components are original', range: '10–10⁶ parts', resolution: 'One part' }, { name: 'Die or random-number generator', measures: 'Which part is replaced next', range: '1–N', resolution: '—' }, { name: 'Survey instrument', measures: 'Which object respondents call the original', range: '—', resolution: 'One response' }],
    procedure: ['Replace one randomly selected block at a time, keeping the removed blocks.', 'Record the number of original blocks remaining after each replacement.', 'Rebuild a second model from the removed blocks.', 'Ask respondents at several stages which model is the original and why.'],
    controls: ['Systematic (oldest-first) replacement, which should give a straight-line decline', 'A version in which the removed blocks are destroyed, removing the rival candidate'],
    signatures: ['Original fraction near (1 − 1/N)ⁿ after n random replacements, about 37 % at n = N', 'Half of the original material gone after about 0.69 N random replacements', 'Divided identity judgements only when the reassembled rival exists'],
    safety: [],
  },
  falsify: ['A measured original fraction under verified random replacement that departs from (1 − 1/N)ⁿ by many standard deviations.', 'The logical claim would be refuted by a consistent assignment satisfying both sufficiency criteria and the uniqueness of the original while the two ships are distinct; the truth table shows there is none.'],
  alternatives: [
    { name: 'Continuity view', text: 'The repaired ship is the original because it is linked to it by a continuous history as a functioning ship; the reassembled object is a new ship made of old planks.' },
    { name: 'Mereological essentialism', text: 'An object is its parts; the reassembled ship is the original and the repaired one became a different ship as soon as a plank was changed.' },
    { name: 'Four-dimensionalism', text: 'Ships are extended in time. Two distinct space-time objects share their early temporal parts, and the question "which is the original?" is a question about reference, not about the world.' },
    { name: 'Conventionalism or degrees of identity', text: 'Identity of artefacts over time is partly a matter of purpose and convention, or comes in degrees, so no single answer is required.' },
  ],
  limits: 'Parts are treated as equal and interchangeable; the expected-fraction formulae are exact for uniform random or strictly ordered replacement. The identity verdict applies the adopted criteria mechanically with a majority threshold for material composition and is an illustration of the logical structure, not a metaphysical result.',
  numerics: { method: 'Closed-form geometric and linear depletion; seeded replacement simulation on a model of at most 4000 parts' },
  extensions: ['Parts of unequal size or importance', 'Age-dependent failure rates', 'Gradual-replacement and duplication cases in personal identity', 'Authenticity criteria used in conservation practice'],
};

// ================================================================== 8. Grandfather paradox
/** Iterate the bit-flip channel p -> p + q(1 - 2p) around the loop; returns the sequence of probabilities. */
function ctcIterate(q, p0, n) { const out = [p0]; let p = p0; for (let k = 0; k < n; k++) { p = p + q * (1 - 2 * p); out.push(p); } return out; }
const grandfatherParadox = {
  id: 'grandfather-paradox',
  title: 'The grandfather paradox',
  module: 1, klass: ['II', 'III'], domains: ['logic', 'relativity'], hypothetical: true,
  keywords: ['grandfather paradox', 'time travel', 'time machine', 'closed timelike curve', 'kill your grandfather', 'novikov', 'self-consistency', 'deutsch', 'travel back in time', 'causal loop'],
  summary: 'A bit sent back in time passes through a gate that may negate it. A single classical history has no consistent solution when the gate always flips; Deutsch\'s model has the half-and-half mixture as its fixed point.',
  background: [
    'If a traveller could return to the past and prevent an event on which the journey depends, the journey would both occur and not occur. The paradox can be reduced to one bit: a signal emerges from a time machine, passes through a NOT gate and enters the machine to become the signal that emerged. The condition "the value that emerges equals the negation of itself" has no solution.',
    'General relativity admits solutions containing closed timelike curves, although it is unknown whether any can be realised. Two principal proposals keep such space-times free of contradiction. The self-consistency principle associated with Novikov holds that only histories that are consistent around the loop occur. Deutsch\'s model lets the looping system be in a mixed state and requires only that the state be a fixed point of the evolution; for the negating gate the unique fixed point assigns probability one half to each value. Neither proposal has experimental support, because no closed timelike curve is available.',
  ],
  phenomena: ['Closed causal loop', 'Consistency constraint on histories', 'Fixed point of a stochastic map', 'Oscillation of the undamped iteration'],
  laws: ['causality', 'logic_nc', 'kolmogorov'],
  refs: ['Lewis, D. (1976). The paradoxes of time travel. American Philosophical Quarterly 13, 145–152.', 'Friedman, J. et al. (1990). Cauchy problem in spacetimes with closed timelike curves. Physical Review D 42, 1915–1930.', 'Echeverria, F., Klinkhammer, G. & Thorne, K. S. (1991). Billiard balls in wormhole spacetimes with closed timelike curves: classical theory. Physical Review D 44, 1077–1099.', 'Deutsch, D. (1991). Quantum mechanics near closed timelike lines. Physical Review D 44, 3197–3217.', 'Lloyd, S. et al. (2011). Closed timelike curves via postselection: theory and experimental test of consistency. Physical Review Letters 106, 040403.'],
  inputs: [
    inp('q_flip', 'Probability that the gate negates the bit', '1', 1, { min: 0, max: 1, kind: 'hypothetical', aliases: ['flip probability', 'probability of killing', 'gate probability'] }),
    inp('p_0', 'Initial guess for the probability that the emerging bit is 1', '1', 1, { min: 0, max: 1, kind: 'hypothetical', aliases: ['initial probability', 'initial state'] }),
    inp('n_it', 'Passes around the loop to iterate', '1', 40, { min: 4, max: 400, kind: 'numerical', aliases: ['iterations', 'passes'] }),
    inp('seed', 'Random seed', '1', 11, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('single_history', 'There is a single classical history: the bit has one definite value on the loop.', { why: 'The everyday picture in which the paradox is stated', alt: 'Deutsch\'s model: the bit on the loop may be in a probabilistic mixture, constrained only to be a fixed point of the gate\'s action.', affects: ['n_cons', 'p_fix'] }),
    asm('novikov', 'Only self-consistent histories occur: what enters the time machine is what emerged from it.', { why: 'Novikov\'s self-consistency principle; the minimal requirement for a loop in one space-time', alt: 'No consistency constraint: the traveller arrives in a separate branch whose history need not match the one departed from.', affects: ['n_cons', 'P_cons'] }),
  ],
  symbols: { x_in: ['Bit value emerging from the time machine', '1'], x_out: ['Bit value entering the time machine', '1'], f_g: ['Gate action in a given history (1 = negate)', '1'], P_cons: ['Total weight of self-consistent histories', '1'], p_in: ['Probability that the emerging bit is 1', '1'], p_out: ['Probability that the entering bit is 1', '1'], p_fix: ['Fixed-point probability', '1'], rho_c: ['Contraction factor per pass', '1'], S_fix: ['Entropy of the fixed-point state', '1'] },
  equations: a => (a.single_history ? [
    eq('gate', 'Gate acting on a definite bit', 'x_out', 'x_in + f_g - 2*x_in*f_g', { kind: 'definition', origin: 'Exclusive-or written arithmetically' }),
    ...(a.novikov ? [eq('ctc', 'Consistency around the loop', 'x_in', 'x_out', { kind: 'boundary', origin: 'Novikov self-consistency', needs: ['novikov'] })] : []),
    eq('pc', 'Weight of self-consistent histories', 'P_cons', a.novikov ? '1 - q_flip' : '1', { kind: 'derived', origin: a.novikov ? 'Only histories in which the gate does not negate satisfy the loop condition' : 'No constraint is imposed' }),
  ] : [
    eq('chan', 'Gate acting on the probability of the value 1', 'p_out', 'p_in + q_flip*(1 - 2*p_in)', { kind: 'law', origin: 'Total probability for a bit-flip channel', needs: [] }),
    ...(a.novikov ? [
      eq('ctc', 'Deutsch consistency condition', 'p_in', 'p_out', { kind: 'boundary', origin: 'Deutsch (1991): the state on the loop is a fixed point of the evolution', needs: ['novikov'] }),
      eq('fix', 'Fixed point', 'p_fix', '1/2', { kind: 'derived', origin: 'Solution of p = p + q(1 − 2p) for q > 0' }),
      eq('ent', 'Entropy of the fixed point (bits)', 'S_fix', '-(p_fix*ln(p_fix) + (1 - p_fix)*ln(1 - p_fix))/ln(2)', { kind: 'definition', origin: 'Shannon entropy' }),
    ] : []),
    eq('rate', 'Contraction factor per pass', 'rho_c', 'abs(1 - 2*q_flip)', { kind: 'derived', origin: 'Linear map about the fixed point' }),
  ]),
  derivation: a => [
    { text: 'Let x be the value of the bit that emerges from the time machine. The gate outputs the negation of x when it acts and x otherwise; the output then enters the machine.', tex: 'x_{out} = x_{in}\\oplus f,\\qquad f\\in\\{0,1\\}' },
    ...(a.single_history ? [
      a.novikov
        ? { text: 'In a single history the value entering must be the value that emerged. This holds exactly when the gate does not negate. If the gate always negates there is no consistent history at all.', tex: 'x_{in} = x_{in}\\oplus f \\iff f = 0' }
        : { text: 'Without a consistency requirement the output is simply delivered to a different history, and every combination is allowed.', tex: 'x_{out} = x_{in}\\oplus f\\quad\\text{(no constraint)}' },
    ] : [
      { text: 'Describe the bit by the probability p that its value is 1. A gate that negates with probability q maps p linearly.', tex: 'p_{out} = (1-q)\\,p_{in} + q\\,(1-p_{in}) = p_{in} + q\\,(1-2p_{in})' },
      { text: 'Deutsch\'s condition asks only that the state entering the machine equal the state that emerged. For any q > 0 this has exactly one solution.', tex: 'p = p + q(1-2p) \\iff p = \\tfrac12' },
      { text: 'Iterating the map changes the distance from the fixed point by the factor (1 − 2q) per pass. For q = 1 the plain iteration alternates for ever, the dynamical image of the paradox, while its running average converges to one half.', tex: 'p_k - \\tfrac12 = (1-2q)^k\\left(p_0-\\tfrac12\\right)' },
    ]),
  ],
  solve(v, a) {
    const q = v.q_flip, p0 = v.p_0, n = int(v.n_it, 4, 2000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const seq = ctcIterate(q, p0, n), steps = seq.map((_, i) => i);
    let run = 0; const avg = seq.map((p, i) => { run += p; return run / (i + 1); });
    const rho = Math.abs(1 - 2 * q), dev0 = Math.abs(p0 - 0.5);
    const nConv = dev0 <= 1e-6 ? 0 : rho >= 1 ? Infinity : rho === 0 ? 1 : Math.max(1, Math.ceil(Math.log(1e-6 / dev0) / Math.log(rho)));
    // enumeration of definite histories (value emerging, gate action) carrying non-zero weight
    const hist = [];
    for (const x of [0, 1]) for (const f of [0, 1]) { const w = f ? q : 1 - q; if (w > 0) hist.push({ x, f, w, ok: (x ^ f) === x }); }
    const allowed = a.novikov ? hist.filter(h => h.ok) : hist;
    const nCons = allowed.length, pCons = a.novikov ? 1 - q : 1;
    // single-history trial runs: does the value survive one pass unchanged?
    let x = p0 >= 0.5 ? 1 : 0, okCount = 0; const bits = [x];
    for (let k = 0; k < n; k++) { const f = rnd() < q ? 1 : 0; if (!f) okCount++; x ^= f; bits.push(x); }
    const pFix = 0.5, sFix = 1, noFix = a.single_history ? 'Not applicable: a single history has no mixed state' : !a.novikov ? 'Not applicable: no consistency condition is imposed' : undefined;
    let verdict, code;
    if (!a.novikov) { verdict = 'No constraint imposed: the altered bit belongs to another branch and nothing is contradicted'; code = 2; }
    else if (a.single_history) { code = q >= 1 ? 0 : 1; verdict = q >= 1 ? 'Paradox: no self-consistent single history exists' : q <= 0 ? 'Consistent: the gate never negates' : 'Consistent only in histories where the gate fails to negate'; }
    else { code = 1; verdict = q > 0 ? 'Consistent: the unique fixed point is the equal mixture of 0 and 1' : 'Consistent: every state is a fixed point; the maximum-entropy rule selects the equal mixture'; }
    const warnings = ['Closed timelike curves are hypothetical. The results state what each consistency rule implies for the toy circuit, not what would be observed.'];
    if (!a.single_history && a.novikov && rho >= 1 && dev0 > 0) warnings.push(q >= 1 ? 'With a gate that always negates, plain iteration alternates and never settles; the fixed point exists nevertheless and is reached by the running average.' : 'With a gate that never negates, every state is a fixed point.');
    return {
      scalars: [
        scalar('verdict', 'Consistency of the loop', code, '1', { text: verdict, status: 'hypothetical' }),
        scalar('n_cons', 'Definite histories permitted', nCons, '1', { text: `${nCons} of ${hist.length} with non-zero weight`, status: 'hypothetical' }),
        scalar('P_cons', 'Total weight of the permitted histories', pCons, '1', { ...PCT, status: 'hypothetical' }),
        scalar('f_cons', 'Simulated fraction of passes that leave the bit unchanged', okCount / n, '1', PCT),
        scalar('p_fix', 'Fixed-point probability that the bit is 1', noFix ? NaN : pFix, '1', { text: noFix, status: 'hypothetical' }),
        scalar('S_fix', 'Entropy of the fixed-point state (bits)', noFix ? NaN : sFix, '1', { text: noFix ? 'Not applicable' : undefined, status: 'hypothetical' }),
        scalar('rho_c', 'Contraction factor per pass', rho, '1'),
        scalar('n_conv', 'Passes for plain iteration to come within 10⁻⁶ of one half', nConv, '1', { text: Number.isFinite(nConv) ? undefined : 'Never: the iteration does not contract' }),
        scalar('p_avg', 'Running average of the iterated probability', avg[n], '1'),
        scalar('p_end', 'Iterated probability after the last pass', seq[n], '1'),
      ],
      series: [
        line('iteration', 'Probability that the bit is 1 after each pass around the loop', 'Pass', '–', steps, [{ label: 'Plain iteration', data: seq, dash: a.single_history }, { label: 'Running average', data: avg, dash: a.single_history }, { label: 'Fixed point 1/2', data: steps.map(() => 0.5), dash: true }], 'Probability', '–', { status: 'hypothetical' }),
        line('history', 'A single definite history followed around the loop', 'Pass', '–', steps, [{ label: 'Bit value', data: bits, dash: !a.single_history }], 'Bit value', '–', { status: 'hypothetical' }),
        line('deviation', 'Distance of the plain iteration from the fixed point', 'Pass', '–', steps, [{ label: '|p − 1/2|', data: seq.map(p => Math.max(Math.abs(p - 0.5), 1e-17)) }], 'Distance', '–', { logy: true, status: 'hypothetical' }),
      ],
      checks: [
        check('One half is a fixed point of the gate', 0.5 + q * (1 - 2 * 0.5) - 0.5, 1e-15, 'p = p + q(1 − 2p) at p = 1/2'),
        check('Probabilities remain in [0, 1]', seq.some(p => p < -1e-12 || p > 1 + 1e-12) ? 1 : 0, 0, ''),
        check('Weights of all definite histories sum to two', N.sum(hist.map(h => h.w)) - 2, 1e-12, 'One unit of probability for each possible emerging value'),
      ],
      warnings,
    };
  },
  benchmarks() {
    const out = [], s = ctcIterate(0.25, 1, 10);
    out.push(bench('Deviation after ten passes with flip probability one quarter', s[10] - 0.5, 0.5 * Math.pow(0.5, 10), 'Geometric contraction (1 − 2q)ᵏ', 1e-12));
    const o = ctcIterate(1, 0.9, 9);
    out.push(bench('Running average of the alternating iteration for a certain flip', N.mean(o), 0.5, 'Cesàro mean of p₀, 1 − p₀, p₀, …', 1e-12));
    out.push(bench('Fixed point of the half-flip channel reached in one pass', ctcIterate(0.5, 0.2, 1)[1], 0.5, 'p + ½(1 − 2p) = ½', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    return svg(`
      ${S.path('M200 240 C80 240 80 90 200 90 L440 90 C560 90 560 240 440 240 Z', 'd-line')}
      ${S.rect(280, 70, 80, 40, 'd-hazard')} ${S.text(320, 96, 'NOT gate')} ${S.text(320, 60, `acts with probability ${lab(v.q_flip)}`, 'd-text d-small')}
      ${S.rect(270, 220, 100, 40)} ${S.text(320, 246, 'time machine')}
      ${S.arrow(230, 90, 270, 90)} ${S.arrow(370, 90, 420, 90)} ${S.arrow(420, 240, 376, 240)} ${S.arrow(264, 240, 216, 240)}
      ${S.text(120, 170, 'emerges', 'd-text d-small')} ${S.text(120, 186, 'in the past', 'd-text d-small')}
      ${S.text(525, 170, 'enters', 'd-text d-small')} ${S.text(525, 186, 'in the future', 'd-text d-small')}
      ${S.arrow(60, 320, 580, 320, 'd-dim')} ${S.text(320, 340, 'external time', 'd-text d-small')}
      ${S.text(320, 165, a.single_history ? (a.novikov ? 'x = NOT x has no solution' : 'no consistency condition') : 'p = 1 − p  ⇒  p = 1/2')}
      ${S.text(320, 30, 'Hypothetical closed timelike curve', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'X', text: 'The bit that emerges from the time machine is 1' }, { k: 'Y', text: 'The bit that enters the time machine is 1' }],
    premises: ['Y <-> ~X', 'X <-> Y'],
    conclusion: null,
  },
  philosophy: [
    'The paradox is often taken to show that travel into one\'s own past is impossible. What it strictly shows is narrower: no single history contains both the journey and the act that prevents it. Lewis argued that time travel into the past is therefore coherent provided the traveller does not, and in the relevant sense cannot, do what would undo the journey.',
    'The two formal resolutions carry different metaphysical pictures. Self-consistency keeps one history and restricts which initial conditions are jointly possible, which sits uneasily with the idea that local conditions can be freely chosen. Deutsch\'s fixed-point condition always has a solution but is naturally read in terms of many histories, and it introduces nonlinear evolution whose interpretation is disputed.',
    'Because no closed timelike curve is known to exist, the argument functions as a test of the internal coherence of physical theories that permit them, and as a way of exposing assumptions about causation, freedom and the fixity of the past that ordinary reasoning leaves implicit.',
  ],
  experiment: {
    objective: 'Since no closed timelike curve is available, test the internal consistency of each rule by simulation and, for post-selected analogues, by a laboratory circuit that mimics the loop statistics.',
    apparatus: ['A computer simulation of the looped circuit', 'A feedback circuit in which an inverter\'s delayed output is returned to its input, as a classical analogue of the iteration', 'A photonic post-selection experiment of the kind used to emulate consistency conditions'],
    instruments: [{ name: 'Simulation log', measures: 'State after each pass and residual of the consistency condition', range: '1–10⁴ passes', resolution: 'Double precision' }, { name: 'Oscilloscope (analogue circuit)', measures: 'Oscillation or settling of the inverter loop', range: '0–5 V', resolution: '≈ 1 ns' }, { name: 'Coincidence counter (photonic analogue)', measures: 'Fraction of runs passing the post-selection', range: '0–1', resolution: 'Poisson counting error' }],
    procedure: ['Enumerate the definite histories and mark those satisfying the loop condition.', 'Iterate the probabilistic map from several starting states and record the limit or its absence.', 'Vary the gate probability from 0 to 1 and tabulate the fixed point and the rate of approach.', 'In an analogue experiment, compare the fraction of post-selected runs with the weight of consistent histories.'],
    controls: ['A gate that never acts, for which every state is consistent', 'An identity loop with no gate'],
    signatures: ['No consistent definite history when the gate always negates', 'Fixed point at one half for every non-zero gate probability', 'Weight of consistent definite histories equal to one minus the gate probability'],
    safety: [],
  },
  falsify: ['The model is a statement about hypothetical physics and cannot at present be tested directly. Within its own terms it would be refuted by a definite assignment satisfying x = NOT x, or by a fixed point of the bit-flip channel other than one half for non-zero flip probability.', 'If closed timelike curves were found, observation of an inconsistent history would refute self-consistency, and statistics incompatible with a fixed-point state would refute Deutsch\'s condition.'],
  alternatives: [
    { name: 'Novikov self-consistency', text: 'Only globally consistent solutions of the local laws occur. Studies of billiard balls in wormhole space-times found consistent solutions for every initial condition examined, often infinitely many.' },
    { name: 'Deutsch\'s fixed-point model', text: 'The state on the loop is a fixed point of the evolution; a solution always exists. The price is nonlinearity and, on the usual reading, a many-histories ontology.' },
    { name: 'Post-selected closed timelike curves', text: 'Consistency is imposed by post-selection, as in teleportation with a discarded outcome. Paradoxical circuits then have zero probability of occurring, a different prediction from Deutsch\'s.' },
    { name: 'Chronology protection', text: 'Hawking conjectured that quantum effects prevent closed timelike curves from forming, so the question does not arise physically.' },
    { name: 'Branching histories', text: 'The traveller arrives in a different branch; the departure history is unaffected and no constraint is needed. Whether this counts as travel into one\'s own past is disputed.' },
  ],
  limits: 'A one-bit toy circuit with a classical probabilistic gate. Deutsch\'s model is properly formulated for quantum density matrices; the classical channel used here reproduces its result for this circuit only. Nothing is assumed or implied about whether closed timelike curves can exist.',
  numerics: { method: 'Exhaustive enumeration of definite histories; fixed-point iteration of a linear stochastic map with Cesàro averaging', stability: 'Contracts when the flip probability is strictly between 0 and 1', resolution: 'n_it' },
  extensions: ['Quantum version with density matrices and a controlled-NOT interaction', 'Polchinski\'s billiard-ball paradox with a continuum of consistent solutions', 'Computational power of closed timelike curves', 'Comparison of Deutsch and post-selected models on the same circuit'],
};

// ================================================================== 9. Laplace's demon and chaos
/** Lyapunov exponent of the logistic map by orbit averaging of ln|f'(x)|. */
function logisticLyapunov(r, x0, n, burn = 300) {
  let x = x0, s = 0;
  const stepf = () => { x = r * x * (1 - x); if (!(x > 0 && x < 1)) x = 0.5 * (x0 + 0.37) % 1 || 0.31; };
  for (let i = 0; i < burn; i++) stepf();
  for (let i = 0; i < n; i++) { s += Math.log(Math.max(Math.abs(r * (1 - 2 * x)), 1e-300)); stepf(); }
  return s / n;
}
const laplaceDemonChaos = {
  id: 'laplace-demon-chaos',
  title: 'Laplace\'s demon and the limits of prediction',
  module: 1, klass: ['II', 'I'], domains: ['classical', 'logic'],
  keywords: ['laplace\'s demon', 'laplace demon', 'laplaces demon', 'determinism', 'predictability', 'chaos', 'butterfly effect', 'lyapunov exponent', 'logistic map', 'sensitive dependence', 'prediction horizon'],
  summary: 'A deterministic rule with sensitive dependence on initial conditions: Lyapunov exponent of the logistic map, exponential growth of an initial error and the resulting horizon of prediction.',
  background: [
    'Laplace imagined an intellect that knew the positions and velocities of all bodies at one instant and could compute the whole future and past. The image expresses determinism: the present state fixes all other states. It is commonly taken to imply that prediction is limited only by ignorance that could in principle be removed.',
    'Chaotic systems separate the two ideas. Their laws are deterministic, yet nearby states diverge exponentially at a rate given by the largest Lyapunov exponent. Any finite error in the initial state therefore grows to the size of the system in a time that increases only logarithmically with the precision of the measurement. The logistic map is the simplest example; at parameter 4 its exponent is exactly ln 2, so each iteration destroys one binary digit of knowledge.',
  ],
  phenomena: ['Deterministic chaos', 'Exponential divergence of nearby trajectories', 'Logarithmic return on measurement precision', 'Loss of information at a fixed rate per step'],
  laws: ['causality', 'newton2'],
  refs: ['Laplace, P.-S. (1814). Essai philosophique sur les probabilités. Courcier.', 'Lorenz, E. N. (1963). Deterministic nonperiodic flow. Journal of the Atmospheric Sciences 20, 130–141.', 'May, R. M. (1976). Simple mathematical models with very complicated dynamics. Nature 261, 459–467.', 'Lighthill, J. (1986). The recently recognized failure of predictability in Newtonian dynamics. Proceedings of the Royal Society A 407, 35–50.', 'Ott, E. (2002). Chaos in Dynamical Systems, 2nd ed. Cambridge University Press.'],
  inputs: [
    inp('r_map', 'Logistic-map parameter r', '1', 4, { min: 1, max: 4, aliases: ['map parameter', 'growth parameter', 'logistic parameter'] }),
    inp('x_0', 'Initial state', '1', 0.2, { min: 0.001, max: 0.999, aliases: ['initial state', 'initial condition', 'starting value'] }),
    inp('delta_0', 'Uncertainty of the initial state', '1', 1e-10, { min: 1e-15, max: 0.01, aliases: ['measurement precision', 'initial error', 'precision', 'uncertainty'] }),
    inp('Delta_tol', 'Largest tolerable prediction error', '1', 0.1, { min: 0.001, max: 0.5, aliases: ['tolerance', 'tolerable error'] }),
    inp('sigma_n', 'Disturbance per step (used when the dynamics is not isolated)', '1', 1e-12, { min: 1e-16, max: 0.001, aliases: ['noise', 'disturbance'] }),
    inp('n_it', 'Iterations used to estimate the Lyapunov exponent', '1', 20000, { min: 1000, max: 500000, kind: 'numerical', aliases: ['iterations'] }),
    inp('seed', 'Random seed', '1', 5, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('finite_precision', 'The initial state is known only to finite precision.', { why: 'Every physical measurement has finite resolution', alt: 'Laplace\'s demon: the initial state is known exactly, so the deterministic rule gives the future without error for all time.', affects: ['t_star'] }),
    asm('isolated', 'The dynamics is isolated and exactly known: no disturbance acts between steps.', { why: 'Idealised deterministic system', alt: 'A small unpredictable disturbance acts at every step and limits prediction even when the initial state is exact.', affects: ['t_star'] }),
  ],
  symbols: { x_k: ['State at step k', '1'], x_next: ['State at the following step', '1'], lambda_k: ['Local stretching rate at step k', '1'], lambda_L: ['Lyapunov exponent per step', '1'], delta_n: ['Error after n steps', '1'], n_k: ['Number of steps', '1'], delta_eff: ['Effective initial error', '1'], t_star: ['Prediction horizon in steps', '1'] },
  equations: a => {
    const dEff = a.finite_precision && a.isolated ? 'delta_0' : 'delta_eff', limited = a.finite_precision || !a.isolated;
    return [
      eq('map', 'Logistic map', 'x_next', 'r_map*x_k*(1 - x_k)', { kind: 'law', origin: 'May (1976); a deterministic rule' }),
      eq('loc', 'Local stretching rate', 'lambda_k', 'ln(abs(r_map*(1 - 2*x_k)))', { kind: 'definition', origin: 'Logarithm of the derivative of the map; its orbit average is the Lyapunov exponent' }),
      ...(limited ? [
        ...(a.finite_precision && a.isolated ? [] : [eq('eff', 'Effective initial error', 'delta_eff', a.finite_precision ? 'max(delta_0, sigma_n)' : 'sigma_n', { kind: 'closure', origin: 'The larger of the measurement error and the per-step disturbance sets the starting error' })]),
        eq('grow', 'Growth of a small error', 'delta_n', `${dEff}*exp(lambda_L*n_k)`, { kind: 'derived', origin: 'Linearised dynamics averaged along the orbit' }),
        eq('hor', 'Prediction horizon', 't_star', `ln(Delta_tol/${dEff})/lambda_L`, { kind: 'derived', origin: 'Error reaching the tolerance' }),
      ] : [
        eq('grow', 'Error of an exactly known state', 'delta_n', '0', { kind: 'hypothesis', origin: 'Laplace\'s demon: zero initial error stays zero under a deterministic rule' }),
      ]),
    ];
  },
  derivation: a => [
    { text: 'The state evolves by a fixed rule with no element of chance. Given x₀ exactly, every later state is determined.', tex: 'x_{k+1} = r\\,x_k\\,(1-x_k)' },
    { text: 'Two states a small distance δ apart are mapped to states whose separation is multiplied by the magnitude of the derivative of the map.', tex: '\\delta_{k+1} \\approx \\left|r\\,(1-2x_k)\\right|\\,\\delta_k' },
    { text: 'Averaging the logarithm of that factor along the orbit gives the Lyapunov exponent. When it is positive, small errors grow exponentially on average.', tex: '\\lambda = \\lim_{n\\to\\infty}\\frac1n\\sum_{k=0}^{n-1}\\ln\\left|r(1-2x_k)\\right|,\\qquad \\delta_n \\approx \\delta_0\\,e^{\\lambda n}' },
    a.finite_precision || !a.isolated
      ? { text: 'Prediction fails once the error reaches the tolerance Δ. The horizon grows only with the logarithm of the precision: each further decimal digit buys a fixed number of steps.', tex: 't^* = \\frac{1}{\\lambda}\\ln\\frac{\\Delta}{\\delta_0},\\qquad \\frac{\\partial t^*}{\\partial\\log_{10}(1/\\delta_0)} = \\frac{\\ln 10}{\\lambda}' }
      : { text: 'With an exactly known state and an undisturbed rule the error is zero at every step: determinism then does give unlimited prediction. The horizon is finite as soon as either idealisation is relaxed.', tex: '\\delta_0 = 0 \\;\\Rightarrow\\; \\delta_n = 0\\ \\text{for all } n' },
    { text: 'For r = 4 the substitution x = sin²(πθ) turns the map into angle doubling, for which the exponent is exactly ln 2.', tex: 'r = 4:\\qquad \\theta_{k+1} = 2\\theta_k \\bmod 1,\\qquad \\lambda = \\ln 2' },
  ],
  solve(v, a) {
    const r = v.r_map, nIt = int(v.n_it, 1000, 2000000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const lam = logisticLyapunov(r, v.x_0, nIt);
    const d0 = a.finite_precision ? v.delta_0 : 0, sig = a.isolated ? 0 : v.sigma_n, dEff = Math.max(d0, sig);
    const chaotic = lam > 1e-9;
    const horizon = !chaotic || dEff === 0 ? Infinity : Math.max(0, Math.log(v.Delta_tol / dEff) / lam);
    const hText = !chaotic ? 'Unlimited: the orbit is stable and errors do not grow' : dEff === 0 ? 'Unlimited in principle: exact initial state and undisturbed dynamics' : undefined;
    // twin trajectories
    const nT = Math.min(3000, Number.isFinite(horizon) ? Math.ceil(2.2 * horizon) + 40 : 200), clampU = x => Math.min(1 - 1e-16, Math.max(1e-16, x));
    let x = v.x_0, y = clampU(v.x_0 + d0), nMeas = NaN; const steps = [], diff = [], pred = [];
    for (let k = 0; k <= nT; k++) {
      const d = Math.abs(y - x);
      steps.push(k); diff.push(Math.max(d, 1e-18)); pred.push(Math.max(Math.min(dEff * Math.exp(lam * k), 1), 1e-18));
      if (Number.isNaN(nMeas) && d > v.Delta_tol) nMeas = k;
      x = r * x * (1 - x); y = clampU(r * y * (1 - y) + (sig > 0 ? sig * rnd.normal() : 0));
    }
    const fp = chaotic ? Math.log(v.Delta_tol / 1.1e-16) / lam : Infinity;
    const ds = N.logspace(1e-16, 1e-2, 60), rs = N.linspace(2.5, 4, 121);
    const warnings = [];
    if (!chaotic) warnings.push('At this parameter the orbit settles on a stable fixed point or cycle. The system is predictable for all time; the limit on prediction arises only in the chaotic range.');
    if (dEff === 0 && chaotic) warnings.push('The twin trajectories in the simulation start identically and remain identical. A real computation still loses one binary digit per step at r = 4 because of rounding, so even the "exact" orbit is reliable for only a few dozen steps in double precision.');
    return {
      scalars: [
        scalar('lambda_L', 'Lyapunov exponent per step', lam, '1', { note: chaotic ? 'chaotic' : 'regular' }),
        scalar('lam_bits', 'Information lost per step (bits)', lam / Math.LN2, '1'),
        scalar('t_dbl', 'Steps for an error to double', chaotic ? Math.LN2 / lam : Infinity, '1', { text: chaotic ? undefined : 'Errors do not grow' }),
        scalar('t_star', 'Prediction horizon (steps)', horizon, '1', { text: hText }),
        scalar('n_meas', 'Step at which the simulated twin trajectories first differ by more than the tolerance', nMeas, '1', { text: Number.isNaN(nMeas) ? 'Not reached in the simulated run' : undefined }),
        scalar('dt_dec', 'Extra steps gained per further decimal digit of precision', chaotic ? Math.LN10 / lam : Infinity, '1', { text: chaotic ? undefined : 'Not applicable' }),
        scalar('n_fp', 'Horizon of a double-precision computation', fp, '1', { text: chaotic ? undefined : 'Unlimited' }),
        scalar('delta_eff', 'Effective initial error', dEff, '1'),
      ],
      series: [
        line('divergence', 'Separation of two initially close trajectories', 'Step', '–', steps, [{ label: 'Simulated separation', data: diff }, { label: 'δ₀ exp(λn), capped at 1', data: pred, dash: true }, { label: 'Tolerance', data: steps.map(() => v.Delta_tol), dash: true }], 'Separation', '–', { logy: true }),
        line('horizon', 'Prediction horizon against initial precision', 'Initial uncertainty', '–', ds, [{ label: 'Horizon', data: ds.map(d => (chaotic ? Math.max(0, Math.log(v.Delta_tol / d) / lam) : NaN)) }, { label: 'Zero', data: ds.map(() => 0), dash: true }], 'Steps', '–', { logx: true, note: chaotic ? 'A straight line on a logarithmic axis: precision buys time only logarithmically.' : 'No finite horizon: the orbit is stable.' }),
        line('lyapunov', 'Lyapunov exponent against the map parameter', 'Parameter r', '–', rs, [{ label: 'Lyapunov exponent', data: rs.map(q => Math.max(-3, logisticLyapunov(q, 0.3, 300, 200))) }, { label: 'Zero', data: rs.map(() => 0), dash: true }], 'Exponent per step', '–'),
      ],
      checks: [
        check('Exponent does not exceed the bound ln r', Math.max(0, lam - Math.log(Math.max(r, 1)) - 1e-9), 1e-9, 'The derivative of the map is at most r in magnitude'),
        check('States remain in the unit interval', diff.some(d => d > 1) ? 1 : 0, 0, ''),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const out = [];
    out.push(bench('Lyapunov exponent at r = 4', logisticLyapunov(4, 0.2, 200000), Math.LN2, 'Exact value ln 2 from conjugacy with the doubling map', 0.01));
    out.push(bench('Lyapunov exponent at r = 2.5', logisticLyapunov(2.5, 0.2, 2000), -Math.LN2, 'Stable fixed point x* = 0.6 with derivative −1/2', 1e-9));
    out.push(bench('Lyapunov exponent at r = 3.2', logisticLyapunov(3.2, 0.2, 2000), 0.5 * Math.log(0.16), 'Stable two-cycle with multiplier 4 + 2r − r² = 0.16', 1e-9));
    const s = this.solve({ ...v, r_map: 4, delta_0: 1e-10, Delta_tol: 0.1 }, { finite_precision: true, isolated: true });
    out.push(bench('Horizon times exponent for δ₀ = 10⁻¹⁰ and Δ = 0.1', val(s, 't_star') * val(s, 'lambda_L'), 9 * Math.LN10, 'ln(Δ/δ₀): nine decades, about 30 steps at one bit per step', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const up = [], lo = [];
    for (let i = 0; i <= 40; i++) { const x = 90 + i * 12, s = 2 * Math.exp(i * 0.1); up.push([x, 190 - 18 * Math.sin(i * 0.5) - s]); lo.push([x, 190 - 18 * Math.sin(i * 0.5) + s]); }
    return svg(`
      ${S.poly(up)} ${S.poly(lo, 'd-line d-hazard')}
      ${S.circle(90, 190, 5)} ${S.text(90, 225, `x₀ ± ${a.finite_precision ? lab(v.delta_0) : '0'}`, 'd-text d-small')}
      ${S.dim(570, up[40][1], 570, lo[40][1], '')} ${S.text(600, 194, 'Δ', 'd-text', 'middle')}
      ${S.arrow(90, 300, 570, 300, 'd-dim')} ${S.text(330, 322, 'time (steps)', 'd-text d-small')}
      ${S.text(320, 50, 'Deterministic rule: x → r x (1 − x)')}
      ${S.text(320, 75, `r = ${lab(v.r_map)}; nearby states separate as exp(λ n)`, 'd-text d-small')}
      ${S.text(330, 345, 'Prediction horizon t* = ln(Δ/δ₀)/λ', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Det', text: 'The laws are deterministic' }, { k: 'Exact', text: 'The initial state is known with unlimited precision' }, { k: 'Chaos', text: 'The dynamics has sensitive dependence on initial conditions' }, { k: 'Pred', text: 'The future can be predicted arbitrarily far ahead' }],
    premises: ['Det', 'Chaos', '~Exact', '(Det & Exact) -> Pred', '(Chaos & ~Exact) -> ~Pred'],
    conclusion: 'Det & ~Pred',
  },
  philosophy: [
    'Determinism is a claim about the world: one state fixes the others. Predictability is a claim about an observer: what can be inferred from obtainable information with obtainable computation. Laplace\'s image runs the two together by granting the observer exact data. Chaos shows that the inference from the first to the second fails for any observer with finite precision.',
    'The distinction matters for how probabilistic descriptions are understood. In a chaotic deterministic system probabilities express limited knowledge of the initial state, yet they are forced on every finite observer and are in that sense objective features of the epistemic situation.',
    'The argument leaves the metaphysical question of determinism open. It also does not by itself bear on free will: unpredictability is neither freedom nor its absence. What it removes is the assumption that a deterministic theory is automatically a predictive one.',
  ],
  experiment: {
    objective: 'Measure the rate at which two nearly identical initial conditions of a deterministic system diverge and verify the logarithmic dependence of the prediction horizon on initial precision.',
    apparatus: ['A computer iterating the logistic map in two or more arithmetic precisions', 'A physical chaotic system such as a driven double pendulum, a dripping tap or a chaotic electronic circuit (Chua\'s circuit)', 'A data-acquisition system able to prepare or select nearly identical initial states'],
    instruments: [{ name: 'Arbitrary-precision arithmetic library', measures: 'Reference trajectory', range: '50–1000 significant digits', resolution: 'Exact to the working precision' }, { name: 'Angle encoder or voltage digitiser', measures: 'State of the physical system', range: 'Full scale of the motion', resolution: '12–16 bits' }, { name: 'Timer', measures: 'Time at which trajectories separate beyond tolerance', range: '0–100 s', resolution: '1 ms' }],
    procedure: ['Compute a reference orbit at high precision.', 'Start a second orbit displaced by a known small amount and record the separation at each step.', 'Fit the exponential part of the growth to obtain the Lyapunov exponent.', 'Repeat with the initial displacement reduced by factors of ten and record the step at which the tolerance is exceeded.'],
    controls: ['A parameter value with a stable cycle, for which the separation should decay', 'Comparison of single and double precision runs from identical starting values'],
    signatures: ['Separation growing as a straight line on a logarithmic axis until it saturates', 'Slope equal to ln 2 per step at r = 4', 'Horizon increasing by ln 10/λ steps for each tenfold improvement of precision'],
    safety: ['For a mechanical pendulum: guard the swing area and secure the pivot'],
  },
  falsify: ['An orbit-averaged exponent at r = 4 that differs from ln 2 beyond statistical error.', 'A chaotic regime in which the measured prediction horizon grows in proportion to the precision instead of to its logarithm.'],
  alternatives: [
    { name: 'Laplacian determinism', text: 'With exact initial data and unlimited computation the future is fully calculable. This is logically consistent; the idealisation of exact data is what fails for physical observers.' },
    { name: 'Intrinsic indeterminism', text: 'Quantum mechanics, on most interpretations, makes some outcomes irreducibly probabilistic, limiting prediction independently of chaos.' },
    { name: 'Computational limits', text: 'Even with exact data, a predictor that is part of the universe it predicts faces limits of memory, speed and self-reference.' },
    { name: 'Statistical predictability', text: 'Although individual trajectories are unpredictable beyond the horizon, invariant measures and long-term statistics of chaotic systems can be predicted reliably.' },
  ],
  limits: 'One-dimensional logistic map with parameter between 1 and 4. The horizon formula assumes exponential growth at the mean rate, valid while the error is small; local growth rates fluctuate, so simulated and estimated horizons agree only approximately. The exponent is estimated from a finite orbit and carries statistical error of order n^(−1/2).',
  numerics: { method: 'Orbit averaging of the logarithmic derivative; direct iteration of twin trajectories', order: 0.5, stability: 'Round-off itself grows at the Lyapunov rate; the reference orbit is meaningful statistically, not pointwise', resolution: 'n_it' },
  extensions: ['Lorenz system and weather prediction', 'Finite-size Lyapunov exponents and scale-dependent predictability', 'Shadowing and the reliability of numerical chaotic orbits', 'Prediction of long-term statistics from the invariant density'],
};

// ================================================================== 10. Olbers' paradox
const olbersParadox = {
  id: 'olbers-paradox',
  title: 'Olbers\' paradox: why the night sky is dark',
  module: 1, klass: ['II', 'I'], domains: ['space', 'logic'],
  keywords: ['olbers\' paradox', 'olbers paradox', 'olbers', 'dark night sky', 'why is the night sky dark', 'night sky', 'infinite universe', 'sky brightness', 'static universe', 'darkness at night'],
  summary: 'In an infinite, static, eternal universe filled uniformly with stars, every shell contributes equal flux and the sky would blaze. Partial sums against radius, and the finite brightness that results from a finite age and expansion.',
  background: [
    'If stars are distributed uniformly through infinite space, the number in a thin shell around the observer grows as the square of its radius while the flux from each falls as the inverse square. Every shell therefore delivers the same flux, and the total grows without limit; allowing for nearer stars hiding more distant ones, the sky would be as bright as the surface of a star in every direction. The dark night sky contradicts this.',
    'Absorption by intervening matter does not help, since in an eternal universe the absorber would heat up and re-radiate. The accepted resolution is that the universe has a finite age: light has reached us only from within a horizon of order the speed of light times that age, and within it the stars cover a minute fraction of the sky. Expansion reduces the brightness further through redshift, but by a factor of order unity; the finite age is the decisive effect.',
  ],
  phenomena: ['Inverse-square dilution of flux', 'Growth of source counts with distance', 'Occultation of distant stars by nearer ones', 'Light-travel horizon', 'Cosmological redshift'],
  laws: ['energy', 'causality', 'sr'],
  refs: ['Olbers, H. W. M. (1823). Über die Durchsichtigkeit des Weltraums. Berliner Astronomisches Jahrbuch für das Jahr 1826, 110–121.', 'Harrison, E. R. (1977). The dark night sky paradox. American Journal of Physics 45, 119–124.', 'Harrison, E. R. (1987). Darkness at Night: A Riddle of the Universe. Harvard University Press.', 'Wesson, P. S., Valle, K. & Stabell, R. (1987). The extragalactic background light and a definitive resolution of Olbers\'s paradox. Astrophysical Journal 317, 601–606.', 'Wesson, P. S. (1991). Olbers\'s paradox and the spectral intensity of the extragalactic background light. Astrophysical Journal 367, 399–406.'],
  inputs: [
    inp('n_s', 'Mean number density of stars', '1/Mpc^3', 1.5e8, { min: 1e6, max: 1e12, aliases: ['star density', 'number density', 'stellar density'], src: 'Number of Sun-like stars that reproduces the observed local luminosity density of galaxies, of order 1–2 × 10⁸ solar luminosities per cubic megaparsec' }),
    inp('L_s', 'Luminosity of a typical star', 'W', 3.828e26, { min: 1e24, max: 1e30, aliases: ['luminosity', 'stellar luminosity'], src: 'Nominal solar luminosity (IAU 2015)' }),
    inp('R_s', 'Radius of a typical star', 'm', 6.957e8, { min: 1e7, max: 1e11, aliases: ['stellar radius', 'star radius'], src: 'Nominal solar radius (IAU 2015)' }),
    inp('t_0', 'Age of the universe (or Hubble time in the steady-state case)', 'Gyr', 13.8, { min: 0.1, max: 100, aliases: ['age of the universe', 'age', 'hubble time'], src: 'Planck Collaboration (2020), rounded' }),
    inp('R_plot', 'Largest radius shown in the partial sums', 'Mpc', 1e19, { min: 1e6, max: 1e22, kind: 'numerical', aliases: ['plot radius', 'maximum radius'] }),
  ],
  assumptions: [
    asm('eternal', 'The stars have been shining for an unlimited time, so light from every distance has arrived.', { why: 'Premise of the classical paradox', alt: 'The universe has a finite age: only sources within the light-travel distance c·t₀ contribute.', affects: ['F_sky'] }),
    asm('static', 'Space is static: light is not redshifted on its way.', { why: 'Premise of the classical paradox', alt: 'Space expands. In a matter-dominated model the bolometric brightness is 3/5 of the static value for the same age; for an eternal steady-state universe it is one quarter of n L c times the Hubble time.', affects: ['F_sky'] }),
    asm('transparent', 'Stars do not hide one another: every star in every shell contributes its full flux.', { why: 'The simple shell argument', alt: 'Nearer stars occult more distant ones, so the sum saturates at the surface brightness of a star.', affects: ['F_sky'] }),
  ],
  symbols: { j_L: ['Luminosity density', 'W/m^3'], F_sky: ['Flux received from the whole sky', 'W/m^2'], F_R: ['Flux summed out to a given radius', 'W/m^2'], F_surf: ['Flux when every line of sight ends on a star', 'W/m^2'], r: ['Distance from the observer', 'm'], ell_s: ['Mean free path of a line of sight before it meets a star', 'm'], R_h: ['Light-travel horizon', 'm'], f_cov: ['Fraction of the sky covered by stellar discs', '1'] },
  equations: a => [
    eq('lum', 'Luminosity density', 'j_L', 'n_s*L_s', { kind: 'definition' }),
    eq('path', 'Mean free path of a line of sight', 'ell_s', '1/(n_s*pi*R_s^2)', { kind: 'derived', origin: 'Geometric cross-section of a stellar disc' }),
    a.transparent
      ? eq('shell', 'Flux contributed per unit thickness of shell', 'pd(F_R, r)', 'n_s*L_s', { kind: 'law', origin: 'Number of stars 4πr²n dr times flux L/(4πr²) from each', needs: ['transparent'] })
      : eq('shell', 'Flux contributed per unit thickness of shell, with occultation', 'pd(F_R, r)', 'n_s*L_s*exp(-r/ell_s)', { kind: 'law', origin: 'Inverse-square law with the probability that the line of sight is still unobstructed' }),
    eq('surf', 'Flux when the sky is covered by stellar discs', 'F_surf', 'L_s/(pi*R_s^2)', { kind: 'derived', origin: 'Limit n L ℓ of the occulted sum; four times the surface flux of a star' }),
    ...(a.eternal && a.static ? [
      a.transparent ? eq('tot', 'Sum out to radius r', 'F_R', 'n_s*L_s*r', { kind: 'derived', origin: 'Every shell contributes equally: the sum grows without bound', needs: ['eternal', 'static', 'transparent'] }) : eq('tot', 'Total from an infinite universe', 'F_sky', 'L_s/(pi*R_s^2)', { kind: 'derived', origin: 'Saturation of the occulted sum', needs: ['eternal', 'static'] }),
    ] : a.eternal ? [
      eq('tot', 'Total in an eternal, exponentially expanding (steady-state) universe', 'F_sky', 'n_s*L_s*c*t_0/4', { kind: 'derived', origin: 'Bolometric intensity integral with scale factor exp(t/t₀) and constant proper emissivity', needs: ['eternal'] }),
    ] : [
      eq('hor', 'Light-travel horizon', 'R_h', 'c*t_0', { kind: 'law', origin: 'Finite speed of light and finite age' }),
      eq('tot', a.static ? 'Total from within the horizon' : 'Total from within the horizon, with redshift', 'F_sky', `${a.static ? '' : '(3/5)*'}${a.transparent ? 'n_s*L_s*c*t_0' : 'n_s*L_s*ell_s*2*exp(-c*t_0/(2*ell_s))*sinh(c*t_0/(2*ell_s))'}`, { kind: 'derived', origin: a.static ? 'Shell sum truncated at the horizon' : 'Bolometric intensity integral with scale factor proportional to t^(2/3) and conserved comoving sources', needs: a.static ? ['static'] : [], ...(a.transparent ? {} : { note: `The occulted sum n L ℓ (1 − exp(−c t₀/ℓ)) is written with a hyperbolic sine so that it stays accurate when the horizon is far smaller than the mean free path.${a.static ? '' : ' The redshift factor 3/5 is applied to it, an approximation that is very accurate in the same regime.'}` }) }),
    ]),
    eq('cov', 'Fraction of the sky covered by stars', 'f_cov', 'F_sky/F_surf', { kind: 'definition' }),
  ],
  derivation: a => [
    { text: 'A shell of radius r and thickness dr contains 4πr² n dr stars. Each delivers the flux L/(4πr²), so the shell contributes an amount independent of its radius.', tex: 'dF = 4\\pi r^2 n\\,dr\\cdot\\frac{L}{4\\pi r^2} = n\\,L\\,dr' },
    a.transparent
      ? { text: 'Summing over shells out to radius R gives a flux proportional to R, which diverges for an infinite, eternal, static universe.', tex: 'F(R) = n\\,L\\,R \\;\\longrightarrow\\; \\infty' }
      : { text: 'A line of sight travels a mean distance ℓ = 1/(nπR_s²) before ending on a stellar disc. Counting only unobstructed stars the sum saturates at the brightness of a stellar surface.', tex: 'F(R) = n L\\,\\ell\\left(1-e^{-R/\\ell}\\right) \\;\\longrightarrow\\; \\frac{L}{\\pi R_s^2}' },
    ...(a.eternal ? [] : [{ text: 'If the stars have shone only for a time t₀, no light has arrived from beyond R_h = c t₀. Since R_h is vastly smaller than ℓ, only a tiny fraction of sight lines end on a star.', tex: 'F = n\\,L\\,c\\,t_0,\\qquad f_{cov} = \\frac{c\\,t_0}{\\ell} \\ll 1' }]),
    ...(a.static ? [] : [{ text: 'In an expanding universe each photon is redshifted and the arrival rate is reduced. For conserved comoving sources the bolometric flux is the static result weighted by the scale factor at emission.', tex: 'F = n_0 L\\,c\\int_0^{t_0}\\frac{a(t)}{a(t_0)}\\,dt = \\tfrac35\\,n_0 L\\,c\\,t_0\\quad\\text{for } a\\propto t^{2/3}' }]),
    { text: 'The observed darkness therefore rules out the conjunction of the four classical premises; it does not by itself say which one fails.', tex: '\\lnot\\,(\\text{infinite}\\land\\text{static}\\land\\text{eternal}\\land\\text{uniform})' },
  ],
  solve(v, a) {
    const nL = v.n_s * v.L_s, ell = 1 / (v.n_s * Math.PI * v.R_s ** 2), Rh = C.c * v.t_0, Fsurf = v.L_s / (Math.PI * v.R_s ** 2);
    const Ftr = R => nL * R, Foc = R => nL * ell * (-Math.expm1(-R / ell)), Fof = R => (a.transparent ? Ftr(R) : Foc(R));
    let F, text;
    if (a.eternal && a.static) { F = a.transparent ? Infinity : Fsurf; text = a.transparent ? 'Diverges: grows without bound as more shells are added' : undefined; }
    else if (a.eternal) F = nL * Rh / 4;
    else F = (a.static ? 1 : 0.6) * Fof(Rh);
    const fcov = F / Fsurf, Mpc = 3.0856775814913673e22;
    const Rs = N.logspace(1, Math.max(v.R_plot / Mpc, 100), 120).map(x => x * Mpc);
    const ages = N.logspace(0.1, 100, 60).map(x => x * 1e9 * YEAR);
    // numerical shell sum to the horizon as an independent check of the closed form
    const rr = N.linspace(0, Rh, 2001), numSum = N.trapz(rr, rr.map(x => (a.transparent ? nL : nL * Math.exp(-x / ell))));
    const warnings = [];
    if (a.eternal && a.static) warnings.push(a.transparent ? 'The classical premises give an infinitely bright sky. This is the paradox: the observed darkness shows that at least one premise is false.' : 'With occultation the classical premises give a sky as bright as the surface of a star in every direction, about 180 000 times the flux of full sunlight for Sun-like stars. This is the paradox in the form stated by Olbers.');
    if (!a.static && !a.transparent) warnings.push(a.eternal ? 'Occultation is not applied in the steady-state case: the result n L c t₀/4 counts every star, which is accurate while c t₀ is much smaller than the mean free path.' : 'Occultation and expansion are combined approximately: the redshift factor is applied to the occulted sum. The difference is negligible while the horizon is much smaller than the mean free path.');
    return {
      scalars: [
        scalar('j_L', 'Luminosity density', nL, 'W/m^3'),
        scalar('ell_s', 'Mean free path of a line of sight before it meets a star', ell, 'm', { show: 'ly' }),
        scalar('R_h', 'Light-travel distance c·t₀', Rh, 'm', { show: 'ly' }),
        scalar('F_surf', 'Flux if every line of sight ended on a star', Fsurf, 'W/m^2'),
        scalar('F_sky', 'Flux received from the whole sky', F, 'W/m^2', { text }),
        scalar('f_cov', 'Sky brightness as a fraction of a stellar surface', fcov, '1', { text: Number.isFinite(fcov) ? undefined : 'Unbounded' }),
        scalar('F_plot', 'Partial sum out to the largest radius shown', Fof(Rs[Rs.length - 1]), 'W/m^2'),
        scalar('R_eq', 'Radius at which the transparent sum equals a stellar surface', ell, 'm', { show: 'ly' }),
        scalar('F_hor', 'Static sum truncated at the light-travel distance', Fof(Rh), 'W/m^2'),
      ],
      series: [
        line('partial-sums', 'Flux summed over shells out to a given radius', 'Radius', 'Mpc', Rs.map(x => x / Mpc), [{ label: 'Every star counted (transparent)', data: Rs.map(Ftr), dash: !a.transparent }, { label: 'With occultation', data: Rs.map(Foc), dash: a.transparent }, { label: 'Stellar-surface brightness', data: Rs.map(() => Fsurf), dash: true }, { label: 'Within the light-travel distance', data: Rs.map(() => Foc(Rh)), dash: true }], 'Flux', 'W/m²', { logx: true, logy: true, note: `The light-travel distance is ${lab(Rh / Mpc, 'Mpc')}; the mean free path is ${lab(ell / Mpc, 'Mpc')}.` }),
        line('age', 'Sky flux against the age of the universe', 'Age', 'Gyr', ages.map(t => t / (1e9 * YEAR)), [{ label: 'Static, finite age', data: ages.map(t => Fof(C.c * t)) }, { label: 'Expanding, matter-dominated', data: ages.map(t => 0.6 * Fof(C.c * t)), dash: true }], 'Flux', 'W/m²', { logx: true, logy: true }),
      ],
      checks: [
        check('Numerical shell sum to the light-travel distance against the closed form', (numSum - Fof(Rh)) / Fof(Rh), 1e-6, 'Trapezoidal sum over 2000 shells'),
        check('Saturated flux equals n L ℓ', (nL * ell - Fsurf) / Fsurf, 1e-12, 'Identity n L/(n π R²) = L/(π R²)'),
        check('Occulted sum never exceeds the brightness of a stellar surface', Math.max(0, Foc(Rh) / Fsurf - 1), 1e-12, 'Physical bound on the sky brightness'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const off = { eternal: false, static: true, transparent: true }, out = [];
    const r = this.solve(v, off);
    out.push(bench('Finite-age flux against n L c t₀', val(r, 'F_sky'), v.n_s * v.L_s * C.c * v.t_0, 'Shell sum truncated at the horizon', 1e-12));
    const e = this.solve(v, { ...off, static: false });
    const us = N.linspace(0, 1, 4001), xe = N.linspace(0, 12, 4001);
    out.push(bench('Ratio of expanding to static brightness', val(e, 'F_sky') / val(r, 'F_sky'), N.trapz(us, us.map(u => 3 * u ** 4)), 'Matter-dominated expansion: ∫(t/t₀)^(2/3) dt/t₀ = 3/5, integrated numerically with t/t₀ = u³', 1e-6));
    const ss = this.solve(v, { eternal: true, static: false, transparent: true });
    out.push(bench('Steady-state brightness as a fraction of n L c t₀', val(ss, 'F_sky') / val(r, 'F_sky'), N.trapz(xe, xe.map(x => Math.exp(-4 * x))), 'Redshift and dilution (a/a₀)⁴ integrated over an unlimited past: ∫ e^(−4x) dx = 1/4', 1e-4));
    const o = this.solve(v, { eternal: true, static: true, transparent: false });
    out.push(bench('Olbers\' limit against the stellar-surface value', val(o, 'F_sky'), v.L_s / (Math.PI * v.R_s ** 2), 'L/(π R_s²)', 1e-12));
    const ell = 1 / (v.n_s * Math.PI * v.R_s ** 2), xs = N.linspace(0, 3 * ell, 4001);
    out.push(bench('Occulted sum to three mean free paths, numerical against analytic', N.trapz(xs, xs.map(x => Math.exp(-x / ell))) / ell, 1 - Math.exp(-3), '∫ e^(−r/ℓ) dr', 1e-6));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const stars = [[150, 110], [470, 95], [520, 250], [130, 260], [250, 60], [400, 300], [565, 170], [80, 180], [300, 310], [210, 290]];
    return svg(`
      ${S.circle(320, 185, 60, 'd-line')} ${S.circle(320, 185, 110, 'd-line')} ${S.circle(320, 185, 160, 'd-dim')}
      ${S.circle(320, 185, 6)} ${S.text(320, 210, 'observer', 'd-text d-small')}
      ${stars.map(([x, y]) => S.circle(x, y, 3, 'd-hazard')).join('')}
      ${S.arrow(470, 95, 335, 178)} ${S.arrow(130, 260, 306, 190)}
      ${S.text(320, 118, 'shell: stars ∝ r², flux of each ∝ 1/r²', 'd-text d-small')}
      ${S.text(320, 20, a.eternal ? 'Eternal universe: every shell contributes' : `Finite age: only shells within c·t₀ = ${lab(C.c * v.t_0 / LY / 1e9, 'Gly')} contribute`)}
      ${S.text(320, 355, 'Each shell adds the same flux n L dr', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Infinite', text: 'The universe is infinite in extent' }, { k: 'Static', text: 'The universe is static' }, { k: 'Eternal', text: 'The stars have shone for an unlimited time' }, { k: 'Uniform', text: 'Stars fill space uniformly' }, { k: 'Bright', text: 'The night sky is uniformly bright' }],
    premises: ['(Infinite & Static & Eternal & Uniform) -> Bright', '~Bright'],
    conclusion: '~(Infinite & Static & Eternal & Uniform)',
  },
  philosophy: [
    'Olbers\' paradox is a rare case in which an everyday observation — that it gets dark at night — refutes a cosmological model. The inference is a simple modus tollens: the premises entail a bright sky, the sky is dark, so the premises are not all true.',
    'The logic identifies that something must be given up but not what. Historically the favoured candidates were absorption, a finite stellar system and a hierarchical distribution; the finite age of the luminous universe became the accepted answer only in the twentieth century, when independent evidence for it appeared. The episode illustrates the Duhem–Quine point that an observation tests a conjunction of hypotheses.',
    'It also shows the value of quantification. The qualitative argument suggests that expansion and redshift are the cure; the calculation shows that they change the result by a factor of order unity, whereas the finite age changes it by many orders of magnitude.',
  ],
  experiment: {
    objective: 'Measure the integrated brightness of the night sky from extragalactic sources and compare it with the flux expected from the luminosity density of the universe and its age.',
    apparatus: ['A space-borne or outer-solar-system photometer, beyond most of the zodiacal light', 'Deep galaxy counts in several wavebands to integrate the resolved light', 'Models of zodiacal and Galactic foregrounds for subtraction'],
    instruments: [{ name: 'Absolute photometer with a cold shutter', measures: 'Sky surface brightness', range: '0.1–5 µm', resolution: '≈ 1 nW m⁻² sr⁻¹' }, { name: 'Wide-field imaging survey', measures: 'Galaxy number counts and fluxes', range: 'to about 30th magnitude', resolution: 'Photometric error of a few per cent' }, { name: 'Redshift survey', measures: 'Luminosity density as a function of epoch', range: '0 < z < 10', resolution: '—' }],
    procedure: ['Measure the total sky brightness in fields at high Galactic and ecliptic latitude.', 'Subtract modelled zodiacal light, diffuse Galactic light and resolved stars.', 'Integrate the galaxy counts to obtain a lower limit to the extragalactic background.', 'Compare with the prediction from the measured luminosity density integrated over cosmic time with the redshift factor.'],
    controls: ['Dark-current and stray-light measurements with the shutter closed', 'Fields at different ecliptic latitudes to test the zodiacal subtraction', 'Independent upper limits from the attenuation of gamma rays from distant blazars'],
    signatures: ['An extragalactic background of order 10⁻⁷ W m⁻² over the whole sky in the optical and near infrared, many orders of magnitude below stellar-surface brightness', 'Agreement between the integrated galaxy light and the luminosity density times the light-travel time, to within a factor of a few', 'A spectrum reflecting the redshifted starlight of all epochs'],
    safety: [],
  },
  falsify: ['An extragalactic background light greatly exceeding the luminosity density multiplied by c times the age of the universe.', 'Evidence that stars shone at their present density for a time long compared with the mean free path divided by c, combined with a dark sky, would refute the finite-age resolution.'],
  alternatives: [
    { name: 'Finite age (accepted resolution)', text: 'Stars have shone for about ten billion years; light from beyond the corresponding distance has not arrived, and within it stars cover a negligible fraction of the sky.' },
    { name: 'Expansion and redshift', text: 'Redshift lowers photon energies and arrival rates. It reduces the bolometric background by roughly a factor of two and is essential only in eternal expanding models such as the steady-state theory.' },
    { name: 'Absorption by dust', text: 'Proposed by Chéseaux and Olbers. In an eternal universe the dust reaches equilibrium with the radiation and re-emits as much as it absorbs, so the sky is no darker.' },
    { name: 'Finite or hierarchical distribution of stars', text: 'A finite island of stars, or a fractal distribution whose mean density falls with scale, also gives a finite sum. Observations show approximate uniformity on large scales.' },
    { name: 'Finite stellar lifetimes', text: 'Stars do not contain enough energy to fill space with radiation at stellar-surface temperature; the available luminous energy is exhausted long before equilibrium is reached. This is closely related to the finite-age resolution.' },
  ],
  limits: 'Identical stars at uniform density in Euclidean space; bolometric flux summed over the whole sky. The expanding case uses matter-dominated expansion with conserved comoving sources and a constant luminosity; evolution of the star-formation rate, the cosmological constant and spectral effects are not included. The numbers are order-of-magnitude estimates: with the default density of Sun-like stars the luminosity density is 1.5 × 10⁸ solar luminosities per cubic megaparsec and the finite-age flux n L c t₀ is about 2.6 × 10⁻⁷ W m⁻² over the whole sky, that is about 20 nW m⁻² sr⁻¹ (12 nW m⁻² sr⁻¹ with the redshift factor 3/5), the same order as the measured extragalactic background light.',
  numerics: { method: 'Closed-form shell integrals; trapezoidal check to the horizon' },
  extensions: ['Luminosity density evolving with redshift from the measured star-formation history', 'Spectral energy distribution of the background light', 'The cosmic microwave background as the redshifted glow of an opaque early universe', 'Gravitational analogue: the Seeliger paradox for Newtonian gravity'],
};

// ================================================================== 11. Birthday problem
/** Probability that among n people at least two have birthdays within w days of each other (w = 0: same day); d equally likely days on a circular year. */
function birthdayExact(n, d, w = 0) {
  if (n < 2) return 0;
  if (d < n * (w + 1)) return 1;
  let lq = 0; for (let i = 1; i < n; i++) lq += Math.log((d - n * w - i) / d);
  return -Math.expm1(lq);
}
/** Smallest group size for which the probability of a match reaches one half. */
function birthdayN50(d, w = 0) { for (let n = 2; n <= d + 1; n++) if (birthdayExact(n, d, w) >= 0.5) return n; return d + 1; }
/** Seasonal day weights p_i = (1 + a cos(2π i/d))/d, which sum to one for d ≥ 2. */
const seasonal = (d, amp) => Float64Array.from({ length: d }, (_, i) => (1 + amp * Math.cos(2 * Math.PI * i / d)) / d);
/** P(all distinct) for 0..J people with unequal day probabilities: q_j = j!·e_j(p), by one pass over the days. */
function distinctProbs(p, J) { const q = new Float64Array(J + 1); q[0] = 1; for (let i = 0; i < p.length; i++) for (let j = Math.min(J, i + 1); j >= 1; j--) q[j] += j * p[i] * q[j - 1]; return q; }
const birthdayProblem = {
  id: 'birthday-problem',
  title: 'The birthday problem',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['birthday problem', 'birthday paradox', 'shared birthday', 'same birthday', 'birthday', 'collision probability', 'hash collision', 'coincidence', '23 people'],
  summary: 'Probability that at least two of n people share a birthday among d equally likely days: exact product, exponential approximation, the group size for an even chance, and a seeded simulation.',
  background: [
    'In a group of only 23 people the probability that two share a birthday exceeds one half, although there are 365 possible days. The result surprises because intuition compares the group size with the number of days, whereas the relevant quantity is the number of pairs, which grows as the square of the group size: 23 people form 253 pairs.',
    'The same mathematics governs collisions of hash values, the security of digital signatures against "birthday attacks", and the assessment of coincidences generally. Unequal birthday frequencies, as actually observed, can only increase the probability of a match.',
  ],
  phenomena: ['Quadratic growth of the number of pairs', 'Complement rule', 'Poisson approximation for rare coincidences', 'Monte-Carlo estimation'],
  laws: ['kolmogorov'],
  refs: ['von Mises, R. (1939). Über Aufteilungs- und Besetzungswahrscheinlichkeiten. Revue de la Faculté des Sciences de l\'Université d\'Istanbul 4, 145–163.', 'Feller, W. (1968). An Introduction to Probability Theory and Its Applications, Vol. 1, 3rd ed. Wiley.', 'Naus, J. I. (1968). An extension of the birthday problem. The American Statistician 22(1), 27–29.', 'Bloom, D. M. (1973). A birthday problem. American Mathematical Monthly 80, 1141–1142.', 'Diaconis, P. & Mosteller, F. (1989). Methods for studying coincidences. Journal of the American Statistical Association 84, 853–861.'],
  inputs: [
    inp('n_p', 'Number of people', '1', 23, { min: 1, max: 400, aliases: ['people', 'group size', 'persons', 'students'] }),
    inp('d_y', 'Number of equally likely days', '1', 365, { min: 2, max: 10000, aliases: ['days', 'days in the year', 'possible values', 'bins'] }),
    inp('w_d', 'Window for a near match, in days (used when near matches count)', '1', 1, { min: 0, max: 7, aliases: ['window', 'within days'] }),
    inp('a_s', 'Seasonal amplitude of birth frequency (used when birthdays are not uniform)', '1', 0.2, { min: 0, max: 1, aliases: ['seasonality', 'seasonal amplitude'] }),
    inp('n_trials', 'Simulated groups', '1', 10000, { min: 100, max: 200000, kind: 'numerical', aliases: ['trials', 'simulations'] }),
    inp('seed', 'Random seed', '1', 2, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('uniform', 'Every day is equally likely to be a birthday.', { why: 'The standard statement; a good approximation for real births', alt: 'Birth frequency varies sinusoidally through the year with the stated amplitude. A match becomes more likely.', affects: ['P_share'] }),
    asm('exact_day', 'Only birthdays on exactly the same day count as a match.', { why: 'The standard statement', alt: 'Birthdays within the stated number of days of each other count. Far fewer people are then needed.', affects: ['P_share', 'n_50'] }),
    asm('independent', 'Birthdays of different people are independent.', { why: 'No twins or selection by date', alt: 'Not modelled quantitatively: dependence such as twins in the group raises the probability of a match; a warning is given.' }),
  ],
  symbols: { N_pair: ['Number of pairs of people', '1'], P_share: ['Probability of at least one match', '1'], P_apx: ['Exponential approximation', '1'], Q_k: ['Probability that the first k people have no match', '1'], Q_next: ['Probability that the first k + 1 people have no match', '1'], k_i: ['Number of people already considered', '1'], s_2: ['Sum of squared day probabilities', '1'], E_pair: ['Expected number of matching pairs', '1'] },
  equations: a => [
    eq('pairs', 'Number of pairs', 'N_pair', 'n_p*(n_p - 1)/2', { kind: 'definition' }),
    ...(a.uniform ? [
      a.exact_day
        ? eq('rec', 'No-match recurrence', 'Q_next', 'Q_k*(1 - k_i/d_y)', { kind: 'law', origin: 'Multiplication rule: the next person must avoid k occupied days', needs: ['uniform', 'independent'] })
        : eq('rec', 'No-near-match recurrence', 'Q_next', 'Q_k*(1 - (n_p*w_d + k_i)/d_y)', { kind: 'derived', origin: 'Naus (1968): circular spacings of at least w + 1 days', needs: ['uniform', 'independent'] }),
      eq('exp', 'Expected number of matching pairs', 'E_pair', a.exact_day ? 'N_pair/d_y' : 'N_pair*min((2*w_d + 1)/d_y, 1)', { kind: 'derived', origin: 'Linearity of expectation over pairs' + (a.exact_day ? '' : '; a window that spans the whole year makes every pair a match') }),
    ] : [
      eq('s2', 'Probability that two given people share a day', 's_2', 'ifpos(d_y - 2.5, (1 + a_s^2/2)/d_y, (1 + a_s^2)/d_y)', { kind: 'derived', origin: 'Sum of squared day probabilities for a sinusoidal distribution: the squared cosine averages one half over three or more days and one over two days' }),
      a.exact_day
        ? eq('exp', 'Expected number of matching pairs', 'E_pair', 'N_pair*s_2', { kind: 'derived', origin: 'Linearity of expectation over pairs' })
        : eq('exp', 'Expected number of matching pairs', 'E_pair', 'N_pair*ifpos(d_y - 2*w_d - 1, s_2 + (2*w_d + (a_s^2/2)*(sin((2*w_d + 1)*pi/d_y)/sin(pi/d_y) - 1))/d_y, 1)', { kind: 'derived', origin: 'Linearity of expectation over pairs; the chance that two people fall within w days is s₂ plus the sum over non-zero offsets of Σ pᵢ pᵢ₊ₒ = (1 + ½a² cos(2πo/d))/d, and is one when the window spans the whole year' }),
    ]),
    eq('apx', 'Exponential approximation', 'P_apx', '1 - exp(-E_pair)', { kind: 'derived', origin: 'Poisson approximation for the number of matching pairs' }),
  ],
  derivation: a => [
    { text: 'It is easier to compute the probability that no two people match. Add people one at a time: the (k + 1)-th must avoid the k days already taken.', tex: 'Q_n = \\prod_{k=0}^{n-1}\\left(1-\\frac{k}{d}\\right) = \\frac{d!}{(d-n)!\\,d^{\\,n}}' },
    { text: 'The probability of at least one shared birthday is the complement.', tex: 'P(n) = 1 - Q_n' },
    { text: 'Taking logarithms and using ln(1 − x) ≈ −x for small x gives an exponential in the number of pairs divided by the number of days.', tex: 'P(n) \\approx 1 - \\exp\\left(-\\frac{n(n-1)}{2d}\\right) \\approx 1 - e^{-n^2/2d}' },
    { text: 'Setting the approximation equal to one half gives the group size for an even chance, which grows only as the square root of the number of days.', tex: 'n_{50} \\approx \\tfrac12 + \\sqrt{\\tfrac14 + 2d\\ln 2} \\approx 1.18\\sqrt{d}' },
    ...(a.exact_day ? [] : [{ text: 'If birthdays within w days count, the no-match event requires n gaps of at least w + 1 days around a circular year, which shortens the effective year by n w days.', tex: 'Q_n = \\prod_{i=1}^{n-1}\\frac{d - n w - i}{d}' }]),
    ...(a.uniform ? [] : [{ text: 'With unequal day probabilities p_i the no-match probability is n! times the n-th elementary symmetric polynomial of the p_i. By Schur concavity it is largest when all days are equally likely.', tex: 'Q_n = n!\\,e_n(p_1,\\ldots,p_d) \\le \\frac{d!}{(d-n)!\\,d^{\\,n}}' }]),
  ],
  solve(v, a) {
    const n = int(v.n_p, 1, 5000), d = int(v.d_y, 2, 100000), w = a.exact_day ? 0 : int(v.w_d, 0, 30), amp = a.uniform ? 0 : Math.min(v.a_s, 1);
    const nT = int(v.n_trials, 100, 1000000), rnd = N.rng(int(v.seed, 1, 2147483647)), warnings = [];
    const pairs = n * (n - 1) / 2, p = a.uniform ? null : seasonal(d, amp);
    // pMatch: probability that two given people fall within w days of each other (w = 0: on the same day)
    let exact, n50, exactOf, haveExact = true, s2 = 1 / d, pMatch = Math.min((2 * w + 1) / d, 1);
    if (a.uniform) { exactOf = m => birthdayExact(m, d, w); exact = exactOf(n); n50 = birthdayN50(d, w); }
    else {
      s2 = 0; for (let i = 0; i < d; i++) s2 += p[i] * p[i];
      // a window that reaches every day of the circular year makes any two people a match
      if (2 * w + 1 >= d) pMatch = 1; else { pMatch = 0; for (let o = -w; o <= w; o++) for (let i = 0; i < d; i++) pMatch += p[i] * p[((i + o) % d + d) % d]; }
      if (w === 0) {
        const J = Math.min(d, Math.max(n, Math.ceil(1.7 * Math.sqrt(d)) + 10)), q = distinctProbs(p, J);
        exactOf = m => (m > d ? 1 : m <= J ? 1 - q[m] : NaN); exact = exactOf(n);
        n50 = d + 1; for (let m = 2; m <= J; m++) if (1 - q[m] >= 0.5) { n50 = m; break; }
      } else { haveExact = false; exactOf = m => -Math.expm1(-m * (m - 1) / 2 * pMatch); exact = NaN; n50 = NaN; warnings.push('No closed form is used for near matches with unequal birthday frequencies; the simulated frequency and the Poisson approximation are reported.'); }
    }
    const ePair = pairs * pMatch, apx = -Math.expm1(-ePair), apxSimple = -Math.expm1(-n * n / (2 * d) * (2 * w + 1));
    if (!a.independent) warnings.push('Dependence between birthdays is not modelled. Positive dependence, such as twins, raises the probability of a match above the value shown.');
    // simulation
    const perGroup = Math.min(n, 1.3 * Math.sqrt(d / (2 * w + 1)) + 2) * (1 + 2 * amp), nSim = Math.max(200, Math.min(nT, Math.floor(600000 / perGroup)));
    const notes = nSim < nT ? [`The simulation was limited to ${nSim} groups to keep the run short for this group size and number of days.`] : [];
    const stamp = new Int32Array(d), cp = marks(nSim), xs = [], ys = []; let hits = 0, ci = 0;
    for (let t = 1; t <= nSim; t++) {
      let match = false;
      for (let i = 0; i < n && !match; i++) {
        let day = Math.floor(rnd() * d);
        if (amp > 0) while (rnd() * (1 + amp) >= p[day] * d) day = Math.floor(rnd() * d);
        for (let o = -w; o <= w; o++) if (stamp[((day + o) % d + d) % d] === t) { match = true; break; }
        stamp[day] = t;
      }
      if (match) hits++;
      if (t === cp[ci]) { ci++; xs.push(t); ys.push(hits / t); }
    }
    const fSim = hits / nSim, ref = haveExact ? exact : fSim, sig = Math.sqrt(Math.max(ref * (1 - ref), 0) / nSim);
    const nMax = Math.min(Math.max(n, Number.isFinite(n50) ? 2 * n50 : 60, 10), 1200), stepN = Math.max(1, Math.ceil(nMax / 150));
    const ns = []; for (let m = 1; m <= nMax; m += stepN) ns.push(m);
    return {
      scalars: [
        scalar('P_share', `Probability of at least one ${w ? 'near ' : ''}match`, exact, '1', { ...PCT, text: haveExact ? undefined : 'No closed form: see the simulated frequency' }),
        scalar('P_apx', 'Poisson approximation 1 − exp(−expected matching pairs)', apx, '1', PCT),
        scalar('P_apx2', 'Simplest approximation 1 − exp(−n²/2d)', apxSimple, '1', PCT),
        scalar('f_sim', 'Simulated frequency', fSim, '1', PCT),
        scalar('sigma_mc', 'Standard error of the simulated frequency', sig, '1'),
        scalar('n_sim', 'Groups simulated', nSim, '1'),
        scalar('n_50', 'Smallest group with at least an even chance', n50, '1', { text: Number.isFinite(n50) ? undefined : 'Not computed for this combination' }),
        scalar('N_pair', 'Number of pairs', pairs, '1'),
        scalar('E_pair', 'Expected number of matching pairs', ePair, '1'),
        scalar('s_2', 'Probability that two given people share a day', s2, '1'),
      ],
      series: [
        line('p-vs-n', 'Probability of a match against group size', 'Number of people', '–', ns, [{ label: haveExact ? 'Exact' : 'Poisson approximation', data: ns.map(exactOf) }, { label: '1 − exp(−n²/2d)', data: ns.map(m => -Math.expm1(-m * m / (2 * d) * (2 * w + 1))), dash: true }, { label: 'One half', data: ns.map(() => 0.5), dash: true }], 'Probability', '–'),
        line('convergence', 'Simulated frequency against number of groups', 'Groups simulated', '–', xs, [{ label: 'Simulated', data: ys }, { label: haveExact ? 'Exact' : 'Final estimate', data: xs.map(() => ref), dash: true }], 'Frequency', '–', { logx: true }),
      ],
      checks: [
        check('Simulated frequency against the exact probability', haveExact ? fSim - exact : 0, 4 * sig + 1e-12, 'Within four binomial standard errors'),
        check('Pigeonhole principle', n > d && haveExact ? exact - 1 : 0, 1e-12, 'More people than days forces a match'),
        check('Probability lies in [0, 1]', haveExact && (exact < 0 || exact > 1) ? 1 : 0, 0, ''),
        check('Unequal frequencies do not lower the probability', !a.uniform && haveExact ? Math.max(0, birthdayExact(n, d, 0) - exact) : 0, 1e-9, 'Schur concavity of the no-match probability'),
      ],
      warnings, notes,
    };
  },
  benchmarks(v, a) {
    const out = [];
    out.push(bench('Twenty-three people, 365 days', birthdayExact(23, 365), 0.5072972343, 'Classical value 0.5072972343…', 1e-9));
    out.push(bench('Smallest group for an even chance of birthdays within one day', birthdayN50(365, 1), 14, 'Naus (1968)', 1e-12));
    out.push(bench('Smallest group for an even chance, 365 days', birthdayN50(365), 23, 'von Mises (1939); Feller (1968)', 1e-12));
    // brute-force enumeration of a small case to test the near-match formula
    let ok = 0; const dd = 11, tot = dd ** 3;
    for (let x = 0; x < dd; x++) for (let y = 0; y < dd; y++) for (let z = 0; z < dd; z++) { const c = (p, q) => { const g = Math.abs(p - q); return Math.min(g, dd - g) <= 1; }; if (c(x, y) || c(x, z) || c(y, z)) ok++; }
    out.push(bench('Near-match formula against enumeration (3 people, 11 days, ±1 day)', birthdayExact(3, dd, 1), ok / tot, 'Exhaustive enumeration of 1331 cases', 1e-12));
    out.push(bench('Unequal-frequency algorithm with zero amplitude', 1 - distinctProbs(seasonal(365, 0), 23)[23], birthdayExact(23, 365), 'Must reduce to the uniform result', 1e-10));
    const r = this.solve(v, a), P = val(r, 'P_share');
    if (Number.isFinite(P) && P > 0) out.push(bench('Simulated against exact probability', val(r, 'f_sim'), P, 'Tolerance of four standard errors', Math.max(4 * val(r, 'sigma_mc') / P, 1e-9)));
    return out;
  },
  validation: [],
  diagram(v) {
    const n = Math.min(int(v.n_p, 1, 5000), 12), cx = 200, cy = 185, R = 105, pts = Array.from({ length: n }, (_, i) => [cx + R * Math.cos(2 * Math.PI * i / n), cy + R * Math.sin(2 * Math.PI * i / n)]);
    const lines = []; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) lines.push(S.line(pts[i][0].toFixed(1), pts[i][1].toFixed(1), pts[j][0].toFixed(1), pts[j][1].toFixed(1), 'd-dim'));
    const N0 = int(v.n_p, 1, 5000);
    return svg(`
      ${lines.join('')} ${pts.map(([x, y]) => S.circle(x.toFixed(1), y.toFixed(1), 6)).join('')}
      ${S.text(200, 330, `${n} people shown: ${n * (n - 1) / 2} pairs`, 'd-text d-small')}
      ${S.text(470, 120, `${N0} people`)} ${S.text(470, 150, `${N0 * (N0 - 1) / 2} pairs`)} ${S.text(470, 180, `${int(v.d_y, 2, 100000)} days`)}
      ${S.text(470, 225, 'Each pair matches with', 'd-text d-small')} ${S.text(470, 243, 'probability about 1/d', 'd-text d-small')}
      ${S.text(320, 40, 'Coincidences are counted over pairs, not people')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Likely', text: 'A shared birthday is more likely than not in the group' }, { k: 'Comparable', text: 'The number of people is comparable with the number of days' }],
    premises: ['Likely', '~Comparable'],
    conclusion: '~(Likely -> Comparable)',
  },
  philosophy: [
    'The birthday problem is called a paradox only because the answer conflicts with expectation; nothing in it is contradictory. It is a clean example of a veridical paradox, in which the calculation is secure and it is intuition that must be revised.',
    'The misjudgement has an identifiable source. People tend to answer a different question — the chance that someone shares my birthday — which does require a group comparable with the number of days. The original question quantifies over all pairs.',
    'More broadly the problem cautions against reading significance into coincidences. With enough opportunities for a match, some match is to be expected, and its occurrence is weak evidence for any special explanation.',
  ],
  experiment: {
    objective: 'Estimate the frequency of shared birthdays in groups of a given size and compare it with the exact probability.',
    apparatus: ['Published birthday lists for many groups of equal size, such as sports squads or school classes', 'Alternatively a computer simulation drawing days uniformly at random'],
    instruments: [{ name: 'Tabulation of each group', measures: 'Whether at least two members share a day and month', range: '≥ 100 groups', resolution: 'One group' }, { name: 'Histogram of all birthdays', measures: 'Departure from uniformity', range: '365 days', resolution: 'One day' }],
    procedure: ['Fix the group size and collect birthdays for many independent groups.', 'Record for each group whether any two members share a birthday.', 'Compute the frequency and its binomial standard error.', 'Repeat for several group sizes and plot against the exact curve.'],
    controls: ['Exclude twins and other related pairs', 'Check for selection effects that concentrate birthdays, such as age cut-off dates in junior sport', 'Simulated groups drawn from the observed birthday histogram'],
    signatures: ['About half of all groups of 23 containing a shared birthday', 'Frequency following 1 − exp(−n(n − 1)/2d) closely for moderate n', 'A slight excess over the uniform prediction where birth dates are unevenly distributed'],
    safety: [],
  },
  falsify: ['An observed match frequency in large samples of independent groups that lies significantly below the uniform-year prediction, since unequal frequencies can only raise it.', 'A simulated frequency that differs from the exact probability by many standard errors.'],
  alternatives: [
    { name: 'The "same as mine" problem', text: 'The probability that someone in a group of n shares a particular person\'s birthday is 1 − (1 − 1/d)ⁿ, which reaches one half only at n = 253 for 365 days. Confusing the two questions accounts for most of the surprise.' },
    { name: 'Non-uniform birthdays', text: 'Real birth dates show seasonal and weekly patterns. The effect on the answer is small and always in the direction of more matches.' },
    { name: 'Near matches and multiple matches', text: 'Counting birthdays within a day of each other needs only 14 people for an even chance; requiring three people to share a day needs 88.' },
  ],
  limits: 'Independent birthdays on a year of d days. The exact uniform results are evaluated in logarithms and are accurate to floating-point precision. The unequal-frequency case uses a sinusoidal distribution; for near matches with unequal frequencies only the simulation and a Poisson approximation are given. Leap days are ignored unless d is set accordingly.',
  numerics: { method: 'Exact product in logarithms; dynamic programme for elementary symmetric polynomials with unequal frequencies; seeded Monte-Carlo simulation', order: 0.5, resolution: 'n_trials' },
  extensions: ['Three or more people sharing a birthday', 'Collision resistance of hash functions and the birthday attack', 'Matches between two distinct groups', 'Empirical birth-date distributions'],
};

// ================================================================== 12. Bayes and the diagnostic test
const bayesDiagnostic = {
  id: 'bayes-diagnostic-test',
  title: 'Base rates and the diagnostic test',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['base rate fallacy', 'base rate', 'diagnostic test', 'false positive', 'positive predictive value', 'bayes theorem', 'bayes', 'sensitivity', 'specificity', 'prevalence', 'screening test', 'medical test'],
  summary: 'Probability of disease given a positive test from prevalence, sensitivity and specificity: predictive values, likelihood ratios and a natural-frequency table.',
  background: [
    'A test that detects a disease in 90 % of those who have it and gives a false alarm in 5 % of those who do not sounds reliable. Yet if only 1 % of the people tested have the disease, most positive results are false: about 15 % of those who test positive are actually ill. Neglecting the prevalence — the base rate — is one of the best documented errors of probabilistic judgement, among clinicians as well as lay people.',
    'Bayes\' theorem gives the correct calculation. It is most transparent in terms of natural frequencies: of 10 000 people, 100 are ill and 90 of them test positive, while 495 of the 9 900 healthy people also test positive, so 90 of the 585 positives are true. In odds form the post-test odds equal the pre-test odds multiplied by the likelihood ratio of the result.',
  ],
  phenomena: ['Conditional probability and its inversion', 'Base-rate neglect', 'Likelihood ratios', 'Dependence of predictive value on the tested population'],
  laws: ['kolmogorov'],
  refs: ['Bayes, T. (1763). An essay towards solving a problem in the doctrine of chances. Philosophical Transactions of the Royal Society 53, 370–418.', 'Casscells, W., Schoenberger, A. & Graboys, T. B. (1978). Interpretation by physicians of clinical laboratory results. New England Journal of Medicine 299, 999–1001.', 'Eddy, D. M. (1982). Probabilistic reasoning in clinical medicine: problems and opportunities. In D. Kahneman, P. Slovic & A. Tversky (eds), Judgment under Uncertainty: Heuristics and Biases, Cambridge University Press, 249–267.', 'Altman, D. G. & Bland, J. M. (1994). Diagnostic tests 2: predictive values. BMJ 309, 102.', 'Gigerenzer, G. & Hoffrage, U. (1995). How to improve Bayesian reasoning without instruction: frequency formats. Psychological Review 102, 684–704.'],
  inputs: [
    inp('prev', 'Prevalence in the tested population', '%', 1, { min: 0.001, max: 99, aliases: ['prevalence', 'base rate', 'prior probability'] }),
    inp('sens', 'Sensitivity (true-positive rate)', '%', 90, { min: 1, max: 100, aliases: ['sensitivity', 'true positive rate', 'detection rate'] }),
    inp('spec', 'Specificity (true-negative rate)', '%', 95, { min: 1, max: 100, aliases: ['specificity', 'true negative rate'] }),
    inp('p_pre', 'Pre-test probability for a patient with symptoms (used when the person is not a random member of the population)', '%', 30, { min: 0.1, max: 99, aliases: ['pre-test probability', 'pretest probability', 'clinical suspicion'] }),
    inp('N_pop', 'Size of the reference population for the frequency table', '1', 10000, { min: 100, max: 1e9, aliases: ['population', 'people tested', 'out of'] }),
  ],
  assumptions: [
    asm('screening', 'The person tested is a random member of the population, so the prior probability is the prevalence.', { why: 'Screening without symptoms', alt: 'The person was tested because of symptoms; the stated pre-test probability replaces the prevalence.', affects: ['PPV', 'NPV'] }),
    asm('single_test', 'The decision rests on a single test result.', { why: 'The standard problem', alt: 'The test is repeated and "positive" means positive on both of two conditionally independent tests.', affects: ['PPV', 'LR_p'] }),
    asm('fixed_rates', 'Sensitivity and specificity are properties of the test and do not depend on who is tested.', { why: 'Usual working assumption', alt: 'Not modelled quantitatively: spectrum effects make both rates vary with disease severity and case mix; a warning is given.' }),
  ],
  symbols: { P_pos: ['Probability of a positive result', '1'], PPV: ['Positive predictive value', '1'], NPV: ['Negative predictive value', '1'], LR_p: ['Likelihood ratio of a positive result', '1'], LR_n: ['Likelihood ratio of a negative result', '1'], O_post: ['Post-test odds of disease after a positive result', '1'] },
  equations: a => {
    const p0 = a.screening ? 'prev' : 'p_pre', se = a.single_test ? 'sens' : 'sens^2', fp = a.single_test ? '(1 - spec)' : '(1 - spec)^2';
    return [
      eq('tot', 'Probability of a positive result', 'P_pos', `${se}*${p0} + ${fp}*(1 - ${p0})`, { kind: 'law', origin: 'Law of total probability' }),
      eq('ppv', 'Positive predictive value', 'PPV', `${se}*${p0}/P_pos`, { kind: 'law', origin: 'Bayes\' theorem' }),
      eq('npv', 'Negative predictive value', 'NPV', `(1 - ${fp})*(1 - ${p0})/(1 - P_pos)`, { kind: 'law', origin: 'Bayes\' theorem' }),
      eq('lrp', 'Likelihood ratio of a positive result', 'LR_p', `${se}/${fp}`, { kind: 'definition' }),
      eq('lrn', 'Likelihood ratio of a negative result', 'LR_n', `(1 - ${se})/(1 - ${fp})`, { kind: 'definition' }),
      eq('odds', 'Post-test odds after a positive result', 'O_post', `LR_p*${p0}/(1 - ${p0})`, { kind: 'derived', origin: 'Odds form of Bayes\' theorem' }),
    ];
  },
  derivation: a => [
    { text: 'Let D denote disease and + a positive result. The test is described by its sensitivity P(+ | D) and specificity P(− | not D); the question asks for P(D | +), the reverse conditional.', tex: 'P(D\\mid +) = \\frac{P(+\\mid D)\\,P(D)}{P(+)}' },
    { text: 'A positive result arises either from a diseased person correctly detected or from a healthy person falsely flagged.', tex: 'P(+) = \\text{sens}\\cdot\\pi + (1-\\text{spec})(1-\\pi)' },
    { text: 'The positive predictive value is the share of true positives among all positives. When the prior π is small the false positives from the large healthy group dominate.', tex: 'PPV = \\frac{\\text{sens}\\cdot\\pi}{\\text{sens}\\cdot\\pi + (1-\\text{spec})(1-\\pi)}' },
    { text: 'In odds form the test multiplies the prior odds by the likelihood ratio, which separates what the test contributes from what was known beforehand.', tex: '\\frac{P(D\\mid +)}{P(\\lnot D\\mid +)} = \\frac{\\text{sens}}{1-\\text{spec}}\\cdot\\frac{\\pi}{1-\\pi}' },
    ...(a.single_test ? [] : [{ text: 'Two conditionally independent positive results multiply the odds by the likelihood ratio twice.', tex: '\\text{odds}_{post} = LR_+^{\\,2}\\cdot\\frac{\\pi}{1-\\pi}' }]),
  ],
  solve(v, a) {
    const pi = a.screening ? v.prev : v.p_pre, m = a.single_test ? 1 : 2, se = Math.pow(v.sens, m), fp = Math.pow(1 - v.spec, m), sp = 1 - fp;
    const pPos = se * pi + fp * (1 - pi), ppv = se * pi / pPos, npv = sp * (1 - pi) / (1 - pPos);
    const lrp = fp > 0 ? se / fp : Infinity, lrn = (1 - se) / sp, oPre = pi / (1 - pi), oPost = lrp * oPre;
    const Np = Math.round(v.N_pop), TP = Np * pi * se, FN = Np * pi * (1 - se), FP = Np * (1 - pi) * fp, TN = Np * (1 - pi) * sp;
    const prev50 = fp / (se + fp), ppvOf = x => (se * x + fp * (1 - x) > 0 ? se * x / (se * x + fp * (1 - x)) : 0), npvOf = x => sp * (1 - x) / (sp * (1 - x) + (1 - se) * x);
    const ps = N.logspace(1e-5, 0.99, 120), ms = [1, 2, 3, 4, 5, 6];
    const warnings = [];
    if (ppv < 0.5 && se > 0.5) warnings.push(`Most positive results are false at this prior probability: of ${lab(TP + FP, '', 4)} positives in ${Np}, only ${lab(TP, '', 4)} are true.`);
    if (!a.fixed_rates) warnings.push('Sensitivity and specificity measured in one population may not transfer to another with a different mix of disease severity; treat the figures as indicative.');
    if (v.sens + v.spec < 1) warnings.push('Sensitivity plus specificity is below 100 %: the test is worse than chance, and a positive result lowers the probability of disease.');
    return {
      scalars: [
        scalar('PPV', 'Positive predictive value: probability of disease given a positive result', ppv, '1', PCT),
        scalar('NPV', 'Negative predictive value: probability of no disease given a negative result', npv, '1', PCT),
        scalar('P_pos', 'Probability of a positive result', pPos, '1', PCT),
        scalar('LR_p', 'Likelihood ratio of a positive result', lrp, '1', { text: Number.isFinite(lrp) ? undefined : 'Unbounded: no false positives' }),
        scalar('LR_n', 'Likelihood ratio of a negative result', lrn, '1'),
        scalar('O_pre', 'Pre-test odds of disease', oPre, '1'),
        scalar('O_post', 'Post-test odds after a positive result', oPost, '1', { text: Number.isFinite(oPost) ? undefined : 'Unbounded' }),
        scalar('TP', 'True positives in the reference population', TP, '1'),
        scalar('FP', 'False positives in the reference population', FP, '1'),
        scalar('FN', 'False negatives in the reference population', FN, '1'),
        scalar('TN', 'True negatives in the reference population', TN, '1'),
        scalar('acc', 'Overall accuracy', (TP + TN) / Np, '1', PCT),
        scalar('prev_50', 'Prior probability at which a positive result is as likely true as false', prev50, '1', PCT),
      ],
      series: [
        line('ppv-vs-prev', 'Predictive values against prior probability', 'Prior probability of disease', '–', ps, [{ label: 'Positive predictive value', data: ps.map(ppvOf) }, { label: 'Negative predictive value', data: ps.map(npvOf) }, { label: 'One half', data: ps.map(() => 0.5), dash: true }], 'Probability', '–', { logx: true }),
        line('frequencies', 'Natural frequencies in the reference population', 'Category', '–', [1, 2, 3, 4], [{ label: 'People', data: [TP, FP, FN, TN] }], 'Number of people', '–', { kind: 'bar', categories: ['True positive', 'False positive', 'False negative', 'True negative'] }),
        line('sequential', 'Probability of disease after successive positive results', 'Number of independent positive tests', '–', ms, [{ label: 'Probability of disease', data: ms.map(k => { const o = v.spec < 1 ? oPre * Math.pow(v.sens / (1 - v.spec), k) : Infinity; return Number.isFinite(o) ? o / (1 + o) : 1; }) }], 'Probability', '–'),
      ],
      checks: [
        check('Natural frequencies add up to the population', (TP + FP + FN + TN - Np) / Np, 1e-12, ''),
        check('Odds form agrees with the direct form', Number.isFinite(oPost) ? oPost / (1 + oPost) - ppv : 0, 1e-12, 'Two statements of Bayes\' theorem'),
        check('Total probability of the result', pPos * ppv + (1 - pPos) * (1 - npv) - pi, 1e-12, 'Averaging the posteriors recovers the prior'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const on = { screening: true, single_test: true, fixed_rates: true }, out = [];
    const e = this.solve({ ...v, prev: 0.01, sens: 0.8, spec: 0.904 }, on);
    out.push(bench('Mammography example: probability of cancer given a positive result', val(e, 'PPV'), 0.008 / (0.008 + 0.09504), 'Gigerenzer & Hoffrage (1995), after Eddy (1982): prevalence 1 %, sensitivity 80 %, false-positive rate 9.6 %, giving about 7.8 %', 1e-12));
    const c = this.solve({ ...v, prev: 0.001, sens: 1, spec: 0.95 }, on);
    out.push(bench('Harvard Medical School problem', val(c, 'PPV'), 0.001 / (0.001 + 0.04995), 'Casscells et al. (1978): about 2 %', 1e-12));
    const d = this.solve({ ...v, prev: 0.01, sens: 0.9, spec: 0.95, N_pop: 10000 }, on);
    out.push(bench('Natural frequencies: true positives among 10 000', val(d, 'TP'), 90, '100 ill, 90 detected', 1e-12));
    out.push(bench('Natural frequencies: false positives among 10 000', val(d, 'FP'), 495, '9 900 healthy, 5 % flagged', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const pi = a.screening ? v.prev : v.p_pre, m = a.single_test ? 1 : 2, se = Math.pow(v.sens, m), fp = Math.pow(1 - v.spec, m), Np = Math.round(v.N_pop);
    const box = (x, y, t1, t2, cls = 'd-body') => `${S.rect(x - 70, y, 140, 46, cls)}${S.text(x, y + 20, t1, 'd-text d-small')}${S.text(x, y + 38, t2)}`;
    return svg(`
      ${box(320, 20, 'people tested', lab(Np, '', 4))}
      ${S.arrow(280, 66, 180, 116)} ${S.arrow(360, 66, 460, 116)}
      ${box(170, 118, 'with the disease', lab(Np * pi, '', 4))} ${box(470, 118, 'without the disease', lab(Np * (1 - pi), '', 4))}
      ${S.arrow(140, 164, 95, 224)} ${S.arrow(200, 164, 245, 224)} ${S.arrow(440, 164, 395, 224)} ${S.arrow(500, 164, 545, 224)}
      ${box(85, 226, 'test positive', lab(Np * pi * se, '', 4), 'd-hazard')} ${box(245, 226, 'test negative', lab(Np * pi * (1 - se), '', 4))}
      ${box(395, 226, 'test positive', lab(Np * (1 - pi) * fp, '', 4), 'd-hazard')} ${box(555, 226, 'test negative', lab(Np * (1 - pi) * (1 - fp), '', 4))}
      ${S.text(320, 315, `Of ${lab(Np * (pi * se + (1 - pi) * fp), '', 4)} positive results, ${lab(Np * pi * se, '', 4)} are true`)}
      ${S.text(320, 340, `Positive predictive value ${lab(100 * pi * se / (pi * se + (1 - pi) * fp), '%')}`, 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Disease', text: 'The person has the disease' }, { k: 'Positive', text: 'The test result is positive' }],
    premises: ['Disease -> Positive', 'Positive'],
    conclusion: 'Disease',
  },
  philosophy: [
    'The base-rate problem shows the difference between the probability of evidence given a hypothesis and the probability of the hypothesis given the evidence. Treating one as the other is, in its deductive limit, the fallacy of affirming the consequent: from "the disease produces a positive result" and "the result is positive" nothing follows about the disease without information on how else a positive result can arise.',
    'It is also a standard illustration of the role of prior probability in inductive inference. Bayesians take the dependence on the prior to be a feature that makes explicit what any sound inference must use; critics worry about where priors come from when no reference population is given. In screening the prior is an observable frequency and the dispute does not arise.',
    'The finding that the same problem becomes easy when stated in natural frequencies has been used to argue that human reasoning is adapted to counts of cases, and that apparent irrationality may reflect the format of information as much as the reasoner.',
  ],
  experiment: {
    objective: 'Measure the predictive values of a test in a defined population and compare them with the values calculated from sensitivity, specificity and prevalence.',
    apparatus: ['A cohort tested with both the index test and an independent reference standard', 'Alternatively coloured counters in an urn to represent the four outcome groups, for a classroom demonstration'],
    instruments: [{ name: 'Index test', measures: 'Positive or negative result', range: '—', resolution: '—' }, { name: 'Reference standard (for example biopsy or long-term follow-up)', measures: 'True disease status', range: '—', resolution: '—' }, { name: 'Two-by-two table', measures: 'Counts of true and false positives and negatives', range: '≥ 1000 people', resolution: 'One person' }],
    procedure: ['Apply the index test and the reference standard to every member of the cohort, with assessors blind to the other result.', 'Tabulate the four outcome counts.', 'Estimate sensitivity, specificity and prevalence with confidence intervals.', 'Compare the observed fraction of true positives among positives with the calculated predictive value.'],
    controls: ['Verification of test-negative as well as test-positive cases, to avoid partial-verification bias', 'Repetition in a population of different prevalence to demonstrate the change in predictive value at fixed sensitivity and specificity'],
    signatures: ['Positive predictive value rising steeply with prevalence', 'Post-test odds equal to pre-test odds times the likelihood ratio', 'Predictive value in low-prevalence screening far below the sensitivity'],
    safety: ['Clinical studies require ethical approval, informed consent and protection of personal data'],
  },
  falsify: ['An observed share of true positives among positives that differs from the Bayes value by more than sampling error when sensitivity, specificity and prevalence are measured in the same cohort.', 'Predictive values that fail to change with prevalence across otherwise comparable populations.'],
  alternatives: [
    { name: 'Base-rate neglect', text: 'The common intuitive answer equates the probability of disease given a positive result with the sensitivity. It is correct only when the prior odds happen to make the two equal.' },
    { name: 'Frequentist reading', text: 'Sensitivity and specificity are long-run error rates of the procedure; without a reference class no probability is assigned to the individual case. Predictive values are then properties of a tested population, not of a patient.' },
    { name: 'Individualised priors', text: 'For a symptomatic patient the relevant prior is the clinical pre-test probability, not the population prevalence, and may be much higher.' },
  ],
  limits: 'Binary disease state and binary test with fixed sensitivity and specificity. Repeated tests are treated as conditionally independent given disease status, which is optimistic when errors have a common cause. Sampling uncertainty in the inputs is not propagated.',
  numerics: { method: 'Closed-form application of Bayes\' theorem' },
  extensions: ['Confidence intervals for predictive values', 'Continuous test results and receiver-operating-characteristic curves', 'Correlated repeat tests', 'Decision thresholds from the costs of false positives and false negatives'],
};

// ================================================================== 13. St Petersburg paradox
const stPetersburg = {
  id: 'st-petersburg',
  title: 'The St Petersburg paradox',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['st petersburg paradox', 'st. petersburg paradox', 'saint petersburg', 'st petersburg', 'infinite expected value', 'bernoulli utility', 'coin until heads', 'doubling game', 'expected utility', 'fair price'],
  summary: 'A coin is tossed until it first shows heads; the prize doubles with every toss. The expected prize diverges, yet a capped bank gives roughly log₂ of the cap and logarithmic utility gives a modest fair price.',
  background: [
    'A fair coin is tossed until it first lands heads. If that happens on toss k the player receives 2ᵏ units. Each possible outcome contributes exactly one unit to the expected value, so the expectation is infinite, and a player who values gambles by their expected monetary value should pay any finite fee to play. Hardly anyone would pay more than a few tens of units.',
    'Daniel Bernoulli proposed in 1738 that people value money by a concave utility, specifically its logarithm, which makes the game worth a small finite amount. Other resolutions point out that no bank can pay unbounded prizes — with a cap the expectation is only about the base-two logarithm of the cap — or that the expectation is a poor guide to a quantity whose sample average grows without settling.',
  ],
  phenomena: ['Divergent expectation', 'Diminishing marginal utility', 'Truncation by finite resources', 'Slow, logarithmic growth of the sample mean'],
  laws: ['kolmogorov'],
  refs: ['Bernoulli, D. (1738). Specimen theoriae novae de mensura sortis. English translation: Exposition of a new theory on the measurement of risk. Econometrica 22 (1954), 23–36.', 'Feller, W. (1945). Note on the law of large numbers and "fair" games. Annals of Mathematical Statistics 16, 301–304.', 'Samuelson, P. A. (1977). St. Petersburg paradoxes: defanged, dissected, and historically described. Journal of Economic Literature 15, 24–55.', 'Peters, O. (2011). The time resolution of the St Petersburg paradox. Philosophical Transactions of the Royal Society A 369, 4913–4931.'],
  inputs: [
    inp('B_cap', 'Largest prize the bank can pay (used when the bank is finite)', '1', 1e9, { min: 2, max: 1e15, aliases: ['bankroll', 'cap', 'maximum prize', 'bank'] }),
    inp('w_0', 'Wealth of the player (used when utility is logarithmic)', '1', 10000, { min: 1, max: 1e12, aliases: ['wealth', 'player wealth'] }),
    inp('p_h', 'Probability of heads (used when the coin is not fair)', '1', 0.6, { min: 0.05, max: 0.95, aliases: ['probability of heads', 'coin bias'] }),
    inp('n_plays', 'Simulated plays', '1', 65536, { min: 100, max: 2000000, kind: 'numerical', aliases: ['plays', 'games', 'trials'] }),
    inp('seed', 'Random seed', '1', 4, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('unlimited_bank', 'The bank can pay any prize, however large.', { why: 'The classical statement', alt: 'Prizes are capped at the bank\'s resources; the expectation becomes finite and small.', affects: ['E_val'] }),
    asm('linear_utility', 'The player values a gamble by its expected monetary value.', { why: 'The premise that generates the paradox', alt: 'The player maximises expected logarithmic utility of wealth (Bernoulli), which gives a finite fair price.', affects: ['c_fair'] }),
    asm('fair_coin', 'The coin is fair.', { why: 'The classical statement', alt: 'Heads has the stated probability. If it exceeds one half the expectation converges without any other change.', affects: ['E_val'] }),
  ],
  symbols: { a_k: ['Contribution of the k-th outcome to the expectation', '1'], k_i: ['Toss on which heads first appears', '1'], E_K: ['Expectation counting only the first K outcomes', '1'], K_t: ['Number of outcomes counted', '1'], L_c: ['Tosses the bank can cover in full', '1'], E_cap: ['Expectation with a capped bank', '1'], U_ln: ['Expected logarithm of the prize', '1'], C_e: ['Certainty equivalent under logarithmic utility of the prize', '1'] },
  equations: a => [
    a.fair_coin
      ? eq('term', 'Contribution of the k-th outcome', 'a_k', '(1/2)^k_i*2^k_i', { kind: 'law', origin: 'Probability 2⁻ᵏ times prize 2ᵏ: every outcome contributes one unit', needs: ['fair_coin'] })
      : eq('term', 'Contribution of the k-th outcome', 'a_k', 'p_h*(1 - p_h)^(k_i - 1)*2^k_i', { kind: 'law', origin: 'Geometric distribution of the first head' }),
    a.fair_coin
      ? eq('part', 'Expectation over the first K outcomes', 'E_K', 'K_t', { kind: 'derived', origin: 'Sum of K equal terms: unbounded as K grows', needs: ['fair_coin'] })
      : eq('part', 'Expectation over the first K outcomes', 'E_K', '2*p_h*(1 - (2*(1 - p_h))^K_t)/(2*p_h - 1)', { kind: 'derived', origin: 'Finite geometric sum with ratio 2(1 − p)', note: 'Indeterminate at a probability of exactly one half, where the sum equals K.' }),
    ...(a.unlimited_bank ? [] : [
      eq('lc', 'Tosses covered in full', 'L_c', 'floor(ln(B_cap)/ln(2))', { kind: 'definition' }),
      a.fair_coin
        ? eq('cap', 'Expectation with a capped bank', 'E_cap', 'L_c + B_cap/2^L_c', { kind: 'derived', origin: 'L full terms plus the capped tail', needs: ['fair_coin'] })
        : eq('cap', 'Expectation with a capped bank', 'E_cap', '2*p_h*(1 - (2*(1 - p_h))^L_c)/(2*p_h - 1) + B_cap*(1 - p_h)^L_c', { kind: 'derived', origin: 'Finite geometric sum over L tosses plus the capped tail of probability (1 − p)ᴸ', note: 'Indeterminate at a probability of exactly one half, where the first term equals L.' }),
    ]),
    ...(a.linear_utility ? [] : [
      a.unlimited_bank
        ? eq('ulog', 'Expected logarithm of the prize', 'U_ln', a.fair_coin ? '2*ln(2)' : 'ln(2)/p_h', { kind: 'derived', origin: 'Mean of a geometric distribution times ln 2' })
        : eq('ulog', 'Expected logarithm of the capped prize', 'U_ln', a.fair_coin ? 'ln(2)*(2 - (L_c + 2)/2^L_c) + ln(B_cap)/2^L_c' : 'ln(2)*(1 - (L_c + 1)*(1 - p_h)^L_c + L_c*(1 - p_h)^(L_c + 1))/p_h + ln(B_cap)*(1 - p_h)^L_c', { kind: 'derived', origin: 'Truncated mean of a geometric distribution times ln 2, plus the capped tail' }),
      eq('ce', 'Certainty equivalent', 'C_e', 'exp(U_ln)', { kind: 'closure', origin: 'Bernoulli (1738): logarithmic utility' }),
    ]),
  ],
  derivation: a => [
    { text: 'The first head appears on toss k with probability 2⁻ᵏ and pays 2ᵏ. Each outcome therefore contributes one unit to the expected prize.', tex: 'E = \\sum_{k=1}^{\\infty} 2^{-k}\\cdot 2^{k} = 1 + 1 + 1 + \\cdots = \\infty' },
    { text: 'If the bank can pay at most B, prizes beyond L = ⌊log₂ B⌋ tosses are replaced by B. The expectation is then finite and grows only logarithmically with the bank.', tex: 'E_B = \\sum_{k=1}^{L} 1 + B\\sum_{k>L}2^{-k} = L + \\frac{B}{2^{L}}' },
    { text: 'With logarithmic utility of the prize the expected utility converges. Its exponential, the certainty equivalent, is four units.', tex: 'E[\\ln X] = \\sum_{k=1}^{\\infty}\\frac{k\\ln 2}{2^{k}} = 2\\ln 2,\\qquad C = e^{2\\ln 2} = 4' },
    { text: 'For a player with wealth w the fair fee c leaves expected log-wealth unchanged. It rises slowly with wealth.', tex: '\\sum_{k=1}^{\\infty}2^{-k}\\ln\\left(w - c + 2^{k}\\right) = \\ln w' },
    { text: 'The sample mean of n plays does not converge to a constant; it is typically of order log₂ n, so even very long experience suggests a modest value.', tex: '\\frac{S_n}{n\\log_2 n} \\xrightarrow{\\;P\\;} 1' },
    ...(a.fair_coin ? [] : [{ text: 'For a coin with probability p of heads the series is geometric with ratio 2(1 − p); it converges exactly when p exceeds one half.', tex: 'E = \\sum_{k\\ge1}p\\,(1-p)^{k-1}2^{k} = \\frac{2p}{2p-1}\\quad (p > \\tfrac12)' }]),
  ],
  solve(v, a) {
    const p = a.fair_coin ? 0.5 : v.p_h, B = v.B_cap, capOn = !a.unlimited_bank, KM = 1000;
    const pk = k => p * Math.pow(1 - p, k - 1), prize = k => (capOn ? Math.min(Math.pow(2, k), B) : Math.pow(2, k));
    const L = Math.floor(Math.log2(B) + 1e-12);
    let eCap = 0; for (let k = 1; k <= L; k++) eCap += pk(k) * Math.pow(2, k); eCap += B * Math.pow(1 - p, L);
    const eInf = 2 * (1 - p) < 1 ? 2 * p / (2 * p - 1) : Infinity, eVal = capOn ? eCap : eInf;
    // expected logarithm of the prize and wealth-based fair fee
    const qs = [], zs = []; let uLn = 0, pSum = 0;
    for (let k = 1; k <= KM; k++) { const q = pk(k); if (q < 1e-22) break; qs.push(q); zs.push(prize(k)); pSum += q; uLn += q * Math.log(prize(k)); }
    const cEq = Math.exp(uLn);
    const gain = c => { let s = 0; for (let k = 0; k < qs.length; k++) s += qs[k] * Math.log((v.w_0 - c + zs[k]) / v.w_0); return s; };
    let lo = 0, hi = v.w_0 + 2 - 1e-9 * (v.w_0 + 2);
    for (let i = 0; i < 70; i++) { const mid = 0.5 * (lo + hi); if (gain(mid) > 0) lo = mid; else hi = mid; }
    const cFair = 0.5 * (lo + hi), value = a.linear_utility ? eVal : cFair;
    // simulation of the running average prize
    const nP = int(v.n_plays, 100, 5000000), rnd = N.rng(int(v.seed, 1, 2147483647)), cp = marks(nP), xs = [], ys = []; let tot = 0, big = 0, ci = 0;
    for (let t = 1; t <= nP; t++) { let k = 1; while (rnd() >= p && k < KM) k++; const x = prize(k); tot += x; if (x > big) big = x; if (t === cp[ci]) { ci++; xs.push(t); ys.push(tot / t); } }
    const Ks = Array.from({ length: 40 }, (_, i) => i + 1); let run = 0;
    const partial = Ks.map(k => { run += pk(k) * prize(k); return run; });
    const warnings = [];
    if (!Number.isFinite(value)) warnings.push('The expected prize is infinite, so a player guided by expected monetary value should pay any finite fee. This is the paradox: the premise conflicts with every reasonable valuation of the game.');
    if (!a.fair_coin && p > 0.5) warnings.push('With heads more likely than tails the expectation converges and there is no paradox.');
    return {
      scalars: [
        scalar('E_val', 'Expected prize under the adopted assumptions', eVal, '1', { text: Number.isFinite(eVal) ? undefined : 'Diverges: infinite' }),
        scalar('E_cap', 'Expected prize with the bank capped at the stated amount', eCap, '1'),
        scalar('L_c', 'Tosses the capped bank can cover in full', L, '1'),
        scalar('U_ln', 'Expected natural logarithm of the prize', uLn, '1'),
        scalar('C_e', 'Certainty equivalent under logarithmic utility of the prize', cEq, '1'),
        scalar('c_fair', 'Largest fee a log-utility player with the stated wealth should pay', cFair, '1'),
        scalar('value', 'Value of the game under the adopted theory', value, '1', { text: Number.isFinite(value) ? undefined : 'Unbounded: any finite fee is acceptable' }),
        scalar('m_sim', 'Average prize in the simulated plays', tot / nP, '1'),
        scalar('x_max', 'Largest prize in the simulated plays', big, '1'),
        scalar('x_med', 'Median prize', Math.pow(2, Math.ceil(Math.log(0.5) / Math.log(1 - p) - 1e-12)), '1'),
      ],
      series: [
        line('running-mean', 'Average prize against number of plays', 'Plays', '–', xs, [{ label: 'Simulated running average', data: ys }, { label: 'log₂ n (typical growth, fair coin)', data: xs.map(t => Math.max(Math.log2(t), 1)), dash: true }, ...(Number.isFinite(eVal) ? [{ label: 'Expected prize', data: xs.map(() => eVal), dash: true }] : [])], 'Average prize', '–', { logx: true }),
        line('partial-expectation', 'Expectation counting only the first K outcomes', 'Outcomes counted K', '–', Ks, [{ label: 'Partial expectation', data: partial }], 'Expected prize', '–'),
      ],
      checks: [
        check('Outcome probabilities sum to one', pSum + Math.pow(1 - p, qs.length) - 1, 1e-12, 'Geometric distribution: summed terms plus the closed-form remainder'),
        check('Capped expectation against the closed form', a.fair_coin ? (eCap - (L + B / Math.pow(2, L))) / eCap : 0, 1e-12, 'L + B/2ᴸ for a fair coin'),
        check('Fair fee leaves expected log-wealth unchanged', gain(cFair), 1e-9, 'Root of the indifference condition'),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const out = [];
    const c = this.solve({ ...v, B_cap: Math.pow(2, 20) }, { unlimited_bank: false, linear_utility: true, fair_coin: true });
    out.push(bench('Expected prize with a bank of 2²⁰', val(c, 'E_val'), 21, 'L + B/2ᴸ with L = 20', 1e-12));
    const u = this.solve(v, { unlimited_bank: true, linear_utility: false, fair_coin: true });
    out.push(bench('Certainty equivalent under logarithmic utility of the prize', val(u, 'C_e'), 4, 'Bernoulli (1738): exp(2 ln 2)', 1e-12));
    const b = this.solve({ ...v, p_h: 0.75 }, { unlimited_bank: true, linear_utility: true, fair_coin: false });
    out.push(bench('Expected prize when heads has probability 3/4', val(b, 'E_val'), 3, '2p/(2p − 1)', 1e-12));
    let s = 0; for (let k = 1; k <= 200; k++) s += 0.75 * Math.pow(0.25, k - 1) * Math.pow(2, k);
    out.push(bench('Direct summation of that series', s, 3, 'Geometric series with ratio 1/2', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const xs = [70, 190, 310, 430];
    return svg(`
      ${xs.map((x, i) => `${S.circle(x, 150, 22)}${S.text(x, 155, 'toss', 'd-text d-small')}${S.arrow(x, 172, x, 232)}${S.text(x + 8, 205, 'H', 'd-text d-small', 'start')}${S.rect(x - 34, 234, 68, 34, 'd-hazard')}${S.text(x, 256, `win ${Math.pow(2, i + 1)}`, 'd-text d-small')}${S.text(x, 292, `prob. 1/${Math.pow(2, i + 1)}`, 'd-text d-small')}${S.arrow(x + 22, 150, x + 98, 150)}${S.text(x + 60, 142, 'T', 'd-text d-small')}`).join('')}
      ${S.text(565, 155, '…')}
      ${S.text(320, 50, 'Toss until the first head; the prize doubles with every toss')}
      ${S.text(320, 80, a.unlimited_bank ? 'Each outcome adds 1 to the expected prize' : `Bank limited to ${lab(v.B_cap, '', 3)}`, 'd-text d-small')}
      ${S.text(320, 335, 'Expected prize = 1 + 1 + 1 + …', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'InfiniteEV', text: 'The expected monetary value of the game is infinite' }, { k: 'MaxEV', text: 'A rational player pays any fee below the expected monetary value' }, { k: 'PayAny', text: 'A rational player would pay any finite fee to play' }],
    premises: ['InfiniteEV', '(InfiniteEV & MaxEV) -> PayAny', '~PayAny'],
    conclusion: '~MaxEV',
  },
  philosophy: [
    'The paradox was the first serious challenge to the rule that gambles should be valued by their expected monetary payoff. Bernoulli\'s answer introduced utility as distinct from money and with it the framework of expected-utility theory.',
    'Logarithmic utility does not end the matter. If prizes grow fast enough — for example 2 raised to the power 2ᵏ — expected log utility diverges again, which suggests that any unbounded utility function is open to a version of the paradox. Some conclude that utility must be bounded; others locate the problem in the idealisation of unlimited prizes, or in the use of an ensemble average for a single player who experiences outcomes in sequence.',
    'The case also raises the question of how to treat events of very small probability and very large payoff, which recurs in discussions of catastrophic risk.',
  ],
  experiment: {
    objective: 'Observe the behaviour of the average prize over many plays and elicit the fee people are willing to pay for one play.',
    apparatus: ['A coin, or a computer simulation with a recorded seed', 'A questionnaire or auction mechanism for eliciting willingness to pay'],
    instruments: [{ name: 'Play log', measures: 'Number of tosses and prize in each play', range: '10²–10⁶ plays', resolution: 'One play' }, { name: 'Incentive-compatible elicitation (for example a Becker–DeGroot–Marschak auction)', measures: 'Maximum acceptable fee', range: '0–100 units', resolution: 'One unit' }],
    procedure: ['Play the game repeatedly and record each prize.', 'Plot the running average against the number of plays on a logarithmic axis.', 'Separately, ask participants for the largest fee they would pay, with and without a stated cap on the prize.', 'Compare stated fees with the capped expectation and with the logarithmic-utility value.'],
    controls: ['A bounded game with the same first few prizes', 'Different random seeds, to display the dependence of the average on rare large prizes'],
    signatures: ['Running average that jumps at rare large prizes and drifts upward roughly as log₂ n', 'Typical willingness to pay of a few units to a few tens of units', 'Half of all plays ending with the smallest prize'],
    safety: [],
  },
  falsify: ['A simulated running average that settles to a constant as the number of plays grows without limit in the uncapped fair game.', 'The descriptive claim of expected-value maximisation is refuted by the routine observation that people decline large fees.'],
  alternatives: [
    { name: 'Diminishing marginal utility (Bernoulli)', text: 'Value is the expected logarithm of wealth, giving a small finite price. A faster-growing prize schedule revives the paradox unless utility is bounded.' },
    { name: 'Finite resources', text: 'No counterparty can pay unbounded prizes. With any realistic cap the expected value is a few tens of units.' },
    { name: 'Neglect of small probabilities', text: 'Outcomes below some probability threshold are ignored in practice (Buffon, d\'Alembert). The threshold is hard to justify in principle.' },
    { name: 'Time averages', text: 'A single player experiences plays in sequence; the long-run growth rate of wealth under repeated play, not the ensemble average, is taken as the relevant quantity, which leads again to a logarithmic criterion.' },
  ],
  limits: 'Independent tosses and a prize of 2ᵏ for a first head on toss k. Sums are truncated at 1000 tosses, far beyond floating-point significance. The simulated average depends strongly on the seed because it is dominated by rare large prizes; that sensitivity is itself the point of the plot.',
  numerics: { method: 'Direct summation of the series; bisection for the fair fee; seeded Monte-Carlo simulation', resolution: 'n_plays' },
  extensions: ['Super-St-Petersburg games with faster-growing prizes', 'Kelly betting and growth-optimal strategies', 'Bounded utility functions', 'Pascal\'s mugging and decisions about tiny probabilities of vast outcomes'],
};

// ================================================================== 14. Two envelopes
/** Truncated geometric prior on the smaller amount 2^k, k = 0..K, and everything that follows from it exactly. */
function envelopePrior(r, K) {
  const w = Array.from({ length: K + 1 }, (_, k) => Math.pow(r, k)), tot = N.sum(w);
  for (let k = 0; k <= K; k++) w[k] /= tot;
  const levels = [];
  for (let j = 0; j <= K + 1; j++) {
    const small = j <= K ? 0.5 * w[j] : 0, large = j >= 1 ? 0.5 * w[j - 1] : 0, P = small + large, x = Math.pow(2, j), pUp = small / P;
    levels.push({ j, x, P, pUp, gain: x * (pUp - 0.5 * (1 - pUp)) });
  }
  return { w, levels };
}
const twoEnvelopes = {
  id: 'two-envelopes',
  title: 'The two-envelope paradox',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['two envelopes', 'two envelope', 'two-envelope', 'exchange paradox', 'envelope paradox', 'necktie paradox', 'switch envelopes', 'twice as much', 'always switch'],
  summary: 'One envelope holds twice as much as the other. The argument that switching always gains 25 % fails because no proper prior makes "double" and "half" equally likely at every amount; exact conditional gains under a geometric prior, and a simulation.',
  background: [
    'You are handed one of two envelopes and told that one contains twice as much money as the other. Whatever amount x you hold, the other envelope seems to contain 2x or x/2 with equal probability, so its expected content is 1.25x and you should switch. But the same reasoning applies after switching, and by symmetry switching cannot be advantageous.',
    'The flaw lies in treating the two possibilities as equally likely conditional on every amount x. That would require a prior distribution over the smaller amount that gives equal weight to all scales, which is not a probability distribution. Under any proper prior the conditional probability that the other envelope is the larger depends on x, and the conditional gains from switching average to zero whenever the mean amount is finite. Priors with infinite mean can make switching conditionally favourable at every amount, a residual paradox closely related to the St Petersburg game.',
  ],
  phenomena: ['Conditional expectation', 'Improper prior distributions', 'Symmetry of exchange', 'Dependence of an optimal decision on the observed amount'],
  laws: ['kolmogorov', 'logic_nc'],
  refs: ['Kraitchik, M. (1942). Mathematical Recreations. W. W. Norton.', 'Nalebuff, B. (1989). Puzzles: the other person\'s envelope is always greener. Journal of Economic Perspectives 3(1), 171–181.', 'Christensen, R. & Utts, J. (1992). Bayesian resolution of the "exchange paradox". The American Statistician 46, 274–276.', 'Broome, J. (1995). The two-envelope paradox. Analysis 55, 6–11.', 'Chalmers, D. J. (2002). The St. Petersburg two-envelope paradox. Analysis 62, 155–157.'],
  inputs: [
    inp('r_g', 'Ratio of the geometric prior: each doubling of the smaller amount is this much less likely', '1', 0.4, { min: 0.05, max: 0.95, aliases: ['prior ratio', 'geometric ratio'] }),
    inp('x_thr', 'Threshold strategy: switch only when the observed amount is below this', '1', 8, { min: 1, max: 1e6, aliases: ['threshold', 'switch below'] }),
    inp('K_max', 'Largest exponent k of the smaller amount 2ᵏ', '1', 12, { min: 2, max: 40, kind: 'numerical', aliases: ['largest amount', 'maximum exponent'] }),
    inp('n_trials', 'Simulated games', '1', 20000, { min: 100, max: 1000000, kind: 'numerical', aliases: ['trials', 'games'] }),
    inp('seed', 'Random seed', '1', 6, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('proper_prior', 'The amounts are drawn from a proper probability distribution, so the chance that the other envelope is the larger depends on the amount observed.', { why: 'Required by the axioms of probability', alt: 'The naive argument: whatever amount is observed, the other envelope holds double or half with equal probability. No probability distribution has this property.', affects: ['g_c', 'G_all'] }),
    asm('looks', 'The player sees the amount in the chosen envelope before deciding.', { why: 'Allows the decision to depend on the amount', alt: 'The envelope stays closed. Nothing distinguishes the two, so every strategy has zero expected gain.', affects: ['G_thr'] }),
  ],
  symbols: { x_obs: ['Amount observed in the chosen envelope', '1'], P_up: ['Probability that the other envelope holds the larger amount', '1'], E_other: ['Expected content of the other envelope', '1'], g_c: ['Conditional expected gain from switching as a fraction of the amount observed', '1'], G_all: ['Expected gain from always switching', '1'] },
  equations: a => (a.proper_prior ? [
    eq('pup', 'Probability that the other envelope is the larger (interior amounts)', 'P_up', 'r_g/(1 + r_g)', { kind: 'derived', origin: 'Bayes\' theorem with the geometric prior', needs: ['proper_prior'] }),
    eq('other', 'Expected content of the other envelope', 'E_other', 'P_up*2*x_obs + (1 - P_up)*x_obs/2', { kind: 'law', origin: 'Conditional expectation' }),
    eq('gain', 'Conditional gain as a fraction of the observed amount', 'g_c', '(r_g - 1/2)/(1 + r_g)', { kind: 'derived', origin: 'E_other/x − 1' }),
    eq('sym', 'Expected gain from always switching', 'G_all', '0', { kind: 'law', origin: 'Symmetry of the two envelopes under a prior with finite mean' }),
  ] : [
    eq('pup', 'Probability that the other envelope is the larger (naive)', 'P_up', '1/2', { kind: 'hypothesis', origin: 'Principle of indifference applied to every amount; not satisfiable by any probability distribution' }),
    eq('other', 'Expected content of the other envelope (naive)', 'E_other', '(1/2)*2*x_obs + (1/2)*x_obs/2', { kind: 'hypothesis', origin: 'The switching argument' }),
    eq('gain', 'Conditional gain as a fraction of the observed amount (naive)', 'g_c', '1/4', { kind: 'hypothesis', origin: 'The switching argument' }),
  ]),
  derivation: a => [
    { text: 'Let the smaller amount be s, drawn from a prior with probabilities w(s), and let the player receive either envelope with probability one half. Observing x, either s = x and the other envelope holds 2x, or s = x/2 and it holds x/2.', tex: 'P(\\text{other} = 2x\\mid x) = \\frac{w(x)}{w(x) + w(x/2)}' },
    ...(a.proper_prior ? [
      { text: 'For the geometric prior on amounts 2ᵏ with w(2ᵏ) proportional to rᵏ, this probability is the same for all interior amounts but is not one half.', tex: 'P_{up} = \\frac{r}{1+r}' },
      { text: 'The conditional expected gain from switching is then a fixed fraction of the amount observed, negative when r < 1/2.', tex: '\\frac{E[\\text{other}\\mid x] - x}{x} = 2P_{up} + \\tfrac12(1-P_{up}) - 1 = \\frac{r-\\tfrac12}{1+r}' },
      { text: 'At the smallest possible amount switching is certain to gain, and at the largest it is certain to lose. Weighted by the probabilities of observing each amount, the gains cancel exactly.', tex: '\\sum_x P(x)\\,\\big(E[\\text{other}\\mid x]-x\\big) = 0' },
    ] : [
      { text: 'The switching argument takes this probability to be one half for every x, which gives a 25 % expected gain whatever is observed.', tex: 'E[\\text{other}\\mid x] = \\tfrac12(2x) + \\tfrac12\\left(\\tfrac{x}{2}\\right) = \\tfrac54 x' },
      { text: 'Equal probability at every x requires w(x) = w(x/2) for all x: a prior uniform over infinitely many scales, whose total probability cannot be one.', tex: 'w(x) = w(x/2)\\ \\ \\forall x \\;\\Rightarrow\\; \\sum_x w(x) \\in \\{0, \\infty\\}' },
    ]),
    { text: 'A player who sees the amount can do better than never switching by switching only when the amount is small: the smallest possible amount is certainly the smaller of the pair and the largest certainly the larger, so a threshold between them keeps the sure gain and avoids the sure loss.', tex: 'G_{thr} = \\sum_{x < x_{thr}} P(x)\\,\\big(E[\\text{other}\\mid x]-x\\big) > 0\\quad (x_{min} < x_{thr} \\le x_{max})' },
  ],
  solve(v, a) {
    const r = v.r_g, K = int(v.K_max, 2, 45), { w, levels } = envelopePrior(r, K);
    const nT = int(v.n_trials, 100, 5000000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const Ex = N.sum(levels.map(l => l.P * l.x)), Gtrue = N.sum(levels.map(l => l.P * l.gain));
    const naive = l => 0.25 * l.x, gOf = l => (a.proper_prior ? l.gain : naive(l));
    const Gclaim = a.proper_prior ? Gtrue : N.sum(levels.map(l => l.P * naive(l)));
    const Gthr = a.looks ? N.sum(levels.filter(l => l.x < v.x_thr).map(l => l.P * l.gain)) : 0;
    const Gbest = a.looks ? N.sum(levels.map(l => Math.max(0, l.P * l.gain))) : 0;
    const Es2 = N.sum(w.map((q, k) => q * Math.pow(4, k))), sig = Math.sqrt(Es2 / nT);
    // simulation
    const cdf = []; let c = 0; for (const q of w) { c += q; cdf.push(c); }
    const cp = marks(nT), xs = [], yAll = [], yThr = []; let gAll = 0, gThr = 0, ci = 0;
    for (let t = 1; t <= nT; t++) {
      const u = rnd(); let k = 0; while (k < K && u > cdf[k]) k++;
      const s = Math.pow(2, k), holdSmall = rnd() < 0.5, x = holdSmall ? s : 2 * s, d = holdSmall ? s : -s;
      gAll += d; if (a.looks && x < v.x_thr) gThr += d;
      if (t === cp[ci]) { ci++; xs.push(t); yAll.push(gAll / t); yThr.push(gThr / t); }
    }
    const interior = levels[1], pUp = a.proper_prior ? interior.pUp : 0.5, gc = a.proper_prior ? interior.gain / interior.x : 0.25;
    const warnings = [];
    if (!a.proper_prior) warnings.push(`The naive argument claims an expected gain of ${lab(Gclaim)} per game from always switching. The simulation, which must draw the amounts from some actual distribution, gives ${lab(gAll / nT)}: the claim cannot be realised.`);
    if (a.proper_prior && r > 0.5) warnings.push('With a prior ratio above one half, switching is favourable at every amount except the largest possible one; the rare loss at the top exactly offsets the frequent small gains. Without the upper limit the mean amount would be infinite and the paradox would return in a stronger form.');
    return {
      scalars: [
        scalar('P_up', 'Probability that the other envelope is the larger, for interior amounts', pUp, '1', PCT),
        scalar('g_c', 'Conditional expected gain from switching, as a fraction of the amount observed', gc, '1', PCT),
        scalar('E_x', 'Mean amount in the chosen envelope', Ex, '1'),
        scalar('G_all', 'Expected gain per game from always switching, as claimed by the adopted reasoning', Gclaim, '1', { status: a.proper_prior ? undefined : 'hypothetical' }),
        scalar('G_true', 'Exact expected gain per game from always switching', Gtrue, '1'),
        scalar('G_thr', 'Exact expected gain per game from the threshold strategy', Gthr, '1'),
        scalar('G_best', 'Expected gain per game from the best strategy that uses the observed amount', Gbest, '1'),
        scalar('G_sim', 'Simulated gain per game from always switching', gAll / nT, '1'),
        scalar('G_sim_thr', 'Simulated gain per game from the threshold strategy', gThr / nT, '1'),
        scalar('sigma_mc', 'Standard error of the simulated always-switch gain', sig, '1'),
      ],
      series: [
        line('conditional', 'Conditional expected gain from switching at each observed amount', 'log₂ of the amount observed', '–', levels.map(l => l.j), [{ label: 'Exact, from the prior', data: levels.map(l => l.gain / l.x), dash: !a.proper_prior }, { label: 'Naive argument', data: levels.map(() => 0.25), dash: a.proper_prior }, { label: 'Zero', data: levels.map(() => 0), dash: true }], 'Gain / amount observed', '–'),
        line('simulation', 'Simulated average gain per game', 'Games played', '–', xs, [{ label: 'Always switch', data: yAll }, { label: 'Threshold strategy', data: yThr }, { label: 'Exact value for the threshold strategy', data: xs.map(() => Gthr), dash: true }, { label: 'Zero', data: xs.map(() => 0), dash: true }], 'Gain per game', '–', { logx: true }),
        line('observed', 'Probability of observing each amount', 'log₂ of the amount observed', '–', levels.map(l => l.j), [{ label: 'Probability', data: levels.map(l => l.P) }], 'Probability', '–', { kind: 'bar' }),
      ],
      checks: [
        check('Probabilities of the observed amounts sum to one', N.sum(levels.map(l => l.P)) - 1, 1e-12, ''),
        check('Always switching has zero expected gain', Gtrue / Ex, 1e-12, 'Symmetry of exchange under a proper prior'),
        check('Simulated always-switch gain is consistent with zero', gAll / nT, 4 * sig, 'Within four standard errors'),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [], { levels } = envelopePrior(0.4, 12);
    out.push(bench('Conditional probability that the other envelope is larger, r = 0.4', levels[5].pUp, 0.4 / 1.4, 'r/(1 + r)', 1e-12));
    out.push(bench('Conditional gain fraction at interior amounts, r = 0.4', levels[5].gain / levels[5].x, -0.1 / 1.4, '(r − ½)/(1 + r)', 1e-12));
    out.push(bench('Total expected gain from always switching', N.sum(levels.map(l => l.P * l.gain)), 0, 'Symmetry', 1e-12));
    const r = this.solve(v, a);
    out.push(bench('Simulated always-switch gain', val(r, 'G_sim'), 0, 'Zero within four standard errors', 4 * val(r, 'sigma_mc')));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const env = (x, lbl, cls) => `${S.rect(x, 130, 170, 100, cls)}${S.path(`M${x} 130 L${x + 85} 190 L${x + 170} 130`, 'd-line')}${S.text(x + 85, 255, lbl)}`;
    return svg(`
      ${env(110, 'chosen: x', 'd-body')} ${env(360, 'other: 2x or x/2', 'd-hazard')}
      ${S.arrow(285, 180, 355, 180)} ${S.text(320, 170, 'switch?', 'd-text d-small')}
      ${S.text(320, 60, 'One envelope holds twice as much as the other')}
      ${S.text(320, 90, a.proper_prior ? `P(other is larger | x) = r/(1 + r) = ${lab(v.r_g / (1 + v.r_g))}` : 'Naive: P(other is larger | x) = 1/2 for every x', 'd-text d-small')}
      ${S.text(320, 305, a.proper_prior ? 'Conditional gains average to zero over all amounts' : 'Claimed gain of 25 % at every amount: impossible', 'd-text d-small')}
      ${S.text(320, 335, 'The smallest possible amount is certainly the smaller of the pair', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Half', text: 'At every observed amount the other envelope is equally likely to hold double or half' }, { k: 'Gain', text: 'Switching has positive expected gain at every observed amount' }, { k: 'Proper', text: 'The amounts follow a proper prior with finite mean' }, { k: 'Symmetric', text: 'The two envelopes are assigned symmetrically' }],
    premises: ['Half -> Gain', '(Proper & Symmetric) -> ~Gain', 'Proper', 'Symmetric'],
    conclusion: '~Half',
  },
  philosophy: [
    'The paradox is instructive about what an expectation is. The symbol x in the switching argument is used both as a fixed number and as a random quantity whose distribution differs between the two cases being averaged; once the conditioning is made explicit the calculation no longer goes through.',
    'It also exposes the cost of the principle of indifference. Assigning equal probabilities because one has no reason to prefer either case is harmless in finite symmetric problems, but here it tacitly commits the reasoner to an improper prior over all magnitudes.',
    'Versions with infinite expected amounts are not dissolved by this diagnosis. There, switching is favourable conditional on every observation and yet the symmetry remains, showing that dominance-style reasoning with conditional expectations can fail when unconditional expectations do not exist.',
  ],
  experiment: {
    objective: 'Test by repeated play whether always switching yields a gain, and whether a threshold strategy that uses the observed amount does.',
    apparatus: ['Pairs of sealed envelopes prepared from a stated distribution of amounts, one holding twice the other', 'Alternatively a computer simulation with a recorded seed'],
    instruments: [{ name: 'Play log', measures: 'Amount observed, decision, and final amount', range: '≥ 1000 games', resolution: 'One game' }, { name: 'Record of the generating distribution', measures: 'Probabilities of each pair of amounts', range: '—', resolution: '—' }],
    procedure: ['Generate the smaller amount from the chosen distribution and fill the two envelopes.', 'Present one envelope at random; record the amount.', 'Apply each strategy — never switch, always switch, switch below a threshold — to the same sequence of games.', 'Compare average winnings with their standard errors.'],
    controls: ['Never switching as the baseline', 'Repeating with a different generating distribution to show that the best threshold depends on it'],
    signatures: ['No significant difference between always switching and never switching', 'A positive gain for a well-chosen threshold strategy', 'Observed fraction of games in which the other envelope is larger varying with the amount, not fixed at one half'],
    safety: [],
  },
  falsify: ['A long run of games from a proper distribution with finite mean in which always switching gains significantly on average.', 'A distribution of amounts for which the other envelope is the larger with probability exactly one half at every observable amount.'],
  alternatives: [
    { name: 'Bayesian resolution', text: 'The posterior probability that the other envelope is larger depends on the prior and the amount seen; the fixed value of one half is unjustified. This is the account implemented here.' },
    { name: 'Equivocation on x', text: 'In the closed-envelope version the fault is logical: the same symbol denotes the smaller amount in one branch of the calculation and the larger in the other.' },
    { name: 'Infinite-expectation versions', text: 'For priors with infinite mean, such as the geometric prior with ratio above one half and no upper limit, switching is conditionally favourable at every amount. The remaining puzzle is attributed to the non-existence of the unconditional expectation.' },
    { name: 'Randomised switching', text: 'Even with no knowledge of the prior, switching with a probability that decreases with the amount observed gives a strictly positive expected gain.' },
  ],
  limits: 'Amounts are powers of two with a geometric prior truncated at a largest value, so every expectation is finite. The exact results depend on that prior; the qualitative conclusion — that the conditional probability is not one half at every amount — holds for every proper prior. For prior ratios above one quarter the variance of the gain is dominated by rare large amounts and the simulation converges slowly.',
  numerics: { method: 'Exact enumeration over the support of the prior; seeded Monte-Carlo simulation', order: 0.5, resolution: 'n_trials' },
  extensions: ['Continuous priors and the optimal switching rule', 'Cover\'s randomised threshold strategy with an unknown prior', 'The necktie and wallet versions of the puzzle', 'Infinite-mean priors and their relation to the St Petersburg game'],
};

// ================================================================== 15. Simpson's paradox
const simpsonsParadox = {
  id: 'simpsons-paradox',
  title: 'Simpson\'s paradox',
  module: 1, klass: ['II', 'I'], domains: ['logic'],
  keywords: ['simpson\'s paradox', 'simpsons paradox', 'simpson paradox', 'reversal', 'confounding', 'aggregated data', 'stratified', 'lurking variable', 'yule-simpson', 'kidney stone', 'subgroups'],
  summary: 'A treatment can have the higher success rate in every subgroup and the lower rate overall. Stratified and aggregated rates from a two-by-two-by-two table, with the adjusted comparison.',
  background: [
    'An association between two variables can reverse when the data are divided by a third. In a well-known study of kidney-stone treatments, one treatment had the higher success rate for small stones and for large stones separately, yet the lower rate when all patients were pooled. No arithmetic error is involved: the pooled rates are weighted averages of the subgroup rates with different weights for the two treatments, because the more difficult cases were assigned mostly to one of them.',
    'Which comparison answers the practical question depends on the causal structure, not on the numbers. If the stratifying variable influences both the choice of treatment and the outcome, it is a confounder and the stratified comparison is the relevant one. If it lies on the causal path from treatment to outcome, pooling may be appropriate. The data alone cannot distinguish the two cases.',
  ],
  phenomena: ['Weighted averages with unequal weights', 'Confounding', 'Association against causation', 'Standardisation'],
  laws: ['kolmogorov'],
  refs: ['Simpson, E. H. (1951). The interpretation of interaction in contingency tables. Journal of the Royal Statistical Society B 13, 238–241.', 'Blyth, C. R. (1972). On Simpson\'s paradox and the sure-thing principle. Journal of the American Statistical Association 67, 364–366.', 'Bickel, P. J., Hammel, E. A. & O\'Connell, J. W. (1975). Sex bias in graduate admissions: data from Berkeley. Science 187, 398–404.', 'Charig, C. R., Webb, D. R., Payne, S. R. & Wickham, J. E. A. (1986). Comparison of treatment of renal calculi by open surgery, percutaneous nephrolithotomy, and extracorporeal shockwave lithotripsy. British Medical Journal 292, 879–882.', 'Julious, S. A. & Mullee, M. A. (1994). Confounding and Simpson\'s paradox. British Medical Journal 309, 1480–1481.', 'Pearl, J. (2014). Comment: understanding Simpson\'s paradox. The American Statistician 68, 8–13.'],
  inputs: [
    inp('s_A1', 'Group 1, treatment A: successes', '1', 81, { integer: true, min: 0, max: 100000, aliases: ['a successes group 1'], src: 'Charig et al. (1986), stones under 2 cm, open surgery' }),
    inp('n_A1', 'Group 1, treatment A: patients', '1', 87, { integer: true, min: 1, max: 100000, aliases: ['a patients group 1'], src: 'Charig et al. (1986)' }),
    inp('s_B1', 'Group 1, treatment B: successes', '1', 234, { integer: true, min: 0, max: 100000, aliases: ['b successes group 1'], src: 'Charig et al. (1986), stones under 2 cm, percutaneous nephrolithotomy' }),
    inp('n_B1', 'Group 1, treatment B: patients', '1', 270, { integer: true, min: 1, max: 100000, aliases: ['b patients group 1'], src: 'Charig et al. (1986)' }),
    inp('s_A2', 'Group 2, treatment A: successes', '1', 192, { integer: true, min: 0, max: 100000, aliases: ['a successes group 2'], src: 'Charig et al. (1986), stones of 2 cm or more, open surgery' }),
    inp('n_A2', 'Group 2, treatment A: patients', '1', 263, { integer: true, min: 1, max: 100000, aliases: ['a patients group 2'], src: 'Charig et al. (1986)' }),
    inp('s_B2', 'Group 2, treatment B: successes', '1', 55, { integer: true, min: 0, max: 100000, aliases: ['b successes group 2'], src: 'Charig et al. (1986), stones of 2 cm or more, percutaneous nephrolithotomy' }),
    inp('n_B2', 'Group 2, treatment B: patients', '1', 80, { integer: true, min: 1, max: 100000, aliases: ['b patients group 2'], src: 'Charig et al. (1986)' }),
  ],
  assumptions: [
    asm('observed_alloc', 'Patients were allocated to treatments as observed, in different proportions in the two groups.', { why: 'Observational data', alt: 'Allocation is balanced, as in a randomised trial: both treatments receive the same mix of groups. The pooled rates are then weighted alike and no reversal can occur.', affects: ['p_A', 'p_B'] }),
    asm('confounder', 'The grouping variable is a confounder: it affects both the choice of treatment and the outcome.', { why: 'Stone size was known before treatment and influenced the choice', alt: 'The grouping variable is a consequence of treatment (a mediator); the pooled comparison is then the causal one.', affects: ['d_c'] }),
  ],
  symbols: { p_A1: ['Success rate of A in group 1', '1'], p_A2: ['Success rate of A in group 2', '1'], p_B1: ['Success rate of B in group 1', '1'], p_B2: ['Success rate of B in group 2', '1'], p_A: ['Pooled success rate of A', '1'], p_B: ['Pooled success rate of B', '1'], w_A: ['Share of A patients who are in group 1', '1'], w_B: ['Share of B patients who are in group 1', '1'], w_1: ['Share of all patients who are in group 1', '1'], d_adj: ['Difference in success rate, A minus B, standardised to the whole population', '1'], d_agg: ['Difference in pooled success rate, A minus B', '1'] },
  equations: a => [
    eq('ra1', 'Success rate of A in group 1', 'p_A1', 'min(s_A1, n_A1)/n_A1', { kind: 'definition', note: 'Successes cannot exceed patients; a larger entry is limited to the number of patients.' }),
    eq('ra2', 'Success rate of A in group 2', 'p_A2', 'min(s_A2, n_A2)/n_A2', { kind: 'definition', note: 'Successes cannot exceed patients; a larger entry is limited to the number of patients.' }),
    eq('rb1', 'Success rate of B in group 1', 'p_B1', 'min(s_B1, n_B1)/n_B1', { kind: 'definition', note: 'Successes cannot exceed patients; a larger entry is limited to the number of patients.' }),
    eq('rb2', 'Success rate of B in group 2', 'p_B2', 'min(s_B2, n_B2)/n_B2', { kind: 'definition', note: 'Successes cannot exceed patients; a larger entry is limited to the number of patients.' }),
    eq('w1', 'Share of all patients in group 1', 'w_1', '(n_A1 + n_B1)/(n_A1 + n_A2 + n_B1 + n_B2)', { kind: 'definition' }),
    ...(a.observed_alloc ? [
      eq('wa', 'Share of A patients in group 1', 'w_A', 'n_A1/(n_A1 + n_A2)', { kind: 'definition' }),
      eq('wb', 'Share of B patients in group 1', 'w_B', 'n_B1/(n_B1 + n_B2)', { kind: 'definition' }),
      eq('pa', 'Pooled success rate of A', 'p_A', 'w_A*p_A1 + (1 - w_A)*p_A2', { kind: 'law', origin: 'Law of total probability with treatment-specific weights', needs: ['observed_alloc'] }),
      eq('pb', 'Pooled success rate of B', 'p_B', 'w_B*p_B1 + (1 - w_B)*p_B2', { kind: 'law', origin: 'Law of total probability with treatment-specific weights', needs: ['observed_alloc'] }),
    ] : [
      eq('pa', 'Pooled success rate of A under balanced allocation', 'p_A', 'w_1*p_A1 + (1 - w_1)*p_A2', { kind: 'law', origin: 'Law of total probability with common weights' }),
      eq('pb', 'Pooled success rate of B under balanced allocation', 'p_B', 'w_1*p_B1 + (1 - w_1)*p_B2', { kind: 'law', origin: 'Law of total probability with common weights' }),
    ]),
    eq('agg', 'Pooled difference', 'd_agg', 'p_A - p_B', { kind: 'definition' }),
    eq('adj', 'Standardised difference', 'd_adj', 'w_1*(p_A1 - p_B1) + (1 - w_1)*(p_A2 - p_B2)', { kind: 'derived', origin: 'Direct standardisation to the combined population (adjustment formula)' }),
  ],
  derivation: a => [
    { text: 'Within each group the success rate of a treatment is successes divided by patients.', tex: 'p_{Ag} = \\frac{s_{Ag}}{n_{Ag}},\\qquad p_{Bg} = \\frac{s_{Bg}}{n_{Bg}}' },
    { text: 'The pooled rate of each treatment is a weighted average of its group rates, weighted by the share of that treatment\'s patients in each group.', tex: 'p_A = w_A\\,p_{A1} + (1-w_A)\\,p_{A2},\\qquad p_B = w_B\\,p_{B1} + (1-w_B)\\,p_{B2}' },
    a.observed_alloc
      ? { text: 'If the weights differ, A can be better in both groups and still worse overall: it suffices that A is given mostly to the group with the lower success rates.', tex: 'p_{A1} > p_{B1},\\ p_{A2} > p_{B2}\\ \\ \\text{and}\\ \\ p_A < p_B\\quad\\text{requires}\\quad w_A \\ne w_B' }
      : { text: 'With a common weight for both treatments the pooled difference is a weighted average of the group differences and must have their sign when they agree.', tex: 'p_A - p_B = w_1\\,(p_{A1}-p_{B1}) + (1-w_1)\\,(p_{A2}-p_{B2})' },
    { text: 'Standardising both treatments to the group mix of the whole population removes the effect of unequal allocation. If the grouping variable is a confounder this is the causal comparison.', tex: 'd_{adj} = \\sum_g P(g)\\,\\big(p_{Ag} - p_{Bg}\\big)' },
  ],
  solve(v, a) {
    const cnt = (s, n) => { const nn = Math.max(1, Math.round(n)); return [Math.min(nn, Math.max(0, Math.round(s))), nn]; };
    const [sA1, nA1] = cnt(v.s_A1, v.n_A1), [sB1, nB1] = cnt(v.s_B1, v.n_B1), [sA2, nA2] = cnt(v.s_A2, v.n_A2), [sB2, nB2] = cnt(v.s_B2, v.n_B2);
    const warnings = [];
    if (Math.round(v.s_A1) > nA1 || Math.round(v.s_B1) > nB1 || Math.round(v.s_A2) > nA2 || Math.round(v.s_B2) > nB2) warnings.push('A number of successes exceeded the number of patients and has been limited to it.');
    const pA1 = sA1 / nA1, pA2 = sA2 / nA2, pB1 = sB1 / nB1, pB2 = sB2 / nB2, Ntot = nA1 + nA2 + nB1 + nB2;
    const w1 = (nA1 + nB1) / Ntot, wA = a.observed_alloc ? nA1 / (nA1 + nA2) : w1, wB = a.observed_alloc ? nB1 / (nB1 + nB2) : w1;
    const pA = wA * pA1 + (1 - wA) * pA2, pB = wB * pB1 + (1 - wB) * pB2;
    const d1 = pA1 - pB1, d2 = pA2 - pB2, dAgg = pA - pB, dAdj = w1 * d1 + (1 - w1) * d2, dC = a.confounder ? dAdj : dAgg;
    const reversal = d1 * d2 > 0 && dAgg * d1 < 0;
    const orOf = (s1, n1, s2, n2) => (s1 * (n2 - s2)) / ((n1 - s1) * s2);
    const orCrude = orOf(sA1 + sA2, nA1 + nA2, sB1 + sB2, nB1 + nB2);
    const mhNum = sA1 * (nB1 - sB1) / (nA1 + nB1) + sA2 * (nB2 - sB2) / (nA2 + nB2), mhDen = (nA1 - sA1) * sB1 / (nA1 + nB1) + (nA2 - sA2) * sB2 / (nA2 + nB2), orMH = mhNum / mhDen;
    const better = d => (d > 0 ? 'A' : d < 0 ? 'B' : 'neither');
    if (reversal) warnings.push(`Treatment ${better(d1)} has the higher success rate in both groups, yet treatment ${better(dAgg)} has the higher pooled rate. The reversal arises because ${lab(100 * wA)} % of A patients but ${lab(100 * wB)} % of B patients are in group 1, and the groups differ in their chance of success.`);
    const ws = N.linspace(0, 1, 51);
    return {
      scalars: [
        scalar('p_A1', 'Success rate of A in group 1', pA1, '1', PCT), scalar('p_B1', 'Success rate of B in group 1', pB1, '1', PCT),
        scalar('p_A2', 'Success rate of A in group 2', pA2, '1', PCT), scalar('p_B2', 'Success rate of B in group 2', pB2, '1', PCT),
        scalar('p_A', 'Pooled success rate of A', pA, '1', PCT), scalar('p_B', 'Pooled success rate of B', pB, '1', PCT),
        scalar('w_A', 'Share of A patients who are in group 1', wA, '1', PCT), scalar('w_B', 'Share of B patients who are in group 1', wB, '1', PCT),
        scalar('w_1', 'Share of all patients who are in group 1', w1, '1', PCT),
        scalar('d_1', 'Difference A − B in group 1', d1, '1', PCT), scalar('d_2', 'Difference A − B in group 2', d2, '1', PCT),
        scalar('d_agg', 'Difference A − B in the pooled data', dAgg, '1', PCT),
        scalar('d_adj', 'Difference A − B standardised to the whole population', dAdj, '1', PCT),
        scalar('d_c', 'Difference A − B under the adopted causal reading', dC, '1', { ...PCT, text: `${lab(100 * dC)} %: favours ${better(dC)}` }),
        scalar('rev', 'Reversal between stratified and pooled comparisons', reversal ? 1 : 0, '1', { text: reversal ? 'Yes' : 'No' }),
        scalar('OR_c', 'Crude odds ratio, A against B', orCrude, '1', { text: Number.isFinite(orCrude) ? undefined : 'Undefined: an empty cell' }),
        scalar('OR_MH', 'Mantel–Haenszel odds ratio adjusted for group', orMH, '1', { text: Number.isFinite(orMH) ? undefined : 'Undefined: an empty cell' }),
      ],
      series: [
        line('rates', 'Success rates by group and pooled', 'Comparison', '–', [1, 2, 3], [{ label: 'Treatment A', data: [pA1, pA2, pA] }, { label: 'Treatment B', data: [pB1, pB2, pB] }], 'Success rate', '–', { kind: 'bar', categories: ['Group 1', 'Group 2', 'Pooled'] }),
        line('mixing', 'Pooled success rate as a function of the share of patients in group 1', 'Share of the treatment\'s patients in group 1', '–', ws, [{ label: 'Treatment A', data: ws.map(q => q * pA1 + (1 - q) * pA2) }, { label: 'Treatment B', data: ws.map(q => q * pB1 + (1 - q) * pB2) }], 'Pooled success rate', '–', { note: `Treatment A is evaluated at a share of ${lab(wA)} and treatment B at ${lab(wB)}. Comparing the lines at different horizontal positions is what permits a reversal.` }),
      ],
      checks: [
        check('Pooled rate of A equals total successes over total patients', a.observed_alloc ? pA - (sA1 + sA2) / (nA1 + nA2) : 0, 1e-12, 'Weighted-average identity'),
        check('Pooled rate of B equals total successes over total patients', a.observed_alloc ? pB - (sB1 + sB2) / (nB1 + nB2) : 0, 1e-12, 'Weighted-average identity'),
        check('No reversal is possible under balanced allocation', !a.observed_alloc && reversal ? 1 : 0, 0, 'Common weights preserve the sign of concordant group differences'),
        check('Rates lie in [0, 1]', [pA1, pA2, pB1, pB2, pA, pB].some(q => q < 0 || q > 1) ? 1 : 0, 0, ''),
      ],
      warnings,
    };
  },
  benchmarks(v) {
    const d = { s_A1: 81, n_A1: 87, s_B1: 234, n_B1: 270, s_A2: 192, n_A2: 263, s_B2: 55, n_B2: 80 }, on = { observed_alloc: true, confounder: true }, out = [];
    const r = this.solve({ ...v, ...d }, on);
    out.push(bench('Kidney-stone data: pooled success of treatment A', val(r, 'p_A'), 273 / 350, 'Charig et al. (1986): 78 %', 1e-12));
    out.push(bench('Kidney-stone data: pooled success of treatment B', val(r, 'p_B'), 289 / 350, 'Charig et al. (1986): 83 %', 1e-12));
    out.push(bench('Kidney-stone data: reversal present', val(r, 'rev'), 1, 'A better for small and for large stones, B better pooled', 1e-12));
    const b = this.solve({ ...v, ...d }, { ...on, observed_alloc: false });
    out.push(bench('Balanced allocation: pooled difference equals standardised difference', val(b, 'd_agg'), val(b, 'd_adj'), 'Common weights', 1e-12));
    out.push(bench('Kidney-stone data: crude odds ratio', val(r, 'OR_c'), (273 * 61) / (77 * 289), 'Pooled table: 273/77 against 289/61, below one', 1e-12));
    out.push(bench('Kidney-stone data: Mantel–Haenszel odds ratio', val(r, 'OR_MH'), (2916 / 357 + 4800 / 343) / (1404 / 357 + 3905 / 343), 'Stratum sums 81·36/357 + 192·25/343 over 6·234/357 + 71·55/343, above one', 1e-12));
    out.push(bench('Kidney-stone data: standardised difference', val(r, 'd_adj'), 0.51 * (81 / 87 - 234 / 270) + 0.49 * (192 / 263 - 55 / 80), 'Group 1 holds 357 of the 700 patients', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const node = (x, y, t) => `${S.rect(x - 75, y - 22, 150, 44)}${S.text(x, y + 5, t)}`;
    return svg(`
      ${node(320, 70, 'group (e.g. severity)')} ${node(140, 230, 'treatment')} ${node(500, 230, 'outcome')}
      ${a.confounder ? S.arrow(270, 92, 170, 206) : S.arrow(170, 206, 270, 92)} ${S.arrow(370, 92, 470, 206)} ${S.arrow(216, 230, 424, 230)}
      ${S.text(175, 145, a.confounder ? 'influences choice' : 'is changed by', 'd-text d-small')} ${S.text(470, 145, 'influences', 'd-text d-small')} ${S.text(320, 222, 'effect of interest', 'd-text d-small')}
      ${S.text(320, 300, a.confounder ? 'Confounder: compare within groups, then standardise' : 'Mediator: the pooled comparison carries the total effect')}
      ${S.text(320, 330, a.observed_alloc ? 'Allocation differs between groups, as observed' : 'Balanced allocation: no path from group to treatment', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Better1', text: 'Treatment A has the higher success rate in group 1' }, { k: 'Better2', text: 'Treatment A has the higher success rate in group 2' }, { k: 'BetterAll', text: 'Treatment A has the higher success rate in the pooled data' }],
    premises: ['Better1', 'Better2', '~BetterAll'],
    conclusion: '~((Better1 & Better2) -> BetterAll)',
  },
  philosophy: [
    'Simpson\'s paradox refutes an inference that seems close to a logical truth: what holds in each part must hold in the whole. For proportions it does not, because the whole is a weighted average and the weights are part of the data.',
    'The more important lesson is that statistical association does not by itself tell us how to act. The same table can call for the stratified answer or the pooled answer depending on whether the third variable is a cause or an effect of the treatment — information that is causal and comes from outside the table. This has been a central example in the development of formal theories of causal inference.',
    'The apparent conflict with the sure-thing principle of decision theory is resolved in the same way. The principle is valid when the conditioning event is not influenced by the act; it fails, as here, when the act changes the probabilities of the conditions.',
  ],
  experiment: {
    objective: 'Demonstrate the reversal in observational data and its disappearance under randomised allocation.',
    apparatus: ['An observational data set with a treatment, an outcome and a prognostic grouping variable', 'A randomised trial, or a simulated one, of the same treatments', 'Statistical software for stratified analysis'],
    instruments: [{ name: 'Two-by-two-by-two contingency table', measures: 'Counts of success and failure by treatment and group', range: '≥ 100 per cell where possible', resolution: 'One patient' }, { name: 'Mantel–Haenszel or standardisation routine', measures: 'Adjusted effect estimate with confidence interval', range: '—', resolution: '—' }],
    procedure: ['Tabulate outcomes by treatment within each group and pooled.', 'Compute success rates and their differences, with confidence intervals.', 'Compute the standardised difference and the Mantel–Haenszel odds ratio.', 'Repeat on data in which treatment was allocated at random and compare.'],
    controls: ['Randomised allocation, which equalises the group mix between treatments', 'Negative control: a grouping variable unrelated to outcome, which should produce no reversal'],
    signatures: ['Concordant differences within groups with an opposite pooled difference only when allocation is unbalanced', 'Pooled and standardised differences agreeing under randomisation', 'Crude and adjusted odds ratios on opposite sides of one in the observational data'],
    safety: ['Use of patient data requires ethical approval and anonymisation'],
  },
  falsify: ['A data set with identical group mix for both treatments in which the group-specific differences agree in sign and the pooled difference has the opposite sign; the weighted-average identity shows this to be impossible.', 'For the causal reading: a randomised trial whose result agrees with the pooled observational comparison and contradicts the stratified one would indicate that the grouping variable was not acting as a confounder.'],
  alternatives: [
    { name: 'Stratify: the grouping variable is a confounder', text: 'When the variable precedes and influences treatment choice, compare within strata and standardise. For the kidney-stone data this favours open surgery.' },
    { name: 'Pool: the grouping variable is a mediator', text: 'When the variable is affected by the treatment, conditioning on it removes part of the effect; the pooled comparison estimates the total effect.' },
    { name: 'Collider or selection effects', text: 'When the grouping variable is a common effect of treatment and outcome, stratifying creates a spurious association and neither simple analysis is correct.' },
    { name: 'Purely descriptive reading', text: 'Without causal assumptions both sets of rates are correct descriptions of different populations, and neither licenses a recommendation.' },
  ],
  limits: 'Two treatments, two groups and a binary outcome. Sampling uncertainty is not shown: with small cells an apparent reversal may not be statistically significant. The adjusted estimate assumes that the single grouping variable captures all confounding.',
  numerics: { method: 'Exact arithmetic on the contingency table' },
  extensions: ['Confidence intervals and tests of homogeneity', 'More than two strata and continuous confounders', 'Causal diagrams and the back-door criterion', 'The Berkeley admissions data'],
};

// ================================================================== 16. Hilbert's hotel
/** Cantor pairing of bus b ≥ 1 and seat s ≥ 1 onto the positive integers, and its inverse. */
const cantorPair = (b, s) => (b + s - 2) * (b + s - 1) / 2 + s;
const cantorUnpair = z => { const w = Math.floor((Math.sqrt(8 * z - 7) - 1) / 2), s = z - w * (w + 1) / 2; return [w + 2 - s, s]; };
const hilbertHotel = {
  id: 'hilbert-hotel',
  title: 'Hilbert\'s hotel',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['hilbert\'s hotel', 'hilbert hotel', 'hilberts hotel', 'infinite hotel', 'grand hotel', 'countable infinity', 'bijection', 'infinitely many rooms', 'cardinality', 'aleph', 'infinite set'],
  summary: 'A full hotel with countably many rooms can still take one more guest, countably many more, or countably many coach-loads. Explicit room maps verified to be one-to-one on a finite window.',
  background: [
    'Hilbert illustrated the arithmetic of the infinite with a hotel whose rooms are numbered 1, 2, 3, … and all occupied. A new guest is accommodated by moving each occupant from room n to room n + 1, which frees room 1. Infinitely many new guests are accommodated by moving each occupant to room 2n, which frees every odd room. Even infinitely many coaches each carrying infinitely many passengers can be housed, using a pairing of coach and seat numbers with the natural numbers.',
    'Each manoeuvre is a one-to-one correspondence between the set of rooms and a proper part of itself. For finite collections no such correspondence exists; Dedekind took its existence as the definition of an infinite set. The hotel cannot, however, accommodate every infinite collection: Cantor\'s diagonal argument shows that the set of all infinite sequences of two symbols is too large to be listed room by room.',
  ],
  phenomena: ['One-to-one correspondence', 'A set equinumerous with a proper subset of itself', 'Countability of pairs of natural numbers', 'Uncountability by diagonalisation'],
  laws: ['logic_nc'],
  refs: ['Galilei, G. (1638). Discorsi e dimostrazioni matematiche intorno a due nuove scienze, First Day. Elsevier, Leiden.', 'Cantor, G. (1891). Über eine elementare Frage der Mannigfaltigkeitslehre. Jahresbericht der Deutschen Mathematiker-Vereinigung 1, 75–78.', 'Dedekind, R. (1888). Was sind und was sollen die Zahlen? Vieweg.', 'Gamow, G. (1947). One Two Three … Infinity. Viking Press.', 'Ewald, W. & Sieg, W. (eds) (2013). David Hilbert\'s Lectures on the Foundations of Arithmetic and Logic 1917–1933. Springer.'],
  inputs: [
    inp('m_new', 'Number of new guests arriving', '1', 1, { min: 1, max: 1000, aliases: ['new guests', 'arrivals'] }),
    inp('n_room', 'Room of a guest to follow', '1', 7, { min: 1, max: 1000000, aliases: ['room', 'room number', 'guest in room'] }),
    inp('b_bus', 'Coach number of a passenger to follow', '1', 3, { min: 1, max: 1000, aliases: ['bus', 'coach'] }),
    inp('s_seat', 'Seat number of that passenger', '1', 5, { min: 1, max: 1000, aliases: ['seat'] }),
    inp('N_w', 'Rooms in the window used for verification (and in the finite hotel)', '1', 1000, { min: 10, max: 20000, kind: 'numerical', aliases: ['window', 'rooms checked'] }),
    inp('seed', 'Random seed', '1', 8, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('infinite', 'The hotel has one room for every natural number.', { why: 'The premise of the thought experiment', alt: 'The hotel is finite, with as many rooms as the verification window. Shifting the guests pushes some out of the last rooms: a full finite hotel cannot take anyone.', affects: ['n_out'] }),
    asm('countable', 'The arriving guests can be listed one after another.', { why: 'Finite groups, a countable queue, or countably many coaches', alt: 'The arrivals are all infinite sequences of two symbols. Cantor\'s diagonal construction produces a guest who is missing from any proposed room list.', affects: ['n_diag'] }),
  ],
  symbols: { f_s: ['New room under the shift map', '1'], f_d: ['New room under the doubling map', '1'], f_p: ['Room assigned by the pairing map', '1'], n_out: ['Guests left without a room', '1'], d_k: ['k-th digit of the diagonal sequence', '1'], s_kk: ['k-th digit of the k-th listed sequence', '1'] },
  equations: a => [
    eq('shift', 'Shift map for finitely many arrivals', 'f_s', 'n_room + m_new', { kind: 'definition', origin: 'One-to-one map of the naturals onto the naturals above m' }),
    eq('double', 'Doubling map for countably many arrivals', 'f_d', '2*n_room', { kind: 'definition', origin: 'One-to-one map of the naturals onto the even numbers' }),
    eq('pair', 'Pairing map for seat s of coach b', 'f_p', '(b_bus + s_seat - 2)*(b_bus + s_seat - 1)/2 + s_seat', { kind: 'definition', origin: 'Cantor\'s enumeration of pairs along diagonals' }),
    eq('out', 'Guests displaced by the shift', 'n_out', a.infinite ? '0' : 'min(m_new, N_w)', { kind: 'derived', origin: a.infinite ? 'There is no last room' : 'Pigeonhole principle for a finite hotel' }),
    ...(a.countable ? [] : [eq('diag', 'Diagonal sequence', 'd_k', '1 - s_kk', { kind: 'definition', origin: 'Cantor (1891): differ from the k-th listed sequence in the k-th place' })]),
  ],
  derivation: a => [
    { text: 'To admit m new guests, move the occupant of room n to room n + m. Different rooms are sent to different rooms, and rooms 1 to m are left empty.', tex: 'f(n) = n + m,\\qquad f(n) = f(n\') \\Rightarrow n = n\'' },
    { text: 'To admit a countable infinity of new guests, move the occupant of room n to room 2n. All odd-numbered rooms become free, and there are as many of them as there are natural numbers.', tex: 'f(n) = 2n,\\qquad \\text{free rooms: } 1, 3, 5, \\ldots' },
    { text: 'For countably many coaches each with countably many seats, number the pairs (coach, seat) along successive diagonals b + s = constant. Every pair receives exactly one natural number and every natural number is used.', tex: '\\pi(b,s) = \\frac{(b+s-2)(b+s-1)}{2} + s' },
    a.infinite
      ? { text: 'Each map puts the set of rooms in one-to-one correspondence with a proper subset of itself. This is impossible for a finite set and characteristic of an infinite one.', tex: '|\\mathbb{N}| = |\\mathbb{N}\\setminus\\{1,\\ldots,m\\}| = |2\\mathbb{N}| = |\\mathbb{N}\\times\\mathbb{N}|' }
      : { text: 'In a hotel with N rooms the shift sends the occupants of the last m rooms beyond room N. A one-to-one map of a finite set into itself is onto, so no room can be freed.', tex: 'n + m > N \\ \\text{ for } n > N - m' },
    ...(a.countable ? [] : [{ text: 'Suppose the guests are all infinite sequences of 0s and 1s and that sequence s⁽ᵏ⁾ has been given room k. The sequence whose k-th digit differs from the k-th digit of s⁽ᵏ⁾ is a guest with no room.', tex: 'd_k = 1 - s^{(k)}_k \\;\\Rightarrow\\; d \\ne s^{(k)}\\ \\text{for every } k' }]),
  ],
  solve(v, a) {
    const Nw = int(v.N_w, 10, 50000), m = int(v.m_new, 1, 1e6), n0 = int(v.n_room, 1, 1e9), b = int(v.b_bus, 1, 1e6), s = int(v.s_seat, 1, 1e6);
    const rnd = N.rng(int(v.seed, 1, 2147483647));
    // verify the three maps on the window
    const seenS = new Set(), seenD = new Set(); let collisions = 0, lowHit = 0, oddHit = 0;
    for (let n = 1; n <= Nw; n++) {
      const fs = n + m, fd = 2 * n;
      if (seenS.has(fs)) collisions++; seenS.add(fs); if (fs <= m) lowHit++;
      if (seenD.has(fd)) collisions++; seenD.add(fd); if (fd % 2 === 1) oddHit++;
    }
    const D = Math.floor((Math.sqrt(8 * Nw + 1) - 1) / 2), T = D * (D + 1) / 2, seenP = new Set(); let outside = 0;
    for (let bb = 1; bb <= D; bb++) for (let ss = 1; bb + ss <= D + 1; ss++) { const z = cantorPair(bb, ss); if (seenP.has(z)) collisions++; seenP.add(z); if (z < 1 || z > T) outside++; }
    const fp = cantorPair(b, s), back = cantorUnpair(fp);
    const nOut = a.infinite ? 0 : Math.min(m, Nw);
    // diagonal argument on a finite window of a proposed list
    const Wd = Math.min(Nw, 300); let differs = 0;
    if (!a.countable) {
      const list = Array.from({ length: Wd }, () => Uint8Array.from({ length: Wd }, () => (rnd() < 0.5 ? 1 : 0)));
      const diag = list.map((row, k) => 1 - row[k]);
      for (let k = 0; k < Wd; k++) if (list[k].some((x, j) => x !== diag[j])) differs++;
    }
    const verdict = !a.infinite ? `No: ${nOut} guest(s) would be left without a room` : !a.countable ? 'No: any room list omits the diagonal sequence' : 'Yes: every guest, old and new, has a room';
    const ns = Array.from({ length: 30 }, (_, i) => i + 1), G = 12;
    const table = Array.from({ length: G }, (_, i) => Array.from({ length: G }, (_, j) => cantorPair(i + 1, j + 1)));
    const Ws = N.logspace(10, Nw, 30).map(Math.round);
    return {
      scalars: [
        scalar('ok', 'All guests accommodated', a.infinite && a.countable ? 1 : 0, '1', { text: verdict }),
        scalar('f_s', `New room of the guest from room ${n0} after admitting ${m}`, n0 + m, '1', { text: !a.infinite && n0 + m > Nw ? `${n0 + m}: beyond the last room` : undefined }),
        scalar('f_d', `New room of the guest from room ${n0} after doubling`, 2 * n0, '1', { text: !a.infinite && 2 * n0 > Nw ? `${2 * n0}: beyond the last room` : undefined }),
        scalar('f_p', `Room for seat ${s} of coach ${b}`, fp, '1'),
        scalar('n_free', 'Rooms freed by the shift', a.infinite ? m : 0, '1'),
        scalar('n_odd', 'Odd rooms freed by doubling, among the first 2N', a.infinite ? Nw - oddHit : 0, '1'),
        scalar('n_coll', 'Collisions found among the images of the window', collisions, '1'),
        scalar('T_cov', `Rooms filled exactly by the first ${D} diagonals of the pairing`, seenP.size, '1'),
        scalar('n_out', 'Guests left without a room', nOut, '1'),
        scalar('n_diag', 'Listed sequences from which the diagonal sequence differs', a.countable ? NaN : differs, '1', { text: a.countable ? 'Not applicable: the arrivals are countable' : `${differs} of ${Wd}: all of them` }),
        scalar('dens', 'Fraction of the first 2N rooms occupied after doubling', seenD.size / (2 * Nw), '1'),
      ],
      series: [
        line('maps', 'Where each map sends the first thirty guests', 'Original room (or seat of coach 1)', '–', ns, [{ label: `Shift n + ${m}`, data: ns.map(n => n + m) }, { label: 'Doubling 2n', data: ns.map(n => 2 * n) }, { label: 'Pairing, coach 1', data: ns.map(n => cantorPair(1, n)) }, { label: 'Identity', data: ns, dash: true }], 'New room', '–', { kind: 'scatter' }),
        line('freed', 'Rooms freed within a growing window', 'Rooms in the window', '–', Ws, [{ label: 'Freed by the shift', data: Ws.map(() => (a.infinite ? m : 0)) }, { label: 'Freed by doubling (odd rooms up to 2N)', data: Ws.map(q => (a.infinite ? q : 0)) }], 'Free rooms', '–', { logx: true, logy: a.infinite }),
      ],
      fields: [field('pairing-table', 'Room assigned to each seat of each coach', table, [0.5, G + 0.5, 0.5, G + 0.5], 'Seat', 'Coach', 'room')],
      checks: [
        check('The maps are one-to-one on the window', collisions, 0, 'No two guests are sent to the same room'),
        check('The shift leaves the first m rooms empty', lowHit, 0, 'No image is at most m'),
        check('The pairing fills an initial block of rooms exactly', (seenP.size - T) + outside, 0, 'The first D diagonals map onto rooms 1 to D(D + 1)/2'),
        check('Pairing and inverse agree', Math.abs(back[0] - b) + Math.abs(back[1] - s), 0, 'Round trip for the followed passenger'),
      ],
      warnings: a.infinite ? [] : ['In a finite hotel the same room maps fail: the shift needs rooms beyond the last one. The possibility of freeing a room in a full hotel is what distinguishes an infinite set.'],
    };
  },
  benchmarks(v) {
    const out = []; let bad = 0;
    for (let z = 1; z <= 5000; z++) { const [b, s] = cantorUnpair(z); if (b < 1 || s < 1 || cantorPair(b, s) !== z) bad++; }
    out.push(bench('Pairing is a bijection on rooms 1 to 5000', bad, 0, 'Every room has exactly one (coach, seat) pre-image', 1e-12));
    out.push(bench('Pairing of coach 1, seat 1', cantorPair(1, 1), 1, 'Start of the enumeration', 1e-12));
    out.push(bench('Pairing of coach 3, seat 5', cantorPair(3, 5), 26, '(6·7)/2 + 5', 1e-12));
    const r = this.solve({ ...v, N_w: 1000, b_bus: 3, s_seat: 5 }, { infinite: true, countable: true });
    out.push(bench('Rooms filled by the complete diagonals within a window of 1000', val(r, 'T_cov'), 990, 'Triangular number 44·45/2; the next, 1035, exceeds the window', 1e-12));
    out.push(bench('Fraction of rooms 1 to 2000 occupied after doubling', val(r, 'dens'), 0.5, 'Natural density of the even numbers', 1e-12));
    out.push(bench('Collisions among the images of the window', val(r, 'n_coll'), 0, 'All three maps are one-to-one', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const m = Math.min(int(v.m_new, 1, 1e6), 3), xs = Array.from({ length: 8 }, (_, i) => 60 + i * 68);
    return svg(`
      ${S.text(320, 30, a.infinite ? 'Rooms 1, 2, 3, … all occupied' : 'A finite hotel, all rooms occupied')}
      ${xs.map((x, i) => `${S.rect(x - 24, 70, 48, 48)}${S.text(x, 100, `${i + 1}`)}`).join('')} ${S.text(600, 100, a.infinite ? '…' : '', 'd-text')}
      ${xs.map((x, i) => `${S.rect(x - 24, 220, 48, 48, i < m ? 'd-hazard' : 'd-body')}${S.text(x, 250, i < m ? 'free' : `${i + 1 - m}`, i < m ? 'd-text d-small' : 'd-text')}`).join('')} ${S.text(600, 250, a.infinite ? '…' : '', 'd-text')}
      ${xs.slice(0, 8 - m).map((x, i) => S.arrow(x, 122, xs[i + m], 216)).join('')}
      ${S.text(320, 170, `guest in room n moves to room n + ${m}`, 'd-text d-small')}
      ${S.text(320, 305, a.infinite ? 'No guest is left over, because there is no last room' : 'The guests of the last rooms have nowhere to go')}
      ${S.text(320, 335, 'Doubling n → 2n frees every odd room', 'd-text d-small')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Bijection', text: 'There is a one-to-one correspondence between all the rooms and a proper subset of the rooms' }, { k: 'SameSize', text: 'The set of rooms and that proper subset have the same number of elements' }, { k: 'PartSmaller', text: 'A proper part is always smaller than the whole' }],
    premises: ['Bijection', 'Bijection -> SameSize', 'PartSmaller -> ~SameSize'],
    conclusion: '~PartSmaller',
  },
  philosophy: [
    'Hilbert\'s hotel dramatises a conflict between two ways of comparing sizes that agree for finite collections: by containment, on which a proper part is smaller, and by one-to-one correspondence, on which sets that can be paired off are equal. Galileo noticed the conflict for the square numbers and concluded that "equal" and "less" do not apply to infinities. Cantor chose correspondence and obtained a consistent arithmetic of infinite numbers.',
    'Nothing in the story is contradictory, but it is contrary to finite experience, which is why it has been used both to teach set theory and, in philosophical theology and cosmology, to argue that an actual infinity cannot exist in the physical world. The second use needs the additional premise that what is counter-intuitive is impossible.',
    'The diagonal argument marks the limit of the hotel\'s capacity and shows that infinity is not a single size. Whether there is a size strictly between the countable and the continuum is undecided by the standard axioms of set theory.',
  ],
  experiment: {
    objective: 'Verify computationally, on finite windows of increasing size, that the room maps are one-to-one and that the pairing enumerates every coach and seat exactly once.',
    apparatus: ['A computer program implementing the three maps and the inverse pairing', 'A set data structure for detecting repeated room numbers'],
    instruments: [{ name: 'Collision counter', measures: 'Pairs of guests assigned the same room', range: 'Windows of 10 to 10⁶ rooms', resolution: 'Exact' }, { name: 'Coverage counter', measures: 'Rooms in an initial block left unassigned by the pairing', range: 'Diagonals 1 to D', resolution: 'Exact' }],
    procedure: ['Apply each map to rooms 1 to N and record the images.', 'Test for repeated images and for images falling in the block that should be free.', 'Enumerate all coach–seat pairs on the first D diagonals and confirm that the images are exactly the first D(D + 1)/2 rooms.', 'Increase N and repeat; then run the same maps in a hotel with only N rooms and count the guests displaced.'],
    controls: ['A finite hotel, in which the shift must displace exactly m guests', 'A deliberately non-injective map such as n → ⌈n/2⌉, which the collision test must detect'],
    signatures: ['Zero collisions at every window size', 'Number of freed rooms independent of window size for the shift and growing in proportion for doubling', 'Diagonal sequence differing from every listed sequence when the arrivals are uncountable'],
    safety: [],
  },
  falsify: ['Two distinct rooms with the same image under any of the three maps, or a room in the initial block not reached by the pairing.', 'The verification covers only finite windows; the general statements are theorems proved by elementary algebra, not empirical claims.'],
  alternatives: [
    { name: 'Cantorian set theory', text: 'Size is measured by one-to-one correspondence. A set is infinite exactly when it can be matched with a proper subset of itself, and there are infinitely many infinite sizes.' },
    { name: 'Part–whole principle', text: 'Size respects containment. Recent theories of numerosity develop this alternative consistently for countable sets, at the cost of making size depend on how the set is presented.' },
    { name: 'Finitism and potential infinity', text: 'Only finite collections, or processes that can always be continued, are admitted. On this view the completed hotel is not a legitimate object, and the story shows why.' },
    { name: 'Physical impossibility', text: 'Even if the mathematics is coherent, moving infinitely many guests in a finite time would require unbounded speeds and energies; the hotel is a mathematical illustration and not a physical proposal.' },
  ],
  limits: 'The numerical verification is necessarily confined to finite windows and to a finite fragment of the diagonal argument. Room numbers are held as double-precision integers, exact up to 2⁵³. The physical feasibility of relocating infinitely many guests is not addressed.',
  numerics: { method: 'Exhaustive check of injectivity and coverage on a finite window; closed-form inverse of the pairing function', resolution: 'N_w' },
  extensions: ['Countably many layers of infinity: ships carrying coaches carrying passengers', 'Prime-power and interleaving-digit assignments', 'The continuum hypothesis', 'Supertask versions in which the moves are completed in a finite time'],
};

// ================================================================== 17. Drake equation and the Fermi question
const GAL_AGE = 1e10 * YEAR, GAL_DIAM = 1e5 * LY, GAL_THICK = 1e3 * LY, GAL_VOL = Math.PI * (5e4 * LY) ** 2 * GAL_THICK;
const DRAKE_F = [['R_star', 'Star formation rate', false, false], ['f_p', 'Stars with planets', true, false], ['n_e', 'Habitable planets per system', false, false], ['f_l', 'Life arises', true, true], ['f_i', 'Intelligence evolves', true, true], ['f_c', 'Detectable technology', true, true], ['L_civ', 'Lifetime', false, true]];
const drakeFermi = {
  id: 'drake-fermi',
  title: 'The Drake equation and the Fermi question',
  module: 1, klass: ['III', 'I'], domains: ['space', 'logic'], hypothetical: true,
  keywords: ['drake equation', 'fermi paradox', 'fermi question', 'where is everybody', 'extraterrestrial civilisations', 'extraterrestrial civilizations', 'alien civilisations', 'aliens', 'seti', 'great filter', 'are we alone'],
  summary: 'Number of detectable civilisations in the Galaxy from the Drake factors, with a seeded Monte-Carlo treatment of their order-of-magnitude uncertainty and the resulting probability that we are alone.',
  background: [
    'The Drake equation organises the estimate of the number of communicating civilisations in the Milky Way as a product: the rate of star formation, the fraction of stars with planets, the number of habitable planets per system, the fractions on which life, intelligence and detectable technology arise, and the time for which such a technology persists. The first three factors are now constrained by observation. The last four are unknown, in some cases to within tens of orders of magnitude.',
    'Fermi\'s question — where is everybody? — arises because a single civilisation spreading at a small fraction of the speed of light could cross the Galaxy in a time far shorter than its age. Point estimates of the Drake product often suggest many civilisations, which seems hard to reconcile with the absence of evidence. When the uncertainty in each factor is carried through, however, the distribution of the product is so broad that a substantial probability falls on there being none but ourselves, and the absence of evidence is unsurprising.',
  ],
  phenomena: ['Product of uncertain factors', 'Log-uniform uncertainty over orders of magnitude', 'Steady-state balance of appearance and disappearance', 'Galactic colonisation time'],
  laws: ['kolmogorov', 'causality'],
  refs: ['Hart, M. H. (1975). An explanation for the absence of extraterrestrials on Earth. Quarterly Journal of the Royal Astronomical Society 16, 128–135.', 'Tipler, F. J. (1980). Extraterrestrial intelligent beings do not exist. Quarterly Journal of the Royal Astronomical Society 21, 267–281.', 'Brin, G. D. (1983). The great silence: the controversy concerning extraterrestrial intelligent life. Quarterly Journal of the Royal Astronomical Society 24, 283–309.', 'Drake, F. & Sobel, D. (1992). Is Anyone Out There? The Scientific Search for Extraterrestrial Intelligence. Delacorte Press.', 'Webb, S. (2015). If the Universe Is Teeming with Aliens … Where Is Everybody? 2nd ed. Springer.', 'Sandberg, A., Drexler, E. & Ord, T. (2018). Dissolving the Fermi paradox. arXiv:1806.02404.'],
  inputs: [
    inp('R_star', 'Rate of star formation in the Galaxy', '1/yr', 2, { min: 0.5, max: 10, aliases: ['star formation rate', 'stars per year'], src: 'Observational estimates of roughly 1–3 solar masses per year' }),
    inp('f_p', 'Fraction of stars with planets', '1', 0.9, { min: 0.1, max: 1, aliases: ['fraction with planets'], src: 'Exoplanet surveys indicate that most stars have planets' }),
    inp('n_e', 'Habitable planets per planetary system', '1', 0.5, { min: 0.01, max: 5, aliases: ['habitable planets', 'earth-like planets'], src: 'Occurrence-rate estimates from transit surveys; uncertain by a factor of several' }),
    inp('f_l', 'Fraction of habitable planets on which life arises', '1', 0.1, { min: 1e-30, max: 1, kind: 'hypothetical', aliases: ['fraction with life', 'abiogenesis'] }),
    inp('f_i', 'Fraction of those on which intelligence evolves', '1', 0.1, { min: 1e-6, max: 1, kind: 'hypothetical', aliases: ['fraction intelligent', 'intelligence'] }),
    inp('f_c', 'Fraction of those that develop detectable technology', '1', 0.1, { min: 1e-3, max: 1, kind: 'hypothetical', aliases: ['fraction communicating', 'technology'] }),
    inp('L_civ', 'Time for which a civilisation remains detectable', 'yr', 10000, { min: 10, max: 1e9, kind: 'hypothetical', aliases: ['lifetime', 'civilisation lifetime', 'civilization lifetime', 'longevity'] }),
    inp('u_hyp', 'Uncertainty of the four unknown factors, in orders of magnitude either way', '1', 2, { min: 0, max: 6, kind: 'hypothetical', aliases: ['uncertainty', 'orders of magnitude'] }),
    inp('u_ast', 'Uncertainty of the three astrophysical factors, in orders of magnitude either way', '1', 0.3, { min: 0, max: 1, aliases: ['astrophysical uncertainty'] }),
    inp('beta_x', 'Expansion speed of a colonising civilisation as a fraction of the speed of light (used when colonisation is allowed)', '1', 0.01, { min: 1e-5, max: 0.5, kind: 'hypothetical', aliases: ['expansion speed', 'colonisation speed', 'colonization speed'] }),
    inp('n_samples', 'Monte-Carlo samples', '1', 5000, { min: 1000, max: 200000, kind: 'numerical', aliases: ['samples'] }),
    inp('seed', 'Random seed', '1', 9, { min: 1, max: 1000000, kind: 'numerical', aliases: ['seed'] }),
  ],
  assumptions: [
    asm('uncertain', 'Each factor is uncertain over a range of orders of magnitude, and the uncertainty is propagated through the product.', { why: 'Several factors are unconstrained by observation', alt: 'Each factor is taken at its stated value and the product is a single number.', affects: ['P_alone', 'N_med'] }),
    asm('steady', 'Civilisations appear at a steady rate and the number present is that rate times their lifetime.', { why: 'Drake\'s steady-state form', alt: 'The lifetime cannot exceed the age of the Galactic disc, about ten billion years.', affects: ['N_civ'] }),
    asm('no_colonise', 'Civilisations stay near their home stars; each is detectable only from where it arose.', { why: 'The assumption built into the Drake equation', alt: 'A civilisation may spread through the Galaxy at the stated speed. The question becomes whether any arose early enough to have arrived here already.', affects: ['P_alone'] }),
  ],
  symbols: { N_civ: ['Number of detectable civilisations in the Galaxy', '1'], N_ever: ['Number of civilisations that have ever arisen in the Galaxy', '1'], T_gal: ['Age of the Galactic disc', 's'], D_gal: ['Diameter of the Galactic disc', 'm'], t_col: ['Time to cross the Galaxy at the expansion speed', 's'] },
  equations: a => [
    eq('drake', 'Drake equation', 'N_civ', a.steady ? 'R_star*f_p*n_e*f_l*f_i*f_c*L_civ' : 'R_star*f_p*n_e*f_l*f_i*f_c*min(L_civ, T_gal)', { kind: 'hypothesis', origin: 'Drake (1961): steady-state product of rate, fractions and lifetime', needs: a.steady ? ['steady'] : [] }),
    ...(a.no_colonise ? [] : [
      eq('tcol', 'Galactic crossing time', 't_col', 'D_gal/(beta_x*c)', { kind: 'derived', origin: 'Hart (1975): expansion at a fixed fraction of the speed of light' }),
      eq('ever', 'Civilisations that arose early enough to have crossed the Galaxy', 'N_ever', 'R_star*f_p*n_e*f_l*f_i*f_c*max(T_gal - t_col, 0*T_gal)', { kind: 'hypothesis', origin: 'Steady rate of appearance over the age of the disc, less the crossing time' }),
    ]),
  ],
  derivation: a => [
    { text: 'If detectable civilisations appear at a rate Γ per year and each remains detectable for L years, the number present in a steady state is Γ L.', tex: 'N = \\Gamma\\,L' },
    { text: 'The rate of appearance is the rate of star formation multiplied by the chain of fractions leading from a star to a detectable technology.', tex: 'N = R_*\\,f_p\\,n_e\\,f_l\\,f_i\\,f_c\\,L' },
    ...(a.uncertain ? [
      { text: 'Where a factor is known only to within orders of magnitude, a distribution uniform in its logarithm represents that ignorance. The logarithm of N is then a sum of independent uniform variables, whose mean and variance add.', tex: '\\log_{10}N = \\sum_i \\log_{10}x_i,\\qquad \\sigma^2 = \\sum_i\\frac{(b_i-a_i)^2}{12}' },
      { text: 'The probability that we are alone in the Galaxy is the probability mass at N < 1. Because the distribution of N spans many decades, its mean can be large while its median is small.', tex: 'P(N<1) = P\\left(\\log_{10}N < 0\\right)' },
    ] : []),
    ...(a.no_colonise ? [] : [{ text: 'A civilisation expanding at a fraction β of the speed of light crosses the Galactic disc in a time much shorter than the age of the disc. The absence of visitors then bears on the number that have ever arisen, not only on those present now.', tex: 't_{col} = \\frac{D}{\\beta c} \\ll T_{gal}' }]),
  ],
  solve(v, a) {
    const cen = DRAKE_F.map(f => v[f[0]]), nS = int(v.n_samples, 1000, 1000000), rnd = N.rng(int(v.seed, 1, 2147483647));
    const Leff = a.steady ? v.L_civ : Math.min(v.L_civ, GAL_AGE), rate = cen.slice(0, 6).reduce((p, x) => p * x, 1), Npoint = rate * Leff;
    const tCol = GAL_DIAM / (v.beta_x * C.c), window = Math.max(GAL_AGE - tCol, 0), NeverPoint = rate * window;
    // sampling ranges in log10
    const lo = [], hi = [];
    DRAKE_F.forEach((f, i) => { const u = a.uncertain ? (f[3] ? v.u_hyp : v.u_ast) : 0, c = Math.log10(cen[i]); lo.push(c - u); hi.push(f[2] ? Math.min(0, c + u) : c + u); });
    const lgAge = Math.log10(GAL_AGE), lgWin = window > 0 ? Math.log10(window) : -Infinity;
    const logs = new Float64Array(nS); let sum = 0, alone = 0;
    for (let k = 0; k < nS; k++) {
      let lr = 0; for (let i = 0; i < 6; i++) lr += lo[i] + (hi[i] - lo[i]) * rnd();
      let lL = lo[6] + (hi[6] - lo[6]) * rnd(); if (!a.steady) lL = Math.min(lL, lgAge);
      const lgN = lr + lL; logs[k] = lgN; sum += lgN;
      if (a.no_colonise ? lgN < 0 : lr + lgWin < 0) alone++;
    }
    const sorted = Float64Array.from(logs).sort(), qtl = q => sorted[Math.min(nS - 1, Math.floor(q * (nS - 1)))];
    const muMC = sum / nS, muAn = N.sum(lo.map((l, i) => (l + hi[i]) / 2)), sdAn = Math.sqrt(N.sum(lo.map((l, i) => (hi[i] - l) ** 2 / 12)));
    const pAlone = alone / nS, pNorm = sdAn > 0 ? Phi(-muAn / sdAn) : (muAn < 0 ? 1 : 0);
    // mean spacing: three-dimensional while it is smaller than the thickness of the disc, otherwise two-dimensional within the disc
    const med = Math.pow(10, qtl(0.5)), d3 = Math.cbrt(GAL_VOL / med), dnn = med >= 1 ? (d3 <= GAL_THICK ? d3 : Math.sqrt(GAL_VOL / GAL_THICK / med)) : NaN;
    const span = sorted[nS - 1] - sorted[0], hist = span > 1e-9 ? N.histogram(sorted, 40) : { centres: [sorted[0]], counts: [nS] };
    const cdfX = N.linspace(sorted[0], sorted[nS - 1] + 1e-9, 80), cdfY = cdfX.map(x => { let l = 0, h = nS; while (l < h) { const mid = (l + h) >> 1; if (sorted[mid] <= x) l = mid + 1; else h = mid; } return l / nS; });
    const warnings = ['Four of the seven factors are unknown; the results are conditional on the stated values and ranges and are not measurements.'];
    if (a.uncertain && Npoint > 1 && pAlone > 0.1) warnings.push(`The point estimate is ${lab(Npoint)} civilisations, yet ${lab(100 * pAlone)} % of the probability lies at fewer than one. A product of central values conceals how much weight the uncertainty places on an empty Galaxy.`);
    if (!a.no_colonise && window === 0) warnings.push('At this expansion speed the crossing time exceeds the age of the Galaxy: no civilisation could yet have spread across it.');
    return {
      scalars: [
        scalar('N_civ', 'Point estimate of detectable civilisations in the Galaxy', Npoint, '1', { status: 'hypothetical' }),
        scalar('N_med', 'Median of the distribution', med, '1', { status: 'hypothetical' }),
        scalar('N_05', '5th percentile', Math.pow(10, qtl(0.05)), '1', { status: 'hypothetical' }),
        scalar('N_95', '95th percentile', Math.pow(10, qtl(0.95)), '1', { status: 'hypothetical' }),
        scalar('mu_log', 'Mean of log₁₀ N (sampled)', muMC, '1', { status: 'hypothetical' }),
        scalar('sd_log', 'Standard deviation of log₁₀ N (analytic)', sdAn, '1', { status: 'hypothetical' }),
        scalar('P_alone', a.no_colonise ? 'Probability that no other detectable civilisation exists in the Galaxy (N < 1)' : 'Probability that no civilisation arose early enough to have reached us', pAlone, '1', { ...PCT, status: 'hypothetical' }),
        scalar('P_norm', 'Normal approximation to P(N < 1)', pNorm, '1', { ...PCT, status: 'hypothetical' }),
        scalar('d_nn', 'Typical distance to the nearest civilisation at the median', dnn, 'm', { show: 'ly', text: Number.isFinite(dnn) ? undefined : 'None expected within the Galaxy', status: 'hypothetical' }),
        scalar('t_col', 'Time to cross the Galaxy at the stated expansion speed', tCol, 's', { show: 'yr', status: 'hypothetical' }),
        scalar('N_ever', 'Point estimate of civilisations that arose early enough to have crossed the Galaxy', NeverPoint, '1', { status: 'hypothetical' }),
        scalar('T_gal', 'Age of the Galactic disc adopted', GAL_AGE, 's', { show: 'yr' }),
        scalar('D_gal', 'Diameter of the Galactic disc adopted', GAL_DIAM, 'm', { show: 'ly' }),
      ],
      series: [
        line('histogram', 'Distribution of the number of civilisations', 'log₁₀ N', '–', hist.centres, [{ label: 'Samples', data: hist.counts }], 'Count', '–', { kind: 'bar', status: 'hypothetical', note: 'Values to the left of zero correspond to fewer than one civilisation.' }),
        line('cdf', 'Cumulative probability of log₁₀ N', 'log₁₀ N', '–', cdfX, [{ label: 'P(log₁₀ N ≤ x)', data: cdfY }, { label: 'One half', data: cdfX.map(() => 0.5), dash: true }], 'Probability', '–', { status: 'hypothetical' }),
        line('factors', 'Contribution of each factor to log₁₀ N at its stated value', 'Factor', '–', DRAKE_F.map((_, i) => i + 1), [{ label: 'log₁₀ of the factor (rate and lifetime in years)', data: cen.map((x, i) => Math.log10(i === 0 ? x * YEAR : i === 6 ? Leff / YEAR : x)) }], 'log₁₀', '–', { kind: 'bar', categories: DRAKE_F.map(f => f[1]), status: 'hypothetical' }),
      ],
      checks: [
        check('Sampled mean of log₁₀ N against the analytic mean', a.steady ? muMC - muAn : 0, 4 * sdAn / Math.sqrt(nS) + 1e-9, 'Within four standard errors'),
        check('Point estimate equals the product of the factors', Math.log10(Npoint) - N.sum(cen.slice(0, 6).map(Math.log10)) - Math.log10(Leff), 1e-9, ''),
        check('Probability lies in [0, 1]', pAlone < 0 || pAlone > 1 ? 1 : 0, 0, ''),
      ],
      warnings,
    };
  },
  benchmarks(v, a) {
    const out = [];
    const d = this.solve({ ...v, R_star: 1 / YEAR, f_p: 0.5, n_e: 2, f_l: 1, f_i: 0.1, f_c: 0.1, L_civ: 1e4 * YEAR }, { uncertain: false, steady: true, no_colonise: true });
    out.push(bench('Point estimate for unit rate, 0.5, 2, 1, 0.1, 0.1 and 10 000 years', val(d, 'N_civ'), 100, 'Direct product', 1e-9));
    out.push(bench('Median without uncertainty equals the point estimate', val(d, 'N_med'), 100, 'Degenerate distribution', 1e-9));
    const g = N.rng(123); let s = 0; for (let i = 0; i < 100000; i++) s += g();
    out.push(bench('Mean of the uniform generator', s / 1e5, 0.5, 'Tolerance of four standard errors', 4 * Math.sqrt(1 / 12 / 1e5) / 0.5));
    out.push(bench('Galactic crossing time at one per cent of the speed of light', val(this.solve({ ...v, beta_x: 0.01 }, a), 't_col') / YEAR, 1e7, '100 000 light-years at 0.01 c', 1e-6));
    const u = this.solve({ ...v, R_star: 1 / YEAR, f_p: 1, n_e: 1, f_l: 0.01, f_i: 0.01, f_c: 0.01, L_civ: 1e6 * YEAR, u_hyp: 1, u_ast: 0 }, { uncertain: true, steady: true, no_colonise: true });
    out.push(bench('Spread of log₁₀ N for four factors each uncertain by one decade either way', val(u, 'sd_log'), Math.sqrt(4 / 3), 'Variance of a uniform variable of width 2 is 1/3; four add', 1e-12));
    out.push(bench('Probability of N < 1 for a distribution symmetric about N = 1', val(u, 'P_alone'), 0.5, 'Symmetry of the sum of uniform variables; tolerance of four standard errors', 4 / Math.sqrt(int(v.n_samples, 1000, 1000000))));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const w = 78, x0 = 320 - (7 * w + 6 * 6) / 2, names = ['R*', 'f_p', 'n_e', 'f_l', 'f_i', 'f_c', 'L'];
    const vals = [v.R_star * YEAR, v.f_p, v.n_e, v.f_l, v.f_i, v.f_c, v.L_civ / YEAR];
    return svg(`
      ${S.text(320, 40, 'N = R* · f_p · n_e · f_l · f_i · f_c · L')}
      ${names.map((nm, i) => `${S.rect(x0 + i * (w + 6), 80, w, 70, DRAKE_F[i][3] ? 'd-hazard' : 'd-body')}${S.text(x0 + i * (w + 6) + w / 2, 108, nm)}${S.text(x0 + i * (w + 6) + w / 2, 134, lab(vals[i], '', 2), 'd-text d-small')}`).join('')}
      ${S.text(x0 + 1.5 * (w + 6) + w / 2 - 3, 172, 'constrained by observation', 'd-text d-small')} ${S.text(x0 + 4.5 * (w + 6) + w / 2 - 3, 172, 'unknown (hypothetical values)', 'd-text d-small')}
      ${S.path('M120 300 Q320 230 520 300 Q320 330 120 300 Z', 'd-line')} ${S.circle(380, 296, 4, 'd-hazard')} ${S.text(392, 292, 'Sun', 'd-text d-small', 'start')}
      ${S.dim(120, 345, 520, 345, '100 000 light-years')}
      ${S.text(320, 215, a.no_colonise ? 'How many are detectable now?' : `Crossing time at ${lab(v.beta_x)} c: ${lab(GAL_DIAM / (v.beta_x * C.c) / YEAR, 'yr')}`)}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'Many', text: 'Many technological civilisations have arisen in the Galaxy' }, { k: 'Spread', text: 'At least one of them spreads across the Galaxy in a time short compared with its age' }, { k: 'Here', text: 'They, or their artefacts, are present in the Solar System' }, { k: 'Observed', text: 'We observe evidence of them' }],
    premises: ['(Many & Spread) -> Here', 'Here -> Observed', '~Observed'],
    conclusion: '~(Many & Spread)',
  },
  philosophy: [
    'The Drake equation is less a theory than a way of partitioning ignorance. It produces a number only when values are supplied for quantities about which there is, for now, no evidence beyond a single example subject to an observation-selection effect: we could not have found ourselves on a planet where intelligence failed to arise.',
    'The Fermi question is a valid argument whose conclusion is a disjunction: either civilisations are rare, or they do not spread, or they are here undetected, or one of the linking premises fails. Each proposed solution selects a disjunct, and none can presently be tested decisively. The absence of observation is evidence, but its weight depends on how likely detection would be under each alternative.',
    'Treating the factors as distributions instead of point values changes the character of the problem. If a credible state of knowledge already assigns appreciable probability to an empty Galaxy, there is no paradox to resolve, only uncertainty to reduce. That conclusion is itself conditional on the chosen ranges, which is why the inputs here are labelled hypothetical.',
  ],
  experiment: {
    objective: 'Constrain the factors of the Drake equation by observation and search for technosignatures that would bound the number of detectable civilisations.',
    apparatus: ['Exoplanet transit and radial-velocity surveys for the planetary factors', 'Spectroscopy of exoplanet atmospheres for biosignature gases', 'Radio and optical searches for narrow-band or pulsed artificial signals', 'Infrared surveys for waste heat from large-scale engineering'],
    instruments: [{ name: 'Space photometer', measures: 'Occurrence rate of small planets in habitable zones', range: 'Orbital periods to about one year', resolution: 'Transit depth ≈ 10⁻⁴' }, { name: 'Infrared space spectrograph', measures: 'Atmospheric composition of transiting planets', range: '0.6–28 µm', resolution: 'Spectral resolving power 100–3000' }, { name: 'Radio telescope with a multi-channel spectrometer', measures: 'Narrow-band emission', range: '1–10 GHz', resolution: '≈ 1 Hz channels' }],
    procedure: ['Measure planet occurrence rates and correct for detection completeness.', 'Search nearby habitable-zone planets for atmospheric gases out of chemical equilibrium.', 'Survey stars and galaxies for artificial signals and convert non-detections into upper limits on transmitter density and power.', 'Update the distributions of the factors and recompute the distribution of N.'],
    controls: ['Re-observation of candidate signals and rejection of terrestrial interference by position switching', 'Abiotic explanations tested for every candidate biosignature', 'Injection of artificial signals to measure detection efficiency'],
    signatures: ['A confirmed second origin of life, on Mars, an icy moon or an exoplanet, would raise the life factor sharply', 'A confirmed technosignature would settle N ≥ 1 beyond ourselves', 'Continued non-detection lowers the upper bound on the product of the last four factors only slowly'],
    safety: [],
  },
  falsify: ['The claim that N is large is falsified, for a given class of signal, by a complete survey of the Galaxy with no detection; the claim that N is below one is falsified by a single confirmed detection.', 'The steady-state product itself would be undermined by evidence that civilisations arise in bursts or spread between stars, so that their number is not a rate multiplied by a lifetime.'],
  alternatives: [
    { name: 'Rare Earth and the Great Filter', text: 'One or more steps between a habitable planet and a lasting technology is extremely improbable. If the hard step lies ahead of us it concerns our own future.' },
    { name: 'They exist but do not spread or signal', text: 'Interstellar travel may be impractical, expansion may halt for economic or sociological reasons, or civilisations may be short-lived or quiet.' },
    { name: 'They are present but undetected', text: 'Our searches have covered a minute part of the possible range of frequencies, directions, times and kinds of evidence.' },
    { name: 'Dissolution by uncertainty', text: 'With honest ranges on the factors the probability of an empty Galaxy is not small, so the silence needs no special explanation.' },
    { name: 'Selection effects', text: 'Our own existence cannot be used straightforwardly as a data point for the probability of life or intelligence, because it is a precondition for asking the question.' },
  ],
  limits: 'Independent factors, each uniform in its logarithm within a symmetric range about the stated value, with fractions limited to one. The choice of central values and widths for the four unknown factors determines the answer; the model propagates assumptions and does not supply evidence. Galactic structure, the history of star formation and the habitability of different regions are ignored.',
  numerics: { method: 'Seeded Monte-Carlo sampling in logarithmic space; analytic mean and variance of the sum of uniform variables for comparison', order: 0.5, resolution: 'n_samples' },
  extensions: ['Factor distributions based on models of abiogenesis and of evolutionary transitions', 'Time-dependent star-formation history', 'Percolation models of interstellar settlement', 'Bayesian updating on the early appearance of life on Earth'],
};

// ================================================================== 18. Sorites paradox
/** Run the chain of conditionals from n = top down to 1. Returns derived truth of "1 grain is a heap" and diagnostics. */
function soritesChain(nTop, h, tolerant, luk, sample) {
  let hn = h(nTop), v = hn, iMin = 1, nNotFull = 0, nHalf = NaN, nWorst = nTop, si = sample ? sample.length - 1 : -1;
  const outN = [], outV = [], outH = [], outI = [];
  while (si >= 0 && sample[si] > nTop) si--;
  if (si >= 0 && sample[si] === nTop) { outN.push(nTop); outV.push(v); outH.push(hn); outI.push(1); si--; }
  for (let n = nTop; n >= 2; n--) {
    const hm = h(n - 1), I = tolerant ? 1 : Math.min(1, 1 - hn + hm);
    if (I < iMin) { iMin = I; nWorst = n; }
    if (I < 1 - 1e-12) nNotFull++;
    v = luk ? Math.max(0, v + I - 1) : v * I;
    if (Number.isNaN(nHalf) && v < 0.5) nHalf = n - 1;
    if (si >= 0 && sample[si] === n - 1) { outN.push(n - 1); outV.push(v); outH.push(hm); outI.push(I); si--; }
    hn = hm;
  }
  return { v, iMin, nNotFull, nHalf, nWorst, outN: outN.reverse(), outV: outV.reverse(), outH: outH.reverse(), outI: outI.reverse() };
}
const soritesHeap = {
  id: 'sorites-heap',
  title: 'The sorites paradox of the heap',
  module: 1, klass: ['II'], domains: ['logic'],
  keywords: ['sorites paradox', 'sorites', 'paradox of the heap', 'heap of sand', 'grains of sand', 'vagueness', 'vague predicate', 'fuzzy logic', 'borderline case', 'bald man', 'heap'],
  summary: 'Removing one grain never seems to turn a heap into a non-heap, yet ten thousand such steps do. The classical chain of conditionals, and the gradual loss of truth along the chain under fuzzy degrees with Łukasiewicz implication.',
  background: [
    'Ten thousand grains of sand make a heap. If n grains make a heap, so, it seems, do n − 1: a single grain cannot make the difference. Applying the second premise 9 999 times by modus ponens yields the conclusion that one grain makes a heap. The premises appear true, the reasoning valid and the conclusion false.',
    'The paradox arises for any predicate with borderline cases — tall, bald, red, adult. Responses differ on what to revise. Epistemicism keeps classical logic and holds that there is a sharp but unknowable boundary, so one inductive step is false. Supervaluationism holds that the inductive premise is false on every admissible sharpening without any particular step being the false one. Degree theories assign intermediate truth values: each step is almost but not quite true, and the small shortfalls accumulate along the chain.',
  ],
  phenomena: ['Vague predicates and borderline cases', 'Tolerance to small changes', 'Accumulation of small errors over long inference chains', 'Many-valued truth'],
  laws: ['logic_nc', 'logic_em'],
  refs: ['Zadeh, L. A. (1965). Fuzzy sets. Information and Control 8, 338–353.', 'Goguen, J. A. (1969). The logic of inexact concepts. Synthese 19, 325–373.', 'Fine, K. (1975). Vagueness, truth and logic. Synthese 30, 265–300.', 'Williamson, T. (1994). Vagueness. Routledge.', 'Keefe, R. & Smith, P. (eds) (1997). Vagueness: A Reader. MIT Press.'],
  inputs: [
    inp('n_top', 'Number of grains in the starting heap', '1', 10000, { min: 100, max: 1000000, aliases: ['grains', 'starting grains', 'heap size'] }),
    inp('n_mid', 'Number of grains at which "heap" is half true (or at which the sharp boundary lies)', '1', 100, { min: 2, max: 100000, aliases: ['midpoint', 'boundary', 'threshold'] }),
    inp('w_s', 'Width of the borderline region, in grains', '1', 20, { min: 0.5, max: 10000, aliases: ['width', 'steepness', 'borderline width'] }),
  ],
  assumptions: [
    asm('tolerance', 'Tolerance: one grain never makes a difference, so every conditional "if n grains make a heap then n − 1 do" is fully true.', { why: 'The intuitive premise that drives the paradox', alt: 'Each conditional has the truth value that the adopted semantics assigns to it, which may be less than one.', affects: ['v_end', 'I_min'] }),
    asm('bivalent', '"Heap" is a two-valued predicate: every number of grains either makes a heap or does not.', { why: 'Classical logic', alt: 'Heapness comes in degrees, rising smoothly from 0 to 1 across the borderline region (a logistic membership function).', affects: ['h_1', 'I_min'] }),
    asm('lukasiewicz', 'Shortfalls from full truth add along a chain of inferences (Łukasiewicz conjunction).', { why: 'The standard fuzzy logic for sorites reasoning', alt: 'Truth values multiply along the chain (product conjunction).', affects: ['v_end'] }),
  ],
  symbols: { h_n: ['Degree to which n grains make a heap', '1'], h_m: ['Degree to which n − 1 grains make a heap', '1'], n_k: ['Number of grains', '1'], I_k: ['Truth value of the conditional at n grains', '1'], v_k: ['Truth derived so far for the current number of grains', '1'], v_next: ['Truth derived for one grain fewer', '1'] },
  equations: a => [
    a.bivalent
      ? eq('heap', 'Two-valued heap predicate', 'h_n', 'heaviside(n_k - n_mid)', { kind: 'hypothesis', origin: 'Sharp boundary (epistemicism)', needs: ['bivalent'] })
      : eq('heap', 'Degree of heapness', 'h_n', '1/(1 + exp(-(n_k - n_mid)/w_s))', { kind: 'hypothesis', origin: 'Logistic membership function; Zadeh (1965)' }),
    a.tolerance
      ? eq('imp', 'Truth of each inductive conditional', 'I_k', '1', { kind: 'hypothesis', origin: 'Tolerance principle', needs: ['tolerance'] })
      : eq('imp', 'Truth of each inductive conditional', 'I_k', 'min(1, 1 - h_n + h_m)', { kind: 'definition', origin: 'Łukasiewicz implication; reduces to the material conditional for values 0 and 1' }),
    a.lukasiewicz
      ? eq('mp', 'Truth passed on by modus ponens', 'v_next', 'max(0, v_k + I_k - 1)', { kind: 'law', origin: 'Łukasiewicz conjunction of premise and conditional (Goguen 1969)', needs: ['lukasiewicz'] })
      : eq('mp', 'Truth passed on by modus ponens', 'v_next', 'v_k*I_k', { kind: 'law', origin: 'Product conjunction of premise and conditional' }),
  ],
  derivation: a => [
    { text: 'Write H(n) for "n grains make a heap". The argument has one categorical premise and a chain of conditionals.', tex: 'H(N),\\qquad H(n)\\rightarrow H(n-1)\\ \\ (n = N,\\ldots,2)\\qquad\\therefore\\ H(1)' },
    a.bivalent
      ? { text: 'With two truth values, H(N) true and H(1) false, the truth value must change somewhere. At that point the conditional has a true antecedent and a false consequent: exactly one inductive premise is false.', tex: '\\exists\\,n^*:\\ H(n^*)\\land\\lnot H(n^*-1)' }
      : { text: 'Let the degree of heapness rise smoothly with the number of grains. Each conditional is then true to a degree just short of one, the shortfall being the drop in heapness across the step.', tex: 'h(n) = \\frac{1}{1+e^{-(n-n_{mid})/w}},\\qquad I_n = \\min\\big(1,\\,1-h(n)+h(n-1)\\big)' },
    a.lukasiewicz
      ? { text: 'Modus ponens guarantees its conclusion only to the degree of the conjunction of its premises. With Łukasiewicz conjunction the shortfalls add, and the bound telescopes to the degree of heapness itself.', tex: 'v_{n-1} = \\max\\big(0,\\,v_n + I_n - 1\\big) \\;\\Rightarrow\\; v_1 = h(N) -\\sum_{n=2}^{N}\\big(1-I_n\\big) = h(1)' }
      : { text: 'With product conjunction the degrees multiply along the chain, and many factors slightly below one give a product near zero.', tex: 'v_1 = h(N)\\prod_{n=2}^{N} I_n' },
    a.tolerance
      ? { text: 'If every conditional is taken to be fully true, nothing is lost along the chain and the conclusion inherits the full truth of the first premise, contradicting the evident falsity of H(1).', tex: 'I_n = 1\\ \\forall n \\;\\Rightarrow\\; v_1 = h(N) \\approx 1 \\ne h(1) \\approx 0' }
      : { text: 'Each step is nearly valid, yet the conclusion is nearly false: validity in the sense of preserving full truth does not extend to preserving approximate truth over long chains.', tex: '\\min_n I_n \\approx 1 - \\frac{1}{4w}\\quad\\text{but}\\quad v_1 \\approx 0' },
  ],
  solve(v, a) {
    const nTop = int(v.n_top, 10, 2000000), mid = v.n_mid, w = v.w_s;
    const h = a.bivalent ? (n => (n >= mid ? 1 : 0)) : (n => 1 / (1 + Math.exp(-(n - mid) / w)));
    const sample = marks(nTop, 240), r = soritesChain(nTop, h, a.tolerance, a.lukasiewicz, sample);
    const hTop = h(nTop), h1 = h(1), gap = r.v - h1, paradox = gap > 0.5;
    const nBorder = a.bivalent ? 0 : 2 * w * Math.log(9);
    const verdict = paradox ? 'Paradox: premises accepted as true lead by valid steps to a false conclusion'
      : hTop < 0.5 ? 'No paradox: the starting collection is not a clear heap'
        : a.tolerance ? 'No conflict at these values: the single grain is itself counted as a heap'
          : a.bivalent ? `Consistent: exactly one conditional is false, at the sharp boundary between ${Math.ceil(mid)} and ${Math.ceil(mid) - 1} grains`
            : 'Consistent: every conditional is nearly true, and the small shortfalls accumulate until the conclusion is nearly false';
    const warnings = [];
    if (paradox) warnings.push('Tolerance is in force: every conditional is treated as fully true, so the chain delivers "one grain is a heap" with the full truth of the first premise. Switch off tolerance to see how each semantics blocks the argument.');
    if (mid > nTop) warnings.push('The midpoint lies above the starting number of grains, so the starting collection is not a clear heap.');
    return {
      scalars: [
        scalar('verdict', 'Status of the argument', paradox ? 1 : 0, '1', { text: verdict }),
        scalar('h_top', `Truth of "${nTop} grains make a heap"`, hTop, '1'),
        scalar('h_1', 'Truth of "1 grain makes a heap" by direct assessment', h1, '1'),
        scalar('v_end', 'Truth of "1 grain makes a heap" delivered by the chain of inferences', r.v, '1'),
        scalar('gap', 'Excess of the derived over the directly assessed truth', gap, '1'),
        scalar('I_min', 'Truth value of the least true conditional', r.iMin, '1', { text: r.iMin >= 1 ? '1: every conditional is fully true' : undefined }),
        scalar('n_worst', 'Number of grains at which the least true conditional occurs', r.nWorst, '1', { text: r.iMin >= 1 ? 'Not applicable' : undefined }),
        scalar('n_not', 'Conditionals that are less than fully true', r.nNotFull, '1'),
        scalar('n_half', 'Number of grains at which the derived truth first falls below one half', r.nHalf, '1', { text: Number.isNaN(r.nHalf) ? 'Never: the chain stays above one half' : undefined }),
        scalar('n_steps', 'Inference steps in the chain', nTop - 1, '1'),
        scalar('n_border', 'Grains spanned by the borderline region (degree between 0.1 and 0.9)', nBorder, '1'),
      ],
      series: [
        line('truth', 'Truth of "n grains make a heap"', 'Number of grains n', '–', r.outN, [{ label: 'Delivered by the chain from the top', data: r.outV }, { label: 'Direct assessment', data: r.outH, dash: true }], 'Truth value', '–', { logx: true }),
        line('conditional', 'Truth value of each conditional "if n then n − 1"', 'Number of grains n', '–', r.outN, [{ label: 'Truth of the conditional', data: r.outI }], 'Truth value', '–', { logx: true }),
      ],
      checks: [
        check('Truth values lie in [0, 1]', r.outV.some(x => x < -1e-12 || x > 1 + 1e-12) || r.iMin < -1e-12 ? 1 : 0, 0, ''),
        check('Łukasiewicz chain telescopes to the degree of heapness', !a.tolerance && a.lukasiewicz ? r.v - h1 : 0, 1e-8, 'Sum of shortfalls equals the total drop in heapness'),
        check('A two-valued predicate has exactly one false conditional', a.bivalent && !a.tolerance && hTop === 1 && h1 === 0 ? r.nNotFull - 1 : 0, 0, 'The truth value changes once'),
      ],
      warnings,
    };
  },
  benchmarks() {
    const out = [], h = n => 1 / (1 + Math.exp(-(n - 100) / 20));
    const r = soritesChain(10000, h, false, true, null);
    out.push(bench('Łukasiewicz chain from 10 000 grains to one', r.v, h(1), 'Telescoping sum: the bound equals the degree of heapness of one grain', 1e-8));
    out.push(bench('Degree of heapness at the midpoint', h(100), 0.5, 'Logistic function', 1e-12));
    out.push(bench('Least true conditional for a width of 20 grains', r.iMin, 1 - Math.tanh(1 / 80), 'Largest single-grain drop of the logistic function, tanh(1/4w)', 1e-4));
    const c = soritesChain(10000, n => (n >= 100 ? 1 : 0), false, true, null);
    out.push(bench('False conditionals for a sharp boundary', c.nNotFull, 1, 'The truth value changes exactly once', 1e-12));
    const t = soritesChain(10000, h, true, true, null);
    out.push(bench('Chain with full tolerance', t.v, h(10000), 'Nothing is lost along the chain', 1e-12));
    return out;
  },
  validation: [],
  diagram(v, a) {
    const pile = (cx, n, rows) => { let out = ''; for (let r = 0; r < rows; r++) for (let k = 0; k <= r && n > 0; k++, n--) out += S.circle(cx + (k - r / 2) * 9, 150 + r * 8, 4); return out; };
    const pts = Array.from({ length: 41 }, (_, i) => { const x = i / 40, y = a.bivalent ? (x >= 0.5 ? 1 : 0) : 1 / (1 + Math.exp(-(x - 0.5) * 12)); return [100 + 440 * x, 320 - 70 * y]; });
    return svg(`
      ${pile(110, 1, 1)} ${S.text(110, 215, '1 grain', 'd-text d-small')}
      ${pile(250, 6, 3)} ${S.text(250, 215, 'a few', 'd-text d-small')}
      ${pile(400, 21, 6)} ${S.text(400, 215, 'borderline', 'd-text d-small')}
      ${pile(540, 45, 9)} ${S.text(540, 235, 'heap', 'd-text d-small')}
      ${S.arrow(500, 120, 160, 120)} ${S.text(330, 110, 'remove one grain at a time', 'd-text d-small')}
      ${S.line(100, 320, 540, 320, 'd-dim')} ${S.poly(pts.map(p => [p[0].toFixed(1), p[1].toFixed(1)]), 'd-line d-hazard')}
      ${S.text(570, 255, a.bivalent ? 'sharp' : 'degree', 'd-text d-small')} ${S.text(320, 345, 'number of grains →', 'd-text d-small')}
      ${S.text(320, 40, a.tolerance ? 'Each step is taken to be fully truth-preserving' : 'Each step loses a little truth, or one step fails outright')}
    `);
  },
  logicPreset: {
    atoms: [{ k: 'H10000', text: '10 000 grains make a heap' }, { k: 'H1000', text: '1 000 grains make a heap' }, { k: 'H100', text: '100 grains make a heap' }, { k: 'H10', text: '10 grains make a heap' }, { k: 'H1', text: '1 grain makes a heap' }],
    premises: ['H10000', 'H10000 -> H1000', 'H1000 -> H100', 'H100 -> H10', 'H10 -> H1', '~H1'],
    conclusion: null,
  },
  philosophy: [
    'The sorites paradox challenges the assumption that every meaningful predicate divides the world sharply. If vague predicates have no boundaries, classical logic, which presupposes that each statement is true or false, seems not to apply to most of ordinary language; if they do have boundaries, it is mysterious what fixes them and why they cannot be known.',
    'Each response carries a cost. Epistemicism preserves logic by positing sharp cut-offs that no investigation could reveal. Supervaluationism preserves classical theorems while giving up the principle that a true disjunction has a true disjunct. Degree theories respect the gradual transition but replace one sharp boundary with precise numerical degrees, raising the problem of higher-order vagueness: where exactly does full truth end?',
    'The paradox matters outside philosophy wherever continuous quantities are sorted into categories — in law, medicine and classification generally — and it shows that long chains of individually negligible steps can carry a conclusion a long way from its premises.',
  ],
  experiment: {
    objective: 'Measure how people\'s judgements of "heap" change with the number of grains and whether the response depends on the direction of approach.',
    apparatus: ['A series of images or physical piles with the number of grains varied in small steps', 'A forced-choice or graded response task presented in ascending, descending and random order', 'Alternatively a numerical experiment computing the truth carried along the chain under different logics'],
    instruments: [{ name: 'Response recorder', measures: 'Yes/no judgement or rating on a scale from 0 to 1', range: '1–10 000 grains', resolution: 'One response per stimulus' }, { name: 'Psychometric function fit', measures: 'Midpoint and width of the transition', range: '—', resolution: 'Standard error from the fit' }],
    procedure: ['Present piles of varying size and record whether each is judged a heap.', 'Fit a logistic curve to the proportion of "heap" responses against the logarithm or the number of grains.', 'Compare the midpoints obtained in ascending and descending sequences.', 'Use the fitted midpoint and width as inputs and compute the truth lost along the chain.'],
    controls: ['Random presentation order, to remove sequence effects', 'A sharply defined predicate such as "more than 100 grains" as a comparison'],
    signatures: ['A graded transition with no agreed sharp boundary across or within participants', 'Hysteresis: the switch point depends on the direction of approach', 'Individually near-certain steps accumulating to a reversal of the judgement'],
    safety: [],
  },
  falsify: ['Empirically, a sharp and reproducible boundary in judgements shared by all competent speakers would count against treating "heap" as vague.', 'Within the degree-theoretic model, a chain whose derived truth under Łukasiewicz conjunction differed from the degree of heapness of the final number of grains would refute the telescoping identity.'],
  alternatives: [
    { name: 'Epistemicism', text: 'There is a precise number of grains at which a heap ceases to be one; we cannot know it. Classical logic is retained and one inductive premise is false.' },
    { name: 'Supervaluationism', text: 'A statement is true if true on every admissible way of making the predicate precise. The inductive premise is false on every sharpening, so it is false, although no particular step is the false one.' },
    { name: 'Degree theories (fuzzy logic)', text: 'Truth comes in degrees. Each conditional is slightly less than fully true and modus ponens transmits only as much truth as its premises jointly have. This is the account computed here.' },
    { name: 'Contextualism', text: 'The boundary shifts with the context of judgement, and in particular moves away from whichever pair of adjacent cases is under consideration, which explains why no step seems to make a difference.' },
    { name: 'Nihilism', text: 'Vague predicates apply to nothing: strictly there are no heaps. The first premise is rejected.' },
  ],
  limits: 'A single predicate ordered by one parameter, with a logistic membership function or a sharp threshold. The numerical degrees are a modelling choice; the qualitative result — that near-truth of every step does not secure near-truth of the conclusion — does not depend on them. Higher-order vagueness and supervaluationist semantics are not computed.',
  numerics: { method: 'Direct evaluation of the chain of conditionals, one step per grain', stability: 'Rounding error grows at most linearly with the number of steps and stays below 10⁻⁹ for a million grains' },
  extensions: ['Supervaluationist truth as the fraction of admissible sharpenings', 'Higher-order vagueness with a fuzzy boundary of the borderline region', 'Other t-norms and their effect on chain length', 'Forced-march versions and hysteresis in judgement'],
};

export default [montyHall, zenoAchilles, maxwellsDemon, prisonersDilemma, newcombProblem, liarParadox, shipOfTheseus, grandfatherParadox, laplaceDemonChaos, olbersParadox, birthdayProblem, bayesDiagnostic, stPetersburg, twoEnvelopes, simpsonsParadox, hilbertHotel, drakeFermi, soritesHeap];
