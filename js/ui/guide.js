// Plain-language guide to every panel: what it shows, how to read it and what can be done with it.
// A panel is matched by the start of its heading; the guide is attached under the heading when the panel appears.
import { toast } from './dom.js';

// heading (lower case, start of the text) → [what this shows, how to read it, what you can do]
const G = {
  // ------------------------------------------------------------------ home, prompt, library, live data
  'thought and imaginative experiments': ['Module 1: questions of the “what would happen if…” kind, from textbook physics to imagined laws of nature.', 'Each experiment is sorted into a class: I uses accepted physics, II stretches accepted physics to extreme conditions, III changes a law of nature on purpose.', 'Type the experiment in your own words and press the button; nothing needs to be in a special format.'],
  'scientific, engineering and industrial simulation': ['Module 2: calculations for real equipment and processes, with units, checks and exportable code.', 'Option A builds the answer from established equations. Option B looks for a new equation in your data.', 'Describe the system and give whatever numbers you have; anything missing is filled with a labelled default you can change.'],
  'reverse engineering studio': ['Works backwards: from measured results to the equations, inputs or shape that would produce them.', 'Use it when you have data or a drawing but not the model behind it.', 'Open it and upload a table, a drawing or a result file.'],
  'continue where you left off': ['Investigations saved on this device, most recent first.', 'Nothing here is stored on a server; clearing the browser’s site data removes it.', 'Tap one to reopen it exactly as you left it.'],
  'what makes a result trustworthy here': ['The checks every result passes before it is shown.', 'A tick means the check ran and passed; the wording says what was checked and what was not.', ''],
  'explore': ['Short cuts to the other parts of the app.', '', ''],
  'how your prompt is being read': ['A live preview of how your words are being interpreted, before anything is run.', 'It lists the model that will be used, the quantities found in your text and anything still missing. If the model is wrong, add a few words about the physics you mean.', 'Keep typing until the preview matches your intention, then start the investigation.'],
  'what you will get': ['The kinds of result this module produces.', '', ''],
  'accepted formats': ['File types that can be attached as evidence or data.', 'Tables become data series, drawings and meshes become geometry, documents are searched for numbers.', ''],
  'standard relations': ['A reference list of well-known formulas the app can apply directly when no full model fits.', 'Each entry shows the relation, the meaning of its symbols and the conditions under which it holds.', 'Mention the quantities of a relation in a prompt and it is used automatically.'],
  'integrated suites': ['Groups of models that share a subject and can be combined in one investigation.', '', 'Open a suite to see its models, or start any of them directly.'],
  'application domains with specialised outputs': ['Fields for which extra, field-specific results are produced.', '', ''],
  'conditions at a place': ['Present weather, sea and ground conditions for a location, fetched from public services.', 'Every figure carries a label saying where it came from and when it was measured.', 'Enter a place or use your position; the values can then be sent into an investigation as inputs.'],
  'space environment': ['Current solar and geomagnetic activity.', 'Higher index values mean a more disturbed space environment.', ''],
  'near-earth objects today': ['Asteroids passing close to the Earth today.', 'Miss distance is the closest approach; none of these is on a collision course unless stated.', ''],
  'earthquakes, past day': ['Earthquakes of magnitude 4.5 and above in the last 24 hours.', 'Magnitude is logarithmic: each whole step is about 32 times more energy.', ''],
  'open natural events': ['Ongoing natural events such as wildfires, storms and eruptions.', '', ''],
  'scientific literature': ['A search of open scholarly indexes.', 'Results are papers, not conclusions; open one to read the source.', 'Search for a topic to find references for an investigation.'],
  'all connected sources': ['Every outside data service the app can reach, and whether it answered just now.', 'A source that is unreachable does not stop the app; the affected value falls back to a labelled default.', ''],
  'install on this device': ['How to add the app to your home screen so it opens like a normal application.', '', ''],
  'offline and aeroplane mode': ['What works without a connection.', 'All calculation happens on the device, so only live data and the remote proof check need a connection.', ''],
  'resilience': ['How the app behaves when a host or a data source is down.', '', ''],
  'data source key': ['The meaning of the coloured labels attached to every input value.', 'The label says where a number came from: you, a live measurement, a reference table or a default.', 'Tap any label anywhere in the app to see its meaning.'],
  'language-model reading of prompts': ['An optional helper that reads a new prompt with a language model.', 'It decides only how the prompt is understood. The calculation, the checks and the proofs are done by the app itself, on this device.', 'Switch it on here or with the tick box under the prompt.'],
  'privacy and security': ['What is stored, where, and what leaves the device.', '', ''],
  'the workflow': ['The steps an investigation goes through, in order.', 'Each step is a tab in the investigation; you can move between them freely with the arrows at the bottom.', ''],
  'what "verified" does and does not mean': ['The exact scope of the word “verified” in this app.', 'It means the mathematics is consistent and was checked; it does not mean nature agrees. Agreement with nature is tested separately against measurements.', ''],
  'understanding the labels on inputs': ['The meaning of each label that appears next to a number.', '', ''],
  'keyboard': ['Keyboard short cuts.', '', ''],
  'keep data fresh on a schedule': ['How to have live data refreshed automatically.', '', ''],

  // ------------------------------------------------------------------ concept
  'headline results': ['The few numbers that answer the question, before any detail.', 'Each tile is one computed quantity with its unit. A pink “conditional” mark means the number depends on a hypothetical assumption.', 'Go to Simulation for the full set, the charts and the animations.'],
  'original prompt record': ['Your question exactly as you typed it, kept unaltered as the record of what was asked.', '', ''],
  'classification': ['Which kind of experiment this is and why it was sorted that way.', 'Class I uses accepted physics; class II pushes accepted physics to extremes; class III changes a law of nature on purpose. The class decides how cautiously results are labelled.', ''],
  'consolidated scenario': ['Your question restated as a precise scenario: what the system is, what is done to it and what is asked.', 'If this restatement is not what you meant, the rest will not be either.', 'Reword the prompt, or correct the inputs in the Inputs tab.'],
  'model selection': ['The mathematical model chosen to answer the question, and how well it fits your words.', 'The match score compares your wording with each model’s subject. A low score, or a note that a standard relation or a dimensional estimate was used instead, means the answer is rougher.', 'Pick another model from the list if a better one is offered.'],
  'fields involved': ['The branches of science and engineering this question touches.', '', ''],
  'research question and objectives': ['The question turned into something that can be tested, with the specific things to find out.', '', ''],
  'what is known, and what is not': ['The established background and the open points for this subject.', 'Established sources are standard references; disputed views are listed separately so they are not mistaken for settled results.', ''],
  'prior work and novelty': ['Whether this has been done before.', 'A match with a textbook result means the answer can be checked against it; no match means the result is new and unconfirmed.', ''],

  // ------------------------------------------------------------------ system
  'conceptual system': ['A schematic of the physical set-up.', 'Boxes and arrows are the parts and what passes between them. The drawing is illustrative, not to scale.', ''],
  'system overview': ['The parts of the system and how they act on one another.', '', ''],
  'entities, state variables and observables': ['The things in the model, the quantities that describe their state, and what could actually be measured.', 'State variables are what the equations evolve; observables are what an instrument would read; unknowns are what the calculation solves for.', ''],
  'preparation and external influences': ['How the system is set up at the start and what acts on it from outside.', 'Controls are the precautions that stop other effects from being mistaken for the one under study.', ''],

  // ------------------------------------------------------------------ inputs
  'input data register': ['Every number the calculation uses, with its unit and where it came from.', 'The coloured label is the source of the value: supplied by you, read from your prompt, measured live, taken from a reference table, or a default. Defaults are the ones to question first.', 'Change any value or its unit; everything downstream recalculates at once.'],
  'quantities read from your prompt': ['The numbers that were found in your text and what they were taken to mean.', 'If a number was attached to the wrong quantity, correct it in the register above.', ''],
  'location and environment': ['Conditions at a real place, used as inputs when the scenario has a location.', 'Values are measurements or climatological averages from public services, each labelled with its source.', 'Set a place to replace default surroundings with real ones.'],
  'evidence files': ['Files you have attached: data tables, drawings, documents.', 'Tables can be compared with the results; geometry can be measured; documents are searched for values.', 'Attach a file to validate the model against your own measurements.'],
  'reference literature for missing data': ['Where to look up values the app could not supply.', '', ''],

  // ------------------------------------------------------------------ foundations
  'foundational laws and principles': ['The laws of physics the model rests on.', 'These are accepted laws, not assumptions of this calculation. Each equation later on is traced back to one of them.', ''],
  'postulates and hypothetical laws': ['Anything assumed that is not accepted physics.', 'Everything that depends on a hypothetical law is marked “conditional” throughout: it is true if the postulate is, and not otherwise.', ''],
  'consistency assessment': ['A check that the assumptions do not contradict one another or the conservation laws.', 'A conflict listed here means some results cannot all be true together.', ''],
  'assumption register and what depends on each': ['Each simplifying assumption, and the results that would change if it were dropped.', 'An assumption with many dependants is one whose failure matters most.', 'Switch an assumption off in Alternative worlds to see the effect.'],
  'alternative frameworks': ['Other theories that could be used for the same problem.', 'They are listed so the choice of framework is visible, with the regime in which each one applies.', ''],
  'machine check by lean 4': ['An independent proof checker confirming the logical and algebraic steps.', 'A green result means a separate program, not this app, accepted the proof. “Stated condition” means the step holds only under a condition that is written out and not proved.', 'Needs a connection; the check runs by itself and takes a few seconds.'],

  // ------------------------------------------------------------------ equations
  'equation laboratory': ['A place to type your own equations and have them checked and solved.', 'Write each as left side = right side. Symbols are listed underneath so you can give each a unit.', 'Add an equation; it is verified immediately and, if it can be solved, simulated.'],
  'verification summary': ['How many equations passed each kind of check.', 'Verified means dimensionally consistent and mathematically well defined on the stated range. It says nothing yet about agreement with experiment.', ''],
  'derivation from first principles': ['The chain of steps from the basic laws to the working equations.', 'Read from top to bottom: each step names the law or approximation that justifies it.', ''],
  'governing equations': ['The equations that are actually solved, each with its checks.', 'The first label is the kind of equation (law, derived, closure, empirical, definition, hypothesis). The second is the outcome of verification. The list under each equation shows the individual checks: ✓ passed, ✕ failed, ◐ passed with a condition.', 'If an equation fails, a corrected form is proposed and can be adopted with one tap.'],
  'symbol register': ['Every symbol used, with its meaning, unit and physical dimension.', 'Dimensions are written in base quantities: M mass, L length, T time, Θ temperature, I current, N amount.', ''],
  'dimensional analysis': ['The independent dimensionless groups that govern the problem.', 'Two situations with the same values of these groups behave alike, whatever their size. The number of groups is the number of quantities minus the number of independent dimensions.', ''],
  'looking for a new relationship?': ['A pointer to the discovery tools, for when no known equation fits.', '', ''],

  // ------------------------------------------------------------------ discovery
  '1 · candidate law from dimensional analysis': ['A formula suggested purely by the units of the quantities involved.', 'It fixes the powers of each quantity but not the numerical constant in front, which must come from data.', 'Choose the quantity to explain and the ones it may depend on.'],
  '2 · candidate equations from data': ['Equations fitted to an uploaded table.', 'RMSE is the typical error of the fit; R² near 1 means the equation explains almost all the variation. The held-out error is measured on data the fit never saw, and is the one to trust.', 'Pick the columns, run the fit, and adopt a candidate to carry it into the equations.'],
  '3 · hypothesis catalogue and competing mechanisms': ['Rival explanations for the same observations.', 'Each comes with a prediction that would tell it apart from the others.', ''],
  '4 · novelty and prior art': ['Whether a candidate equation is already known.', 'A match with a known law is a confirmation, not a discovery.', ''],

  // ------------------------------------------------------------------ logic
  'formal proposition set': ['The argument broken into simple statements, each given a letter, with premises and a conclusion written using those letters.', 'A premise is something taken as given. The conclusion is the claim being tested. Connectives typed here: ~ not, & and, | or, -> if…then, <-> exactly when.', 'Edit a statement, a premise or the conclusion; the analysis below updates at once.'],
  'result': ['The verdict: whether the conclusion must be true whenever all the premises are.', 'Valid means there is no possible situation with true premises and a false conclusion. It does not mean the premises themselves are true. The formula line reads “premises ⊨ conclusion”: the premises force the conclusion.', ''],
  'the argument in plain words': ['A translation of every letter and formula back into ordinary sentences.', 'Use it to confirm the symbols say what you meant before trusting the verdict.', ''],
  'truth table and possible worlds': ['Every possible combination of true and false for the statements, and what the premises and conclusion come to in each.', 'Read one row at a time: the letters on the left are the situation, the P columns say which premises hold in it, the last column says whether the conclusion holds.', ''],
  'argument structure': ['A picture of which premises the conclusion rests on.', 'Follow the lines from the premise boxes down to the conclusion box; the key underneath explains the line styles.', ''],
  'philosophical and conceptual interpretation': ['What the result means beyond the symbols.', '', ''],
  'limits of this analysis': ['What this kind of logical analysis cannot do.', '', ''],

  // ------------------------------------------------------------------ experiment
  'objective and testability': ['What a real experiment would aim to show, and what result would prove the model wrong.', 'A model that no observation could refute is not being tested.', ''],
  'apparatus and configuration': ['The equipment a real test would need.', '', ''],
  'procedure': ['The steps of the experiment in order, with the comparison cases.', '', ''],
  'measurement system and uncertainty budget': ['What would be measured, with which instrument, and how accurately.', 'The budget adds up each source of error; the total is the smallest effect the experiment could detect.', ''],
  'safety and precautions': ['Hazards of carrying out the experiment for real.', '', ''],
  'test matrix': ['The list of runs to carry out, each with its settings.', 'Each row is one run; the columns are the settings varied between runs.', ''],
  'detectability': ['Whether the predicted effect is large enough to measure.', 'Each figure is how much a predicted quantity moves when its most influential input changes by one per cent. The effect can be detected only if that movement is larger than the smallest step the instrument can resolve.', ''],

  // ------------------------------------------------------------------ simulation
  'simulation status': ['Whether the calculation ran, how, and how long it took.', 'It names the numerical method and any warnings. “Computed” means the equations were solved with your inputs on this device.', 'Change an input and it runs again.'],
  'computed results': ['Every quantity the model calculated, with its value and unit.', 'Values are shown in the most readable unit. A pink “conditional” mark means the value depends on a hypothetical assumption.', 'Open a chart or animation below to see how the quantities vary.'],
  'conservation and consistency diagnostics': ['Checks that the solution obeys the conservation laws it should.', 'Each line is a balance, such as energy in against energy out, with the size of any mismatch. A small residual means the numbers are internally consistent.', ''],
  'parameter response': ['How one result changes as one input is varied, with everything else held fixed.', 'The input runs along the bottom and the result up the side. A flat line means that result does not depend on that input, which is common and correct: each result depends on only a few inputs. The note under the chart says in words what the curve does, shades any stretch where the result has no value and says why, and rings any point where one of the model’s own checks failed.', 'Pick the input. The list of results is then sorted into those that change, those that stay the same and those with no value to plot.'],
  'solution verification: refinement study': ['A test that the numerical answer does not depend on the resolution of the calculation.', 'The model is run at three resolutions. If the answers settle, the observed order of accuracy shows how quickly the error shrinks and the grid-convergence index estimates the error that remains.', ''],
  'generated source code': ['The same calculation written as a stand-alone program.', 'The C++, Python and MATLAB versions reproduce the numbers shown here and can be run outside the app.', 'Copy or download the language you need.'],

  // ------------------------------------------------------------------ visualisation
  'results': ['Charts, maps and animations of the solution.', 'Each figure has its own title, axes with units, and buttons to save it.', ''],
  'schematic': ['A labelled drawing of the set-up with the main dimensions and quantities.', 'Illustrative, not to scale.', ''],
  'uploaded geometry': ['The shape read from a file you attached.', '', ''],
  'data tables': ['The plotted numbers in table form.', '', 'Download them as CSV from the chart buttons or from Export.'],

  // ------------------------------------------------------------------ worlds
  'worlds': ['Alternative versions of the scenario, each with different assumptions or laws.', 'The baseline is the scenario as asked. Each further world changes something, so that the effect of the change can be seen.', 'Create a world, change an assumption or a constant in it, and compare.'],
  'editable assumption catalogue': ['The assumptions and constants of the selected world.', 'Switching an assumption off, or changing a constant, changes the equations that depend on it.', 'Edit a value; the world recalculates.'],
  'which conclusions depend on which assumptions': ['A map from each result to the assumptions it relies on.', 'A result that depends on a questionable assumption is only as reliable as that assumption.', ''],
  'side-by-side comparison': ['Two worlds compared: what was changed and what came out differently.', 'Rows that differ are the consequences of the change; identical rows are unaffected by it.', ''],
  'challenge the explanation': ['A place to record objections and see how the model answers them.', '', 'Write an objection; it is kept with the investigation.'],
  'versions': ['Saved snapshots of this investigation.', '', 'Save a version before a large change so you can return to it.'],

  // ------------------------------------------------------------------ evaluation
  'scientific readiness': ['A five-step scale of how far this result can be trusted.', 'The highlighted step is the present level and the text says why it is not higher. Higher levels need a completed run, numerical checks, and finally agreement with measurements.', ''],
  'scientific gates': ['The individual tests a result has to pass.', 'Green passed, red failed, amber conditional (passed under a stated condition), grey still open. The line under each gate says what was tested and what was found.', ''],
  'numerical verification against exact solutions': ['The solver compared with cases whose exact answer is known.', 'The error column is the difference between the two; a small value shows the numerical method works on this kind of problem.', ''],
  'comparison with published measurements': ['The model compared with measured values from the literature.', 'Each row gives the published figure, the model’s figure and the difference. This, not verification, is what shows agreement with nature.', ''],
  'validate against your own data': ['The model compared with a table you upload.', 'The chart overlays your points on the model’s curve; the error figures summarise the gap.', 'Attach a data table and choose the columns.'],
  'sensitivity': ['Which inputs matter most.', 'Each bar is the percentage change in the result for a one per cent change in that input. Long bars are the inputs worth measuring carefully.', ''],
  'uncertainty': ['The spread in the result caused by uncertainty in the inputs.', 'Each input is varied at random within its uncertainty and the model solved again for every sample; the spread of the answers is the uncertainty of the result. Values supplied by the software are given a wider uncertainty than yours.', 'Press the button to run it.'],
  'interpretation': ['What the numbers mean in words.', '', ''],
  'further evidence required': ['What would have to be measured or shown before the result could be relied on.', '', ''],
  'extensions': ['Ways the study could be taken further.', '', ''],

  // ------------------------------------------------------------------ optimisation
  'optimisation': ['A search for the input values that give the best result.', 'The objective is the quantity made as small or as large as possible. Only the inputs you allow may change, each within its permitted range, and a limit on another result can be imposed.', 'Choose the objective, the free inputs and any limit, then run the search.'],
  'operational recommendations': ['Practical advice that follows from the results.', '', ''],
  'not activated for this scenario': ['Outputs that do not apply to this scenario.', 'They are listed so that it is clear they were considered and left out on purpose.', ''],

  // ------------------------------------------------------------------ safety and readiness
  'hazard identification and mitigation': ['What could go wrong if this were built or tested, and how to reduce the risk.', 'This is a prompt for a proper safety review, not a substitute for one.', ''],
  'standards that typically apply': ['Codes and standards usually relevant to this kind of equipment.', 'Check the current edition and local regulations before relying on any of them.', ''],
  'margins in the present results': ['The computed quantities that express a margin, safety factor, ratio or limit, together with any warnings the model raised.', 'Compare each value with the limit named in its title. If the model reports no explicit margin, the panel says so.', ''],
  'qualification path': ['The steps from calculation to an approved design.', '', ''],
  'prototype and manufacture': ['Considerations for building the thing.', '', ''],
  'integrity of this computation': ['Where the calculation ran and what record of it is kept.', '', ''],

  // ------------------------------------------------------------------ export
  'complete package': ['Everything about this investigation in one download.', 'The archive holds the reports, equations, code, data and figures listed underneath.', 'Download it to keep or share the whole study.'],
  'reports': ['Written reports of the investigation.', '', 'Choose a format to download.'],
  'mathematics and code': ['The equations and the generated programs as files.', '', ''],
  'data': ['The numbers as files: inputs, results and plotted series.', '', ''],
  'coverage of the output catalogue': ['How many of the possible outputs this investigation produced.', 'Outputs are only produced when the scenario calls for them; a low count is not a fault.', ''],
  'data sources used': ['Where every outside value in this investigation came from.', '', ''],
  'audit trail': ['A time-stamped log of every change made to this investigation.', '', ''],

  // ------------------------------------------------------------------ reverse engineering
  'reverse engineering': ['Working backwards from results to causes.', 'Three routes are offered: A finds equations in data, B finds the inputs of a known model, C recovers a shape.', ''],
  'a · reconstruct equations from the data': ['Finds an equation that reproduces an uploaded table.', 'The error figures say how well the equation reproduces the data; a good fit is a candidate, not a proof.', 'Choose the columns and run.'],
  'b · reconstruct the inputs of': ['Finds the input values that make a model reproduce measured results.', 'Each recovered input comes with an uncertainty. Strongly correlated inputs cannot be separated by this data: only a combination of them is determined.', 'Select which inputs are unknown and supply the measured values.'],
  'c · reconstruct geometry': ['Recovers dimensions and shape from a drawing, mesh or image.', '', ''],
  'classification of what has been reconstructed': ['The meaning of the labels attached to reconstructed values.', 'The label says how a value was obtained, from supplied by you down to unresolved, so a reconstructed number is never mistaken for a measured one.', ''],
};

// figures are titled by what they plot, so they are explained by their kind
const FIG = [
  ['canvas[data-series]', ['A line chart of one computed quantity against another.', 'The axis labels give each quantity and its unit. Where several lines are drawn, the legend names them.', 'PNG saves the picture; CSV saves the numbers behind it.']],
  ['canvas[data-field]', ['A colour map of a quantity over a region.', 'Position on the map is position in space; the colour bar at the side converts colour to value.', 'PNG saves the picture.']],
  ['canvas[data-anim]', ['An animation of the solution changing in time.', 'The read-out beside the slider is the simulated time, not the playing time.', 'Press Play, drag the slider to any instant, or record a video.']],
  ['canvas[data-path]', ['A three-dimensional view of a path or shape.', 'The axes are positions in space.', 'Drag to rotate; scroll or pinch to zoom.']],
];

const keys = Object.keys(G).sort((a, b) => b.length - a.length);
const esc = s => s.replace(/&/g, '&amp;').replace(/</g, '&lt;');
// heading text without the labels and buttons that sit inside it
const own = h => [...h.childNodes].filter(n => n.nodeType === 3 || (n.nodeType === 1 && !n.matches('.chip,button,.btn'))).map(n => n.textContent).join('').replace(/\s+/g, ' ').trim().toLowerCase();
function box([what, read, act]) {
  const d = document.createElement('details'); d.className = 'guide';
  d.innerHTML = `<summary><span><b>What this shows.</b> ${esc(what)}</span></summary>${read || act ? `<div class="body">${read ? `<p><b>How to read it.</b> ${esc(read)}</p>` : ''}${act ? `<p><b>What you can do.</b> ${esc(act)}</p>` : ''}</div>` : ''}`;
  if (!read && !act) d.classList.add('flat');
  return d;
}
function attach(h) {
  if (h.dataset.g) return; h.dataset.g = '1';
  if (h.closest('.guide,.modal,a')) return;
  const text = own(h), k = keys.find(x => text.startsWith(x));
  let g = k ? G[k] : null;
  const card = h.closest('.card');
  if (!g && card && h.tagName === 'H3') { const f = FIG.find(([sel]) => card.querySelector(sel)); if (f) g = f[1]; }
  if (!g) return;
  const anchor = h.parentElement.matches('.row') ? h.parentElement : h;
  anchor.after(box(g));
}
const scan = root => { if (root.matches && root.matches('h2,h3')) attach(root); root.querySelectorAll && root.querySelectorAll('h2,h3').forEach(attach); };

/**
 * Keep every value inside its tile: typeset numbers cannot wrap, so one that is wider than its box is set smaller until
 * it fits, and plain-text values that are still too long are allowed to wrap onto further lines.
 */
function fitTile(v) {
  v.style.fontSize = ''; v.classList.remove('wraps');
  const box = v.parentElement, room = box.clientWidth - parseFloat(getComputedStyle(box).paddingLeft) - parseFloat(getComputedStyle(box).paddingRight); if (room <= 0) return;
  const base = parseFloat(getComputedStyle(v).fontSize); let size = base;
  while (v.scrollWidth > room + 0.5 && size > base * 0.55) { size -= 0.5; v.style.fontSize = `${size}px`; }
  if (v.scrollWidth > room + 0.5) { v.classList.add('wraps'); v.style.fontSize = `${base * 0.75}px`; }
}
const fitAll = root => root.querySelectorAll && root.querySelectorAll('.stat .v').forEach(fitTile);

/** Explain every panel under root now, and every panel added to it later. */
export function watch(root) {
  let queue = new Set(), pending = false;
  const flush = () => { pending = false; const q = [...queue]; queue = new Set(); q.forEach(n => { if (n.isConnected) scan(n); }); clearTimeout(fitT); fitT = setTimeout(() => fitAll(root), 120); };
  let fitT; window.addEventListener('resize', () => { clearTimeout(fitT); fitT = setTimeout(() => fitAll(root), 150); });
  new MutationObserver(list => { for (const r of list) r.addedNodes.forEach(n => { if (n.nodeType === 1 && !n.classList.contains('guide')) queue.add(n); }); if (queue.size && !pending) { pending = true; requestAnimationFrame(flush); } }).observe(root, { childList: true, subtree: true });
  scan(root); setTimeout(() => fitAll(root), 200);
  // a label is a description, not a control: tapping one says what it means
  document.addEventListener('click', ev => { const c = ev.target.closest('.chip[title],th[title]'); if (c && !ev.target.closest('button,a,summary')) toast(c.title, 5200); });
}
