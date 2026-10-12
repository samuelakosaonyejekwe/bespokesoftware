// Report, code and data exporters. One structured report is built per investigation and then
// rendered to Markdown, HTML (print-to-PDF), LaTeX and DOCX. Code generators emit Python,
// MATLAB/Octave and C++ for every explicit relation, with the in-app results embedded for cross-checking.
import * as E from './expr.js';
import { fmt, fromSI, tryUnit } from './units.js';
import { writeZip } from './zip.js';
import { LAWS } from '../data/domains.js';
import { CLASS_NAME } from '../engine/prompt.js';
import { PROV, READINESS } from '../engine/core.js';

const val = s => (s.text ? s.text : `${fmt(s.show && tryUnit(s.show) ? fromSI(s.value, s.show) : s.value, 5)} ${s.show || (s.unit === '1' ? '' : s.unit)}`.trim());
const iso = ts => new Date(ts).toISOString().replace('T', ' ').slice(0, 16) + ' UTC';
export const slug = s => String(s).toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '').slice(0, 48) || 'investigation';

/** Structured report: [{h, blocks: [{p}|{eq, text}|{table:{head, rows}}|{list}|{note}|{code, lang}]}] */
export function buildReport(inv, c, extra = {}) {
  const m = c.model, S = [];
  const sec = (h, blocks) => { const b = blocks.filter(Boolean); if (b.length) S.push({ h, blocks: b }); };
  sec('Record', [
    { table: { head: ['Item', 'Value'], rows: [['Title', inv.title], ['Module', inv.module === 1 ? 'Module 1 — thought and imaginative experiments' : 'Module 2 — scientific, engineering and industrial simulation'], ['Operating option', inv.mode === 'B' ? 'Novel equation discovery' : inv.mode.startsWith('re') ? 'Reverse engineering' : 'First-principles model generation'], ['Experiment class', inv.klass.tags.map(k => `Class ${k} — ${CLASS_NAME[k]}`).join('; ')], ['Scientific readiness', `${c.readiness.level + 1} of 5 — ${c.readiness.label}`], ['World', (inv.worlds.find(w => w.id === c.worldId) || {}).name], ['Investigation ID', inv.id], ['Generated', iso(Date.now())]] } },
    { p: 'Original prompt (preserved verbatim):' }, { note: inv.prompt },
  ]);
  if (m) sec('Scenario and scientific background', [{ p: m.summary }, ...[].concat(m.background || []).map(p => ({ p })), m.phenomena ? { p: `Physical mechanisms involved: ${m.phenomena.join('; ')}.` } : null, m.limits ? { p: `Validity envelope: ${m.limits}` } : null]);
  else sec('Scenario', [{ p: 'No computable model from the library was matched to this prompt. The sections below record what could be established from the prompt alone, and what further information is needed.' }]);
  sec('Foundational laws and principles', [{ table: { head: ['Law', 'Statement'], rows: c.generic.laws.map(k => [LAWS[k].name, LAWS[k].text]) } }]);
  if (c.inputs.length) sec('Input data register', [
    { p: 'Every input is labelled with its origin. Software-supplied values are reference values adopted because none was given; they are not measurements.' },
    { table: { head: ['Symbol', 'Quantity', 'Value', 'Unit', 'Origin', 'Basis'], rows: c.inputs.map(i => [i.sym, i.name, fmt(i.value, 6), i.unit, PROV[i.prov].label, i.note || '']) } },
  ]);
  if (m && (m.assumptions || []).length) sec('Assumptions', [{ table: { head: ['Assumption', 'In force', 'Rationale', 'If removed'], rows: m.assumptions.map(a => [a.text, c.a[a.id] ? 'Yes' : 'No', a.why || '', a.alt || '']) } }]);
  if (c.derivation && c.derivation.length) sec('Derivation from first principles', c.derivation.flatMap((d, i) => [{ p: `${i + 1}. ${d.text}` }, d.tex ? { eq: d.tex } : null]));
  if (c.equations.length) sec('Governing equations', [
    ...c.verification.records.flatMap(r => [{ eq: r.tex || `${r.lhs} = ${r.rhs}`, text: `${r.lhs} = ${r.rhs}`, label: r.name }, { p: `${r.name} — ${(c.equations.find(q => q.id === r.id) || {}).kind}; origin: ${(c.equations.find(q => q.id === r.id) || {}).origin || 'stated in the model'}. Verification: ${r.status}.` }]),
    { p: c.verification.closure.text },
  ]);
  if (c.verification) sec('Mathematical verification', [
    { table: { head: ['Equation', 'Check', 'Outcome', 'Detail'], rows: c.verification.records.flatMap(r => r.steps.map(s => [r.name, s.check, s.ok === true ? 'Established' : s.ok === false ? 'Failed' : 'Conditional', s.text])) } },
    ...c.verification.records.filter(r => r.regularised).map(r => ({ p: `Regularised form of “${r.name}”: ${r.regularised.lhs} = ${r.regularised.rhs}. ${r.regularised.text}` })),
  ]);
  if (c.logic) sec('Logical analysis', [
    { table: { head: ['', 'Formula'], rows: [...inv.logic.premises.map((p, i) => [`Premise ${i + 1}`, p]), ...(inv.logic.conclusion ? [['Conclusion', inv.logic.conclusion]] : [])] } },
    inv.logic.atoms && inv.logic.atoms.length ? { table: { head: ['Symbol', 'Proposition'], rows: inv.logic.atoms.map(a => [a.k, a.text]) } } : null,
    ...c.logic.lines.map(p => ({ p })),
  ]);
  if (c.result.status === 'computed') {
    sec('Computed results', [
      { table: { head: ['Quantity', 'Symbol', 'Value'], rows: c.result.scalars.map(s => [s.name, s.sym, val(s) + (s.status === 'hypothetical' ? ' (conditional on a hypothetical closure)' : '')]) } },
      ...c.result.warnings.map(w => ({ note: w })),
      c.result.checks.length ? { table: { head: ['Consistency check', 'Residual', 'Tolerance', 'Outcome'], rows: c.result.checks.map(k => [k.name, fmt(k.value, 3), fmt(k.tol, 3), k.pass ? 'Pass' : 'Fail']) } } : null,
    ]);
  } else sec('Computed results', [{ note: `Not computed: ${c.result.error || 'insufficient information'}` }]);
  if (c.benchmarks.length) sec('Numerical verification against exact solutions', [{ table: { head: ['Benchmark', 'Computed', 'Exact', 'Relative difference', 'Outcome', 'Source'], rows: c.benchmarks.map(b => [b.name, fmt(b.got, 6), fmt(b.expected, 6), fmt(b.rel, 2), b.pass ? 'Pass' : 'Fail', b.ref]) } }]);
  if (c.validation.length) sec('Comparison with published measurements', c.validation.flatMap(v => [{ p: `${v.name}. Source: ${v.ref}.${v.note ? ' ' + v.note : ''}` }, { table: { head: ['Case', 'Observed', 'Predicted', 'Difference', 'Within 2σ'], rows: v.cases.map(k => [k.label, `${fmt(k.observed, 5)}${k.sigma ? ' ± ' + fmt(k.sigma, 2) : ''}`, fmt(k.predicted, 5), `${fmt(k.rel * 100, 3)} %`, k.pass ? 'Yes' : 'No']) } }]));
  sec('Scientific gates', [{ table: { head: ['Gate', 'Status', 'Evidence'], rows: c.gates.map(g => [`${g.id} — ${g.name}`, { pass: 'Passed', fail: 'Failed', conditional: 'Conditional', open: 'Open' }[g.status], g.text]) } }]);
  sec('Scientific readiness', [{ p: `Level ${c.readiness.level + 1} of 5: ${c.readiness.label}. The scale is: ${READINESS.map((r, i) => `${i + 1} ${r}`).join('; ')}.` }, { list: c.readiness.why }]);
  if (extra.sensitivity) sec('Sensitivity', [{ p: 'Normalised sensitivities (percentage change in the output per one per cent change in the input).' }, { table: { head: ['Input', ...extra.sensitivity.outputs.slice(0, 5).map(o => o.sym)], rows: extra.sensitivity.rows.map(r => [r.name, ...extra.sensitivity.outputs.slice(0, 5).map(o => fmt(r.s[o.sym], 3))]) } }]);
  if (extra.uncertainty) sec('Uncertainty', [{ p: `${extra.uncertainty.n} Latin-hypercube samples of the uncertain inputs.` }, { table: { head: ['Quantity', 'Median', '5th percentile', '95th percentile'], rows: extra.uncertainty.stats.map(s => [s.name, fmt(s.p50, 5), fmt(s.p05, 5), fmt(s.p95, 5)]) } }]);
  if (extra.assumptionMap) sec('Dependence of conclusions on assumptions', [{ table: { head: ['Assumption removed', 'Largest change', 'Conclusions affected', 'Equations changed'], rows: extra.assumptionMap.rows.map(r => [r.text, `${fmt(r.maxRel * 100, 3)} %`, r.dependents.join('; ') || 'none', r.changedEq.join('; ') || 'none']) } }, { p: `Robust to every single assumption change (< 1 %): ${extra.assumptionMap.robust.join('; ') || 'none'}.` }]);
  if (extra.worlds && extra.worlds.worlds.length > 1) sec('Alternative worlds compared', [{ table: { head: ['Quantity', ...extra.worlds.worlds.map(w => w.name)], rows: extra.worlds.rows.map(r => [r.name, ...r.cells.map(x => (x ? val(x) : '—'))]) } }]);
  if (m && m.experiment) sec('Experimental design', [{ p: m.experiment.objective }, { p: 'Apparatus:' }, { list: m.experiment.apparatus || [] }, (m.experiment.instruments || []).length ? { table: { head: ['Instrument', 'Measures', 'Range', 'Resolution'], rows: m.experiment.instruments.map(i => [i.name, i.measures, i.range, i.resolution]) } } : null, { p: 'Procedure:' }, { list: m.experiment.procedure || [] }, { p: 'Controls:' }, { list: m.experiment.controls || [] }, { p: 'Expected signatures:' }, { list: m.experiment.signatures || [] }, (m.experiment.safety || []).length ? { p: 'Safety:' } : null, { list: m.experiment.safety || [] }]);
  if (m && m.falsify) sec('Falsification criteria', [{ list: m.falsify }]);
  if (m && m.alternatives) sec('Competing explanations', [{ list: m.alternatives.map(a => `${a.name}: ${a.text}`) }]);
  if (m && m.hazards) sec('Hazards', [{ table: { head: ['Hazard', 'Cause', 'Mitigation'], rows: m.hazards.map(h => [h.hazard, h.cause, h.mitigation]) } }, m.standards ? { p: `Standards that typically apply (identification only; no compliance is claimed): ${m.standards.join('; ')}.` } : null]);
  if (inv.challenges.length) sec('Challenges raised and responses', inv.challenges.flatMap(q => [{ p: `Challenge: ${q.text}` }, { p: `Response: ${q.response}` }]));
  if (inv.uploads.length) sec('Evidence files', [{ table: { head: ['File', 'Size', 'SHA-256', 'Reading'], rows: inv.uploads.map(u => [u.name, `${(u.size / 1024).toFixed(1)} kB`, u.sha256 || '', u.summary]) } }]);
  if (m && m.refs) sec('References', [{ list: m.refs }]);
  sec('Limitations of this report', [{ list: ['Numerical convergence and internal consistency do not show that a device works or that a hypothesis is true.', 'Software-supplied inputs are reference values, not measurements of your system.', 'Engineering release requires recognised standards, competent review and measured qualification.', ...(m && (m.hypothetical || inv.klass.primary === 'III') ? ['This investigation rests on a hypothetical law. Its conclusions are conditional on that law.'] : [])] }]);
  sec('Audit trail', [{ table: { head: ['Time', 'Action'], rows: inv.audit.slice(-60).map(a => [iso(a.ts), a.action]) } }]);
  return { title: inv.title, sections: S };
}

const mdEsc = s => String(s ?? '').replace(/\|/g, '\\|').replace(/\n/g, ' ');
export function toMarkdown(rep) {
  let o = `# ${rep.title}\n\n`;
  for (const s of rep.sections) {
    o += `## ${s.h}\n\n`;
    for (const b of s.blocks) {
      if (b.p) o += `${b.p}\n\n`; else if (b.note) o += `> ${String(b.note).replace(/\n/g, '\n> ')}\n\n`;
      else if (b.eq) o += `$$${b.eq}$$\n\n`; else if (b.list) o += b.list.map(x => `- ${x}`).join('\n') + '\n\n';
      else if (b.code) o += '```' + (b.lang || '') + '\n' + b.code + '\n```\n\n';
      else if (b.table) o += `| ${b.table.head.map(mdEsc).join(' | ')} |\n| ${b.table.head.map(() => '---').join(' | ')} |\n${b.table.rows.map(r => `| ${r.map(mdEsc).join(' | ')} |`).join('\n')}\n\n`;
    }
  }
  return o;
}
const hEsc = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
/** Standalone HTML; `renderTex(tex)` may supply pre-rendered math markup. */
export function toHtml(rep, renderTex, figures = []) {
  let o = `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>${hEsc(rep.title)}</title><meta name="viewport" content="width=device-width,initial-scale=1"><style>body{font:15px/1.55 Georgia,'Times New Roman',serif;max-width:920px;margin:2rem auto;padding:0 1.2rem;color:#111}h1{font-size:1.7rem}h2{font-size:1.2rem;margin-top:2rem;border-bottom:1px solid #bbb;padding-bottom:.2rem}table{border-collapse:collapse;width:100%;font-size:.86rem;margin:.6rem 0}th,td{border:1px solid #bbb;padding:.3rem .45rem;text-align:left;vertical-align:top}th{background:#f1f1f1}blockquote{border-left:3px solid #999;margin:.6rem 0;padding:.2rem .9rem;color:#333;background:#f8f8f8}.eq{text-align:center;margin:.8rem 0;overflow-x:auto}figure{margin:1rem 0;text-align:center}figure img{max-width:100%}figcaption{font-size:.85rem;color:#444}@media print{h2{break-after:avoid}table,figure{break-inside:avoid}}</style></head><body><h1>${hEsc(rep.title)}</h1>`;
  for (const s of rep.sections) {
    o += `<h2>${hEsc(s.h)}</h2>`;
    for (const b of s.blocks) {
      if (b.p) o += `<p>${hEsc(b.p)}</p>`; else if (b.note) o += `<blockquote>${hEsc(b.note)}</blockquote>`;
      else if (b.eq) o += `<div class="eq">${renderTex ? renderTex(b.eq) : `<code>${hEsc(b.text || b.eq)}</code>`}</div>`;
      else if (b.list) o += `<ul>${b.list.map(x => `<li>${hEsc(x)}</li>`).join('')}</ul>`;
      else if (b.code) o += `<pre>${hEsc(b.code)}</pre>`;
      else if (b.table) o += `<table><thead><tr>${b.table.head.map(h => `<th>${hEsc(h)}</th>`).join('')}</tr></thead><tbody>${b.table.rows.map(r => `<tr>${r.map(x => `<td>${hEsc(x)}</td>`).join('')}</tr>`).join('')}</tbody></table>`;
    }
    if (s.h === 'Computed results') figures.forEach(f => { o += `<figure><img src="${f.src}" alt="${hEsc(f.caption)}"><figcaption>${hEsc(f.caption)}</figcaption></figure>`; });
  }
  return o + '</body></html>';
}
const tEsc = s => String(s ?? '').replace(/\\/g, '\\textbackslash{}').replace(/([&%$#_{}])/g, '\\$1').replace(/~/g, '\\textasciitilde{}').replace(/\^/g, '\\textasciicircum{}').replace(/[−–]/g, '--').replace(/×/g, '$\\times$').replace(/°/g, '$^\\circ$').replace(/≤/g, '$\\le$').replace(/≥/g, '$\\ge$').replace(/[σ]/g, '$\\sigma$').replace(/[µμ]/g, '$\\mu$').replace(/[²]/g, '$^2$').replace(/[³]/g, '$^3$').replace(/[→]/g, '$\\rightarrow$').replace(/[¬]/g, '$\\lnot$').replace(/[∧]/g, '$\\land$').replace(/[∨]/g, '$\\lor$').replace(/[↔]/g, '$\\leftrightarrow$').replace(/[≠]/g, '$\\ne$').replace(/[≈]/g, '$\\approx$').replace(/[∞]/g, '$\\infty$').replace(/[√]/g, '$\\surd$').replace(/[π]/g, '$\\pi$').replace(/[ε]/g, '$\\varepsilon$').replace(/[ρ]/g, '$\\rho$').replace(/[θ]/g, '$\\theta$').replace(/[τ]/g, '$\\tau$').replace(/[λ]/g, '$\\lambda$').replace(/[Δ]/g, '$\\Delta$').replace(/[ℓ]/g, '$\\ell$').replace(/[“”]/g, "''").replace(/[‘’]/g, "'").replace(/[⁰¹⁴-⁹⁻]/g, '').replace(/[^\x00-\x7F]/g, c => ({ 'é': "\\'e", 'ö': '\\"o', 'ü': '\\"u', 'ä': '\\"a', 'ï': '\\"i', 'Å': '\\AA{}', 'ø': '\\o{}', 'ł': '\\l{}', '—': '---', '…': '\\ldots{}', '·': '$\\cdot$', '½': '$\\tfrac12$', '±': '$\\pm$', '≪': '$\\ll$', '≫': '$\\gg$', '∝': '$\\propto$', '∇': '$\\nabla$', '∂': '$\\partial$', '∫': '$\\int$', 'Σ': '$\\Sigma$', 'Π': '$\\Pi$', 'Ω': '$\\Omega$', 'ω': '$\\omega$', 'α': '$\\alpha$', 'β': '$\\beta$', 'γ': '$\\gamma$', 'δ': '$\\delta$', 'κ': '$\\kappa$', 'ν': '$\\nu$', 'φ': '$\\varphi$', 'ψ': '$\\psi$', 'η': '$\\eta$', 'ξ': '$\\xi$', 'ζ': '$\\zeta$', 'χ': '$\\chi$', 'Γ': '$\\Gamma$', 'Λ': '$\\Lambda$', 'Φ': '$\\Phi$', 'Ψ': '$\\Psi$', 'Θ': '$\\Theta$', 'ħ': '$\\hbar$', '⊨': '$\\models$', '⊤': '$\\top$', '⊥': '$\\bot$', '⊕': '$\\oplus$', '′': "'", '₀': '$_0$', '₁': '$_1$', '₂': '$_2$', '₃': '$_3$' }[c] ?? '?'));
export function toLatex(rep) {
  let o = `\\documentclass[11pt,a4paper]{article}\n\\usepackage[margin=25mm]{geometry}\n\\usepackage{amsmath,amssymb,longtable,booktabs,array}\n\\usepackage[T1]{fontenc}\n\\setlength{\\parindent}{0pt}\\setlength{\\parskip}{6pt}\n\\title{${tEsc(rep.title)}}\n\\date{\\today}\n\\begin{document}\n\\maketitle\n\\tableofcontents\n\\newpage\n`;
  for (const s of rep.sections) {
    o += `\\section{${tEsc(s.h)}}\n`;
    for (const b of s.blocks) {
      if (b.p) o += `${tEsc(b.p)}\n\n`; else if (b.note) o += `\\begin{quote}${tEsc(b.note)}\\end{quote}\n`;
      else if (b.eq) o += `\\begin{equation}\n${b.eq}\n\\end{equation}\n`;
      else if (b.list && b.list.length) o += `\\begin{itemize}\n${b.list.map(x => `\\item ${tEsc(x)}`).join('\n')}\n\\end{itemize}\n`;
      else if (b.code) o += `\\begin{verbatim}\n${b.code}\n\\end{verbatim}\n`;
      else if (b.table) { const n = b.table.head.length, w = (0.94 / n).toFixed(3); o += `{\\footnotesize\\begin{longtable}{${`>{\\raggedright\\arraybackslash}p{${w}\\linewidth}`.repeat(n)}}\n\\toprule\n${b.table.head.map(h => `\\textbf{${tEsc(h)}}`).join(' & ')}\\\\\n\\midrule\n\\endhead\n${b.table.rows.map(r => r.map(tEsc).join(' & ') + '\\\\').join('\n')}\n\\bottomrule\n\\end{longtable}}\n`; }
    }
  }
  return o + '\\end{document}\n';
}
const xEsc = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/[\x00-\x08\x0B\x0C\x0E-\x1F]/g, '');
/** Minimal but valid WordprocessingML document. */
export function toDocx(rep) {
  const run = (t, o = {}) => `<w:r>${o.b || o.i || o.mono || o.size ? `<w:rPr>${o.b ? '<w:b/>' : ''}${o.i ? '<w:i/>' : ''}${o.mono ? '<w:rFonts w:ascii="Consolas" w:hAnsi="Consolas"/>' : ''}${o.size ? `<w:sz w:val="${o.size}"/>` : ''}</w:rPr>` : ''}<w:t xml:space="preserve">${xEsc(t)}</w:t></w:r>`;
  const para = (inner, style) => `<w:p>${style ? `<w:pPr><w:pStyle w:val="${style}"/></w:pPr>` : ''}${inner}</w:p>`;
  let body = para(run(rep.title), 'Title');
  for (const s of rep.sections) {
    body += para(run(s.h), 'Heading1');
    for (const b of s.blocks) {
      if (b.p) body += para(run(b.p)); else if (b.note) body += para(run(b.note, { i: true }));
      else if (b.eq) body += `<w:p><w:pPr><w:jc w:val="center"/></w:pPr>${run(b.text || b.eq, { mono: true })}</w:p>`;
      else if (b.list) body += b.list.map(x => para(run('•  ' + x))).join('');
      else if (b.code) body += b.code.split('\n').map(l => para(run(l, { mono: true, size: 18 }))).join('');
      else if (b.table) {
        const cell = (t, head) => `<w:tc><w:tcPr><w:tcW w:w="0" w:type="auto"/>${head ? '<w:shd w:val="clear" w:color="auto" w:fill="E7E6E6"/>' : ''}</w:tcPr>${para(run(t, { b: head, size: 18 }))}</w:tc>`;
        body += `<w:tbl><w:tblPr><w:tblW w:w="5000" w:type="pct"/><w:tblBorders>${['top', 'left', 'bottom', 'right', 'insideH', 'insideV'].map(k => `<w:${k} w:val="single" w:sz="4" w:space="0" w:color="999999"/>`).join('')}</w:tblBorders></w:tblPr><w:tr>${b.table.head.map(h => cell(h, true)).join('')}</w:tr>${b.table.rows.map(r => `<w:tr>${r.map(x => cell(x)).join('')}</w:tr>`).join('')}</w:tbl>${para('')}`;
      }
    }
  }
  const W = 'xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"';
  const doc = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:document ${W}><w:body>${body}<w:sectPr><w:pgSz w:w="11906" w:h="16838"/><w:pgMar w:top="1300" w:right="1200" w:bottom="1300" w:left="1200" w:header="708" w:footer="708" w:gutter="0"/></w:sectPr></w:body></w:document>`;
  const styles = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:styles ${W}><w:docDefaults><w:rPrDefault><w:rPr><w:rFonts w:ascii="Calibri" w:hAnsi="Calibri"/><w:sz w:val="21"/></w:rPr></w:rPrDefault><w:pPrDefault><w:pPr><w:spacing w:after="120"/></w:pPr></w:pPrDefault></w:docDefaults><w:style w:type="paragraph" w:default="1" w:styleId="Normal"><w:name w:val="Normal"/></w:style><w:style w:type="paragraph" w:styleId="Title"><w:name w:val="Title"/><w:basedOn w:val="Normal"/><w:pPr><w:spacing w:after="240"/></w:pPr><w:rPr><w:b/><w:sz w:val="40"/></w:rPr></w:style><w:style w:type="paragraph" w:styleId="Heading1"><w:name w:val="heading 1"/><w:basedOn w:val="Normal"/><w:pPr><w:keepNext/><w:spacing w:before="320" w:after="120"/><w:outlineLvl w:val="0"/></w:pPr><w:rPr><w:b/><w:sz w:val="28"/><w:color w:val="1F3864"/></w:rPr></w:style></w:styles>`;
  return writeZip([
    { name: '[Content_Types].xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/><Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/></Types>' },
    { name: '_rels/.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/></Relationships>' },
    { name: 'word/_rels/document.xml.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>' },
    { name: 'word/document.xml', data: doc }, { name: 'word/styles.xml', data: styles },
  ]);
}

// ---------------------------------------------------------------- source code
const RESERVED = new Set(['lambda', 'in', 'is', 'as', 'if', 'or', 'and', 'not', 'del', 'def', 'for', 'from', 'global', 'pass', 'class', 'with', 'yield', 'while', 'try', 'None', 'True', 'False', 'import', 'return', 'int', 'double', 'float', 'char', 'long', 'short', 'auto', 'new', 'delete', 'this', 'union', 'struct', 'template', 'operator', 'private', 'public', 'namespace', 'using', 'end', 'function', 'i', 'j', 'eps', 'pi', 'gamma', 'beta', 'abs', 'min', 'max', 'exp', 'log', 'sqrt', 'sin', 'cos', 'tan', 'time', 'y0', 'y1', 'yn', 'j0', 'j1', 'jn', 'rhs', 'main', 'y', 't']);
const safe = s => { const k = s.replace(/[^A-Za-z0-9_]/g, '_'); return RESERVED.has(k) ? `${k}_v` : k; };
/** Order explicit algebraic equations so each is evaluated after the symbols it needs. */
function explicitPlan(c) {
  const inputSyms = new Set(c.inputs.map(i => i.sym)), known = new Set(inputSyms), plan = [], odes = [], skipped = [];
  const consts = Object.entries(c.table).filter(([, v]) => v.constant).map(([k, v]) => ({ sym: k, value: v.value, unit: v.unit, name: v.name }));
  consts.forEach(k => known.add(k.sym));
  const pending = c.equations.map(q => { try { return { q, L: E.parse(q.lhs), R: E.parse(q.rhs) }; } catch { return null; } }).filter(Boolean);
  let progress = true;
  while (progress) {
    progress = false;
    for (const it of pending) {
      if (it.done) continue;
      const rs = [...E.symbols(it.R)];
      // only relations that assign a new symbol from known ones are executable; a relation whose left side is an
      // input is a consistency condition, and one flagged exportable: false is evaluated differently in the solver
      if (it.q.exportable === false || (it.L.t === 'sym' && inputSyms.has(it.L.n))) continue;
      if (it.L.t === 'sym' && !E.hasDiffOps(it.R) && rs.every(s => known.has(s))) { plan.push(it); known.add(it.L.n); it.done = true; progress = true; }
    }
  }
  // differential equations are integrable only when every symbol on their right sides is available
  const cand = pending.filter(it => !it.done && it.q.exportable !== false && it.L.t === 'fn' && it.L.n === 'd' && it.L.args[0].t === 'sym' && it.L.args[1] && it.L.args[1].t === 'sym' && !E.hasDiffOps(it.R));
  const st = new Set(cand.map(it => it.L.args[0].n)), tv = cand.length ? cand[0].L.args[1].n : null;
  if (cand.length && cand.every(it => !inputSyms.has(it.L.args[0].n) && !known.has(it.L.args[0].n) && [...E.symbols(it.R)].every(s => known.has(s) || st.has(s) || s === tv))) cand.forEach(it => { odes.push(it); it.done = true; });
  pending.filter(it => !it.done).forEach(it => skipped.push(it.q));
  return { plan, odes, skipped, consts: consts.filter(k => c.equations.some(q => new RegExp(`\\b${k.sym}\\b`).test(q.lhs + ' ' + q.rhs))) };
}
const header = (inv, c, cm) => [`${cm} ${inv.title}`, `${cm} Generated ${iso(Date.now())} | investigation ${inv.id} | world: ${(inv.worlds.find(w => w.id === c.worldId) || {}).name}`, `${cm} Model: ${c.model ? c.model.title : 'none'}`, `${cm}`, `${cm} Explicit relations of the model are implemented below. Relations that are implicit, differential in`, `${cm} space, or closed by a tabulated correlation are listed as comments with their origin; the in-app`, `${cm} solver results are embedded at the end so this script can be checked against them.`].join('\n');

export function toPython(inv, c) {
  const { plan, odes, skipped, consts } = explicitPlan(c);
  const L = [header(inv, c, '#'), '', 'import math', 'import numpy as np', '', '# ---- inputs (SI units) -----------------------------------------------'];
  c.inputs.forEach(i => L.push(`${safe(i.sym)} = ${i.si!==undefined?repr(i.si):'float("nan")'}  # ${i.name} [${i.unit} -> SI]; ${PROV[i.prov].label}`));
  if (consts.length) { L.push('', '# ---- constants ---------------------------------------------------------'); consts.forEach(k => L.push(`${safe(k.sym)} = ${repr(k.value)}  # ${k.name} [${k.unit}]`)); }
  L.push('pi = np.pi', '', '# ---- explicit relations --------------------------------------------------');
  plan.forEach(it => L.push(`# ${it.q.name} (${it.q.kind}${it.q.origin ? '; ' + it.q.origin : ''})`, `${safe(it.L.n)} = ${E.toCode(it.R, 'python', safe)}`));
  if (odes.length) {
    const st = odes.map(o => o.L.args[0].n), tv = odes[0].L.args[1].n;
    L.push('', '# ---- ordinary differential equations -------------------------------------', 'from scipy.integrate import solve_ivp', '', `def rhs(${safe(tv)}, y):`, `    ${st.map(safe).join(', ')}${st.length === 1 ? ',' : ''} = y`, `    return [${odes.map(o => E.toCode(o.R, 'python', safe)).join(',\n            ')}]`, '', `def integrate(y0, t_end, method="LSODA"):`, `    """Integrate the system from the initial state y0 (order: ${st.join(', ')}) to t_end."""`, `    return solve_ivp(rhs, (0.0, t_end), y0, method=method, rtol=1e-8, atol=1e-10, dense_output=True)`);
  }
  if (skipped.length) { L.push('', '# ---- relations not reducible to an explicit assignment --------------------'); skipped.forEach(q => L.push(`# ${q.name}: ${q.lhs} = ${q.rhs}   [${q.kind}${q.origin ? '; ' + q.origin : ''}]`)); }
  L.push('', '# ---- reference results from the in-app solver ----------------------------', 'reference = {');
  c.result.scalars.filter(s => Number.isFinite(s.value)).forEach(s => L.push(`    "${s.sym}": ${repr(s.value)},  # ${s.name} [${s.unit}]`));
  L.push('}', '', 'if __name__ == "__main__":', '    for name, ref in reference.items():', '        if name in globals() and isinstance(globals()[name], (int, float)):', '            got = globals()[name]', '            print(f"{name:>12s}  script {got: .6e}   in-app {ref: .6e}   diff {abs(got - ref) / (abs(ref) + 1e-300):.2e}")', '        else:', '            print(f"{name:>12s}  in-app {ref: .6e}")', '');
  return L.join('\n');
}
const repr = v => (Number.isFinite(v) ? (Number.isInteger(v) && Math.abs(v) < 1e15 ? v.toFixed(1) : String(v)) : 'float("nan")');
export function toMatlab(inv, c) {
  const { plan, odes, skipped, consts } = explicitPlan(c);
  const L = [header(inv, c, '%'), '', 'clear; clc;', '', '%% inputs (SI units)'];
  c.inputs.forEach(i => L.push(`${safe(i.sym)} = ${String(i.si)};  % ${i.name} [${i.unit} -> SI]; ${PROV[i.prov].label}`));
  if (consts.length) { L.push('', '%% constants'); consts.forEach(k => L.push(`${safe(k.sym)} = ${String(k.value)};  % ${k.name} [${k.unit}]`)); }
  L.push('', '%% explicit relations');
  plan.forEach(it => L.push(`% ${it.q.name} (${it.q.kind})`, `${safe(it.L.n)} = ${E.toCode(it.R, 'matlab', safe)};`));
  if (odes.length) { const st = odes.map(o => o.L.args[0].n); L.push('', '%% ordinary differential equations', `rhs = @(t, y) [${odes.map(o => E.toCode(o.R, 'matlab', s => (st.includes(s) ? `y(${st.indexOf(s) + 1})` : safe(s)))).join(';\n             ')}];`, `y0 = [${st.map(() => '0').join('; ')}];  % set the initial state`, `opts = odeset('RelTol', 1e-8, 'AbsTol', 1e-10);`, '[t, y] = ode45(rhs, [0 1], y0, opts);'); }
  if (skipped.length) { L.push('', '%% relations not reducible to an explicit assignment'); skipped.forEach(q => L.push(`% ${q.name}: ${q.lhs} = ${q.rhs}   [${q.kind}]`)); }
  L.push('', '%% reference results from the in-app solver', 'reference = struct();');
  c.result.scalars.filter(s => Number.isFinite(s.value)).forEach(s => L.push(`reference.${safe(s.sym)} = ${String(s.value)};  % ${s.name} [${s.unit}]`));
  L.push('', 'names = fieldnames(reference);', 'for k = 1:numel(names)', '    if exist(names{k}, \'var\')', '        got = eval(names{k});', '        fprintf(\'%12s  script % .6e   in-app % .6e\\n\', names{k}, got, reference.(names{k}));', '    else', '        fprintf(\'%12s  in-app % .6e\\n\', names{k}, reference.(names{k}));', '    end', 'end', '');
  return L.join('\n');
}
export function toCpp(inv, c) {
  const { plan, odes, skipped, consts } = explicitPlan(c);
  const L = [header(inv, c, '//'), '', '#include <cmath>', '#include <cstdio>', '#include <vector>', '#include <array>', '#include <algorithm>', '#ifndef M_PI', '#define M_PI 3.14159265358979323846', '#endif', '', 'int main() {', '    // inputs (SI units)'];
  const lit = v => (Number.isFinite(v) ? (Number.isInteger(v) ? v.toFixed(1) : String(v)) : 'NAN');
  c.inputs.forEach(i => L.push(`    const double ${safe(i.sym)} = ${lit(i.si)};  // ${i.name} [${i.unit} -> SI]; ${PROV[i.prov].label}`));
  consts.forEach(k => L.push(`    const double ${safe(k.sym)} = ${lit(k.value)};  // ${k.name} [${k.unit}]`));
  L.push('    const double pi = M_PI; (void)pi;', '', '    // explicit relations');
  plan.forEach(it => L.push(`    // ${it.q.name} (${it.q.kind})`, `    const double ${safe(it.L.n)} = ${E.toCode(it.R, 'cpp', safe)};`));
  if (odes.length) {
    const st = odes.map(o => o.L.args[0].n), n = st.length;
    L.push('', '    // ordinary differential equations: classical fourth-order Runge-Kutta', `    using State = std::array<double, ${n}>;`, `    auto rhs = [&](double t, const State& y) -> State {`, '        (void)t;', ...st.map((s, i) => `        const double ${safe(s)} = y[${i}];`), `        return State{ ${odes.map(o => E.toCode(o.R, 'cpp', safe)).join(',\n                      ')} };`, '    };', `    State y{};  // set the initial state`, '    const double t0 = 0.0, t1 = 1.0; const int steps = 10000; const double h = (t1 - t0) / steps;', '    for (int k = 0; k < steps; ++k) {', '        const double t = t0 + k * h; State k1 = rhs(t, y), a, b, cc;', `        for (int i = 0; i < ${n}; ++i) a[i] = y[i] + 0.5 * h * k1[i];`, '        State k2 = rhs(t + 0.5 * h, a);', `        for (int i = 0; i < ${n}; ++i) b[i] = y[i] + 0.5 * h * k2[i];`, '        State k3 = rhs(t + 0.5 * h, b);', `        for (int i = 0; i < ${n}; ++i) cc[i] = y[i] + h * k3[i];`, '        State k4 = rhs(t + h, cc);', `        for (int i = 0; i < ${n}; ++i) y[i] += h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]);`, '    }', ...st.map((s, i) => `    std::printf("${s}(t1) = % .8e\\n", y[${i}]);`));
  }
  if (skipped.length) { L.push('', '    // relations not reducible to an explicit assignment'); skipped.forEach(q => L.push(`    // ${q.name}: ${q.lhs} = ${q.rhs}   [${q.kind}]`)); }
  L.push('', '    // results, with the in-app solver value alongside');
  const have = new Set(plan.map(it => it.L.n));
  c.result.scalars.filter(s => Number.isFinite(s.value)).forEach(s => L.push(have.has(s.sym) ? `    std::printf("%12s  program % .6e   in-app % .6e\\n", "${s.sym}", ${safe(s.sym)}, ${lit(s.value)});` : `    std::printf("%12s  in-app % .6e\\n", "${s.sym}", ${lit(s.value)});`));
  L.push('    return 0;', '}', '');
  return L.join('\n');
}

// ---------------------------------------------------------------- data
const csvCell = v => (typeof v === 'number' ? (Number.isFinite(v) ? String(v) : '') : /[",\n]/.test(String(v)) ? `"${String(v).replace(/"/g, '""')}"` : String(v ?? ''));
export function seriesCsv(s) {
  const head = [`${s.x.label} (${s.x.unit})`, ...s.y.map(y => `${y.label} (${s.yUnit})`)], n = s.x.data.length;
  return [head.map(csvCell).join(','), ...Array.from({ length: n }, (_, i) => [s.x.data[i], ...s.y.map(y => y.data[i])].map(csvCell).join(','))].join('\n');
}
export const inputsCsv = c => ['symbol,quantity,value,unit,value_SI,origin,basis', ...c.inputs.map(i => [i.sym, i.name, i.value, i.unit, i.si, PROV[i.prov].label, i.note || ''].map(csvCell).join(','))].join('\n');
export const scalarsCsv = c => ['symbol,quantity,value_SI,unit', ...c.result.scalars.map(s => [s.sym, s.name, s.value, s.unit].map(csvCell).join(','))].join('\n');
/** Machine-readable model definition. */
export function modelJson(inv, c) {
  return JSON.stringify({
    format: 'bespoke-model/1', generated: new Date().toISOString(), id: inv.id, title: inv.title, module: inv.module, mode: inv.mode, prompt: inv.prompt,
    class: inv.klass, domains: inv.domains.map(d => d.key), model: c.model ? { id: c.model.id, title: c.model.title, hypothetical: !!c.model.hypothetical } : null, location: inv.location,
    inputs: c.inputs.map(i => ({ symbol: i.sym, name: i.name, value: i.value, unit: i.unit, si: i.si, origin: i.prov, basis: i.note, relativeUncertainty: i.unc, range_si: i.rangeSI })),
    assumptions: (c.model?.assumptions || []).map(a => ({ id: a.id, text: a.text, inForce: c.a[a.id], rationale: a.why, alternative: a.alt })),
    equations: c.equations.map(q => { const r = c.verification.records.find(x => x.id === q.id) || {}; return { id: q.id, name: q.name, lhs: q.lhs, rhs: q.rhs, latex: r.tex, kind: q.kind, origin: q.origin, dependsOn: q.needs || [], verification: r.status, checks: r.steps, regularised: r.regularised ? { lhs: r.regularised.lhs, rhs: r.regularised.rhs } : null }; }),
    symbols: Object.fromEntries(Object.entries(c.table).map(([k, v]) => [k, { name: v.name, unit: v.unit }])),
    closure: c.verification ? c.verification.closure : null,
    results: { status: c.result.status, error: c.result.error || null, scalars: c.result.scalars.map(s => ({ symbol: s.sym, name: s.name, value: s.value, unit: s.unit, text: s.text })), checks: c.result.checks, warnings: c.result.warnings },
    benchmarks: c.benchmarks, validation: c.validation, gates: c.gates, readiness: c.readiness,
    logic: inv.logic ? { ...inv.logic, status: c.logic ? c.logic.status : null } : null,
    worlds: inv.worlds, uploads: inv.uploads.map(u => ({ name: u.name, size: u.size, sha256: u.sha256, family: u.family, summary: u.summary })), audit: inv.audit,
  }, null, 2);
}

/** Complete reproducible package as a ZIP blob. */
export function buildPackage(inv, c, parts) {
  const base = slug(inv.title), rep = parts.report;
  const files = [
    { name: `${base}/README.txt`, data: `${inv.title}\n\nReproducible research package generated ${iso(Date.now())}.\n\nreport/      the investigation report (Markdown, HTML, LaTeX)\nmodel/       machine-readable model definition, inputs and results\nequations/   LaTeX equation dossier and Lean 4 verification source\ncode/        Python, MATLAB/Octave and C++ implementations of the explicit relations\ndata/        every plotted series as CSV\nfigures/     figures as PNG\n\nTo check the Lean file:  lake env lean equations/verification.lean  (inside a project that depends on Mathlib),\nor paste it into the Lean 4 web editor.\nTo run the Python script:  python code/model.py   (needs numpy; scipy for differential equations)\nTo compile the C++ program:  g++ -O2 -std=c++17 code/model.cpp -o model && ./model\n` },
    { name: `${base}/report/report.md`, data: toMarkdown(rep) }, { name: `${base}/report/report.html`, data: toHtml(rep, parts.renderTex, parts.figures || []) }, { name: `${base}/report/report.tex`, data: toLatex(rep) },
    { name: `${base}/model/model.json`, data: modelJson(inv, c) }, { name: `${base}/model/inputs.csv`, data: inputsCsv(c) }, { name: `${base}/model/results.csv`, data: scalarsCsv(c) },
    { name: `${base}/equations/equations.tex`, data: equationsTex(inv, c) }, { name: `${base}/equations/verification.lean`, data: parts.lean },
    { name: `${base}/code/model.py`, data: toPython(inv, c) }, { name: `${base}/code/model.m`, data: toMatlab(inv, c) }, { name: `${base}/code/model.cpp`, data: toCpp(inv, c) },
    ...c.result.series.map(s => ({ name: `${base}/data/${slug(s.id)}.csv`, data: seriesCsv(s) })),
    ...(parts.pngs || []).map(p => ({ name: `${base}/figures/${slug(p.name)}.png`, data: p.bytes })),
  ];
  return writeZip(files);
}
export function equationsTex(inv, c) {
  const L = [`% Equation dossier: ${inv.title}`, '\\documentclass[11pt]{article}', '\\usepackage{amsmath,amssymb}', '\\usepackage[margin=25mm]{geometry}', '\\begin{document}', `\\section*{${tEsc(inv.title)}}`, '\\subsection*{Symbols}', '\\begin{tabular}{lll}'];
  Object.entries(c.table).filter(([k]) => c.equations.some(q => new RegExp(`\\b${k}\\b`).test(q.lhs + ' ' + q.rhs))).forEach(([k, v]) => L.push(`$${E.symTex(k)}$ & ${tEsc(v.name || '')} & ${tEsc(v.unit || '')}\\\\`));
  L.push('\\end{tabular}', '\\subsection*{Derivation}');
  (c.derivation || []).forEach(d => { L.push(tEsc(d.text)); if (d.tex) L.push(`\\begin{equation*}${d.tex}\\end{equation*}`); });
  L.push('\\subsection*{Governing equations}');
  c.verification.records.forEach(r => { const q = c.equations.find(x => x.id === r.id) || {}; L.push(`\\paragraph{${tEsc(r.name)}} (${tEsc(q.kind || '')}${q.origin ? '; ' + tEsc(q.origin) : ''})`, `\\begin{equation}${r.tex || ''}\\end{equation}`); if (r.regularised) L.push(`Regularised form, finite and smooth on the whole declared domain: \\begin{equation*}${r.regularised.tex}\\end{equation*}`); });
  L.push('\\end{document}', '');
  return L.join('\n');
}

export function download(name, data, type = 'text/plain;charset=utf-8') {
  const blob = data instanceof Blob ? data : new Blob([data], { type }), url = URL.createObjectURL(blob), a = document.createElement('a');
  a.href = url; a.download = name; document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 4000);
}
