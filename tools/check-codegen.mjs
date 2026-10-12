// Generates the C++ and Python source for every model, compiles and runs the C++, runs the Python
// when numpy is available, and compares every explicitly computed quantity with the in-app result.
//   node tools/check-codegen.mjs
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { MODELS } from '../js/models/index.js';
import { createInvestigation, compute } from '../js/engine/core.js';
import { toCpp, toPython } from '../js/core/exporters.js';

const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'codegen-'));
const hasNumpy = spawnSync('python3', ['-c', 'import numpy'], { stdio: 'ignore' }).status === 0;
let cppOk = 0, cppFail = 0, pyOk = 0, pyFail = 0, compared = 0, mismatched = 0;
for (const m of MODELS) {
  const inv = createInvestigation({ module: [].concat(m.module).includes(2) ? 2 : 1, prompt: m.summary, modelId: m.id }), c = compute(inv);
  const base = path.join(dir, m.id.replace(/[^a-z0-9]/gi, '_'));
  fs.writeFileSync(base + '.cpp', toCpp(inv, c));
  try {
    execFileSync('g++', ['-std=c++17', '-O1', '-w', base + '.cpp', '-o', base], { stdio: 'pipe' });
    const out = execFileSync(base, { encoding: 'utf8' });
    cppOk++;
    for (const line of out.split('\n')) { const mm = /program\s+(\S+)\s+in-app\s+(\S+)/.exec(line); if (!mm) continue; const a = parseFloat(mm[1]), b = parseFloat(mm[2]); compared++; if (Math.abs(a - b) > 1e-6 * Math.max(Math.abs(b), 1e-12) && !(Number.isNaN(a) && Number.isNaN(b))) { mismatched++; console.log(`  differs  ${m.id}: ${line.trim()}`); } }
  } catch (e) { cppFail++; console.log(`  C++ FAIL ${m.id}: ${String(e.stderr || e.message).split('\n').slice(0, 2).join(' ')}`); }
  if (hasNumpy) {
    fs.writeFileSync(base + '.py', toPython(inv, c));
    const r = spawnSync('python3', ['-I', base + '.py'], { encoding: 'utf8' });
    if (r.status === 0) pyOk++; else { pyFail++; console.log(`  Py  FAIL ${m.id}: ${(r.stderr || '').trim().split('\n').slice(-1)[0]}`); }
  }
}
fs.rmSync(dir, { recursive: true, force: true });
console.log(`C++: ${cppOk} compiled and ran, ${cppFail} failed; ${compared} quantities compared with the in-app solver, ${mismatched} differ`);
console.log(hasNumpy ? `Python: ${pyOk} ran, ${pyFail} failed` : 'Python: numpy is not installed here, so the scripts were not run');
process.exit(cppFail || pyFail ? 1 : 0);
