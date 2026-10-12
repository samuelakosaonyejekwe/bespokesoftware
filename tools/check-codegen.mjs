// Generates the C++ and Python source for every model, compiles and runs the C++, runs the Python
// when numpy is available, and compares every explicitly computed quantity with the in-app result.
//   node tools/check-codegen.mjs [js/models/<pack>.js]
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { MODELS } from '../js/models/index.js';
import { createInvestigation, compute } from '../js/engine/core.js';
import { toCpp, toPython, toMatlab } from '../js/core/exporters.js';

const only = process.argv[2] ? new Set((await import(path.resolve(process.argv[2]))).default.map(m => m.id)) : null;
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'codegen-'));
const hasNumpy = spawnSync('python3', ['-c', 'import numpy'], { stdio: 'ignore' }).status === 0;
// MATLAB files are run with GNU Octave when it is available (set OCTAVE to its launcher, e.g. "octave-cli")
const octave = process.env.OCTAVE ? process.env.OCTAVE.split(' ') : (spawnSync('octave-cli', ['--version'], { stdio: 'ignore' }).status === 0 ? ['octave-cli'] : null);
let mOk = 0, mFail = 0, mCompared = 0, mDiff = 0;
let cppOk = 0, cppFail = 0, pyOk = 0, pyFail = 0, compared = 0, mismatched = 0;
for (const m of MODELS) {
  if (only && !only.has(m.id)) continue;
  const inv = createInvestigation({ module: [].concat(m.module).includes(2) ? 2 : 1, prompt: m.summary, modelId: m.id }), c = compute(inv);
  const base = path.join(dir, m.id.replace(/[^a-z0-9]/gi, '_'));
  fs.writeFileSync(base + '.cpp', toCpp(inv, c));
  try {
    execFileSync('g++', ['-std=c++17', '-O1', '-w', base + '.cpp', '-o', base], { stdio: 'pipe' });
    const out = execFileSync(base, { encoding: 'utf8', timeout: 60000 });
    cppOk++;
    for (const line of out.split('\n')) { const mm = /program\s+(\S+)\s+in-app\s+(\S+)/.exec(line); if (!mm) continue; const a = parseFloat(mm[1]), b = parseFloat(mm[2]); compared++; if (Math.abs(a - b) > 1e-3 * Math.abs(b) + 1e-12 && !(Number.isNaN(a) && Number.isNaN(b))) { mismatched++; console.log(`  differs  ${m.id}: ${line.trim()}`); } }
  } catch (e) { cppFail++; console.log(`  C++ FAIL ${m.id}: ${String(e.stderr || e.message).split('\n').slice(0, 2).join(' ')}`); }
  if (octave) {
    const mf = base + '.m'; fs.writeFileSync(mf, toMatlab(inv, c));
    const r = spawnSync(octave[0], [...octave.slice(1), '--no-gui', '--quiet', '--norc', mf], { encoding: 'utf8', timeout: 120000 });
    if (r.status === 0) { mOk++; for (const line of r.stdout.split('\n')) { const mm = /script\s+(\S+)\s+in-app\s+(\S+)/.exec(line); if (!mm) continue; const x = parseFloat(mm[1]), y = parseFloat(mm[2]); mCompared++; if (Math.abs(x - y) > 1e-3 * Math.abs(y) + 1e-12 && !(Number.isNaN(x) && Number.isNaN(y))) { mDiff++; console.log(`  differs (MATLAB) ${m.id}: ${line.trim()}`); } } }
    else { mFail++; console.log(`  MATLAB FAIL ${m.id}: ${(r.stderr || r.stdout || '').trim().split('\n').slice(0, 2).join(' ')}`); }
  }
  if (hasNumpy) {
    fs.writeFileSync(base + '.py', toPython(inv, c));
    const r = spawnSync('python3', ['-I', base + '.py'], { encoding: 'utf8', timeout: 60000 });
    if (r.status === 0) pyOk++; else { pyFail++; console.log(`  Py  FAIL ${m.id}: ${(r.stderr || '').trim().split('\n').slice(-1)[0]}`); }
  }
}
fs.rmSync(dir, { recursive: true, force: true });
console.log(`C++: ${cppOk} compiled and ran, ${cppFail} failed; ${compared} quantities compared with the in-app solver, ${mismatched} differ`);
console.log(hasNumpy ? `Python: ${pyOk} ran, ${pyFail} failed` : 'Python: numpy is not installed here, so the scripts were not run');
console.log(octave ? `MATLAB (run with GNU Octave): ${mOk} ran, ${mFail} failed; ${mCompared} quantities compared, ${mDiff} differ` : 'MATLAB: GNU Octave is not available here, so the scripts were not run');
process.exit(cppFail || pyFail || mismatched || mFail || mDiff ? 1 : 0);
