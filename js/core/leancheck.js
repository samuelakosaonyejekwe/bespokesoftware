// Machine-checks a generated proof file with a real Lean 4 kernel and the Mathlib library, from
// inside the application. The file is sent over a WebSocket, speaking the language-server protocol,
// to the public Lean server operated by the Lean community (live.lean-lang.org); Lean elaborates
// every theorem and returns its diagnostics. Results are remembered per file content, so the same
// equations are never sent twice. A connection is required; without one the on-device checks stand.

const SERVER = 'wss://live.lean-lang.org/websocket/MathlibDemo';
const FOLDER = 'MathlibDemo';
const KEY = 'bespoke.lean.';
const mem = new Map();

export async function sourceHash(source) {
  const h = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(source));
  return [...new Uint8Array(h)].slice(0, 12).map(b => b.toString(16).padStart(2, '0')).join('');
}
export function cached(hash) {
  if (mem.has(hash)) return mem.get(hash);
  try { const s = localStorage.getItem(KEY + hash); if (s) { const v = JSON.parse(s); mem.set(hash, v); return v; } } catch { /* storage unavailable */ }
  return null;
}
function remember(hash, v) {
  mem.set(hash, v);
  try { localStorage.setItem(KEY + hash, JSON.stringify(v)); const keys = Object.keys(localStorage).filter(k => k.startsWith(KEY)); if (keys.length > 60) keys.slice(0, 20).forEach(k => localStorage.removeItem(k)); } catch { /* ignore */ }
}

/** Name of the theorem that contains a given (1-based) line. */
function theoremAt(lines, line) {
  for (let i = Math.min(line, lines.length) - 1; i >= 0; i--) { const m = /^\s*(?:theorem|lemma|example|def)\s+([A-Za-z0-9_'.]+)?/.exec(lines[i]); if (m) return m[1] || 'example'; }
  return '';
}

/**
 * @returns {Promise<{ok, errors:[{line, theorem, message}], warnings, theorems, ms, at, cached?}>}
 * Rejects with an Error when the server cannot be reached or does not answer in time.
 */
export async function checkLean(source, { force = false, timeout = 150000, onStatus } = {}) {
  const hash = await sourceHash(source);
  if (!force) { const c = cached(hash); if (c) return { ...c, cached: true }; }
  if (typeof navigator !== 'undefined' && navigator.onLine === false) throw new Error('The device is offline. The proof file will be checked by Lean when a connection is available.');
  const lines = source.split('\n'), theorems = lines.filter(l => /^\s*theorem\s/.test(l)).length;
  return new Promise((resolve, reject) => {
    let ws, done = false, diags = [], t0 = Date.now();
    const uri = `file:///${FOLDER}/${FOLDER}.lean`;
    const finish = (fn, v) => { if (done) return; done = true; clearTimeout(timer); try { ws.close(); } catch { /* already closed */ } fn(v); };
    const timer = setTimeout(() => finish(reject, new Error('Lean did not answer in time. The server may be busy; try again shortly.')), timeout);
    try { ws = new WebSocket(SERVER); } catch (e) { clearTimeout(timer); reject(new Error('A connection to the Lean server could not be opened.')); return; }
    const send = o => ws.send(JSON.stringify({ jsonrpc: '2.0', ...o }));
    ws.onopen = () => { onStatus && onStatus('Connected. Starting Lean…'); send({ id: 0, method: 'initialize', params: { processId: null, clientInfo: { name: 'Bespoke', version: '1' }, rootUri: `file:///${FOLDER}`, capabilities: {} } }); };
    ws.onmessage = ev => {
      let m; try { m = JSON.parse(ev.data); } catch { return; }
      if (m.id === 0 && m.result) { send({ method: 'initialized', params: {} }); send({ method: 'textDocument/didOpen', params: { textDocument: { uri, languageId: 'lean4', version: 1, text: source } } }); send({ id: 1, method: 'textDocument/waitForDiagnostics', params: { uri, version: 1 } }); onStatus && onStatus(`Lean is checking ${theorems} theorems…`); }
      else if (m.method === 'textDocument/publishDiagnostics') diags = m.params.diagnostics || [];
      else if (m.method === '$/lean/fileProgress') { const p = m.params.processing || []; if (p.length && onStatus) onStatus(`Lean is checking: line ${p[0].range.start.line + 1} of ${lines.length}…`); }
      else if (m.id != null && m.method) send({ id: m.id, result: null });
      else if (m.id === 1) {
        if (m.error) { finish(reject, new Error(`Lean reported a protocol error: ${m.error.message || 'unknown'}`)); return; }
        const errors = diags.filter(d => d.severity === 1).map(d => ({ line: d.range.start.line + 1, theorem: theoremAt(lines, d.range.start.line + 1), message: String(d.message).slice(0, 600) }));
        const sorry = diags.filter(d => /declaration uses 'sorry'|uses `sorry`/.test(d.message)).length;
        const v = { ok: errors.length === 0 && sorry === 0, errors, sorry, warnings: diags.filter(d => d.severity === 2).length, theorems, ms: Date.now() - t0, at: Date.now(), hash };
        remember(hash, v); finish(resolve, v);
      }
    };
    ws.onerror = () => finish(reject, new Error('The Lean server could not be reached.'));
    ws.onclose = () => finish(reject, new Error('The connection to the Lean server closed before the check finished.'));
  });
}
