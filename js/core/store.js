// On-device persistence (IndexedDB) for investigations and uploaded evidence.
// Nothing leaves the device unless the user exports it.

const DB = 'bespoke-studio', VERSION = 1;
let dbp = null;
const memory = { inv: new Map(), blob: new Map() };
let useMemory = typeof indexedDB === 'undefined';

function open() {
  if (useMemory) return Promise.resolve(null);
  if (dbp) return dbp;
  dbp = new Promise(resolve => {
    try {
      const req = indexedDB.open(DB, VERSION);
      req.onupgradeneeded = () => { const db = req.result; if (!db.objectStoreNames.contains('inv')) db.createObjectStore('inv', { keyPath: 'id' }); if (!db.objectStoreNames.contains('blob')) db.createObjectStore('blob'); };
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => { useMemory = true; resolve(null); };
      req.onblocked = () => { useMemory = true; resolve(null); };
    } catch { useMemory = true; resolve(null); }
  });
  return dbp;
}
const tx = async (store, mode, fn) => {
  const db = await open();
  if (!db) return fn(null);
  return new Promise((resolve, reject) => { const t = db.transaction(store, mode), s = t.objectStore(store); let out; try { out = fn(s); } catch (e) { reject(e); return; } t.oncomplete = () => resolve(out && 'result' in out ? out.result : out); t.onerror = () => reject(t.error); t.onabort = () => reject(t.error); });
};

/** Uploads keep bulky parsed content (tables, geometry, text) in a separate store keyed by upload id. */
const slim = inv => ({ ...inv, uploads: inv.uploads.map(u => ({ ...u, tables: (u.tables || []).map(t => ({ name: t.name, rows: t.rows, columns: t.columns.map(c => ({ name: c.name, unit: c.unit, numeric: c.numeric })) })), text: u.text ? u.text.slice(0, 600) : '', geometry: u.geometry ? { ...u.geometry, points: undefined, tris: undefined } : null, drawing: u.drawing ? { bbox: u.drawing.bbox } : null, heavy: true })) });

export async function saveInvestigation(inv) {
  const rec = slim(inv);
  if (useMemory) { memory.inv.set(inv.id, JSON.parse(JSON.stringify(rec))); return; }
  await tx('inv', 'readwrite', s => s.put(JSON.parse(JSON.stringify(rec))));
}
export async function saveUpload(u, file) {
  const heavy = { tables: u.tables, text: u.text, geometry: u.geometry, drawing: u.drawing };
  if (useMemory) { memory.blob.set(u.id, heavy); if (file) memory.blob.set(u.id + ':file', file); return; }
  await tx('blob', 'readwrite', s => { s.put(heavy, u.id); if (file && file.size < 30 * 1024 * 1024) s.put(file, u.id + ':file'); });
}
export async function loadUpload(id) {
  if (useMemory) return memory.blob.get(id) || null;
  return tx('blob', 'readonly', s => s.get(id));
}
export async function loadUploadFile(id) {
  if (useMemory) return memory.blob.get(id + ':file') || null;
  return tx('blob', 'readonly', s => s.get(id + ':file'));
}
export async function loadInvestigation(id) {
  let inv;
  if (useMemory) inv = memory.inv.get(id); else inv = await tx('inv', 'readonly', s => s.get(id));
  if (!inv) return null;
  for (const u of inv.uploads) if (u.heavy) { const h = await loadUpload(u.id); if (h) Object.assign(u, h); delete u.heavy; }
  return inv;
}
export async function listInvestigations() {
  let all;
  if (useMemory) all = [...memory.inv.values()]; else all = await tx('inv', 'readonly', s => s.getAll());
  return (all || []).map(i => ({ id: i.id, title: i.title, module: i.module, mode: i.mode, updated: i.updated, created: i.created, klass: i.klass, modelId: i.modelId, prompt: i.prompt, location: i.location, worlds: i.worlds.length })).sort((a, b) => b.updated - a.updated);
}
export async function deleteInvestigation(id) {
  const inv = useMemory ? memory.inv.get(id) : await tx('inv', 'readonly', s => s.get(id));
  if (useMemory) { memory.inv.delete(id); return; }
  await tx('inv', 'readwrite', s => s.delete(id));
  if (inv) await tx('blob', 'readwrite', s => { inv.uploads.forEach(u => { s.delete(u.id); s.delete(u.id + ':file'); }); });
}
export async function storageEstimate() {
  try { if (navigator.storage && navigator.storage.estimate) { const e = await navigator.storage.estimate(); return { used: e.usage, quota: e.quota }; } } catch { /* unsupported */ }
  return null;
}
export async function persist() { try { return navigator.storage && navigator.storage.persist ? await navigator.storage.persist() : false; } catch { return false; } }

export const prefs = {
  get(k, d) { try { const v = localStorage.getItem('bespoke.pref.' + k); return v == null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem('bespoke.pref.' + k, JSON.stringify(v)); } catch { /* ignore */ } },
};
