// File intake. Every upload is hashed, checked against its claimed type, parsed by a
// format-specific reader where one exists, and otherwise registered as evidence with its
// verified signature. Nothing in an upload is ever executed.
import { readZip, sha256 } from './zip.js';
import { tryUnit } from './units.js';

export const MAX_BYTES = 200 * 1024 * 1024;
const dec = new TextDecoder('utf-8', { fatal: false });
const ext = name => (/\.([A-Za-z0-9]+)$/.exec(name) || [, ''])[1].toLowerCase();

/** Format families shown in the interface. tier: full = parsed into data; meta = header/summary read; reg = registered and verified only. */
export const FORMATS = [
  { family: 'Documents', exts: ['txt', 'md', 'tex', 'rtf', 'docx', 'pdf', 'html', 'xml', 'log'], tier: 'full' },
  { family: 'Numerical data', exts: ['csv', 'tsv', 'dat', 'json', 'xlsx', 'nc', 'cdf', 'h5', 'hdf5', 'mat', 'npy'], tier: 'full' },
  { family: 'CAD geometry', exts: ['step', 'stp', 'iges', 'igs', 'x_t', 'x_b', 'sldprt', 'ipt', 'f3d', '3mf'], tier: 'meta' },
  { family: 'Meshes', exts: ['stl', 'obj', 'ply', 'off', 'vtk', 'vtu', 'msh', 'cgns'], tier: 'full' },
  { family: 'Point clouds', exts: ['xyz', 'pts', 'las', 'laz', 'e57', 'pcd'], tier: 'full' },
  { family: 'Engineering drawings', exts: ['dxf', 'dwg', 'svg'], tier: 'full' },
  { family: 'Material structures', exts: ['cif', 'poscar', 'vasp', 'pdb'], tier: 'meta' },
  { family: 'Microscopy and tomography', exts: ['tif', 'tiff', 'dcm', 'png', 'jpg', 'jpeg', 'bmp', 'gif', 'webp'], tier: 'meta' },
  { family: 'Geographical data', exts: ['geojson', 'kml', 'kmz', 'gpx', 'shp', 'asc'], tier: 'full' },
  { family: 'Astronomical data', exts: ['fits', 'fit', 'tle'], tier: 'meta' },
  { family: 'Mathematics and source code', exts: ['mathml', 'mml', 'py', 'm', 'cpp', 'c', 'h', 'hpp', 'jl', 'f90', 'lean', 'ipynb'], tier: 'full' },
  { family: 'Archives', exts: ['zip'], tier: 'meta' },
];
export const ACCEPT = FORMATS.flatMap(f => f.exts.map(e => '.' + e)).join(',');
const familyOf = e => (FORMATS.find(f => f.exts.includes(e)) || { family: 'Other' }).family;

const SIGS = [
  { name: 'PDF', test: b => b[0] === 0x25 && b[1] === 0x50 && b[2] === 0x44 && b[3] === 0x46, exts: ['pdf'] },
  { name: 'ZIP container', test: b => b[0] === 0x50 && b[1] === 0x4B && (b[2] === 3 || b[2] === 5), exts: ['zip', 'docx', 'xlsx', 'pptx', 'kmz', '3mf', 'f3d', 'odt', 'ods', 'npz'] },
  { name: 'PNG', test: b => b[0] === 0x89 && b[1] === 0x50 && b[2] === 0x4E && b[3] === 0x47, exts: ['png'] },
  { name: 'JPEG', test: b => b[0] === 0xFF && b[1] === 0xD8, exts: ['jpg', 'jpeg'] },
  { name: 'GIF', test: b => b[0] === 0x47 && b[1] === 0x49 && b[2] === 0x46, exts: ['gif'] },
  { name: 'TIFF', test: b => (b[0] === 0x49 && b[1] === 0x49 && b[2] === 0x2A) || (b[0] === 0x4D && b[1] === 0x4D && b[3] === 0x2A), exts: ['tif', 'tiff'] },
  { name: 'HDF5', test: b => b[0] === 0x89 && b[1] === 0x48 && b[2] === 0x44 && b[3] === 0x46, exts: ['h5', 'hdf5', 'nc', 'mat', 'cgns'] },
  { name: 'NetCDF classic', test: b => b[0] === 0x43 && b[1] === 0x44 && b[2] === 0x46 && (b[3] === 1 || b[3] === 2), exts: ['nc', 'cdf'] },
  { name: 'LAS point cloud', test: b => b[0] === 0x4C && b[1] === 0x41 && b[2] === 0x53 && b[3] === 0x46, exts: ['las', 'laz'] },
  { name: 'FITS', test: b => dec.decode(b.subarray(0, 6)) === 'SIMPLE', exts: ['fits', 'fit'] },
  { name: 'E57', test: b => dec.decode(b.subarray(0, 8)) === 'ASTM-E57', exts: ['e57'] },
  { name: 'NumPy array', test: b => b[0] === 0x93 && dec.decode(b.subarray(1, 6)) === 'NUMPY', exts: ['npy'] },
  { name: 'Windows executable', test: b => b[0] === 0x4D && b[1] === 0x5A, exts: [], reject: true },
  { name: 'ELF executable', test: b => b[0] === 0x7F && b[1] === 0x45 && b[2] === 0x4C && b[3] === 0x46, exts: [], reject: true },
  { name: 'Mach-O executable', test: b => (b[0] === 0xCF || b[0] === 0xCE) && b[1] === 0xFA && b[2] === 0xED && b[3] === 0xFE, exts: [], reject: true },
];

const num = s => { const v = parseFloat(s); return Number.isFinite(v) ? v : NaN; };
const isNumStr = s => /^\s*[-+]?(\d+\.?\d*|\.\d+)([eEdD][-+]?\d+)?\s*$/.test(s);

// ---------------------------------------------------------------- tabular text
export function parseDelimited(text, name = 'table') {
  const lines = text.split(/\r?\n/).filter(l => l.trim() && !/^\s*(#|%|\/\/)/.test(l));
  if (!lines.length) return null;
  const sample = lines.slice(0, 20).join('\n');
  const delim = [',', '\t', ';', '|'].map(d => [d, sample.split(d).length]).sort((a, b) => b[1] - a[1])[0];
  const splitter = delim[1] > lines.slice(0, 20).length ? l => splitCsv(l, delim[0]) : l => l.trim().split(/\s+/);
  const rows = lines.map(splitter);
  const width = rows.map(r => r.length).sort((a, b) => a - b)[Math.floor(rows.length / 2)];
  const first = rows[0], hasHeader = first.some(c => !isNumStr(c));
  const body = (hasHeader ? rows.slice(1) : rows).filter(r => r.length >= width);
  const headers = hasHeader ? first : Array.from({ length: width }, (_, i) => `col${i + 1}`);
  const columns = [];
  for (let j = 0; j < width; j++) {
    const raw = (headers[j] || `col${j + 1}`).trim().replace(/^"|"$/g, '');
    const mu = /^(.*?)\s*[\[(]\s*([^\])]+?)\s*[\])]\s*$/.exec(raw);
    const unit = mu && tryUnit(mu[2]) ? mu[2] : '';
    const data = body.map(r => num(String(r[j]).replace(/[dD]([-+]?\d)/, 'e$1')));
    const numeric = data.filter(Number.isFinite).length >= 0.8 * data.length && data.length > 0;
    columns.push({ name: (mu && unit ? mu[1] : raw) || `col${j + 1}`, unit, data: numeric ? data : null, text: numeric ? null : body.map(r => String(r[j] ?? '')), numeric });
  }
  return { name, columns, rows: body.length };
}
function splitCsv(line, d) {
  const out = []; let cur = '', q = false;
  for (let i = 0; i < line.length; i++) { const c = line[i]; if (c === '"') { if (q && line[i + 1] === '"') { cur += '"'; i++; } else q = !q; } else if (c === d && !q) { out.push(cur); cur = ''; } else cur += c; }
  out.push(cur); return out.map(s => s.trim());
}

// ---------------------------------------------------------------- geometry helpers
function geoFromPoints(pts, faces, kind) {
  const n = pts.length / 3; if (!n) return null;
  const mn = [Infinity, Infinity, Infinity], mx = [-Infinity, -Infinity, -Infinity];
  for (let i = 0; i < n; i++) for (let k = 0; k < 3; k++) { const v = pts[3 * i + k]; if (v < mn[k]) mn[k] = v; if (v > mx[k]) mx[k] = v; }
  let area = 0, volume = 0, nf = 0;
  if (faces) {
    nf = faces.length / 3;
    for (let f = 0; f < nf; f++) {
      const a = faces[3 * f] * 3, b = faces[3 * f + 1] * 3, c = faces[3 * f + 2] * 3;
      const ux = pts[b] - pts[a], uy = pts[b + 1] - pts[a + 1], uz = pts[b + 2] - pts[a + 2], vx = pts[c] - pts[a], vy = pts[c + 1] - pts[a + 1], vz = pts[c + 2] - pts[a + 2];
      const cx = uy * vz - uz * vy, cy = uz * vx - ux * vz, cz = ux * vy - uy * vx;
      area += 0.5 * Math.hypot(cx, cy, cz);
      volume += (pts[a] * (pts[b + 1] * pts[c + 2] - pts[b + 2] * pts[c + 1]) - pts[a + 1] * (pts[b] * pts[c + 2] - pts[b + 2] * pts[c]) + pts[a + 2] * (pts[b] * pts[c + 1] - pts[b + 1] * pts[c])) / 6;
    }
  }
  const stride = Math.max(1, Math.floor(n / 6000)), sample = [];
  for (let i = 0; i < n; i += stride) sample.push(pts[3 * i], pts[3 * i + 1], pts[3 * i + 2]);
  let edges = null;
  if (faces && nf <= 20000) { edges = []; const st = Math.max(1, Math.floor(nf / 4000)); for (let f = 0; f < nf; f += st) edges.push(faces[3 * f], faces[3 * f + 1], faces[3 * f + 2]); }
  return { kind, nVertices: n, nFaces: nf, bbox: [mn, mx], size: mx.map((v, k) => v - mn[k]), area: faces ? area : null, volume: faces ? Math.abs(volume) : null, closedHint: faces ? Math.abs(volume) > 1e-12 : false, points: sample, tris: edges ? { idx: edges, pts: nf <= 20000 ? Array.from(pts) : null } : null };
}
function parseStl(buf) {
  const u8 = new Uint8Array(buf), dv = new DataView(buf);
  const head = dec.decode(u8.subarray(0, 512));
  const nTri = u8.length >= 84 ? dv.getUint32(80, true) : 0;
  if (!(84 + nTri * 50 === u8.length) && /^\s*solid/.test(head) && /facet/.test(head)) {
    const t = dec.decode(u8), re = /vertex\s+([-+\d.eE]+)\s+([-+\d.eE]+)\s+([-+\d.eE]+)/g, pts = []; let m;
    while ((m = re.exec(t))) pts.push(+m[1], +m[2], +m[3]);
    const faces = Array.from({ length: pts.length / 3 }, (_, i) => i);
    return geoFromPoints(pts, faces, 'Triangle mesh (ASCII STL)');
  }
  if (84 + nTri * 50 > u8.length) throw new Error('STL file is truncated');
  const pts = new Float32Array(nTri * 9), faces = new Uint32Array(nTri * 3);
  for (let i = 0; i < nTri; i++) { const o = 84 + i * 50 + 12; for (let k = 0; k < 9; k++) pts[i * 9 + k] = dv.getFloat32(o + k * 4, true); faces[i * 3] = i * 3; faces[i * 3 + 1] = i * 3 + 1; faces[i * 3 + 2] = i * 3 + 2; }
  return geoFromPoints(pts, faces, 'Triangle mesh (binary STL)');
}
function parseObj(text) {
  const pts = [], faces = [];
  for (const l of text.split('\n')) {
    if (l.startsWith('v ')) { const p = l.trim().split(/\s+/); pts.push(+p[1], +p[2], +p[3]); }
    else if (l.startsWith('f ')) { const p = l.trim().split(/\s+/).slice(1).map(s => { const i = parseInt(s, 10); return i < 0 ? pts.length / 3 + i : i - 1; }); for (let k = 1; k < p.length - 1; k++) faces.push(p[0], p[k], p[k + 1]); }
  }
  return geoFromPoints(pts, faces.length ? faces : null, faces.length ? 'Polygon mesh (OBJ)' : 'Point set (OBJ)');
}
function parsePly(buf) {
  const u8 = new Uint8Array(buf), headEnd = (() => { const s = dec.decode(u8.subarray(0, Math.min(u8.length, 8192))); const i = s.indexOf('end_header'); return i < 0 ? -1 : i + 'end_header'.length + (s[i + 10] === '\r' ? 2 : 1); })();
  if (headEnd < 0) throw new Error('PLY header not found');
  const head = dec.decode(u8.subarray(0, headEnd)), nV = +(/element vertex (\d+)/.exec(head) || [, 0])[1], nF = +(/element face (\d+)/.exec(head) || [, 0])[1];
  if (/format ascii/.test(head)) {
    const lines = dec.decode(u8.subarray(headEnd)).split('\n'), pts = [], faces = [];
    for (let i = 0; i < nV; i++) { const p = lines[i].trim().split(/\s+/); pts.push(+p[0], +p[1], +p[2]); }
    for (let i = 0; i < nF; i++) { const p = (lines[nV + i] || '').trim().split(/\s+/).map(Number); for (let k = 2; k < p[0]; k++) faces.push(p[1], p[k], p[k + 1]); }
    return geoFromPoints(pts, faces.length ? faces : null, 'PLY (ASCII)');
  }
  // binary little-endian: read leading x,y,z floats using declared vertex property sizes
  const vBlock = head.slice(head.indexOf('element vertex')).split('element')[1] || '';
  const sizes = { char: 1, uchar: 1, int8: 1, uint8: 1, short: 2, ushort: 2, int16: 2, uint16: 2, int: 4, uint: 4, int32: 4, uint32: 4, float: 4, float32: 4, double: 8, float64: 8 };
  const props = [...vBlock.matchAll(/property (\w+) (\w+)/g)].map(m => ({ type: m[1], name: m[2] }));
  const stride = props.reduce((a, p) => a + (sizes[p.type] || 4), 0), dv = new DataView(buf, headEnd), le = /binary_little_endian/.test(head);
  const off = n => { let o = 0; for (const p of props) { if (p.name === n) return [o, p.type]; o += sizes[p.type] || 4; } return null; };
  const ox = off('x'), oy = off('y'), oz = off('z'); if (!ox) throw new Error('PLY has no x/y/z vertex properties');
  const rd = (i, o) => (o[1] === 'double' || o[1] === 'float64' ? dv.getFloat64(i * stride + o[0], le) : dv.getFloat32(i * stride + o[0], le));
  const pts = new Float32Array(nV * 3);
  for (let i = 0; i < nV && (i + 1) * stride <= dv.byteLength; i++) { pts[3 * i] = rd(i, ox); pts[3 * i + 1] = rd(i, oy); pts[3 * i + 2] = rd(i, oz); }
  return geoFromPoints(pts, null, `PLY (binary), ${nF} faces declared`);
}
function parseXyz(text) {
  const lines = text.split(/\r?\n/), first = lines[0].trim();
  if (/^\d+$/.test(first) && lines.length >= +first + 2 && /^[A-Za-z]{1,2}\s/.test((lines[2] || '').trim())) {
    const n = +first, pts = [], species = {};
    for (let i = 0; i < n; i++) { const p = (lines[i + 2] || '').trim().split(/\s+/); if (p.length >= 4) { species[p[0]] = (species[p[0]] || 0) + 1; pts.push(+p[1], +p[2], +p[3]); } }
    const g = geoFromPoints(pts, null, 'Atomistic structure (XYZ, coordinates in Å)');
    return { geometry: g, meta: { atoms: n, composition: Object.entries(species).map(([k, v]) => `${k}${v}`).join(' '), comment: lines[1] } };
  }
  const pts = [];
  for (const l of lines) { const p = l.trim().split(/[\s,;]+/); if (p.length >= 3 && isNumStr(p[0]) && isNumStr(p[1]) && isNumStr(p[2])) pts.push(+p[0], +p[1], +p[2]); }
  return { geometry: geoFromPoints(pts, null, 'Point cloud (XYZ)'), meta: {} };
}
function parseVtk(text) {
  const m = /POINTS\s+(\d+)\s+\w+\s+([\s\S]*?)(?:\n[A-Z_]{4,}|$)/.exec(text); if (!m) return null;
  const v = m[2].trim().split(/\s+/).slice(0, +m[1] * 3).map(Number);
  const cells = +(/CELLS\s+(\d+)/.exec(text) || [, 0])[1], fields = [...text.matchAll(/(?:SCALARS|VECTORS)\s+(\S+)/g)].map(x => x[1]);
  const g = geoFromPoints(v, null, `VTK legacy dataset (${(/DATASET\s+(\S+)/.exec(text) || [, 'unknown'])[1]})`);
  return { geometry: g, meta: { cells, fields: fields.join(', ') || 'none' } };
}
function parseStep(text) {
  const pts = []; const re = /CARTESIAN_POINT\s*\(\s*'[^']*'\s*,\s*\(\s*([-+\d.eE]+)\s*,\s*([-+\d.eE]+)\s*(?:,\s*([-+\d.eE]+))?\s*\)/g; let m;
  while ((m = re.exec(text)) && pts.length < 600000) pts.push(+m[1], +m[2], +(m[3] || 0));
  const count = k => (text.match(new RegExp(`=\\s*${k}\\s*\\(`, 'g')) || []).length;
  const unit = /SI_UNIT\s*\(\s*\.(MILLI|CENTI|MICRO)?\.?\s*,?\s*\.METRE\./.exec(text);
  const meta = { schema: (/FILE_SCHEMA\s*\(\s*\(\s*'([^']+)'/.exec(text) || [, 'unknown'])[1], product: (/PRODUCT\s*\(\s*'([^']*)'/.exec(text) || [, ''])[1], solids: count('MANIFOLD_SOLID_BREP'), faces: count('ADVANCED_FACE'), edges: count('EDGE_CURVE'), cylinders: count('CYLINDRICAL_SURFACE'), planes: count('PLANE'), lengthUnit: unit ? `${(unit[1] || '').toLowerCase()}metre` : 'not stated' };
  return { geometry: geoFromPoints(pts, null, 'B-rep control points (STEP)'), meta };
}
function parseIges(text) {
  const types = {}; for (const l of text.split('\n')) if (l[72] === 'D') { const t = parseInt(l.slice(0, 8), 10); if (t) types[t] = (types[t] || 0) + 0.5; }
  const names = { 100: 'circular arcs', 110: 'lines', 116: 'points', 120: 'surfaces of revolution', 122: 'tabulated cylinders', 126: 'B-spline curves', 128: 'B-spline surfaces', 142: 'curves on surfaces', 144: 'trimmed surfaces', 186: 'solids (B-rep)', 314: 'colour definitions', 406: 'properties', 408: 'subfigure instances', 502: 'vertices', 504: 'edges', 508: 'loops', 510: 'faces', 514: 'shells' };
  return { meta: { entities: Object.entries(types).map(([k, v]) => `${Math.round(v)} ${names[k] || `type ${k}`}`).join(', ') || 'none found' } };
}
function parseDxf(text) {
  const g = text.split(/\r?\n/), ents = {}, segs = []; let i = g.findIndex((l, k) => l.trim() === 'ENTITIES' && g[k - 1] && g[k - 1].trim() === '2');
  if (i < 0) i = 0;
  let cur = null; const flush = () => {
    if (!cur) return; ents[cur.t] = (ents[cur.t] || 0) + 1; const v = cur.v;
    if (cur.t === 'LINE' && v[10] != null) segs.push([[v[10][0], v[20][0]], [v[11][0], v[21][0]]]);
    else if ((cur.t === 'LWPOLYLINE' || cur.t === 'POLYLINE') && v[10]) { const p = v[10].map((x, k) => [x, v[20][k]]); if ((v[70] && (v[70][0] & 1))) p.push(p[0]); segs.push(p); }
    else if ((cur.t === 'CIRCLE' || cur.t === 'ARC') && v[40]) { const a0 = cur.t === 'ARC' ? v[50][0] * Math.PI / 180 : 0; let a1 = cur.t === 'ARC' ? v[51][0] * Math.PI / 180 : 2 * Math.PI; if (a1 < a0) a1 += 2 * Math.PI; const p = []; for (let k = 0; k <= 48; k++) { const a = a0 + (a1 - a0) * k / 48; p.push([v[10][0] + v[40][0] * Math.cos(a), v[20][0] + v[40][0] * Math.sin(a)]); } segs.push(p); }
    cur = null;
  };
  for (; i + 1 < g.length; i += 2) {
    const code = parseInt(g[i], 10), val = (g[i + 1] || '').trim();
    if (code === 0) { flush(); if (val === 'ENDSEC' && Object.keys(ents).length) break; if (val !== 'SECTION' && val !== 'ENDSEC' && val !== 'EOF' && val !== 'SEQEND' && val !== 'VERTEX') cur = { t: val, v: {} }; }
    else if (cur && [10, 11, 20, 21, 40, 50, 51, 70].includes(code)) (cur.v[code] = cur.v[code] || []).push(parseFloat(val));
  }
  flush();
  const all = segs.flat(), xs = all.map(p => p[0]), ys = all.map(p => p[1]);
  const bbox = all.length ? [[Math.min(...xs), Math.min(...ys), 0], [Math.max(...xs), Math.max(...ys), 0]] : null;
  return { meta: { entities: Object.entries(ents).map(([k, v]) => `${v} ${k}`).join(', ') || 'none found', units: (/\$INSUNITS\s+70\s+(\d+)/.exec(text) || [, 'not stated'])[1] }, drawing: { segs: segs.slice(0, 6000), bbox } };
}
function parseLas(buf) {
  const dv = new DataView(buf); if (buf.byteLength < 227) throw new Error('LAS header truncated');
  const vMaj = dv.getUint8(24), vMin = dv.getUint8(25), off = dv.getUint32(96, true), fmt = dv.getUint8(104) & 0x3F, recLen = dv.getUint16(105, true);
  let n = dv.getUint32(107, true); if (vMaj === 1 && vMin >= 4 && buf.byteLength >= 255) n = Number(dv.getBigUint64(247, true)) || n;
  const sc = [dv.getFloat64(131, true), dv.getFloat64(139, true), dv.getFloat64(147, true)], of = [dv.getFloat64(155, true), dv.getFloat64(163, true), dv.getFloat64(171, true)];
  const mx = [dv.getFloat64(179, true), dv.getFloat64(195, true), dv.getFloat64(211, true)], mn = [dv.getFloat64(187, true), dv.getFloat64(203, true), dv.getFloat64(219, true)];
  const pts = [], stride = Math.max(1, Math.floor(n / 6000));
  for (let i = 0; i < n && off + (i + 1) * recLen <= buf.byteLength; i += stride) { const o = off + i * recLen; pts.push(dv.getInt32(o, true) * sc[0] + of[0], dv.getInt32(o + 4, true) * sc[1] + of[1], dv.getInt32(o + 8, true) * sc[2] + of[2]); }
  const g = pts.length ? geoFromPoints(pts, null, 'LiDAR point cloud (LAS)') : { kind: 'LiDAR point cloud (LAS header only)', points: [] };
  Object.assign(g, { nVertices: n, bbox: [mn, mx], size: mx.map((v, k) => v - mn[k]) });
  return { geometry: g, meta: { version: `${vMaj}.${vMin}`, pointFormat: fmt, points: n } };
}
function parseFits(buf) {
  const u8 = new Uint8Array(buf), cards = {};
  for (let o = 0; o + 80 <= u8.length && o < 2880 * 20; o += 80) { const c = dec.decode(u8.subarray(o, o + 80)), k = c.slice(0, 8).trim(); if (k === 'END') break; if (c[8] === '=') cards[k] = c.slice(10).split(' /')[0].trim().replace(/^'|'$/g, '').trim(); }
  const nax = +cards.NAXIS || 0;
  return { meta: { bitpix: cards.BITPIX, dimensions: Array.from({ length: nax }, (_, i) => cards[`NAXIS${i + 1}`]).join(' × ') || 'none', object: cards.OBJECT || '', telescope: cards.TELESCOP || '', instrument: cards.INSTRUME || '', date: cards['DATE-OBS'] || cards.DATE || '', units: cards.BUNIT || '' } };
}
function parseNetcdf(buf) {
  const dv = new DataView(buf); let p = 4; const u8 = new Uint8Array(buf);
  const i32 = () => { const v = dv.getInt32(p); p += 4; return v; };
  const str = () => { const n = i32(), s = dec.decode(u8.subarray(p, p + n)); p += n + ((4 - (n % 4)) % 4); return s; };
  const numrecs = i32(), dims = [], vars = [];
  try {
    let tag = i32(), n = i32(); if (tag === 0x0A) for (let i = 0; i < n; i++) { const name = str(), len = i32(); dims.push(`${name} = ${len || `unlimited (${numrecs})`}`); }
    const skipAtts = () => { const t = i32(), m = i32(); if (t === 0x0C) for (let i = 0; i < m; i++) { str(); const ty = i32(), ne = i32(), sz = { 1: 1, 2: 1, 3: 2, 4: 4, 5: 4, 6: 8 }[ty] || 1, bytes = ne * sz; p += bytes + ((4 - (bytes % 4)) % 4); } };
    skipAtts(); tag = i32(); n = i32();
    if (tag === 0x0B) for (let i = 0; i < n && i < 400; i++) { const name = str(), nd = i32(); p += 4 * nd; skipAtts(); const ty = i32(); p += 4 + (u8[3] === 2 ? 8 : 4); vars.push(`${name} (${['', 'byte', 'char', 'short', 'int', 'float', 'double'][ty] || '?'}, ${nd}-D)`); }
  } catch { /* partial header is still useful */ }
  return { meta: { dimensions: dims.join('; ') || 'none read', variables: vars.join('; ') || 'none read' } };
}
function parseKml(text) {
  const pts = []; for (const m of text.matchAll(/<coordinates>([\s\S]*?)<\/coordinates>/g)) for (const t of m[1].trim().split(/\s+/)) { const c = t.split(',').map(Number); if (c.length >= 2 && Number.isFinite(c[0])) pts.push(c[0], c[1], c[2] || 0); }
  for (const m of text.matchAll(/<(?:trkpt|wpt|rtept)\s+lat="([-\d.]+)"\s+lon="([-\d.]+)"/g)) pts.push(+m[2], +m[1], 0);
  return { geometry: geoFromPoints(pts, null, 'Geographic coordinates (longitude, latitude)'), meta: { placemarks: (text.match(/<Placemark/g) || []).length } };
}
function parseGeojson(obj) {
  const pts = [], types = {};
  const walk = c => { if (typeof c[0] === 'number') pts.push(c[0], c[1], c[2] || 0); else c.forEach(walk); };
  const feats = obj.type === 'FeatureCollection' ? obj.features : obj.type === 'Feature' ? [obj] : [{ geometry: obj }];
  feats.forEach(f => { if (f.geometry && f.geometry.coordinates) { types[f.geometry.type] = (types[f.geometry.type] || 0) + 1; walk(f.geometry.coordinates); } });
  const props = feats[0] && feats[0].properties ? Object.keys(feats[0].properties) : [];
  return { geometry: geoFromPoints(pts, null, 'Geographic features (longitude, latitude)'), meta: { features: feats.length, types: Object.entries(types).map(([k, v]) => `${v} ${k}`).join(', '), properties: props.slice(0, 12).join(', ') } };
}
function parseCif(text) {
  const g = k => (new RegExp(`${k}\\s+([-\\d.]+)`).exec(text) || [, ''])[1];
  return { meta: { a: g('_cell_length_a'), b: g('_cell_length_b'), c: g('_cell_length_c'), alpha: g('_cell_angle_alpha'), beta: g('_cell_angle_beta'), gamma: g('_cell_angle_gamma'), spaceGroup: (/_symmetry_space_group_name_H-M\s+'?([^'\n]+)/.exec(text) || /_space_group_name_H-M_alt\s+'?([^'\n]+)/.exec(text) || [, ''])[1].trim(), formula: (/_chemical_formula_sum\s+'?([^'\n]+)/.exec(text) || [, ''])[1].trim() } };
}
function parsePoscar(text) {
  const l = text.split(/\r?\n/), s = parseFloat(l[1]), v = [2, 3, 4].map(i => l[i].trim().split(/\s+/).map(Number).map(x => x * s));
  const len = v.map(a => Math.hypot(...a)); const sp = l[5].trim().split(/\s+/), cnt = (isNumStr(sp[0]) ? l[5] : l[6]).trim().split(/\s+/).map(Number);
  return { meta: { a: len[0].toFixed(4), b: len[1].toFixed(4), c: len[2].toFixed(4), species: isNumStr(sp[0]) ? '' : sp.join(' '), atoms: cnt.reduce((a, b) => a + b, 0), comment: l[0] } };
}
function tiffInfo(buf) {
  const dv = new DataView(buf), le = dv.getUint16(0) === 0x4949, o = dv.getUint32(4, le), n = dv.getUint16(o, le), m = {};
  for (let i = 0; i < n && o + 2 + (i + 1) * 12 <= buf.byteLength; i++) { const e = o + 2 + i * 12, tag = dv.getUint16(e, le), type = dv.getUint16(e + 2, le), val = type === 3 ? dv.getUint16(e + 8, le) : dv.getUint32(e + 8, le); if (tag === 256) m.width = val; if (tag === 257) m.height = val; if (tag === 258) m.bitsPerSample = val; if (tag === 277) m.samplesPerPixel = val; if (tag === 33550 || tag === 34735) m.georeferenced = 'yes (GeoTIFF tags present)'; }
  return { meta: m };
}
async function pdfText(buf) {
  const u8 = new Uint8Array(buf), raw = new TextDecoder('latin1').decode(u8); const out = []; let pos = 0, n = 0, total = 0;
  const pages = (raw.match(/\/Type\s*\/Page[^s]/g) || []).length;
  while (n < 400 && total < 400000) {
    const s = raw.indexOf('stream', pos); if (s < 0) break; const e = raw.indexOf('endstream', s); if (e < 0) break;
    const dict = raw.slice(Math.max(0, s - 300), s); let start = s + 6; if (raw[start] === '\r') start++; if (raw[start] === '\n') start++;
    pos = e + 9; n++;
    if (!/FlateDecode/.test(dict) || /\/Subtype\s*\/Image|\/Type\s*\/XRef|\/Type\s*\/ObjStm|FontFile|\/Length1/.test(dict)) continue;
    try {
      const ds = new DecompressionStream('deflate'), rd = new Blob([u8.subarray(start, e)]).stream().pipeThrough(ds).getReader(); const chunks = []; let len = 0;
      for (;;) { const { done, value } = await rd.read(); if (done) break; len += value.length; if (len > 4e6) { rd.cancel(); break; } chunks.push(value); }
      const txt = new TextDecoder('latin1').decode(await new Blob(chunks).arrayBuffer());
      if (!/BT[\s\S]*?ET/.test(txt)) continue;
      let line = '';
      for (const m of txt.matchAll(/\[((?:[^\]\\]|\\.)*)\]\s*TJ|\(((?:[^)\\]|\\.)*)\)\s*(?:Tj|'|")|(T\*|ET|Td|TD)/g)) {
        if (m[3]) { if (line.trim()) { out.push(line); total += line.length; } line = ''; continue; }
        const seg = m[1] != null ? [...m[1].matchAll(/\(((?:[^)\\]|\\.)*)\)|(-?\d+\.?\d*)/g)].map(x => (x[1] != null ? x[1] : (+x[2] < -180 ? ' ' : ''))).join('') : m[2];
        line += seg.replace(/\\([()\\])/g, '$1').replace(/\\(\d{3})/g, (_, o) => String.fromCharCode(parseInt(o, 8))).replace(/\\[nrtbf]/g, ' ');
      }
      if (line.trim()) out.push(line);
    } catch { /* unreadable stream: skip */ }
  }
  const text = out.join('\n').replace(/[^\x09\x0A\x20-\x7E -ÿ]/g, '').replace(/[ \t]+/g, ' ');
  return { text, pages };
}
const xmlText = xml => xml.replace(/<w:tab\/>/g, '\t').replace(/<\/w:p>|<w:br\/>/g, '\n').replace(/<\/w:tc>/g, '\t').replace(/<[^>]+>/g, '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&amp;/g, '&');
async function parseXlsx(entries) {
  const get = async n => { const e = entries.find(x => x.name === n); return e ? e.text() : ''; };
  const ss = [...(await get('xl/sharedStrings.xml')).matchAll(/<si>([\s\S]*?)<\/si>/g)].map(m => xmlText(m[1]));
  const tables = [];
  for (const e of entries.filter(x => /^xl\/worksheets\/sheet\d+\.xml$/.test(x.name)).slice(0, 8)) {
    const xml = await e.text(), rows = [];
    for (const r of xml.matchAll(/<row[^>]*>([\s\S]*?)<\/row>/g)) {
      const row = [];
      for (const c of r[1].matchAll(/<c\s+([^>]*?)(?:\/>|>([\s\S]*?)<\/c>)/g)) {
        const ref = (/r="([A-Z]+)\d+"/.exec(c[1]) || [, 'A'])[1], col = [...ref].reduce((a, ch) => a * 26 + ch.charCodeAt(0) - 64, 0) - 1;
        const t = (/t="(\w+)"/.exec(c[1]) || [, 'n'])[1], v = c[2] ? (/<v>([\s\S]*?)<\/v>/.exec(c[2]) || /<t[^>]*>([\s\S]*?)<\/t>/.exec(c[2]) || [, ''])[1] : '';
        row[col] = t === 's' ? ss[+v] ?? '' : xmlText(v);
      }
      rows.push(Array.from(row, x => x ?? ''));
    }
    if (rows.length) { const t = parseDelimited(rows.map(r => r.map(x => (/[,"\n]/.test(x) ? `"${String(x).replace(/"/g, '""')}"` : x)).join(',')).join('\n'), e.name.replace(/^.*\//, '').replace('.xml', '')); if (t) tables.push(t); }
  }
  return tables;
}

/** Read one File/Blob. Returns the upload record (never throws; problems go into `warnings`). */
export async function importFile(file) {
  const e = ext(file.name), rec = { id: Math.random().toString(36).slice(2, 10), name: file.name, size: file.size, ext: e, family: familyOf(e), tier: 'registered', summary: '', tables: [], text: '', geometry: null, drawing: null, meta: {}, warnings: [], ts: Date.now(), mime: file.type || '' };
  if (file.size > MAX_BYTES) { rec.rejected = true; rec.summary = `Rejected: larger than the ${MAX_BYTES / 1048576} MB intake limit.`; return rec; }
  let buf;
  try { buf = await file.arrayBuffer(); } catch (err) { rec.rejected = true; rec.summary = `Could not be read: ${err.message}`; return rec; }
  rec.sha256 = await sha256(buf);
  const head = new Uint8Array(buf, 0, Math.min(buf.byteLength, 16));
  const sig = SIGS.find(s => { try { return s.test(head); } catch { return false; } });
  if (sig && sig.reject) { rec.rejected = true; rec.summary = `Rejected: the content is a ${sig.name.toLowerCase()}, which is never accepted.`; return rec; }
  rec.signature = sig ? sig.name : 'text or unrecognised binary';
  if (sig && sig.exts.length && !sig.exts.includes(e)) rec.warnings.push(`Content looks like ${sig.name} but the file is named .${e}. It was read according to its content.`);
  const text = () => dec.decode(new Uint8Array(buf));
  try {
    if (sig && sig.name === 'ZIP container') {
      const entries = readZip(buf);
      rec.meta.entries = entries.length;
      if (entries.some(x => x.name === 'word/document.xml')) { rec.text = xmlText(await entries.find(x => x.name === 'word/document.xml').text()); rec.tier = 'parsed'; rec.summary = `Word document, ${rec.text.split(/\s+/).length.toLocaleString()} words extracted.`; if (entries.some(x => /vbaProject/.test(x.name))) rec.warnings.push('Contains macros. They were ignored.'); }
      else if (entries.some(x => x.name === 'xl/workbook.xml')) { rec.tables = await parseXlsx(entries); rec.tier = 'parsed'; rec.summary = `Workbook, ${rec.tables.length} sheet(s): ${rec.tables.map(t => `${t.rows} rows × ${t.columns.length} columns`).join('; ')}.`; }
      else if (entries.some(x => /\.kml$/i.test(x.name))) { Object.assign(rec, parseKml(await entries.find(x => /\.kml$/i.test(x.name)).text())); rec.tier = 'parsed'; rec.summary = `Compressed KML with ${rec.meta.placemarks} placemark(s).`; }
      else { rec.tier = 'summarised'; rec.meta.contents = entries.slice(0, 40).map(x => x.name).join(', '); rec.summary = `Archive with ${entries.length} entries. Contents are listed but not extracted; upload individual files to analyse them.`; }
    } else if (sig && sig.name === 'PDF') { const p = await pdfText(buf); rec.text = p.text; rec.meta.pages = p.pages; rec.tier = p.text.length > 40 ? 'parsed' : 'summarised'; rec.summary = p.text.length > 40 ? `PDF, ${p.pages} page(s); ${p.text.split(/\s+/).length.toLocaleString()} words of text recovered (best effort: scanned pages and embedded fonts may be missed).` : `PDF, ${p.pages} page(s). No extractable text layer was found (likely scanned or image-based); it is kept as evidence.`; }
    else if (['png', 'jpg', 'jpeg', 'gif', 'webp', 'bmp'].includes(e)) { rec.image = true; rec.tier = 'summarised'; rec.summary = 'Image. Shown as visual evidence; dimensions and any scale must be supplied separately — pixels are not measurements.'; }
    else if (e === 'svg') { const t = text(); rec.image = true; rec.svgSafe = !/<script|on\w+\s*=|javascript:/i.test(t); rec.tier = 'summarised'; rec.summary = `Vector drawing (${(t.match(/<(path|line|rect|circle|polyline|polygon|ellipse)\b/g) || []).length} shapes).${rec.svgSafe ? '' : ' Active content was found and will not be run.'}`; }
    else if (['tif', 'tiff'].includes(e)) { Object.assign(rec, tiffInfo(buf)); rec.tier = 'summarised'; rec.summary = `TIFF image ${rec.meta.width} × ${rec.meta.height}, ${rec.meta.bitsPerSample}-bit.`; }
    else if (e === 'stl') { rec.geometry = parseStl(buf); }
    else if (e === 'obj') { rec.geometry = parseObj(text()); }
    else if (e === 'ply') { rec.geometry = parsePly(buf); }
    else if (e === 'off') { const l = text().split(/\r?\n/).filter(x => x.trim() && !x.startsWith('#')); const [nv, nf] = (l[0].trim() === 'OFF' ? l[1] : l[0].replace('OFF', '')).trim().split(/\s+/).map(Number), o = l[0].trim() === 'OFF' ? 2 : 1, pts = [], fc = []; for (let i = 0; i < nv; i++) pts.push(...l[o + i].trim().split(/\s+/).slice(0, 3).map(Number)); for (let i = 0; i < nf; i++) { const p = l[o + nv + i].trim().split(/\s+/).map(Number); for (let k = 2; k < p[0]; k++) fc.push(p[1], p[k], p[k + 1]); } rec.geometry = geoFromPoints(pts, fc, 'Polygon mesh (OFF)'); }
    else if (['xyz', 'pts'].includes(e)) { Object.assign(rec, parseXyz(text())); }
    else if (e === 'vtk') { const r = parseVtk(text()); if (r) Object.assign(rec, r); }
    else if (['step', 'stp'].includes(e)) { Object.assign(rec, parseStep(text())); rec.tier = 'summarised'; rec.summary = `STEP model (${rec.meta.schema}): ${rec.meta.solids} solid(s), ${rec.meta.faces} faces, ${rec.meta.edges} edges. Overall extents are taken from its control points; exact surfaces need a CAD kernel.`; }
    else if (['iges', 'igs'].includes(e)) { Object.assign(rec, parseIges(text())); rec.tier = 'summarised'; rec.summary = `IGES file: ${rec.meta.entities}.`; }
    else if (e === 'dxf') { Object.assign(rec, parseDxf(text())); rec.tier = 'parsed'; rec.summary = `DXF drawing: ${rec.meta.entities}.`; }
    else if (e === 'las') { Object.assign(rec, parseLas(buf)); }
    else if (['fits', 'fit'].includes(e)) { Object.assign(rec, parseFits(buf)); rec.tier = 'summarised'; rec.summary = `FITS file, data array ${rec.meta.dimensions}${rec.meta.object ? `, object ${rec.meta.object}` : ''}.`; }
    else if (sig && sig.name === 'NetCDF classic') { Object.assign(rec, parseNetcdf(buf)); rec.tier = 'summarised'; rec.summary = 'NetCDF classic file: dimensions and variables listed from its header.'; }
    else if (['kml', 'gpx'].includes(e)) { Object.assign(rec, parseKml(text())); }
    else if (e === 'cif') { Object.assign(rec, parseCif(text())); rec.tier = 'summarised'; rec.summary = `Crystal structure${rec.meta.formula ? ` ${rec.meta.formula}` : ''}: a = ${rec.meta.a} Å, b = ${rec.meta.b} Å, c = ${rec.meta.c} Å${rec.meta.spaceGroup ? `, space group ${rec.meta.spaceGroup}` : ''}.`; }
    else if (['poscar', 'vasp'].includes(e) || /^(POSCAR|CONTCAR)/i.test(file.name)) { Object.assign(rec, parsePoscar(text())); rec.tier = 'summarised'; rec.summary = `Crystal cell ${rec.meta.a} × ${rec.meta.b} × ${rec.meta.c} Å with ${rec.meta.atoms} atoms.`; }
    else if (e === 'shp') { const dv = new DataView(buf); rec.meta = { shapeType: dv.getInt32(32, true), bbox: [0, 1, 2, 3].map(i => dv.getFloat64(36 + 8 * i, true).toFixed(5)).join(', ') }; rec.tier = 'summarised'; rec.summary = `Shapefile, bounding box ${rec.meta.bbox}.`; }
    else if (e === 'tle' || (e === 'txt' && /^1 \d{5}[A-Z ] /m.test(text().slice(0, 400)))) { const l = text().split(/\r?\n/).filter(Boolean), i = l.findIndex(x => x.startsWith('1 ')); if (i >= 0 && l[i + 1]) { const b = l[i + 1]; rec.meta = { name: i > 0 ? l[i - 1].trim() : '', inclination_deg: +b.slice(8, 16), raan_deg: +b.slice(17, 25), eccentricity: +('0.' + b.slice(26, 33)), argPerigee_deg: +b.slice(34, 42), meanMotion_rev_per_day: +b.slice(52, 63) }; rec.tier = 'parsed'; rec.summary = `Orbital elements${rec.meta.name ? ` for ${rec.meta.name}` : ''}: inclination ${rec.meta.inclination_deg}°, eccentricity ${rec.meta.eccentricity}, ${rec.meta.meanMotion_rev_per_day} rev/day.`; } rec.text = text(); }
    else if (['json', 'geojson', 'ipynb'].includes(e)) {
      const t = text(), obj = JSON.parse(t);
      if (obj && (obj.type === 'FeatureCollection' || obj.type === 'Feature' || obj.coordinates)) Object.assign(rec, parseGeojson(obj));
      else if (Array.isArray(obj) && obj.length && typeof obj[0] === 'object' && !Array.isArray(obj[0])) { const keys = Object.keys(obj[0]); rec.tables = [{ name: file.name, rows: obj.length, columns: keys.map(k => { const d = obj.map(r => (typeof r[k] === 'number' ? r[k] : num(r[k]))); const numeric = d.filter(Number.isFinite).length >= 0.8 * d.length; return { name: k, unit: '', data: numeric ? d : null, text: numeric ? null : obj.map(r => String(r[k] ?? '')), numeric }; }) }]; }
      else if (obj && typeof obj === 'object' && Object.values(obj).some(v => Array.isArray(v) && typeof v[0] === 'number')) { const cols = Object.entries(obj).filter(([, v]) => Array.isArray(v) && typeof v[0] === 'number'); rec.tables = [{ name: file.name, rows: Math.max(...cols.map(c => c[1].length)), columns: cols.map(([k, v]) => ({ name: k, unit: '', data: v, numeric: true })) }]; }
      else if (e === 'ipynb' && obj.cells) rec.text = obj.cells.map(c => (Array.isArray(c.source) ? c.source.join('') : c.source)).join('\n\n');
      else rec.text = t.slice(0, 200000);
      rec.tier = 'parsed';
    }
    else if (['csv', 'tsv', 'dat', 'asc'].includes(e)) { const t = parseDelimited(text(), file.name); if (t) rec.tables = [t]; rec.tier = 'parsed'; }
    else if (!sig) {
      const t = text();
      const printable = t.slice(0, 4000).replace(/[\x20-\x7E\s -￿]/g, '').length < 40;
      if (printable) { rec.text = t.slice(0, 2e6); rec.tier = 'parsed'; const tb = /^[\s\d.,;eE+\-\t]+$/m.test(t.slice(0, 2000)) ? parseDelimited(t, file.name) : null; if (tb && tb.columns.filter(c => c.numeric).length >= 2 && tb.rows >= 3) rec.tables = [tb]; }
    }
    if (rec.geometry) { rec.tier = 'parsed'; const g = rec.geometry; rec.summary = rec.summary || `${g.kind}: ${g.nVertices.toLocaleString()} points${g.nFaces ? `, ${g.nFaces.toLocaleString()} triangles` : ''}; extents ${g.size.map(v => +v.toPrecision(4)).join(' × ')}${g.area ? `; surface area ${+g.area.toPrecision(4)}` : ''}${g.volume ? `; enclosed volume ${+g.volume.toPrecision(4)}` : ''} (file units).`; }
    if (rec.tables.length && !rec.summary) rec.summary = `${rec.tables.length} table(s): ${rec.tables.map(t => `${t.rows.toLocaleString()} rows × ${t.columns.length} columns (${t.columns.filter(c => c.numeric).length} numeric)`).join('; ')}.`;
    if (rec.text && !rec.summary) rec.summary = `Text, ${rec.text.split(/\s+/).length.toLocaleString()} words.${['py', 'm', 'cpp', 'c', 'jl', 'f90', 'lean', 'h', 'hpp'].includes(e) ? ' Source code is stored for reference and is never executed.' : ''}`;
    if (!rec.summary) { rec.summary = `Registered as evidence (${rec.signature}). This format needs a dedicated reader that is not built in; its hash and metadata are recorded so results stay traceable.`; }
  } catch (err) { rec.warnings.push(`The reader stopped early: ${err.message}`); rec.summary = rec.summary || 'Registered as evidence; the content could not be fully parsed.'; }
  if (rec.text && rec.text.length > 2e6) rec.text = rec.text.slice(0, 2e6);
  return rec;
}

/** Equations found in free text or LaTeX: lines of the form  lhs = rhs  that parse in the expression grammar. */
export function findEquations(text, parse) {
  const out = [];
  const clean = s => s.replace(/\\frac\{([^{}]+)\}\{([^{}]+)\}/g, '($1)/($2)').replace(/\\sqrt\{([^{}]+)\}/g, 'sqrt($1)').replace(/\\(cdot|times)/g, '*').replace(/\\left|\\right|\\,|\\;|\\!|\$/g, '').replace(/\\(alpha|beta|gamma|delta|epsilon|theta|lambda|mu|nu|rho|sigma|tau|phi|omega|pi|ell|kappa|eta|xi|zeta|psi|chi)/g, '$1').replace(/\\(sin|cos|tan|exp|ln|log|tanh|sinh|cosh)/g, '$1').replace(/\^\{([^{}]+)\}/g, '^($1)').replace(/_\{([^{}]+)\}/g, '_$1').replace(/[{}]/g, '').replace(/\s+/g, ' ');
  for (const raw of String(text).split(/\r?\n|\\\\|;/)) {
    const line = clean(raw).trim().replace(/[.,]$/, '');
    if (line.length < 3 || line.length > 200 || (line.match(/=/g) || []).length !== 1) continue;
    const [l, r] = line.split('=').map(s => s.trim());
    if (!l || !r || /[<>!]$/.test(l) || / {1,}[a-z]{4,} /.test(` ${l} `) || r.split(' ').filter(w => /^[a-zA-Z]{5,}$/.test(w) && !/^(sqrt|log10|tanh|sinh|cosh|asin|acos|atan)$/.test(w)).length > 1) continue;
    try { parse(l); parse(r); out.push({ lhs: l, rhs: r, raw: raw.trim().slice(0, 200) }); } catch { /* not an equation */ }
    if (out.length >= 40) break;
  }
  return out;
}
