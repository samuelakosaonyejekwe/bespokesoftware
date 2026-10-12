// Minimal ZIP reader and writer (store + deflate via the platform's Compression Streams).
// Used to read DOCX / XLSX / KMZ / 3MF uploads and to build export packages, with guards
// against decompression bombs and path traversal.

const CRC = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
export function crc32(u8) { let c = 0xFFFFFFFF; for (let i = 0; i < u8.length; i++) c = CRC[(c ^ u8[i]) & 0xFF] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
const enc = new TextEncoder(), dec = new TextDecoder();

export const LIMITS = { maxEntries: 5000, maxEntryBytes: 80 * 1024 * 1024, maxTotalBytes: 300 * 1024 * 1024, maxRatio: 200 };

async function inflateRaw(u8, limit) {
  if (typeof DecompressionStream === 'undefined') throw new Error('This browser cannot decompress archives');
  const ds = new DecompressionStream('deflate-raw');
  const reader = new Blob([u8]).stream().pipeThrough(ds).getReader();
  const chunks = []; let total = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    total += value.length;
    if (total > limit) { reader.cancel(); throw new Error('Archive entry expands beyond the safety limit'); }
    chunks.push(value);
  }
  const out = new Uint8Array(total); let o = 0; chunks.forEach(c => { out.set(c, o); o += c.length; });
  return out;
}

/** List the entries of a ZIP archive. Returns [{name, size, compressedSize, method, read(): Promise<Uint8Array>, text(): Promise<string>}] */
export function readZip(buffer) {
  const u8 = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer), dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
  let eocd = -1;
  for (let i = u8.length - 22; i >= Math.max(0, u8.length - 65557); i--) if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
  if (eocd < 0) throw new Error('Not a ZIP archive (no end-of-central-directory record)');
  const count = dv.getUint16(eocd + 10, true); let p = dv.getUint32(eocd + 16, true);
  if (count > LIMITS.maxEntries) throw new Error(`Archive has ${count} entries; the limit is ${LIMITS.maxEntries}`);
  const entries = []; let total = 0;
  for (let k = 0; k < count; k++) {
    if (dv.getUint32(p, true) !== 0x02014b50) throw new Error('Corrupt ZIP central directory');
    const method = dv.getUint16(p + 10, true), csize = dv.getUint32(p + 20, true), size = dv.getUint32(p + 24, true);
    const nlen = dv.getUint16(p + 28, true), elen = dv.getUint16(p + 30, true), clen = dv.getUint16(p + 32, true), off = dv.getUint32(p + 42, true);
    const name = dec.decode(u8.subarray(p + 46, p + 46 + nlen));
    p += 46 + nlen + elen + clen;
    if (name.includes('..') || name.startsWith('/') || /^[A-Za-z]:/.test(name)) continue; // path traversal
    if (size > LIMITS.maxEntryBytes) throw new Error(`Entry "${name}" is larger than the safety limit`);
    if (csize > 0 && size / csize > LIMITS.maxRatio && size > 1e6) throw new Error(`Entry "${name}" has a suspicious compression ratio`);
    total += size; if (total > LIMITS.maxTotalBytes) throw new Error('Archive expands beyond the total safety limit');
    const read = async () => {
      const ln = dv.getUint16(off + 26, true), le = dv.getUint16(off + 28, true), start = off + 30 + ln + le, raw = u8.subarray(start, start + csize);
      if (method === 0) return raw;
      if (method === 8) return inflateRaw(raw, Math.max(size, 1) + 1024);
      throw new Error(`Unsupported ZIP compression method ${method}`);
    };
    entries.push({ name, size, compressedSize: csize, method, dir: name.endsWith('/'), read, text: async () => dec.decode(await read()) });
  }
  return entries;
}

/** Build a ZIP (stored, no compression) from [{name, data: string | Uint8Array}]. Returns a Blob. */
export function writeZip(files) {
  const parts = [], central = []; let offset = 0;
  const now = new Date(), dosTime = (now.getHours() << 11) | (now.getMinutes() << 5) | (now.getSeconds() >> 1), dosDate = ((now.getFullYear() - 1980) << 9) | ((now.getMonth() + 1) << 5) | now.getDate();
  for (const f of files) {
    const data = typeof f.data === 'string' ? enc.encode(f.data) : f.data, name = enc.encode(f.name), crc = crc32(data);
    const lh = new DataView(new ArrayBuffer(30));
    lh.setUint32(0, 0x04034b50, true); lh.setUint16(4, 20, true); lh.setUint16(6, 0x0800, true); lh.setUint16(8, 0, true); lh.setUint16(10, dosTime, true); lh.setUint16(12, dosDate, true);
    lh.setUint32(14, crc, true); lh.setUint32(18, data.length, true); lh.setUint32(22, data.length, true); lh.setUint16(26, name.length, true); lh.setUint16(28, 0, true);
    parts.push(new Uint8Array(lh.buffer), name, data);
    const ch = new DataView(new ArrayBuffer(46));
    ch.setUint32(0, 0x02014b50, true); ch.setUint16(4, 20, true); ch.setUint16(6, 20, true); ch.setUint16(8, 0x0800, true); ch.setUint16(10, 0, true); ch.setUint16(12, dosTime, true); ch.setUint16(14, dosDate, true);
    ch.setUint32(16, crc, true); ch.setUint32(20, data.length, true); ch.setUint32(24, data.length, true); ch.setUint16(28, name.length, true); ch.setUint32(42, offset, true);
    central.push(new Uint8Array(ch.buffer), name);
    offset += 30 + name.length + data.length;
  }
  const csize = central.reduce((a, b) => a + b.length, 0), end = new DataView(new ArrayBuffer(22));
  end.setUint32(0, 0x06054b50, true); end.setUint16(8, files.length, true); end.setUint16(10, files.length, true); end.setUint32(12, csize, true); end.setUint32(16, offset, true);
  return new Blob([...parts, ...central, new Uint8Array(end.buffer)], { type: 'application/zip' });
}

export async function sha256(buffer) {
  const h = await crypto.subtle.digest('SHA-256', buffer);
  return [...new Uint8Array(h)].map(b => b.toString(16).padStart(2, '0')).join('');
}
