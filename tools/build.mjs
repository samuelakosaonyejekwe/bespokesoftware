// Prepares the static site for publishing:
//   1. writes sw.js from tools/sw.template.js with the list of files to keep offline and a content hash;
//   2. writes bespoke-offline.zip, a complete copy of the application for self-hosting.
// The application itself needs no build step; this only refreshes those two generated files.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const INCLUDE = ['index.html', 'manifest.webmanifest', 'config.json', 'css', 'js', 'vendor', 'icons'];
const walk = p => (fs.statSync(p).isDirectory() ? fs.readdirSync(p).sort().flatMap(f => walk(path.join(p, f))) : [p]);
const files = INCLUDE.flatMap(f => walk(path.join(root, f))).map(f => path.relative(root, f).split(path.sep).join('/'));
const hash = crypto.createHash('sha256');
files.forEach(f => { hash.update(f); hash.update(fs.readFileSync(path.join(root, f))); });
const tpl = fs.readFileSync(path.join(root, 'tools/sw.template.js'), 'utf8');
hash.update(tpl);
const version = hash.digest('hex').slice(0, 12);
fs.writeFileSync(path.join(root, 'sw.js'), tpl.replace('__VERSION__', version).replace('__ASSETS__', JSON.stringify(['./', ...files])));

// ---- offline bundle (stored ZIP, no dependencies)
const crcTable = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
const crc32 = b => { let c = 0xFFFFFFFF; for (let i = 0; i < b.length; i++) c = crcTable[(c ^ b[i]) & 0xFF] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; };
const extra = ['sw.js', 'README.md', 'tools/serve.mjs'].filter(f => fs.existsSync(path.join(root, f)));
const parts = [], central = []; let offset = 0;
for (const f of [...files, ...extra]) {
  const data = fs.readFileSync(path.join(root, f)), name = Buffer.from('bespoke/' + f), crc = crc32(data);
  const lh = Buffer.alloc(30); lh.writeUInt32LE(0x04034b50, 0); lh.writeUInt16LE(20, 4); lh.writeUInt16LE(0x0800, 6); lh.writeUInt32LE(crc, 14); lh.writeUInt32LE(data.length, 18); lh.writeUInt32LE(data.length, 22); lh.writeUInt16LE(name.length, 26);
  parts.push(lh, name, data);
  const ch = Buffer.alloc(46); ch.writeUInt32LE(0x02014b50, 0); ch.writeUInt16LE(20, 4); ch.writeUInt16LE(20, 6); ch.writeUInt16LE(0x0800, 8); ch.writeUInt32LE(crc, 16); ch.writeUInt32LE(data.length, 20); ch.writeUInt32LE(data.length, 24); ch.writeUInt16LE(name.length, 28); ch.writeUInt32LE(offset, 42);
  central.push(ch, name); offset += 30 + name.length + data.length;
}
const csize = central.reduce((a, b) => a + b.length, 0), end = Buffer.alloc(22);
end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(files.length + extra.length, 8); end.writeUInt16LE(files.length + extra.length, 10); end.writeUInt32LE(csize, 12); end.writeUInt32LE(offset, 16);
fs.writeFileSync(path.join(root, 'bespoke-offline.zip'), Buffer.concat([...parts, ...central, end]));
console.log(`sw.js version ${version}, ${files.length} files kept offline; bespoke-offline.zip ${(offset / 1048576).toFixed(2)} MB`);
