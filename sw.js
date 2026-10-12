// Service worker: keeps the whole application available offline, updates it in the background,
// caches answers from scientific data sources for offline use, and falls back to mirror hosts.
const VERSION = '0042ee2d259e';
const SHELL = `bespoke-shell-${VERSION}`;
const DATA = 'bespoke-data-v1';
const RUNTIME = 'bespoke-runtime-v1';
const ASSETS = ["./","index.html","manifest.webmanifest","config.json","css/app.css","js/app.js","js/core/connectors.js","js/core/discover.js","js/core/exporters.js","js/core/expr.js","js/core/importers.js","js/core/inverse.js","js/core/lean.js","js/core/logic.js","js/core/num.js","js/core/plot.js","js/core/store.js","js/core/units.js","js/core/verify.js","js/core/zip.js","js/data/catalogue.js","js/data/domains.js","js/data/reference.js","js/engine/core.js","js/engine/custom.js","js/engine/prompt.js","js/models/aerospace-space-classical.js","js/models/em-waves-materials.js","js/models/flow-assurance.js","js/models/index.js","js/models/kit.js","js/models/logic-thought.js","js/models/marine-offshore-structural.js","js/models/nuclear.js","js/models/relativity-quantum.js","js/models/thermal-process-cfd.js","js/ui/dom.js","js/ui/investigation.js","js/ui/pages.js","js/ui/widgets.js","js/ui/ws-a.js","js/ui/ws-b.js","vendor/katex/fonts/KaTeX_AMS-Regular.woff2","vendor/katex/fonts/KaTeX_Caligraphic-Bold.woff2","vendor/katex/fonts/KaTeX_Caligraphic-Regular.woff2","vendor/katex/fonts/KaTeX_Fraktur-Bold.woff2","vendor/katex/fonts/KaTeX_Fraktur-Regular.woff2","vendor/katex/fonts/KaTeX_Main-Bold.woff2","vendor/katex/fonts/KaTeX_Main-BoldItalic.woff2","vendor/katex/fonts/KaTeX_Main-Italic.woff2","vendor/katex/fonts/KaTeX_Main-Regular.woff2","vendor/katex/fonts/KaTeX_Math-BoldItalic.woff2","vendor/katex/fonts/KaTeX_Math-Italic.woff2","vendor/katex/fonts/KaTeX_SansSerif-Bold.woff2","vendor/katex/fonts/KaTeX_SansSerif-Italic.woff2","vendor/katex/fonts/KaTeX_SansSerif-Regular.woff2","vendor/katex/fonts/KaTeX_Script-Regular.woff2","vendor/katex/fonts/KaTeX_Size1-Regular.woff2","vendor/katex/fonts/KaTeX_Size2-Regular.woff2","vendor/katex/fonts/KaTeX_Size3-Regular.woff2","vendor/katex/fonts/KaTeX_Size4-Regular.woff2","vendor/katex/fonts/KaTeX_Typewriter-Regular.woff2","vendor/katex/katex.min.css","vendor/katex/katex.min.js","icons/apple-touch-icon.png","icons/icon-192.png","icons/icon-512.png","icons/icon.svg","icons/maskable-512.png","icons/maskable.svg"];
const DATA_HOSTS = ['api.open-meteo.com', 'marine-api.open-meteo.com', 'geocoding-api.open-meteo.com', 'gis.ngdc.noaa.gov', 'power.larc.nasa.gov', 'services.swpc.noaa.gov', 'api.nasa.gov', 'api.wheretheiss.at', 'eonet.gsfc.nasa.gov', 'earthquake.usgs.gov', 'api.crossref.org', 'api.openalex.org', 'en.wikipedia.org', 'pubchem.ncbi.nlm.nih.gov'];
const RUNTIME_HOSTS = ['cdn.jsdelivr.net'];

self.addEventListener('install', event => {
  event.waitUntil((async () => {
    const cache = await caches.open(SHELL);
    // add individually so that one missing optional file cannot block installation
    await Promise.all(ASSETS.map(async url => { try { const res = await fetch(new Request(url, { cache: 'reload' })); if (res.ok) await cache.put(url, res); } catch { /* fetched later on demand */ } }));
    await self.skipWaiting();
  })());
});

self.addEventListener('activate', event => {
  event.waitUntil((async () => {
    const keys = await caches.keys();
    await Promise.all(keys.filter(k => k.startsWith('bespoke-shell-') && k !== SHELL).map(k => caches.delete(k)));
    await self.clients.claim();
  })());
});

async function mirrors() {
  try { const cache = await caches.open(SHELL); const res = await cache.match('config.json'); if (res) { const cfg = await res.clone().json(); return Array.isArray(cfg.mirrors) ? cfg.mirrors : []; } } catch { /* no configuration cached */ }
  return [];
}

/** Application files: always from this version's own cache, so that files from two releases are never mixed.
 *  A new release arrives as a new service worker, which fills a new cache and then takes over. */
async function shell(request) {
  const cache = await caches.open(SHELL);
  const url = new URL(request.url);
  const key = url.pathname.endsWith('/') ? url.pathname + 'index.html' : url.pathname;
  const cached = await cache.match(request, { ignoreSearch: true }) || await cache.match(key, { ignoreSearch: true });
  if (cached) return cached;
  try { const res = await fetch(request, { cache: 'no-cache' }); if (res && res.ok) { cache.put(request, res.clone()).catch(() => {}); return res; } if (res) return res; }
  catch { /* offline or host unreachable */ }
  const rel = url.pathname.replace(new URL(self.registration.scope).pathname, '');
  for (const m of await mirrors()) { try { const res = await fetch(new URL(rel, m.endsWith('/') ? m : m + '/'), { mode: 'cors' }); if (res.ok) { cache.put(request, res.clone()).catch(() => {}); return res; } } catch { /* try the next mirror */ } }
  if (request.mode === 'navigate') { const index = await cache.match('index.html') || await cache.match('./index.html') || await cache.match('./'); if (index) return index; }
  return new Response('This file is not available offline yet.', { status: 503, headers: { 'Content-Type': 'text/plain' } });
}

/** Scientific data: prefer the network, keep the answer, serve the saved copy when the network fails. */
async function data(request) {
  const cache = await caches.open(DATA);
  try {
    const res = await fetch(request);
    if (res && res.ok) cache.put(request, res.clone()).catch(() => {});
    return res;
  } catch (err) {
    const cached = await cache.match(request);
    if (cached) return cached;
    throw err;
  }
}
/** Large optional runtimes (the Python interpreter): cache on first use, then serve from the device. */
async function runtime(request) {
  const cache = await caches.open(RUNTIME);
  const cached = await cache.match(request);
  if (cached) return cached;
  const res = await fetch(request);
  if (res && (res.ok || res.type === 'opaque')) cache.put(request, res.clone()).catch(() => {});
  return res;
}

self.addEventListener('fetch', event => {
  const { request } = event;
  if (request.method !== 'GET') return;
  const url = new URL(request.url);
  if (url.origin === self.location.origin) { event.respondWith(shell(request)); return; }
  if (DATA_HOSTS.includes(url.hostname)) { event.respondWith(data(request)); return; }
  if (RUNTIME_HOSTS.includes(url.hostname)) { event.respondWith(runtime(request)); }
});

/** Background refresh of the feeds that do not depend on a location (where the platform allows it). */
const FEEDS = ['https://services.swpc.noaa.gov/products/noaa-planetary-k-index.json', 'https://services.swpc.noaa.gov/products/summary/solar-wind-speed.json', 'https://earthquake.usgs.gov/earthquakes/feed/v1.0/summary/4.5_day.geojson', 'https://eonet.gsfc.nasa.gov/api/v3/events?limit=12&status=open'];
async function refreshFeeds() {
  const cache = await caches.open(DATA);
  await Promise.all(FEEDS.map(async u => { try { const res = await fetch(u); if (res.ok) await cache.put(u, res); } catch { /* next time */ } }));
  // also pick up a newer version of the application itself
  try { await self.registration.update(); } catch { /* offline */ }
}
self.addEventListener('periodicsync', event => { if (event.tag === 'refresh-data') event.waitUntil(refreshFeeds()); });
self.addEventListener('sync', event => { if (event.tag === 'refresh-data') event.waitUntil(refreshFeeds()); });
self.addEventListener('message', event => { if (event.data === 'refresh') event.waitUntil(refreshFeeds()); if (event.data === 'skipWaiting') self.skipWaiting(); });
