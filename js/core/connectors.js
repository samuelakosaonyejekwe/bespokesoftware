// Live data connectors. All requests are made directly from the user's own browser to public
// scientific services, so freshness never depends on any one machine or server. Every result
// records where it came from and when; the last good answer is kept on the device and is
// clearly marked as cached when the network or the source is unavailable.

const KEY = 'bespoke.conn.';
const mem = new Map();
const nasaKey = () => { try { return localStorage.getItem('bespoke.nasaKey') || 'DEMO_KEY'; } catch { return 'DEMO_KEY'; } };

/** Catalogue of sources: what they provide, who runs them, and how often the source itself is updated. */
export const SOURCES = [
  { id: 'weather', name: 'Surface weather', provider: 'Open-Meteo (national weather-service models: ECMWF, NOAA GFS, DWD ICON and others)', gives: 'Air temperature, pressure, humidity, wind at a point', cadence: 'Model runs hourly to six-hourly; values at 15-minute resolution', ttl: 15 * 60e3, licence: 'CC BY 4.0', home: 'https://open-meteo.com' },
  { id: 'marine', name: 'Sea state', provider: 'Open-Meteo Marine (ECMWF WAM, NOAA GFS-Wave, Copernicus Marine)', gives: 'Significant wave height, wave period, sea-surface temperature, surface current', cadence: 'Model runs every 6–12 hours', ttl: 30 * 60e3, licence: 'CC BY 4.0', home: 'https://open-meteo.com/en/docs/marine-weather-api' },
  { id: 'relief', name: 'Bathymetry and terrain', provider: 'NOAA National Centers for Environmental Information — global DEM mosaic', gives: 'Seabed depth or ground elevation at a point', cadence: 'Static survey compilation, revised occasionally', ttl: 30 * 864e5, licence: 'US public domain', home: 'https://www.ncei.noaa.gov' },
  { id: 'oceanprofile', name: 'Ocean temperature and salinity at depth', provider: 'GLODAP v2 mapped climatology (ship-borne measurements 1972–2013), served by EMODnet Physics', gives: 'Measured-data climatology of sea-water temperature and salinity on 33 depth levels, one-degree grid; used for seabed temperature', cadence: 'Static climatology of quality-controlled measurements', ttl: 90 * 864e5, licence: 'Open (GLODAP data policy; cite Lauvset et al. 2016)', home: 'https://glodap.info' },
  { id: 'climate', name: 'Climatology', provider: 'NASA POWER (Langley Research Center)', gives: 'Long-term monthly means of temperature and wind', cadence: 'Multi-decade averages, updated yearly', ttl: 30 * 864e5, licence: 'NASA open data', home: 'https://power.larc.nasa.gov' },
  { id: 'geocode', name: 'Place names', provider: 'Open-Meteo Geocoding (GeoNames)', gives: 'Coordinates and elevation of named places', cadence: 'Updated periodically', ttl: 30 * 864e5, licence: 'CC BY 4.0', home: 'https://open-meteo.com/en/docs/geocoding-api' },
  { id: 'spaceweather', name: 'Space weather', provider: 'NOAA Space Weather Prediction Center', gives: 'Planetary K index, solar-wind speed, interplanetary magnetic field', cadence: 'Solar wind every minute; K index every 3 hours', ttl: 5 * 60e3, licence: 'US public domain', home: 'https://www.swpc.noaa.gov' },
  { id: 'neo', name: 'Near-Earth objects', provider: 'NASA / JPL Center for Near-Earth Object Studies', gives: 'Asteroids passing Earth today: size, speed, miss distance', cadence: 'Daily', ttl: 6 * 3600e3, licence: 'NASA open data', home: 'https://api.nasa.gov' },
  { id: 'iss', name: 'Space station position', provider: 'wheretheiss.at (from NORAD orbital elements)', gives: 'Current latitude, longitude, altitude and speed of the International Space Station', cadence: 'Every second', ttl: 10e3, licence: 'Open', home: 'https://wheretheiss.at' },
  { id: 'events', name: 'Natural events', provider: 'NASA Earth Observatory Natural Event Tracker', gives: 'Open storms, volcanic eruptions, wildfires, sea-ice events', cadence: 'Several times a day', ttl: 3600e3, licence: 'NASA open data', home: 'https://eonet.gsfc.nasa.gov' },
  { id: 'quakes', name: 'Earthquakes', provider: 'US Geological Survey', gives: 'Earthquakes of magnitude 4.5 and above in the past day', cadence: 'Every minute', ttl: 5 * 60e3, licence: 'US public domain', home: 'https://earthquake.usgs.gov' },
  { id: 'literature', name: 'Scientific literature', provider: 'Crossref and OpenAlex', gives: 'Published papers matching a query: title, authors, year, venue, DOI, citations', cadence: 'Daily', ttl: 864e5, licence: 'CC0 metadata', home: 'https://www.crossref.org' },
  { id: 'encyclopedia', name: 'Background summaries', provider: 'Wikipedia REST', gives: 'Short encyclopaedic summary of a topic', cadence: 'Continuous', ttl: 7 * 864e5, licence: 'CC BY-SA 4.0', home: 'https://www.wikipedia.org' },
  { id: 'chem', name: 'Chemical properties', provider: 'PubChem (US National Library of Medicine)', gives: 'Molecular weight and formula for a named compound', cadence: 'Continuous', ttl: 30 * 864e5, licence: 'US public domain', home: 'https://pubchem.ncbi.nlm.nih.gov' },
];
export const sourceById = id => SOURCES.find(s => s.id === id);

const status = {};
export const sourceStatus = () => ({ ...status });
const listeners = new Set();
export const onStatus = fn => { listeners.add(fn); return () => listeners.delete(fn); };
const setStatus = (id, s) => { status[id] = { ...status[id], ...s }; listeners.forEach(fn => { try { fn(id, status[id]); } catch { /* listener errors are not ours */ } }); };

function loadCached(k) {
  if (mem.has(k)) return mem.get(k);
  try { const s = localStorage.getItem(KEY + k); if (s) { const v = JSON.parse(s); mem.set(k, v); return v; } } catch { /* storage unavailable */ }
  return null;
}
function saveCached(k, v) {
  mem.set(k, v);
  try { localStorage.setItem(KEY + k, JSON.stringify(v)); } catch { try { Object.keys(localStorage).filter(x => x.startsWith(KEY)).slice(0, 20).forEach(x => localStorage.removeItem(x)); } catch { /* ignore */ } }
}

/** Fetch JSON with timeout, on-device caching and honest staleness flags. */
export async function getJSON(sourceId, url, { ttl, force = false, key = url } = {}) {
  const src = sourceById(sourceId), maxAge = ttl ?? (src ? src.ttl : 3600e3), k = `${sourceId}|${key}`, hit = loadCached(k), now = Date.now();
  if (hit && !force && now - hit.ts < maxAge) return { data: hit.data, ts: hit.ts, stale: false, cached: true, source: src ? src.provider : sourceId };
  if (typeof navigator !== 'undefined' && navigator.onLine === false) {
    setStatus(sourceId, { ok: false, offline: true, at: now, error: 'Device is offline' });
    if (hit) return { data: hit.data, ts: hit.ts, stale: true, cached: true, source: src ? src.provider : sourceId };
    throw new Error('Offline and no saved copy is available');
  }
  const ctl = new AbortController(), timer = setTimeout(() => ctl.abort(), 15000);
  try {
    const res = await fetch(url, { signal: ctl.signal, headers: { Accept: 'application/json' }, credentials: 'omit', referrerPolicy: 'no-referrer' });
    if (!res.ok) throw new Error(`The source answered with status ${res.status}`);
    const data = await res.json();
    saveCached(k, { data, ts: now });
    setStatus(sourceId, { ok: true, at: now, error: null, offline: false });
    return { data, ts: now, stale: false, cached: false, source: src ? src.provider : sourceId };
  } catch (err) {
    setStatus(sourceId, { ok: false, at: now, error: err.name === 'AbortError' ? 'Timed out' : err.message });
    if (hit) return { data: hit.data, ts: hit.ts, stale: true, cached: true, source: src ? src.provider : sourceId, error: err.message };
    throw err;
  } finally { clearTimeout(timer); }
}

export async function geocode(name) {
  const r = await getJSON('geocode', `https://geocoding-api.open-meteo.com/v1/search?name=${encodeURIComponent(name)}&count=5&language=en`);
  return (r.data.results || []).map(g => ({ name: [g.name, g.admin1, g.country].filter(Boolean).join(', '), lat: g.latitude, lon: g.longitude, alt: g.elevation, source: 'Open-Meteo Geocoding (GeoNames)', marine: false }));
}

/**
 * Environmental conditions at a point, keyed by the engine's environmental bindings (SI units).
 * Each entry: {value, source, ts, stale}. Partial results are returned when some sources fail.
 */
export async function environment(lat, lon, { force = false } = {}) {
  const out = {}, errors = [], la = lat.toFixed(3), lo = lon.toFixed(3);
  const put = (k, value, r, label) => { if (Number.isFinite(value)) out[k] = { value, source: label || r.source, ts: r.ts, stale: r.stale }; };
  const tasks = [
    getJSON('weather', `https://api.open-meteo.com/v1/forecast?latitude=${la}&longitude=${lo}&current=temperature_2m,relative_humidity_2m,surface_pressure,wind_speed_10m&wind_speed_unit=ms`, { force }).then(r => {
      const c = r.data.current || {};
      put('air_temp', c.temperature_2m + 273.15, r); put('air_pressure', c.surface_pressure * 100, r); put('wind_speed', c.wind_speed_10m, r); put('humidity', c.relative_humidity_2m / 100, r);
      if (Number.isFinite(c.temperature_2m) && Number.isFinite(c.surface_pressure)) put('air_density', c.surface_pressure * 100 / (287.05 * (c.temperature_2m + 273.15)), r, `${r.source} (ideal-gas density from pressure and temperature)`);
    }).catch(e => errors.push(`Weather: ${e.message}`)),
    getJSON('marine', `https://marine-api.open-meteo.com/v1/marine?latitude=${la}&longitude=${lo}&current=wave_height,wave_period,sea_surface_temperature,ocean_current_velocity`, { force }).then(r => {
      const c = r.data.current || {};
      put('wave_height', c.wave_height, r); put('wave_period', c.wave_period, r);
      if (c.sea_surface_temperature != null) put('sea_surface_temp', c.sea_surface_temperature + 273.15, r);
      if (c.ocean_current_velocity != null) put('current_speed', c.ocean_current_velocity / 3.6, r);
    }).catch(e => errors.push(`Sea state: ${e.message}`)),
    getJSON('relief', `https://gis.ngdc.noaa.gov/arcgis/rest/services/DEM_mosaics/DEM_global_mosaic/ImageServer/identify?geometry=${encodeURIComponent(JSON.stringify({ x: +lo, y: +la, spatialReference: { wkid: 4326 } }))}&geometryType=esriGeometryPoint&returnGeometry=false&returnCatalogItems=false&f=json`, { force }).then(r => {
      const z = parseFloat(r.data.value);
      if (Number.isFinite(z)) { if (z < 0) put('water_depth', -z, r); put('elevation', Math.max(z, 0), r); }
    }).catch(e => errors.push(`Bathymetry: ${e.message}`)),
  ];
  await Promise.all(tasks);
  // seabed temperature and salinity from the measured-data climatology, at the depth just found
  if (out.water_depth) { try { const b = await seabed(lat, lon, out.water_depth.value); if (b) { put('seabed_temp', b.T + 273.15, b, `${b.source}; ${b.level} m level${b.clipped ? ` (deepest level with data; seabed at ${Math.round(out.water_depth.value)} m)` : ''}`); if (Number.isFinite(b.S)) put('salinity', b.S, b, b.source); } } catch (e) { errors.push(`Seabed temperature: ${e.message}`); } }
  out.latitude = { value: lat, source: 'Location', ts: Date.now(), stale: false };
  return { env: out, errors };
}

const GLODAP_DEPTHS = [0, 10, 20, 30, 50, 75, 100, 125, 150, 200, 250, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500, 1750, 2000, 2500, 3000, 3500, 4000, 4500, 5000, 5500];
/** Temperature (°C) and salinity at the seabed from the GLODAP v2 mapped climatology: interpolated in depth, or the deepest level holding data. */
export async function seabed(lat, lon, depth) {
  const la = Math.min(89.5, Math.max(-89.5, Math.floor(lat) + 0.5)), lo = Math.min(179.5, Math.max(-179.5, Math.floor(lon) + 0.5));
  const base = 'https://erddap.emodnet-physics.eu/erddap/griddap/GLODAPv2_2016b_MappedClimatologies.json', q = v => `${v}%5B(0):1:(32)%5D%5B(${la})%5D%5B(${lo})%5D`;
  const r = await getJSON('oceanprofile', `${base}?${q('temperature')},${q('salinity')}`, { key: `${la},${lo}` });
  const rows = r.data.table.rows.map(x => ({ z: GLODAP_DEPTHS[x[0]], T: x[3], S: x[4] })).filter(x => Number.isFinite(x.T) && x.T > -5 && x.T < 40);
  if (!rows.length) return null;
  const deepest = rows[rows.length - 1];
  if (depth >= deepest.z) return { T: deepest.T, S: deepest.S, level: deepest.z, clipped: depth > deepest.z * 1.25 + 50, ts: r.ts, stale: r.stale, source: sourceById('oceanprofile').provider };
  let i = 0; while (i < rows.length - 2 && rows[i + 1].z < depth) i++;
  const a = rows[i], b = rows[i + 1], f = (depth - a.z) / (b.z - a.z || 1);
  return { T: a.T + (b.T - a.T) * f, S: a.S + (b.S - a.S) * f, level: Math.round(depth), clipped: false, ts: r.ts, stale: r.stale, source: sourceById('oceanprofile').provider };
}

export async function spaceWeather(force = false) {
  const out = { errors: [] };
  await Promise.all([
    getJSON('spaceweather', 'https://services.swpc.noaa.gov/products/noaa-planetary-k-index.json', { force }).then(r => { const a = r.data, last = a[a.length - 1]; const kp = Array.isArray(last) ? parseFloat(last[1]) : parseFloat(last.Kp); const t = Array.isArray(last) ? last[0] : last.time_tag; out.kp = { value: kp, time: t, ts: r.ts, stale: r.stale, series: a.slice(-24).map(x => (Array.isArray(x) ? { t: x[0], v: parseFloat(x[1]) } : { t: x.time_tag, v: parseFloat(x.Kp) })).filter(x => Number.isFinite(x.v)) }; }).catch(e => out.errors.push(`K index: ${e.message}`)),
    getJSON('spaceweather', 'https://services.swpc.noaa.gov/products/summary/solar-wind-speed.json', { force }).then(r => { const d = Array.isArray(r.data) ? r.data[0] : r.data; out.wind = { value: parseFloat(d.proton_speed ?? d.WindSpeed) * 1000, time: d.time_tag ?? d.TimeStamp, ts: r.ts, stale: r.stale }; }).catch(e => out.errors.push(`Solar wind: ${e.message}`)),
    getJSON('spaceweather', 'https://services.swpc.noaa.gov/products/summary/solar-wind-mag-field.json', { force }).then(r => { const d = Array.isArray(r.data) ? r.data[0] : r.data; out.imf = { bt: parseFloat(d.bt ?? d.Bt) * 1e-9, bz: parseFloat(d.bz_gsm ?? d.Bz) * 1e-9, time: d.time_tag ?? d.TimeStamp, ts: r.ts, stale: r.stale }; }).catch(e => out.errors.push(`Magnetic field: ${e.message}`)),
  ]);
  return out;
}
export async function nearEarthObjects(force = false) {
  const r = await getJSON('neo', `https://api.nasa.gov/neo/rest/v1/feed/today?detailed=false&api_key=${nasaKey()}`, { force, key: 'today' });
  const list = Object.values(r.data.near_earth_objects || {}).flat().map(o => { const ca = (o.close_approach_data || [])[0] || {}; return { name: o.name, dMin: o.estimated_diameter?.meters?.estimated_diameter_min, dMax: o.estimated_diameter?.meters?.estimated_diameter_max, hazardous: o.is_potentially_hazardous_asteroid, speed: parseFloat(ca.relative_velocity?.kilometers_per_second) * 1000, miss: parseFloat(ca.miss_distance?.kilometers) * 1000, when: ca.close_approach_date_full }; }).sort((a, b) => a.miss - b.miss);
  return { list, ts: r.ts, stale: r.stale };
}
export async function issPosition(force = true) {
  const r = await getJSON('iss', 'https://api.wheretheiss.at/v1/satellites/25544', { force });
  return { lat: r.data.latitude, lon: r.data.longitude, alt: r.data.altitude * 1000, speed: r.data.velocity / 3.6, visibility: r.data.visibility, ts: r.ts, stale: r.stale };
}
export async function naturalEvents(force = false) {
  const r = await getJSON('events', 'https://eonet.gsfc.nasa.gov/api/v3/events?limit=12&status=open', { force });
  return { list: (r.data.events || []).map(e => ({ title: e.title, category: (e.categories[0] || {}).title, date: (e.geometry[e.geometry.length - 1] || {}).date, coords: (e.geometry[e.geometry.length - 1] || {}).coordinates })), ts: r.ts, stale: r.stale };
}
export async function earthquakes(force = false) {
  const r = await getJSON('quakes', 'https://earthquake.usgs.gov/earthquakes/feed/v1.0/summary/4.5_day.geojson', { force });
  return { list: (r.data.features || []).map(f => ({ mag: f.properties.mag, place: f.properties.place, time: f.properties.time, depth: f.geometry.coordinates[2] * 1000, lon: f.geometry.coordinates[0], lat: f.geometry.coordinates[1] })).sort((a, b) => b.mag - a.mag), ts: r.ts, stale: r.stale };
}
export async function climatology(lat, lon) {
  const r = await getJSON('climate', `https://power.larc.nasa.gov/api/temporal/climatology/point?parameters=T2M,WS10M,PS,RH2M&community=RE&longitude=${lon.toFixed(2)}&latitude=${lat.toFixed(2)}&format=JSON`);
  const p = r.data.properties.parameter;
  return { T: p.T2M, wind: p.WS10M, pressure: p.PS, humidity: p.RH2M, ts: r.ts, stale: r.stale };
}

/** Literature search across two independent indexes; results are merged by DOI. */
export async function literature(query, n = 8) {
  const out = [], errors = [];
  await Promise.all([
    getJSON('literature', `https://api.crossref.org/works?query=${encodeURIComponent(query)}&rows=${n}&select=title,author,issued,DOI,container-title,is-referenced-by-count,type`).then(r => (r.data.message.items || []).forEach(w => out.push({ title: (w.title || [''])[0], authors: (w.author || []).slice(0, 4).map(a => [a.given, a.family].filter(Boolean).join(' ')).join(', ') + ((w.author || []).length > 4 ? ' et al.' : ''), year: w.issued?.['date-parts']?.[0]?.[0], venue: (w['container-title'] || [''])[0], doi: w.DOI, cited: w['is-referenced-by-count'], via: 'Crossref', ts: r.ts, stale: r.stale }))).catch(e => errors.push(`Crossref: ${e.message}`)),
    getJSON('literature', `https://api.openalex.org/works?search=${encodeURIComponent(query)}&per-page=${n}&select=title,publication_year,doi,cited_by_count,primary_location,authorships`).then(r => (r.data.results || []).forEach(w => out.push({ title: w.title || '', authors: (w.authorships || []).slice(0, 4).map(a => a.author?.display_name).filter(Boolean).join(', ') + ((w.authorships || []).length > 4 ? ' et al.' : ''), year: w.publication_year, venue: w.primary_location?.source?.display_name || '', doi: (w.doi || '').replace('https://doi.org/', ''), cited: w.cited_by_count, via: 'OpenAlex', ts: r.ts, stale: r.stale }))).catch(e => errors.push(`OpenAlex: ${e.message}`)),
  ]);
  const seen = new Map();
  out.forEach(w => { const k = (w.doi || w.title).toLowerCase(); if (!w.title) return; if (seen.has(k)) { const o = seen.get(k); o.via = `${o.via}, ${w.via}`; o.cited = Math.max(o.cited || 0, w.cited || 0); } else seen.set(k, w); });
  return { results: [...seen.values()].sort((a, b) => (b.cited || 0) - (a.cited || 0)), errors, query };
}
export async function encyclopedia(topic) {
  const r = await getJSON('encyclopedia', `https://en.wikipedia.org/api/rest_v1/page/summary/${encodeURIComponent(topic.replace(/ /g, '_'))}`);
  return { title: r.data.title, extract: r.data.extract, url: r.data.content_urls?.desktop?.page, ts: r.ts, stale: r.stale };
}
export async function compound(name) {
  const r = await getJSON('chem', `https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/name/${encodeURIComponent(name)}/property/MolecularWeight,MolecularFormula,IUPACName/JSON`);
  const p = r.data.PropertyTable.Properties[0];
  return { formula: p.MolecularFormula, molarMass: parseFloat(p.MolecularWeight) / 1000, iupac: p.IUPACName, ts: r.ts, stale: r.stale };
}

export const age = ts => { const s = (Date.now() - ts) / 1000; return s < 90 ? 'just now' : s < 3600 ? `${Math.round(s / 60)} min ago` : s < 172800 ? `${Math.round(s / 3600)} h ago` : `${Math.round(s / 86400)} days ago`; };

/** Refresh the sources that matter to saved investigations; used by periodic background sync. */
export async function refreshAll(locations = []) {
  const jobs = [spaceWeather(true).catch(() => null), earthquakes(true).catch(() => null), naturalEvents(true).catch(() => null)];
  locations.slice(0, 6).forEach(l => jobs.push(environment(l.lat, l.lon, { force: true }).catch(() => null)));
  await Promise.all(jobs);
  try { localStorage.setItem('bespoke.lastRefresh', String(Date.now())); } catch { /* ignore */ }
}
