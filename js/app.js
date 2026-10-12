// Application shell: routing, history arrows, installation, offline status and updates.
import { $, $$, toast, esc } from './ui/dom.js';
import * as Pages from './ui/pages.js';
import { investigationView } from './ui/investigation.js';
import { prefs } from './core/store.js';
import { refreshAll } from './core/connectors.js';
import { watch as typesetMath } from './ui/mathify.js';
import { watch as explainPanels } from './ui/guide.js';

const main = $('#main');
const routes = {
  '': Pages.home, m1: () => Pages.promptPage(1), m2: () => Pages.promptPage(2), re: Pages.reversePage, saved: Pages.savedPage,
  library: Pages.libraryPage, fields: Pages.fieldsPage, sources: Pages.sourcesPage, settings: Pages.settingsPage, help: Pages.helpPage, refresh: Pages.refreshPage, i: investigationView,
};
let cleanup = null, pos = 0, max = 0;

async function render() {
  const [, name = '', ...rest] = (location.hash || '#/').split('?')[0].split('/');
  const query = Object.fromEntries(new URLSearchParams((location.hash.split('?')[1] || '')));
  // position in the session history drives the arrows
  if (history.state && typeof history.state.pos === 'number') pos = history.state.pos;
  else { pos = Math.min(max + 1, pos + 1); max = pos; history.replaceState({ pos }, ''); }
  max = Math.max(max, pos); sessionStorage.setItem('bespoke.max', String(max));
  $('#nav-back').disabled = pos <= 0; $('#nav-fwd').disabled = pos >= max;
  if (cleanup) { try { cleanup(); } catch { /* view already gone */ } cleanup = null; }
  const view = routes[name] || Pages.notFound;
  let v;
  try { v = await view(rest, query); }
  catch (err) { console.error(err); v = { title: 'Something went wrong', crumb: 'Error', html: `<div class="card"><h2>This page could not be shown</h2><p class="dim">${esc(err.message)}</p><a class="btn" href="#/">Return home</a></div>` }; }
  if (!v) return;
  document.title = `${v.title} — Bespoke`;
  $('#crumb').textContent = v.crumb || v.title;
  main.innerHTML = `<div class="fade">${v.html && v.html.__raw != null ? v.html.__raw : v.html}</div>`;
  $$('.botnav a').forEach(a => a.toggleAttribute('aria-current', false));
  const nav = { '': 'home', m1: 'm1', m2: 'm2', re: 're', sources: 'sources' }[name]; if (nav) $(`.botnav a[data-nav="${nav}"]`)?.setAttribute('aria-current', 'page');
  if (!v.keepScroll) window.scrollTo(0, 0);
  // each view gets a fresh root element so that its event listeners disappear with it
  if (v.after) { try { cleanup = (await v.after(main.firstElementChild)) || null; } catch (err) { console.error(err); toast(`A panel failed to draw: ${err.message}`); } }
  main.focus({ preventScroll: true });
}
export const go = hash => { if (location.hash === hash) render(); else location.hash = hash; };
export const rerender = () => render();

// ---- history arrows
max = +(sessionStorage.getItem('bespoke.max') || 0);
if (!history.state) history.replaceState({ pos: 0 }, ''); else pos = history.state.pos || 0;
$('#nav-back').addEventListener('click', () => history.back());
$('#nav-fwd').addEventListener('click', () => history.forward());
window.addEventListener('keydown', e => { if (e.altKey && e.key === 'ArrowLeft') history.back(); if (e.altKey && e.key === 'ArrowRight') history.forward(); });
window.addEventListener('hashchange', render);
window.addEventListener('popstate', () => { /* hashchange follows; state already carries the position */ });

// ---- appearance
const applyTheme = t => { document.documentElement.dataset.theme = t; document.querySelector('meta[name=theme-color]').content = t === 'light' ? '#f4f6fb' : '#0a0f1c'; };
applyTheme(prefs.get('theme', window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark'));
$('#theme').addEventListener('click', () => { const t = document.documentElement.dataset.theme === 'light' ? 'dark' : 'light'; prefs.set('theme', t); applyTheme(t); render(); });
// equation fonts are loaded without blocking first paint
const kcss = $('#katex-css'); if (kcss) kcss.media = 'all';

// ---- network status
const net = $('#net');
const setNet = () => { const on = navigator.onLine !== false; net.classList.toggle('off', !on); net.querySelector('span').textContent = on ? 'Online' : 'Offline'; net.title = on ? 'Online: live data sources are reachable' : 'Offline: the application keeps working with saved data'; };
window.addEventListener('online', () => { setNet(); toast('Back online: live data will refresh'); });
window.addEventListener('offline', () => { setNet(); toast('You are offline. Everything on this device still works.'); });
setNet();

// ---- installation
let deferred = null;
const installBtn = $('#install');
const standalone = window.matchMedia('(display-mode: standalone)').matches || navigator.standalone === true;
window.addEventListener('beforeinstallprompt', e => { e.preventDefault(); deferred = e; installBtn.hidden = false; });
window.addEventListener('appinstalled', () => { installBtn.hidden = true; deferred = null; toast('Installed. You can now open Bespoke from your home screen or app list, with or without a connection.'); });
if (!standalone) installBtn.hidden = false;
export async function install() {
  if (deferred) { deferred.prompt(); const r = await deferred.userChoice; if (r.outcome === 'accepted') installBtn.hidden = true; deferred = null; return; }
  go('#/settings');
  setTimeout(() => document.getElementById('install-help')?.scrollIntoView({ behavior: 'smooth' }), 200);
}
installBtn.addEventListener('click', install);
export const canPromptInstall = () => !!deferred;
export const isStandalone = () => standalone;

// ---- service worker: offline shell, background refresh, automatic updates
if ('serviceWorker' in navigator && location.protocol !== 'file:') {
  window.addEventListener('load', async () => {
    try {
      const hadController = !!navigator.serviceWorker.controller;
      // when a newer release takes control, reload once so that every file comes from the same release
      let reloaded = false;
      navigator.serviceWorker.addEventListener('controllerchange', () => { if (hadController && !reloaded) { reloaded = true; location.reload(); } });
      const reg = await navigator.serviceWorker.register('sw.js', { scope: './', updateViaCache: 'none' });
      reg.update().catch(() => {});
      setInterval(() => reg.update().catch(() => {}), 30 * 60 * 1000);
      document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible') reg.update().catch(() => {}); });
      if ('periodicSync' in reg) { try { const st = await navigator.permissions.query({ name: 'periodic-background-sync' }); if (st.state === 'granted') await reg.periodicSync.register('refresh-data', { minInterval: 3 * 3600 * 1000 }); } catch { /* not granted on this platform */ } }
    } catch (err) { console.warn('Offline support could not be enabled:', err.message); }
  });
}
// refresh live feeds whenever the application comes to the foreground, at most every ten minutes
let lastRefresh = 0;
const foregroundRefresh = () => { if (document.visibilityState !== 'visible' || navigator.onLine === false || Date.now() - lastRefresh < 600e3) return; lastRefresh = Date.now(); refreshAll(prefs.get('locations', [])).catch(() => {}); };
document.addEventListener('visibilitychange', foregroundRefresh); setTimeout(foregroundRefresh, 4000);

window.addEventListener('error', e => console.error(e.error || e.message));
const boot = () => { typesetMath(main); explainPanels(main); render(); };
if (window.katex || document.readyState === 'complete') boot(); else window.addEventListener('DOMContentLoaded', boot);
