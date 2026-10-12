// Small DOM and formatting helpers shared by every view.
import { fmt, fromSI, tryUnit, dimEq } from '../core/units.js';
import { PROV } from '../engine/core.js';

export const esc = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
/** Tagged template that escapes interpolations unless wrapped with raw(). Arrays are joined. */
export const raw = s => ({ __raw: String(s ?? '') });
export function html(strings, ...vals) {
  let o = '';
  strings.forEach((s, i) => { o += s; if (i < vals.length) { const v = vals[i]; o += Array.isArray(v) ? v.map(x => (x && x.__raw != null ? x.__raw : esc(x))).join('') : v && v.__raw != null ? v.__raw : v === false || v == null ? '' : esc(v); } });
  return raw(o);
}
export const join = (arr, fn) => raw(arr.map((x, i) => { const r = fn(x, i); return r && r.__raw != null ? r.__raw : esc(r); }).join(''));

/** Render LaTeX to markup; falls back to code when the renderer has not loaded yet. */
export function tex(src, display = false) {
  try { if (window.katex) return raw(window.katex.renderToString(src, { displayMode: display, throwOnError: false, strict: 'ignore', output: 'html' })); } catch { /* fall through */ }
  return raw(`<code>${esc(src)}</code>`);
}
export const texStr = (src, display = true) => tex(src, display).__raw;

export const chip = (label, tone = 'mute', title = '') => raw(`<span class="chip ${tone}"${title ? ` title="${esc(title)}"` : ''}>${esc(label)}</span>`);
export const provChip = key => { const p = PROV[key] || PROV.SUPPLIED; return chip(p.label, p.tone, p.text); };
export const STATE = {
  computed: ['Computed', 'ok'], derived: ['Derived', 'ok'], generated: ['Generated', 'live'], verified: ['Verified', 'ok'], validated: ['Compared with data', 'ok'],
  partial: ['Partly supported', 'warn'], interactive: ['Interactive', 'live'], ondemand: ['On request', 'soft'], needs: ['Needs your data', 'warn'],
  na: ['Not applicable here', 'mute'], unavailable: ['Unavailable', 'mute'], failed: ['Failed', 'bad'], conditional: ['Conditional', 'hypo'],
};
export const stateChip = k => chip(...(STATE[k] || STATE.na));

/** Scalar value in its preferred display unit. */
export function showScalar(s, sig = 5) {
  if (s.text) return s.text;
  const u = s.show && tryUnit(s.show) && tryUnit(s.unit) && dimEq(tryUnit(s.show).dim, tryUnit(s.unit).dim) ? s.show : s.unit;
  const v = u === s.unit ? s.value : fromSI(s.value, u);
  return `${fmt(v, sig)}${u && u !== '1' ? ' ' + u : ''}`;
}
export const pct = (x, sig = 3) => (Number.isFinite(x) ? `${x >= 0 ? '+' : ''}${fmt(x * 100, sig)} %` : '—');
export const when = ts => new Date(ts).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' });
export const bytes = n => (n < 1024 ? `${n} B` : n < 1048576 ? `${(n / 1024).toFixed(1)} kB` : `${(n / 1048576).toFixed(1)} MB`);

/** Units offered for an input: its own unit plus common alternatives of the same dimension. */
const FAMILIES = [['m', 'km', 'cm', 'mm', 'um', 'nm', 'in', 'ft', 'mi', 'AU', 'ly'], ['Pa', 'kPa', 'MPa', 'GPa', 'bar', 'atm', 'psi'], ['K', '°C', '°F'], ['s', 'ms', 'us', 'ns', 'min', 'h', 'd', 'yr'], ['kg', 'g', 'mg', 't', 'lb'], ['m/s', 'km/h', 'kn', 'mph'], ['m^3/s', 'm^3/h', 'L/s', 'L/min', 'bbl/d'], ['kg/s', 'kg/h', 't/h'], ['N', 'kN', 'MN', 'lbf'], ['J', 'kJ', 'MJ', 'kWh', 'eV', 'MeV'], ['W', 'kW', 'MW', 'hp'], ['Pa s', 'cP'], ['Hz', 'kHz', 'MHz', 'GHz', 'THz', 'rpm'], ['rad', 'deg'], ['1', '%'], ['V', 'kV', 'mV'], ['A', 'mA', 'uA'], ['m^2', 'cm^2', 'mm^2'], ['m^3', 'L', 'mL', 'bbl'], ['kg/m^3', 'g/L'], ['N/m', 'kN/m'], ['T', 'mT', 'uT', 'G']];
export function unitChoices(unit) {
  const u = tryUnit(unit); if (!u) return [unit];
  const fam = FAMILIES.find(f => { const t = tryUnit(f[0]); return t && dimEq(t.dim, u.dim); });
  return [...new Set([unit, ...(fam || [])])];
}

export function toast(msg, ms = 3200) {
  const t = document.getElementById('toast'); if (!t) return;
  t.textContent = msg; t.classList.add('show'); clearTimeout(toast._t); toast._t = setTimeout(() => t.classList.remove('show'), ms);
}
/** Delegate events: on(root, 'click', '[data-act]', (ev, el) => …) */
export function on(root, type, sel, fn) { root.addEventListener(type, ev => { const el = ev.target.closest(sel); if (el && root.contains(el)) fn(ev, el); }); }
export const debounce = (fn, ms = 250) => { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };
export const $ = (sel, root = document) => root.querySelector(sel);
export const $$ = (sel, root = document) => [...root.querySelectorAll(sel)];
export const copy = async text => { try { await navigator.clipboard.writeText(text); toast('Copied to clipboard'); } catch { toast('Copy is not available in this browser'); } };
export const table = (head, rows, cls = '') => raw(`<div class="tw"><table class="${cls}"><thead><tr>${head.map(h => `<th${h && h.num ? ' class="num"' : ''}>${esc(h && h.t != null ? h.t : h)}</th>`).join('')}</tr></thead><tbody>${rows.map(r => `<tr>${r.map(c => `<td${c && c.num ? ' class="num"' : ''}>${c && c.__raw != null ? c.__raw : c && c.t != null ? (c.t.__raw != null ? c.t.__raw : esc(c.t)) : esc(c)}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`);
export const num = t => ({ t, num: true });
export const section = (title, body, open = false, extra = '') => raw(`<details${open ? ' open' : ''}><summary>${esc(title)} ${extra && extra.__raw != null ? extra.__raw : esc(extra)}</summary><div class="body">${body && body.__raw != null ? body.__raw : esc(body)}</div></details>`);
